-- Prove2me | Definitions.Def_RankingQueryCost_Joint_Completion
-- name    : RankingQueryCost_Joint_Completion
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T13:25:38.279349+00:00
-- url     : https://prove2.me/theorems/95213610-be9b-4387-9167-c0aae93a0c70
-- title:
--   Algorithm 2 and its implicit completed tournament
-- statement:
--   With $D=s+1$, process objects in public-label order. Insert each into the maintained sequence by binary search using the ledger, then inspect its at-most-$D$ neighbors on either side. At a backward comparison with $u$, remove the inserted object, $u$, and its immediate neighbor toward $u$ as a triple. After the updates, acquire every star incident to a removed object.
--
--   $$\widetilde T_e=\begin{cases}T_e&e\text{ acquired},\\\text{forward in the final sequence}&e\text{ unqueried}.\end{cases}$$
--
--   Band status, disjointness of removed triples, fault charges and compatibility preservation are separate theorem conclusions. The unrestricted lower-bound forced-completion task may refuse; every release must fill only forced orientations. Its success requirement is probability at least $3/4$ in every clean world.
--
--   **Formalization Note** The scan order is public. The invariant refers to completed retained-insertion or removal updates, as in the source's proof, rather than an instant before the insertion's band comparisons have been read. A forced orientation set in a legal record extends an order, so list representation loses no sound forced completion.
--
--   Comparison stars are traversed in the explicit public lexicographic pair order `pairList n`; no classically chosen list order is required by a finite implementation.
-- source:
--   Chaoqiang Fu, Yifan Su, Daofeng Li, STOC 2027 submission #812 (October 2026), §4.2, Algorithm 2 and Lemmas 4.7–4.8, pp. 19–22, PDF pp. 20–23; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/812.pdf

import Definitions.Def_RankingQueryCost_Joint_Interaction

set_option autoImplicit false

noncomputable section

namespace RankingQueryCost.Joint

attribute [local instance] Classical.propDecidable

/-- Compare arbitrary distinct labels through the one physical ledger. Result true means i wins.
The equal-label case is never requested by Algorithm 2 and has the explicit value false. -/
def readLabels {n : ℕ} (W : ComparisonWorld n) (h : ℕ) (S : InteractionState n)
    (i j : Fin n) : Bool × InteractionState n :=
  if hij : i < j then
    let out := readIdentity h W S [] ⟨(i, j), hij⟩
    (!out.1, out.2)
  else if hji : j < i then readIdentity h W S [] ⟨(j, i), hji⟩
  else (false, S)

/-- Binary search is governed by observed comparisons, without assuming transitivity.
The final predecessor and successor are the actual binary-search bounds. -/
def insertionSearch {n : ℕ} (W : ComparisonWorld n) (h : ℕ) (v : Fin n)
    (C : List (Fin n)) : ℕ → ℕ → ℕ → InteractionState n → ℕ × InteractionState n
  | 0, lo, _, S => (lo, S)
  | fuel + 1, lo, hi, S =>
    if lo < hi then
      let mid := (lo + hi) / 2
      match C[mid]? with
      | none => (lo, S)
      | some u =>
        let out := readLabels W h S v u
        if out.1 then insertionSearch W h v C fuel (mid + 1) hi out.2
        else insertionSearch W h v C fuel lo mid out.2
    else (lo, S)

/-- Scan near neighbors in a fixed public order, stopping at the first backward answer. -/
def scanBand {n : ℕ} (W : ComparisonWorld n) (h : ℕ) (v : Fin n)
    (pos : ℕ) : List (ℕ × Fin n) → InteractionState n → Option (Fin n) × InteractionState n
  | [], S => (none, S)
  | (j, u) :: rest, S =>
    let out := readLabels W h S v u
    let forward := if j < pos then out.1 else !out.1
    if forward then scanBand W h v pos rest out.2 else (some u, out.2)

structure InsertionState (n : ℕ) where
  sequence : List (Fin n)
  triples : List (Fin n × Fin n × Fin n)
  interaction : InteractionState n

def insertionStart {n : ℕ} (S : InteractionState n) : InsertionState n := ⟨[], [], S⟩

/-- One completed insertion or removal update of Algorithm 2. There is no invariant in
this definition; the band invariant and the fault charge are the content of Lemma 4.7. -/
def insertObject {n : ℕ} (s h : ℕ) (W : ComparisonWorld n) (v : Fin n)
    (I : InsertionState n) : InsertionState n :=
  let search := insertionSearch W h v I.sequence (I.sequence.length + 1) 0 I.sequence.length I.interaction
  let C := I.sequence.take search.1 ++ [v] ++ I.sequence.drop search.1
  let neighbors := ((List.range C.length).filter fun j =>
    decide (j ≠ search.1 ∧ (if j < search.1 then search.1 - j else j - search.1) ≤ s + 1)).filterMap
      fun j => (C[j]?).map fun u => (j, u)
  let scanned := scanBand W h v search.1 neighbors search.2
  match scanned.1 with
  | none => ⟨C, I.triples, scanned.2⟩
  | some u =>
    let index := C.idxOf u
    let zi := if index < search.1 then search.1 - 1 else search.1 + 1
    match C[zi]? with
    | none => ⟨C, I.triples, scanned.2⟩
    | some z => ⟨(C.erase v).erase u |>.erase z, I.triples ++ [(v, u, z)], scanned.2⟩

def insertionThrough {n : ℕ} (s h m : ℕ) (W : ComparisonWorld n)
    (S : InteractionState n) : InsertionState n :=
  ((List.finRange n).take m).foldl (fun I v => insertObject s h W v I) (insertionStart S)

def removedVertices {n : ℕ} (I : InsertionState n) : List (Fin n) :=
  I.triples.flatMap fun t => [t.1, t.2.1, t.2.2]

def BandInvariant {n : ℕ} (s : ℕ) (I : InsertionState n) : Prop :=
  I.sequence.Nodup ∧ ∀ (i j : ℕ) (u v : Fin n),
    I.sequence[i]? = some u → I.sequence[j]? = some v → i < j → j - i ≤ s + 1 →
      RecordedForward I.interaction.ledger u v ∨ ForcedForward s I.interaction.ledger u v

/-- Full exceptional stars are acquired after all insertion/removal updates. -/
def completionState {n : ℕ} (s h : ℕ) (W : ComparisonWorld n)
    (S : InteractionState n) : InsertionState n :=
  let I := insertionThrough s h n W S
  let F := (removedVertices I).toFinset
  let stars := (pairList n).filter fun e => decide (e.1.1 ∈ F ∨ e.1.2 ∈ F)
  { I with interaction := stars.foldl (fun S e => (readIdentity h W S [] e).2) I.interaction }

/-- Implicit tournament: acquired replies are retained verbatim. Only unqueried pairs
are oriented by the maintained sequence; correctness is a theorem, not a field. -/
def filledTournament {n : ℕ} (T : Transcript n) (C : List (Fin n)) : Tournament n :=
  fun e => match T e with
  | some b => b
  | none => decide (C.idxOf e.1.1 < C.idxOf e.1.2)

/-- Public sequence decoding for unrestricted forced-completion lower-bound policies. -/
def decodeSequence (n : ℕ) (c : List ℕ) : List (Fin n) :=
  c.filterMap fun j => if hj : j < n then some ⟨j, hj⟩ else none

/-- A forced-completion policy may refuse. Every released record must retain acquired answers
and fill only forced orientations, with a complete sequence as its implicit representation. -/
def SoundForcedPolicy {n : ℕ} (a h : ℕ) (A : QueryPolicy n) : Prop :=
  ∀ W, LegalWorld a W → ∀ ω o, Returns A W h ω o → o.emission = true →
    SoundCompletion (a + h) o.state.ledger
      (filledTournament o.state.ledger (decodeSequence n o.certificate))

def CleanCompletionSuccess {n : ℕ} (A : QueryPolicy n) : Prop :=
  ∀ W : ComparisonWorld n, W.initial = ∅ →
    (3 / 4 : ENNReal) ≤ privateLaw {ω | ∃ o, Returns A W 0 ω o ∧ o.emission = true}

end RankingQueryCost.Joint


