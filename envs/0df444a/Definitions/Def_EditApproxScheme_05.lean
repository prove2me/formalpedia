-- Prove2me | Definitions.Def_EditApproxScheme_05
-- name    : EditApproxScheme_05
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-15T16:33:44.968544+00:00
-- url     : https://prove2.me/theorems/3fbbbe7b-8d03-42bf-839a-478583866a64
-- title:
--   Edit-distance approximation scheme, part 5 of 20: the online optimizer
-- statement:
--   This is **part 5 of 20** of the definitions of a uniform almost-linear approximation scheme for edit distance, which the main statement `OAI.EditApproximation.almostLinearEditDistanceRawBandV3` is about. This part contains the finite online optimizer: smoothed gradients, optimizer updates and coefficients, online minima, maximizers and group selection, together with target intervals and their normalization and footprints.
--
--   Each part imports the previous one, so importing part 20 brings all definitions into scope. A description of the whole scheme is given in part 20.
--
--   **Formalization Note** These 20 parts replace the single 1.4 MB block `Def_EditApproximation`, which was too large for the platform to import. In the source, the supporting lemmas were pasted as local `have` proofs inside the definition bodies: 948 copies of 145 lemmas. Each lemma is now proved once as a top-level theorem and cited by name; one lemma that nothing used was dropped. The file was then split into sequential parts by deleting declarations. All 1,403 declarations from the source keep exactly the same elaborated types.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/EditApproximation.lean#L2567-L2816 (line numbers refer to the lemma-lifted file, 12,145 lines)

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/EditApproximation.lean
-- Part 5 of 20 of the edit-distance approximation definitions: embedded proof lemmas lifted
-- to top-level theorems (OAI.EditApproximation.Lemmas.*), then split by skeleton subtraction.

import Definitions.Def_EditApproxScheme_04

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation.BinaryFraction

open Finset

def gradientWithWork {d : ℕ} (G : ℕ) (linear point : Vector OAI.EditApproximation.BinaryFraction d) :
    Vector OAI.EditApproximation.BinaryFraction d × ℕ :=
  OAI.EditApproximation.vectorMapWithWork d (OAI.EditApproximation.BinaryFraction.gradientCellWithWork G linear point)

def scoredArgmaxWithWork {α : Type u_1} (score : α → OAI.EditApproximation.BinaryFraction × ℕ) :
    List α → Option (α × OAI.EditApproximation.BinaryFraction) × ℕ
  | [] => (none, 0)
  | a :: rest =>
    let tail := scoredArgmaxWithWork score rest
    let current := score a
    match tail.1 with
    | none => (some (a, current.1), tail.2 + current.2 + 1)
    | some best =>
      let comparison := current.1.ltWithWork best.2
      (if comparison.1 then some best else some (a, current.1),
        tail.2 + current.2 + comparison.2 + 2)

def optimizerUpdateWithWork {d : ℕ} (j : ℕ) (previous selected : Vector OAI.EditApproximation.BinaryFraction d) :
    Vector OAI.EditApproximation.BinaryFraction d × ℕ :=
  let step := OAI.EditApproximation.BinaryFraction.divWithWork (OAI.EditApproximation.BinaryFraction.nat 2) (OAI.EditApproximation.BinaryFraction.nat (j + 2))
  let complement := OAI.EditApproximation.BinaryFraction.subWithWork OAI.EditApproximation.BinaryFraction.one step.1
  let result := OAI.EditApproximation.vectorMapWithWork d fun i =>
    let first := OAI.EditApproximation.BinaryFraction.canonicalMulWithWork complement.1 (previous.get i)
    let second := OAI.EditApproximation.BinaryFraction.canonicalMulWithWork step.1 (selected.get i)
    let total := OAI.EditApproximation.BinaryFraction.canonicalAddWithWork first.1 second.1
    (total.1, first.2 + second.2 + total.2 + 4)
  (result.1, step.2 + complement.2 + result.2 + Nat.size (j + 2) + 4)

def bandMassTotalWithWork {M : ℕ} (mass : Vector OAI.EditApproximation.BinaryFraction M) : OAI.EditApproximation.BinaryFraction × ℕ :=
  OAI.EditApproximation.BinaryFraction.dotWithWork mass (Vector.replicate M OAI.EditApproximation.BinaryFraction.one)

def coefficientWithWork (kappa : OAI.EditApproximation.BinaryFraction) : OAI.EditApproximation.BinaryFraction × ℕ :=
  let scaled := OAI.EditApproximation.BinaryFraction.canonicalMulWithWork (OAI.EditApproximation.BinaryFraction.nat 2) kappa
  let difference := OAI.EditApproximation.BinaryFraction.subWithWork OAI.EditApproximation.BinaryFraction.one scaled.1
  (difference.1, scaled.2 + difference.2 + 1)

def naturalDistanceLeWithWork (a b radius : ℕ) : Bool × ℕ :=
  let distance := OAI.EditApproximation.BinaryFraction.distanceWithWork (OAI.EditApproximation.BinaryFraction.nat a) (OAI.EditApproximation.BinaryFraction.nat b)
  let result := distance.1.leWithWork (OAI.EditApproximation.BinaryFraction.nat radius)
  (result.1, distance.2 + result.2 + Nat.size a + Nat.size b + Nat.size radius + 3)

def onlineMinimumWithWork : List OAI.EditApproximation.BinaryFraction → Option OAI.EditApproximation.BinaryFraction × ℕ
  | [] => (none, 1)
  | first :: rest =>
    let result := OAI.EditApproximation.BinaryFraction.minimumWithWork first rest
    (some result.1, result.2 + 1)

def refinementUpdateWithWork (delta cone : OAI.EditApproximation.BinaryFraction) : Option OAI.EditApproximation.BinaryFraction → OAI.EditApproximation.BinaryFraction × ℕ
  | none => (cone, 1)
  | some online =>
    let denominator := OAI.EditApproximation.BinaryFraction.canonicalAddWithWork OAI.EditApproximation.BinaryFraction.one delta
    let lower := OAI.EditApproximation.BinaryFraction.divWithWork cone denominator.1
    let clipped := OAI.EditApproximation.BinaryFraction.maxWithWork lower.1 online
    let result := OAI.EditApproximation.BinaryFraction.minWithWork cone clipped.1
    (result.1, denominator.2 + lower.2 + clipped.2 + result.2 + 2)

def equalWithWork (a b : OAI.EditApproximation.BinaryFraction) : Bool × ℕ :=
  let left := a.leWithWork b
  let right := b.leWithWork a
  (left.1 && right.1, left.2 + right.2 + 1)

def roundedSpacingWithWork (theta envelope : OAI.EditApproximation.BinaryFraction) : List Bool × ℕ :=
  let product := OAI.EditApproximation.BinaryFraction.canonicalMulWithWork theta envelope
  let clipped := OAI.EditApproximation.BinaryFraction.maxWithWork OAI.EditApproximation.BinaryFraction.one product.1
  let rounded := OAI.EditApproximation.BinaryFraction.naturalCeilingWithWork clipped.1
  (rounded.1, product.2 + clipped.2 + rounded.2 + 2)

def maximizerWithWork {d : ℕ} (gradient : Vector OAI.EditApproximation.BinaryFraction d)
    (vertices : List (Vector OAI.EditApproximation.BinaryFraction d)) : Vector OAI.EditApproximation.BinaryFraction d × ℕ :=
  let selected := OAI.EditApproximation.BinaryFraction.scoredArgmaxWithWork (OAI.EditApproximation.BinaryFraction.dotWithWork gradient) vertices
  ((selected.1.map Prod.fst).getD (Vector.replicate d OAI.EditApproximation.BinaryFraction.zero), selected.2 + d + 1)

def groupTermsWithWork {M : ℕ} (h : OAI.EditApproximation.BinaryFraction) (envelope values : Vector OAI.EditApproximation.BinaryFraction M)
    (indices : List (Fin M)) : List OAI.EditApproximation.BinaryFraction × ℕ :=
  OAI.EditApproximation.arithmeticMapWithWork (fun i =>
    let test := OAI.EditApproximation.BinaryFraction.equalWithWork (envelope.get i) h
    (if test.1 then values.get i else OAI.EditApproximation.BinaryFraction.zero, test.2 + 2)) indices

def selectGroupWithWork {ι : Type u_1} (members : List ι) (hne : members ≠ [])
    (estimate : ι → OAI.EditApproximation.BinaryFraction × ℕ) : ι × ℕ :=
  let selected := OAI.EditApproximation.BinaryFraction.scoredArgmaxWithWork (fun member =>
    let result := estimate member
    (result.1.neg, result.2 + 1)) members
  ((selected.1.map Prod.fst).getD (members.head hne), selected.2 + 1)

def finiteOptimizerWithWork {d : ℕ} (vertices : List (Vector OAI.EditApproximation.BinaryFraction d))
    (linear : Vector OAI.EditApproximation.BinaryFraction d) (G : ℕ) : ℕ → Vector OAI.EditApproximation.BinaryFraction d × ℕ
  | 0 => (vertices.headD (Vector.replicate d OAI.EditApproximation.BinaryFraction.zero), d + 1)
  | j + 1 =>
    let previous := finiteOptimizerWithWork vertices linear G j
    let gradient := OAI.EditApproximation.BinaryFraction.gradientWithWork G linear previous.1
    let selected := OAI.EditApproximation.BinaryFraction.maximizerWithWork gradient.1 vertices
    let updated := OAI.EditApproximation.BinaryFraction.optimizerUpdateWithWork j previous.1 selected.1
    (updated.1, previous.2 + gradient.2 + selected.2 + updated.2 + 3)

def selectionWithWork {α : Type u_1} {d : ℕ}
    (vertices : List (α × Vector OAI.EditApproximation.BinaryFraction d)) (linear : Vector OAI.EditApproximation.BinaryFraction d) (G j : ℕ) :
    Option α × ℕ :=
  let iterate := OAI.EditApproximation.BinaryFraction.finiteOptimizerWithWork (vertices.map Prod.snd) linear G j
  let gradient := OAI.EditApproximation.BinaryFraction.gradientWithWork G linear iterate.1
  let selected := OAI.EditApproximation.BinaryFraction.scoredArgmaxWithWork (fun vertex => OAI.EditApproximation.BinaryFraction.dotWithWork gradient.1 vertex.2) vertices
  (selected.1.map fun chosen => chosen.1.1, iterate.2 + gradient.2 + selected.2 + 1)

end OAI.EditApproximation.BinaryFraction

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation.BitQuery

def value {ι : Type u_1} {β : Type u_2} (oracle : ι → OAI.EditApproximation.BinaryFraction) : OAI.EditApproximation.BitQuery ι β → β
  | .done result => result
  | .read key next => value oracle (next (oracle key))
  | .charge _ next => value oracle next

def work {ι : Type u_1} {β : Type u_2} (oracle : ι → OAI.EditApproximation.BinaryFraction) (readWork : ι → ℕ) : OAI.EditApproximation.BitQuery ι β → ℕ
  | .done _ => 0
  | .read key next => readWork key + work oracle readWork (next (oracle key))
  | .charge steps next => steps + work oracle readWork next

def bind {ι : Type u_1} {α : Type u_2} {β : Type u_3} : OAI.EditApproximation.BitQuery ι α → (α → OAI.EditApproximation.BitQuery ι β) → OAI.EditApproximation.BitQuery ι β
  | .done result, next => next result
  | .read key continuation, next => .read key (fun word => bind (continuation word) next)
  | .charge steps continuation, next => .charge steps (bind continuation next)

def compute {ι : Type u_1} {α : Type u_2} (execution : α × ℕ) : OAI.EditApproximation.BitQuery ι α :=
  .charge execution.2 (.done execution.1)

def mapKeysWithWork {ι : Type u_1} {κ : Type u_2} {β : Type u_3} (f : ι → κ × ℕ) : OAI.EditApproximation.BitQuery ι β → OAI.EditApproximation.BitQuery κ β
  | .done result => .done result
  | .read key next => .charge (f key).2
      (.read (f key).1 (fun word => mapKeysWithWork f (next word)))
  | .charge steps next => .charge steps (mapKeysWithWork f next)

def restrictWithWork {ι : Type u_1} (P : ι → Prop)
    (test : ι → Bool × ℕ) (htest : ∀ key, (test key).1 = true ↔ P key) :
    OAI.EditApproximation.BitQuery ι OAI.EditApproximation.BinaryFraction → OAI.EditApproximation.BitQuery {key // P key} OAI.EditApproximation.BinaryFraction
  | .done result => .done result
  | .charge steps next => .charge steps (restrictWithWork P test htest next)
  | .read key next => .charge (test key).2
      (if h : (test key).1 = true then
        .read ⟨key, (htest key).mp h⟩ (fun word => restrictWithWork P test htest (next word))
       else restrictWithWork P test htest (next (OAI.EditApproximation.BinaryFraction.nat 0)))

def runMemo {ι : Type u_1} {κ : Type u_2}
    (ask : ι → OAI.EditApproximation.BinaryMemo OAI.EditApproximation.BinaryFraction → OAI.EditApproximation.BitRecursiveMemoResult κ) :
    OAI.EditApproximation.BitQuery ι OAI.EditApproximation.BinaryFraction → OAI.EditApproximation.BinaryMemo OAI.EditApproximation.BinaryFraction → OAI.EditApproximation.BitRecursiveMemoResult κ
  | .done result, memory => ⟨result, memory, [], 0, 0, 0⟩
  | .read key next, memory =>
    let first := ask key memory
    let rest := runMemo ask (next first.value) first.memory
    ⟨rest.value, rest.memory, first.freshKeys ++ rest.freshKeys,
      first.dictionaryVisits + rest.dictionaryVisits, first.requests + rest.requests,
      first.localWork + rest.localWork⟩
  | .charge steps next, memory =>
    let rest := runMemo ask next memory
    {rest with localWork := steps + rest.localWork}

inductive Footprint {ι : Type u_1} {β : Type u_2} : OAI.EditApproximation.BitQuery ι β → Type _ where
  | done (value : β) : Footprint (.done value)
  | read (key : ι) (next : OAI.EditApproximation.BinaryFraction → OAI.EditApproximation.BitQuery ι β)
      (continuation : ∀ word, Footprint (next word)) : Footprint (.read key next)
  | charge {steps : ℕ} {next : OAI.EditApproximation.BitQuery ι β} (cells : ℕ)
      (continuation : Footprint next) : Footprint (.charge steps next)

def collect {ι : Type u_1} {κ : Type u_2} {β : Type u_3} (reader : κ → OAI.EditApproximation.BitQuery ι OAI.EditApproximation.BinaryFraction) :
    List κ → (List OAI.EditApproximation.BinaryFraction → OAI.EditApproximation.BitQuery ι β) → OAI.EditApproximation.BitQuery ι β
  | [], next => next []
  | key :: rest, next => (reader key).bind (fun word =>
      .charge 3 (collect reader rest (fun words => next (word :: words))))

def normalize {ι : Type u_1} (program : OAI.EditApproximation.BitQuery ι OAI.EditApproximation.BinaryFraction)
    (base : List Bool) (hbase : 0 < OAI.EditApproximation.bitWordValue base) (remaining : ℕ) :
    OAI.EditApproximation.BitQuery ι OAI.EditApproximation.BinaryFraction :=
  program.bind fun word => OAI.EditApproximation.BitQuery.compute (OAI.EditApproximation.BinaryFraction.finishCachedWithWork (word, 0) base hbase remaining)

end OAI.EditApproximation.BitQuery

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

open EditDistortion

def substring {α : Type u} (word : List α) (lo hi : ℕ) : List α :=
  (word.take hi).drop lo

structure TargetInterval (length : ℕ) where
  lo : ℕ
  hi : ℕ
  ordered : lo ≤ hi
  valid : hi ≤ length

def occurrenceDeficit {α : Type u} [DecidableEq α] (a : α) (word : List α) : ℕ :=
  word.length - if a ∈ word then 1 else 0

def natListMinimum (fallback : ℕ) : List ℕ → ℕ
  | [] => fallback
  | first :: rest => min first (natListMinimum fallback rest)

def coarsePadTo {α : Type u} (n : ℕ) (word : List α) : List (Option α) :=
  word.map some ++ List.replicate (n - word.length) none

def connectionBudget {n : ℕ} (start : ℕ) (states : List (OAI.EditApproximation.TargetInterval n))
    (finish : ℕ) : ℕ :=
  match states with
  | [] => Nat.dist start finish
  | state :: rest => Nat.dist start state.lo + connectionBudget state.hi rest finish

def singletonCost {α : Type u} [DecidableEq α] (a : α) (word : List α) : ℕ :=
  if word = [] then 1 else OAI.EditApproximation.occurrenceDeficit a word

def makeTargetState (n lo hi : ℕ) : Option (OAI.EditApproximation.TargetInterval n) :=
  if h : lo ≤ hi ∧ hi ≤ n then some ⟨lo, hi, h.1, h.2⟩ else none

def targetEndpointDistance {n : ℕ} (q r : OAI.EditApproximation.TargetInterval n) : ℕ :=
  Nat.dist q.lo r.lo + Nat.dist q.hi r.hi

def targetStates (n : ℕ) : List (OAI.EditApproximation.TargetInterval n) :=
  (List.range (n + 1)).flatMap fun lo =>
    (List.range (n + 1)).filterMap fun hi => OAI.EditApproximation.makeTargetState n lo hi

def shortSourceCost {α : Type u_1} [DecidableEq α] (source target : List α) : ℕ :=
  match source with
  | [] => target.length
  | a :: _ => OAI.EditApproximation.singletonCost a target

def exactSuffixDP {α : Type u_1} [DecidableEq α] : List α → List α → List ℕ
  | [], target => List.ofFn fun j : Fin (target.length + 1) => target.length - j.val
  | a :: rest, target =>
    let previous := exactSuffixDP rest target
    List.ofFn fun j : Fin (target.length + 1) =>
      OAI.EditApproximation.natListMinimum (OAI.EditApproximation.singletonCost a [] + previous.getD j.val 0)
        ((List.range (target.length - j.val + 1)).map fun k =>
          OAI.EditApproximation.singletonCost a ((target.drop j.val).take k) + previous.getD (j.val + k) 0)

def exactSuffixAnswer {α : Type u_1} [DecidableEq α] (source target : List α) : ℕ :=
  (OAI.EditApproximation.exactSuffixDP source target).getD 0 0

end OAI.EditApproximation

end


