-- Prove2me | Definitions.Def_FixedMachinePrec_EvaluateFamily
-- name    : FixedMachinePrec_EvaluateFamily
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:05:55.2017+00:00
-- url     : https://prove2.me/theorems/ed7263ea-6681-477c-b918-a752e396f6b6
-- title:
--   Algorithms 2–5: lookup, states of a parent, the reachability pass, reconstruction, and EvaluateFamily
-- statement:
--   Fix finite families $\mathcal F$ (candidate sets) and $\mathcal F_{\mathrm{cut}}$ (cuts). The **family table** stores for each $X\in\mathcal F$ a bit $a(X)$ and a schedule $\sigma(X)$; initially all bits are $0$ except $a(\emptyset)=1$, $\sigma(\emptyset)=()$.
--
--   1. **Lookup** (Algorithm 2): $\mathrm{Lookup}(X)=a(X)$ if $X\in\mathcal F$ and $0$ otherwise; Fetch returns $\sigma(X)$.
--   2. **BuildStates** (Algorithm 3): for each cut $C\in\mathcal F_{\mathrm{cut}}$ in vector order, put $L=W\cap C$ and skip unless $m\mid|L|$; for each $m$-subset $Z\subseteq W\setminus L$ in the fixed subset order put $R=W\setminus(L\cup Z)$ and append the **state** $(L,Z,R)$ exactly when $m\mid|R|$, $Z$ is an antichain, and $L$ and $L\cup Z$ are ideals of $W$. Duplicates are kept.
--   3. **Edges** (2): $i\to j$ iff $L_i\cup Z_i\subseteq L_j$ and $\mathrm{Lookup}(L_j\setminus(L_i\cup Z_i))=1$. A state is *initial* if $\mathrm{Lookup}(L_i)=1$ and *final* if $\mathrm{Lookup}(R_i)=1$.
--   4. **Reachability pass** (Algorithm 4, Steps 3–4): initial records are reached with predecessor START; indices are bucketed stably by $|L_i|$ and processed in increasing order; each reached source scans all targets once and marks every unreached target $j$ with $i\to j$, setting its predecessor to $i$.
--   5. **Reconstruct** (Algorithm 5): from a reached final record $t$, follow predecessors back to START and concatenate $\mathrm{Fetch}(L_{i_1}),Z_{i_1},\mathrm{Fetch}(L_{i_2}\setminus(L_{i_1}\cup Z_{i_1})),\dots,Z_{i_k},\mathrm{Fetch}(R_{i_k})$.
--   6. **EvaluateFamily** (Algorithm 4): process the nonempty rows of $\mathcal F$ in the order $(|X|,b_N\cdots b_1)$, skipping rows with $m\nmid|X|$; for a parent $W$, at the *first* reached final record set $a(W)=1$ and store the reconstructed schedule.
--
--   **Formalization Note** Records are indexed from $0$. A table maps every subset to an optional list of slots; only rows of $\mathcal F$ are written.
-- source:
--   K. Jansen, Precedence Constraint Scheduling on a Fixed Number of Machines, manuscript dated 1 November 2026 (sha256 08cdf3e1…), §3.1, pp.7–8, Definition 3.1, Algorithms 2–5 and (2), pp.8–9

import Mathlib
import Definitions.Def_FixedMachinePrec_FullSchedule
import Definitions.Def_FixedMachinePrec_FixedOrders

namespace FixedMachinePrec

/-- A state record `(L, Z, R)` of one parent `W` (Definition 3.1, p.7). -/
structure StateRec (N : ℕ) where
  /-- the prefix `L = W ∩ C` -/
  L : Finset (Fin N)
  /-- the marked full slot `Z`, `|Z| = m` -/
  Z : Finset (Fin N)
  /-- the remaining suffix `R = W \ (L ∪ Z)` -/
  R : Finset (Fin N)

/-- The family table: `σ(X) = some S` means `a(X) = 1` with stored full schedule `S`; `none` means
`a(X) = 0`, `σ(X) = ⊥` (§3.1, p.7). -/
abbrev Table (N : ℕ) := Finset (Fin N) → Option (List (Finset (Fin N)))

/-- The predecessor field of a state record: `UNREACHED`, `START`, or a predecessor index. -/
inductive PredField where
  | unreached
  | start
  | pred (i : ℕ)
  deriving DecidableEq

/-- **Algorithm 2, Lookup** (p.8): the stored value of the row of `X` if `X ∈ F`, and nothing
otherwise (`Lookup(X) = a(X)` for `X ∈ F`, `0` for `X ∉ F`); `Fetch(X)` is the stored schedule. -/
def lookup {N : ℕ} (F : Finset (Finset (Fin N))) (tab : Table N) (X : Finset (Fin N)) :
    Option (List (Finset (Fin N))) :=
  if X ∈ F then tab X else none

/-- **Algorithm 3, BuildStates(W, F_cut, m)** (p.8): for each `C ∈ F_cut` in lexicographic vector
order, `L = W ∩ C` (skipped unless `m ∣ |L|`); for each `m`-subset `Z` of `W \ L` in the fixed
subset order, `R = W \ (L ∪ Z)`, and `(L, Z, R)` is appended exactly when `m ∣ |R|`,
`Antichain(Z)`, `Ideal(L, W)` and `Ideal(L ∪ Z, W)`. Duplicate triples from different cuts are
kept. -/
def buildStates {N : ℕ} (prec : Fin N → Fin N → Prop) [DecidableRel prec] (m : ℕ)
    (Fcut : Finset (Finset (Fin N))) (W : Finset (Fin N)) : List (StateRec N) :=
  (listByCode Fcut).flatMap fun C =>
    let L := W ∩ C
    if m ∣ L.card then
      ((mSubsetsLex N m).filter fun Z => decide (Z ⊆ W \ L)).filterMap fun Z =>
        let R := W \ (L ∪ Z)
        if m ∣ R.card ∧ (∀ x ∈ Z, ∀ y ∈ Z, ¬ prec x y) ∧ (∀ x ∈ L, ∀ y ∈ W, prec y x → y ∈ L) ∧
            (∀ x ∈ L ∪ Z, ∀ y ∈ W, prec y x → y ∈ L ∪ Z) then
          some ⟨L, Z, R⟩
        else none
    else []

/-- The edge test (2), p.8: `i → j` iff `L_i ∪ Z_i ⊆ L_j` and `Lookup(L_j \ (L_i ∪ Z_i)) = 1`,
for a lookup answer `lk` (`lk X = true` iff `Lookup(X) = 1`). -/
def edge {N : ℕ} (st : List (StateRec N)) (lk : Finset (Fin N) → Bool) (i j : ℕ) : Bool :=
  match st[i]?, st[j]? with
  | some a, some b => decide (a.L ∪ a.Z ⊆ b.L) && lk (b.L \ (a.L ∪ a.Z))
  | _, _ => false

/-- **Steps 3–4 of Algorithm 4** (p.9) on the state list `st` of one parent, with the lookup
answers `lk` fixed. Step 3: record `i` is reached with predecessor `START` iff
`Lookup(L_i) = 1`. Step 4: the indices are bucketed stably by `|L_i|` and the buckets processed
in increasing order; for each source `i` that is reached when its turn comes, the targets
`j = 1, …, s` are inspected once and, if `reached[j] = 0` and (2) holds, `reached[j] := 1`,
`pred[j] := i`, effective immediately. Returns `(reached, pred)`.

**Formalization Note** Record indices are 0-based (`0, …, s − 1`). -/
def reachPass {N : ℕ} (st : List (StateRec N)) (lk : Finset (Fin N) → Bool) :
    (ℕ → Bool) × (ℕ → PredField) :=
  let s := st.length
  let r0 : ℕ → Bool := fun i => match st[i]? with | some a => lk a.L | none => false
  let p0 : ℕ → PredField := fun i => if r0 i then .start else .unreached
  let order : List ℕ := (List.range (N + 1)).flatMap fun c =>
    (List.range s).filter fun i => match st[i]? with | some a => a.L.card = c | none => false
  order.foldl
    (fun (rp : (ℕ → Bool) × (ℕ → PredField)) i =>
      if rp.1 i then
        (List.range s).foldl
          (fun (rp : (ℕ → Bool) × (ℕ → PredField)) j =>
            if !rp.1 j && edge st lk i j then
              (Function.update rp.1 j true, Function.update rp.2 j (.pred i))
            else rp)
          rp
      else rp)
    (r0, p0)

/-- Follow predecessor fields backward from `i` until a record with predecessor `START`, with at
most `fuel` records; returns the path `i₁, …, i_k` in forward order (Algorithm 5, Step 1, p.9). -/
def tracePath (p : ℕ → PredField) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | fuel + 1, i =>
    match p i with
    | .start => [i]
    | .pred j => tracePath p fuel j ++ [i]
    | .unreached => []

/-- The pieces after the initial prefix in Algorithm 5, Steps 3–4: for the path `i₁, …, i_k`,
`Z_{i_1}, Fetch(L_{i_2} \ (L_{i_1} ∪ Z_{i_1})), Z_{i_2}, …, Z_{i_k}, Fetch(R_{i_k})`. -/
def assemble {N : ℕ} (st : List (StateRec N)) (fetch : Finset (Fin N) → List (Finset (Fin N))) :
    List ℕ → List (Finset (Fin N))
  | [] => []
  | [i] =>
    match st[i]? with
    | some a => [a.Z] ++ fetch a.R
    | none => []
  | i :: j :: rest =>
    match st[i]?, st[j]? with
    | some a, some b => [a.Z] ++ fetch (b.L \ (a.L ∪ a.Z)) ++ assemble st fetch (j :: rest)
    | _, _ => []

/-- **Algorithm 5, Reconstruct(t, S_W)** (p.9): follow the predecessor fields back from `t`, then
concatenate `Fetch(L_{i_1})`, `Z_{i_1}`, `Fetch(L_{i_2} \ (L_{i_1} ∪ Z_{i_1}))`, …, `Z_{i_k}`,
`Fetch(R_{i_k})`. -/
def reconstruct {N : ℕ} (st : List (StateRec N)) (fetch : Finset (Fin N) → List (Finset (Fin N)))
    (p : ℕ → PredField) (t : ℕ) : List (Finset (Fin N)) :=
  let path := tracePath p st.length t
  match path with
  | [] => []
  | i :: _ =>
    match st[i]? with
    | some a => fetch a.L ++ assemble st fetch path
    | none => []

/-- Steps 3–5 of Algorithm 4 for one parent `W` on the current table: build the states, run the
reachability pass, and, at the first record `t` with `reached[t] = 1` and `Lookup(R_t) = 1`, set
`a(W) = 1` and `σ(W) = Reconstruct(t, S_W)`; otherwise leave `(W, 0, ⊥)`. -/
def processParent {N : ℕ} (prec : Fin N → Fin N → Prop) [DecidableRel prec] (m : ℕ)
    (F Fcut : Finset (Finset (Fin N))) (tab : Table N) (W : Finset (Fin N)) : Table N :=
  let st := buildStates prec m Fcut W
  let lk : Finset (Fin N) → Bool := fun X => (lookup F tab X).isSome
  let fetch : Finset (Fin N) → List (Finset (Fin N)) := fun X => (lookup F tab X).getD []
  let rp := reachPass st lk
  match (List.range st.length).find? (fun i =>
      rp.1 i && match st[i]? with | some a => lk a.R | none => false) with
  | none => tab
  | some t => Function.update tab W (some (reconstruct st fetch rp.2 t))

/-- **Algorithm 4, EvaluateFamily(J, F, F_cut, m)** (Jansen, *Precedence Constraint Scheduling on a
Fixed Number of Machines*, manuscript, sha256 08cdf3e1…, Algorithm 4, p.9, with Algorithms 2, 3
and 5, pp.8–9): the rows of `F` are sorted by `(|X|, b_N ⋯ b_1)`; initially every value is `0`
except `a(∅) = 1`, `σ(∅) = ()`; the nonempty rows are processed in that order, a row whose
cardinality is not a multiple of `m` being skipped. Returns the final table.

**Formalization Note** A table maps every subset to `Option` of a list of slots (`none` is
`a = 0`, `σ = ⊥`); only rows of `F` are ever written, and Lookup answers `0` outside `F`. Slots are
`Finset`s, so "labels within each slot increasing" is the canonical listing of a slot. -/
def evaluateFamily {N : ℕ} (prec : Fin N → Fin N → Prop) [DecidableRel prec] (m : ℕ)
    (F Fcut : Finset (Finset (Fin N))) : Table N :=
  let tab0 : Table N := fun X => if X = ∅ ∧ (∅ : Finset (Fin N)) ∈ F then some [] else none
  (listByCardCode F).foldl
    (fun tab W => if W = ∅ ∨ ¬ m ∣ W.card then tab else processParent prec m F Fcut tab W)
    tab0

end FixedMachinePrec


