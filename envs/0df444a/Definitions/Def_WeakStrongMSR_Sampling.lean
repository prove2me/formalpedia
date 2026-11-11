-- Prove2me | Definitions.Def_WeakStrongMSR_Sampling
-- name    : WeakStrongMSR_Sampling
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T08:27:38.546+00:00
-- url     : https://prove2.me/theorems/3ce75e67-83c1-45c0-81cd-cc308414effd
-- title:
--   The sampling step (§3.1.1, Algorithm 1)
-- statement:
--   Sampling starts from $S=\emptyset$ and $\mathcal C=\emptyset$ and performs at most $ck$ rounds. Before each round, if $|X\setminus S|\le ckh$ it strongly queries all remaining points and stops. A round does the following.
--
--   1. Solve LP (1) to obtain $y$.
--   2. Draw $h$ independent points with probabilities proportional to $y$.
--   3. Strongly query the distinct new points $Q$ and append them to $S$ in order of first appearance.
--   4. If $|S|\ge h+1$, give each $s\in Q$ the witness set $W_s$ of its $h$ nearest points in $S\setminus\{s\}$ (exact distances, ties by insertion order).
--   5. For every distinct $R\in\{\mathrm{md}(x,s):x\notin S_{\mathrm{old}}\}$, add $(A,s,R)$ with $A=\{x\notin S_{\mathrm{old}}:\mathrm{md}(x,s)\le R\}$ whenever $y(A)>R+\lambda$ (Eq. (4)).
--   6. Intersect every stored set with the new $X\setminus S$.
--
--   $E=\bigcup_sE_s$ is the set of points corrupt for the witness set of some sampled centre (Definition 3.2).
--
--   **Formalization Note** The number of strong queries of sampling is the length of the final strong set. A draw from a vector with no positive weight outside $S$ draws nothing; this never happens for an optimal LP solution while points remain. Remaining points are queried in index order, and candidate radii are processed in increasing order.
-- source:
--   Friggstad–Jamshidian–Vakilian, Minimum Sum-of-Radii Clustering with Strong and Weak Oracles (manuscript, STOC 2027 submission, sha256 5f8fbaf3…67e8f92a0), §3.1.1, pp.8–9 (PDF 9–10), Algorithm 1, p.9 (PDF 10); Definition 3.2, p.10 (PDF 11)

import Mathlib
import Definitions.Def_WeakStrongMSR_Model
import Definitions.Def_WeakStrongMSR_Estimates
import Definitions.Def_WeakStrongMSR_Draws
import Definitions.Def_WeakStrongMSR_LP

open scoped Classical

set_option autoImplicit false

namespace WeakStrongMSR

/-!
# The sampling step (§3.1.1, Algorithm 1)

Friggstad–Jamshidian–Vakilian, *Minimum Sum-of-Radii Clustering with Strong and Weak Oracles*
(manuscript, sha256 5f8fbaf3…67e8f92a0), §3.1.1, pp.8–9 and Algorithm 1, p.9: "Initially S = ∅ and
C = ∅. We perform at most ck rounds, stopping earlier if |X \ S| ≤ ckh; in that case we strongly
query all remaining points. In a round, solve (1), independently draw h points with replacement
with probabilities proportional to an optimal solution y, and let Q be the set of distinct drawn
points. Strongly query Q and add it to S." Witness sets: "the h nearest points to s in S \ {s},
breaking ties by insertion order in S"; candidates (4): add `(A, s, R)` with
`A = {x ∈ X \ S_old : md(x, s) ≤ R}` for each distinct `R ∈ {md(x, s) : x ∈ X \ S_old}` with
`y(A) > R + λ`; line 10: "Replace every stored (A, s, R) by (A ∩ (X \ S), s, R)". Definition 3.2:
`E = ⋃_s E_s` over the sampled centres with witness sets.

This module bundles the state, one round, the loop and the law of the sampling step.

**Formalization Note.**
* The strong set is a list in insertion order (each point once); the number of strong queries of
  sampling is its length (each test starts from an empty strong set, §3 p.6).
* The check "`|X ∖ S| ≤ ckh`" is made before each of the at most `ck` rounds; after `ck` rounds
  sampling stops. "Query all remaining points" inserts them in index order (R12).
* A draw is an `Option (Fin n)`: with an LP solution `y` of positive total weight on `X ∖ S` the
  draw is `x ∉ S` with probability `y_x / ∑ y`; otherwise (never, when `y` is optimal and
  `X ∖ S ≠ ∅`) the draw is `none` and queries nothing.
* `Q` lists the distinct drawn points in order of first appearance; the candidate radii are
  processed in increasing order. The witness set `W_s` of each sampled centre is recorded (in the
  candidates and in `wit`) to name the sets `E_s` of Definition 3.2. -/

/-- The state of the sampling step. -/
structure SampState (n : ℕ) where
  /-- The strong set, in insertion order. -/
  S : List (Fin n)
  /-- The candidate family `C`. -/
  cands : List (Cand n)
  /-- Every sampled centre that received a witness set, with its witness set `W_s`. -/
  wit : List (Fin n × Finset (Fin n))
  /-- Whether the remaining points have been queried (sampling stopped early). -/
  done : Bool

/-- The unnormalized draw weights: `y_x` on points outside `S`, `0` on `S` and on `none`. -/
noncomputable def drawWeight {n : ℕ} (S : List (Fin n)) (y : Fin n → ℝ) :
    Option (Fin n) → ENNReal
  | some x => if x ∈ S then 0 else ENNReal.ofReal (y x)
  | none => 0

/-- One draw with probabilities proportional to `y` on `X ∖ S` (`none` if `y` has no positive
weight there). -/
noncomputable def drawLaw {n : ℕ} (S : List (Fin n)) (y : Fin n → ℝ) : PMF (Option (Fin n)) :=
  if h : ∑' o, drawWeight S y o ≠ 0 then
    PMF.normalize (drawWeight S y) h (by
      rw [tsum_fintype]
      refine ENNReal.sum_ne_top.2 (fun o _ => ?_)
      cases o with
      | none => simp [drawWeight]
      | some x => simp only [drawWeight]; split_ifs <;> simp)
  else PMF.pure none

/-- The points of `l` not in `S`, without repetition, in order of first appearance. -/
def newDistinct {n : ℕ} (S l : List (Fin n)) : List (Fin n) :=
  l.foldl (fun acc x => if x ∈ S ∨ x ∈ acc then acc else acc ++ [x]) []

/-- The witness set of `s`: the `h` nearest points to `s` in `S ∖ {s}` by exact distance, ties
broken by insertion order (stable sort). -/
noncomputable def witnessList {n : ℕ} (d : Fin n → Fin n → ℝ) (S : List (Fin n)) (s : Fin n)
    (h : ℕ) : List (Fin n) :=
  ((S.filter (· ≠ s)).mergeSort (fun a b => decide (d s a ≤ d s b))).take h

/-- The candidates added at the sampled centre `s` with witness set `W` (Algorithm 1, lines 7–9):
for each distinct `R ∈ {md(x, s) : x ∉ S_old}` in increasing order, `A = {x ∉ S_old : md(x, s) ≤ R}`
is added if `y(A) > R + λ`. Here `S'` is the strong set after the round's queries. -/
noncomputable def roundCands {n : ℕ} (d w : Fin n → Fin n → ℝ) (lam : ℝ) (y : Fin n → ℝ)
    (Sold S' : List (Fin n)) (s : Fin n) (W : Finset (Fin n)) : List (Cand n) :=
  let rest := Finset.univ.filter (fun x => x ∉ Sold)
  let md := mdEst d w S'.toFinset s W
  ((rest.image md).sort (· ≤ ·)).filterMap (fun R =>
    let A := rest.filter (fun x => md x ≤ R)
    if R + lam < ∑ x ∈ A, y x then some ⟨A, s, R, W⟩ else none)

/-- One sampling round (Algorithm 1) with the LP routine `sel`. -/
noncomputable def sampleRound {n : ℕ} (sel : LPSelector n) (d w : Fin n → Fin n → ℝ) (h : ℕ)
    (lam : ℝ) (st : SampState n) : PMF (SampState n) :=
  let y := sel st.S.toFinset st.cands lam h
  (iidDraws (drawLaw st.S y) h).map (fun draws =>
    let Q := newDistinct st.S (draws.filterMap id)
    let S' := st.S ++ Q
    let ws : List (Fin n × Finset (Fin n)) :=
      if h + 1 ≤ S'.length then Q.map (fun s => (s, (witnessList d S' s h).toFinset)) else []
    let newC := ws.flatMap (fun p => roundCands d w lam y st.S S' p.1 p.2)
    { S := S'
      cands := (st.cands ++ newC).map (fun c => { c with A := c.A.filter (· ∉ S') })
      wit := st.wit ++ ws
      done := false })

/-- Stop early: strongly query every remaining point, in index order. -/
def sampleFinish {n : ℕ} (st : SampState n) : SampState n :=
  { st with S := st.S ++ (List.finRange n).filter (· ∉ st.S), done := true }

/-- The sampling loop with `r` rounds left. -/
noncomputable def sampleLoop {n : ℕ} (c k h : ℕ) (lam : ℝ) (sel : LPSelector n)
    (d w : Fin n → Fin n → ℝ) : ℕ → SampState n → PMF (SampState n)
  | 0, st => PMF.pure st
  | r + 1, st =>
      if st.done then PMF.pure st
      else if (Finset.univ.filter (fun x => x ∉ st.S)).card ≤ c * k * h then
        PMF.pure (sampleFinish st)
      else (sampleRound sel d w h lam st).bind (sampleLoop c k h lam sel d w r)

/-- The law of the output of the sampling step: at most `ck` rounds from `S = ∅`, `C = ∅`. -/
noncomputable def sampleLaw {n : ℕ} (c k h : ℕ) (lam : ℝ) (sel : LPSelector n)
    (d w : Fin n → Fin n → ℝ) : PMF (SampState n) :=
  sampleLoop c k h lam sel d w (c * k) ⟨[], [], [], false⟩

/-- `E = ⋃_s E_s`: the points corrupt for the witness set of some sampled centre
(Definition 3.2), for the corruption set `C`. -/
noncomputable def sampleE {n : ℕ} (C : Finset (Sym2 (Fin n))) (st : SampState n) :
    Finset (Fin n) :=
  st.wit.toFinset.biUnion (fun p => corruptSet C p.2)

end WeakStrongMSR


