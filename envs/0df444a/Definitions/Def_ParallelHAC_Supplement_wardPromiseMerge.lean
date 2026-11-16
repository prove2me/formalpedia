-- Prove2me | Definitions.Def_ParallelHAC_Supplement_wardPromiseMerge
-- name    : ParallelHAC_Supplement_wardPromiseMerge
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:32:50.13048+00:00
-- url     : https://prove2.me/theorems/a2091c6e-c509-4c61-bb0c-93bfc4f9a430
-- title:
--   $(1+\gamma/n)$-approximate promise merge HAC with $d_{\mathrm{Ward}}$ (Definition 8)
-- statement:
--   An instance consists of a dimension $k$, a list of $n$ pairwise distinct points of $\mathbb R^k$ with rational coordinates, and two distinct designated points $a,b$ among them; $P\subseteq\mathbb R^k$ is the point set. It is written as a bit string: the self-delimiting binary codes of $k$, $n$, then for each point and coordinate a sign bit, a numerator and a positive denominator, then the positions of $a$ and $b$.
--
--   The cluster $\{a,b\}$ **appears** in a HAC run if some merge $i\in\{1,\dots,n-1\}$ merges two clusters whose union is $\{a,b\}$.
--
--   For constants $\gamma$, $c_D$ and $A$, the promise problem **$(1+\gamma/n)$-approximate promise merge HAC with $d_{\mathrm{Ward}}$** has as domain the encodings of instances with
--   1. $n\ge2$ points,
--   2. dimension $k\le c_D\log_2 n$,
--   3. constant aspect ratio: every $d_{\mathrm{Ward}}(\{u\},\{v\})$ with $u\ne v$ is positive and at most $A$ times every other such value,
--   4. the promise that $\{a,b\}$ appears in every $(1+\gamma/n)$-approximate HAC run for $d_{\mathrm{Ward}}$ on $P$, or in none of them.
--
--   The answer is YES when $\{a,b\}$ appears in every such run.
--
--   This is Definition 8 with $\varepsilon=\gamma/n$, restricted to $\mathbb R^{O(\log n)}$ and constant aspect ratio, the problem of Theorem 8.
--
--   **Formalization Note** HAC runs are the base mission's `ParallelHAC.HACRun` (every tie-breaking). Rational coordinates are what the reduction of §6 outputs (p.50); $n$ is the number of points, not the length of the string.
-- source:
--   Bateni, Dhulipala, Fletcher, Gowda, Hershkowitz, Jayaram, Łącki, Parallel Hierarchical Agglomerative Clustering in Low Dimensions, arXiv:2507.20047 (sha256 a21061c8…), §2.5, Definition 8 and Theorem 8, p.13 (PDF p.16); §6, p.50 (PDF p.53)

import Mathlib
import Definitions.Def_ArrighiStarFree_HalfLevel_SpaceMachine
import Definitions.Def_ParallelHAC_HACRun
import Definitions.Def_ParallelHAC_Supplement_wardLinkage
import Definitions.Def_ParallelHAC_Supplement_CCV

namespace ParallelHAC.Supplement

open ArrighiStarFree.HalfLevel

/-!
# (1 + ε)-approximate promise merge HAC with Ward's linkage (Definition 8, Theorem 8)

Source: arXiv:2507.20047 (sha256 a21061c8…), §2.5, Definition 8 and Theorem 8, printed p.13
(PDF p.16); proof §6, printed pp.42–50 (PDF pp.45–53).

**Formalization Note.** A HAC instance is given as a bit string. Its points have rational
coordinates, each written as a sign bit, a numerator and a positive denominator in binary. This
is what the reduction of §6 outputs: on p.50 every coordinate is rounded to inverse-polynomial
precision with `O(log N)`-bit arithmetic. The constants `γ` (approximation), `cD` (dimension
`k ≤ cD log₂ n`, i.e. `ℝ^{O(log n)}`) and `A` (constant aspect ratio) are parameters, fixed before
the input. `n` is the number of points, not the length of the encoding.
-/

/-- A rational number written as `(−1)^neg · num / den`. -/
structure RatCode where
  /-- Sign bit (`true` = negative). -/
  neg : Bool
  /-- Numerator. -/
  num : ℕ
  /-- Denominator (positive in a well-formed instance). -/
  den : ℕ

/-- The value `(−1)^neg · num / den`. -/
noncomputable def RatCode.val (q : RatCode) : ℝ :=
  (if q.neg then -1 else 1) * (q.num : ℝ) / q.den

/-- An encoded instance of promise merge HAC: the dimension `k`, the list of points (each a list
of `k` rational coordinates), and the list positions `ia`, `ib` of the two designated points
`a, b` (0-based). -/
structure WardInstance where
  /-- The dimension `k`. -/
  dim : ℕ
  /-- The points, as coordinate lists. -/
  points : List (List RatCode)
  /-- Position of `a` in `points`. -/
  ia : ℕ
  /-- Position of `b` in `points`. -/
  ib : ℕ

/-- The point of `ℝ^k` with the given coordinate list. -/
noncomputable def WardInstance.point (I : WardInstance) (p : List RatCode) :
    EuclideanSpace ℝ (Fin I.dim) :=
  WithLp.toLp 2 (fun i => (p.getD i ⟨false, 0, 1⟩).val)

/-- The point set `P ⊆ ℝ^k` of the instance. -/
noncomputable def WardInstance.pointSet (I : WardInstance) :
    Finset (EuclideanSpace ℝ (Fin I.dim)) :=
  (I.points.map I.point).toFinset

/-- The designated point `a`. -/
noncomputable def WardInstance.a (I : WardInstance) : EuclideanSpace ℝ (Fin I.dim) :=
  I.point (I.points.getD I.ia [])

/-- The designated point `b`. -/
noncomputable def WardInstance.b (I : WardInstance) : EuclideanSpace ℝ (Fin I.dim) :=
  I.point (I.points.getD I.ib [])

/-- Well-formed: every point has `k` coordinates with positive denominators, the points are
pairwise distinct (so `n = |P|` is the length of the list), and `a, b` are two distinct listed
points. -/
def WardInstance.WellFormed (I : WardInstance) : Prop :=
  (∀ p ∈ I.points, p.length = I.dim ∧ ∀ q ∈ p, 0 < q.den) ∧
  (I.points.map I.point).Nodup ∧
  I.ia < I.points.length ∧ I.ib < I.points.length ∧ I.ia ≠ I.ib

/-- The encoding: the codes of `k`, `n`, then for each point and each coordinate the sign
(`0`/`1`), numerator and denominator, then `ia` and `ib`. -/
def WardInstance.encode (I : WardInstance) : List Bool :=
  encodeNats ([I.dim, I.points.length] ++
    I.points.flatMap (fun p => p.flatMap (fun q => [if q.neg then 1 else 0, q.num, q.den])) ++
    [I.ia, I.ib])

/-- **The cluster `{a, b}` appears in the run** (Definition 8): some merge `i ∈ [1, n − 1]`
produces exactly the cluster `A_i ∪ B_i = {a, b}`. -/
def MergesPair {V : Type*} [DecidableEq V] {P : Finset V} {d : Finset V → Finset V → ℝ}
    {c : ℝ} (R : ParallelHAC.HACRun P d c) (a b : V) : Prop :=
  ∃ i, 1 ≤ i ∧ i ≤ P.card - 1 ∧ R.A i ∪ R.B i = {a, b}

/-- The instance has **constant aspect ratio** `≤ A` for Ward's linkage (p.7): every Ward's
linkage between distinct points is positive, and any two such linkages are within factor `A`. -/
def WardInstance.AspectLE (I : WardInstance) (A : ℝ) : Prop :=
  (∀ u ∈ I.pointSet, ∀ v ∈ I.pointSet, u ≠ v → 0 < wardLinkage I.dim {u} {v}) ∧
  ∀ u ∈ I.pointSet, ∀ v ∈ I.pointSet, ∀ w ∈ I.pointSet, ∀ x ∈ I.pointSet, u ≠ v → w ≠ x →
    wardLinkage I.dim {u} {v} ≤ A * wardLinkage I.dim {w} {x}

/-- **(1 + γ/n)-approximate promise merge HAC with `d_Ward` in `ℝ^{O(log n)}`, constant aspect
ratio** (Definition 8 with `ε = γ/n`, p.13), as a promise problem on bit strings. The domain is
the set of encodings of well-formed instances with `n ≥ 2` points, dimension `k ≤ cD · log₂ n`,
aspect ratio at most `A`, and the promise that the cluster `{a, b}` appears in every
`(1 + γ/n)`-approximate HAC run for `d_Ward`, or in none of them. The answer is YES when it
appears in every run.
Source: arXiv:2507.20047 (sha256 a21061c8…), Definition 8 and Theorem 8, printed p.13
(PDF p.16). -/
noncomputable def wardPromiseMerge (γ cD A : ℝ) : PromiseProblem where
  domain := {x | ∃ I : WardInstance, I.WellFormed ∧ I.encode = x ∧
    2 ≤ I.points.length ∧
    (I.dim : ℝ) ≤ cD * Real.logb 2 I.points.length ∧
    I.AspectLE A ∧
    ((∀ R : ParallelHAC.HACRun I.pointSet (wardLinkage I.dim) (1 + γ / I.points.length),
        MergesPair R I.a I.b) ∨
      (∀ R : ParallelHAC.HACRun I.pointSet (wardLinkage I.dim) (1 + γ / I.points.length),
        ¬ MergesPair R I.a I.b))}
  answer := fun x => ∃ I : WardInstance, I.WellFormed ∧ I.encode = x ∧
    ∀ R : ParallelHAC.HACRun I.pointSet (wardLinkage I.dim) (1 + γ / I.points.length),
      MergesPair R I.a I.b

end ParallelHAC.Supplement


