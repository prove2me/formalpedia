-- Prove2me | Definitions.Def_PerturbedWF_transNorm
-- name    : PerturbedWF_transNorm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T08:30:49.023191+00:00
-- url     : https://prove2.me/theorems/3d7fab32-0e2e-46ac-90ae-65cc54844765
-- title:
--   Finite metrics, the transportation norm $\|z\|$ (2.1) and the dual unit ball $B^*$
-- statement:
--   Let $[n]$ be a finite set of points and $d:[n]\times[n]\to\mathbb R$ a **metric**: $d(i,i)=0$, $d(i,j)=d(j,i)$, $d(i,k)\le d(i,j)+d(j,k)$, and $d(i,j)>0$ for $i\ne j$. Write $\langle v,x\rangle=\sum_i v_ix_i$ and $e_i$ for the $i$-th unit vector.
--
--   On the zero-sum vectors $Z=\{z\in\mathbb R^n:\sum_i z_i=0\}$ the metric induces the **transportation norm**
--   $$\|z\|=\min\Big\{\sum_{i,j\in[n]}d(i,j)f_{ij}\ :\ z=\sum_{i,j\in[n]}f_{ij}(e_j-e_i),\ f\in\mathbb R^{n\times n}_{\ge0}\Big\},\qquad(2.1)$$
--   where $f_{ij}$ is the mass moved from $i$ to $j$. For two configurations $x,y$ of equal total mass, $\|x-y\|$ is the cheapest way to redistribute the mass of $y$ into $x$.
--
--   The **dual unit ball** is $B^*=\{v\in\mathbb R^n:\|v\|^*\le1\}$, where $\|v\|^*=\sup_{\|z\|=1}|\langle v,z\rangle|$; by (2.2), $v\in B^*$ if and only if
--   $$|v_i-v_j|\le d(i,j)\qquad\text{for all } i,j\in[n].$$
--
--   These are the metric objects in which every cost of the mission is measured.
--
--   **Formalization Note.** The points form a finite type `ι`. `transNorm d z` is the real infimum of the set in (2.1): the set is nonempty exactly for zero-sum $z$ and bounded below by $0$ when $d\ge0$, so it is the paper's minimum there; on a vector that is not zero-sum the value is the junk value $0$, and the definition is only applied to differences of two configurations of equal mass. `dualBall d` is defined by the characterization $|v_i-v_j|\le d(i,j)$ (the right-hand side of the "if and only if" after (2.2)).
-- source:
--   Coester, Kashaev, Online Metric Problems via Randomly Perturbed Work Functions (STOC 2027 submission, held version, sha256 e2e30a44…), §2 'Configurations', 'Transportation norm', 'Dual (semi)norm', p.5 (PDF p.6), eq. (2.1) and the sentence after (2.2)

import Mathlib

namespace PerturbedWF

/-!
# Finite metrics, the transportation norm (2.1) and the dual unit ball

C. Coester, D. Kashaev, *Online Metric Problems via Randomly Perturbed Work Functions*, STOC 2027
submission (held version, sha256 e2e30a44…), §2, "Configurations", "Transportation norm" and
"Dual (semi)norm", p.5 (PDF p.6), eq. (2.1) and the sentence after (2.2).

**Formalization Note.**
* The points of the metric space are a finite type `ι` (the paper's `[n]`), and the metric is a
  function `d : ι → ι → ℝ`; `IsFinMetric d` says that `d` is a metric (zero on the diagonal,
  symmetric, triangle inequality, positive off the diagonal).
* `transNorm d z` is the infimum in (2.1) of the transport cost `∑ i j, d i j * F i j` over
  nonnegative flows `F` with `z = ∑ i j, F i j • (e_j − e_i)`. The set is nonempty exactly when `z`
  is a zero-sum vector, and for `d ≥ 0` it is bounded below by `0`, so the real `sInf` is the
  paper's minimum there. On a vector that is not zero-sum the set is empty and the value is the
  junk value `0`; the definition is only applied to differences of two configurations of equal
  total mass.
* `dualBall d` is the set of `v` with `|v i − v j| ≤ d i j` for all `i, j`. The paper defines
  `B* = {v : ‖v‖* ≤ 1}` and observes, via (2.2), that `v ∈ B*` iff `|v_i − v_j| ≤ d(i, j)` for
  every `i, j`; the right-hand side is taken as the definition.
* `dot v x = ∑ i, v i * x i` is the inner product `⟨v, x⟩`.
-/

/-- `d` is a metric on the finite set `ι`: zero on the diagonal, symmetric, triangle inequality,
and positive between distinct points. -/
def IsFinMetric {ι : Type} (d : ι → ι → ℝ) : Prop :=
  (∀ i, d i i = 0) ∧ (∀ i j, d i j = d j i) ∧ (∀ i j k, d i k ≤ d i j + d j k) ∧
    (∀ i j, i ≠ j → 0 < d i j)

/-- The inner product `⟨v, x⟩ = ∑ i, v i * x i` on `ℝ^ι`. -/
def dot {ι : Type} [Fintype ι] (v x : ι → ℝ) : ℝ := ∑ i, v i * x i

/-- The transportation norm (2.1): the cheapest cost `∑ i j, d(i, j) f_ij` of a nonnegative flow
`f` (`f_ij` is the mass moved from `i` to `j`) with `z = ∑ i j, f_ij (e_j − e_i)`.
Meaningful on zero-sum vectors (see the module note). -/
noncomputable def transNorm {ι : Type} [Fintype ι] [DecidableEq ι] (d : ι → ι → ℝ)
    (z : ι → ℝ) : ℝ :=
  sInf {c : ℝ | ∃ F : ι → ι → ℝ, (∀ i j, 0 ≤ F i j) ∧
    z = ∑ i, ∑ j, F i j • (Pi.single j (1 : ℝ) - Pi.single i (1 : ℝ)) ∧
    c = ∑ i, ∑ j, d i j * F i j}

/-- The dual unit ball `B*`, by its characterization `|v_i − v_j| ≤ d(i, j)` for all `i, j`. -/
def dualBall {ι : Type} (d : ι → ι → ℝ) : Set (ι → ℝ) :=
  {v | ∀ i j, |v i - v j| ≤ d i j}

end PerturbedWF


