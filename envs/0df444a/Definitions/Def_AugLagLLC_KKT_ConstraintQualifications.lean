-- Prove2me | Definitions.Def_AugLagLLC_KKT_ConstraintQualifications
-- name    : AugLagLLC_KKT_ConstraintQualifications
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T09:36:20.266185+00:00
-- url     : https://prove2.me/theorems/6b15b2cb-dad1-48d8-9bd1-b5d6836c4255
-- title:
--   KKT points, the CPLD condition and MFCQ for a smooth nonlinear program (pp. 2–3, 8)
-- statement:
--   This file fixes three textbook notions for a nonlinear program on $\mathbb R^n$,
--
--   $$\text{minimize } F(x)\quad\text{subject to}\quad H_i(x)=0\ (i\in\iota),\qquad G_j(x)\le 0\ (j\in\kappa),$$
--
--   where $\iota$ and $\kappa$ are finite index sets and $F$, $H_i$, $G_j:\mathbb R^n\to\mathbb R$. The gradient $\nabla$ is taken with respect to the Euclidean inner product $\langle\cdot,\cdot\rangle$.
--
--   1. **KKT point.** A point $x$ is a KKT point if it is feasible ($H_i(x)=0$ for all $i$, $G_j(x)\le 0$ for all $j$) and there are multipliers $a\in\mathbb R^\iota$ and $b\in\mathbb R^\kappa$ with $b_j\ge 0$ for all $j$, $b_j=0$ whenever $G_j(x)<0$, and
--   $$\nabla F(x)+\sum_{i\in\iota}a_i\nabla H_i(x)+\sum_{j\in\kappa}b_j\nabla G_j(x)=0.$$
--   2. **CPLD** (constant positive linear dependence, Qi and Wei). A point $x$ satisfies CPLD if the following holds for every $I\subseteq\iota$ and every $J\subseteq\{j\in\kappa : G_j(x)=0\}$: whenever there are coefficients $a_i$ ($i\in I$) and $b_j\ge 0$ ($j\in J$), not all zero, with
--   $$\sum_{i\in I}a_i\nabla H_i(x)+\sum_{j\in J}b_j\nabla G_j(x)=0,$$
--   the vectors $\{\nabla H_i(z)\}_{i\in I}\cup\{\nabla G_j(z)\}_{j\in J}$ are linearly dependent for every $z$ in some neighbourhood of $x$.
--   3. **MFCQ** (Mangasarian–Fromovitz). A point $x$ satisfies MFCQ if the gradients $\nabla H_i(x)$, $i\in\iota$, are linearly independent and there is a direction $d\in\mathbb R^n$ with $\langle\nabla H_i(x),d\rangle=0$ for all $i$ and $\langle\nabla G_j(x),d\rangle<0$ for every $j$ with $G_j(x)=0$.
--
--   In the paper, CPLD is the constraint qualification under which feasible limit points of the augmented Lagrangian method are KKT points (Theorem 4.2); it is strictly weaker than MFCQ, which in addition yields bounded multiplier estimates.
--
--   **Formalization Note.** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)` and $\nabla$ is Mathlib's `gradient`. The paper states CPLD in words ("the gradients involved in that combination are linearly dependent"); quantifying over all index subsets $I$, $J$ is equivalent, because a subset containing the support of the combination is dependent as soon as the support is. Families of gradients are indexed by $I\oplus J$ (`Sum.elim`), so two constraints with equal gradients count as dependent. CPLD and MFCQ carry no feasibility clause; the theorems state feasibility separately, as the paper does. The paper defines neither KKT nor MFCQ; both are the standard notions it cites ([36, 43]).
-- source:
--   Andreani, Birgin, Martínez & Schuverdt, On augmented Lagrangian methods with general lower-level constraints, HAL hal-01295437v1, pp. 2–3 (definition of CPLD, Qi–Wei [41]); p. 8, Theorem 4.2 (KKT point, MFCQ [36, 43])

import Mathlib

namespace AugLagLLC.KKT

open Filter Topology
open scoped InnerProductSpace

variable {n : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- KKT point of `minimize F x subject to H i x = 0 (i : ι), G j x ≤ 0 (j : κ)` on
`EuclideanSpace ℝ (Fin n)`: `x` is feasible and there are multipliers `a` (free) and `b ≥ 0`, with
`b j = 0` whenever the constraint `j` is inactive (`G j x < 0`), such that the gradient of the
Lagrangian vanishes. -/
def IsKKT (F : EuclideanSpace ℝ (Fin n) → ℝ) (H : ι → EuclideanSpace ℝ (Fin n) → ℝ)
    (G : κ → EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  (∀ i, H i x = 0) ∧ (∀ j, G j x ≤ 0) ∧
    ∃ (a : ι → ℝ) (b : κ → ℝ), (∀ j, 0 ≤ b j) ∧ (∀ j, G j x < 0 → b j = 0) ∧
      gradient F x + ∑ i, a i • gradient (H i) x + ∑ j, b j • gradient (G j) x = 0

/-- The constant positive linear dependence condition (CPLD) of Qi and Wei at `x`, for the
constraints `H i = 0` (`i : ι`) and `G j ≤ 0` (`j : κ`), in subset form: for every finite set `I` of
equality indices and every set `J` of inequality indices active at `x`, if some combination of
`{∇H i x}_{i ∈ I} ∪ {∇G j x}_{j ∈ J}` with nonnegative coefficients on `J`, not all coefficients on
`I ∪ J` zero, vanishes, then the family `{∇H i z}_{i ∈ I} ∪ {∇G j z}_{j ∈ J}` (indexed by `I ⊕ J`,
so a repeated vector counts as dependent) is linearly dependent for every `z` in a neighbourhood
of `x`. No feasibility clause: theorems state feasibility separately. -/
def CPLDAt (H : ι → EuclideanSpace ℝ (Fin n) → ℝ) (G : κ → EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ (I : Finset ι) (J : Finset κ), (∀ j ∈ J, G j x = 0) →
    (∃ (a : ι → ℝ) (b : κ → ℝ), (∀ j ∈ J, 0 ≤ b j) ∧
        ((∃ i ∈ I, a i ≠ 0) ∨ (∃ j ∈ J, b j ≠ 0)) ∧
        ∑ i ∈ I, a i • gradient (H i) x + ∑ j ∈ J, b j • gradient (G j) x = 0) →
      ∀ᶠ z in 𝓝 x, ¬ LinearIndependent ℝ
        (Sum.elim (fun i : I => gradient (H i) z) (fun j : J => gradient (G j) z))

/-- The Mangasarian–Fromovitz constraint qualification (MFCQ) at `x`: the equality gradients
`∇H i x` are linearly independent, and some direction `d` is orthogonal to all of them and makes
`⟪∇G j x, d⟫ < 0` for every inequality active at `x` (`G j x = 0`). -/
def MFCQAt (H : ι → EuclideanSpace ℝ (Fin n) → ℝ) (G : κ → EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  LinearIndependent ℝ (fun i => gradient (H i) x) ∧
    ∃ d : EuclideanSpace ℝ (Fin n), (∀ i, ⟪gradient (H i) x, d⟫_ℝ = 0) ∧
      ∀ j, G j x = 0 → ⟪gradient (G j) x, d⟫_ℝ < 0

end AugLagLLC.KKT


