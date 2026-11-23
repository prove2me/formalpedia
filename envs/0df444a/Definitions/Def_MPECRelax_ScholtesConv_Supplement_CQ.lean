-- Prove2me | Definitions.Def_MPECRelax_ScholtesConv_Supplement_CQ
-- name    : MPECRelax_ScholtesConv_Supplement_CQ
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T11:28:00.115733+00:00
-- url     : https://prove2.me/theorems/99f80f52-19d1-488e-bbb0-3afe48ca6768
-- title:
--   §2.1–2.2, pp. 3–6 — tangent, linearized and polar cones; LICQ, CRCQ, CPLD, ACQ, GCQ; MPEC-LICQ and MPEC-CPLD
-- statement:
--   Let $X=\{x\in\mathbb R^n : g_i(x)\le0\ (i\in\iota),\ h_j(x)=0\ (j\in\kappa)\}$ be the feasible set of a standard nonlinear program (2) with continuously differentiable data, and let $I_g(x)=\{i : g_i(x)=0\}$ be its active inequality constraints at $x$.
--
--   1. **Tangent cone** (p. 3). The (Bouligand) tangent cone of a set $X$ at $x$ is
--   $$T_X(x)=\{d\in\mathbb R^n : \exists\, x^k\in X,\ \exists\,\{\tau_k\}\downarrow0 \text{ with } x^k\to x,\ (x^k-x)/\tau_k\to d\}.$$
--   2. **Linearized cone** (p. 3). $L_X(x)=\{d : \nabla g_i(x)^{\mathsf T}d\le0\ (i\in I_g(x)),\ \nabla h_j(x)^{\mathsf T}d=0\ (\text{all } j)\}$.
--   3. **Polar cone** (p. 3). $C^\circ=\{v : v^{\mathsf T}d\le0 \text{ for all } d\in C\}$.
--   4. **LICQ** (p. 3). The gradients $\nabla g_i(x)$ ($i\in I_g(x)$) and $\nabla h_j(x)$ (all $j$) are linearly independent.
--   5. **CPLD** (p. 4). For all $I_1\subseteq I_g(x)$, $I_2\subseteq\kappa$ such that $\{\nabla g_i(x)\}_{i\in I_1}\cup\{\nabla h_j(x)\}_{j\in I_2}$ is positive-linearly dependent (Definition 2.1), the gradients $\{\nabla g_i(y)\}_{i\in I_1}\cup\{\nabla h_j(y)\}_{j\in I_2}$ are linearly dependent for all $y$ in a neighborhood of $x$.
--   6. **CRCQ** (p. 3). There is a neighborhood $N$ of $x$ such that for all $I_1\subseteq I_g(x)$, $I_2\subseteq\kappa$ the gradients $\{\nabla g_i(y)\}_{i\in I_1}\cup\{\nabla h_j(y)\}_{j\in I_2}$ have the same rank (depending on $I_1,I_2$) for all $y\in N$.
--   7. **ACQ** and **GCQ** (p. 3). ACQ holds at $x$ if $T_X(x)=L_X(x)$; GCQ holds if $T_X(x)^\circ=L_X(x)^\circ$.
--   8. **MPEC-LICQ, MPEC-CPLD** (Definition 2.4, p. 6). For a feasible point $x^*$ of the MPEC (1), MPEC-LICQ (MPEC-CPLD) holds at $x^*$ if standard LICQ (CPLD) holds at $x^*$ for the tightened program $\mathrm{TNLP}(x^*)$.
--
--   MFCQ, the remaining condition of the list on p. 3, is the published `NLP.IsMFCQ`. These are the constraint qualifications in which Theorems 3.7, 3.8, 3.11 and 3.12 are stated; CRCQ completes the paper's list and is used by no theorem here.
--
--   **Formalization Note** The objects are built on the published `MPECRelax.ScholtesConv.NLP` and `MPECRelax.ScholtesConv.MPEC` (whose `TNLP` has subtype index sets, so a constraint exists only for the indices the paper lists). Gradient sets are indexed families (`Sum.elim` of the active inequality and the equality gradients), so a repeated gradient makes LICQ fail. $\{\tau_k\}\downarrow0$ is a positive, nonincreasing sequence tending to $0$ (the paper's notation); dropping the monotonicity gives the same cone. The rank of a family is the dimension of its span. The polar cone is defined for every set; the paper defines it for nonempty sets, and both cones it is applied to contain $0$ at feasible points.
-- source:
--   Hoheisel, Kanzow, Schwartz, Theoretical and numerical comparison of relaxation methods for mathematical programs with complementarity constraints, Preprint 299, Univ. Würzburg, Sept. 2010, pp. 3–4 (tangent, linearized, polar cones; LICQ, ACQ, GCQ; CPLD), p. 6, Definition 2.4

import Mathlib
import Definitions.Def_MPECRelax_ScholtesConv_NLP
import Definitions.Def_MPECRelax_ScholtesConv_MPEC

open Filter Topology
open scoped RealInnerProductSpace

namespace MPECRelax.ScholtesConv.Supplement

variable {n : ℕ} {ι κ : Type}

/-- The feasible set `X = {x | g_i(x) ≤ 0, h_j(x) = 0}` of the NLP (2). -/
def feasSet (P : NLP n ι κ) : Set (E n) := {x | P.Feasible x}

/-- The (Bouligand) tangent cone of a set `X` at `x` (p. 3): all `d` for which there are
`x^k ∈ X` and `{τ_k} ↓ 0` (positive, nonincreasing, tending to `0`) with `x^k → x` and
`(x^k − x)/τ_k → d`. -/
def tangentCone (X : Set (E n)) (x : E n) : Set (E n) :=
  {d | ∃ (xk : ℕ → E n) (τ : ℕ → ℝ), (∀ k, xk k ∈ X) ∧ (∀ k, 0 < τ k) ∧ Antitone τ ∧
    Tendsto τ atTop (𝓝 0) ∧ Tendsto xk atTop (𝓝 x) ∧
    Tendsto (fun k => (τ k)⁻¹ • (xk k - x)) atTop (𝓝 d)}

/-- The linearized cone of the NLP (2) at `x` (p. 3):
`{d | ⟪∇g_i(x), d⟫ ≤ 0 (i ∈ I_g(x)), ⟪∇h_j(x), d⟫ = 0 (all j)}`. -/
def linCone (P : NLP n ι κ) (x : E n) : Set (E n) :=
  {d | (∀ i ∈ P.activeSet x, ⟪gradient (P.g i) x, d⟫ ≤ 0) ∧ ∀ j, ⟪gradient (P.h j) x, d⟫ = 0}

/-- The polar cone `C° = {v | ⟪v, d⟫ ≤ 0 for all d ∈ C}` (p. 3). -/
def polar (C : Set (E n)) : Set (E n) := {v | ∀ d ∈ C, ⟪v, d⟫ ≤ 0}

/-- The linear independence constraint qualification (LICQ) at `x` (p. 3): the family of
gradients `∇g_i(x)` (`i ∈ I_g(x)`) and `∇h_j(x)` (all `j`) is linearly independent. -/
def IsLICQ (P : NLP n ι κ) (x : E n) : Prop :=
  LinearIndependent ℝ
    (Sum.elim (fun i : ↥(P.activeSet x) => gradient (P.g i.1) x) (fun j : κ => gradient (P.h j) x))

/-- The constant positive linear dependence condition (CPLD) at `x` (p. 4): for all
`I₁ ⊆ I_g(x)` and `I₂ ⊆ κ` such that `{∇g_i(x) | i ∈ I₁} ∪ {∇h_j(x) | j ∈ I₂}` is
positive-linearly dependent (Definition 2.1), the family `{∇g_i(y) | i ∈ I₁} ∪ {∇h_j(y) | j ∈ I₂}`
is linearly dependent for all `y` in a neighborhood of `x`. -/
def IsCPLD [Fintype ι] [Fintype κ] (P : NLP n ι κ) (x : E n) : Prop :=
  ∀ (I₁ : Set ι) (I₂ : Set κ), I₁ ⊆ P.activeSet x → P.PosLinDep x I₁ I₂ →
    ∀ᶠ y in 𝓝 x, ¬ LinearIndependent ℝ
      (Sum.elim (fun i : ↥I₁ => gradient (P.g i.1) y) (fun j : ↥I₂ => gradient (P.h j.1) y))

/-- The constant rank constraint qualification (CRCQ) at `x` (p. 3): there is a neighborhood
`N` of `x` such that for all `I₁ ⊆ I_g(x)` and `I₂ ⊆ κ` the family
`{∇g_i(y) | i ∈ I₁} ∪ {∇h_j(y) | j ∈ I₂}` has the same rank for all `y ∈ N` (the rank of the
family is the dimension of its span; constant on `N`, hence equal to its rank at `x`). -/
def IsCRCQ (P : NLP n ι κ) (x : E n) : Prop :=
  ∃ N ∈ 𝓝 x, ∀ (I₁ : Set ι) (I₂ : Set κ), I₁ ⊆ P.activeSet x → ∀ y ∈ N,
    Module.finrank ℝ (Submodule.span ℝ (Set.range
      (Sum.elim (fun i : ↥I₁ => gradient (P.g i.1) y) (fun j : ↥I₂ => gradient (P.h j.1) y)))) =
    Module.finrank ℝ (Submodule.span ℝ (Set.range
      (Sum.elim (fun i : ↥I₁ => gradient (P.g i.1) x) (fun j : ↥I₂ => gradient (P.h j.1) x))))

/-- The Abadie constraint qualification (ACQ) at `x` (p. 3): `T_X(x) = L_X(x)`. -/
def IsACQ (P : NLP n ι κ) (x : E n) : Prop :=
  tangentCone (feasSet P) x = linCone P x

/-- The Guignard constraint qualification (GCQ) at `x` (p. 3): `T_X(x)° = L_X(x)°`. -/
def IsGCQ (P : NLP n ι κ) (x : E n) : Prop :=
  polar (tangentCone (feasSet P) x) = polar (linCone P x)

variable {m p l : ℕ}

/-- Definition 2.4: MPEC-LICQ holds at `xs` if standard LICQ holds at `xs` for TNLP(xs). -/
def MPEC_LICQ (P : MPEC n m p l) (xs : E n) : Prop :=
  IsLICQ (P.TNLP xs) xs

open Classical in
/-- Definition 2.4: MPEC-CPLD holds at `xs` if standard CPLD holds at `xs` for TNLP(xs). -/
def MPEC_CPLD (P : MPEC n m p l) (xs : E n) : Prop :=
  IsCPLD (P.TNLP xs) xs

end MPECRelax.ScholtesConv.Supplement


