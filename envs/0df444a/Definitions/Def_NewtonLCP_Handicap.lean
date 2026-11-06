-- Prove2me | Definitions.Def_NewtonLCP_Handicap
-- name    : NewtonLCP_Handicap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:27:58.545225+00:00
-- url     : https://prove2.me/theorems/65201f72-9f82-4f74-887f-510b8294707e
-- title:
--   $\mathcal P_\star(\kappa)$-matrices and the handicap number $\hat\kappa(M)$
-- statement:
--   For $M\in\mathbb R^{n\times n}$ and $x\in\mathbb R^n$ let $I^+_M(x)=\{i: x_i(Mx)_i>0\}$ and $I^-_M(x)=\{i:x_i(Mx)_i<0\}$. A number $\kappa\ge0$ is admissible for $M$ if for every $x\in\mathbb R^n$
--
--   $$(1+4\kappa)\sum_{i\in I^+_M(x)}x_i(Mx)_i+\sum_{i\in I^-_M(x)}x_i(Mx)_i\ \ge\ 0 .$$
--
--   The **handicap number** is $\hat\kappa(M)=\inf\{\kappa\ge0:\kappa\text{ admissible}\}$ (display (1)). $M\in\mathcal P_\star$ if some $\kappa\ge0$ is admissible (finite handicap), and $M\in\mathcal P_\star(\kappa)$ if $M\in\mathcal P_\star$ and $\hat\kappa(M)\le\kappa$. $\mathcal P_\star(0)$ is the class of monotone matrices.
--
--   The handicap number measures how far $M$ is from monotone; the iteration bounds of the mission depend on it.
--
--   **Formalization Note** The paper sets $\hat\kappa(M)=\infty$ off $\mathcal P_\star$. Lean's real infimum of the empty set is $0$, so every statement that mentions $\hat\kappa(M)$ also assumes $M\in\mathcal P_\star$, and "$\hat\kappa(M)>\kappa$" is written as $M\notin\mathcal P_\star(\kappa)$. The infimum is attained, so $M\in\mathcal P_\star(\kappa)$ iff $\kappa\ge0$ is admissible (checked in the verification file).
-- source:
--   Ma–Végh–Vladu, Newton Steps are Faster for Linear Complementarity Problems, STOC 2027 submission (manuscript sha256 a70e5eab…), display (1), p.2; §2.2, p.6

import Mathlib

open Matrix Finset

namespace NewtonLCP

/-!
# P⋆(κ)-matrices and the handicap number

Ma–Végh–Vladu, *Newton Steps are Faster for Linear Complementarity Problems*, STOC 2027
submission manuscript (sha256 a70e5eab…40f8), §1, display (1), p.2; §2.2, p.6.

For `x ∈ ℝⁿ` let `I⁺_M(x) = {i : xᵢ(Mx)ᵢ > 0}` and `I⁻_M(x) = {i : xᵢ(Mx)ᵢ < 0}`. The handicap
number is `κ̂(M) = inf {κ ≥ 0 : (1+4κ) Σ_{I⁺} xᵢ(Mx)ᵢ + Σ_{I⁻} xᵢ(Mx)ᵢ ≥ 0 ∀ x}` (1);
`P⋆(κ) = {M : κ̂(M) ≤ κ}` and `P⋆ = ⋃_{κ ≥ 0} P⋆(κ)`, the matrices of finite handicap.

**Formalization Note.** The paper sets `κ̂(M) = ∞` off `P⋆` (p.6). Here `handicap M` is the real
`sInf` of the set in (1), which is `0` when that set is empty, i.e. off `P⋆`; every statement of
this mission that mentions `handicap M` also assumes `IsPStar M`. "`M ∈ P⋆(κ)`" is
`IsPStarK M κ := IsPStar M ∧ handicap M ≤ κ`, and the paper's "`κ̂(M) > κ`" (which includes
`κ̂(M) = ∞`) is `¬ IsPStarK M κ`. The infimum in (1) is attained (the condition is monotone and
closed in `κ`), so `IsPStarK M κ ↔ 0 ≤ κ ∧ PStarCond M κ`; this is checked in the mission's
verification file.
-/

variable {ι : Type*} [Fintype ι]

/-- The inequality of (1) for a given `κ`, for every `x ∈ ℝⁿ`:
`(1 + 4κ) Σ_{i ∈ I⁺_M(x)} xᵢ(Mx)ᵢ + Σ_{i ∈ I⁻_M(x)} xᵢ(Mx)ᵢ ≥ 0`. -/
def PStarCond (M : Matrix ι ι ℝ) (κ : ℝ) : Prop :=
  ∀ x : ι → ℝ,
    0 ≤ (1 + 4 * κ) * ∑ i ∈ univ.filter (fun i => 0 < x i * (M *ᵥ x) i), x i * (M *ᵥ x) i
      + ∑ i ∈ univ.filter (fun i => x i * (M *ᵥ x) i < 0), x i * (M *ᵥ x) i

/-- `M ∈ P⋆`: some `κ ≥ 0` satisfies (1), i.e. `M` has finite handicap (p.2). -/
def IsPStar (M : Matrix ι ι ℝ) : Prop :=
  ∃ κ : ℝ, 0 ≤ κ ∧ PStarCond M κ

/-- The handicap number `κ̂(M)` of (1), p.2 (junk value `0` off `P⋆`; see the module note). -/
noncomputable def handicap (M : Matrix ι ι ℝ) : ℝ :=
  sInf {κ : ℝ | 0 ≤ κ ∧ PStarCond M κ}

/-- `M ∈ P⋆(κ)`: `M ∈ P⋆` and `κ̂(M) ≤ κ` (p.2). -/
def IsPStarK (M : Matrix ι ι ℝ) (κ : ℝ) : Prop :=
  IsPStar M ∧ handicap M ≤ κ

end NewtonLCP


