-- Prove2me | Definitions.Def_RobustMultiStop_IsLatticeSpace
-- name    : RobustMultiStop_IsLatticeSpace
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:29:25.746407+00:00
-- url     : https://prove2.me/theorems/39ea8dce-5921-47a8-94c3-27e013795dad
-- title:
--   The space $\mathfrak X$ of positions: a lattice subspace of $L^0(\mathcal F_N)$ containing the indicators
-- statement:
--   Let $(\Omega,(\mathcal F_t)_{t\ge0},P)$ be a filtered probability space and $N$ a horizon (the paper's $T$). A linear subspace $\mathfrak X$ of the space of $P$-a.e. classes of real random variables is a **space of positions** if
--
--   1. every $X\in\mathfrak X$ is $\mathcal F_N$-measurable, i.e. $\mathfrak X\subseteq L^0(\Omega,\mathcal F_N,P)$ (the paper's $\mathcal F:=\mathcal F_T$);
--   2. $\mathfrak X$ is closed under $X\wedge Y$ and $X\vee Y$;
--   3. $1_A\in\mathfrak X$ for every $A\in\mathcal F_N$.
--
--   This is the standing setting of §2.1: the functionals $\rho_t$ act on $\mathfrak X$, and the lattice structure is what allows maxima of rewards and pastings of stopping rules to stay inside the domain.
--
--   **Formalization Note** $\mathfrak X$ is a `Submodule ℝ (Ω →ₘ[P] ℝ)`, so every (in)equality is almost sure. $P$ lives on an ambient σ-algebra containing $\mathcal F_N$; since all positions are $\mathcal F_N$-measurable, only its restriction to $\mathcal F_N$ matters.
-- source:
--   Laeven, Schoenmakers, Schweizer & Stadje, Robust Multiple Stopping — A Pathwise Duality Approach, arXiv:2006.01802v2, §2.1, p.4 ("𝔛 be a linear subspace of L⁰(Ω, F, P) with F := F_T … closed under the operations ∧ (min) and ∨ (max) … contains all indicator functions 1_A, A ∈ F")

import Mathlib

open MeasureTheory

namespace RobustMultiStop

/-- The space `𝔛` of positions, Laeven, Schoenmakers, Schweizer & Stadje, *Robust Multiple
Stopping — A Pathwise Duality Approach*, arXiv:2006.01802v2, §2.1, p.4: "𝔛 be a linear subspace of
L⁰(Ω, F, P) with F := F_T. We further assume that 𝔛 has a lattice structure, i.e., 𝔛 is closed
under the operations ∧ (min) and ∨ (max), and that 𝔛 contains all indicator functions 1_A, A ∈ F."

`𝔛` is a linear subspace of the space `Ω →ₘ[P] ℝ` of a.e.-classes of random variables such that

* every element of `𝔛` is (a.e.) `F N`-measurable (the paper's `F := F_T`);
* `𝔛` is closed under `⊓` and `⊔`;
* the class of `1_A` lies in `𝔛` for every `A ∈ F N`.

**Formalization Note** Random variables are classes in `Ω →ₘ[P] ℝ`, so every (in)equality is
`P`-almost sure, as in the paper. `N` is the exercise horizon, the paper's `T` (or `T + L` after the
paper's extension `H_j ≡ 0`, `F_j ≡ F_T` for `j > T`, p.6). The probability `P` lives on an ambient
σ-algebra `m0 ⊇ F N`; since every position is `F N`-measurable, only the restriction of `P` to
`F N` matters. -/
structure IsLatticeSpace {Ω : Type*} {m0 : MeasurableSpace Ω} {P : Measure Ω}
    (F : Filtration ℕ m0) (N : ℕ) (𝔛 : Submodule ℝ (Ω →ₘ[P] ℝ)) : Prop where
  /-- `𝔛 ⊆ L⁰(Ω, F_N, P)`. -/
  measurable : ∀ X ∈ 𝔛, AEStronglyMeasurable[F N] (X : Ω → ℝ) P
  /-- closed under `∧` (min). -/
  inf_mem : ∀ X ∈ 𝔛, ∀ Y ∈ 𝔛, X ⊓ Y ∈ 𝔛
  /-- closed under `∨` (max). -/
  sup_mem : ∀ X ∈ 𝔛, ∀ Y ∈ 𝔛, X ⊔ Y ∈ 𝔛
  /-- `1_A ∈ 𝔛` for every `A ∈ F_N`. -/
  indicator_mem : ∀ A : Set Ω, MeasurableSet[F N] A →
    ∀ Z : Ω →ₘ[P] ℝ, (Z : Ω → ℝ) =ᵐ[P] A.indicator (fun _ => (1 : ℝ)) → Z ∈ 𝔛

end RobustMultiStop


