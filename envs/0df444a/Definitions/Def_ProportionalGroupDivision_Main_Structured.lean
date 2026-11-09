-- Prove2me | Definitions.Def_ProportionalGroupDivision_Main_Structured
-- name    : ProportionalGroupDivision_Main_Structured
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:13:10.32561+00:00
-- url     : https://prove2.me/theorems/2ab25140-3665-4af0-974d-c910737df900
-- title:
--   Definition 4 and (1) — $(\Delta_i)$-structured matrices, $\Xi(s,r)$, and the Theorem 6 bound
-- statement:
--   Given positive reals $\Delta_1\ge\Delta_2\ge\dots\ge\Delta_N$, a matrix $A\in[0,1]^{N\times m}$ is **$(\Delta_i)$-structured** if for every $i\in[N]$ the maximum column sum of the submatrix formed by rows $i,\dots,N$ is at most $\Delta_i$:
--
--   $$\forall\,1\le i\le N:\qquad \max_{g\in[m]}\ \sum_{h=i}^{N}A_{h,g}\ \le\ \Delta_i .$$
--
--   This is a condition on tail column sums, a nonuniform version of the Beck–Fiala column-sum bound. The **error function** of equation (1) is
--
--   $$\Xi(s,r)=C\,\log_2(4s)\,\sqrt{\log_2(4r)},$$
--
--   where $C$ is a constant from Theorem 6. The property of $C$ used there, `TopDownBound C`, says: for all $N,m$, every sequence $\Delta_1\ge\dots\ge\Delta_N>0$, every $(\Delta_i)$-structured $A\in[0,1]^{N\times m}$ and every $x_0\in[0,1]^m$ there is $x\in\{0,1\}^m$ with
--
--   $$|\langle A_i,x_0-x\rangle|\ \le\ C\log_2\!\big(4\max\{1,N/\Delta_N\}\big)\cdot\sqrt{\Delta_i\log_2(4\Delta_1/\Delta_N)}\qquad(1\le i\le N).$$
--
--   **Formalization Note** The predicate `IsStructured A Δ` contains the standing data of Definition 4: $\Delta$ positive and nonincreasing and all entries in $[0,1]$. Rows are `Fin N` (0-based); the column index type is arbitrary, so the same predicate applies after deleting columns. $C$ is an explicit parameter of $\Xi$; the statements that need the property of Theorem 6 assume `TopDownBound C`.
-- source:
--   Alexander Shekhovtsov, Georgy Sokolov, Mikhail Cherniavskii, Andrey Kupavskii, Nearly Tight Bounds for Proportional Group Fair Divisions and One-Sided Discrepancy, STOC 2027 submission #606 (October 2026), PDF SHA-256 b01bf42964a30eaf9c85a3d02713fc0ac4cd63ae8653853fa44b062c0220f39a, Definition 4, Theorem 6 and equation (1), PDF pp. 5–6 = printed pp. 5–6

import Mathlib

open scoped BigOperators

namespace ProportionalGroupDivision.Main

/-!
# `(Δ_i)`-structured matrices, the error function `Ξ`, and the Top-down Beck–Fiala bound
(Definition 4 and Theorem 6, PDF p. 5; equation (1), pp. 5–6)
-/

/-- Definition 4 (p. 5): given positive reals `Δ_1 ≥ Δ_2 ≥ ⋯ ≥ Δ_N`, a matrix `A ∈ [0,1]^{N × γ}`
is `(Δ_i)`-structured if for every row `i` every column sum of the submatrix of rows `i, …, N` is at
most `Δ_i`: `∀ i, ∀ g, ∑_{h ≥ i} A_{h,g} ≤ Δ_i`. Rows are `Fin N` (the paper's `1, …, N`); the
column index type `γ` is arbitrary (in the paper `[m]`, or the remaining columns after deleting
some). The definition includes its standing data: `Δ` positive and nonincreasing, entries in
`[0,1]`. -/
def IsStructured {N : ℕ} {γ : Type*} (A : Fin N → γ → ℝ) (Δ : Fin N → ℝ) : Prop :=
  (∀ i, 0 < Δ i) ∧ Antitone Δ ∧ (∀ i g, 0 ≤ A i g ∧ A i g ≤ 1) ∧
    ∀ (i : Fin N) (g : γ), ∑ h ∈ Finset.univ.filter (fun h => i ≤ h), A h g ≤ Δ i

/-- Equation (1) (p. 5): `Ξ(s, r) = C · log₂(4s) · √(log₂(4r))`, with the constant `C` as an
explicit parameter (the paper takes `C` from Theorem 6). -/
noncomputable def Xi (C s r : ℝ) : ℝ :=
  C * Real.logb 2 (4 * s) * Real.sqrt (Real.logb 2 (4 * r))

/-- The conclusion of Theorem 6 (p. 5) for the constant `C`: for all `N, m`, every sequence of
reals `Δ_1 ≥ ⋯ ≥ Δ_N > 0`, every `(Δ_i)`-structured `A ∈ [0,1]^{N×m}` and every `x₀ ∈ [0,1]^m`
there is `x ∈ {0,1}^m` with, for all rows `i`,
`|⟨A_i, x₀ − x⟩| ≤ C · log₂(4 · max{1, N/Δ_N}) · √(Δ_i · log₂(4Δ_1/Δ_N))`.
Here `Δ_1 = Δ ⟨0, _⟩` and `Δ_N = Δ ⟨N − 1, _⟩`. The constant `C` of `Ξ` in Corollary 7 and
Theorem 8 is a constant with this property. -/
def TopDownBound (C : ℝ) : Prop :=
  ∀ (N m : ℕ) (Δ : Fin N → ℝ) (A : Matrix (Fin N) (Fin m) ℝ) (x₀ : Fin m → ℝ),
    IsStructured A Δ → (∀ g, x₀ g ∈ Set.Icc (0 : ℝ) 1) →
    ∃ x : Fin m → ℝ, (∀ g, x g = 0 ∨ x g = 1) ∧
      ∀ i : Fin N,
        |∑ g, A i g * (x₀ g - x g)| ≤
          C * Real.logb 2 (4 * max 1 ((N : ℝ) / Δ ⟨N - 1, by have := i.pos; omega⟩)) *
            Real.sqrt (Δ i * Real.logb 2 (4 * Δ ⟨0, i.pos⟩ / Δ ⟨N - 1, by have := i.pos; omega⟩))

end ProportionalGroupDivision.Main


