-- Prove2me | Definitions.Def_StochFictPlay_Supermodular_StochOrder
-- name    : StochFictPlay_Supermodular_StochOrder
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T10:16:25.588631+00:00
-- url     : https://prove2.me/theorems/b810af24-debe-410e-bc96-4cb6c32b17b9
-- title:
--   Stochastic dominance coordinates $T$, the set $T(\Sigma)$, order intervals and the dynamic (T)
-- statement:
--   Fix the game data of the Game definition.
--
--   1. **Stochastic dominance coordinates.** For $x^\alpha \in \mathbb R^{n^\alpha}$, $T^\alpha x^\alpha \in \mathbb R^{n^\alpha - 1}$ has entries
--   $$(T^\alpha x^\alpha)_i = \sum_{j > i} x^\alpha_j,$$
--   the mass that $x^\alpha$ places on strategies larger than $i$. $T x = (T^1 x^1, \dots, T^p x^p)$, and profiles are compared componentwise: $T x \le T y$ means that each $y^\alpha$ stochastically dominates $x^\alpha$.
--   2. **Order interval.** $[\underline x, \bar x] = \{x \in \Sigma : T\underline x \le T x \le T \bar x\}$.
--   3. **The image of $\Sigma$.** $T(\Sigma) = \{v : 1 \ge v^\alpha_0 \ge v^\alpha_1 \ge \dots \ge v^\alpha_{n^\alpha-2} \ge 0 \text{ for all } \alpha\}$.
--   4. **Inverse.** $(T^\alpha)^{-1} v^\alpha$ has entries $x_j = v_{j-1} - v_j$ with the conventions $v_{-1} = 1$ and $v_{n^\alpha - 1} = 0$.
--   5. **The dynamic (T).** $\dot v^\alpha = T^\alpha \tilde B^\alpha\big((T^{-\alpha})^{-1} v^{-\alpha}\big) - v^\alpha$.
--
--   These coordinates turn the perturbed best response dynamic of a supermodular game into a cooperative system.
--
--   **Formalization Note** Indices are 0-based: the paper's $\sum_{j=i+1}^{n^\alpha}$ becomes the sum over $j > i$. $T^\alpha$ and $(T^\alpha)^{-1}$ are defined (linearly, resp. affinely) on the whole ambient space, so the field of (T) is defined on all of $\prod_\alpha \mathbb R^{n^\alpha-1}$ and its partial derivatives are ordinary derivatives. $(T^\alpha)^{-1}$ inverts $T^\alpha$ on the simplex.
-- source:
--   Hofbauer and Sandholm, On the Global Convergence of Stochastic Fictitious Play, Econometrica 70 (2002); authors' manuscript of February 21, 2002, p. 19 (operators T^alpha and T), p. 20 (order interval in Theorem 5.2, the dynamic (T) and the set T(Sigma))

import Mathlib
import Definitions.Def_StochFictPlay_Supermodular_Game

open scoped ENNReal

namespace StochFictPlay.Supermodular

/-- The stochastic dominance coordinates `T^α : ∆S^α → ℝ^{n^α − 1}` (manuscript p. 19),
`(T^α x^α)_i = ∑_{j = i+1}^{n^α} x^α_j`, the mass that `x^α` places on strategies larger than
`i`. With 0-based strategies `Fin m` and coordinates `Fin (m - 1)`, coordinate `i` is the sum
of `x j` over `j > i`. Defined (linearly) on all of `ℝ^m`. -/
def Tco {m : ℕ} (x : Fin m → ℝ) : Fin (m - 1) → ℝ :=
  fun i => ∑ j : Fin m, if i.val < j.val then x j else 0

/-- The target space `∏_α ℝ^{n^α − 1}` of `T`. -/
abbrev Coord {p : ℕ} (n : Fin p → ℕ) := (α : Fin p) → Fin (n α - 1) → ℝ

/-- `T(x¹, …, x^p) = (T¹x¹, …, T^p x^p)` (p. 19). Profiles are compared through `T` with the
componentwise order of `Coord n`: `T x ≤ T y` means that every player's `y^α` stochastically
dominates `x^α`. -/
def Tmap {p : ℕ} {n : Fin p → ℕ} (x : Mixed n) : Coord n :=
  fun α => Tco (x α)

/-- The order interval `[x̲, x̄] = {x ∈ Σ : T x̲ ≤ T x ≤ T x̄}` (Theorem 5.2, p. 20). -/
def orderInterval {p : ℕ} (n : Fin p → ℕ) (xl xu : Mixed n) : Set (Mixed n) :=
  {x | x ∈ mixedProfiles n ∧ Tmap xl ≤ Tmap x ∧ Tmap x ≤ Tmap xu}

/-- `T(Σ) = {(v¹, …, v^p) : 1 ≥ v^α_1 ≥ … ≥ v^α_{n^α−1} ≥ 0 for all α}` (p. 20). -/
def TSigma {p : ℕ} (n : Fin p → ℕ) : Set (Coord n) :=
  {v | ∀ α, (∀ i, v α i ≤ 1 ∧ 0 ≤ v α i) ∧ Antitone (v α)}

/-- The extended coordinate `k ↦ v_{k−1}` (0-based) used to invert `T^α`: its value is `1` at
`k = 0` (all mass lies on strategies `≥ 0`), `v (k − 1)` for `1 ≤ k ≤ m − 1`, and `0` for
`k ≥ m` (no mass above the top strategy). -/
def tailMass {m : ℕ} (v : Fin (m - 1) → ℝ) (k : ℕ) : ℝ :=
  if k = 0 then 1 else if h : k - 1 < m - 1 then v ⟨k - 1, h⟩ else 0

/-- The inverse `(T^α)^{-1}` of `T^α` on `T^α(∆S^α)` (p. 20): `x_j = v_{j−1} − v_j` with
`v_{−1} = 1` and `v_{m−1} = 0` (0-based). It is affine and is defined on all of `ℝ^{m−1}`. -/
def Tinv {m : ℕ} (v : Fin (m - 1) → ℝ) : Fin m → ℝ :=
  fun j => tailMass v j.val - tailMass v (j.val + 1)

/-- The profile-wise inverse `T^{-1} v = ((T¹)^{-1} v¹, …, (T^p)^{-1} v^p)`. -/
def TinvMap {p : ℕ} {n : Fin p → ℕ} (v : Coord n) : Mixed n :=
  fun α => Tinv (v α)

/-- The vector field of the transformed dynamic
`(T) v̇^α = T^α B̃^α((T^{−α})^{-1} v^{−α}) − v^α` (p. 20), on the ambient space `Coord n`.
Player `α`'s perturbed best response depends only on the opponents' coordinates. -/
noncomputable def gField {p : ℕ} {n : Fin p → ℕ} (f : (α : Fin p) → (Fin (n α) → ℝ) → ℝ≥0∞)
    (u : (α : Fin p) → Profile n → ℝ) : Coord n → Coord n :=
  fun v α => Tco (pbr f u (TinvMap v) α) - v α

end StochFictPlay.Supermodular


