-- Prove2me | Definitions.Def_ElimAgree_Supplement_Hyp35
-- name    : ElimAgree_Supplement_Hyp35
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:34:38.775741+00:00
-- url     : https://prove2.me/theorems/2d583bf8-7f0e-487f-9434-a4811afcc25a
-- title:
--   Hypothesis (3.5): a graded spectral decomposition
-- statement:
--   Let $\pi$ be a full-support law on a finite set $\Omega$ and $f$ a Boolean function on $\Omega\times\Omega$ with two symmetric couplings $\nu_1,\nu_0$ of $\pi$ with itself, supported on $f^{-1}(1)$ and $f^{-1}(0)$. Let $K_1,K_0$ be their conditional-expectation operators on $L^2(\pi)$, $(K_bu)(x)=\mathbb E_{\nu_b}[u(Y)\mid X=x]$, and put $K=\tfrac12(K_1+K_0)$, $V=\tfrac12(K_1-K_0)$. **Hypothesis (3.5)** with parameters $\gamma,\tau>0$ says: $L^2(\pi)=\bigoplus_{j=0}^mE_j$ orthogonally, with $E_0$ the constants, and $K$, $V$ act on $E_j$ as scalars $\kappa_j$, $v_j$ with
--
--   $$\kappa_0=1,\quad v_0=0,\quad |\kappa_j|\le e^{-\gamma j},\quad |v_j|\le\tau je^{-\gamma j}\qquad(j\ge1).$$
--
--   This is the hypothesis of the graded local transfer (Theorem 3.13); Lemma 3.14 verifies it for disjointness.
--
--   **Formalization Note** $L^2(\pi)$ is $\Omega\to\mathbb R$ with $\langle u,w\rangle=\sum_x\pi(x)u(x)w(x)$; the decomposition is a family of pairwise orthogonal subspaces whose span is everything.
-- source:
--   Ben Daniel, Can Many Instances Be Cheaper Than One? The Price of Agreement in Elimination, manuscript (STOC 2027 submission; held version sha256 eea57875…), §3.6, p.12 (PDF p.14), display (3.5)

import Mathlib
import Definitions.Def_ElimAgree_IsLaw

namespace ElimAgree

namespace Supplement

/-!
# Hypothesis (3.5): a graded spectral decomposition for `f` on `Ω × Ω`

Ben Daniel, *Can Many Instances Be Cheaper Than One? The Price of Agreement in Elimination*,
manuscript (STOC 2027 submission), §3.6, p.12, display (3.5).

**Formalization Note.** Functions on the finite set `Ω` are `Ω → ℝ`; `L²(π)` carries the
`π`-weighted inner product `⟨u, w⟩ = Σ_x π(x) u(x) w(x)` (`piInner`). The conditional-expectation
operator of a coupling `ν` of `π` with itself is `(K u)(x) = Σ_y ν(x, y) u(y) / π(x)`; `π` has full
support, so the division is by a positive number. The decomposition `L²(π) = ⊕_{j=0}^m E_j` is a
family of subspaces that are pairwise `π`-orthogonal and span `Ω → ℝ`.
-/

variable {Ω : Type} [Fintype Ω]

/-- `ν` is a symmetric coupling of `π` with itself: nonnegative, symmetric, with marginal `π`. -/
def IsSymCoupling (π : Ω → ℝ) (ν : Ω × Ω → ℝ) : Prop :=
  (∀ p, 0 ≤ ν p) ∧ (∀ x y, ν (x, y) = ν (y, x)) ∧ ∀ x, ∑ y, ν (x, y) = π x

/-- The conditional-expectation operator of `ν` on `L²(π)`: `(K u)(x) = E_ν[u(Y) | X = x]`. -/
noncomputable def condOp (π : Ω → ℝ) (ν : Ω × Ω → ℝ) (u : Ω → ℝ) : Ω → ℝ :=
  fun x => (∑ y, ν (x, y) * u y) / π x

/-- `K = ½(K₁ + K₀)` (p.12). -/
noncomputable def opK (π : Ω → ℝ) (ν₁ ν₀ : Ω × Ω → ℝ) (u : Ω → ℝ) : Ω → ℝ :=
  fun x => (condOp π ν₁ u x + condOp π ν₀ u x) / 2

/-- `V = ½(K₁ − K₀)` (p.12). -/
noncomputable def opV (π : Ω → ℝ) (ν₁ ν₀ : Ω × Ω → ℝ) (u : Ω → ℝ) : Ω → ℝ :=
  fun x => (condOp π ν₁ u x - condOp π ν₀ u x) / 2

/-- The inner product of `L²(π)`. -/
def piInner (π : Ω → ℝ) (u w : Ω → ℝ) : ℝ := ∑ x, π x * u x * w x

/-- Hypothesis (3.5) with parameters `γ, τ > 0` (p.12): `π` is a full-support law on `Ω`; `ν₁`, `ν₀`
are symmetric couplings of `π` with itself supported on `f^{−1}(1)` and `f^{−1}(0)`;
`L²(π) = ⊕_{j=0}^m E_j` orthogonally with `E_0` the constants; `K` and `V` act on `E_j` as the scalars
`κ_j`, `v_j`; and `κ_0 = 1`, `v_0 = 0`, `|κ_j| ≤ e^{−γj}`, `|v_j| ≤ τ j e^{−γj}` for `j ≥ 1`. -/
def Hyp35 (π : Ω → ℝ) (f : Ω → Ω → Bool) (ν₁ ν₀ : Ω × Ω → ℝ) (γ τ : ℝ) : Prop :=
  IsLaw π ∧ (∀ x, 0 < π x) ∧ IsSymCoupling π ν₁ ∧ IsSymCoupling π ν₀ ∧
  (∀ x y, ν₁ (x, y) ≠ 0 → f x y = true) ∧ (∀ x y, ν₀ (x, y) ≠ 0 → f x y = false) ∧
  0 < γ ∧ 0 < τ ∧
  ∃ (m : ℕ) (E : Fin (m + 1) → Submodule ℝ (Ω → ℝ)) (κ v : Fin (m + 1) → ℝ),
    (∀ i j, i ≠ j → ∀ u ∈ E i, ∀ w ∈ E j, piInner π u w = 0) ∧
    (⨆ j, E j) = ⊤ ∧
    E 0 = Submodule.span ℝ {fun _ => (1 : ℝ)} ∧
    (∀ j, ∀ u ∈ E j, opK π ν₁ ν₀ u = κ j • u ∧ opV π ν₁ ν₀ u = v j • u) ∧
    κ 0 = 1 ∧ v 0 = 0 ∧
    ∀ j : Fin (m + 1), 1 ≤ (j : ℕ) →
      |κ j| ≤ Real.exp (-(γ * j)) ∧ |v j| ≤ τ * j * Real.exp (-(γ * j))

end Supplement

end ElimAgree


