-- Prove2me | Definitions.Def_HOTrap_LocalReconstruction
-- name    : HOTrap_LocalReconstruction
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:48:06.713204+00:00
-- url     : https://prove2.me/theorems/6a256360-85b8-4972-943c-0ae4ea3d6288
-- title:
--   Degree-$p$ local polynomial reconstruction property
-- statement:
--   A finite set $X\subseteq S$ with Lagrange basis $(\ell_x)_{x\in X}$ has the degree-$p$ reconstruction property with exponent $\beta$ if $c\in X$, $|X|=\binom{d+p}p$, $X$ is unisolvent for $\Pi^d_p$, and for every map $F\in C^{p,\beta}(L)$ near $S$ and all supplied values with $\|\tilde F_x-F(x)\|\le\tau$, the interpolant $P=\sum_x\tilde F_x\ell_x$ has components in $\Pi^d_p$, satisfies $P(c)=\tilde F_c$, and obeys
--   $$
--   \|D^j(P-F)\|_{\infty,S}\le\frac32a_{p-j,\beta}L\rho^{p-j+\beta}+\Lambda_j\tau,\qquad j=0,1,
--   $$
--   where $\Lambda_0,\Lambda_1$ are the value and derivative stability constants of the basis on $S$.
--
--   Proposition A.5 asserts that such sets exist.
--
--   **Formalization Note** $X$ and $\ell$ are fixed before $F$, $L$ and $\tau$, which is "nonadaptively chosen". $\Lambda_0,\Lambda_1$ range over all upper bounds of the stability sums on $S$; this is equivalent to using their suprema.
-- source:
--   Zhou–Sugiyama–Suzuki, Finding Stationary Points under Higher-Order Smoothness: Trapping Algorithms and First-Order Lower Bounds, arXiv:2610.02791, Proposition A.5, Eq. (58), p.56

import Mathlib
import Definitions.Def_HOTrap_HolderNear
import Definitions.Def_HOTrap_PolyLE
import Definitions.Def_HOTrap_IsPolyMap
import Definitions.Def_HOTrap_IsUnisolvent
import Definitions.Def_HOTrap_IsLagrangeBasis
import Definitions.Def_HOTrap_interpolant
import Definitions.Def_HOTrap_taylorConst

universe u

namespace HOTrap

/-- **Degree-`p` local polynomial reconstruction at the node set `X`** with Lagrange basis `ℓ`, the property
of Zhou–Sugiyama–Suzuki, *Finding Stationary Points under Higher-Order Smoothness: Trapping Algorithms and First-Order Lower Bounds*, arXiv:2610.02791, Proposition A.5, p.56. The set `X ⊆ S` contains `c`, has `(d+p choose p)` elements and is
unisolvent for `Π^d_p`. For every map `F ∈ C^{p,β}(L)` near `S` and supplied values with
`∥F̃ₓ − F(x)∥ ≤ τ`, the interpolant `P = ∑ₓ F̃ₓ ℓₓ` has components in `Π^d_p`, `P(c) = F̃_c`, and Eq. (58):
`∥D^j(P − F)∥_{∞,S} ≤ (3/2) a_{p−j,β} L ρ^{p−j+β} + Λⱼ τ` for `j = 0, 1`.

**Formalization Note** `X` and `ℓ` come before `G`, `F`, `L` and `τ` in the statements that use this
predicate, which is "nonadaptively chosen". `Λ₀, Λ₁` are arbitrary upper bounds of the stability sums on
`S`, which is equivalent to using their suprema and avoids a junk `sSup`. The sup norms over `S` are
written pointwise. `p ≥ 1` is assumed where the predicate is used, so `p - 1` is exact. -/
def LocalReconstruction {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d))) (c : EuclideanSpace ℝ (Fin d)) (ρ : ℝ) (p : ℕ) (β : ℝ)
    (X : Finset (EuclideanSpace ℝ (Fin d))) (ℓ : X → EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  (↑X ⊆ S) ∧ X.card = (d + p).choose p ∧
    IsUnisolvent (PolyLE d p) (Subtype.val : X → EuclideanSpace ℝ (Fin d)) ∧
    IsLagrangeBasis (PolyLE d p) (Subtype.val : X → EuclideanSpace ℝ (Fin d)) ℓ ∧
    ∃ hc : c ∈ X,
      ∀ (G : Type u) [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
        (F : EuclideanSpace ℝ (Fin d) → G) (Ft : X → G) (L τ Λ₀ Λ₁ : ℝ),
        0 ≤ L → 0 ≤ τ → HolderNear S p β L F → (∀ x : X, ‖Ft x - F x‖ ≤ τ) →
        (∀ y ∈ S, ∑ x, |ℓ x y| ≤ Λ₀) → (∀ y ∈ S, ∑ x, ‖gradient (ℓ x) y‖ ≤ Λ₁) →
        IsPolyMap (PolyLE d p) (interpolant ℓ Ft) ∧
          interpolant ℓ Ft c = Ft ⟨c, hc⟩ ∧
          (∀ y ∈ S, ‖interpolant ℓ Ft y - F y‖ ≤
            3 / 2 * taylorConst p β * L * ρ ^ ((p : ℝ) + β) + Λ₀ * τ) ∧
          (∀ y ∈ S, ‖fderiv ℝ (fun w => interpolant ℓ Ft w - F w) y‖ ≤
            3 / 2 * taylorConst (p - 1) β * L * ρ ^ (((p - 1 : ℕ) : ℝ) + β) + Λ₁ * τ)

end HOTrap


