-- Prove2me | Definitions.Def_JRCurvedQFT_Symmetries_IsSymmetricLocalSemigroup
-- name    : JRCurvedQFT_Symmetries_IsSymmetricLocalSemigroup
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T07:01:47.94642+00:00
-- url     : https://prove2.me/theorems/f4e82ba9-239e-4fa8-b612-8b90687904d2
-- title:
--   Symmetric local semigroup $(S_\alpha,\mathscr D_\alpha,T)$
-- statement:
--   Let $\mathcal H$ be a Hilbert space and $T>0$. A **symmetric local semigroup** $(S_\alpha,\mathscr D_\alpha,T)$ consists of symmetric linear operators $S_\alpha$ with domains $\mathscr D_\alpha\subset\mathcal H$, $\alpha\in[0,T]$, such that:
--
--   1. $\mathscr D_\alpha\supset\mathscr D_\beta$ for $\alpha\le\beta$, and $\bigcup_{0<\alpha\le T}\mathscr D_\alpha$ is dense in $\mathcal H$;
--   2. $\alpha\mapsto S_\alpha$ is weakly continuous: for $f\in\mathscr D_\beta$ and $g\in\mathcal H$, $\alpha\mapsto\langle g,S_\alpha f\rangle$ is continuous on $[0,\beta]$;
--   3. $S_0=I$ and $S_\beta(\mathscr D_\alpha)\subset\mathscr D_{\alpha-\beta}$ for $0\le\beta\le\alpha\le T$;
--   4. $S_\alpha S_\beta=S_{\alpha+\beta}$ on $\mathscr D_{\alpha+\beta}$ for $\alpha,\beta,\alpha+\beta\in[0,T]$.
--
--   No single $\mathscr D_\alpha$ need be dense.
-- source:
--   Jaffe, Ritter, Quantum Field Theory on Curved Backgrounds. II. Spacetime Symmetries, arXiv:0704.0052v1, Definition 6.1, pp. 10–11

import Mathlib
import Definitions.Def_JRCurvedQFT_Symmetries_pmapApply

open scoped Manifold ContDiff ENNReal Topology InnerProductSpace
open Bundle MeasureTheory

namespace JRCurvedQFT.Symmetries

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A **symmetric local semigroup** `(S_α, 𝒟_α, T)`.

Jaffe, Ritter, *Quantum Field Theory on Curved Backgrounds. II. Spacetime Symmetries*, arXiv:0704.0052v1, Definition 6.1, pp. 10–11: "Let ℋ be a Hilbert space, let T > 0 and for each α ∈ [0, T], let
S_α be a symmetric linear operator on the domain 𝒟_α ⊂ ℋ, such that: (i) 𝒟_α ⊃ 𝒟_β if α ≤ β and
𝒟 := ⋃_{0<α≤T} 𝒟_α is dense in ℋ, (ii) α → S_α is weakly continuous, (iii) S_0 = I,
S_β(𝒟_α) ⊂ 𝒟_{α−β} for 0 ≤ β ≤ α ≤ T, and (iv) S_α S_β = S_{α+β} on 𝒟_{α+β} for
α, β, α + β ∈ [0, T]."

**Formalization Note** (ii) is read as: for `f ∈ 𝒟_β` and any `g`, `α ↦ ⟪g, S_α f⟫` is continuous
on `[0, β]`, the interval on which `S_α f` is defined. `S_0 = I` is on `𝒟_0`. The operators are only
constrained for `α ∈ [0, T]`. -/
structure IsSymmetricLocalSemigroup (T : ℝ) (D : ℝ → Submodule ℂ H) (S : ℝ → (H →ₗ.[ℂ] H)) :
    Prop where
  T_pos : 0 < T
  domain_eq : ∀ α ∈ Set.Icc 0 T, (S α).domain = D α
  symmetric : ∀ α ∈ Set.Icc 0 T, ∀ x y : (S α).domain, ⟪S α x, (y : H)⟫_ℂ = ⟪(x : H), S α y⟫_ℂ
  antitone : ∀ α β, 0 ≤ α → α ≤ β → β ≤ T → D β ≤ D α
  dense : Dense (⋃ α ∈ Set.Ioc 0 T, (D α : Set H))
  weak_continuous : ∀ β ∈ Set.Icc 0 T, ∀ f ∈ D β, ∀ g : H,
    ContinuousOn (fun α => ⟪g, pmapApply (S α) f⟫_ℂ) (Set.Icc 0 β)
  zero_eq : ∀ f ∈ D 0, pmapApply (S 0) f = f
  maps_domain : ∀ α β, 0 ≤ β → β ≤ α → α ≤ T → ∀ f ∈ D α, pmapApply (S β) f ∈ D (α - β)
  semigroup : ∀ α β, 0 ≤ α → 0 ≤ β → α + β ≤ T → ∀ f ∈ D (α + β),
    pmapApply (S α) (pmapApply (S β) f) = pmapApply (S (α + β)) f

end JRCurvedQFT.Symmetries


