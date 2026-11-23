-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicCoefficientSplitting
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicCoefficientSplitting
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:22:50.969893+00:00
-- url     : https://prove2.me/theorems/69200bad-ca40-43c5-b768-4b7fcbc779c1
-- title:
--   Isotropic Coefficient Splitting
-- statement:
--   Definitions and structural lemmas for Isotropic Coefficient Splitting, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/IsotropicCoefficientSplitting.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicOutsideLine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex Metric
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace Data
variable {r : ℕ} (X : Data E r)
def IsOrtho (x : Frame X.Ψ r) : Prop :=
  ∀ τ : X.Ψ, gram τ.1 X.Gm (mat x τ) = Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)
abbrev Coord : Type := X.Ψ → Fin (r - X.p0) → Fin X.p0 → ℂ
def lowBlock (Z : X.Coord) (τ : X.Ψ) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun a b => (if a = b then 1 else 0) +
    if h : X.p0 ≤ (a : ℕ) ∧ (b : ℕ) < X.p0 then
      Z τ ⟨(a : ℕ) - X.p0, by have := a.isLt; omega⟩ ⟨b, h.2⟩ else 0
def xZ (x : Frame X.Ψ r) (Z : X.Coord) : Frame X.Ψ r :=
  fun τ => (mat x τ * X.lowBlock Z τ : Matrix (Fin r) (Fin r) ℂ)
def opN {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) : ℝ :=
  sSup {t | ∃ v : Fin n → ℂ, v ≠ 0 ∧
    t = Real.sqrt (∑ i, ‖Matrix.mulVec A v i‖ ^ 2) / Real.sqrt (∑ j, ‖v j‖ ^ 2)}
def zN (Z : X.Coord) : ℝ := ⨆ τ : X.Ψ, opN (Matrix.of (Z τ))
end Data
def OrthonormalFlagTranslate : Prop :=
  ∀ (r : ℕ) (X : Data E r),
    (∀ x ∈ X.dom, ∃ b ∈ Bor X.Ψ r, X.IsOrtho (rmul x b)) ∧
    (∀ (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ),
      (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, P (rmul x b) = bchar la b * P x) →
      ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, X.pnorm la P (rmul x b) = X.pnorm la P x) ∧
    ∀ x ∈ X.dom, ∀ x' ∈ X.dom, X.SameFlag x x' → (∀ ξ : Fin r → E,
      X.Jz x = X.Jz x' ∧ X.Uz x ξ = X.Uz x' ξ ∧ X.aproj x ξ = X.aproj x' ξ) ∧ X.maj x = X.maj x'
def OrthonormalChartNormControl : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x : Frame X.Ψ r), x ∈ X.dom → X.IsOrtho x → ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 / 10 →
    (∀ Z : X.Coord, X.zN Z ≤ ρ →
      X.xZ x Z ∈ X.dom ∧
      (∀ (la : Wt X.Ψ r) (w : ℝ), (∑ τ, X.spread la τ) ≤ w →
        |Real.log (X.nfac la (X.xZ x Z)) - Real.log (X.nfac la x)| ≤ 4 * w * r * X.zN Z ^ 2) ∧
      ∀ τ v, (1 - ρ) / (1 + ρ) * X.maj x τ v ≤ X.maj (X.xZ x Z) τ v ∧
        X.maj (X.xZ x Z) τ v ≤ (1 + ρ) / (1 - ρ) * X.maj x τ v) ∧
    ∀ G : Frame X.Ψ r → ℂ, DifferentiableOn ℂ G X.dom →
      DifferentiableOn ℂ (fun Z : X.Coord => G (X.xZ x Z)) {Z | X.zN Z < ρ}
def NearSupremumTransference : Prop :=
  ∀ (r : ℕ) (X : DataX E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (ξ : Fin r → E) (ν : X.Ψ → ℝ)
    (c1 w : ℝ) (z0 : Frame X.Ψ r), ShortVectorHypotheses X la P ξ ν c1 w z0 →
    ∀ x' ∈ X.dom, (∀ τ, (1 - d6rh c1 w) / (1 + d6rh c1 w) ≤ X.tt ξ x' τ ∧
      X.tt ξ x' τ ≤ (1 + d6rh c1 w) / (1 - d6rh c1 w)) →
    X.hatN la (X.fj la ξ ν P) x' ≤
      Real.exp 2 * sSup {t | ∃ y ∈ X.FramesOverBasis ξ, t = X.hatN la (X.fj la ξ ν P) y}
def SchwarzLemmaBall : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (γ : V → ℂ) (ρ S : ℝ), 0 < ρ →
    DifferentiableOn ℂ γ (closedBall 0 ρ) → (∀ Z ∈ closedBall (0 : V) ρ, ‖γ Z‖ ≤ Real.exp (9 / 4) * S) →
    S / 2 < ‖γ 0‖ → ‖γ 0‖ ≤ S → ∀ Z ∈ ball (0 : V) (ρ / 21), γ Z ≠ 0
def SplitData {r : ℕ} (X : DataX E r) (ξ : Fin r → E) (La : ℝ) (z : Frame X.Ψ r)
    (lam : Fin (r - 2) → Fin r → E) : Prop :=
  (∀ j, lam j ∈ X.L' ∧ herm X.Gm (lam j) ξ = 0) ∧
  LinearIndependent E (Fin.cons ξ lam : Fin (r - 2 + 1) → Fin r → E) ∧
  (∀ j k : Fin (r - 2), (j : ℕ) < X.p0 - 1 → X.p0 - 1 ≤ (k : ℕ) → herm X.Gm (lam j) (lam k) = 0) ∧
  (∀ j : Fin (r - 2), (j : ℕ) < X.p0 - 1 → (∀ τ : X.Ψ, 0 < (τ.1 (herm X.Gm (lam j) (lam j))).re) ∧
    X.Jz z (X.ucomp z ξ (X.embV (lam j))) = I • X.ucomp z ξ (X.embV (lam j))) ∧
  (∀ j : Fin (r - 2), X.p0 - 1 ≤ (j : ℕ) → (∀ τ : X.Ψ, (τ.1 (herm X.Gm (lam j) (lam j))).re < 0) ∧
    X.Jz z (X.ucomp z ξ (X.embV (lam j))) = -(I • X.ucomp z ξ (X.embV (lam j)))) ∧
  ∀ j (τ : X.Ψ), ‖τ.1 (herm X.Gm (lam j) (lam j))‖ ≤ La ^ 2
def OrthonormalShortVectorBound : Prop :=
  ∀ (r : ℕ) (X : DataX E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (ξ : Fin r → E) (ν : X.Ψ → ℝ)
    (c1 w : ℝ) (z0 : Frame X.Ψ r), ShortVectorHypotheses X la P ξ ν c1 w z0 →
    ∀ x0 ∈ X.dom, X.IsOrtho x0 → X.SameFlag z0 x0 →
    ∃ (lam : Fin (r - 2) → Fin r → E) (h1 : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (Z1 : X.Coord),
      X.IsUnitaryC h1 ∧
      (∀ s t : X.Ψ → ℂ, X.applyV h1 (X.lineV ξ s + X.Jz z0 (X.lineV ξ t)) =
        X.lineV ξ s + X.Jz z0 (X.lineV ξ t)) ∧
      (∀ u ∈ X.Uz z0 ξ, X.applyV h1 u ∈ X.Uz z0 ξ) ∧
      SplitData X ξ (d6La r X.p0 (fdeg E) (dE E) (flowEpsilonBound X.g (dE E) (fdeg E) X.NA X.NC c1 w) (d6rh c1 w))
        (X.lmulC h1 z0) lam ∧
      X.SameFlag (X.lmulC h1 z0) (X.xZ x0 Z1) ∧ X.zN Z1 ≤ d6rh c1 w / 100
def IsotropicCoefficientSplitting : Prop :=
  ∀ (r : ℕ) (X : Data E r) (ξ : Fin r → E), X.IsIso ξ →
    ∃ f : (Fin r → E) → E, (∀ μ ∈ X.Λp ξ, f μ • ξ ∈ X.Λ) ∧
      (∀ μ ∈ X.Λp ξ, ∀ μ' ∈ X.Λp ξ, f (μ + μ') = f μ + f μ') ∧
      (∀ (α : 𝓞 E), ∀ μ ∈ X.Λp ξ, f ((α : E) • μ) = α * f μ) ∧
      ∀ e : E, e • ξ ∈ X.Λ → f (e • ξ) = e
def NoShortVectorLowerBound : Prop :=
  ∀ (r : ℕ) (X : DataX E r) (ξ : Fin r → E) (ep0 : ℝ), X.IsIso ξ → 0 < ep0 → ∀ z ∈ X.FramesOverBasis ξ,
    (∀ x ∈ X.L', herm X.Gm x ξ = 0 → (∀ e : E, x ≠ e • ξ) →
      ∃ τ : X.Ψ, ep0 ≤ X.maj z τ (X.ucomp z ξ (X.embV x) τ)) →
    ∀ δ : X.Ψ → (Fin r → ℂ) →ₗ[ℂ] ℂ, ∃ μ ∈ X.Λp ξ, ∀ u ∈ X.Uz z ξ, ∀ τ : X.Ψ,
      X.maj z τ ((δ τ (u τ) - (dE E : ℂ) * (-τ.1 X.ξ0) *
          hermC τ.1 X.Gm (u τ) (X.ucomp z ξ (X.embV μ) τ)) • Data.emb τ.1 ξ) ≤
        frameIndexBound r (fdeg E) (dE E) (rdE E) X.NA X.NC ep0 ^ 2 * X.maj z τ (u τ)
def UnitaryUnipotentMove : Prop :=
  ∀ (r : ℕ) (X : DataX E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (ξ : Fin r → E) (ν : X.Ψ → ℝ)
    (c1 w : ℝ) (z0 : Frame X.Ψ r), ShortVectorHypotheses X la P ξ ν c1 w z0 →
    ∀ x0 ∈ X.dom, X.IsOrtho x0 → X.SameFlag z0 x0 →
    ∀ (lam : Fin (r - 2) → Fin r → E) (h1 : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (Z1 : X.Coord),
      X.IsUnitaryC h1 →
      (∀ s t : X.Ψ → ℂ, X.applyV h1 (X.lineV ξ s + X.Jz z0 (X.lineV ξ t)) =
        X.lineV ξ s + X.Jz z0 (X.lineV ξ t)) →
      (∀ u ∈ X.Uz z0 ξ, X.applyV h1 u ∈ X.Uz z0 ξ) →
      SplitData X ξ (d6La r X.p0 (fdeg E) (dE E) (flowEpsilonBound X.g (dE E) (fdeg E) X.NA X.NC c1 w) (d6rh c1 w))
        (X.lmulC h1 z0) lam →
      X.SameFlag (X.lmulC h1 z0) (X.xZ x0 Z1) → X.zN Z1 ≤ d6rh c1 w / 100 →
      ∀ n' : ℕ, 1000 * frameIndexBound r (fdeg E) (dE E) (rdE E) X.NA X.NC
          (flowEpsilonBound X.g (dE E) (fdeg E) X.NA X.NC c1 w) / d6rh c1 w ≤ n' →
      ∃ (n : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (Z : X.Coord),
        X.IsUnitaryC n ∧ (∀ τ, Matrix.mulVec (n τ) (Data.emb τ.1 ξ) = Data.emb τ.1 ξ) ∧
        (∀ μ ∈ X.Λp ξ, ∃ e : E, e • ξ ∈ X.Λ ∧
          (n' : ℂ) • X.aproj (X.lmulC n (X.lmulC h1 z0)) ξ (X.embV μ) = X.embV (e • ξ)) ∧
        SplitData X ξ (d6La r X.p0 (fdeg E) (dE E) (flowEpsilonBound X.g (dE E) (fdeg E) X.NA X.NC c1 w)
          (d6rh c1 w)) (X.lmulC n (X.lmulC h1 z0)) lam ∧
        X.SameFlag (X.lmulC n (X.lmulC h1 z0)) (X.xZ x0 Z) ∧ X.zN Z < d6rh c1 w / 21
end
end ReciprocityTheory.ChartRestriction.G.FD


