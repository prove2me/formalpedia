-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_ExistsHarrisTaylorObjectOfLevelLift
-- name    : Development_AutomorphicSpectrum_Definitions_MembershipCriteria_ExistsHarrisTaylorObjectOfLevelLift
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:14:47.293718+00:00
-- url     : https://prove2.me/theorems/e0b51b05-ef3e-4ffb-b324-8b9b1e5c8776
-- title:
--   Exists Harris Taylor Object Of Level Lift
-- statement:
--   Definitions and structural lemmas for Exists Harris Taylor Object Of Level Lift, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/MembershipCriteria/ExistsHarrisTaylorObjectOfLevelLift.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain MeasureTheory Matrix Complex
open scoped Classical
namespace GlobalTheory.CompanionTheory.OM
abbrev Af : Type := FiniteAdeleRing (𝓞 ℚ) ℚ
abbrev W (κ R : Type) : Type := (κ → R) × (κ → R)
instance invTwoAf : Invertible (2 : Af) := (Invertible.map (algebraMap ℚ Af) (2 : ℚ)).copy 2 (map_ofNat _ 2).symm
def psiR : AddChar ℝ ℂ := Circle.coeHom.compAddChar Real.fourierChar
def Zhat : Set Af := {a | ∀ v : HeightOneSpectrum (𝓞 ℚ), a v ∈ v.adicCompletionIntegers ℚ}
def IsPsiF (ψ : AddChar Af ℂ) : Prop :=
  (∀ r : ℚ, ψ (algebraMap ℚ Af r) = cexp (-(2 * Real.pi * I * (r : ℂ)))) ∧ ∀ a ∈ Zhat, ψ a = 1
variable {κ : Type} [Fintype κ]
def IsHaarF (μ : @Measure (κ → Af) (borel _)) : Prop :=
  @Measure.IsAddHaarMeasure _ _ _ (borel _) μ ∧ μ {x | ∀ i, x i ∈ Zhat} = 1
def EF {R : Type} [CommRing R] (w w' : W κ R) : R := w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2
def stdD (κ R : Type) [Fintype κ] [CommRing R] : GlobalTheory.WeilM.Darboux (EF (κ := κ) (R := R)) κ where
  e := LinearEquiv.refl R _
  form _ _ := rfl
def ofQ (κ R : Type) [CommRing R] [Algebra ℚ R] : W κ ℚ →+ W κ R where
  toFun w := (fun i => algebraMap ℚ R (w.1 i), fun i => algebraMap ℚ R (w.2 i))
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp
structure IsCx (J : W κ ℝ →L[ℝ] W κ ℝ) : Prop where
  sq : ∀ u, J (J u) = -u
  keeps : ∀ u v, EF (J u) (J v) = EF u v
  pos : ∀ u, u ≠ 0 → 0 < EF (J u) u
def HJ (J : W κ ℝ →L[ℝ] W κ ℝ) (u v : W κ ℝ) : ℂ := (EF (J u) v : ℝ) + I * (EF u v : ℝ)
def rhoR (w : W κ ℝ) (f : (κ → ℝ) → ℂ) : (κ → ℝ) → ℂ := GlobalTheory.WeilM.schr psiR w f
def rhoF (ψ : AddChar Af ℂ) (w : W κ Af) (Φ : (κ → Af) → ℂ) : (κ → Af) → ℂ := GlobalTheory.WeilM.schr ψ w Φ
def drho (w : W κ ℝ) (f : (κ → ℝ) → ℂ) : (κ → ℝ) → ℂ :=
  fun x => 2 * Real.pi * I * ((x ⬝ᵥ w.2 : ℝ) : ℂ) * f x + fderiv ℝ f x w.1
def cre (J : W κ ℝ →L[ℝ] W κ ℝ) (w : W κ ℝ) (f : (κ → ℝ) → ℂ) : (κ → ℝ) → ℂ :=
  (1 / 2 : ℂ) • (drho w f - I • drho (J w) f)
def ann (J : W κ ℝ →L[ℝ] W κ ℝ) (w : W κ ℝ) (f : (κ → ℝ) → ℂ) : (κ → ℝ) → ℂ :=
  (-1 / 2 : ℂ) • (drho w f + I • drho (J w) f)
def creW (J : W κ ℝ →L[ℝ] W κ ℝ) (l : List (W κ ℝ)) (f : (κ → ℝ) → ℂ) : (κ → ℝ) → ℂ := l.foldr (cre J) f
structure IsVac (J : W κ ℝ →L[ℝ] W κ ℝ) (v : (κ → ℝ) → ℂ) : Prop where
  sch : v ∈ GlobalTheory.WeilM.schFun (κ → ℝ)
  killed : ∀ w, ann J w v = 0
  unit : ∫ x, ‖v x‖ ^ 2 = 1
def Theta (f : (κ → ℝ) → ℂ) (Φ : (κ → Af) → ℂ) : ℂ :=
  ∑' ξ : κ → ℚ, f (fun i => (ξ i : ℝ)) * Φ (fun i => algebraMap ℚ Af (ξ i))
def Gth (J : W κ ℝ →L[ℝ] W κ ℝ) (v : (κ → ℝ) → ℂ) (Φ : (κ → Af) → ℂ) : W κ ℝ → ℂ :=
  fun z => cexp (Real.pi * HJ J z z / 2) * Theta (rhoR z v) Φ
def Ux (J : W κ ℝ →L[ℝ] W κ ℝ) (x : W κ ℝ) (F : W κ ℝ → ℂ) : W κ ℝ → ℂ :=
  fun z => cexp (-(Real.pi * HJ J z x) - Real.pi * HJ J x x / 2) * F (z + x)
def Uad (ψ : AddChar Af ℂ) (J : W κ ℝ →L[ℝ] W κ ℝ) (v : (κ → ℝ) → ℂ) (x : W κ Af) (F : W κ ℝ → ℂ) : W κ ℝ → ℂ :=
  Gth J v (rhoF ψ x (Classical.epsilon fun Φ : (κ → Af) → ℂ => Φ ∈ GlobalTheory.WeilM.SB (κ → Af) ∧ Gth J v Φ = F))
def dW (l : List (W κ ℝ)) (F : W κ ℝ → ℂ) : W κ ℝ → ℂ := l.foldr (fun w G z => fderiv ℝ G z w) F
def IsHolo (J : W κ ℝ →L[ℝ] W κ ℝ) (F : W κ ℝ → ℂ) : Prop :=
  Differentiable ℝ F ∧ ∀ z w, fderiv ℝ F z (J w) = I * fderiv ℝ F z w
def IsLat (Γ : AddSubgroup (W κ ℚ)) : Prop := Γ.FG ∧ Submodule.span ℚ (Γ : Set (W κ ℚ)) = ⊤
def IsSD (Γ : AddSubgroup (W κ ℚ)) : Prop :=
  IsLat Γ ∧ ∀ x, x ∈ Γ ↔ ∀ γ ∈ Γ, ∃ n : ℤ, EF x γ = (n : ℚ)
def hat (Γ : AddSubgroup (W κ ℚ)) : AddSubgroup (W κ Af) := (Γ.map (ofQ κ Af)).topologicalClosure
def re (Γ : AddSubgroup (W κ ℚ)) : AddSubgroup (W κ ℝ) := Γ.map (ofQ κ ℝ)
def HasLaw (ψ : AddChar Af ℂ) (L : AddSubgroup (W κ Af)) (α : W κ Af → ℂ) (Φ : (κ → Af) → ℂ) : Prop :=
  ∀ γ ∈ L, rhoF ψ γ Φ = (α γ)⁻¹ • Φ
def IsCanTheta (J : W κ ℝ →L[ℝ] W κ ℝ) (Γ : AddSubgroup (W κ ℚ)) (α : W κ ℚ → ℂ) (F : W κ ℝ → ℂ) : Prop :=
  IsHolo J F ∧ ∀ γ ∈ Γ, ∀ z, F (z + ofQ κ ℝ γ) =
    α γ * cexp (Real.pi * HJ J z (ofQ κ ℝ γ) + Real.pi * HJ J (ofQ κ ℝ γ) (ofQ κ ℝ γ) / 2) * F z
def ipB (J : W κ ℝ →L[ℝ] W κ ℝ) (D : Set (W κ ℝ)) (F F' : W κ ℝ → ℂ) : ℂ :=
  ⨍ z in D, F z * (starRingEnd ℂ) (F' z) * cexp (-(Real.pi * HJ J z z))
def conjJ (s : W κ ℝ ≃L[ℝ] W κ ℝ) (J : W κ ℝ →L[ℝ] W κ ℝ) : W κ ℝ →L[ℝ] W κ ℝ :=
  (s : W κ ℝ →L[ℝ] W κ ℝ) ∘L J ∘L (s.symm : W κ ℝ →L[ℝ] W κ ℝ)
def IsRealSplit {G : Type} [Group G] (s : G →* (W κ ℝ ≃L[ℝ] W κ ℝ)) (om : G →* Module.End ℂ ((κ → ℝ) → ℂ)) : Prop :=
  (∀ g u v, EF (s g u) (s g v) = EF u v) ∧
    GlobalTheory.WeilM.IsSplitting GlobalTheory.WeilM.realClass psiR (stdD κ ℝ) (fun g w => s g w) om ∧
    GlobalTheory.WeilM.IsUnitaryOn GlobalTheory.WeilM.realClass om
def IsFinSplit (ψ : AddChar Af ℂ) {G : Type} [Group G] (s : G →* (W κ Af ≃L[Af] W κ Af))
    (om : G →* Module.End ℂ ((κ → Af) → ℂ)) : Prop :=
  (∀ g u v, EF (s g u) (s g v) = EF u v) ∧ (∀ g, ∀ Φ ∈ GlobalTheory.WeilM.SB (κ → Af), om g Φ ∈ GlobalTheory.WeilM.SB (κ → Af)) ∧
    (∀ g w, ∀ Φ ∈ GlobalTheory.WeilM.SB (κ → Af), om g (rhoF ψ w Φ) = rhoF ψ (s g w) (om g Φ)) ∧
    ∀ μ, IsHaarF μ → ∀ g, ∀ Φ ∈ GlobalTheory.WeilM.SB (κ → Af), ∫ x, ‖om g Φ x‖ ^ 2 ∂μ = ∫ x, ‖Φ x‖ ^ 2 ∂μ
def frame {G G' : Type} [Group G] [Group G'] (s : G →* (W κ ℝ ≃L[ℝ] W κ ℝ)) (om : G →* Module.End ℂ ((κ → ℝ) → ℂ))
    (om' : G' →* Module.End ℂ ((κ → Af) → ℂ)) (J : W κ ℝ →L[ℝ] W κ ℝ) (v : (κ → ℝ) → ℂ) (φ : (κ → Af) → ℂ)
    (g : G) (g' : G') : W κ ℝ → ℂ :=
  Gth (conjJ (s g) J) (om g v) (om' g' φ)
def ratPts (t : W κ Af ≃L[Af] W κ Af) (L : AddSubgroup (W κ Af)) : AddSubgroup (W κ ℚ) :=
  (L.comap (t.symm : W κ Af →+ W κ Af)).comap (ofQ κ Af)
def stdJ (κ : Type) [Fintype κ] : W κ ℝ →L[ℝ] W κ ℝ :=
  (ContinuousLinearMap.snd ℝ _ _).prod (-ContinuousLinearMap.fst ℝ _ _)
end GlobalTheory.CompanionTheory.OM
end


