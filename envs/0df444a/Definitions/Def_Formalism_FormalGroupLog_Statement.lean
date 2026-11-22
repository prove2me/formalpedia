-- Prove2me | Definitions.Def_Formalism_FormalGroupLog_Statement
-- name    : Formalism_FormalGroupLog_Statement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:05:09.19833+00:00
-- url     : https://prove2.me/theorems/ca8fb37b-4ac0-4ee1-b36f-18c5a5cd200e
-- title:
--   Statement
-- statement:
--   Definitions and structural lemmas for Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupLog/Statement.lean

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CapelliComplements_FirstLemmaM
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
universe u v
namespace Formalism.G
section Hom
variable {R : Type u} [CommRing R]
abbrev atX (f : PowerSeries R) : MvPowerSeries (Fin 2) R := f.subst (MvPowerSeries.X (0 : Fin 2))
abbrev atY (f : PowerSeries R) : MvPowerSeries (Fin 2) R := f.subst (MvPowerSeries.X (1 : Fin 2))
def IsHom (F G : FormalGroup R) (f : PowerSeries R) : Prop :=
  constantCoeff f = 0 ∧ f.subst F.toPowerSeries = G.toPowerSeries.subst ![atX f, atY f]
def IsLog (F : FormalGroup R) (f : PowerSeries R) : Prop :=
  constantCoeff f = 0 ∧ coeff 1 f = 1 ∧ f.subst F.toPowerSeries = atX f + atY f
end Hom
def HomId : Prop :=
  ∀ (R : Type u) [CommRing R] (F : FormalGroup R), IsHom F F PowerSeries.X
def HomComp : Prop :=
  ∀ (R : Type u) [CommRing R] (F G H : FormalGroup R) (f g : PowerSeries R),
    IsHom F G f → IsHom G H g → IsHom F H (g.subst f)
def LogIffHomGa : Prop :=
  ∀ (R : Type u) [CommRing R] (F : FormalGroup R) (f : PowerSeries R),
    IsLog F f ↔ (IsHom F FormalGroup.𝔾ₐ f ∧ coeff 1 f = 1)
def LogDeterminesLaw : Prop :=
  ∀ (R : Type u) [CommRing R] (F G : FormalGroup R) (f : PowerSeries R),
    IsLog F f → IsLog G f → F = G
def LogExistsUnique : Prop :=
  ∀ (R : Type u) [CommRing R] [Algebra ℚ R] (F : FormalGroup R), ∃! f : PowerSeries R, IsLog F f
def IsCommOfRat : Prop :=
  ∀ (R : Type u) [CommRing R] [Algebra ℚ R] (F : FormalGroup R), F.IsComm
section FunEq
variable {K : Type u} [NormedField K]
def IntegralPS (f : PowerSeries K) : Prop := ∀ n : ℕ, ‖coeff n f‖ ≤ 1
def IntegralMv {ι : Type v} (F : MvPowerSeries ι K) : Prop :=
  ∀ d : ι →₀ ℕ, ‖MvPowerSeries.coeff d F‖ ≤ 1
def DivBy (x : K) (f : PowerSeries K) : Prop := ∀ n : ℕ, ‖coeff n f‖ ≤ ‖x‖
def IsFrobLift (p q : ℕ) (σ : K →+* K) : Prop := ∀ a : K, ‖a‖ ≤ 1 → ‖σ a - a ^ q‖ ≤ ‖(p : K)‖
def IsFunEqType (p q : ℕ) (σ : K →+* K) (f : PowerSeries K) : Prop :=
  IntegralPS (f - (p : K)⁻¹ • (PowerSeries.map σ f).subst ((PowerSeries.X : PowerSeries K) ^ q))
def IsFunEqTypeMv {ι : Type v} (p q : ℕ) (hq : q ≠ 0) (σ : K →+* K) (φ : MvPowerSeries ι K) :
    Prop :=
  IntegralMv (φ - (p : K)⁻¹ • MvPowerSeries.expand q hq (MvPowerSeries.map σ φ))
end FunEq
def unitBall (K : Type u) [NormedField K] [IsUltrametricDist K] : Subring K := by
  first | exact @Bl.FirstLemmaM.goal1 K ‹_› ‹_› | exact @Bl.FirstLemmaM.goal1 K ‹_› | exact @Bl.FirstLemmaM.goal1 K | exact @Bl.FirstLemmaM.goal1
def FunctionalEquationSetting (K : Type u) [NormedField K] (p q : ℕ) (σ : K →+* K) : Prop :=
  p.Prime ∧ (∃ h : ℕ, 0 < h ∧ q = p ^ h) ∧ ‖(p : K)‖ < 1 ∧ IsFrobLift p q σ
def FunEqGroup : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (p q : ℕ) (σ : K →+* K),
    FunctionalEquationSetting K p q σ →
    ∀ f : PowerSeries K, constantCoeff f = 0 → coeff 1 f = 1 → IsFunEqType p q σ f →
      ∃ F : MvPowerSeries (Fin 2) K, MvPowerSeries.constantCoeff F = 0 ∧ IntegralMv F ∧
        f.subst F = atX f + atY f
def FunEqFormalGroup : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (p q : ℕ) (σ : K →+* K),
    FunctionalEquationSetting K p q σ →
    ∀ f : PowerSeries K, constantCoeff f = 0 → coeff 1 f = 1 → IsFunEqType p q σ f →
      ∃ F : FormalGroup (unitBall K), IsLog (F.map (unitBall K).subtype) f
def FunEqHom : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (p q : ℕ) (σ : K →+* K),
    FunctionalEquationSetting K p q σ →
    ∀ f g : PowerSeries K, constantCoeff f = 0 → coeff 1 f = 1 → IsFunEqType p q σ f →
      constantCoeff g = 0 → IsFunEqType p q σ g →
      ∃ h : PowerSeries K, constantCoeff h = 0 ∧ IntegralPS h ∧ f.subst h = g
def FunEqSubst : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (p q : ℕ) (hq : q ≠ 0)
    (σ : K →+* K), FunctionalEquationSetting K p q σ →
    ∀ f : PowerSeries K, constantCoeff f = 0 → IsFunEqType p q σ f →
    ∀ (ι : Type v) (α : MvPowerSeries ι K), MvPowerSeries.constantCoeff α = 0 → IntegralMv α →
      IsFunEqTypeMv p q hq σ (f.subst α)
def SubstInjective : Prop :=
  ∀ (R : Type u) [CommRing R] (ι : Type v) (f : PowerSeries R) (a b : MvPowerSeries ι R),
    constantCoeff f = 0 → coeff 1 f = 1 →
    MvPowerSeries.constantCoeff a = 0 → MvPowerSeries.constantCoeff b = 0 →
    f.subst a = f.subst b → a = b
def FunEqCongr : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (p q : ℕ) (σ : K →+* K),
    FunctionalEquationSetting K p q σ →
    ∀ f : PowerSeries K, constantCoeff f = 0 → coeff 1 f = 1 → IsFunEqType p q σ f →
    ∀ α β : PowerSeries K, constantCoeff α = 0 → constantCoeff β = 0 →
      IntegralPS α → IntegralPS β → ∀ r : ℕ, 1 ≤ r →
        (DivBy ((p : K) ^ r) (α - β) ↔ DivBy ((p : K) ^ r) (f.subst α - f.subst β))
def FrobLiftPadic : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], FunctionalEquationSetting ℚ_[p] p p (RingHom.id ℚ_[p])
def FunEqPadic : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (f : PowerSeries ℚ_[p]),
    constantCoeff f = 0 → coeff 1 f = 1 → IsFunEqType p p (RingHom.id ℚ_[p]) f →
    ∃ F : FormalGroup ℤ_[p], IsLog (F.map PadicInt.Coe.ringHom) f
def ltLog (p : ℕ) [Fact p.Prime] : PowerSeries ℚ_[p] :=
  PowerSeries.mk fun n => by
    classical exact if ∃ k : ℕ, p ^ k = n then ((n : ℚ_[p]))⁻¹ else 0
def LubinTateExample : Prop :=
  ∀ (p : ℕ) [Fact p.Prime],
    ∃ F : FormalGroup ℤ_[p], IsLog (F.map PadicInt.Coe.ringHom) (ltLog p) ∧
      ∃ e : PowerSeries ℤ_[p], IsHom F F e ∧ coeff 1 e = (p : ℤ_[p]) ∧
        ∀ n : ℕ, (p : ℤ_[p]) ∣ coeff n (e - PowerSeries.X ^ p)
abbrev gauss {K : Type u} [NormedField K] {ι : Type v} (c : ℝ) (F : MvPowerSeries ι K) : ℝ :=
  MvPowerSeries.gaussNorm (fun a : K => ‖a‖) (fun _ : ι => c) F
abbrev HasGauss {K : Type u} [NormedField K] {ι : Type v} (c : ℝ) (F : MvPowerSeries ι K) : Prop :=
  MvPowerSeries.HasGaussNorm (fun a : K => ‖a‖) (fun _ : ι => c) F
def LemmaBGauss : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] (ι : Type v) (n : ℕ) (c P : ℝ),
    0 ≤ c → 1 ≤ P →
    ∀ (u : MvPowerSeries ι K) (S : Finset (Fin n) → MvPowerSeries ι K)
      (A : Fin n → MvPowerSeries ι K) (Jf : Finset (Fin n)),
      HasGauss c u → gauss c u ≤ 1 →
      (∀ J, HasGauss c (S J) ∧ gauss c (S J) ≤ 1) →
      (∀ j, HasGauss c (A j)) →
      (∀ j, j ∉ Jf → gauss c (A j) ≤ 1) → (∀ j, j ∈ Jf → gauss c (A j) ≤ P) →
      HasGauss c (u * ∑ J : Finset (Fin n), S J * ∏ j ∈ J, A j) ∧
        gauss c (u * ∑ J : Finset (Fin n), S J * ∏ j ∈ J, A j) ≤ P ^ Jf.card
def CauchyCoeff : Prop :=
  ∀ (K : Type u) [NormedField K] (ι : Type v) (c : ℝ) (F : MvPowerSeries ι K) (α : ι →₀ ℕ),
    0 ≤ c → HasGauss c F → ‖MvPowerSeries.coeff α F‖ * c ^ α.degree ≤ gauss c F
def iterPderiv {K : Type u} [CommRing K] {r : ℕ} (α : Fin r → ℕ) :
    Module.End K (MvPowerSeries (Fin r) K) :=
  ((List.finRange r).map fun i => ((MvPowerSeries.pderiv K i).toLinearMap) ^ (α i)).prod
def IterPderivConst : Prop :=
  ∀ (K : Type u) [CommRing K] (r : ℕ) (α : Fin r → ℕ) (F : MvPowerSeries (Fin r) K),
    MvPowerSeries.constantCoeff (iterPderiv α F) =
      ((∏ i, (α i).factorial : ℕ) : K) * MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm α) F
def LemmaB : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] (r n : ℕ) (c₀ P : ℝ),
    0 < c₀ → 1 ≤ P →
    ∀ (u : MvPowerSeries (Fin r) K) (S : Finset (Fin n) → MvPowerSeries (Fin r) K)
      (A : Fin n → MvPowerSeries (Fin r) K) (Jf : Finset (Fin n)),
      HasGauss c₀ u → gauss c₀ u ≤ 1 →
      (∀ J, HasGauss c₀ (S J) ∧ gauss c₀ (S J) ≤ 1) →
      (∀ j, HasGauss c₀ (A j)) →
      (∀ j, j ∉ Jf → gauss c₀ (A j) ≤ 1) → (∀ j, j ∈ Jf → gauss c₀ (A j) ≤ P) →
      ∀ α : Fin r → ℕ,
        ‖MvPowerSeries.constantCoeff
            (iterPderiv α (u * ∑ J : Finset (Fin n), S J * ∏ j ∈ J, A j))‖ * c₀ ^ (∑ i, α i) ≤
          ‖((∏ i, (α i).factorial : ℕ) : K)‖ * P ^ Jf.card
end Formalism.G


