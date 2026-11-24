-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsSectionOrder
-- name    : GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsSectionOrder
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:40:26.722694+00:00
-- url     : https://prove2.me/theorems/65a22127-1020-4912-baa5-e6e8b59734ca
-- title:
--   Statements Section Order
-- statement:
--   Definitions and structural lemmas for Statements Section Order, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/StatementsSectionOrder.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LineInhabitant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
section Chart
variable {F : Type} [Field F] {n : ℕ}
def chartIncIdeal (I : Ideal (MvPolynomial (Fin n) F)) (t : Fin n → F) (e : ℕ) :
    Ideal (MvPolynomial (Fin n ⊕ Fin e × Fin n) F) :=
  (I ⊔ Ideal.span {linForm t - 1}).map (rename Sum.inl) ⊔
    Ideal.span (Set.range fun i : Fin e => ∑ m, X (Sum.inr (i, m)) * X (Sum.inl m))
def ChartInc (I : Ideal (MvPolynomial (Fin n) F)) (t : Fin n → F) (e : ℕ) : Type :=
  MvPolynomial (Fin n ⊕ Fin e × Fin n) F ⧸ chartIncIdeal I t e
instance (I : Ideal (MvPolynomial (Fin n) F)) (t : Fin n → F) (e : ℕ) : CommRing (ChartInc I t e) :=
  inferInstanceAs (CommRing (MvPolynomial (Fin n ⊕ Fin e × Fin n) F ⧸ chartIncIdeal I t e))
def chartIncHom (I : Ideal (MvPolynomial (Fin n) F)) (t : Fin n → F) (e : ℕ) :
    MvPolynomial (Fin e × Fin n) F →+* ChartInc I t e :=
  (Ideal.Quotient.mk (chartIncIdeal I t e)).comp (rename Sum.inr).toRingHom
instance (I : Ideal (MvPolynomial (Fin n) F)) (t : Fin n → F) (e : ℕ) :
    Algebra (MvPolynomial (Fin e × Fin n) F) (ChartInc I t e) :=
  (chartIncHom I t e).toAlgebra
def chartX (I : Ideal (MvPolynomial (Fin n) F)) (t : Fin n → F) (e : ℕ) :
    MvPolynomial (Fin n) F →+* ChartInc I t e :=
  (Ideal.Quotient.mk (chartIncIdeal I t e)).comp (rename Sum.inl).toRingHom
def chartLin (I : Ideal (MvPolynomial (Fin n) F)) (t : Fin n → F) (e : ℕ) (u : Fin n → F) :
    ChartInc I t e :=
  chartX I t e (linForm u)
abbrev ChartLoc (I : Ideal (MvPolynomial (Fin n) F)) (t : Fin n → F) (e : ℕ)
    (p : Ideal (MvPolynomial (Fin e × Fin n) F)) [p.IsPrime] : Type :=
  Localization (Algebra.algebraMapSubmonoid (ChartInc I t e) p.primeCompl)
def chartIdeal (I : Ideal (MvPolynomial (Fin n) F)) (t : Fin n → F) (e : ℕ)
    (p : Ideal (MvPolynomial (Fin e × Fin n) F)) [p.IsPrime] (W : Ideal (MvPolynomial (Fin n) F)) :
    Ideal (ChartLoc I t e p) :=
  (W.map (chartX I t e)).map (algebraMap (ChartInc I t e) (ChartLoc I t e p))
end Chart
def IncIdealBelow.Statement : Prop :=
  ∀ (F : Type) [Field F] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) F))
    (f : MvPolynomial (Fin (e + 1) × Fin n) F), IsProjPrime I → IsChowForm I (e + 1) f →
      incIdeal I e = ⊥
def SpecFirstMemIncIdeal.Statement : Prop :=
  ∀ (F : Type) [Field F] (n e : ℕ) (I W : Ideal (MvPolynomial (Fin n) F))
    (f : MvPolynomial (Fin (e + 1) × Fin n) F) (t : Fin n → F), IsChowForm I (e + 1) f → I ≤ W →
      linForm t ∈ W → specFirst f t ∈ incIdeal W e
def ChartChoice.Statement : Prop :=
  ∀ (F : Type) [Field F] [CharZero F] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) F))
    (f : MvPolynomial (Fin (e + 1) × Fin n) F) (q : MvPolynomial (Fin e × Fin n) F),
    IsProjPrime I → IsChowForm I (e + 1) f → Prime q → ∃ t : Fin n → F, ¬ q ∣ specFirst f t
def SpecFirstNe.Statement : Prop :=
  ∀ (F : Type) [Field F] [CharZero F] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) F))
    (f : MvPolynomial (Fin (e + 1) × Fin n) F) (u : Fin n → F),
    IsProjPrime I → IsChowForm I (e + 1) f → linForm u ∉ I → specFirst f u ≠ 0
def LocalizationPrimeDVR.Statement : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [UniqueFactorizationMonoid R]
    (q : R) (p : Ideal R) [p.IsPrime], Prime q → p = Ideal.span {q} →
      IsDiscreteValuationRing (Localization.AtPrime p)
def EmultiplicityOrd.Statement : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [UniqueFactorizationMonoid R]
    (q x : R) (p : Ideal R) [p.IsPrime], Prime q → p = Ideal.span {q} → x ≠ 0 →
      emultiplicity q x = Ring.ord (Localization.AtPrime p) (algebraMap R _ x)
def ChartFinite.Statement : Prop :=
  ∀ (F : Type) [Field F] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) F))
    (f : MvPolynomial (Fin (e + 1) × Fin n) F) (t : Fin n → F)
    (p : Ideal (MvPolynomial (Fin e × Fin n) F)) [p.IsPrime],
    IsProjPrime I → IsChowForm I (e + 1) f → specFirst f t ∉ p →
      Module.Finite (Localization.AtPrime p) (ChartLoc I t e p)
def ChartLocDomain.Statement : Prop :=
  ∀ (F : Type) [Field F] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) F))
    (f : MvPolynomial (Fin (e + 1) × Fin n) F) (t : Fin n → F)
    (p : Ideal (MvPolynomial (Fin e × Fin n) F)) [p.IsPrime],
    IsProjPrime I → IsChowForm I (e + 1) f → linForm t ∉ I →
      IsDomain (ChartLoc I t e p) ∧
        Function.Injective (algebraMap (Localization.AtPrime p) (ChartLoc I t e p)) ∧
        ∀ u : Fin n → F, linForm u ∉ I →
          algebraMap (ChartInc I t e) (ChartLoc I t e p) (chartLin I t e u) ≠ 0
def ChartNorm.Statement : Prop :=
  ∀ (F : Type) [Field F] [CharZero F] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) F))
    (f : MvPolynomial (Fin (e + 1) × Fin n) F) (t : Fin n → F)
    (p : Ideal (MvPolynomial (Fin e × Fin n) F)) [p.IsPrime],
    IsProjPrime I → IsChowForm I (e + 1) f → (p = ⊥ ∨ ∃ q, Prime q ∧ p = Ideal.span {q}) →
      specFirst f t ∉ p → ∀ u : Fin n → F,
        algebraMap _ (Localization.AtPrime p) (specFirst f u) =
          algebraMap _ (Localization.AtPrime p) (specFirst f t) *
            LinearMap.det (LinearMap.mulLeft (Localization.AtPrime p)
              (algebraMap (ChartInc I t e) (ChartLoc I t e p) (chartLin I t e u)))
open Classical in

def ChartLength.Statement : Prop :=
  ∀ (F : Type) [Field F] [CharZero F] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) F))
    (f : MvPolynomial (Fin (e + 1) × Fin n) F) (t u : Fin n → F)
    (q : MvPolynomial (Fin e × Fin n) F) (p : Ideal (MvPolynomial (Fin e × Fin n) F)) [p.IsPrime],
    IsProjPrime I → IsChowForm I (e + 1) f → linForm u ∉ I → Prime q → p = Ideal.span {q} →
      ¬ q ∣ specFirst f t →
        Module.length (Localization.AtPrime p) (ChartLoc I t e p ⧸ LinearMap.range
            (LinearMap.mulLeft (Localization.AtPrime p)
              (algebraMap (ChartInc I t e) (ChartLoc I t e p) (chartLin I t e u)))) =
          ∑ W ∈ (divCycle I u).support with Ideal.span {q} = incIdeal W e,
            ((divCycle I u W : ℕ) : ℕ∞)
def LengthFiniteAlgebra.Statement : Prop :=
  ∀ (O B : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [CommRing B] [Algebra O B]
    [Module.Finite O B] (θ : B),
    Module.length O (B ⧸ LinearMap.range (LinearMap.mulLeft O θ)) =
      ∑ᶠ 𝔓 : MaximalSpectrum B,
        Ring.ord (Localization.AtPrime 𝔓.asIdeal) (algebraMap B _ θ) * Module.length O (B ⧸ 𝔓.asIdeal)
def ChartMaxIdeals.Statement : Prop :=
  ∀ (F : Type) [Field F] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) F))
    (f : MvPolynomial (Fin (e + 1) × Fin n) F) (t u : Fin n → F)
    (q : MvPolynomial (Fin e × Fin n) F) (p : Ideal (MvPolynomial (Fin e × Fin n) F)) [p.IsPrime],
    IsProjPrime I → IsChowForm I (e + 1) f → linForm u ∉ I → Prime q → p = Ideal.span {q} →
      ¬ q ∣ specFirst f t →
        Set.BijOn (chartIdeal I t e p)
          {W | W ∈ (divCycle I u).support ∧ Ideal.span {q} = incIdeal W e}
          {𝔓 | 𝔓.IsMaximal ∧
            algebraMap (ChartInc I t e) (ChartLoc I t e p) (chartLin I t e u) ∈ 𝔓}
def ChartLocalOrder.Statement : Prop :=
  ∀ (F : Type) [Field F] (n e : ℕ) (I W : Ideal (MvPolynomial (Fin n) F))
    (f : MvPolynomial (Fin (e + 1) × Fin n) F) (t u : Fin n → F)
    (q : MvPolynomial (Fin e × Fin n) F) (p : Ideal (MvPolynomial (Fin e × Fin n) F)) [p.IsPrime],
    IsProjPrime I → IsChowForm I (e + 1) f → linForm u ∉ I → Prime q → p = Ideal.span {q} →
      ¬ q ∣ specFirst f t → W ∈ relComps (I ⊔ Ideal.span {linForm u}) → q ∈ incIdeal W e →
        linForm t ∉ W →
          ∃ _ : (chartIdeal I t e p W).IsPrime,
            Ring.ord (Localization.AtPrime (chartIdeal I t e p W))
                (algebraMap (ChartLoc I t e p) _
                  (algebraMap (ChartInc I t e) (ChartLoc I t e p) (chartLin I t e u))) =
              (localMult (I ⊔ Ideal.span {linForm u}) W : ℕ∞)
def ChartResidueDegree.Statement : Prop :=
  ∀ (F : Type) [Field F] [CharZero F] (n e : ℕ) (I W : Ideal (MvPolynomial (Fin n) F))
    (f : MvPolynomial (Fin (e + 1) × Fin n) F) (t u : Fin n → F)
    (q : MvPolynomial (Fin e × Fin n) F) (p : Ideal (MvPolynomial (Fin e × Fin n) F)) [p.IsPrime],
    IsProjPrime I → IsChowForm I (e + 1) f → linForm u ∉ I → Prime q → p = Ideal.span {q} →
      ¬ q ∣ specFirst f t → W ∈ relComps (I ⊔ Ideal.span {linForm u}) → q ∈ incIdeal W e →
        linForm t ∉ W →
          Module.length (Localization.AtPrime p) (ChartLoc I t e p ⧸ chartIdeal I t e p W) = 1
section Inhabitants
open LineChowForm
def uLine : Fin 2 → ℚ := fun j => if j = 0 then 1 else 0
def tLine : Fin 2 → ℚ := fun j => if j = 0 then 0 else 1
def qLine : MvPolynomial (Fin 1 × Fin 2) ℚ := X (0, 1)
end Inhabitants
end
end GroundTheory.Heights₂.Heights


