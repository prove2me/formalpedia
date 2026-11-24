-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
-- name    : GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:29:24.142501+00:00
-- url     : https://prove2.me/theorems/4700f7bc-72fd-484f-a567-4b3ac148bd3f
-- title:
--   Statements
-- statement:
--   Definitions and structural lemmas for Statements, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/Statements.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
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
section Objects
variable {F : Type*} [Field F] {n : ℕ}
def incIdeal (P : Ideal (MvPolynomial (Fin n) F)) (k : ℕ) : Ideal (MvPolynomial (Fin k × Fin n) F) :=
  ⨅ v ∈ incidence P k,
    RingHom.ker (aeval v : MvPolynomial (Fin k × Fin n) F →ₐ[F] AlgebraicClosure F)
def genPt (P : Ideal (MvPolynomial (Fin n) F)) : Fin n → FractionRing (MvPolynomial (Fin n) F ⧸ P) :=
  fun j => algebraMap (MvPolynomial (Fin n) F ⧸ P) _ (Ideal.Quotient.mk P (X j))
def genSubst {R : Type*} [CommRing R] {k : ℕ} (ζ c : Fin n → R) (ij : Fin k × Fin n) :
    MvPolynomial (Fin k × Fin n) R :=
  X ij - (∑ l, X (ij.1, l) * C (ζ l)) * C (c ij.2)
end Objects
def FGNullstellensatz.Statement : Prop :=
  ∀ (F : Type) [Field F] (D : Type) [CommRing D] [IsReduced D] [Algebra F D]
    [Algebra.FiniteType F D] (r : D), (∀ φ : D →ₐ[F] AlgebraicClosure F, φ r = 0) → r = 0
def ProjNullstellensatz.Statement : Prop :=
  ∀ (F : Type) [Field F] (n : ℕ) (P : Ideal (MvPolynomial (Fin n) F)), IsProjPrime P →
    ∃ x : Fin n → AlgebraicClosure F, x ≠ 0 ∧ ∀ g ∈ P, aeval x g = 0
def IncidenceGeneric.Statement : Prop :=
  ∀ (F : Type) [Field F] (n k : ℕ) (P : Ideal (MvPolynomial (Fin n) F)) [P.IsPrime]
    (c : Fin n → FractionRing (MvPolynomial (Fin n) F ⧸ P)), ∑ j, c j * genPt P j = 1 →
      ∀ g : MvPolynomial (Fin k × Fin n) F,
        g ∈ incIdeal P k ↔ aeval (genSubst (genPt P) c) g = 0
def IncIdealPrime.Statement : Prop :=
  ∀ (F : Type) [Field F] (n k : ℕ) (P : Ideal (MvPolynomial (Fin n) F)), P.IsPrime → IsRelevant P →
    (incIdeal P k).IsPrime
def ChowFormMultiHomog.Statement : Prop :=
  ∀ (F : Type) [Field F] (n k : ℕ) (P : Ideal (MvPolynomial (Fin n) F))
    (f : MvPolynomial (Fin k × Fin n) F), IsProjPrime P → IsChowForm P k f →
      ∃ δ, 1 ≤ δ ∧ IsMultiHomog δ f
def ConeDimOfChowForm.Statement : Prop :=
  ∀ (F : Type) [Field F] (n k : ℕ) (P : Ideal (MvPolynomial (Fin n) F))
    (f : MvPolynomial (Fin k × Fin n) F), IsProjPrime P → IsChowForm P k f →
      ringKrullDim (MvPolynomial (Fin n) F ⧸ P) = ((k : ℕ) : WithBot ℕ∞)
def MinimalPrimeHomog.Statement : Prop :=
  ∀ (F : Type) [Field F] (n : ℕ) (J W : Ideal (MvPolynomial (Fin n) F)), IsHomogIdeal J →
    W ∈ J.minimalPrimes → IsHomogIdeal W
def ConeDimComponent.Statement : Prop :=
  ∀ (F : Type) [Field F] (n e : ℕ) (I W : Ideal (MvPolynomial (Fin n) F)) (u : Fin n → F),
    IsProjPrime I → ringKrullDim (MvPolynomial (Fin n) F ⧸ I) = ((e + 1 : ℕ) : WithBot ℕ∞) →
      linForm u ∉ I → W ∈ relComps (I ⊔ Ideal.span {linForm u}) →
        IsProjPrime W ∧ ringKrullDim (MvPolynomial (Fin n) F ⧸ W) = ((e : ℕ) : WithBot ℕ∞)
def ChowFormExists.Statement : Prop :=
  ∀ (F : Type) [Field F] (n k : ℕ) (P : Ideal (MvPolynomial (Fin n) F)), IsProjPrime P →
    ringKrullDim (MvPolynomial (Fin n) F ⧸ P) = ((k : ℕ) : WithBot ℕ∞) → ∃ g, IsChowForm P k g
def LengthQuotientDet.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (M : Type) [AddCommGroup M]
    [Module O M] [Module.Free O M] [Module.Finite O M] (φ : M →ₗ[O] M), LinearMap.det φ ≠ 0 →
      Module.length O (M ⧸ LinearMap.range φ) = Ring.ord O (LinearMap.det φ)
def OrdPolynomialLocalization.Statement : Prop :=
  ∀ (R : Type) [CommRing R] (σ : Type) (p : Ideal R) [p.IsPrime]
    [(Ideal.map (C : R →+* MvPolynomial σ R) p).IsPrime] (x : R),
    Ring.ord (Localization.AtPrime (Ideal.map (C : R →+* MvPolynomial σ R) p))
        (algebraMap (MvPolynomial σ R) _ (C x)) =
      Ring.ord (Localization.AtPrime p) (algebraMap R _ x)
open Classical in

def SectionOrder.Statement : Prop :=
  ∀ (F : Type) [Field F] [CharZero F] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) F))
    (f : MvPolynomial (Fin (e + 1) × Fin n) F) (u : Fin n → F),
    IsProjPrime I → IsChowForm I (e + 1) f → linForm u ∉ I →
      specFirst f u ≠ 0 ∧ ∀ q : MvPolynomial (Fin e × Fin n) F, Irreducible q →
        emultiplicity q (specFirst f u) =
          ∑ W ∈ (divCycle I u).support with Ideal.span {q} = incIdeal W e,
            ((divCycle I u W : ℕ) : ℕ∞)
section Inhabitants
end Inhabitants
end
end GroundTheory.Heights₂.Heights


