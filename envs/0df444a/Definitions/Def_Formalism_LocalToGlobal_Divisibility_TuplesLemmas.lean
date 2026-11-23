-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_Divisibility_TuplesLemmas
-- name    : Formalism_LocalToGlobal_Divisibility_TuplesLemmas
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:49:14.795734+00:00
-- url     : https://prove2.me/theorems/40515163-a14f-4ff6-8bdd-da43607f147e
-- title:
--   Tuples Lemmas
-- statement:
--   Definitions and structural lemmas for Tuples Lemmas, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/TuplesLemmas.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_Tuples
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain TensorProduct Formalism.UG Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
namespace Formalism.L2.DIV
section Proved
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {L : Type} [Field L]
end Proved
section ProvedK
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {K : Type} [Field K] [NumberField K] [StarRing K] {S : Set ℕ}
end ProvedK
def IsConjOf {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) : Prop :=
  σ ≠ AlgHom.id F E ∧ (∀ e, σ (σ e) = e) ∧ ∀ e, σ e = e → ∃ a : F, algebraMap F E a = e
def FixedIsIdF : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsConjOf σ → (h90 σ).ker = (idF F E).range
def Hilbert90FiniteIdeles : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsConjOf σ → U1 σ = (h90 σ).range
def DetInUnitaryOne : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E), IsUnit J.det →
    ∀ g ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F), Matrix.GeneralLinearGroup.det g ∈ U1 σ
def DetTwMul : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (L : Type) [Field L]
    (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (ξ : Chr F E L),
    IsConjOf σ → IsUnit J.det → (idF F E).range ≤ ξ.ker →
    ∀ g ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F), ∀ g' ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F),
      detTw σ ξ (g * g') = detTw σ ξ g * detTw σ ξ g'
def DetTwRat : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (L : Type) [Field L]
    (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (ξ : Chr F E L),
    IsConjOf σ → IsUnit J.det → (idF F E).range ≤ ξ.ker → (ratId F E).range ≤ ξ.ker →
    ∀ g ∈ ratPts σ J (FiniteAdeleRing (𝓞 F) F), detTw σ ξ g = 1
def DetTwSq : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (L : Type) [Field L]
    (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (ξ : Chr F E L),
    IsConjOf σ → IsUnit J.det → (idF F E).range ≤ ξ.ker →
    ∀ g ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F), ξ (Matrix.GeneralLinearGroup.det g) = detTw σ ξ g ^ 2
def ConjInv : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (L : Type) [Field L]
    (σ : E →ₐ[F] E) (ξ : Chr F E L), IsConjOf σ → (idF F E).range ≤ ξ.ker → ξ.comp (conjId σ) = ξ⁻¹
def FinOrdAuto : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (L : Type) [Field L],
    kills Lˣ (ratId F E).range ⊓ openChr F E L ≤ CommGroup.torsion (Chr F E L)
def QprimeFinite : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (L : Type) [Field L]
    (ξ : Chr F E L), ξ ∈ openChr F E L → (Qprime ξ).Finite
def ResCharEx : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (L : Type) [Field L]
    (ξ : Chr F E L), (∀ v : HeightOneSpectrum (𝓞 F), wildAt E v ≤ ξ.ker) →
    ∀ P : HeightOneSpectrum (𝓞 E), ∃! χ, IsResChar ξ P χ
def ResCharMul : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (L : Type) [Field L]
    (ξ η : Chr F E L), (∀ v : HeightOneSpectrum (𝓞 F), wildAt E v ≤ ξ.ker) →
    (∀ v : HeightOneSpectrum (𝓞 F), wildAt E v ≤ η.ker) →
    ∀ P : HeightOneSpectrum (𝓞 E), resChar (ξ * η) P = resChar ξ P * resChar η P
def ResCharRam : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (L : Type) [Field L],
    Module.finrank F E = 2 →
    ∀ (ξ : Chr F E L), (∀ v : HeightOneSpectrum (𝓞 F), wildAt E v ≤ ξ.ker) → (idF F E).range ≤ ξ.ker →
    ∀ (v : HeightOneSpectrum (𝓞 F)) (P P' : HeightOneSpectrum (𝓞 E)), P ≠ P' →
      Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = P.asIdeal * P'.asIdeal →
      (v ∈ Qprime ξ ↔ resChar ξ P ≠ 1)
def ResCharConj : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (L : Type) [Field L]
    (ξ : Chr F E L), (∀ v : HeightOneSpectrum (𝓞 F), wildAt E v ≤ ξ.ker) → (idF F E).range ≤ ξ.ker →
    ∀ (v : HeightOneSpectrum (𝓞 F)) (P P' : HeightOneSpectrum (𝓞 E)), P ≠ P' →
      Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = P.asIdeal * P'.asIdeal →
      ∀ (n : 𝓞 F) (a : (𝓞 E ⧸ P.asIdeal)ˣ) (a' : (𝓞 E ⧸ P'.asIdeal)ˣ),
        (a : 𝓞 E ⧸ P.asIdeal) = Ideal.Quotient.mk P.asIdeal (algebraMap (𝓞 F) (𝓞 E) n) →
        (a' : 𝓞 E ⧸ P'.asIdeal) = Ideal.Quotient.mk P'.asIdeal (algebraMap (𝓞 F) (𝓞 E) n) →
        resChar ξ P a * resChar ξ P' a' = 1
def InertOrdRes : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (L : Type) [Field L],
    Module.finrank F E = 2 →
    ∀ (ξ : Chr F E L), (∀ v : HeightOneSpectrum (𝓞 F), wildAt E v ≤ ξ.ker) → (idF F E).range ≤ ξ.ker →
    ∀ (v : HeightOneSpectrum (𝓞 F)) (P P' : HeightOneSpectrum (𝓞 E)), P ≠ P' →
      Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = P.asIdeal * P'.asIdeal →
      ∀ n : ℕ, InertOrd ξ v n ↔ orderOf (resChar ξ P) = n
def DegOnePlc : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)), DegOne v → Ideal.absNorm v.asIdeal = plc v
def BasePrime : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (L : Type) [Field L],
    Module.finrank F E = 2 →
    ∀ (S : Set ℕ) (p : ℕ) (δ : Tup F E L S), IsBaseChar p (δ : Chr F E L) → p % 15 = 1
def TildeLocal : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (L : Type) [Field L]
    (σ : E →ₐ[F] E) (ξ : Chr F E L), IsConjOf σ →
    (∀ v : HeightOneSpectrum (𝓞 F), wildAt E v ≤ ξ.ker) → (idF F E).range ≤ ξ.ker →
    ∀ (P : HeightOneSpectrum (𝓞 E)) (v : HeightOneSpectrum (𝓞 F)), P.asIdeal.under (𝓞 F) = v.asIdeal →
    ∀ (u : (RInt F E)ˣ) (a : (𝓞 E ⧸ P.asIdeal)ˣ) (b : 𝓞 E), Ideal.Quotient.mk P.asIdeal b = a →
      Units.map (RInt F E).subtype.toMonoidHom u ∈ suppAt E v →
      (u : RInt F E) - toRInt F E b ∈ P.asIdeal.map (toRInt F E) →
      (∀ P' : HeightOneSpectrum (𝓞 E), P' ≠ P → (u : RInt F E) - 1 ∈ P'.asIdeal.map (toRInt F E)) →
      tilde σ ξ ⟨h90 σ (Units.map (RInt F E).subtype.toMonoidHom u), _, rfl⟩ = resChar ξ P a
def Mu0Quot : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (L : Type) [Field L]
    (σ : E →ₐ[F] E) (Ψ : Finset (E →+* L)) (e : (E →+* L) → ℤ) (G : Set ℕ) (μ μ' : Chr F E L),
    IsMu0 σ Ψ e G μ → IsMu0 σ Ψ e G μ' → μ * μ'⁻¹ ∈ finChar F E L
end Formalism.L2.DIV
end


