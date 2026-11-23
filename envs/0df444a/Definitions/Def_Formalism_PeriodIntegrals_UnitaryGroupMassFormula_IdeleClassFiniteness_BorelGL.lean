-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdeleClassFiniteness_BorelGL
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdeleClassFiniteness_BorelGL
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:45:24.599636+00:00
-- url     : https://prove2.me/theorems/c00b03df-caba-4abf-a993-c457c4584ee8
-- title:
--   Borel GL
-- statement:
--   Definitions and structural lemmas for Borel GL, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdeleClassFiniteness/BorelGL.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdeleClassFiniteness_OhatCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PIW.ClassFinD
open NumberField IsDedekindDomain
def IsUpperUni {R : Type} [CommRing R] {n : ℕ} (u : Matrix (Fin n) (Fin n) R) : Prop :=
  (∀ i j, j < i → u i j = 0) ∧ ∀ i, u i i = 1
def IsDiagM {R : Type} [CommRing R] {n : ℕ} (t : Matrix (Fin n) (Fin n) R) : Prop :=
  ∀ i j, i ≠ j → t i j = 0
def IwasawaAf : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (g : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)),
    ∃ u t k : GL (Fin n) (FiniteAdeleRing (𝓞 F) F),
      IsUpperUni u.val ∧ IsDiagM t.val ∧ k ∈ KGL F n ∧ g = u * t * k
def UnipApprox : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (u t : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)),
    IsUpperUni u.val → IsDiagM t.val →
      ∃ ν : GL (Fin n) F, ∃ w ∈ KGL F n, u = glIncl F n ν * t * w * t⁻¹
def IdeleClassFin : Prop :=
  ∀ (F : Type) [Field F] [NumberField F],
    ∃ C : Finset (FiniteAdeleRing (𝓞 F) F)ˣ, ∀ a : (FiniteAdeleRing (𝓞 F) F)ˣ,
      ∃ f : Fˣ, ∃ c ∈ C, ∃ e : (FiniteAdeleRing (𝓞 F) F)ˣ,
        (e : FiniteAdeleRing (𝓞 F) F) ∈ Ohat F ∧
        ((e⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) ∈ Ohat F ∧
        a = Units.map (algebraMap F (FiniteAdeleRing (𝓞 F) F) : F →* FiniteAdeleRing (𝓞 F) F) f * c * e
def diagGL {R : Type} [CommRing R] (n : ℕ) : (Fin n → Rˣ) →* GL (Fin n) R :=
  (Units.map (Matrix.diagonalRingHom (Fin n) R : (Fin n → R) →* Matrix (Fin n) (Fin n) R)).comp
    (MulEquiv.piUnits.symm : (Fin n → Rˣ) ≃* (Fin n → R)ˣ).toMonoidHom
end PIW.ClassFinD
end


