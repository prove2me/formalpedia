-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:14:24.717362+00:00
-- url     : https://prove2.me/theorems/79e4ac88-e5fa-48d3-9e7e-c7f196b5e02b
-- title:
--   Character Orthogonality Dual
-- statement:
--   Definitions and structural lemmas for Character Orthogonality Dual, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CharacterOrthogonalityDual.lean

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5
open scoped ComplexConjugate
namespace Formalism.FourierDecayAlt.P.A5x3
section Alg
variable {K : Type} [CommRing K] (R : Subring K) (ψ : AddChar K ℂ)
theorem mem_rng (x : K) : x ∈ LinearMap.range (Algebra.linearMap R K) ↔ x ∈ R := by
  constructor
  · rintro ⟨r, rfl⟩; exact r.2
  · intro h; exact ⟨⟨x, h⟩, rfl⟩
theorem mk_eq_mk (x y : K) :
    (Submodule.Quotient.mk x : KR R) = Submodule.Quotient.mk y ↔ x - y ∈ R := by
  rw [Submodule.Quotient.eq, mem_rng]
variable {R ψ}
theorem psi_of_mem (h : ∀ a : K, (∀ r ∈ R, ψ (a * r) = 1) ↔ a ∈ R) {a : K} (ha : a ∈ R) :
    ψ a = 1 := by
  simpa using (h a).2 ha 1 R.one_mem
theorem psiKR_mk (h : ∀ a : K, (∀ r ∈ R, ψ (a * r) = 1) ↔ a ∈ R) (a : K) :
    psiKR R ψ (Submodule.Quotient.mk a) = ψ a := by
  unfold psiKR
  have h1 : Quotient.out (Submodule.Quotient.mk a : KR R) - a ∈ R :=
    (mk_eq_mk R _ _).1 (Submodule.Quotient.mk_out _)
  have h2 : Quotient.out (Submodule.Quotient.mk a : KR R)
      = (Quotient.out (Submodule.Quotient.mk a : KR R) - a) + a := by ring
  rw [h2, AddChar.map_add_eq_mul, psi_of_mem h h1, one_mul]
def psiBar (h : ∀ a : K, (∀ r ∈ R, ψ (a * r) = 1) ↔ a ∈ R) : AddChar (KR R) ℂ where
  toFun := psiKR R ψ
  map_zero_eq_one' := by
    have := psiKR_mk h 0
    rw [Submodule.Quotient.mk_zero] at this
    rw [this, AddChar.map_zero_eq_one]
  map_add_eq_mul' := by
    intro x y
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      induction y using Submodule.Quotient.induction_on with
      | H y =>
        rw [← Submodule.Quotient.mk_add, psiKR_mk h, psiKR_mk h, psiKR_mk h,
          AddChar.map_add_eq_mul]
variable {C : Type} [AddCommGroup C] [Module R C]
def chC (h : ∀ a : K, (∀ r ∈ R, ψ (a * r) = 1) ↔ a ∈ R) (μ : C →ₗ[R] KR R) : AddChar C ℂ :=
  (psiBar h).compAddMonoidHom μ.toAddMonoidHom
def chS (h : ∀ a : K, (∀ r ∈ R, ψ (a * r) = 1) ↔ a ∈ R) (S : Submodule R (C →ₗ[R] KR R))
    (c : C) : AddChar S ℂ :=
  (psiBar h).compAddMonoidHom
    ((LinearMap.applyₗ c : (C →ₗ[R] KR R) →ₗ[R] KR R).comp S.subtype).toAddMonoidHom
end Alg
section Alg2
variable {K : Type} [CommRing K] {R : Subring K} {ψ : AddChar K ℂ}
variable {C : Type} [AddCommGroup C] [Module R C]
end Alg2
section Cok
variable {K : Type} [CommRing K] (R : Subring K) {n : ℕ}
def rowFun (Z : Matrix (Fin n) (Fin n) K) (a : Fin n) : (Fin n → R) →ₗ[R] KR R :=
  (Submodule.mkQ _).comp ((LinearMap.proj a : (Fin n → K) →ₗ[R] K).comp
    ((Z⁻¹.mulVecLin.restrictScalars R).comp (coeLin R)))
end Cok
section Top
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K}
  {ψ : AddChar K ℂ}
end Top
end Formalism.FourierDecayAlt.P.A5x3
namespace Formalism.FourierDecayAlt.P
open A5x3
end Formalism.FourierDecayAlt.P


