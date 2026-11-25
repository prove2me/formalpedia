-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsDvdOfAlgebraic
-- name    : Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsDvdOfAlgebraic
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T01:22:51.897286+00:00
-- url     : https://prove2.me/theorems/906b7d78-96cf-46b1-b445-cfe9965a62ee
-- title:
--   Exists Dvd Of Algebraic
-- statement:
--   Definitions and structural lemmas for Exists Dvd Of Algebraic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsDvdOfAlgebraic.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_PolyImgSuccAbove
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.SectionBasis
open MvPolynomial ReciprocityTheory.ChartRestriction.G.T0 GlobalTheory.GenericSection
open scoped TensorProduct
section Univ
variable {K Ω Kl K' : Type} [Field K] [Field Ω] [Algebra K Ω] [Field Kl] [Field K'] [Algebra K Kl]
  [Algebra Kl K'] [Algebra K K'] [IsScalarTower K Kl K']
variable (K Kl K') in

def incl : Ω →+* K' ⊗[Kl] (Kl ⊗[K] Ω) :=
  (Algebra.TensorProduct.includeRight : (Kl ⊗[K] Ω) →ₐ[Kl] K' ⊗[Kl] (Kl ⊗[K] Ω)).toRingHom.comp
    (Algebra.TensorProduct.includeRight : Ω →ₐ[K] Kl ⊗[K] Ω).toRingHom
end Univ
section Comp
variable {K Ω K' : Type} [Field K] [Field Ω] [Algebra K Ω] [Field K'] [Algebra K K'] {D N : ℕ}
end Comp
section All
variable {K K' : Type} [Field K] [Field K'] [Algebra K K'] {D N : ℕ} {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ Z, Field (Ω Z)] [∀ Z, Algebra K (Ω Z)]
end All
section Loc
variable {K Kl K' : Type} [Field K] [Field Kl] [Field K'] [Algebra K Kl] [Algebra Kl K'] [Algebra K K']
  [IsScalarTower K Kl K'] {ι : Type} [Fintype ι] {Ω : ι → Type} [∀ Z, Field (Ω Z)] [∀ Z, Algebra K (Ω Z)]
end Loc
end GlobalTheory.SectionBasis


