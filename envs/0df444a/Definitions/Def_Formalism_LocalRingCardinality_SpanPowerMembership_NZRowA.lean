-- Prove2me | Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZRowA
-- name    : Formalism_LocalRingCardinality_SpanPowerMembership_NZRowA
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T18:33:08.242986+00:00
-- url     : https://prove2.me/theorems/101acec7-baac-446c-9b9e-fc9935c1d1e3
-- title:
--   NZRow A
-- statement:
--   Definitions and structural lemmas for NZRow A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZRowA.lean

import Definitions.Def_Formalism_LocalRingCardinality_DataRows
import Definitions.Def_Formalism_LocalRingCardinality_DataForms
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


set_option autoImplicit false
noncomputable section
namespace Formalism.BasicNotions.Examples₂.NZ
open NumberField IsDedekindDomain Formalism.BasicNotions
section Std
variable (K : Type) [Field K] [NumberField K] [StarRing K] (n : ℕ)
abbrev stdH : HLat K where
  V := Fin n → K
  ι := Fin n
  b := Pi.basisFun K (Fin n)
  X := fun _ => 1
  L := Submodule.span (𝓞 K) (Set.range (Pi.basisFun K (Fin n)))
end Std
section JB0
variable {K : Type} [Field K] (σ : K →+* ℂ) {n : ℕ}
  {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (b : OrthonormalBasis (Fin n) ℂ V)
def jB : (Fin n → K) →ₛₗ[σ] V where
  toFun x := ∑ i, σ (x i) • b i
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c x := by simp [mul_smul, Finset.smul_sum]
open Classical in

def genB : Finset V := Finset.univ.image b
end JB0
section JB
variable {K : Type} [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ) {n : ℕ}
  {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (b : OrthonormalBasis (Fin n) ℂ V)
theorem genB_span : Submodule.span ℂ (genB b : Set V) = ⊤ := by
  have := b.toBasis.span_eq
  rw [b.coe_toBasis] at this
  classical
  rw [genB, Finset.coe_image, Finset.coe_univ, Set.image_univ]
  exact this
def oB {O : Type} [CommRing O] (φ : O →+* ℂ) : Rows.OLat O φ V := ⟨genB b, genB_span b⟩
end JB
end Formalism.BasicNotions.Examples₂.NZ


