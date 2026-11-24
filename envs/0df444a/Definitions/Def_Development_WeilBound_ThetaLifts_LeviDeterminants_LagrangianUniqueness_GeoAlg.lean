-- Prove2me | Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_LagrangianUniqueness_GeoAlg
-- name    : Development_WeilBound_ThetaLifts_LeviDeterminants_LagrangianUniqueness_GeoAlg
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:56:45.843312+00:00
-- url     : https://prove2.me/theorems/b367de3a-a8f0-415b-83bb-0ba5c3a4cc12
-- title:
--   Geo Alg
-- statement:
--   Definitions and structural lemmas for Geo Alg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/LagrangianUniqueness/GeoAlg.lean

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
open Matrix GlobalTheory.WeilM Module
namespace PositivityTheory.ThKF0.Geo
section Form
variable {F : Type} [Field F] {κ : Type} [Fintype κ]
def om (F : Type) [Field F] (κ : Type) [Fintype κ] : LinearMap.BilinForm F ((κ → F) × (κ → F)) :=
  LinearMap.mk₂ F (fun w w' => w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2)
    (fun _ _ _ => by simp only [Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]; ring)
    (fun _ _ _ => by simp only [Prod.smul_fst, Prod.smul_snd, smul_dotProduct, dotProduct_smul, smul_eq_mul]; ring)
    (fun _ _ _ => by simp only [Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]; ring)
    (fun _ _ _ => by simp only [Prod.smul_fst, Prod.smul_snd, smul_dotProduct, dotProduct_smul, smul_eq_mul]; ring)
end Form
section Abs
variable {F : Type} [Field F] {A : Type} [CommRing A] [Algebra F A]
variable (A) in

def emb (κ : Type) : ((κ → F) × (κ → F)) →ₗ[F] ((κ → A) × (κ → A)) :=
  ((Algebra.linearMap F A).compLeft κ).prodMap ((Algebra.linearMap F A).compLeft κ)
variable {VA : Type} [AddCommGroup VA] [Module A VA] [Module F VA] [IsScalarTower F A VA] {BA : VA → VA → A}
  {κ : Type} [Fintype κ] {V : Type} [AddCommGroup V] [Module F V]
variable {VB : Type} [AddCommGroup VB] [Module A VB] [Module F VB] [IsScalarTower F A VB] {BB : VB → VB → A}
  {κ₁ : Type} [Fintype κ₁] {V₁ : Type} [AddCommGroup V₁] [Module F V₁] {U : Type} [AddCommGroup U] [Module F U]
end Abs
section Mat
variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
  {α β α' β' : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype α'] [DecidableEq α']
  [Fintype β'] [DecidableEq β']
end Mat
end PositivityTheory.ThKF0.Geo


