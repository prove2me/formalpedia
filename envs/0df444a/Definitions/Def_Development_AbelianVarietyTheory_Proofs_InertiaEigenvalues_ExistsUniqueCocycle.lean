-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUniqueCocycle
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUniqueCocycle
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T01:51:58.808279+00:00
-- url     : https://prove2.me/theorems/86a72896-0c0d-4416-9a1d-d29c0ce76a43
-- title:
--   Exists Unique Cocycle
-- statement:
--   Definitions and structural lemmas for Exists Unique Cocycle, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsUniqueCocycle.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.HlCoc
open Topology
def SD (M G : Type) : Type := M × G
variable {G M : Type} [Group G] [AddCommGroup M] [DistribMulAction G M]
def SD.mk (x : M) (g : G) : SD M G := (x, g)
instance : Mul (SD M G) := ⟨fun p q => (p.1 + p.2 • q.1, p.2 * q.2)⟩
instance : One (SD M G) := ⟨((0 : M), (1 : G))⟩
instance : Inv (SD M G) := ⟨fun p => (-(p.2⁻¹ • p.1), p.2⁻¹)⟩
@[simp] lemma mul_fst (p q : SD M G) : (p * q).1 = p.1 + p.2 • q.1 := rfl
@[simp] lemma mul_snd (p q : SD M G) : (p * q).2 = p.2 * q.2 := rfl
omit [DistribMulAction G M] in
@[simp] lemma one_fst : (1 : SD M G).1 = 0 := rfl
omit [DistribMulAction G M] in
@[simp] lemma one_snd : (1 : SD M G).2 = 1 := rfl
@[simp] lemma inv_fst (p : SD M G) : (p⁻¹).1 = -(p.2⁻¹ • p.1) := rfl
@[simp] lemma inv_snd (p : SD M G) : (p⁻¹).2 = p.2⁻¹ := rfl
instance : Group (SD M G) :=
  Group.ofLeftAxioms
    (fun p q r => Prod.ext (by simp [smul_add, mul_smul, add_assoc]) (by simp [mul_assoc]))
    (fun p => Prod.ext (by simp) (by simp))
    (fun p => Prod.ext (by simp) (by simp))
def sndHom : SD M G →* G where
  toFun p := p.2
  map_one' := rfl
  map_mul' _ _ := rfl
variable [TopologicalSpace G] [TopologicalSpace M]
instance : TopologicalSpace (SD M G) := inferInstanceAs (TopologicalSpace (M × G))
omit [Group G] [AddCommGroup M] [DistribMulAction G M] in
lemma cont_fst : Continuous (fun p : SD M G => p.1) := continuous_fst
omit [Group G] [AddCommGroup M] [DistribMulAction G M] in
lemma cont_snd : Continuous (fun p : SD M G => p.2) := continuous_snd
instance [T2Space M] [T2Space G] : T2Space (SD M G) := inferInstanceAs (T2Space (M × G))
variable [IsTopologicalGroup G] [IsTopologicalAddGroup M] [ContinuousSMul G M]
instance : IsTopologicalGroup (SD M G) where
  continuous_mul := by
    refine Continuous.prodMk ?_ ?_
    · exact (cont_fst.comp continuous_fst).add
        ((cont_snd.comp continuous_fst).smul (cont_fst.comp continuous_snd))
    · exact (cont_snd.comp continuous_fst).mul (cont_snd.comp continuous_snd)
  continuous_inv := by
    refine Continuous.prodMk ?_ ?_
    · exact (cont_snd.inv.smul cont_fst).neg
    · exact cont_snd.inv
end GlobalTheory.HlCoc


