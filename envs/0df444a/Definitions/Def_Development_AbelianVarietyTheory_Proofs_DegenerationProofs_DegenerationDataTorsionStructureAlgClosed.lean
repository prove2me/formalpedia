-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataTorsionStructureAlgClosed
-- name    : Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataTorsionStructureAlgClosed
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:47:08.677913+00:00
-- url     : https://prove2.me/theorems/22924062-d47b-4246-baf1-15d775075329
-- title:
--   Degeneration Data Torsion Structure Alg Closed
-- statement:
--   Definitions and structural lemmas for Degeneration Data Torsion Structure Alg Closed, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/DegenerationDataTorsionStructureAlgClosed.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationWeilPairingPropertiesStatement
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_face__8d4277abb339

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
noncomputable section
namespace GlobalTheory.Ex.QStr
@[ext] structure Ext {O : Type} [CommRing O] (N : NumD O) (b : N.A) where
  x : N.X
  u : Oˣ
instance {O : Type} [CommRing O] (N : NumD O) (b : N.A) : CommGroup (Ext N b) where
  mul e e' := ⟨e.x + e'.x, e.u * e'.u / N.θ (N.c e.x) (N.c e'.x) b⟩
  one := ⟨0, 1⟩
  inv e := ⟨-e.x, N.θ (N.c (-e.x)) (N.c e.x) b / e.u⟩
  mul_assoc e e' e'' := by
    refine Ext.ext (add_assoc e.x e'.x e''.x) ?_
    change e.u * e'.u / N.θ (N.c e.x) (N.c e'.x) b * e''.u / N.θ (N.c (e.x + e'.x)) (N.c e''.x) b =
      e.u * (e'.u * e''.u / N.θ (N.c e'.x) (N.c e''.x) b) / N.θ (N.c e.x) (N.c (e'.x + e''.x)) b
    have a := congrArg Additive.ofMul (N.cub.coc (N.c e.x) (N.c e'.x) (N.c e''.x) b)
    rw [N.c_add, N.c_add]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div] at a ⊢
    linear_combination (norm := abel) -a
  one_mul e := by
    refine Ext.ext (zero_add e.x) ?_
    change 1 * e.u / N.θ (N.c 0) (N.c e.x) b = e.u
    rw [N.c_zero, N.cub.face, one_mul, div_one]
  mul_one e := by
    refine Ext.ext (add_zero e.x) ?_
    change e.u * 1 / N.θ (N.c e.x) (N.c 0) b = e.u
    rw [N.c_zero, N.cub.face₂, mul_one, div_one]
  inv_mul_cancel e := by
    refine Ext.ext (neg_add_cancel e.x) ?_
    change N.θ (N.c (-e.x)) (N.c e.x) b / e.u * e.u / N.θ (N.c (-e.x)) (N.c e.x) b = 1
    rw [div_mul_cancel, div_self']
  mul_comm e e' := by
    refine Ext.ext (add_comm e.x e'.x) ?_
    change e.u * e'.u / N.θ (N.c e.x) (N.c e'.x) b = e'.u * e.u / N.θ (N.c e'.x) (N.c e.x) b
    rw [N.cub.s01, mul_comm]
section Chr
variable {X U ι : Type} [AddCommGroup X] [CommGroup U] [Fintype ι] (v : Module.Basis ι ℤ X)
def chr : (ι → U) →* (Multiplicative X →* U) :=
  MonoidHom.mk' (fun u => MonoidHom.mk' (fun χ => ∏ i, u i ^ v.repr χ.toAdd i) fun a b => by
    simp [zpow_add, Finset.prod_mul_distrib]) fun u u' => by
    ext χ
    simp [mul_zpow, Finset.prod_mul_distrib]
end Chr
section Main
variable {C : Type} [Field C] [IsAlgClosed C] (N : NumD C) {k : ℕ}
end Main
end GlobalTheory.Ex.QStr
end


