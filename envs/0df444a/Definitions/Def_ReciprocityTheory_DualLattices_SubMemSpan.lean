-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_SubMemSpan
-- name    : ReciprocityTheory_DualLattices_SubMemSpan
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:28:24.625789+00:00
-- url     : https://prove2.me/theorems/8c7283aa-6f30-47ec-8103-41b689b2b3ca
-- title:
--   Sub Mem Span
-- statement:
--   Definitions and structural lemmas for Sub Mem Span, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SubMemSpan.lean

import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_IsPairingValueAddRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct
namespace ReciprocityTheory.PGsh
universe u
variable {R₀ : Type u} [CommRing R₀]
namespace OAdj
variable {B : BX R₀} {O : LAlg R₀} (A : OAdj B O) {R : LAlg R₀} (s : LHom O R)
end OAdj
namespace DualPair
variable {R : LAlg R₀} (Dp : DualPair R)
lemma sub_mem_span (d : (Dp.D : Type u)) : d - Dp.σ.1 (Dp.π.1 d) ∈ Ideal.span {Dp.η} := by
  rw [← Dp.ker_eq, RingHom.mem_ker, map_sub, Dp.sect, sub_self]
lemma mul_span (a b : (Dp.D : Type u)) (ha : a ∈ Ideal.span {Dp.η}) (hb : b ∈ Ideal.span {Dp.η}) :
    a * b = 0 := by
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
  obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.1 hb
  calc c * Dp.η * (d * Dp.η) = c * d * (Dp.η * Dp.η) := by ring
    _ = 0 := by rw [Dp.η_sq, mul_zero]
def mr (r : (R : Type u)) : LHom Dp.D Dp.D :=
  ⟨{ toFun := fun d => Dp.σ.1 (Dp.π.1 d) + Dp.σ.1 r * (d - Dp.σ.1 (Dp.π.1 d))
     map_one' := by simp
     map_mul' := fun d e => by
       have hk := Dp.mul_span _ _ (Dp.sub_mem_span d) (Dp.sub_mem_span e)
       simp only [map_mul]
       linear_combination (Dp.σ.1 r - Dp.σ.1 r * Dp.σ.1 r) * hk
     map_zero' := by simp
     map_add' := fun d e => by simp only [map_add]; ring
     commutes' := fun c => by simp },
   ⟨fun d hd => by
     have h1 := hd.map Dp.π.1
     have e : Dp.π.1 (Dp.σ.1 (Dp.π.1 d) + Dp.σ.1 r * (d - Dp.σ.1 (Dp.π.1 d))) = Dp.π.1 d := by
       simp [Dp.sect]
     refine Dp.π.2.map_nonunit d ?_
     convert h1 using 1
     exact e.symm⟩⟩
end DualPair
namespace OAdj
variable {B : BX R₀} {O : LAlg R₀} (A : OAdj B O) {R : LAlg R₀} (s : LHom O R)
end OAdj
end ReciprocityTheory.PGsh


