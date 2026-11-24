-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsTwistedGroupLike
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsTwistedGroupLike
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T23:29:09.335518+00:00
-- url     : https://prove2.me/theorems/7f41f937-ad68-4b23-a0f4-13061c3edf3e
-- title:
--   Exists Twisted Group Like
-- statement:
--   Definitions and structural lemmas for Exists Twisted Group Like, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsTwistedGroupLike.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_MemPrimitiveTensorsIffIsPrimitiveElem
import Theorems.Thm_GlobalTheory_IsBicharacter_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open TensorProduct Coalgebra WithConv
noncomputable section
namespace GlobalTheory
namespace TwistedGroupLike
variable {K H : Type} [Field K] [CommRing H] [Bialgebra K H]
def counitLeft : H ⊗[K] H →ₐ[K] H :=
  (Algebra.TensorProduct.lid K H).toAlgHom.comp
    (Algebra.TensorProduct.map (Bialgebra.counitAlgHom K H) (AlgHom.id K H))
@[simp] theorem counitLeft_tmul (a b : H) : counitLeft (a ⊗ₜ[K] b) = counit (R := K) a • b := by
  simp [counitLeft]
theorem counitLeft_eq_lid (y : H ⊗[K] H) :
    counitLeft y = TensorProduct.lid K H (LinearMap.rTensor H (counit (R := K)) y) := by
  induction y with
  | zero => simp
  | add a b ha hb => simp [ha, hb]
  | tmul a b => simp
theorem counitLeft_comul (x : H) : counitLeft (comul (R := K) x) = x := by
  rw [counitLeft_eq_lid, Coalgebra.rTensor_counit_comul, TensorProduct.lid_tmul, one_smul]
def IsCocycle (c : H ⊗[K] H) : Prop :=
  c ⊗ₜ[K] (1 : H) * Algebra.TensorProduct.map (Bialgebra.comulAlgHom K H) (AlgHom.id K H) c =
    (Algebra.TensorProduct.assoc K K K H H H).symm
      ((1 : H) ⊗ₜ[K] c * Algebra.TensorProduct.map (AlgHom.id K H) (Bialgebra.comulAlgHom K H) c)
theorem counitLeft_assoc_symm_tmul (a : H) (y : H ⊗[K] H) :
    Algebra.TensorProduct.map counitLeft (AlgHom.id K H)
      ((Algebra.TensorProduct.assoc K K K H H H).symm (a ⊗ₜ[K] y)) = counit (R := K) a • y := by
  induction y with
  | zero => simp
  | add y z hy hz => simp only [TensorProduct.tmul_add, map_add, smul_add, hy, hz]
  | tmul b d => simp [TensorProduct.smul_tmul']
theorem counitLeft_map_comul (y : H ⊗[K] H) :
    Algebra.TensorProduct.map counitLeft (AlgHom.id K H)
      (Algebra.TensorProduct.map (Bialgebra.comulAlgHom K H) (AlgHom.id K H) y) = y := by
  induction y with
  | zero => simp
  | add y z hy hz => simp only [map_add, hy, hz]
  | tmul a b => simp [counitLeft_comul]
theorem counitLeft_assoc_symm_map_comul (y : H ⊗[K] H) :
    Algebra.TensorProduct.map counitLeft (AlgHom.id K H)
      ((Algebra.TensorProduct.assoc K K K H H H).symm
        (Algebra.TensorProduct.map (AlgHom.id K H) (Bialgebra.comulAlgHom K H) y)) =
      comul (R := K) (counitLeft y) := by
  induction y with
  | zero => simp
  | add y z hy hz => simp only [map_add, hy, hz]
  | tmul a b =>
    rw [Algebra.TensorProduct.map_tmul, counitLeft_assoc_symm_tmul, counitLeft_tmul, map_smul]
    rfl
theorem counitLeft_eq_smul_one (c : H ⊗[K] H) (hu : IsUnit c) (hc : IsCocycle c) :
    counitLeft c = counit (R := K) (counitLeft c) • (1 : H) := by
  have h := congrArg (Algebra.TensorProduct.map counitLeft (AlgHom.id K H)) hc
  rw [map_mul, map_mul, map_mul, counitLeft_map_comul, counitLeft_assoc_symm_map_comul,
    counitLeft_assoc_symm_tmul, Bialgebra.counit_one, one_smul, Algebra.TensorProduct.map_tmul,
    AlgHom.id_apply, mul_comm] at h
  have h5 : counitLeft c ⊗ₜ[K] (1 : H) = comul (R := K) (counitLeft c) := hu.mul_left_cancel h
  have h6 := congrArg counitLeft h5
  rw [counitLeft_tmul, counitLeft_comul] at h6
  exact h6.symm
def comulTw (c : H ⊗[K] H) : H →ₗ[K] H ⊗[K] H := LinearMap.mulLeft K c ∘ₗ comul
theorem comulTw_apply (c : H ⊗[K] H) (x : H) : comulTw c x = c * comul (R := K) x := rfl
theorem rTensor_comulTw (c y : H ⊗[K] H) :
    (comulTw c).rTensor H y =
      c ⊗ₜ[K] (1 : H) * Algebra.TensorProduct.map (Bialgebra.comulAlgHom K H) (AlgHom.id K H) y := by
  induction y with
  | zero => simp
  | add y z hy hz => simp only [map_add, mul_add, hy, hz]
  | tmul a b => simp [comulTw_apply, Algebra.TensorProduct.tmul_mul_tmul]
theorem lTensor_comulTw (c y : H ⊗[K] H) :
    (comulTw c).lTensor H y =
      (1 : H) ⊗ₜ[K] c * Algebra.TensorProduct.map (AlgHom.id K H) (Bialgebra.comulAlgHom K H) y := by
  induction y with
  | zero => simp
  | add y z hy hz => simp only [map_add, mul_add, hy, hz]
  | tmul a b => simp [comulTw_apply, Algebra.TensorProduct.tmul_mul_tmul]
theorem assoc_eq (z : (H ⊗[K] H) ⊗[K] H) :
    TensorProduct.assoc K H H H z = Algebra.TensorProduct.assoc K K K H H H z := rfl
theorem map_comul_id (y : H ⊗[K] H) :
    Algebra.TensorProduct.map (Bialgebra.comulAlgHom K H) (AlgHom.id K H) y =
      (comul (R := K) (A := H)).rTensor H y := by
  induction y with
  | zero => simp
  | add y z hy hz => simp only [map_add, hy, hz]
  | tmul a b => simp
theorem map_id_comul (y : H ⊗[K] H) :
    Algebra.TensorProduct.map (AlgHom.id K H) (Bialgebra.comulAlgHom K H) y =
      (comul (R := K) (A := H)).lTensor H y := by
  induction y with
  | zero => simp
  | add y z hy hz => simp only [map_add, hy, hz]
  | tmul a b => simp
theorem comulTw_coassoc (c : H ⊗[K] H) (hc : IsCocycle c) (x : H) :
    TensorProduct.assoc K H H H ((comulTw c).rTensor H (comulTw c x)) =
      (comulTw c).lTensor H (comulTw c x) := by
  rw [rTensor_comulTw, lTensor_comulTw, comulTw_apply, assoc_eq,
    map_mul (Algebra.TensorProduct.map (Bialgebra.comulAlgHom K H) (AlgHom.id K H)),
    map_mul (Algebra.TensorProduct.map (AlgHom.id K H) (Bialgebra.comulAlgHom K H)),
    ← mul_assoc, ← mul_assoc, hc, map_mul (Algebra.TensorProduct.assoc K K K H H H),
    AlgEquiv.apply_symm_apply]
  rw [map_comul_id (comul x), map_id_comul (comul x), ← assoc_eq, Coalgebra.coassoc_apply]
def kappa (c : H ⊗[K] H) : K := counit (R := K) (counitLeft c)
theorem kappa_ne_zero (c : H ⊗[K] H) (hu : IsUnit c) : kappa c ≠ 0 := by
  have := hu.map ((Bialgebra.counitAlgHom K H).comp counitLeft)
  exact this.ne_zero
theorem comm_eq (y : H ⊗[K] H) : TensorProduct.comm K H H y = Algebra.TensorProduct.comm K H H y :=
  rfl
theorem comm_comulTw [Coalgebra.IsCocomm K H] (c : H ⊗[K] H)
    (hs : Algebra.TensorProduct.comm K H H c = c) (x : H) :
    TensorProduct.comm K H H (comulTw c x) = comulTw c x := by
  rw [comulTw_apply, comm_eq, map_mul, hs, ← comm_eq, Coalgebra.comm_comul]
theorem lid_rTensor_smul_counit (c : H ⊗[K] H) (y : H ⊗[K] H) :
    TensorProduct.lid K H (((kappa c)⁻¹ • counit (R := K) (A := H)).rTensor H y) =
      (kappa c)⁻¹ • counitLeft y := by
  induction y with
  | zero => simp
  | add y z hy hz => simp only [map_add, smul_add, hy, hz]
  | tmul a b => simp [smul_smul]
theorem rid_lTensor_smul_counit (c : H ⊗[K] H) (y : H ⊗[K] H) :
    TensorProduct.rid K H (((kappa c)⁻¹ • counit (R := K) (A := H)).lTensor H y) =
      (kappa c)⁻¹ • counitLeft (TensorProduct.comm K H H y) := by
  induction y with
  | zero => simp
  | add y z hy hz => simp only [map_add, smul_add, hy, hz]
  | tmul a b => simp [smul_smul]
theorem counitLeft_comulTw (c : H ⊗[K] H) (hu : IsUnit c) (hc : IsCocycle c) (x : H) :
    (kappa c)⁻¹ • counitLeft (comulTw c x) = x := by
  rw [comulTw_apply, map_mul, counitLeft_comul, counitLeft_eq_smul_one c hu hc, smul_mul_assoc,
    one_mul, ← kappa, smul_smul, inv_mul_cancel₀ (kappa_ne_zero c hu), one_smul]
theorem rTensor_counit_comulTw (c : H ⊗[K] H) (hu : IsUnit c) (hc : IsCocycle c) (x : H) :
    ((kappa c)⁻¹ • counit (R := K) (A := H)).rTensor H (comulTw c x) = 1 ⊗ₜ[K] x := by
  apply (TensorProduct.lid K H).injective
  rw [lid_rTensor_smul_counit, counitLeft_comulTw c hu hc, TensorProduct.lid_tmul, one_smul]
theorem lTensor_counit_comulTw [Coalgebra.IsCocomm K H] (c : H ⊗[K] H) (hu : IsUnit c)
    (hc : IsCocycle c) (hs : Algebra.TensorProduct.comm K H H c = c) (x : H) :
    ((kappa c)⁻¹ • counit (R := K) (A := H)).lTensor H (comulTw c x) = x ⊗ₜ[K] (1 : K) := by
  apply (TensorProduct.rid K H).injective
  rw [rid_lTensor_smul_counit, comm_comulTw c hs, counitLeft_comulTw c hu hc,
    TensorProduct.rid_tmul, one_smul]
variable (K H) in

def Twisted (_c : H ⊗[K] H) : Type := H
instance (c : H ⊗[K] H) : AddCommGroup (Twisted K H c) := inferInstanceAs (AddCommGroup H)
instance (c : H ⊗[K] H) : Module K (Twisted K H c) := inferInstanceAs (Module K H)
instance (c : H ⊗[K] H) [Module.Finite K H] : Module.Finite K (Twisted K H c) :=
  inferInstanceAs (Module.Finite K H)
def twistedCoalgebra [Coalgebra.IsCocomm K H] (c : H ⊗[K] H) (hu : IsUnit c) (hc : IsCocycle c)
    (hs : Algebra.TensorProduct.comm K H H c = c) : Coalgebra K (Twisted K H c) where
  comul := comulTw (K := K) (H := H) c
  counit := (kappa c)⁻¹ • counit (R := K) (A := H)
  coassoc := LinearMap.ext fun x => comulTw_coassoc c hc x
  rTensor_counit_comp_comul := LinearMap.ext fun x => rTensor_counit_comulTw c hu hc x
  lTensor_counit_comp_comul := LinearMap.ext fun x => lTensor_counit_comulTw c hu hc hs x
end TwistedGroupLike
end GlobalTheory


