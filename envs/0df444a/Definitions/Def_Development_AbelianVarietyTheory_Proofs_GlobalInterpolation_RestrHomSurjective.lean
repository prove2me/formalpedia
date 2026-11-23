-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RestrHomSurjective
-- name    : Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RestrHomSurjective
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T18:51:58.820439+00:00
-- url     : https://prove2.me/theorems/23bad410-b99e-403f-b1aa-87e53c53ad0a
-- title:
--   Restr Hom Surjective
-- statement:
--   Definitions and structural lemmas for Restr Hom Surjective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/RestrHomSurjective.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DisjointSpanPerpLat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal
namespace GlobalTheory.UnitVectorStabiliser
section General
open Formalism.UG
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
  (s : A →+* A) (J : Matrix n n A)
theorem hf_add_right (x y z : n → A) : hform s J x (y + z) = hform s J x y + hform s J x z := by
  simp only [hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]
theorem hf_smul_right (c : A) (x y : n → A) : hform s J x (c • y) = c * hform s J x y := by
  simp only [hform, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
theorem hf_eq (x y : n → A) : hform s J x y = (fun i => s (x i)) ⬝ᵥ (J *ᵥ y) := by
  simp only [hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
theorem hf_mulVec (g : Matrix n n A) (x y : n → A) :
    hform s J (g *ᵥ x) (g *ᵥ y) = hform s (cT s g * J * g) x y := by
  rw [hf_eq, hf_eq, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec _ (cT s g)]
  congr 1
  funext i
  simp [cT, Matrix.vecMul, Matrix.mulVec, dotProduct, mul_comm]
def hfLin (x : n → A) : (n → A) →ₗ[A] A where
  toFun := hform s J x
  map_add' := hf_add_right s J x
  map_smul' c y := hf_smul_right s J c x y
end General
section Place
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (v : HeightOneSpectrum (𝓞 F))
theorem mem_stabVec (x : Fin M → Ev F E v) (g : HA (Fv F v) σ J) :
    g ∈ stabVec σ J v x ↔ act σ J v g x = x := by
  unfold stabVec
  rw [MulAction.mem_stabilizer_iff]
  exact ⟨fun h => congrFun h 0, fun h => funext fun _ => h⟩
theorem act_mul (g h : HA (Fv F v) σ J) (x : Fin M → Ev F E v) :
    act σ J v (g * h) x = act σ J v g (act σ J v h x) := by
  unfold act
  rw [Matrix.mulVec_mulVec]; rfl
theorem act_one (x : Fin M → Ev F E v) : act σ J v 1 x = x := Matrix.one_mulVec x
theorem hR_act (g : HA (Fv F v) σ J) (y z : Fin M → Ev F E v) :
    hR (Fv F v) σ J (act σ J v g y) (act σ J v g z) = hR (Fv F v) σ J y z := by
  unfold hR act
  rw [hf_mulVec]
  congr 1
  exact (show HR (Fv F v) σ J from g).2
theorem act_mem_perp_iff (x : Fin M → Ev F E v) (g : HA (Fv F v) σ J) (hg : g ∈ stabVec σ J v x)
    (y : Fin M → Ev F E v) : act σ J v g y ∈ perp σ J v x ↔ y ∈ perp σ J v x := by
  show hR (Fv F v) σ J x (act σ J v g y) = 0 ↔ hR (Fv F v) σ J x y = 0
  rw [← hR_act σ J v g x y, (mem_stabVec σ J v x g).1 hg]
def restr (x : Fin M → Ev F E v) (g : HA (Fv F v) σ J) (hg : g ∈ stabVec σ J v x) :
    perp σ J v x ≃ₗ[Ev F E v] perp σ J v x where
  toFun y := ⟨act σ J v g y, (act_mem_perp_iff σ J v x g hg y).2 y.2⟩
  invFun y := ⟨act σ J v g⁻¹ y, (act_mem_perp_iff σ J v x g⁻¹ (inv_mem hg) y).2 y.2⟩
  map_add' y z := Subtype.ext (by
    show act σ J v g (y.1 + z.1) = act σ J v g y.1 + act σ J v g z.1
    unfold act
    rw [Matrix.mulVec_add])
  map_smul' c y := Subtype.ext (by
    show act σ J v g (c • y.1) = c • act σ J v g y.1
    unfold act
    rw [Matrix.mulVec_smul])
  left_inv y := Subtype.ext (by
    show act σ J v g⁻¹ (act σ J v g y) = y
    rw [← act_mul, inv_mul_cancel, act_one])
  right_inv y := Subtype.ext (by
    show act σ J v g (act σ J v g⁻¹ y) = y
    rw [← act_mul, mul_inv_cancel, act_one])
def restrHom (L' : Submodule (OEv F E v) (Fin M → Ev F E v)) (x : Fin M → Ev F E v) :
    (stabLat σ J v L' ⊓ stabVec σ J v x : Subgroup (HA (Fv F v) σ J)) →*
      unitaryLatIn σ J v (perp σ J v x) L' where
  toFun g := ⟨restr σ J v x g g.2.2, fun y z => hR_act σ J v g y z, fun y => g.2.1 y⟩
  map_one' := Subtype.ext (LinearEquiv.ext fun y => Subtype.ext (act_one σ J v y))
  map_mul' g h := Subtype.ext (LinearEquiv.ext fun y => Subtype.ext (act_mul σ J v g h y))
end Place
end GlobalTheory.UnitVectorStabiliser


