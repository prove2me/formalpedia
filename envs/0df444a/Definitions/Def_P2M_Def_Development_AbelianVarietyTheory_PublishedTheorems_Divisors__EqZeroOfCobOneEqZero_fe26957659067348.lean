-- Prove2me | Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__EqZeroOfCobOneEqZero_fe26957659067348
-- name    : P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__EqZeroOfCobOneEqZero_fe26957659067348
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T00:52:11.857411+00:00
-- url     : https://prove2.me/theorems/4582c12a-f6c2-4b76-838b-12c8755f6f8f
-- title:
--   Eq Zero Of Cob One Eq Zero
-- statement:
--   Definitions and structural lemmas for Eq Zero Of Cob One Eq Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/EqZeroOfCobOneEqZero.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToSpanSingletonConstGenInjective
import Theorems.Thm_GlobalTheory_AugCot_baseChangeAug_tmul
import Theorems.Thm_GlobalTheory_AugCot_baseChangeEquiv_tmul_d
import Theorems.Thm_GlobalTheory_AugCot_mvPolynomialBasis_apply
import Theorems.Thm_GlobalTheory_IsBicharacter_map
import Theorems.Thm_GlobalTheory_PDivGroup_muLieGen_dlogT
import Theorems.Thm_GlobalTheory_PDiv_digit_zero
import Theorems.Thm_GlobalTheory_PDiv_muChar_muT
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.AugCot.baseChangeAug_tmul
attribute [local simp] GlobalTheory.AugCot.baseChangeEquiv_tmul_d
attribute [local simp] GlobalTheory.AugCot.mvPolynomialBasis_apply
attribute [local simp] GlobalTheory.PDiv.digit_zero
attribute [local simp] GlobalTheory.PDiv.muChar_muT
attribute [local simp] GlobalTheory.PDivGroup.muLieGen_dlogT


set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra CategoryTheory
namespace GlobalTheory
namespace PDiv
section Level
variable {O A B : Type} [CommRing O] [CommRing A] [CommRing B] [Bialgebra O A] [Bialgebra O B]
variable (O A) in

def cobOne : A →ₗ[O] A ⊗[O] A :=
  comul - (TensorProduct.mk O A A).flip 1 - TensorProduct.mk O A A 1
theorem cobOne_apply (b : A) : cobOne O A b = comul b - b ⊗ₜ 1 - 1 ⊗ₜ b := rfl
variable (O A) in

def cobTwo : A ⊗[O] A →ₗ[O] A ⊗[O] (A ⊗[O] A) :=
  TensorProduct.mk O A (A ⊗[O] A) 1 - (TensorProduct.assoc O A A A).toLinearMap ∘ₗ comul.rTensor A
    + comul.lTensor A - ((TensorProduct.mk O A A).flip 1).lTensor A
theorem cobTwo_apply (c : A ⊗[O] A) : cobTwo O A c =
    1 ⊗ₜ c - TensorProduct.assoc O A A A (comul.rTensor A c) + comul.lTensor A c
      - ((TensorProduct.mk O A A).flip 1).lTensor A c := rfl
variable (O A) in

def symCocycles : Submodule O (A ⊗[O] A) :=
  LinearMap.ker (cobTwo O A) ⊓ LinearMap.ker ((TensorProduct.comm O A A).toLinearMap - LinearMap.id)
theorem mem_symCocycles {c : A ⊗[O] A} :
    c ∈ symCocycles O A ↔ cobTwo O A c = 0 ∧ TensorProduct.comm O A A c = c := by
  simp [symCocycles, sub_eq_zero]
theorem cobTwo_cobOne (b : A) : cobTwo O A (cobOne O A b) = 0 := by
  have h1 : ∀ t : A ⊗[O] A, TensorProduct.assoc O A A A (t ⊗ₜ 1) =
      ((TensorProduct.mk O A A).flip 1).lTensor A t := fun t => by
    induction t with
    | zero => simp
    | tmul a b => simp
    | add x y hx hy => simp only [add_tmul, map_add, hx, hy]
  have h2 : comul (R := O) (1 : A) = 1 ⊗ₜ 1 := by simp [Algebra.TensorProduct.one_def]
  simp only [cobTwo_apply, cobOne_apply, map_sub, tmul_sub, coassoc_apply, LinearMap.rTensor_tmul,
    LinearMap.lTensor_tmul, h1, h2, LinearMap.flip_apply, mk_apply]
  rw [assoc_tmul 1 1 b]
  abel
theorem cobOne_mem [IsCocomm O A] (b : A) : cobOne O A b ∈ symCocycles O A :=
  mem_symCocycles.2 ⟨cobTwo_cobOne b, by
    simp only [cobOne_apply, map_sub, comm_comul, comm_tmul]; abel⟩
abbrev pullbackTwo (f : A →ₐc[O] B) : A ⊗[O] A →ₗ[O] B ⊗[O] B :=
  TensorProduct.map (f : A →ₗ[O] B) (f : A →ₗ[O] B)
theorem pullTwo_comul (f : A →ₐc[O] B) (a : A) : pullbackTwo f (comul a) = comul (f a) :=
  LinearMap.congr_fun (CoalgHomClass.map_comp_comul f) a
theorem pullTwo_cobOne (f : A →ₐc[O] B) (b : A) :
    pullbackTwo f (cobOne O A b) = cobOne O B (f b) := by
  simp [cobOne_apply, pullTwo_comul]
theorem cobTwo_pullTwo (f : A →ₐc[O] B) (c : A ⊗[O] A) :
    cobTwo O B (pullbackTwo f c) = TensorProduct.map (f : A →ₗ[O] B) (pullbackTwo f) (cobTwo O A c) := by
  induction c with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a b =>
    have h := TensorProduct.map_map_assoc (f : A →ₗ[O] B) (f : A →ₗ[O] B) (f : A →ₗ[O] B)
      (comul a ⊗ₜ b)
    simp [cobTwo_apply, pullTwo_comul, h]
theorem pullTwo_mem (f : A →ₐc[O] B) {c : A ⊗[O] A} (hc : c ∈ symCocycles O A) :
    pullbackTwo f c ∈ symCocycles O B := by
  rw [mem_symCocycles] at hc ⊢
  exact ⟨by rw [cobTwo_pullTwo, hc.1, map_zero], by rw [← TensorProduct.map_comm, hc.2]⟩
theorem pullTwo_comp {D : Type} [CommRing D] [Bialgebra O D] (g : B →ₐc[O] D) (f : A →ₐc[O] B)
    (c : A ⊗[O] A) : pullbackTwo (g.comp f) c = pullbackTwo g (pullbackTwo f c) := by
  induction c with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a b => simp
end Level
end PDiv
namespace PDivGroup
open PDiv
variable {p : ℕ} {O : Type} [CommRing O] (G H K : PDivGroup p O)
def funs : Submodule O (∀ n, G.A n) where
  carrier := {b | ∀ n, G.res n (b (n + 1)) = b n}
  zero_mem' _ := map_zero _
  add_mem' {v w} hv hw n := by rw [Pi.add_apply, map_add, hv n, hw n, Pi.add_apply]
  smul_mem' c w hw n := by rw [Pi.smul_apply, map_smul, hw n, Pi.smul_apply]
def cocycles : Submodule O (∀ n, G.A n ⊗[O] G.A n) where
  carrier := {c | ∀ n, c n ∈ symCocycles O (G.A n) ∧ pullbackTwo (G.res n) (c (n + 1)) = c n}
  zero_mem' _ := ⟨zero_mem _, map_zero _⟩
  add_mem' {v w} hv hw n := ⟨add_mem (hv n).1 (hw n).1, by
    rw [Pi.add_apply, map_add, (hv n).2, (hw n).2, Pi.add_apply]⟩
  smul_mem' c w hw n := ⟨Submodule.smul_mem _ c (hw n).1, by
    rw [Pi.smul_apply, map_smul, (hw n).2, Pi.smul_apply]⟩
def cob : G.funs →ₗ[O] G.cocycles where
  toFun b := ⟨fun n => cobOne O _ (b.1 n), fun n =>
    ⟨cobOne_mem _, (pullTwo_cobOne _ _).trans (congrArg _ (b.2 n))⟩⟩
  map_add' _ _ := Subtype.ext (funext fun _ => map_add (cobOne O _) _ _)
  map_smul' _ _ := Subtype.ext (funext fun _ => map_smul (cobOne O _) _ _)
def dFun : G.funs →ₗ[O] G.omega where
  toFun b := ⟨fun n => dUnit O (b.1 n), fun n => (cotMap_d _ _).trans (congrArg _ (b.2 n))⟩
  map_add' _ _ := Subtype.ext (funext fun _ => map_add (AugCot.d _) _ _)
  map_smul' _ _ := Subtype.ext (funext fun _ => map_smul (AugCot.d _) _ _)
abbrev VecExt : Type := G.cocycles ⧸ LinearMap.range G.cob
abbrev RigExt : Type := (G.cocycles × G.omega) ⧸ LinearMap.range (G.cob.prod G.dFun)
def rigMk : G.cocycles × G.omega →ₗ[O] G.RigExt := Submodule.mkQ _
def rigOfOmega : G.omega →ₗ[O] G.RigExt := G.rigMk ∘ₗ LinearMap.inr O _ _
def rigToExt : G.RigExt →ₗ[O] G.VecExt :=
  Submodule.mapQ _ _ (LinearMap.fst O _ _) (by rintro _ ⟨b, rfl⟩; exact ⟨b, rfl⟩)
variable {G H K}
def funsMap (f : G ⟶ H) : H.funs →ₗ[O] G.funs where
  toFun b := ⟨fun n => f.app n (b.1 n), fun n => (res_app f n _).trans (congrArg _ (b.2 n))⟩
  map_add' _ _ := Subtype.ext (funext fun n => map_add (f.app n) _ _)
  map_smul' _ _ := Subtype.ext (funext fun n => map_smul (f.app n) _ _)
def cocyclesMap (f : G ⟶ H) : H.cocycles →ₗ[O] G.cocycles where
  toFun c := ⟨fun n => pullbackTwo (f.app n) (c.1 n), fun n => ⟨pullTwo_mem _ (c.2 n).1, by
    rw [← pullTwo_comp, f.comm, pullTwo_comp, (c.2 n).2]⟩⟩
  map_add' _ _ := Subtype.ext (funext fun n => map_add (pullbackTwo (f.app n)) _ _)
  map_smul' _ _ := Subtype.ext (funext fun n => map_smul (pullbackTwo (f.app n)) _ _)
theorem cocyclesMap_cob (f : G ⟶ H) (b : H.funs) :
    cocyclesMap f (H.cob b) = G.cob (funsMap f b) :=
  Subtype.ext (funext fun _ => pullTwo_cobOne _ _)
def vecExtMap (f : G ⟶ H) : H.VecExt →ₗ[O] G.VecExt :=
  Submodule.mapQ _ _ (cocyclesMap f) (by
    rintro _ ⟨b, rfl⟩; exact ⟨funsMap f b, (cocyclesMap_cob f b).symm⟩)
variable [Fact p.Prime]
theorem omegaMap_dFun (f : G ⟶ H) (b : H.funs) :
    omegaMap G H f (H.dFun b) = G.dFun (funsMap f b) :=
  Subtype.ext (funext fun _ => cotMap_d _ _)
def rigExtMap (f : G ⟶ H) : H.RigExt →ₗ[O] G.RigExt :=
  Submodule.mapQ _ _ ((cocyclesMap f).prodMap (omegaMap G H f)) (by
    rintro _ ⟨b, rfl⟩
    exact ⟨funsMap f b, Prod.ext (cocyclesMap_cob f b).symm (omegaMap_dFun f b).symm⟩)
variable (G) in

abbrev LieUniv : Type := Module.Dual O G.RigExt
def lieUnivMap (f : G ⟶ H) : G.LieUniv →ₗ[O] H.LieUniv := (rigExtMap f).dualMap
variable (G) in

def lieUnivToLie : G.LieUniv →ₗ[O] G.Lie := G.rigOfOmega.dualMap
section Carry
variable (p O)
def digitFun (n : ℕ) : (const p O).A n := (constFun p O n).symm fun k => (k.val : O)
variable {p O}
end Carry
end PDivGroup
end GlobalTheory


