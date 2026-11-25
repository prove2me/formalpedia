-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RigOfOmegaInjectiveOfEqZero
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_RigOfOmegaInjectiveOfEqZero
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T01:30:02.342958+00:00
-- url     : https://prove2.me/theorems/0b460c12-97ed-4358-b9fd-ad38f2b67878
-- title:
--   Rig Of Omega Injective Of Eq Zero
-- statement:
--   Definitions and structural lemmas for Rig Of Omega Injective Of Eq Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RigOfOmegaInjectiveOfEqZero.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToBaseChangePtsBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DUnitMemRangeOfMemKerIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_PadicActionConstInjective
import Theorems.Thm_GlobalTheory_AugCot_baseChangeAug_tmul
import Theorems.Thm_GlobalTheory_AugCot_baseChangeEquiv_tmul_d
import Theorems.Thm_GlobalTheory_AugCot_mvPolynomialBasis_apply
import Theorems.Thm_GlobalTheory_CartierDual_isPrimitiveElem_iff_mul
import Theorems.Thm_GlobalTheory_IsBicharacter_map
import Theorems.Thm_GlobalTheory_PDivGroup_muLieGen_dlogT
import Theorems.Thm_GlobalTheory_PDivGroup_rigExtMap_id
import Theorems.Thm_GlobalTheory_PDivGroup_rigExtMap_mk
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
attribute [local simp] GlobalTheory.PDivGroup.rigExtMap_id
attribute [local simp] GlobalTheory.PDivGroup.rigExtMap_mk


set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra Bialgebra CategoryTheory
namespace GlobalTheory
namespace PDiv
section Lift
variable {R R' M N : Type} [CommRing R] [CommRing R'] [Algebra R R'] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R' N]
def liftSemi (f : M →ₛₗ[algebraMap R R'] N) : R' ⊗[R] M →ₗ[R'] N :=
  letI : Module R N := Module.compHom _ (algebraMap R R')
  haveI : IsScalarTower R R' N := ⟨fun a b w => by rw [Algebra.smul_def, mul_smul]; rfl⟩
  LinearMap.liftBaseChange R'
    { toFun := f, map_add' := map_add f, map_smul' := fun r m => map_smulₛₗ f r m }
@[simp] theorem liftSemi_tmul (f : M →ₛₗ[algebraMap R R'] N) (r : R') (m : M) :
    liftSemi f (r ⊗ₜ m) = r • f m := rfl
end Lift
section Level
variable {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {A A' : Type} [CommRing A]
  [Bialgebra R A] [CommRing A'] [Bialgebra R' A']
def SemiBialgHom.prim (f : SemiBialgHom σ A A') :
    LinearMap.ker (cobOne R A) →ₛₗ[σ] LinearMap.ker (cobOne R' A') where
  toFun b := ⟨f b.1, (f.two_cobOne b.1).symm.trans ((congrArg f.two b.2).trans (map_zero _))⟩
  map_add' _ _ := Subtype.ext (map_add f.lin _ _)
  map_smul' _ _ := Subtype.ext (f.smul_map _ _)
@[simp] theorem SemiBialgHom.prim_val (f : SemiBialgHom σ A A') (b : LinearMap.ker (cobOne R A)) :
    (f.prim b).1 = f b.1 := rfl
theorem isPrimitiveElem_of_mem_ker {b : A} (hb : b ∈ LinearMap.ker (cobOne R A)) :
    IsPrimitiveElem R b := by
  rw [LinearMap.mem_ker, cobOne_apply, sub_sub, sub_eq_zero] at hb
  exact hb
theorem evalAt_mul [Module.Finite R A] [Module.Projective R A] [IsCocomm R A]
    (b : LinearMap.ker (cobOne R A)) (φ ψ : CartierDual R A) :
    CartierDual.evalAt R A b.1 (φ * ψ) =
      counitAlgHom R (CartierDual R A) φ • CartierDual.evalAt R A b.1 ψ +
        counitAlgHom R (CartierDual R A) ψ • CartierDual.evalAt R A b.1 φ :=
  (CartierDual.isPrimitiveElem_iff_mul b.1).1 (isPrimitiveElem_of_mem_ker b.2) φ ψ
variable (R A) in

def primTangent [Module.Finite R A] [Module.Projective R A] [IsCocomm R A] :
    LinearMap.ker (cobOne R A) →ₗ[R] Module.Dual R (Cot R (CartierDual R A)) where
  toFun b := AugCot.lift _ (CartierDual.evalAt R A b.1) (evalAt_mul b)
  map_add' b b' := AugCot.hom_ext fun φ => by simp
  map_smul' r b := AugCot.hom_ext fun φ => by simp
@[simp] theorem primTangent_d [Module.Finite R A] [Module.Projective R A] [IsCocomm R A]
    (b : LinearMap.ker (cobOne R A)) (φ : CartierDual R A) :
    primTangent R A b (dUnit R φ) = φ b.1 := AugCot.lift_d _ _ (evalAt_mul b) φ
variable [IsCocomm R A] [IsCocomm R' A']
variable (R A) in

def levelRel : A →ₗ[R] symCocycles R A × Cot R A :=
  ((cobOne R A).codRestrict _ fun _ => cobOne_mem _).prod (AugCot.d (counitAlgHom R A))
variable (R A) in

abbrev LevelRig : Type := (symCocycles R A × Cot R A) ⧸ LinearMap.range (levelRel R A)
omit [IsCocomm R A] [IsCocomm R' A'] in

def SemiBialgHom.levelPair (f : SemiBialgHom σ A A') :
    symCocycles R A × Cot R A →ₛₗ[σ] symCocycles R' A' × Cot R' A' where
  toFun x := (⟨f.two x.1.1, f.two_mem x.1.2⟩, f.cot x.2)
  map_add' _ _ := Prod.ext (Subtype.ext (map_add f.two _ _)) (map_add f.cot _ _)
  map_smul' _ _ := Prod.ext (Subtype.ext (map_smulₛₗ f.two _ _)) (map_smulₛₗ f.cot _ _)
def SemiBialgHom.levelRig (f : SemiBialgHom σ A A') : LevelRig R A →ₛₗ[σ] LevelRig R' A' :=
  Submodule.mapQ _ _ f.levelPair (by
    rintro _ ⟨b, rfl⟩
    exact ⟨f b, Prod.ext (Subtype.ext (f.two_cobOne b).symm) (f.cot_d b).symm⟩)
end Level
end PDiv
namespace PDivGroup
open PDiv
variable {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R)
def resOne (n : ℕ) : G.A (n + 1) →ₐc[R] G.A 1 :=
  Nat.rec (motive := fun n => G.A (n + 1) →ₐc[R] G.A 1) (BialgHom.id R _)
    (fun n f => f.comp (G.res (n + 1))) n
def transl (n : ℕ) : G.A (n + 1) →ₐ[R] G.A (n + 1) ⊗[R] G.A 1 :=
  (Algebra.TensorProduct.map (AlgHom.id R _) (G.resOne n : G.A (n + 1) →ₐ[R] G.A 1)).comp
    (comulAlgHom R _)
def primLie : LinearMap.ker (cobOne R (G.A 1)) →ₗ[R] G.dual.Lie :=
  (G.dual.omegaLevel 1).dualMap ∘ₗ primTangent R (G.A 1)
def cocyclesLevel (n : ℕ) : G.cocycles →ₗ[R] symCocycles R (G.A n) :=
  (LinearMap.proj n ∘ₗ G.cocycles.subtype).codRestrict _ fun c => (c.2 n).1
def rigLevel (n : ℕ) : G.RigExt →ₗ[R] LevelRig R (G.A n) :=
  Submodule.mapQ _ _ ((G.cocyclesLevel n).prodMap (G.omegaLevel n)) (by
    rintro _ ⟨b, rfl⟩
    exact ⟨b.1 n, rfl⟩)
end PDivGroup
end GlobalTheory


