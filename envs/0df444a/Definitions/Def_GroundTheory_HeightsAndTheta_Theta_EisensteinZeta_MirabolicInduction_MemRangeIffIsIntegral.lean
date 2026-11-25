-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_MemRangeIffIsIntegral
-- name    : GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_MemRangeIffIsIntegral
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T09:39:08.576835+00:00
-- url     : https://prove2.me/theorems/bdd50d7b-60ce-5b65-89d7-7b6f8d650b7c
-- title:
--   Mem Range Iff Is Integral
-- statement:
--   Definitions and structural lemmas for Mem Range Iff Is Integral, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/MemRangeIffIsIntegral.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianSpaces
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HermitianLattice
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianDisc
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_CMDatum
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_DedekindZetaSeries_ChainWittIndexHypothesesMet
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_Isometric_refl
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_Isometric_trans
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_equivOfIsometry_apply
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_restrict_apply
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
import Theorems.Thm_GroundTheory_Automorphic_finiteAdeleUnitaryEquiv_apply
import Theorems.Thm_GroundTheory_Automorphic_matrixCoords_zero
import Theorems.Thm_GroundTheory_Automorphic_unitaryPiEquiv_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteAdeleSingle_apply_self
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteProj_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_infiniteProj_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_fst
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_snd
import Theorems.Thm_GroundTheory_Global_RestrictedProduct_continuousUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
import Theorems.Thm_GroundTheory_LocalField_coe_normUnits
import Theorems.Thm_GroundTheory_LocalField_ord_zero
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_embedding_conj_e96b6af5af35
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.HermitianForm.equivOfIsometry_apply
attribute [local simp] GroundTheory.Automorphic.HermitianForm.restrict_apply
attribute [local simp] GroundTheory.Automorphic.conj_conj
attribute [local simp] GroundTheory.Automorphic.finiteAdeleUnitaryEquiv_apply
attribute [local simp] GroundTheory.Automorphic.matrixCoords_zero
attribute [local simp] GroundTheory.Automorphic.unitaryPiEquiv_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteAdeleSingle_apply_self
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteProj_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.infiniteProj_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_fst
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_snd
attribute [local simp] GroundTheory.Global.RestrictedProduct.continuousUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk
attribute [local simp] GroundTheory.LocalField.coe_normUnits
attribute [local simp] GroundTheory.LocalField.ord_zero
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply


set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Theta
namespace FunctionalEquationAlt
open NumberField TensorProduct Module GroundTheory.Automorphic
open scoped nonZeroDivisors
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
def CAt {E : Type} [Field E] (_σ : E →+* ℂ) : Type := ℂ
namespace CAt
variable {E : Type} [Field E] (σ : E →+* ℂ)
instance : Field (CAt σ) := inferInstanceAs (Field ℂ)
instance : Algebra ℂ (CAt σ) := inferInstanceAs (Algebra ℂ ℂ)
def ofComplex : ℂ ≃ₐ[ℂ] CAt σ := AlgEquiv.refl
instance : Algebra E (CAt σ) := ((ofComplex σ).toRingHom.comp σ).toAlgebra
theorem smul_def (a : E) (z : CAt σ) : a • z = ofComplex σ (σ a) * z := rfl
theorem complex_smul_def (c : ℂ) (z : CAt σ) : c • z = ofComplex σ c * z := rfl
instance : SMulCommClass E ℂ (CAt σ) where
  smul_comm a c z := by
    rw [smul_def, complex_smul_def, complex_smul_def, smul_def, mul_left_comm]
instance : SMulCommClass ℂ E (CAt σ) := SMulCommClass.symm _ _ _
end CAt
open CAt
abbrev Fib {E : Type} [Field E] (σ : E →+* ℂ) (V : Type) [AddCommGroup V] [Module E V] : Type :=
  CAt σ ⊗[E] V
section FibSMul
variable {E : Type} [Field E] (σ : E →+* ℂ) (V : Type) [AddCommGroup V] [Module E V]
theorem fib_smul_eq (a : CAt σ) (x : Fib σ V) : a • x = (ofComplex σ).symm a • x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [smul_zero]
  | tmul z e => rw [smul_tmul', smul_tmul', complex_smul_def, smul_eq_mul]; rfl
  | add x y hx hy => rw [smul_add, smul_add, hx, hy]
instance (W : Type) [AddCommGroup W] [Module E W] :
    LinearMap.CompatibleSMul (Fib σ V) (Fib σ W) ℂ (CAt σ) where
  map_smul f c x := by
    rw [show c • x = (ofComplex σ c) • x from (fib_smul_eq σ V _ x).symm,
      show c • f x = (ofComplex σ c) • f x from (fib_smul_eq σ W _ (f x)).symm, map_smul]
instance [FiniteDimensional E V] : FiniteDimensional ℂ (Fib σ V) := by
  have : Module.Finite ℂ (CAt σ) := Module.Finite.equiv (ofComplex σ).toLinearEquiv
  exact Module.Finite.trans (CAt σ) (Fib σ V)
end FibSMul
structure MetSpace (E : Type) [Field E] [NumberField E] where

  V : Type
  [instAddCommGroup : AddCommGroup V]
  [instModule : Module E V]
  [instFD : FiniteDimensional E V]
  [instModuleO : Module (𝓞 E) V]
  [instTower : IsScalarTower (𝓞 E) E V]

  form : ∀ τ : InfinitePlace E, InnerProductSpace.Core ℂ (Fib τ.embedding V)
attribute [instance] MetSpace.instAddCommGroup MetSpace.instModule MetSpace.instFD
  MetSpace.instModuleO MetSpace.instTower
variable {E : Type} [Field E] [NumberField E]
namespace MetSpace
variable (S : MetSpace E)
def FibSp (τ : InfinitePlace E) : Type := Fib τ.embedding S.V
instance (τ : InfinitePlace E) : AddCommGroup (S.FibSp τ) :=
  inferInstanceAs (AddCommGroup (Fib τ.embedding S.V))
instance (τ : InfinitePlace E) : Module ℂ (S.FibSp τ) :=
  inferInstanceAs (Module ℂ (Fib τ.embedding S.V))
instance (τ : InfinitePlace E) : NormedAddCommGroup (S.FibSp τ) :=
  letI : InnerProductSpace.Core ℂ (S.FibSp τ) := S.form τ
  this.toNormedAddCommGroup
instance (τ : InfinitePlace E) : InnerProductSpace ℂ (S.FibSp τ) := InnerProductSpace.ofCore _
instance (τ : InfinitePlace E) : FiniteDimensional ℂ (S.FibSp τ) :=
  inferInstanceAs (FiniteDimensional ℂ (Fib τ.embedding S.V))
def pt (τ : InfinitePlace E) (v : S.V) : S.FibSp τ := (1 : CAt τ.embedding) ⊗ₜ[E] v
def pair (y y' : S.V) : ℝ := ∑ τ : InfinitePlace E, (inner ℂ (S.pt τ y) (S.pt τ y')).re
def gram {ι : Type} (b : ι → S.V) : Matrix ι ι ℝ := Matrix.of fun i j => S.pair (b i) (b j)
open Classical in

def covol (A : Submodule (𝓞 E) S.V) : ℝ :=
  if h : ∃ n : ℕ, Nonempty (Basis (Fin n) ℤ A) then
    Real.sqrt (S.gram fun i => ((h.choose_spec.some i : A) : S.V)).det
  else 0
def rk (A : Submodule (𝓞 E) S.V) : ℕ := finrank E (Submodule.span E (A : Set S.V))
end MetSpace
variable (E) in

def fPl : ℕ := Fintype.card (InfinitePlace E)
variable (E) in

def rd : ℝ := |(discr E : ℝ)| ^ ((1 : ℝ) / (2 * fPl E))
namespace MetSpace
variable (S : MetSpace E)
def ht (A : Submodule (𝓞 E) S.V) : ℝ := S.covol A * (2 / rd E) ^ (fPl E * S.rk A)
def ta (A : Submodule (𝓞 E) S.V) : ℝ := S.ht A ^ ((1 : ℝ) / (2 * fPl E * S.rk A))
end MetSpace
namespace MetSpace
variable (S : MetSpace E)
def toSp (τ : InfinitePlace E) : Fib τ.embedding S.V ≃ₗ[ℂ] S.FibSp τ := LinearEquiv.refl ℂ _
def fibSub (W : Submodule E S.V) (τ : InfinitePlace E) : Submodule ℂ (S.FibSp τ) :=
  (LinearMap.range (TensorProduct.AlgebraTensorModule.lTensor (CAt τ.embedding) (CAt τ.embedding)
    (W.subtype.restrictScalars E))).restrictScalars ℂ
def quotEquiv (W : Submodule E S.V) (τ : InfinitePlace E) :
    Fib τ.embedding (S.V ⧸ W) ≃ₗ[ℂ] S.FibSp τ ⧸ S.fibSub W τ :=
  ((TensorProduct.AlgebraTensorModule.tensorQuotientEquiv (CAt τ.embedding) E (CAt τ.embedding)
    W).restrictScalars ℂ).trans (Submodule.Quotient.restrictScalarsEquiv ℂ _).symm
def quotMap (W : Submodule E S.V) (τ : InfinitePlace E) :
    Fib τ.embedding (S.V ⧸ W) →ₗ[ℂ] S.FibSp τ :=
  (S.fibSub W τ)ᗮ.subtype ∘ₗ
    ((Submodule.quotientEquivOfIsCompl (S.fibSub W τ) (S.fibSub W τ)ᗮ
      (Submodule.isCompl_orthogonal _)).toLinearMap ∘ₗ (S.quotEquiv W τ).toLinearMap)
theorem quotMap_injective (W : Submodule E S.V) (τ : InfinitePlace E) :
    Function.Injective (S.quotMap W τ) := by
  intro a b h
  exact (S.quotEquiv W τ).injective ((Submodule.quotientEquivOfIsCompl (S.fibSub W τ) (S.fibSub W τ)ᗮ
    (Submodule.isCompl_orthogonal _)).injective ((S.fibSub W τ)ᗮ.injective_subtype h))
def quot (W : Submodule E S.V) : MetSpace E where
  V := S.V ⧸ W
  form τ := Heights.coreOfInjective (S.quotMap W τ) (S.quotMap_injective W τ)
def restrictMap (W : Submodule E S.V) (τ : InfinitePlace E) :
    Fib τ.embedding W →ₗ[ℂ] S.FibSp τ :=
  (W.subtype.baseChange (CAt τ.embedding)).restrictScalars ℂ
theorem restrictMap_injective (W : Submodule E S.V) (τ : InfinitePlace E) :
    Function.Injective (S.restrictMap W τ) := by
  change Function.Injective (W.subtype.baseChange (CAt τ.embedding))
  rw [LinearMap.baseChange_eq_ltensor]
  exact Module.Flat.lTensor_preserves_injective_linearMap _ W.injective_subtype
def restrict (W : Submodule E S.V) : MetSpace E where
  V := W
  form τ := Heights.coreOfInjective (S.restrictMap W τ) (S.restrictMap_injective W τ)
def dualCoord (τ : InfinitePlace E) :
    Fib τ.embedding (Module.Dual E S.V) →ₗ[CAt τ.embedding]
      Module.Dual (CAt τ.embedding) (Fib τ.embedding S.V) :=
  LinearMap.liftBaseChange (CAt τ.embedding) (Module.Dual.baseChange (CAt τ.embedding))
theorem dualCoord_tmul_tmul (τ : InfinitePlace E) (z w : CAt τ.embedding) (φ : Module.Dual E S.V)
    (v : S.V) : S.dualCoord τ (z ⊗ₜ φ) (w ⊗ₜ v) = z * (algebraMap E (CAt τ.embedding) (φ v) * w) := by
  rw [dualCoord, LinearMap.liftBaseChange_tmul, LinearMap.smul_apply,
    Module.Dual.baseChange_apply_tmul, smul_eq_mul, Algebra.smul_def]
theorem dualCoord_injective (τ : InfinitePlace E) : Function.Injective (S.dualCoord τ) := by
  classical
  let b := Module.finBasis E S.V
  have hψ : ∀ ψ : Module.Dual E S.V, ∑ i, ψ (b i) • b.coord i = ψ := by
    intro ψ
    refine b.ext fun j ↦ ?_
    rw [LinearMap.sum_apply]
    simp only [LinearMap.smul_apply, Basis.coord_apply, Basis.repr_self, smul_eq_mul]
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij; simp [hij]
    · simp
  have hrec : ∀ x, ∑ i, S.dualCoord τ x (1 ⊗ₜ b i) ⊗ₜ b.coord i = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero, LinearMap.zero_apply, zero_tmul, Finset.sum_const_zero]
    | add x y hx hy =>
      simp only [map_add, LinearMap.add_apply, add_tmul, Finset.sum_add_distrib, hx, hy]
    | tmul z ψ =>
      conv_rhs => rw [← hψ ψ]
      rw [tmul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [dualCoord_tmul_tmul, mul_one, ← smul_tmul, Algebra.smul_def, mul_comm]
  intro x y hxy
  rw [← hrec x, ← hrec y, hxy]
def dualFunctional (τ : InfinitePlace E) (x : Fib τ.embedding (Module.Dual E S.V)) :
    StrongDual ℂ (S.FibSp τ) :=
  LinearMap.toContinuousLinearMap ((ofComplex τ.embedding).symm.toLinearMap ∘ₗ
    ((S.dualCoord τ x).restrictScalars ℂ : S.FibSp τ →ₗ[ℂ] CAt τ.embedding))
def riesz (τ : InfinitePlace E) (x : Fib τ.embedding (Module.Dual E S.V)) : S.FibSp τ :=
  (InnerProductSpace.toDual ℂ (S.FibSp τ)).symm (S.dualFunctional τ x)
theorem inner_riesz (τ : InfinitePlace E) (x : Fib τ.embedding (Module.Dual E S.V))
    (v : S.FibSp τ) :
    inner ℂ (S.riesz τ x) v = (ofComplex τ.embedding).symm (S.dualCoord τ x ((S.toSp τ).symm v)) := by
  rw [riesz, InnerProductSpace.toDual_symm_apply]
  rfl
theorem riesz_add (τ : InfinitePlace E) (x y : Fib τ.embedding (Module.Dual E S.V)) :
    S.riesz τ (x + y) = S.riesz τ x + S.riesz τ y := by
  refine ext_inner_right ℂ fun v ↦ ?_
  rw [inner_add_left, inner_riesz, inner_riesz, inner_riesz, map_add, LinearMap.add_apply, map_add]
theorem riesz_smul (τ : InfinitePlace E) (c : ℂ) (x : Fib τ.embedding (Module.Dual E S.V)) :
    S.riesz τ (c • x) = starRingEnd ℂ c • S.riesz τ x := by
  refine ext_inner_right ℂ fun v ↦ ?_
  have hc : c • x = ofComplex τ.embedding c • x := by
    rw [fib_smul_eq τ.embedding _ (ofComplex τ.embedding c) x, AlgEquiv.symm_apply_apply]
  rw [inner_smul_left, Complex.conj_conj, inner_riesz, inner_riesz, hc, map_smul,
    LinearMap.smul_apply, smul_eq_mul, map_mul, AlgEquiv.symm_apply_apply]
theorem riesz_eq_zero (τ : InfinitePlace E) (x : Fib τ.embedding (Module.Dual E S.V))
    (hx : S.riesz τ x = 0) : x = 0 := by
  refine S.dualCoord_injective τ ?_
  rw [map_zero]
  refine LinearMap.ext fun u ↦ ?_
  have := S.inner_riesz τ x (S.toSp τ u)
  rw [hx, inner_zero_left, LinearEquiv.symm_apply_apply] at this
  rw [LinearMap.zero_apply]
  exact (ofComplex τ.embedding).symm.injective (by rw [← this, map_zero])
@[instance_reducible]
def dualCore (τ : InfinitePlace E) : InnerProductSpace.Core ℂ (Fib τ.embedding (Module.Dual E S.V)) where
  inner x y := inner ℂ (S.riesz τ y) (S.riesz τ x)
  conj_inner_symm x y := inner_conj_symm _ _
  re_inner_nonneg x := inner_self_nonneg
  add_left x y z := by rw [riesz_add, inner_add_right]
  smul_left x y r := by rw [riesz_smul, inner_smul_right]
  definite x hx := S.riesz_eq_zero τ x (inner_self_eq_zero.mp hx)
def dual : MetSpace E where
  V := Module.Dual E S.V
  form τ := S.dualCore τ
end MetSpace
section Lattices
variable {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
abbrev espan (A : Submodule (𝓞 E) V) : Submodule E V := Submodule.span E (A : Set V)
def SatIn (A' A : Submodule (𝓞 E) V) : Prop :=
  A' ≤ A ∧ ∀ (c : 𝓞 E) (x : V), c ≠ 0 → x ∈ A → c • x ∈ A' → x ∈ A'
def smulIdeal (aa : FractionalIdeal (𝓞 E)⁰ E) (A : Submodule (𝓞 E) V) : Submodule (𝓞 E) V :=
  Submodule.span (𝓞 E) {v | ∃ a ∈ aa, ∃ x ∈ A, v = a • x}
section Herm
variable {F : Type} [Field F] [Algebra F E] [Algebra.IsQuadraticExtension F E]
def IsSelfDual (h : HermitianForm F E V) (L : Submodule (𝓞 E) V) : Prop :=
  ∀ y : V, y ∈ L ↔ ∀ l ∈ L, h.toSesq y l ∈ Set.range (algebraMap (𝓞 E) E)
def IsIsotropic (h : HermitianForm F E V) (I : Submodule (𝓞 E) V) : Prop :=
  ∀ x ∈ I, ∀ y ∈ I, h.toSesq x y = 0
def perpIn (h : HermitianForm F E V) (L R : Submodule (𝓞 E) V) : Submodule (𝓞 E) V :=
  L ⊓ ⨅ r : R, LinearMap.ker ((h.toSesq (r : V)).restrictScalars (𝓞 E))
end Herm
end Lattices
namespace MetSpace
variable (S : MetSpace E)
def quotBy (N : Submodule (𝓞 E) S.V) : MetSpace E := S.quot (espan N)
def quotLat (N M : Submodule (𝓞 E) S.V) : Submodule (𝓞 E) (S.quotBy N).V :=
  M.map (((espan N).mkQ.restrictScalars (𝓞 E)) : S.V →ₗ[𝓞 E] (S.quotBy N).V)
def least (A : Submodule (𝓞 E) S.V) : ℝ :=
  sInf {t | ∃ M : Submodule (𝓞 E) S.V, M ≤ A ∧ M ≠ ⊥ ∧ S.ta M = t}
def largest (A : Submodule (𝓞 E) S.V) : ℝ :=
  sSup {t | ∃ A' : Submodule (𝓞 E) S.V, SatIn A' A ∧ A' ≠ A ∧ (S.quotBy A').ta (S.quotLat A' A) = t}
def tOne (A : Submodule (𝓞 E) S.V) : ℝ :=
  sInf {t | ∃ M : Submodule (𝓞 E) S.V, M ≤ A ∧ S.rk M = 1 ∧ S.ta M = t}
def Semistable (A : Submodule (𝓞 E) S.V) : Prop := S.least A = S.ta A
def pieceSize {l : ℕ} (L : Fin (l + 1) → Submodule (𝓞 E) S.V) (i : Fin l) : ℝ :=
  (S.quotBy (L i.castSucc)).ta (S.quotLat (L i.castSucc) (L i.succ))
def IsSizeFlag (A : Submodule (𝓞 E) S.V) {l : ℕ} (L : Fin (l + 1) → Submodule (𝓞 E) S.V) : Prop :=
  L 0 = ⊥ ∧ L (Fin.last l) = A ∧ StrictMono L ∧ (∀ i, SatIn (L i) A) ∧
    (∀ i : Fin l, (S.quotBy (L i.castSucc)).Semistable (S.quotLat (L i.castSucc) (L i.succ))) ∧
    StrictMono (S.pieceSize L)
def spanAt (A : Submodule (𝓞 E) S.V) (τ : InfinitePlace E) : Submodule ℂ (S.FibSp τ) :=
  Submodule.span ℂ (S.pt τ '' (A : Set S.V))
def fibMap (T : MetSpace E) (φ : S.V →ₗ[E] T.V) (τ : InfinitePlace E) :
    S.FibSp τ →ₗ[ℂ] T.FibSp τ :=
  ((φ.baseChange (CAt τ.embedding)).restrictScalars ℂ : Fib τ.embedding S.V →ₗ[ℂ] Fib τ.embedding T.V)
def opNormOn (T : MetSpace E) (φ : S.V →ₗ[E] T.V) (A : Submodule (𝓞 E) S.V) (τ : InfinitePlace E) :
    ℝ :=
  sInf {C : ℝ | 0 ≤ C ∧ ∀ u ∈ S.spanAt A τ, ‖S.fibMap T φ τ u‖ ≤ C * ‖u‖}
def spanSp (A : Submodule (𝓞 E) S.V) : MetSpace E := S.restrict (espan A)
def inSpan (A A' : Submodule (𝓞 E) S.V) : Submodule (𝓞 E) (S.spanSp A).V :=
  A'.comap (((espan A).subtype.restrictScalars (𝓞 E)) : (S.spanSp A).V →ₗ[𝓞 E] S.V)
def dualSp (A : Submodule (𝓞 E) S.V) : MetSpace E := (S.spanSp A).dual
def dualLatIn (W : Submodule E S.V) (A : Submodule (𝓞 E) S.V) :
    Submodule (𝓞 E) (Module.Dual E W) where
  carrier := {φ | ∀ a : W, (a : S.V) ∈ A → φ a ∈ Set.range (algebraMap (𝓞 E) E)}
  add_mem' {φ ψ} hφ hψ a ha := by
    obtain ⟨x, hx⟩ := hφ a ha
    obtain ⟨y, hy⟩ := hψ a ha
    exact ⟨x + y, by rw [LinearMap.add_apply, map_add, hx, hy]⟩
  zero_mem' a _ := ⟨0, by rw [map_zero, LinearMap.zero_apply]⟩
  smul_mem' c φ hφ a ha := by
    obtain ⟨x, hx⟩ := hφ a ha
    exact ⟨c * x, by rw [LinearMap.smul_apply, map_mul, hx, Algebra.smul_def]⟩
def dualLat (A : Submodule (𝓞 E) S.V) : Submodule (𝓞 E) (S.dualSp A).V := S.dualLatIn (espan A) A
def annLat (A A' : Submodule (𝓞 E) S.V) : Submodule (𝓞 E) (S.dualSp A).V :=
  S.dualLat A ⊓ (((espan A').comap (espan A).subtype).dualAnnihilator.restrictScalars (𝓞 E) :
    Submodule (𝓞 E) (Module.Dual E (espan A)))
end MetSpace
namespace MetSpace
variable (S : MetSpace E)
def gapCount {l : ℕ} (L : Fin (l + 1) → Submodule (𝓞 E) S.V) : ℕ :=
  (Finset.univ.filter fun i : Fin l => S.pieceSize L i < 1 / 2).card
def taHat {l : ℕ} (L : Fin (l + 1) → Submodule (𝓞 E) S.V) (j : ℕ) : ℝ :=
  if h : j < l then (if j < S.gapCount L then S.pieceSize L ⟨j, h⟩ else 1 / 2) else 1 / 2
end MetSpace
def rhoZero (t : ℝ) (r' : ℕ) : ℝ := (2 * t) ^ ((1 : ℝ) / r')
def MetSpace.IsGapIndex (S : MetSpace E) {l : ℕ} (L : Fin (l + 1) → Submodule (𝓞 E) S.V)
    (t : ℝ) (r' b : ℕ) : Prop :=
  1 ≤ b ∧ b ≤ S.gapCount L ∧ S.taHat L (b - 1) / S.taHat L b ≤ rhoZero t r'
structure SelfDualFrame (F E : Type) [Field F] [Field E] [NumberField E] [Algebra F E]
    [Algebra.IsQuadraticExtension F E] where

  S : MetSpace E

  B : HermitianForm F E S.V

  L : Submodule (𝓞 E) S.V
  fg : L.FG
  selfDual : IsSelfDual B L

  θ : ∀ τ : InfinitePlace E, S.FibSp τ →ₗ[ℂ] S.FibSp τ
  θ_θ : ∀ τ u, θ τ (θ τ u) = u
  θ_isometry : ∀ τ u v, inner ℂ (θ τ u) (θ τ v) = inner ℂ u v
  majorant : ∀ τ (y y' : S.V), inner ℂ (θ τ (S.pt τ y)) (S.pt τ y') = τ.embedding (B.toSesq y y')
namespace SelfDualFrame
variable {F : Type} [Field F] [Algebra F E] [Algebra.IsQuadraticExtension F E]
def lineForm (X : SelfDualFrame F E) (R : Submodule (𝓞 E) X.S.V) (y : X.S.V) :
    (X.S.dualSp R).V :=
  ((X.B.toSesq y).comp (espan R).subtype : Module.Dual E (espan R))
end SelfDualFrame
section Standard
variable (E) (n : ℕ)
def stdCoord (σ : E →+* ℂ) : Fib σ (Fin n → E) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin n) :=
  ((piScalarRight E (CAt σ) (CAt σ) (Fin n)).restrictScalars ℂ).trans
    ((LinearEquiv.piCongrRight fun _ ↦ (ofComplex σ).symm.toLinearEquiv).trans
      (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).symm)
variable {E n}
theorem stdCoord_tmul (σ : E →+* ℂ) (z : CAt σ) (v : Fin n → E) (i : Fin n) :
    stdCoord E n σ (z ⊗ₜ v) i = σ (v i) * (ofComplex σ).symm z := rfl
variable (E n)
def MetSpace.standard : MetSpace E where
  V := Fin n → E
  form τ := Heights.coreOfInjective (stdCoord E n τ.embedding).toLinearMap
    (stdCoord E n τ.embedding).injective
def stdLat : Submodule (𝓞 E) (Fin n → E) :=
  Submodule.span (𝓞 E) (Set.range fun i : Fin n => (Pi.single i 1 : Fin n → E))
variable {E n}
theorem stdLat_fg : (stdLat E n).FG := Submodule.fg_span (Set.finite_range _)
theorem mem_range_iff_isIntegral (x : E) :
    x ∈ Set.range (algebraMap (𝓞 E) E) ↔ IsIntegral ℤ x :=
  ⟨fun ⟨c, hc⟩ => hc ▸ RingOfIntegers.isIntegral_coe c, fun h => ⟨⟨x, h⟩, rfl⟩⟩
theorem mem_stdLat_iff (y : Fin n → E) :
    y ∈ stdLat E n ↔ ∀ i, y i ∈ Set.range (algebraMap (𝓞 E) E) := by
  rw [stdLat, Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, rfl⟩ i
    refine ⟨c i, ?_⟩
    simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def]
  · intro h
    refine ⟨fun i => (h i).choose, funext fun j => ?_⟩
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, Algebra.smul_def, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    exact (h j).choose_spec
end Standard
section Frame
variable (F : Type) [Field F] [NumberField F] [IsTotallyReal F] [IsTotallyComplex E]
  [Algebra F E] [Algebra.IsQuadraticExtension F E]
def signs : Fin 2 → Fˣ := ![1, -1]
def flipMap : (Fin 2 → E) →ₗ[E] (Fin 2 → E) :=
  LinearMap.pi fun i => (algebraMap F E (signs F i) : E) • LinearMap.proj i
variable {F}
theorem signs_sq (i : Fin 2) : algebraMap F E (signs F i) * algebraMap F E (signs F i) = 1 := by
  fin_cases i <;> simp [signs]
theorem flipMap_flipMap (y : Fin 2 → E) : flipMap F (flipMap F y) = y := by
  funext i
  simp only [flipMap, LinearMap.pi_apply, LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul]
  rw [← mul_assoc, signs_sq, one_mul]
end Frame
section Frame
variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] [IsTotallyComplex E]
  [Algebra F E] [Algebra.IsQuadraticExtension F E]
theorem isIntegral_conj {x : E} (hx : IsIntegral ℤ x) : IsIntegral ℤ (conj F E x) :=
  hx.map (conjHom F E).toIntAlgHom
def hypForm : HermitianForm F E (Fin 2 → E) := diagForm (signs F)
theorem hypForm_apply (y y' : Fin 2 → E) :
    (hypForm (F := F) (E := E)).toSesq y y' =
      ∑ i, conj F E (y i) * algebraMap F E (signs F i) * y' i := rfl
theorem stdLat_isSelfDual : IsSelfDual (hypForm (F := F) (E := E)) (stdLat E 2) := by
  intro y
  simp only [mem_range_iff_isIntegral, mem_stdLat_iff, hypForm_apply]
  constructor
  · intro hy l hl
    refine IsIntegral.sum _ fun i _ => ?_
    refine ((isIntegral_conj (hy i)).mul ?_).mul (hl i)
    fin_cases i <;> simp [signs, isIntegral_one, IsIntegral.neg]
  · intro h i
    have key := h (Pi.single i 1) (by
      intro j
      by_cases hij : j = i
      · subst hij; simp [isIntegral_one]
      · simp [Pi.single_apply, hij, isIntegral_zero])
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_apply, hj]) (by simp)] at key
    simp only [Pi.single_eq_same, mul_one] at key
    have hc : IsIntegral ℤ (conj F E (y i)) := by
      fin_cases i
      · simpa [signs] using key
      · simpa [signs] using key.neg
    simpa [conj_conj] using isIntegral_conj (F := F) hc
end Frame
section Frame2
variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] [IsTotallyComplex E]
  [Algebra F E] [Algebra.IsQuadraticExtension F E]
theorem stdCoord_flip (τ : InfinitePlace E) (u : Fib τ.embedding (Fin 2 → E)) (i : Fin 2) :
    stdCoord E 2 τ.embedding ((flipMap F).baseChange (CAt τ.embedding) u) i =
      τ.embedding (algebraMap F E (signs F i)) * stdCoord E 2 τ.embedding u i := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul z v =>
    rw [LinearMap.baseChange_tmul, stdCoord_tmul, stdCoord_tmul]
    simp only [flipMap, LinearMap.pi_apply, LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul,
      map_mul]
    ring
  | add u v hu hv => rw [map_add, map_add, PiLp.add_apply, hu, hv, map_add, PiLp.add_apply, mul_add]
theorem signs_conj_mul (τ : InfinitePlace E) (i : Fin 2) :
    starRingEnd ℂ (τ.embedding (algebraMap F E (signs F i))) *
      τ.embedding (algebraMap F E (signs F i)) = 1 := by
  fin_cases i <;> simp [signs]
theorem flip_flip_fib (τ : InfinitePlace E) (u : Fib τ.embedding (Fin 2 → E)) :
    (flipMap F).baseChange (CAt τ.embedding) ((flipMap F).baseChange (CAt τ.embedding) u) = u := by
  rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp]
  have h : flipMap F ∘ₗ flipMap F = (LinearMap.id : (Fin 2 → E) →ₗ[E] (Fin 2 → E)) :=
    LinearMap.ext flipMap_flipMap
  rw [h, LinearMap.baseChange_id, LinearMap.id_apply]
theorem flip_isometry (τ : InfinitePlace E) (u v : Fib τ.embedding (Fin 2 → E)) :
    inner ℂ (stdCoord E 2 τ.embedding ((flipMap F).baseChange (CAt τ.embedding) u))
        (stdCoord E 2 τ.embedding ((flipMap F).baseChange (CAt τ.embedding) v)) =
      inner ℂ (stdCoord E 2 τ.embedding u) (stdCoord E 2 τ.embedding v) := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, stdCoord_flip]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul]
  linear_combination (stdCoord E 2 τ.embedding v i *
    starRingEnd ℂ (stdCoord E 2 τ.embedding u i)) * signs_conj_mul (F := F) τ i
theorem flip_majorant (τ : InfinitePlace E) (y y' : Fin 2 → E) :
    inner ℂ (stdCoord E 2 τ.embedding
        ((flipMap F).baseChange (CAt τ.embedding) ((1 : CAt τ.embedding) ⊗ₜ y)))
        (stdCoord E 2 τ.embedding ((1 : CAt τ.embedding) ⊗ₜ y')) =
      τ.embedding ((hypForm (F := F) (E := E)).toSesq y y') := by
  rw [LinearMap.baseChange_tmul, hypForm_apply, map_sum]
  simp only [PiLp.inner_apply, RCLike.inner_apply, stdCoord_tmul]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : (ofComplex τ.embedding).symm 1 = 1 := rfl
  simp only [h1, mul_one, map_one, map_mul, embedding_conj]
  fin_cases i <;> simp [flipMap, signs, embedding_conj] <;> ring
def hypFrame : SelfDualFrame F E where
  S := MetSpace.standard E 2
  B := hypForm
  L := stdLat E 2
  fg := stdLat_fg
  selfDual := stdLat_isSelfDual
  θ τ := (MetSpace.standard E 2).fibMap (MetSpace.standard E 2) (flipMap F) τ
  θ_θ τ u := flip_flip_fib τ u
  θ_isometry τ u v := flip_isometry τ u v
  majorant τ y y' := flip_majorant τ y y'
end Frame2
example : SelfDualFrame ℚ GaussQ := hypFrame
example : MetSpace GaussQ :=
  (MetSpace.standard GaussQ 2).quot (Submodule.span GaussQ {(Pi.single 0 1 : Fin 2 → GaussQ)})
example : MetSpace GaussQ :=
  (MetSpace.standard GaussQ 2).restrict (Submodule.span GaussQ {(Pi.single 0 1 : Fin 2 → GaussQ)})
example : MetSpace GaussQ := (MetSpace.standard GaussQ 2).dual
end
end FunctionalEquationAlt
end GroundTheory.Heights₂.Theta


