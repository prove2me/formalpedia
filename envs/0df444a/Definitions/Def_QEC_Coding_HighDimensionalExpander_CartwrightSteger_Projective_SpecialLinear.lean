-- Prove2me | Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Projective_SpecialLinear
-- name    : QEC_Coding_HighDimensionalExpander_CartwrightSteger_Projective_SpecialLinear
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T12:42:30.219574+00:00
-- url     : https://prove2.me/theorems/74550da5-e8dc-400d-a1f7-c873978adf24
-- title:
--   Special Linear
-- statement:
--   Definitions and structural lemmas for Special Linear, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Projective/SpecialLinear.lean

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_Congruence
import Mathlib.GroupTheory.GroupAction.Iwasawa
import Mathlib.GroupTheory.IsPerfect
import Mathlib.LinearAlgebra.Center
import Mathlib.LinearAlgebra.Projectivization.Action
import Mathlib.LinearAlgebra.Projectivization.Independence
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CongruenceLifting_residueTransvectionSpecial_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueXAdjoinRootEquiv_root
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueYAdjoinRootEquiv_root
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.CongruenceLifting.residueTransvectionSpecial_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueXAdjoinRootEquiv_root
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueYAdjoinRootEquiv_root


set_option autoImplicit false
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
open Matrix
open scoped commutatorElement
open scoped Pointwise
noncomputable def specialTransvection
    {K : Type*} [Field K] {n : Type*} [Fintype n] [DecidableEq n]
    (i j : n) (hij : i ≠ j) (c : K) :
    Matrix.SpecialLinearGroup n K :=
  ⟨Matrix.transvection i j c, Matrix.det_transvection_of_ne i j hij c⟩
@[simp] theorem specialTransvection_coe
    {K : Type*} [Field K] {n : Type*} [Fintype n] [DecidableEq n]
    (i j : n) (hij : i ≠ j) (c : K) :
    (specialTransvection i j hij c : Matrix n n K) =
      Matrix.transvection i j c := rfl
noncomputable def specialLinearToPSL
    (P : BasePrime) (r : Rank) (level : Nat) :
    Matrix.SpecialLinearGroup (Fin r.matrixRank)
        (ResidueField P r level) →*
      PSL P r level where
  toFun s := ⟨specialToProjective P r level s, ⟨s, rfl⟩⟩
  map_one' := Subtype.ext (map_one (specialToProjective P r level))
  map_mul' s t :=
    Subtype.ext (map_mul (specialToProjective P r level) s t)
section ProjectiveRoots
open scoped LinearAlgebra.Projectivization
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
noncomputable def linearSpecialTransvection
    (f : Module.Dual K V) (v : V) (hfv : f v = 0) :
    SpecialLinearGroup K V :=
  ⟨LinearEquiv.transvection hfv, LinearEquiv.transvection.det_eq_one hfv⟩
@[simp] theorem linearSpecialTransvection_apply
    (f : Module.Dual K V) (v : V) (hfv : f v = 0) (w : V) :
    linearSpecialTransvection f v hfv w = w + f w • v :=
  rfl
def projectiveRootGenerators (x : ℙ K V) : Set (SpecialLinearGroup K V) :=
  {g | ∃ (f : Module.Dual K V) (v : V) (hv : v ≠ 0) (hfv : f v = 0),
    Projectivization.mk K v hv = x ∧ g = linearSpecialTransvection f v hfv}
def projectiveRootSubgroup (x : ℙ K V) : Subgroup (SpecialLinearGroup K V) :=
  Subgroup.closure (projectiveRootGenerators x)
theorem projectiveRootGenerators_commute (x : ℙ K V)
    (a : SpecialLinearGroup K V) (ha : a ∈ projectiveRootGenerators x)
    (b : SpecialLinearGroup K V) (hb : b ∈ projectiveRootGenerators x) :
    a * b = b * a := by
  obtain ⟨f, v, hv, hfv, hxv, rfl⟩ := ha
  obtain ⟨g, w, hw, hgw, hxw, rfl⟩ := hb
  obtain ⟨u, hu⟩ :=
    (Projectivization.mk_eq_mk_iff K v w hv hw).mp (hxv.trans hxw.symm)
  have hu' : (u : K) • w = v := by
    simpa [Units.smul_def] using hu
  apply SpecialLinearGroup.ext
  intro z
  have hfw : f w = 0 := by
    have hzero : (u : K) * f w = 0 := by
      have := congrArg f hu'
      simpa [map_smul, hfv, smul_eq_mul] using this
    exact (mul_eq_zero.mp hzero).resolve_left (Units.ne_zero u)
  have hgv : g v = 0 := by
    rw [← hu', map_smul, hgw, smul_zero]
  simp only [SpecialLinearGroup.coe_mul, LinearEquiv.mul_apply,
    linearSpecialTransvection_apply, map_add, map_smul]
  simp [hfv, hgw, hfw, hgv, add_assoc, add_left_comm, add_comm]
theorem projectiveRootSubgroup_isMulCommutative (x : ℙ K V) :
    IsMulCommutative (projectiveRootSubgroup x) :=
  Subgroup.isMulCommutative_closure
    (projectiveRootGenerators_commute x)
theorem linearSpecialTransvection_conj
    (a : SpecialLinearGroup K V)
    (f : Module.Dual K V) (v : V) (hfv : f v = 0) :
    a * linearSpecialTransvection f v hfv * a⁻¹ =
      linearSpecialTransvection
        (f.comp (a⁻¹ : V ≃ₗ[K] V).toLinearMap) (a v) (by simp [hfv]) := by
  apply SpecialLinearGroup.ext
  intro z
  simp [linearSpecialTransvection_apply, map_add, map_smul]
theorem projectiveRootGenerators_conj
    (a : SpecialLinearGroup K V) (x : ℙ K V) :
    MulAut.conj a '' projectiveRootGenerators x =
      projectiveRootGenerators (a • x) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨g, hg, rfl⟩
    obtain ⟨f, v, hv, hfv, hx, rfl⟩ := hg
    let f' : Module.Dual K V :=
      f.comp (a⁻¹ : V ≃ₗ[K] V).toLinearMap
    have hf' : f' (a v) = 0 := by simp [f', hfv]
    refine ⟨f', a v, ?_, hf', ?_, ?_⟩
    · exact (a : V ≃ₗ[K] V).map_ne_zero_iff.mpr hv
    · calc
        Projectivization.mk K (a v) _ =
            a • Projectivization.mk K v hv := by
              rw [Projectivization.smul_mk]
              rfl
        _ = a • x := congrArg (a • ·) hx
    · exact linearSpecialTransvection_conj a f v hfv
  · rintro g ⟨f, v, hv, hfv, hx, rfl⟩
    let w : V := a⁻¹ v
    let f' : Module.Dual K V := f.comp (a : V ≃ₗ[K] V).toLinearMap
    have hw : w ≠ 0 := by
      exact (a⁻¹ : V ≃ₗ[K] V).map_ne_zero_iff.mpr hv
    have hf' : f' w = 0 := by simp [f', w, hfv]
    let t := linearSpecialTransvection f' w hf'
    refine ⟨t, ?_, ?_⟩
    · refine ⟨f', w, hw, hf', ?_, rfl⟩
      calc
        Projectivization.mk K w hw =
            a⁻¹ • Projectivization.mk K v hv := by
              rw [Projectivization.smul_mk]
              rfl
        _ = a⁻¹ • (a • x) := congrArg (a⁻¹ • ·) hx
        _ = x := inv_smul_smul a x
    · rw [MulAut.conj_apply, linearSpecialTransvection_conj]
      apply SpecialLinearGroup.ext
      intro z
      simp [f', w, linearSpecialTransvection_apply]
theorem projectiveRootSubgroup_conj
    (a : SpecialLinearGroup K V) (x : ℙ K V) :
    projectiveRootSubgroup (a • x) =
      MulAut.conj a • projectiveRootSubgroup x := by
  rw [Subgroup.pointwise_smul_def, projectiveRootSubgroup, projectiveRootSubgroup]
  change Subgroup.closure (projectiveRootGenerators (a • x)) =
    Subgroup.map (MulAut.conj a).toMonoidHom (Subgroup.closure (projectiveRootGenerators x))
  rw [MonoidHom.map_closure]
  change Subgroup.closure (projectiveRootGenerators (a • x)) =
    Subgroup.closure (MulAut.conj a '' projectiveRootGenerators x)
  rw [projectiveRootGenerators_conj]
section CoordinateRoots
variable {n : Type*} [Fintype n] [DecidableEq n]
def coordinateFunctional (j : n) (c : K) : Module.Dual K (n → K) :=
  c • LinearMap.proj j
def coordinateVector (i : n) : n → K :=
  Pi.single i 1
theorem coordinateVector_ne_zero (i : n) :
    coordinateVector (K := K) i ≠ 0 := by
  intro h
  have := congrFun h i
  simp [coordinateVector] at this
theorem coordinateFunctional_vector_eq_zero
    (i j : n) (hij : i ≠ j) (c : K) :
    coordinateFunctional j c (coordinateVector i) = 0 := by
  simp [coordinateFunctional, coordinateVector, LinearMap.proj_apply,
    Pi.single_apply, hij.symm]
theorem toLinEquiv_specialTransvection
    (i j : n) (hij : i ≠ j) (c : K) :
    Matrix.SpecialLinearGroup.toLin'_equiv
        (specialTransvection i j hij c) =
      linearSpecialTransvection
        (coordinateFunctional j c) (coordinateVector i)
        (coordinateFunctional_vector_eq_zero i j hij c) := by
  apply SpecialLinearGroup.ext
  intro z
  funext k
  change (Matrix.toLin' (Matrix.transvection i j c) z) k = _
  simp [Matrix.toLin'_apply',
    Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec,
    Matrix.single_mulVec, Function.update_apply,
    linearSpecialTransvection_apply,
    coordinateFunctional, coordinateVector, LinearMap.proj_apply,
    Pi.single_apply]
theorem toLinEquiv_specialTransvection_mem_projectiveRoots
    (i j : n) (hij : i ≠ j) (c : K) :
    Matrix.SpecialLinearGroup.toLin'_equiv
        (specialTransvection i j hij c) ∈
      iSup (projectiveRootSubgroup :
        ℙ K (n → K) → Subgroup (SpecialLinearGroup K (n → K))) := by
  let v := coordinateVector (K := K) i
  have hv : v ≠ 0 := coordinateVector_ne_zero i
  let x := Projectivization.mk K v hv
  apply (le_iSup projectiveRootSubgroup x)
  apply Subgroup.subset_closure
  refine ⟨coordinateFunctional j c, v, hv,
    coordinateFunctional_vector_eq_zero i j hij c, rfl, ?_⟩
  exact toLinEquiv_specialTransvection i j hij c
theorem projectiveRootSubgroups_generate_specialLinear
    (r : Rank) {K : Type*} [Field K] :
    iSup (projectiveRootSubgroup :
      ℙ K (Fin r.matrixRank → K) →
        Subgroup (SpecialLinearGroup K (Fin r.matrixRank → K))) = ⊤ := by
  apply top_unique
  intro g hg
  let S : Subgroup (SpecialLinearGroup K (Fin r.matrixRank → K)) :=
    iSup (projectiveRootSubgroup :
      ℙ K (Fin r.matrixRank → K) →
        Subgroup (SpecialLinearGroup K (Fin r.matrixRank → K)))
  let gm : Matrix.SpecialLinearGroup (Fin r.matrixRank) K :=
    Matrix.SpecialLinearGroup.toLin'_equiv.symm g
  let Q : Matrix (Fin r.matrixRank) (Fin r.matrixRank) K → Prop :=
    fun M ↦ ∃ hdet : Matrix.det M = 1,
      Matrix.SpecialLinearGroup.toLin'_equiv
        (⟨M, hdet⟩ : Matrix.SpecialLinearGroup (Fin r.matrixRank) K) ∈ S
  have htrans : ∀ t : Matrix.TransvectionStruct
      (Fin r.matrixRank) K, Q t.toMatrix := by
    intro t
    have hdet := Matrix.det_transvection_of_ne t.i t.j t.hij t.c
    refine ⟨hdet, ?_⟩
    have heq :
        (⟨t.toMatrix, hdet⟩ :
          Matrix.SpecialLinearGroup (Fin r.matrixRank) K) =
          specialTransvection t.i t.j t.hij t.c := by
      apply Subtype.ext
      rfl
    rw [heq]
    exact toLinEquiv_specialTransvection_mem_projectiveRoots
      t.i t.j t.hij t.c
  have hmul : ∀ A B, Q A → Q B → Q (A * B) := by
    rintro A B ⟨hdetA, hAmem⟩ ⟨hdetB, hBmem⟩
    have hdet : Matrix.det (A * B) = 1 := by
      rw [Matrix.det_mul, hdetA, hdetB, one_mul]
    refine ⟨hdet, ?_⟩
    let aSL : Matrix.SpecialLinearGroup (Fin r.matrixRank) K := ⟨A, hdetA⟩
    let bSL : Matrix.SpecialLinearGroup (Fin r.matrixRank) K := ⟨B, hdetB⟩
    have hab :
        (⟨A * B, hdet⟩ : Matrix.SpecialLinearGroup
          (Fin r.matrixRank) K) = aSL * bSL := by
      apply Subtype.ext
      rfl
    rw [hab, map_mul]
    exact S.mul_mem hAmem hBmem
  have hQ : Q (gm : Matrix (Fin r.matrixRank) (Fin r.matrixRank) K) := by
    apply Matrix.diagonal_transvection_induction Q
    · intro D hD
      have hdet : Matrix.det (Matrix.diagonal D) = 1 := hD.trans gm.prop
      cases r with
      | three =>
          exact CongruenceLifting.property_fin3_diagonal
            Q htrans hmul D hdet
      | four =>
          exact CongruenceLifting.property_fin4_diagonal
            Q htrans hmul D hdet
    · exact htrans
    · exact hmul
  obtain ⟨hdet, hgm⟩ := hQ
  change g ∈ S
  change Matrix.SpecialLinearGroup.toLin'_equiv gm ∈ S at hgm
  rw [show Matrix.SpecialLinearGroup.toLin'_equiv gm = g from
    Matrix.SpecialLinearGroup.toLin'_equiv.apply_symm_apply g] at hgm
  exact hgm
end CoordinateRoots
noncomputable def specialLinearIwasawaStructure
    (r : Rank) {K : Type*} [Field K] :
    MulAction.IwasawaStructure
      (SpecialLinearGroup K (Fin r.matrixRank → K))
      (ℙ K (Fin r.matrixRank → K)) where
  T := projectiveRootSubgroup
  is_comm := projectiveRootSubgroup_isMulCommutative
  is_conj := projectiveRootSubgroup_conj
  is_generator := projectiveRootSubgroups_generate_specialLinear r
noncomputable def abstractSpecialLinearToPSL
    (P : BasePrime) (r : Rank) (level : Nat) :
    SpecialLinearGroup (ResidueField P r level)
        (Fin r.matrixRank → ResidueField P r level) →*
      PSL P r level :=
  (specialLinearToPSL P r level).comp
    Matrix.SpecialLinearGroup.toLin'_equiv.symm.toMonoidHom
end ProjectiveRoots
end QEC.Coding.HighDimensionalExpander.CartwrightSteger


