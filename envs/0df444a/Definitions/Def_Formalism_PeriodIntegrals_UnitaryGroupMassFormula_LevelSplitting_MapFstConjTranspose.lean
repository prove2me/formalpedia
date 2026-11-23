-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_MapFstConjTranspose
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_MapFstConjTranspose
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:33:57.508118+00:00
-- url     : https://prove2.me/theorems/dedab90f-cb59-4ad8-84b7-7b3d9e3c7aa4
-- title:
--   Map Fst Conj Transpose
-- statement:
--   Definitions and structural lemmas for Map Fst Conj Transpose, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/MapFstConjTranspose.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_ConjDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_CjDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TensTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TopoAF
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.LevelKSplit.W.MVA
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct
section Ring
variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
variable (R1 R2 : Type) [CommRing R1] [Algebra F R1] [CommRing R2] [Algebra F R2]
def p1 : (R1 × R2) ⊗[F] E →+* R1 ⊗[F] E :=
  (Algebra.TensorProduct.map (AlgHom.fst F R1 R2) (AlgHom.id F E)).toRingHom
def p2 : (R1 × R2) ⊗[F] E →+* R2 ⊗[F] E :=
  (Algebra.TensorProduct.map (AlgHom.snd F R1 R2) (AlgHom.id F E)).toRingHom
variable {R1 R2} in

def crd (R : Type) [CommRing R] [Algebra F R] :
    R ⊗[F] E ≃ₗ[R] (Fin (Module.finrank F E) → R) :=
  (Algebra.TensorProduct.basis R (Module.finBasis F E)).equivFun
theorem crd_symm (R : Type) [CommRing R] [Algebra F R] (c : Fin (Module.finrank F E) → R) :
    (crd (E := E) R).symm c = ∑ k, c k ⊗ₜ (Module.finBasis F E k) := by
  simp [crd, Module.Basis.equivFun_symm_apply, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul']
theorem fst_coordinates (x : (R1 × R2) ⊗[F] E) :
    p1 R1 R2 x = (crd R1).symm (fun k => (crd (R1 × R2) x k).1) := by
  conv_lhs => rw [← (crd (E := E) (R1 × R2)).symm_apply_apply x]
  rw [crd_symm, crd_symm, map_sum]
  rfl
theorem snd_coordinates (x : (R1 × R2) ⊗[F] E) :
    p2 R1 R2 x = (crd R2).symm (fun k => (crd (R1 × R2) x k).2) := by
  conv_lhs => rw [← (crd (E := E) (R1 × R2)).symm_apply_apply x]
  rw [crd_symm, crd_symm, map_sum]
  rfl
def qq (a : R1 ⊗[F] E) (b : R2 ⊗[F] E) : (R1 × R2) ⊗[F] E :=
  (crd (R1 × R2)).symm (fun k => (crd R1 a k, crd R2 b k))
theorem fst_pair (a : R1 ⊗[F] E) (b : R2 ⊗[F] E) : p1 R1 R2 (qq R1 R2 a b) = a := by
  unfold qq
  rw [fst_coordinates, LinearEquiv.apply_symm_apply]
  exact (crd R1).symm_apply_apply a
theorem snd_pair (a : R1 ⊗[F] E) (b : R2 ⊗[F] E) : p2 R1 R2 (qq R1 R2 a b) = b := by
  unfold qq
  rw [snd_coordinates, LinearEquiv.apply_symm_apply]
  exact (crd R2).symm_apply_apply b
theorem qq_p (x : (R1 × R2) ⊗[F] E) : qq R1 R2 (p1 R1 R2 x) (p2 R1 R2 x) = x := by
  apply (crd (E := E) (R1 × R2)).injective
  unfold qq
  rw [LinearEquiv.apply_symm_apply, fst_coordinates, snd_coordinates, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
theorem ext_p {x y : (R1 × R2) ⊗[F] E} (h1 : p1 R1 R2 x = p1 R1 R2 y)
    (h2 : p2 R1 R2 x = p2 R1 R2 y) : x = y := by
  rw [← qq_p R1 R2 x, ← qq_p R1 R2 y, h1, h2]
variable (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
theorem fst_conj_bis (x : (R1 × R2) ⊗[F] E) :
    p1 R1 R2 (sigR (R1 × R2) σ x) = sigR R1 σ (p1 R1 R2 x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => rfl
  | add x y hx hy => simp only [map_add, hx, hy]
theorem snd_conj_alt (x : (R1 × R2) ⊗[F] E) :
    p2 R1 R2 (sigR (R1 × R2) σ x) = sigR R2 σ (p2 R1 R2 x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => rfl
  | add x y hx hy => simp only [map_add, hx, hy]
theorem fst_inclusion (e : E) : p1 R1 R2 (inclR (F := F) (R1 × R2) e) = inclR (F := F) R1 e := rfl
theorem snd_inclusion (e : E) : p2 R1 R2 (inclR (F := F) (R1 × R2) e) = inclR (F := F) R2 e := rfl
theorem map_fst_conj_transpose (P : Matrix (Fin M) (Fin M) ((R1 × R2) ⊗[F] E)) :
    (Formalism.UG.cT (sigR (R1 × R2) σ) P).map (p1 R1 R2) =
      Formalism.UG.cT (sigR R1 σ) (P.map (p1 R1 R2)) := by
  ext i j
  simp [Formalism.UG.cT, fst_conj_bis]
theorem map_snd_conj_transpose (P : Matrix (Fin M) (Fin M) ((R1 × R2) ⊗[F] E)) :
    (Formalism.UG.cT (sigR (R1 × R2) σ) P).map (p2 R1 R2) =
      Formalism.UG.cT (sigR R2 σ) (P.map (p2 R1 R2)) := by
  ext i j
  simp [Formalism.UG.cT, snd_conj_alt]
theorem map_fst_form : (JR (F := F) (R1 × R2) J).map (p1 R1 R2) = JR (F := F) R1 J := by
  ext i j
  exact fst_inclusion R1 R2 (J i j)
theorem map_snd_form : (JR (F := F) (R1 × R2) J).map (p2 R1 R2) = JR (F := F) R2 J := by
  ext i j
  exact snd_inclusion R1 R2 (J i j)
def mlift (m : Matrix (Fin M) (Fin M) (R2 ⊗[F] E)) : Matrix (Fin M) (Fin M) ((R1 × R2) ⊗[F] E) :=
  Matrix.of fun i j => qq R1 R2 ((1 : Matrix (Fin M) (Fin M) (R1 ⊗[F] E)) i j) (m i j)
theorem matrix_lift_fst (m : Matrix (Fin M) (Fin M) (R2 ⊗[F] E)) : (mlift R1 R2 m).map (p1 R1 R2) = 1 := by
  ext i j
  exact fst_pair R1 R2 _ _
theorem matrix_lift_snd (m : Matrix (Fin M) (Fin M) (R2 ⊗[F] E)) : (mlift R1 R2 m).map (p2 R1 R2) = m := by
  ext i j
  exact snd_pair R1 R2 _ _
theorem mext {P Q : Matrix (Fin M) (Fin M) ((R1 × R2) ⊗[F] E)} (h1 : P.map (p1 R1 R2) = Q.map (p1 R1 R2))
    (h2 : P.map (p2 R1 R2) = Q.map (p2 R1 R2)) : P = Q := by
  ext i j
  exact ext_p R1 R2 (congrArg (· i j) h1) (congrArg (· i j) h2)
theorem mlift_mul (m m' : Matrix (Fin M) (Fin M) (R2 ⊗[F] E)) :
    mlift R1 R2 m * mlift R1 R2 m' = mlift R1 R2 (m * m') := by
  apply mext
  · rw [Matrix.map_mul, matrix_lift_fst, matrix_lift_fst, matrix_lift_fst, one_mul]
  · rw [Matrix.map_mul, matrix_lift_snd, matrix_lift_snd, matrix_lift_snd]
theorem mlift_one : mlift R1 R2 (1 : Matrix (Fin M) (Fin M) (R2 ⊗[F] E)) = 1 := by
  apply mext
  · rw [matrix_lift_fst, Matrix.map_one _ (map_zero _) (map_one _)]
  · rw [matrix_lift_snd, Matrix.map_one _ (map_zero _) (map_one _)]
def glift (u : GL (Fin M) (R2 ⊗[F] E)) : GL (Fin M) ((R1 × R2) ⊗[F] E) :=
  ⟨mlift R1 R2 (u : Matrix (Fin M) (Fin M) (R2 ⊗[F] E)), mlift R1 R2 (↑u⁻¹ : Matrix (Fin M) (Fin M) _),
    by rw [mlift_mul, u.mul_inv, mlift_one], by rw [mlift_mul, u.inv_mul, mlift_one]⟩
theorem glift_mem (g : HA R2 σ J) : glift R1 R2 (HA.mat R2 σ J g) ∈ HR (R1 × R2) σ J := by
  have hg : HA.mat R2 σ J g ∈ HR R2 σ J := g.2
  change Formalism.UG.cT (sigR R2 σ) ((HA.mat R2 σ J g : Matrix (Fin M) (Fin M) (R2 ⊗[F] E))) * JR (F := F) R2 J *
    (HA.mat R2 σ J g : Matrix (Fin M) (Fin M) (R2 ⊗[F] E)) = JR (F := F) R2 J at hg
  change Formalism.UG.cT (sigR (R1 × R2) σ) (mlift R1 R2 (HA.mat R2 σ J g : Matrix (Fin M) (Fin M) (R2 ⊗[F] E))) *
    JR (F := F) (R1 × R2) J * mlift R1 R2 (HA.mat R2 σ J g : Matrix (Fin M) (Fin M) (R2 ⊗[F] E)) = JR (F := F) (R1 × R2) J
  apply mext
  · rw [Matrix.map_mul, Matrix.map_mul, map_fst_conj_transpose, map_fst_form, matrix_lift_fst]
    ext i j
    simp [Formalism.UG.cT, Matrix.one_apply]
  · rw [Matrix.map_mul, Matrix.map_mul, map_snd_conj_transpose, map_snd_form, matrix_lift_snd]
    exact hg
def lift (g : HA R2 σ J) : HA (R1 × R2) σ J :=
  (⟨glift R1 R2 (HA.mat R2 σ J g), glift_mem R1 R2 σ J g⟩ : ↥(HR (R1 × R2) σ J))
def psiE : (Fin M → (R1 × R2) ⊗[F] E) ≃+ (Fin M → R1 ⊗[F] E) × (Fin M → R2 ⊗[F] E) where
  toFun x := (fun i => p1 R1 R2 (x i), fun i => p2 R1 R2 (x i))
  invFun y := fun i => qq R1 R2 (y.1 i) (y.2 i)
  left_inv x := funext fun i => qq_p R1 R2 (x i)
  right_inv y := Prod.ext (funext fun i => fst_pair R1 R2 _ _) (funext fun i => snd_pair R1 R2 _ _)
  map_add' x y := by
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> simp
end Ring
end PI.LevelKSplit.W.MVA


