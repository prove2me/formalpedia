-- Prove2me | Definitions.Def_FreeGroupFactorProof14
-- name    : FreeGroupFactorProof14
-- status  : Definition
-- author  : @wurtle
-- created : 2026-11-04T02:23:15.030332+00:00
-- url     : https://prove2.me/theorems/bce53939-4463-4724-a818-6dc965acf55a
-- title:
--   Free group factors: supporting development, part 14
-- statement:
--   Part 14 of the supporting Lean development for the isomorphism of all interpolated free group factors. It contains the definitions (operators on free Fock spaces, Gaussian systems, weighted corner models, stabilization and amplification constructions, and the free-group word maps) that the statements of the published child theorems and of the main theorem's proof refer to, in source order, together with the proved lemmas their bodies rely on. No result is assumed.
--
--   **Formalization Note** Definitions of this development carry proof fields and `Classical.choose` terms, so their dependencies must be proved here rather than imported from theorems. The code is OpenAI's, carved from `lean/OAI/Analysis/FreeGroupFactor` and `lean/OAI/Analysis/InterpolatedFactors` in openai/math at `adc7f12` and ported to Lean 4.33.1 and Mathlib `0df444a`.
-- source:
--   OpenAI, An isomorphism of the free group factors, September 23, 2026, https://github.com/openai/math (paper: preprints/An-isomorphism-of-the-free-group-factors-September-23-2026/An-isomorphism-of-the-free-group-factors-September-23-2026.pdf; Lean: lean/OAI/Analysis/FreeGroupFactor and lean/OAI/Analysis/InterpolatedFactors, Apache License 2.0)

import Mathlib
import Definitions.Def_FreeGroupFactorProof13

set_option linter.all false

section
namespace OAI

noncomputable section

universe u_1 u_2 u_3

namespace FreeGroupFactorMain.WeightedFock

section
open FreeFock
variable {ι : Type u_1} [DecidableEq ι]

variable (u v : ℝ) (i : ι)

end

section
open FreeFock
variable {ι : Type u_2} [DecidableEq ι]

theorem vertex_projection (r : Bool) : IsStarProjection (vertex r : Operator ι) := by
  rw [vertex_eq_proj]
  exact CoordinateProjection.projection _

theorem ambientRect_left (u v : ℝ) (i : ι) (r s : Bool) :
    vertex r*ambientRect u v i r s=ambientRect u v i r s := by
  rw [ambientRect,← mul_assoc,← mul_assoc,vertex_mul_vertex,ite_eq_left rfl]

theorem ambientRect_right (u v : ℝ) (i : ι) (r s : Bool) :
    ambientRect u v i r s*vertex s=ambientRect u v i r s := by
  rw [ambientRect,mul_assoc,vertex_mul_vertex,ite_eq_left rfl]

def diagonalLeg (u v : ℝ) (i : ι) (r : Bool) : Operator ι :=
  ambientRect u v i r r+star (ambientRect u v i r r)

theorem diagonalLeg_selfAdjoint (u v : ℝ) (i : ι) (r : Bool) :
    IsSelfAdjoint (diagonalLeg u v i r) := IsSelfAdjoint.add_star_self (ambientRect u v i r r)

theorem diagonalLeg_left (u v : ℝ) (i : ι) (r : Bool) :
    vertex r*diagonalLeg u v i r=diagonalLeg u v i r := by
  have hs := congrArg star (ambientRect_right u v i r r)
  simp only [star_mul,vertex_star] at hs
  rw [diagonalLeg,mul_add,ambientRect_left,hs]

theorem diagonalLeg_right (u v : ℝ) (i : ι) (r : Bool) :
    diagonalLeg u v i r*vertex r=diagonalLeg u v i r := by
  simpa only [star_mul,vertex_star,(diagonalLeg_selfAdjoint u v i r).star_eq] using
    congrArg star (diagonalLeg_left u v i r)

theorem vertexRoot_inner (u v : ℝ) (r : Bool) :
    inner ℂ (vertex r (vacuum u v : H ι)) (vertex r (vacuum u v))=vacuumTrace u v (vertex r : Operator ι) := by
  rw [← ContinuousLinearMap.adjoint_inner_right (vertex r : Operator ι)]
  change inner ℂ (vacuum u v) ((star (vertex r)*vertex r : Operator ι) (vacuum u v))=_
  rw [vertex_star,vertex_mul_vertex,ite_eq_left rfl]
  rfl

theorem vertexRoot_ne_zero (u v : ℝ) (hu : u≠0) (hv : v≠0) (r : Bool) :
    vertex r (vacuum u v : H ι)≠0 := by
  intro hz
  have hh := congrArg (fun ξ : H ι => ξ ([],r)) hz
  cases r
  · apply hv
    simpa only [weight,vertex_vacuum,Bool.false_eq_true,ite_false,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,
      lp.single_apply,Pi.single_eq_same,mul_one,lp.coeFn_zero,Pi.zero_apply,Complex.ofReal_eq_zero] using hh
  · apply hu
    simpa only [weight,vertex_vacuum,ite_true,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,
      lp.single_apply,Pi.single_eq_same,mul_one,lp.coeFn_zero,Pi.zero_apply,Complex.ofReal_eq_zero] using hh

theorem diagonalLeg_eigen_root_zero (u v : ℝ) (hu : u≠0) (hv : v≠0) (i : ι)
    (r : Bool) (z : ℂ) (η : H ι) (he : diagonalLeg u v i r η=z • η) :
    inner ℂ (vertex r (vacuum u v)) η=0 := by
  apply SupportedSemicircle.unnormalized_eigen_root_zero
    (vertex r) (ambientRect u v i r r) (vertex_projection r)
    (ambientRect_left u v i r r) (ambientRect_right u v i r r)
    _ (vertexRoot_ne_zero u v hu hv r) _ _ _ z η he
  · exact DFunLike.congr_fun (vertex_projection (ι := ι) r).isIdempotentElem.eq _
  · rw [vertexRoot_inner]
    have hh := ambientRect_covariance u v i i r r r r (1:oldAlgebra u v ∅)
    simpa only [OneMemClass.coe_one,mul_one,one_mul,ite_true,and_self] using hh
  · exact ambientRect_annihilate u v i r r (vertexOld u v r)

def diagonalSelf (u v : ℝ) (i : ι) : Operator ι := diagonalLeg u v i true+diagonalLeg u v i false

theorem diagonalSelf_eq (u v : ℝ) (i : ι) :
    diagonalSelf u v i=diagonalCreate u v i+star (diagonalCreate u v i) := by
  simp only [diagonalSelf,diagonalLeg,diagonalCreate,star_add (R := Operator ι)]
  abel

def diagonalShift (u v : ℝ) (i : ι) : ℝ := 2*‖diagonalSelf u v i‖+1

def diagonalGenerator (u v : ℝ) (i : ι) : Operator ι := diagonalSelf u v i+(diagonalShift u v i:ℂ) • P

theorem diagonalSelf_selfAdjoint (u v : ℝ) (i : ι) : IsSelfAdjoint (diagonalSelf u v i) := by
  rw [diagonalSelf_eq]
  exact IsSelfAdjoint.add_star_self (diagonalCreate u v i)

theorem diagonalGenerator_selfAdjoint (u v : ℝ) (i : ι) : IsSelfAdjoint (diagonalGenerator u v i) := by
  change star (_+_)=_+_
  simp only [star_add (R := Operator ι),(diagonalSelf_selfAdjoint u v i).star_eq,star_smul,Complex.star_def,
    Complex.conj_ofReal,projection_P.isSelfAdjoint.star_eq]

theorem diagonalGenerator_eigen_root_zero (u v : ℝ) (hu : u≠0) (hv : v≠0) (i : ι)
    (z : ℂ) (η : H ι) (he : diagonalGenerator u v i η=z • η) : inner ℂ (vacuum u v) η=0 := by
  have hh := OrthogonalSpectralSum.eigen_root_zero (vertex true) (vertex false)
    (diagonalLeg u v i true) (diagonalLeg u v i false) (vertex_projection true) (vertex_projection false)
    (by rw [vertex_mul_vertex];rfl) (diagonalLeg_left u v i true) (diagonalLeg_right u v i true)
    (diagonalLeg_left u v i false) (diagonalLeg_right u v i false) (vacuum u v)
    (diagonalLeg_eigen_root_zero u v hu hv i true) (diagonalLeg_eigen_root_zero u v hu hv i false)
    (diagonalShift u v i) z η he
  simpa only [vertex_true,vertex_false,add_sub_cancel,one_apply_eq_self] using hh

theorem P_mem_diagonalBase (u v : ℝ) (i : ι) : P∈diagonalBase u v i :=
  Bicommutant.subset _ (Set.mem_insert_of_mem _ (P_mem_old u v ∅))

theorem diagonalSelf_mem (u v : ℝ) (i : ι) : diagonalSelf u v i∈diagonalBase u v i := by
  rw [diagonalSelf_eq]
  exact Bicommutant.subset _ (Set.mem_insert _ _)

theorem diagonalGenerator_mem (u v : ℝ) (i : ι) : diagonalGenerator u v i∈diagonalBase u v i :=
  add_mem (diagonalSelf_mem u v i) ((diagonalBase u v i).smul_mem (P_mem_diagonalBase u v i) _)

theorem P_commute_diagonalSelf (u v : ℝ) (i : ι) : Commute P (diagonalSelf u v i) := by
  have hf : Commute P (diagonalLeg u v i true) :=
    (diagonalLeg_left u v i true).trans (diagonalLeg_right u v i true).symm
  have hq : Commute (1-P) (diagonalLeg u v i false) :=
    (diagonalLeg_left u v i false).trans (diagonalLeg_right u v i false).symm
  have hp := (Commute.one_left (diagonalLeg u v i false)).sub_left hq
  rw [sub_sub_cancel] at hp
  exact hf.add_right hp

theorem diagonalBase_eq_generated (u v : ℝ) (i : ι) :
    diagonalBase u v i=Bicommutant.algebra {diagonalGenerator u v i} := by
  apply le_antisymm
  · have hp : P∈Bicommutant.algebra {diagonalGenerator u v i} :=
      SpectralSeparation.separated_projection_mem projection_P (diagonalSelf_selfAdjoint u v i)
        (P_commute_diagonalSelf u v i) (diagonalShift u v i) (by dsimp [diagonalShift];linarith)
    apply Bicommutant.generated_le
    rintro T (rfl|hT)
    · rw [← diagonalSelf_eq]
      have he : diagonalSelf u v i=diagonalGenerator u v i-(diagonalShift u v i:ℂ) • P := by
        rw [diagonalGenerator,add_sub_cancel_right]
      rw [he]
      exact sub_mem (Bicommutant.subset _ (Set.mem_singleton _)) ((Bicommutant.algebra _).smul_mem hp _)
    · apply Bicommutant.generated_le {diagonalGenerator u v i}
        (insert (P:Operator ι) (S u v '' (∅:Set ι))) ?_ hT
      rintro a (rfl|⟨_,h,_⟩)
      · exact hp
      · exact False.elim h
  · apply Bicommutant.generated_le
    rintro T rfl
    exact diagonalGenerator_mem u v i
end

section
open FreeFock GaussianOrthogonal
variable {ι : Type u_3} [DecidableEq ι]

theorem diagonalBase_vertex_commute (u v : ℝ) (i : ι) (r : Bool) (T : diagonalBase u v i) :
    Commute (vertex r : Operator ι) (T:Operator ι) := by
  have hp : P∈StarSubalgebra.centralizer ℂ {diagonalGenerator u v i} := by
    rw [StarSubalgebra.mem_centralizer_iff]
    rintro a rfl
    have hc : Commute P (diagonalGenerator u v i) :=
      (P_commute_diagonalSelf u v i).add_right ((Commute.refl P).smul_right _)
    exact ⟨hc.eq.symm,by rw [(diagonalGenerator_selfAdjoint u v i).star_eq];exact hc.eq.symm⟩
  have hh : (T:Operator ι)∈Bicommutant.algebra {diagonalGenerator u v i} :=
    (diagonalBase_eq_generated u v i).le T.property
  have hc := ((StarSubalgebra.mem_centralizer_iff ℂ).mp hh P hp).1
  cases r
  · exact (Commute.one_left _).sub_left hc
  · exact hc

end

open FreeFock WeightedCornerIndex

end FreeGroupFactorMain.WeightedFock

end

end OAI
end


