-- Prove2me | Definitions.Def_FreeGroupFactorProof04
-- name    : FreeGroupFactorProof04
-- status  : Definition
-- author  : @wurtle
-- created : 2026-11-04T00:40:49.455276+00:00
-- url     : https://prove2.me/theorems/ec10839a-1ba0-4be3-86c5-01c324a50d05
-- title:
--   Free group factors: supporting development, part 4 of 12
-- statement:
--   Part 4 of the supporting Lean development for the isomorphism of all interpolated free group factors. It contains the definitions (operators on free Fock spaces, Gaussian systems, weighted corner models, stabilization and amplification constructions, and the free-group word maps) that the statements of the published child theorems and of the main theorem's proof refer to, in source order, together with the proved lemmas their bodies rely on. No result is assumed.
--
--   **Formalization Note** Definitions of this development carry proof fields and `Classical.choose` terms, so their dependencies must be proved here rather than imported from theorems. The code is OpenAI's, carved from `lean/OAI/Analysis/FreeGroupFactor` and `lean/OAI/Analysis/InterpolatedFactors` in openai/math at `adc7f12` and ported to Lean 4.33.1 and Mathlib `0df444a`.
-- source:
--   OpenAI, An isomorphism of the free group factors, September 23, 2026, https://github.com/openai/math (paper: preprints/An-isomorphism-of-the-free-group-factors-September-23-2026/An-isomorphism-of-the-free-group-factors-September-23-2026.pdf; Lean: lean/OAI/Analysis/FreeGroupFactor and lean/OAI/Analysis/InterpolatedFactors, Apache License 2.0)

import Mathlib
import Definitions.Def_FreeGroupFactorProof03

set_option linter.all false

section
namespace OAI

noncomputable section

universe u_1 u_2 u_3

open Filter Topology
namespace FreeGroupFactorMain.JacobiNonatom

end FreeGroupFactorMain.JacobiNonatom
namespace FreeGroupFactorMain.WeightedFock

section
open FreeFock Filter Topology
open scoped ENNReal
variable {ι : Type u_1} [DecidableEq ι]

end

section
open FreeFock
variable {ι : Type u_2}

variable [DecidableEq ι]

theorem leftEdgeSquare_eigen_root_zero (u v : ℝ) (hu : u≠0) (hv : v≠0)
    (i : ι) (z : ℂ) (hz : z≠0) (ξ : H ι)
    (hξ : (offDiagonal u v i*star (offDiagonal u v i)) ξ=z • ξ) : ξ ([],true)=0 := by
  have he : edgeSquare v u i (flipSpatial.symm ξ)=z • flipSpatial.symm ξ := by
    apply flipSpatial.injective
    rw [map_smul,LinearIsometryEquiv.apply_symm_apply]
    have hh := DFunLike.congr_fun (flipSpatial_conjugates_edgeSquare v u i) ξ
    simpa only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply] using hh.trans hξ
  have hh := edgeSquare_eigen_root_zero v u hv hu i z hz (flipSpatial.symm ξ) he
  have hh' : flipSpatial.symm ξ=flipSpatial ξ := by
    apply flipSpatial.injective
    rw [LinearIsometryEquiv.apply_symm_apply]
    ext w
    simp only [flipSpatial_apply,flipPath_involutive]
  rw [hh',flipSpatial_apply] at hh
  exact hh

end
open FreeFock Amplification.Polar
variable {ι : Type u_3} [DecidableEq ι]

def leftModulus (u v : ℝ) (i : ι) : Operator ι := offDiagonal u v i*star (edgePolar u v i)

theorem leftModulus_selfAdjoint (u v : ℝ) (i : ι) : IsSelfAdjoint (leftModulus u v i) :=
  edge_left_modulus_selfAdjoint u v i

theorem leftModulus_square (u v : ℝ) (hv : 0≤v) (hvu : v<u) (i : ι) :
    leftModulus u v i*leftModulus u v i=offDiagonal u v i*star (offDiagonal u v i) := by
  calc
    _ = leftModulus u v i*star (leftModulus u v i) := by rw [(leftModulus_selfAdjoint u v i).star_eq]
    _ = (offDiagonal u v i*star (edgePolar u v i))*(edgePolar u v i*star (offDiagonal u v i)) := by
      simp only [leftModulus,star_mul,star_star]
    _ = _ := by
      rw [mul_assoc,← mul_assoc (star (edgePolar u v i)),edgePolar_initial u v hv hvu,
        ← mul_assoc,offDiagonal_right]

theorem leftModulus_mul_range (u v : ℝ) (hv : 0≤v) (hvu : v<u) (i : ι) :
    leftModulus u v i*edgeRange u v i=leftModulus u v i := by
  rw [leftModulus,edgeRange,mul_assoc,← mul_assoc (star (edgePolar u v i)),
    edgePolar_initial u v hv hvu,← mul_assoc,offDiagonal_right]

theorem range_mul_leftModulus (u v : ℝ) (hv : 0≤v) (hvu : v<u) (i : ι) :
    edgeRange u v i*leftModulus u v i=leftModulus u v i := by
  simpa only [star_mul,(edgeRange_projection u v i).isSelfAdjoint.star_eq,
    (leftModulus_selfAdjoint u v i).star_eq] using congrArg star (leftModulus_mul_range u v hv hvu i)

theorem starPolar_mul_leftModulus (u v : ℝ) (hv : 0≤v) (hvu : v<u) (i : ι) :
    star (edgePolar u v i)*leftModulus u v i=star (offDiagonal u v i) := by
  rw [← (leftModulus_selfAdjoint u v i).star_eq,leftModulus,star_mul,star_star,
    ← mul_assoc,edgePolar_initial u v hv hvu]
  simpa only [star_mul,projection_P.one_sub.isSelfAdjoint.star_eq]
    using congrArg star (offDiagonal_right u v i)

theorem range_zero_of_starEdge_zero (u v : ℝ) (i : ι) (η : H ι)
    (hη : star (offDiagonal u v i) η=0) : edgeRange u v i η=0 := by
  rw [edgeRange,edgePolar,partialIsometry_final]
  apply (Submodule.starProjection_apply_eq_zero_iff _).mpr
  rw [closedRange_eq_orthogonal_ker,Submodule.orthogonal_orthogonal]
  exact hη

theorem leftModulus_eigen_root_zero (u v : ℝ) (hv : 0<v) (hvu : v<u)
    (i : ι) (z : ℂ) (η : H ι) (he : leftModulus u v i η=z • η) :
    inner ℂ (edgeRange u v i (lp.single 2 ([],true) 1)) η=0 := by
  rw [← ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ (lp.single 2 ([],true) 1) (star (edgeRange u v i) η)=0
  rw [(edgeRange_projection u v i).isSelfAdjoint.star_eq]
  by_cases hz : z=0
  · have hf : leftModulus u v i η=0 := by simpa only [hz,zero_smul] using he
    have hx : star (offDiagonal u v i) η=0 := by
      rw [← starPolar_mul_leftModulus u v hv.le hvu i,mul_apply_eq_comp,hf,map_zero]
    rw [range_zero_of_starEdge_zero u v i η hx,inner_zero_right]
  · have hs : (offDiagonal u v i*star (offDiagonal u v i)) η=(z*z) • η := by
      rw [← leftModulus_square u v hv.le hvu i,mul_apply_eq_comp,he,map_smul,he,smul_smul]
    have hr : edgeRange u v i η=η := by
      apply smul_right_injective (H ι) hz
      change z • edgeRange u v i η=z • η
      rw [← map_smul,← he]
      exact DFunLike.congr_fun (range_mul_leftModulus u v hv.le hvu i) η
    rw [hr]
    simpa only [lp.inner_single_left,RCLike.inner_apply,map_one,mul_one] using
      leftEdgeSquare_eigen_root_zero u v (hv.trans hvu).ne' hv.ne' i (z*z) (mul_ne_zero hz hz) η hs

end FreeGroupFactorMain.WeightedFock

end

end OAI
end

section
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7

open Filter Topology
namespace FreeGroupFactorMain.BicommutantAtom
open InnerProductSpace
variable {E : Type u_1} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
local notation "Op" => E →L[ℂ] E

theorem rankOne_commute_fixed (A : Op) (hA : IsSelfAdjoint A) (x y : E)
    (hx : A x=x) (hy : A y=y) : Commute A (rankOne ℂ x y) := by
  apply ContinuousLinearMap.ext
  intro z
  change A (inner ℂ y z • x)=inner ℂ y (A z) • x
  rw [map_smul,hx,← ContinuousLinearMap.adjoint_inner_left]
  change inner ℂ y z • x=inner ℂ (star A y) z • x
  rw [hA.star_eq,hy]

theorem rankOne_commute_zero (A : Op) (hA : IsSelfAdjoint A) (x y : E)
    (hx : A x=0) (hy : A y=0) : Commute A (rankOne ℂ x y) := by
  apply ContinuousLinearMap.ext
  intro z
  change A (inner ℂ y z • x)=inner ℂ y (A z) • x
  rw [map_smul,hx,← ContinuousLinearMap.adjoint_inner_left]
  change inner ℂ y z • (0:E)=inner ℂ (star A y) z • x
  rw [hA.star_eq,hy,inner_zero_left,zero_smul,smul_zero]

omit [CompleteSpace E] in

theorem scalar_of_rankOne_commutes (d T : Op)
    (h : ∀ x y : E, Commute T (rankOne ℂ (d x) (d y))) :
    ∃ c : ℂ,T*d=c • d := by
  by_cases hd : d=0
  · exact ⟨0,by simp [hd]⟩
  have hx : ∃ x : E,d x≠0 := by
    by_contra! hn
    apply hd
    ext x
    exact hn x
  obtain ⟨x,hx⟩ := hx
  let η := d x
  let a := inner ℂ η η
  have ha : a≠0 := by
    dsimp [a,η]
    exact fun hh => hx ((inner_self_eq_zero (𝕜 := ℂ)).mp hh)
  let b := inner ℂ η (T η)
  refine ⟨a⁻¹*b,?_⟩
  ext z
  have he := DFunLike.congr_fun (h z x).eq η
  change T (a • d z)=b • d z at he
  rw [map_smul] at he
  change T (d z)=(a⁻¹*b) • d z
  calc
    _ = a⁻¹ • (a • T (d z)) := by rw [smul_smul,inv_mul_cancel₀ ha,one_smul]
    _ = _ := by rw [he,smul_smul]

theorem common_kernel_scalar (p s d T : Op) (hp : IsSelfAdjoint p) (hs : IsSelfAdjoint s)
    (hpd : p*d=d) (hsd : s*d=0)
    (hT : T∈StarSubalgebra.centralizer ℂ
      (StarSubalgebra.centralizer ℂ (insert p {s}) : Set Op)) :
    ∃ c : ℂ,T*d=c • d := by
  apply scalar_of_rankOne_commutes d T
  intro x y
  have hpx (z : E) : p (d z)=d z := DFunLike.congr_fun hpd z
  have hsx (z : E) : s (d z)=0 := DFunLike.congr_fun hsd z
  have hR : rankOne ℂ (d x) (d y)∈StarSubalgebra.centralizer ℂ (insert p {s}) := by
    rw [StarSubalgebra.mem_centralizer_iff]
    intro A hA
    rcases Set.mem_insert_iff.mp hA with hA | hA
    · subst A
      have hh := rankOne_commute_fixed p hp (d x) (d y) (hpx x) (hpx y)
      exact ⟨hh.eq,by simpa only [hp.star_eq] using hh.eq⟩
    · have hA' : A=s := hA
      subst A
      have hh := rankOne_commute_zero s hs (d x) (d y) (hsx x) (hsx y)
      exact ⟨hh.eq,by simpa only [hs.star_eq] using hh.eq⟩
  exact ((StarSubalgebra.mem_centralizer_iff ℂ).mp hT _ hR).1.symm
end FreeGroupFactorMain.BicommutantAtom
namespace FreeGroupFactorMain.WeightedFock
open FreeFock Amplification.Polar
variable {ι : Type u_2} [DecidableEq ι]

theorem P_mem_edge (u v : ℝ) (i : ι) : (P : Operator ι)∈edgeAlgebra u v i :=
  StarAlgebra.adjoin_le_centralizer_centralizer ℂ _
    (StarAlgebra.subset_adjoin ℂ _ (Set.mem_insert _ _))

theorem edge_sum_mem_edge (u v : ℝ) (i : ι) :
    offDiagonal u v i+star (offDiagonal u v i)∈edgeAlgebra u v i :=
  StarAlgebra.adjoin_le_centralizer_centralizer ℂ _
    (StarAlgebra.subset_adjoin ℂ _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))

theorem offDiagonal_mul_P (u v : ℝ) (i : ι) : offDiagonal u v i*P=0 :=
  CornerRerouting.right_zero (offDiagonal_right u v i)

theorem offDiagonal_mem_edge (u v : ℝ) (i : ι) : offDiagonal u v i∈edgeAlgebra u v i := by
  have hz : P*star (offDiagonal u v i)=0 := by
    simpa only [star_mul,star_zero (Operator ι),projection_P.isSelfAdjoint.star_eq]
      using congrArg star (offDiagonal_mul_P u v i)
  have he : P*(offDiagonal u v i+star (offDiagonal u v i))=offDiagonal u v i := by
    rw [mul_add,offDiagonal_left,hz,add_zero]
  rw [← he]
  exact mul_mem (P_mem_edge u v i) (edge_sum_mem_edge u v i)

theorem edgePolar_mem_edge (u v : ℝ) (i : ι) : edgePolar u v i∈edgeAlgebra u v i :=
  partialIsometry_mem_centralizer _ (offDiagonal_mem_edge u v i)

theorem edgeRange_mem_edge (u v : ℝ) (i : ι) : edgeRange u v i∈edgeAlgebra u v i :=
  mul_mem (edgePolar_mem_edge u v i) (star_mem (edgePolar_mem_edge u v i))

def edgeDefect (u v : ℝ) (i : ι) : Operator ι := P-edgeRange u v i

theorem edgeDefect_projection (u v : ℝ) (i : ι) : IsStarProjection (edgeDefect u v i) :=
  (edgeRange_projection u v i).sub_of_mul_eq_right projection_P (edgeRange_le_P u v i)

theorem edgeDefect_mem_edge (u v : ℝ) (i : ι) : edgeDefect u v i∈edgeAlgebra u v i :=
  sub_mem (P_mem_edge u v i) (edgeRange_mem_edge u v i)

theorem edgeRange_mul_offDiagonal (u v : ℝ) (i : ι) :
    edgeRange u v i*offDiagonal u v i=offDiagonal u v i := by
  have hf := partialIsometry_factorization (offDiagonal u v i)
  change edgePolar u v i*modulus (offDiagonal u v i)=offDiagonal u v i at hf
  calc
    _ = edgeRange u v i*(edgePolar u v i*modulus (offDiagonal u v i)) := by rw [hf]
    _ = edgePolar u v i*modulus (offDiagonal u v i) := by
      rw [← mul_assoc]
      exact congrArg (fun U => U*modulus (offDiagonal u v i)) (partialIsometry_partial _)
    _ = _ := hf

theorem P_mul_edgeDefect (u v : ℝ) (i : ι) : P*edgeDefect u v i=edgeDefect u v i := by
  rw [edgeDefect,mul_sub,projection_P.isIdempotentElem.eq,edgeRange_le_P]

theorem edgeDefect_mul_P (u v : ℝ) (i : ι) : edgeDefect u v i*P=edgeDefect u v i := by
  simpa only [star_mul,projection_P.isSelfAdjoint.star_eq,(edgeDefect_projection u v i).isSelfAdjoint.star_eq]
    using congrArg star (P_mul_edgeDefect u v i)

theorem edgeSum_mul_defect (u v : ℝ) (i : ι) :
    (offDiagonal u v i+star (offDiagonal u v i))*edgeDefect u v i=0 := by
  have hx : offDiagonal u v i*edgeDefect u v i=0 := by
    rw [← P_mul_edgeDefect u v i,← mul_assoc,offDiagonal_mul_P,zero_mul]
  have hxp : star (offDiagonal u v i)*P=star (offDiagonal u v i) := by
    simpa only [star_mul,projection_P.isSelfAdjoint.star_eq]
      using congrArg star (offDiagonal_left u v i)
  have hxr : star (offDiagonal u v i)*edgeRange u v i=star (offDiagonal u v i) := by
    simpa only [star_mul,(edgeRange_projection u v i).isSelfAdjoint.star_eq]
      using congrArg star (edgeRange_mul_offDiagonal u v i)
  rw [add_mul,hx,zero_add,edgeDefect,mul_sub,hxp,hxr,sub_self]

theorem edge_algebra_scalar_on_defect (u v : ℝ) (i : ι) (T : edgeAlgebra u v i) :
    ∃ c : ℂ,(T : Operator ι)*edgeDefect u v i=c • edgeDefect u v i :=
  BicommutantAtom.common_kernel_scalar P (offDiagonal u v i+star (offDiagonal u v i))
    (edgeDefect u v i) T projection_P.isSelfAdjoint
    (by show star (_+_)=_;simp only [star_add,star_star,add_comm])
    (P_mul_edgeDefect u v i) (edgeSum_mul_defect u v i) T.property

theorem edgeDefect_trace (u v : ℝ) (hv : 0<v) (hvu : v<u) (i : ι) :
    vacuumTrace u v (edgeDefect u v i)=((u^2-v^2 : ℝ):ℂ) := by
  unfold edgeDefect vacuumTrace
  rw [sub_apply,inner_sub_right]
  change vacuumTrace u v P-vacuumTrace u v (edgeRange u v i)=_
  rw [vacuumTrace_P,edgePolar_trace u v hv hvu]
  push_cast
  rfl

end FreeGroupFactorMain.WeightedFock
namespace FreeGroupFactorMain.JacobiNonatom
open Filter Topology

 theorem semicircular_eigenvector_zero (a z : ℂ) (ha : a≠0)
    (x : ℕ → ℂ) (hx : Tendsto x atTop (𝓝 0))
    (hfirst : a*x 1=z*x 0)
    (hstep : ∀ n,a*x (n+2)=z*x (n+1)-a*x n) : ∀ n,x n=0 := by
  have hi := invariant_zero a z ha x hstep hx
  have hb : a*invariant a z x 0=a^2*(x 0)^2 := by
    calc
      _ = a^2*(x 0)^2+(a*x 1)^2-z*x 0*(a*x 1) := by simp only [invariant];ring
      _ = _ := by rw [hfirst];ring
  rw [hi,mul_zero] at hb
  have h0 : x 0=0 := by
    exact sq_eq_zero_iff.mp ((mul_eq_zero.mp hb.symm).resolve_left (pow_ne_zero 2 ha))
  have h1 : x 1=0 := by
    rw [h0,mul_zero] at hfirst
    exact (mul_eq_zero.mp hfirst).resolve_left ha
  intro n
  induction n using Nat.twoStepInduction with
  | zero => exact h0
  | one => exact h1
  | more n hn hn1 =>
    have h := hstep n
    rw [hn,hn1,mul_zero,mul_zero,sub_self] at h
    exact (mul_eq_zero.mp h).resolve_left ha

end FreeGroupFactorMain.JacobiNonatom
namespace FreeGroupFactorMain.IsometricSemicircle
open Filter Topology
variable {E : Type u_3} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (L : E →L[ℂ] E) (hL : star L*L=1) (ξ : E) (hξ : inner ℂ ξ ξ=1)
  (hroot : star L ξ=0)

def chain (n : ℕ) : E := (L^n) ξ

omit [CompleteSpace E] in
theorem chain_zero : chain L ξ 0=ξ := by simp [chain]
omit [CompleteSpace E] in
theorem chain_succ (n : ℕ) : chain L ξ (n+1)=L (chain L ξ n) := by
  simp only [chain,pow_succ',mul_apply_eq_comp]

include hL in
theorem inner_map (x y : E) : inner ℂ (L x) (L y)=inner ℂ x y := by
  apply (ContinuousLinearMap.inner_map_map_iff_adjoint_comp_self L).mpr
  exact hL

include hroot in
theorem inner_root_succ (n : ℕ) : inner ℂ ξ (chain L ξ (n+1))=0 := by
  rw [chain_succ,← ContinuousLinearMap.adjoint_inner_left]
  change inner ℂ (star L ξ) (chain L ξ n)=0
  rw [hroot,inner_zero_left]

include hL hξ hroot in
theorem chain_inner (n m : ℕ) : inner ℂ (chain L ξ n) (chain L ξ m)=if n=m then 1 else 0 := by
  induction n generalizing m with
  | zero =>
    cases m with
    | zero => simpa only [chain_zero,ite_true] using hξ
    | succ m => simpa only [chain_zero,Nat.succ_ne_zero,Nat.zero_ne_add_one,ite_false]
        using inner_root_succ L ξ hroot m
  | succ n ih =>
    cases m with
    | zero =>
      rw [chain_zero,← inner_conj_symm,inner_root_succ L ξ hroot]
      simp
    | succ m =>
      rw [chain_succ,chain_succ,inner_map L hL,ih]
      simp

include hL hξ hroot in
theorem chain_orthonormal : Orthonormal ℂ (chain L ξ) :=
  orthonormal_iff_ite.mpr (chain_inner L hL ξ hξ hroot)

include hL hξ hroot in
theorem chain_coeff_decay (η : E) : Tendsto (fun n => inner ℂ (chain L ξ n) η) atTop (𝓝 0) := by
  have h := ((chain_orthonormal L hL ξ hξ hroot).inner_products_summable η).tendsto_atTop_zero
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp h
  have hn : Tendsto (fun n => ‖inner ℂ (chain L ξ n) η‖) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] using hs
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hn

include hL in
theorem adjoint_chain_succ (n : ℕ) : star L (chain L ξ (n+1))=chain L ξ n := by
  rw [chain_succ]
  change (star L*L) (chain L ξ n)=_
  rw [hL,one_apply_eq_self]

include hroot in
theorem sum_chain_zero : (L+star L) (chain L ξ 0)=chain L ξ 1 := by
  rw [chain_zero,add_apply,hroot,add_zero,chain_succ,chain_zero]

include hL in
theorem sum_chain_succ (n : ℕ) :
    (L+star L) (chain L ξ (n+1))=chain L ξ (n+2)+chain L ξ n := by
  rw [add_apply,adjoint_chain_succ L hL]
  exact congrArg (fun x => x+chain L ξ n) (chain_succ L ξ (n+1)).symm

include hL hξ hroot in

theorem eigen_root_zero (z : ℂ) (η : E) (he : (L+star L) η=z • η) : inner ℂ ξ η=0 := by
  have hself : star (L+star L)=L+star L := by simp [add_comm]
  have h (n : ℕ) : inner ℂ ((L+star L) (chain L ξ n)) η=
      z*inner ℂ (chain L ξ n) η := by
    rw [← ContinuousLinearMap.adjoint_inner_right]
    change inner ℂ (chain L ξ n) (star (L+star L) η)=_
    rw [hself,he,inner_smul_right]
  have hb : (1:ℂ)*inner ℂ (chain L ξ 1) η=z*inner ℂ (chain L ξ 0) η := by
    rw [one_mul]
    simpa only [sum_chain_zero L ξ hroot] using h 0
  have ht (n : ℕ) : (1:ℂ)*inner ℂ (chain L ξ (n+2)) η=
      z*inner ℂ (chain L ξ (n+1)) η-(1:ℂ)*inner ℂ (chain L ξ n) η := by
    have hn := h (n+1)
    rw [sum_chain_succ L hL,inner_add_left] at hn
    linear_combination hn
  simpa only [chain_zero] using JacobiNonatom.semicircular_eigenvector_zero 1 z one_ne_zero
    (fun n => inner ℂ (chain L ξ n) η) (chain_coeff_decay L hL ξ hξ hroot η) hb ht 0

end FreeGroupFactorMain.IsometricSemicircle
namespace FreeGroupFactorMain.SupportedSemicircle
variable {E : Type u_4} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (d L : (E →L[ℂ] E)) (hd : IsStarProjection d) (hleft : d*L=L) (hright : L*d=L)
  (hL : star L*L=d)

def extension : (E →L[ℂ] E) := L+(1-d)

include hd hleft hL in
theorem extension_isometry : star (extension d L)*extension d L=1 := by
  have hsright : star L*d=star L := by
    simpa only [star_mul,hd.isSelfAdjoint.star_eq] using congrArg star hleft
  have hqL : (1-d)*L=0 := by rw [sub_mul,one_mul,hleft,sub_self]
  have hLq : star L*(1-d)=0 := by rw [mul_sub,mul_one,hsright,sub_self]
  rw [extension,star_add,hd.one_sub.isSelfAdjoint.star_eq,add_mul,mul_add,mul_add,
    hL,hLq,hqL,hd.one_sub.isIdempotentElem.eq,add_zero,zero_add,add_sub_cancel]

include hd hleft hright in
theorem supported_sum_left : d*(L+star L)=L+star L := by
  have hs : d*star L=star L := by
    simpa only [star_mul,hd.isSelfAdjoint.star_eq] using congrArg star hright
  rw [mul_add,hleft,hs]

include hd hleft hright in
theorem supported_sum_right : (L+star L)*d=L+star L := by
  have hs : star L*d=star L := by
    simpa only [star_mul,hd.isSelfAdjoint.star_eq] using congrArg star hleft
  rw [add_mul,hright,hs]

include hd hleft hright hL in

theorem eigen_root_zero (ξ : E) (hξ : inner ℂ ξ ξ=1) (hdξ : d ξ=ξ)
    (hroot : star L ξ=0) (z : ℂ) (η : E) (he : (L+star L) η=z • η) :
    inner ℂ ξ η=0 := by
  have hqξ : (1-d : (E →L[ℂ] E)) ξ=0 := by rw [sub_apply,one_apply_eq_self,hdξ,sub_self]
  have hroot' : star (extension d L) ξ=0 := by
    rw [extension,star_add,hd.one_sub.isSelfAdjoint.star_eq,add_apply,hroot,hqξ,add_zero]
  have hqη : (1-d : (E →L[ℂ] E)) (d η)=0 := by
    change ((1-d)*d) η=0
    rw [sub_mul,one_mul,hd.isIdempotentElem.eq,sub_self,zero_apply]
  have he' : (extension d L+star (extension d L)) (d η)=z • d η := by
    have hs : (L+star L) (d η)=z • d η := by
      calc
        _ = (L+star L) η := DFunLike.congr_fun (supported_sum_right d L hd hleft hright) η
        _ = d ((L+star L) η) := (DFunLike.congr_fun (supported_sum_left d L hd hleft hright) η).symm
        _ = _ := by rw [he,map_smul]
    simp only [extension,star_add,hd.one_sub.isSelfAdjoint.star_eq,add_apply,hqη,add_zero] at ⊢
    exact hs
  have hz := IsometricSemicircle.eigen_root_zero (extension d L)
    (extension_isometry d L hd hleft hL) ξ hξ hroot' z (d η) he'
  rw [← ContinuousLinearMap.adjoint_inner_left] at hz
  change inner ℂ (star d ξ) η=0 at hz
  rwa [hd.isSelfAdjoint.star_eq,hdξ] at hz

end FreeGroupFactorMain.SupportedSemicircle
namespace FreeGroupFactorMain.WeightedFock
open FreeFock
variable {ι : Type u_5} [DecidableEq ι]

theorem vacuumTrace_supported_root (u v : ℝ) (T : Operator ι)
    (hl : P*T=T) (hr : T*P=T) :
    vacuumTrace u v T=(u:ℂ)^2*(T (lp.single 2 ([],true) 1)) ([],true) := by
  have hnil : T (lp.single 2 ([],false) 1)=0 := by
    rw [← hr,mul_apply_eq_comp,P_nil_false,map_zero]
  have hcoord : (T (lp.single 2 ([],true) 1)) ([],false)=0 := by
    have hh := DFunLike.congr_fun hl (lp.single 2 ([],true) 1)
    have hc := congrArg (fun ξ : H ι => ξ ([],false)) hh
    simpa only [mul_apply_eq_comp,P,CoordinateProjection.proj_apply,
      Set.indicator_of_notMem (by simp [start] : ([], false) ∉ {w : Path ι | start w = true})] using hc.symm
  rw [vacuumTrace_root_expansion,hnil,hcoord]
  simp only [lp.coeFn_zero,Pi.zero_apply,mul_zero,add_zero,pow_two]

def defectCreation (u v : ℝ) (i j : ι) : Operator ι :=
  edgeDefect u v i*edgeCreation j true true*edgeDefect u v i

theorem defectCreation_left (u v : ℝ) (i j : ι) :
    edgeDefect u v i*defectCreation u v i j=defectCreation u v i j := by
  rw [defectCreation,← mul_assoc,← mul_assoc,(edgeDefect_projection u v i).isIdempotentElem.eq]

theorem defectCreation_right (u v : ℝ) (i j : ι) :
    defectCreation u v i j*edgeDefect u v i=defectCreation u v i j := by
  rw [defectCreation,mul_assoc,(edgeDefect_projection u v i).isIdempotentElem.eq]

theorem defectCreation_covariance (u v : ℝ) (i j : ι) :
    star (defectCreation u v i j)*defectCreation u v i j=
      ((edgeDefect u v i (lp.single 2 ([],true) 1)) ([],true)) • edgeDefect u v i := by
  let d := edgeDefect u v i
  have hid : d*d=d := (edgeDefect_projection u v i).isIdempotentElem.eq
  have hstar : star d=d := (edgeDefect_projection u v i).isSelfAdjoint.star_eq
  have hcov := diagonal_edge_contraction u v i j j
    ⟨d,edgeDefect_mem_edge u v i⟩ true true
  simp only [true_and,ite_true,vertex] at hcov
  change star (edgeCreation j true true)*d*edgeCreation j true true=_ at hcov
  change star (d*edgeCreation j true true*d)*(d*edgeCreation j true true*d)=_
  calc
    _ = d*(star (edgeCreation j true true)*d*edgeCreation j true true)*d := by
      simp only [star_mul,hstar,mul_assoc,← mul_assoc d d,hid]
    _ = _ := by
      rw [hcov,mul_smul_comm,smul_mul_assoc]
      change _ • (edgeDefect u v i*P*edgeDefect u v i)=_
      rw [edgeDefect_mul_P,hid]

theorem defectCreation_root (u v : ℝ) (i j : ι) :
    star (defectCreation u v i j) (edgeDefect u v i (lp.single 2 ([],true) 1))=0 := by
  have hroot := diagonal_annihilation_edge_root u v i j
    (⟨edgeDefect u v i,edgeDefect_mem_edge u v i⟩ : edgeAlgebra u v i) true true
  change star (edgeCreation j true true) (edgeDefect u v i (lp.single 2 ([], true) 1))=0 at hroot
  rw [defectCreation,star_mul,star_mul,(edgeDefect_projection u v i).isSelfAdjoint.star_eq,
    mul_apply_eq_comp,mul_apply_eq_comp]
  have hd : edgeDefect u v i (edgeDefect u v i (lp.single 2 ([],true) 1))=
      edgeDefect u v i (lp.single 2 ([],true) 1) :=
    DFunLike.congr_fun (edgeDefect_projection u v i).isIdempotentElem.eq _
  rw [hd,hroot,map_zero]

end FreeGroupFactorMain.WeightedFock
namespace FreeGroupFactorMain.SupportedSemicircle
variable {E : Type u_6} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem unnormalized_eigen_root_zero (d L : E →L[ℂ] E) (hd : IsStarProjection d)
    (hleft : d*L=L) (hright : L*d=L) (ξ : E) (hξ : ξ≠0) (hdξ : d ξ=ξ)
    (hL : star L*L=inner ℂ ξ ξ • d) (hroot : star L ξ=0)
    (z : ℂ) (η : E) (he : (L+star L) η=z • η) : inner ℂ ξ η=0 := by
  let c : ℂ := (‖ξ‖:ℂ)⁻¹
  have hn : (‖ξ‖:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hξ)
  have hc : c≠0 := inv_ne_zero hn
  have hsc : star c=c := by simp only [c,star_inv₀,Complex.star_def,Complex.conj_ofReal]
  have hu : c*c*inner ℂ ξ ξ=1 := by
    rw [inner_self_eq_norm_sq_to_K]
    dsimp [c]
    field_simp
  have hnorm : inner ℂ (c • ξ) (c • ξ)=1 := by
    rw [inner_smul_left,inner_smul_right]
    change star c*(c*inner ℂ ξ ξ)=1
    rw [hsc,← mul_assoc,hu]
  have hcov : star (c • L)*(c • L)=d := by
    rw [star_smul,hsc,smul_mul_assoc,mul_smul_comm,hL,smul_smul,smul_smul]
    rw [hu,one_smul]
  have hl : d*(c • L)=c • L := by rw [mul_smul_comm,hleft]
  have hr : (c • L)*d=c • L := by rw [smul_mul_assoc,hright]
  have hdv : d (c • ξ)=c • ξ := by rw [map_smul,hdξ]
  have hov : star (c • L) (c • ξ)=0 := by
    rw [star_smul,hsc,_root_.smul_apply,map_smul,hroot,smul_zero,smul_zero]
  have hev : ((c • L)+star (c • L)) η=(c*z) • η := by
    rw [star_smul,hsc,← smul_add,_root_.smul_apply,he,smul_smul]
  have hh := eigen_root_zero d (c • L) hd hl hr hcov (c • ξ) hnorm hdv hov (c*z) η hev
  rw [inner_smul_left] at hh
  change star c*inner ℂ ξ η=0 at hh
  rw [hsc] at hh
  exact (mul_eq_zero.mp hh).resolve_left hc

end FreeGroupFactorMain.SupportedSemicircle
namespace FreeGroupFactorMain.WeightedFock
open FreeFock
variable {ι : Type u_7} [DecidableEq ι]

theorem edgeDefect_root_ne_zero (u v : ℝ) (hv : 0<v) (hvu : v<u) (i : ι) :
    edgeDefect u v i (lp.single 2 ([],true) 1)≠0 := by
  intro hzero
  have he := vacuumTrace_supported_root u v (edgeDefect u v i)
    (P_mul_edgeDefect u v i) (edgeDefect_mul_P u v i)
  rw [edgeDefect_trace u v hv hvu,hzero] at he
  simp only [lp.coeFn_zero,Pi.zero_apply,mul_zero,Complex.ofReal_eq_zero] at he
  nlinarith

theorem edgeDefect_root_inner (u v : ℝ) (i : ι) :
    inner ℂ (edgeDefect u v i (lp.single 2 ([],true) 1))
      (edgeDefect u v i (lp.single 2 ([],true) 1))=
        (edgeDefect u v i (lp.single 2 ([],true) 1)) ([],true) := by
  rw [← ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ (lp.single 2 ([],true) 1)
    ((star (edgeDefect u v i)*edgeDefect u v i) (lp.single 2 ([],true) 1))=_
  rw [(edgeDefect_projection u v i).isSelfAdjoint.star_eq,
    (edgeDefect_projection u v i).isIdempotentElem.eq]
  simp only [lp.inner_single_left,RCLike.inner_apply,map_one,mul_one]

theorem defectSemicircle_eigen_root_zero (u v : ℝ) (hv : 0<v) (hvu : v<u)
    (i j : ι) (z : ℂ) (η : H ι)
    (he : (defectCreation u v i j+star (defectCreation u v i j)) η=z • η) :
    inner ℂ (edgeDefect u v i (lp.single 2 ([],true) 1)) η=0 := by
  apply SupportedSemicircle.unnormalized_eigen_root_zero
    (edgeDefect u v i) (defectCreation u v i j) (edgeDefect_projection u v i)
    (defectCreation_left u v i j) (defectCreation_right u v i j)
    _ (edgeDefect_root_ne_zero u v hv hvu i) _ _ (defectCreation_root u v i j) z η he
  · exact DFunLike.congr_fun (edgeDefect_projection u v i).isIdempotentElem.eq _
  · rw [edgeDefect_root_inner]
    exact defectCreation_covariance u v i j

end FreeGroupFactorMain.WeightedFock

end

end OAI
end

section
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6

open Filter Topology
namespace FreeGroupFactorMain.OrthogonalSpectralSum
variable {E : Type u_1} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
abbrev Op := E →L[ℂ] E

theorem projection_inner (r : Op) (hr : IsStarProjection r) (ξ η : E) :
    inner ℂ (r ξ) (r η)=inner ℂ (r ξ) η := by
  calc
    _ = inner ℂ (r (r ξ)) η := by
      simpa only [← ContinuousLinearMap.star_eq_adjoint,hr.isSelfAdjoint.star_eq] using
        ContinuousLinearMap.adjoint_inner_right r (r ξ) η
    _ = _ := by rw [← mul_apply_eq_comp,hr.isIdempotentElem.eq]

theorem eigen_root_zero (r d f a : Op) (hr : IsStarProjection r) (hd : IsStarProjection d)
    (hrd : r*d=0) (hrf : r*f=f) (hfr : f*r=f) (hda : d*a=a) (had : a*d=a)
    (ξ : E)
    (hf : ∀ z : ℂ, ∀ η, f η=z • η → inner ℂ (r ξ) η=0)
    (ha : ∀ z : ℂ, ∀ η, a η=z • η → inner ℂ (d ξ) η=0)
    (κ z : ℂ) (η : E) (he : (f+a+κ • r) η=z • η) :
    inner ℂ ((r+d) ξ) η=0 := by
  have hdr : d*r=0 := by
    simpa only [star_mul,hr.isSelfAdjoint.star_eq,hd.isSelfAdjoint.star_eq,star_zero]
      using congrArg star hrd
  have hra : r*a=0 := by rw [← hda,← mul_assoc,hrd,zero_mul]
  have hdf : d*f=0 := by rw [← hrf,← mul_assoc,hdr,zero_mul]
  have hrB : r*(f+a+κ • r)=f+κ • r := by
    rw [mul_add,mul_add,hrf,hra,add_zero,mul_smul_comm,hr.isIdempotentElem.eq]
  have hdB : d*(f+a+κ • r)=a := by
    rw [mul_add,mul_add,hdf,hda,zero_add,mul_smul_comm,hdr,smul_zero,add_zero]
  have heR : f (r η)=(z-κ) • (r η) := by
    have hh : (f+κ • r) η=z • (r η) := by
      rw [← hrB,mul_apply_eq_comp,he,map_smul]
    change f η+κ • (r η)=z • (r η) at hh
    rw [← mul_apply_eq_comp,hfr,sub_smul]
    exact eq_sub_of_add_eq hh
  have heD : a (d η)=z • (d η) := by
    rw [← mul_apply_eq_comp,had,← hdB,mul_apply_eq_comp,he,map_smul]
  have hR := hf (z-κ) (r η) heR
  have hD := ha z (d η) heD
  rw [projection_inner r hr] at hR
  rw [projection_inner d hd] at hD
  rw [add_apply,inner_add_left,hR,hD,add_zero]

end FreeGroupFactorMain.OrthogonalSpectralSum
namespace FreeGroupFactorMain.SpectralSeparation
variable {A : Type u_2} [NormedRing A] [NormedAlgebra ℂ A] [StarRing A] [StarModule ℂ A]

omit [StarRing A] [StarModule ℂ A] in

theorem cross_zero {p f t : A} (hp : IsIdempotentElem p) (hpf : Commute p f)
    (κ : ℝ) (hκ : 2*‖f‖<κ) (ht : Commute (f+(κ:ℂ) • p) t) : p*t*(1-p)=0 := by
  let y := p*t*(1-p)
  have hpq : p*(1-p)=0 := by rw [mul_sub,mul_one,hp.eq,sub_self]
  have hfq : Commute f (1-p) := (Commute.one_right f).sub_right hpf.symm
  have hl : p*((f+(κ:ℂ) • p)*t)*(1-p)=f*y+(κ:ℂ) • y := by
    dsimp [y]
    simp only [add_mul,mul_add,smul_mul_assoc,mul_smul_comm,← mul_assoc,hp.eq,hpf.eq]

  have hr : p*(t*(f+(κ:ℂ) • p))*(1-p)=y*f := by
    dsimp [y]
    simp only [mul_add,add_mul,mul_smul_comm,smul_mul_assoc,mul_assoc,hpq,
      mul_zero,smul_zero,add_zero,hfq.eq]

  have he : f*y+(κ:ℂ) • y=y*f := by
    rw [← hl,ht.eq,hr]
  have he' : (κ:ℂ) • y=y*f-f*y :=
    eq_sub_iff_add_eq.mpr ((add_comm _ _).trans he)
  have hκ0 : 0<κ := (mul_nonneg (by norm_num : (0:ℝ)≤2) (norm_nonneg f)).trans_lt hκ
  have hb : κ*‖y‖≤(2*‖f‖)*‖y‖ := by
    calc
      κ*‖y‖ = ‖(κ:ℂ) • y‖ := by rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hκ0]
      _ = ‖y*f-f*y‖ := congrArg norm he'
      _ ≤ ‖y*f‖+‖f*y‖ := norm_sub_le _ _
      _ ≤ ‖y‖*‖f‖+‖f‖*‖y‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ = (2*‖f‖)*‖y‖ := by ring
  have hy : ‖y‖=0 := by nlinarith [norm_nonneg y]
  exact norm_eq_zero.mp hy

theorem separated_projection_mem {p f : A} (hp : IsStarProjection p)
    (hf : IsSelfAdjoint f) (hpf : Commute p f) (κ : ℝ) (hκ : 2*‖f‖<κ) :
    p ∈ StarSubalgebra.centralizer ℂ
      (StarSubalgebra.centralizer ℂ ({f+(κ:ℂ) • p} : Set A) : Set A) := by
  have hB : IsSelfAdjoint (f+(κ:ℂ) • p) := by
    show star (_+_)=_
    simp only [star_add,hf.star_eq,star_smul,hp.isSelfAdjoint.star_eq,
      Complex.star_def,Complex.conj_ofReal]
  have hc (t : A) (ht : t ∈ StarSubalgebra.centralizer ℂ ({f+(κ:ℂ) • p} : Set A)) :
      Commute p t := by
    have hb : Commute (f+(κ:ℂ) • p) t :=
      ((StarSubalgebra.mem_centralizer_iff ℂ).mp ht _ (Set.mem_singleton _)).1
    have hz := cross_zero hp.isIdempotentElem hpf κ hκ hb
    have hbs : Commute (f+(κ:ℂ) • p) (star t) := by
      simpa only [hB.star_eq] using hb.star_star
    have hzs := congrArg star (cross_zero hp.isIdempotentElem hpf κ hκ hbs)
    have hq : star (1-p)=1-p := hp.one_sub.isSelfAdjoint.star_eq
    simp only [star_mul,star_star,hq,hp.isSelfAdjoint.star_eq,star_zero] at hzs
    have h₁ : p*t=p*t*p := by
      simpa only [mul_sub,mul_one,sub_eq_zero] using hz
    have h₂ : t*p=p*t*p := by
      simpa only [← mul_assoc,sub_mul,one_mul,sub_eq_zero] using hzs
    exact h₁.trans h₂.symm
  rw [StarSubalgebra.mem_centralizer_iff]
  intro t ht
  exact ⟨(hc t ht).symm.eq,(hc (star t) (star_mem ht)).symm.eq⟩

end FreeGroupFactorMain.SpectralSeparation
namespace FreeGroupFactorMain.CornerRerouting
variable {A : Type u_3} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]

end FreeGroupFactorMain.CornerRerouting
namespace FreeGroupFactorMain.WeightedFock
open FreeFock
variable {ι : Type u_4} [DecidableEq ι]

theorem edgeRange_mul_P (u v : ℝ) (i : ι) : edgeRange u v i*P=edgeRange u v i := by
  simpa only [star_mul,projection_P.isSelfAdjoint.star_eq,
    (edgeRange_projection u v i).isSelfAdjoint.star_eq] using congrArg star (edgeRange_le_P u v i)

theorem edgeRange_mul_defect (u v : ℝ) (i : ι) : edgeRange u v i*edgeDefect u v i=0 := by
  rw [edgeDefect,mul_sub,edgeRange_mul_P,(edgeRange_projection u v i).isIdempotentElem.eq,sub_self]

theorem defect_mul_edgeRange (u v : ℝ) (i : ι) : edgeDefect u v i*edgeRange u v i=0 := by
  simpa only [star_mul,(edgeRange_projection u v i).isSelfAdjoint.star_eq,
    (edgeDefect_projection u v i).isSelfAdjoint.star_eq,star_zero (Operator ι)]
    using congrArg star (edgeRange_mul_defect u v i)

def defectSemicircle (u v : ℝ) (i j : ι) : Operator ι :=
  defectCreation u v i j+star (defectCreation u v i j)

theorem defectSemicircle_selfAdjoint (u v : ℝ) (i j : ι) :
    IsSelfAdjoint (defectSemicircle u v i j) :=
  IsSelfAdjoint.add_star_self (defectCreation u v i j)

theorem defectSemicircle_left (u v : ℝ) (i j : ι) :
    edgeDefect u v i*defectSemicircle u v i j=defectSemicircle u v i j := by
  have hh := congrArg star (defectCreation_right u v i j)
  simp only [star_mul,(edgeDefect_projection u v i).isSelfAdjoint.star_eq] at hh
  rw [defectSemicircle,mul_add,defectCreation_left,hh]

theorem defectSemicircle_right (u v : ℝ) (i j : ι) :
    defectSemicircle u v i j*edgeDefect u v i=defectSemicircle u v i j := by
  simpa only [star_mul,(edgeDefect_projection u v i).isSelfAdjoint.star_eq,
    (defectSemicircle_selfAdjoint u v i j).star_eq]
    using congrArg star (defectSemicircle_left u v i j)

theorem P_mul_leftModulus (u v : ℝ) (i : ι) : P*leftModulus u v i=leftModulus u v i := by
  rw [leftModulus,← mul_assoc,offDiagonal_left]

theorem P_mul_defectSemicircle (u v : ℝ) (i j : ι) :
    P*defectSemicircle u v i j=defectSemicircle u v i j := by
  rw [← defectSemicircle_left u v i j,← mul_assoc,P_mul_edgeDefect]

def oldBaseShift (u v : ℝ) (i j : ι) : ℝ :=
  2*‖leftModulus u v i+defectSemicircle u v i j‖+1

def oldBaseGenerator (u v : ℝ) (i j : ι) : Operator ι :=
  leftModulus u v i+defectSemicircle u v i j+(oldBaseShift u v i j:ℂ) • edgeRange u v i

theorem oldBaseGenerator_selfAdjoint (u v : ℝ) (i j : ι) :
    IsSelfAdjoint (oldBaseGenerator u v i j) := by
  change star (_+_)=_+_
  simp only [star_add (R := Operator ι),star_smul,(leftModulus_selfAdjoint u v i).star_eq,
    (defectSemicircle_selfAdjoint u v i j).star_eq,(edgeRange_projection u v i).isSelfAdjoint.star_eq,
    Complex.star_def,Complex.conj_ofReal]

theorem oldBaseGenerator_left (u v : ℝ) (i j : ι) :
    P*oldBaseGenerator u v i j=oldBaseGenerator u v i j := by
  rw [oldBaseGenerator,mul_add,mul_add,P_mul_leftModulus,P_mul_defectSemicircle,
    mul_smul_comm,edgeRange_le_P]

theorem oldBaseGenerator_right (u v : ℝ) (i j : ι) :
    oldBaseGenerator u v i j*P=oldBaseGenerator u v i j := by
  simpa only [star_mul,projection_P.isSelfAdjoint.star_eq,(oldBaseGenerator_selfAdjoint u v i j).star_eq]
    using congrArg star (oldBaseGenerator_left u v i j)

theorem oldBaseGenerator_eigen_root_zero (u v : ℝ) (hv : 0<v) (hvu : v<u)
    (i j : ι) (z : ℂ) (η : H ι) (he : oldBaseGenerator u v i j η=z • η) :
    η ([],true)=0 := by
  have hh := OrthogonalSpectralSum.eigen_root_zero
    (edgeRange u v i) (edgeDefect u v i) (leftModulus u v i) (defectSemicircle u v i j)
    (edgeRange_projection u v i) (edgeDefect_projection u v i) (edgeRange_mul_defect u v i)
    (range_mul_leftModulus u v hv.le hvu i) (leftModulus_mul_range u v hv.le hvu i)
    (defectSemicircle_left u v i j) (defectSemicircle_right u v i j)
    (lp.single 2 ([],true) 1) (leftModulus_eigen_root_zero u v hv hvu i)
    (defectSemicircle_eigen_root_zero u v hv hvu i j) (oldBaseShift u v i j) z η he
  have hp : edgeRange u v i+edgeDefect u v i=P := by rw [edgeDefect];abel
  rw [hp,P_nil_true] at hh
  simpa only [lp.inner_single_left,RCLike.inner_apply,map_one,mul_one] using hh

end FreeGroupFactorMain.WeightedFock
namespace FreeGroupFactorMain.Bicommutant
variable {A : Type u_5} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
def algebra (S : Set A) := StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ S : Set A)

theorem subset (S : Set A) : S ⊆ algebra S :=
  fun _ h => StarAlgebra.adjoin_le_centralizer_centralizer ℂ S (StarAlgebra.subset_adjoin ℂ S h)

theorem mono (S T : Set A) (h : S ⊆ T) : algebra S ≤ algebra T :=
  StarSubalgebra.centralizer_le ℂ _ _ (StarSubalgebra.centralizer_le ℂ _ _ h)

theorem generated_le (S T : Set A) (h : T ⊆ algebra S) : algebra T ≤ algebra S := by
  apply StarSubalgebra.centralizer_le
  intro t ht
  change t ∈ StarSubalgebra.centralizer ℂ T
  rw [StarSubalgebra.mem_centralizer_iff]
  intro x hx
  exact ⟨((StarSubalgebra.mem_centralizer_iff ℂ).mp (h hx) t ht).1.symm,
    ((StarSubalgebra.mem_centralizer_iff ℂ).mp (star_mem (h hx)) t ht).1.symm⟩
end FreeGroupFactorMain.Bicommutant

namespace FreeGroupFactorMain.WeightedFock
open FreeFock
variable {ι : Type u_6} [DecidableEq ι]

def diffuseBase (u v : ℝ) (i j : ι) : StarSubalgebra ℂ (Operator ι) :=
  Bicommutant.algebra (insert P {oldBaseGenerator u v i j})

theorem oldBaseGenerator_mem_diffuseBase (u v : ℝ) (i j : ι) :
    oldBaseGenerator u v i j∈diffuseBase u v i j :=
  Bicommutant.subset _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))

end FreeGroupFactorMain.WeightedFock

end

end OAI
end

section
namespace OAI

universe u_1 u_2 u_3 u_4 u_5

noncomputable section
namespace FreeGroupFactorMain
variable {E : Type u_1} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def algebraCyclic (A : StarSubalgebra ℂ (E →L[ℂ] E)) (ξ : E) : Submodule ℂ E where
  carrier := {η | ∃ T ∈ A, T ξ=η}
  zero_mem' := ⟨0,A.zero_mem,rfl⟩
  add_mem' := by
    rintro x y ⟨S,hS,rfl⟩ ⟨T,hT,rfl⟩
    exact ⟨S+T,A.add_mem hS hT,rfl⟩
  smul_mem' := by
    rintro c x ⟨T,hT,rfl⟩
    exact ⟨c • T,A.smul_mem hT c,rfl⟩

 theorem algebraCyclic_invariant (A : StarSubalgebra ℂ (E →L[ℂ] E)) (ξ : E)
    (T : E →L[ℂ] E) (hT : T ∈ A) {η : E} (hη : η ∈ algebraCyclic A ξ) :
    T η ∈ algebraCyclic A ξ := by
  obtain ⟨S,hS,rfl⟩ := hη
  exact ⟨T*S,A.mul_mem hT hS,rfl⟩

 theorem algebraCyclic_closure_invariant (A : StarSubalgebra ℂ (E →L[ℂ] E)) (ξ : E)
    (T : E →L[ℂ] E) (hT : T ∈ A) {η : E} (hη : η ∈ (algebraCyclic A ξ).topologicalClosure) :
    T η ∈ (algebraCyclic A ξ).topologicalClosure := by
  exact closure_minimal (t := {x : E | T x ∈ (algebraCyclic A ξ).topologicalClosure})
    (fun x hx => (algebraCyclic A ξ).le_topologicalClosure (algebraCyclic_invariant A ξ T hT hx))
    ((algebraCyclic A ξ).isClosed_topologicalClosure.preimage T.continuous) hη

 theorem projection_commutes_of_invariant (K : Submodule ℂ E) [K.HasOrthogonalProjection]
    (T : E →L[ℂ] E) (hT : ∀ η ∈ K, T η ∈ K)
    (hTs : ∀ η ∈ K, (star T) η ∈ K) : Commute K.starProjection T := by
  apply ContinuousLinearMap.ext
  intro η
  change K.starProjection (T η)=T (K.starProjection η)
  apply K.eq_starProjection_of_mem_of_inner_eq_zero (hT _ (K.starProjection_apply_mem η))
  intro z hz
  rw [← map_sub,← ContinuousLinearMap.adjoint_inner_right]
  exact K.starProjection_inner_eq_zero η _ (hTs _ hz)

 theorem bicommutant_vector_mem_cyclic (S : Set (E →L[ℂ] E)) (ξ : E)
    (T : E →L[ℂ] E)
    (hT : T ∈ StarSubalgebra.centralizer ℂ
      (StarSubalgebra.centralizer ℂ S : Set (E →L[ℂ] E))) :
    T ξ ∈ (algebraCyclic (StarAlgebra.adjoin ℂ S) ξ).topologicalClosure := by
  let A := StarAlgebra.adjoin ℂ S
  let K := (algebraCyclic A ξ).topologicalClosure
  have hP : K.starProjection ∈ StarSubalgebra.centralizer ℂ S := by
    rw [StarSubalgebra.mem_centralizer_iff]
    intro U hU
    have hUa : U ∈ A := StarAlgebra.subset_adjoin ℂ S hU
    have hc (V : E →L[ℂ] E) (hV : V ∈ A) : Commute K.starProjection V :=
      projection_commutes_of_invariant K V
        (fun _ h => algebraCyclic_closure_invariant A ξ V hV h)
        (fun _ h => algebraCyclic_closure_invariant A ξ (star V) (star_mem hV) h)
    exact ⟨(hc U hUa).eq.symm,(hc (star U) (star_mem hUa)).eq.symm⟩
  have hξ : ξ ∈ K := (algebraCyclic A ξ).le_topologicalClosure ⟨1,A.one_mem,rfl⟩
  have hc := DFunLike.congr_fun (((StarSubalgebra.mem_centralizer_iff ℂ).mp hT _ hP).1) ξ
  change K.starProjection (T ξ)=T (K.starProjection ξ) at hc
  rw [K.starProjection_eq_self_iff.mpr hξ] at hc
  exact K.starProjection_eq_self_iff.mp hc
end FreeGroupFactorMain
namespace FreeGroupFactorMain.PairCyclic

section
variable {E : Type u_2} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
local notation "Pair" => WithLp 2 (E × E)
local notation "Op" => (E →L[ℂ] E)

def diag (T : Op) : Pair →L[ℂ] Pair :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ E E).symm.toContinuousLinearMap ∘L
    T.prodMap T ∘L (WithLp.prodContinuousLinearEquiv 2 ℂ E E).toContinuousLinearMap

theorem diag_apply (T : Op) (x : Pair) : diag T x=WithLp.toLp 2 (T x.fst,T x.snd) := rfl

theorem diag_star [CompleteSpace E] (T : Op) : star (diag T)=diag (star T) := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  simp only [diag_apply,WithLp.prod_inner_apply,
    ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_left]
  rfl

def coord (i : Bool) : Pair →L[ℂ] E :=
  if i then WithLp.sndL 2 ℂ E E else WithLp.fstL 2 ℂ E E

def embed (i : Bool) : E →L[ℂ] Pair :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ E E).symm.toContinuousLinearMap ∘L
    (if i then ContinuousLinearMap.inr ℂ E E else ContinuousLinearMap.inl ℂ E E)

theorem coord_diag (i : Bool) (T : Op) (x : Pair) : coord i (diag T x)=T (coord i x) := by
  cases i <;> rfl

theorem diag_embed (i : Bool) (T : Op) (x : E) : diag T (embed i x)=embed i (T x) := by
  cases i <;> apply (WithLp.prodContinuousLinearEquiv 2 ℂ E E).injective <;>
    simp [diag,embed,ContinuousLinearMap.prodMap]

theorem pair_decompose (x : Pair) : x=embed false (coord false x)+embed true (coord true x) := by
  apply (WithLp.prodContinuousLinearEquiv 2 ℂ E E).injective
  simp [embed,coord]
  rfl

def block (Q : Pair →L[ℂ] Pair) (i j : Bool) : Op := coord i ∘L Q ∘L embed j

theorem block_commute {Q : Pair →L[ℂ] Pair} {T : Op} (h : Commute Q (diag T)) (i j : Bool) :
    Commute (block Q i j) T := by
  ext x
  have hh := congrArg (fun y : Pair => coord i y) (DFunLike.congr_fun h.eq (embed j x))
  simpa only [mul_apply_eq_comp,diag_embed,coord_diag,block,ContinuousLinearMap.comp_apply] using hh

theorem diag_commute_of_blocks {Q : Pair →L[ℂ] Pair} {T : Op}
    (h : ∀ i j, Commute (block Q i j) T) : Commute Q (diag T) := by
  ext x
  have hc (i : Bool) : coord i (Q (diag T x))=coord i (diag T (Q x)) := by
    have hh (j : Bool) := DFunLike.congr_fun (h i j).eq (coord j x)
    simp only [mul_apply_eq_comp,block,ContinuousLinearMap.comp_apply] at hh
    rw [coord_diag, pair_decompose x, map_add,map_add,map_add,map_add,diag_embed,diag_embed,
      hh false,hh true]
    simp only [map_add]
  apply (WithLp.prodContinuousLinearEquiv 2 ℂ E E).injective
  exact Prod.ext (hc false) (hc true)

variable [CompleteSpace E]

end
variable {E : Type u_3} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
local notation "Pair" => WithLp 2 (E × E)
local notation "Op" => (E →L[ℂ] E)

theorem invariant_bicommutant (S : Set Op) (K : Submodule ℂ Pair) [K.HasOrthogonalProjection]
    (hS : ∀ U∈S, ∀ y∈K, diag U y∈K)
    (hSs : ∀ U∈S, ∀ y∈K, diag (star U) y∈K)
    (T : Op) (hT : T∈StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ S : Set Op))
    (x : Pair) (hx : x∈K) : diag T x∈K := by
  have hc (U : Op) (hU : U∈S) : Commute K.starProjection (diag U) :=
    projection_commutes_of_invariant K (diag U) (hS U hU)
      (fun y hy => by rw [diag_star]; exact hSs U hU y hy)
  have hcs (U : Op) (hU : U∈S) : Commute K.starProjection (diag (star U)) := by
    have hs := (hc U hU).star_star
    simpa only [(isSelfAdjoint_starProjection K).star_eq,diag_star] using hs
  have hb (i j : Bool) : block K.starProjection i j∈StarSubalgebra.centralizer ℂ S := by
    rw [StarSubalgebra.mem_centralizer_iff]
    intro U hU
    exact ⟨(block_commute (hc U hU) i j).symm.eq,(block_commute (hcs U hU) i j).symm.eq⟩
  have hcomm := diag_commute_of_blocks (fun i j =>
    (((StarSubalgebra.mem_centralizer_iff ℂ).mp hT _ (hb i j)).1))
  have he := DFunLike.congr_fun hcomm.eq x
  change K.starProjection (diag T x)=diag T (K.starProjection x) at he
  rw [K.starProjection_eq_self_iff.mpr hx] at he
  exact K.starProjection_eq_self_iff.mp he
end FreeGroupFactorMain.PairCyclic
namespace FreeGroupFactorMain.GaussianExtension

section
variable {E : Type u_4} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
local notation "Pair" => WithLp 2 (E × E)
variable (B : StarSubalgebra ℂ (E →L[ℂ] E)) (D : E →L[ℂ] E)

def creationWord (ξ : E) (a : B) (w : List B) : E :=
  (a : (E →L[ℂ] E)) (w.foldr (fun b y => D ((b : (E →L[ℂ] E)) y)) ξ)

def pairNormal (ξ η : E) (w : B × List B) : Pair :=
  WithLp.toLp 2 (creationWord B D ξ w.1 w.2,creationWord B D η w.1 w.2)

def creationWordSpan (ξ η : E) : Submodule ℂ Pair :=
  Submodule.span ℂ (Set.range (pairNormal B D ξ η))

theorem creationWord_coeff (ξ : E) (a b : B) (w : List B) :
    (a : (E →L[ℂ] E)) (creationWord B D ξ b w)=creationWord B D ξ (a*b) w := by
  cases w <;> rfl

theorem creationWord_create (ξ : E) (a : B) (w : List B) :
    D (creationWord B D ξ a w)=creationWord B D ξ 1 (a::w) := rfl

variable (κ : B → B) (hκ : ∀ a : B,star D*(a : (E →L[ℂ] E))*D=(κ a : (E →L[ℂ] E)))

theorem creationWord_annihilate_nil (ξ : E) (hξ : ∀ a : B,star D ((a : (E →L[ℂ] E)) ξ)=0) (a : B) :
    star D (creationWord B D ξ a [])=0 := hξ a

include hκ in
theorem creationWord_annihilate_cons (ξ : E) (a b : B) (w : List B) :
    star D (creationWord B D ξ a (b::w))=creationWord B D ξ (κ a*b) w := by
  have hh := DFunLike.congr_fun (hκ a) (creationWord B D ξ b w)
  exact hh

theorem pairNormal_coeff (ξ η : E) (a : B) (w : B × List B) :
    PairCyclic.diag (a : (E →L[ℂ] E)) (pairNormal B D ξ η w)=pairNormal B D ξ η (a*w.1,w.2) := by
  simp only [pairNormal,PairCyclic.diag_apply,WithLp.toLp_fst,WithLp.toLp_snd,creationWord_coeff]

theorem pairNormal_create (ξ η : E) (w : B × List B) :
    PairCyclic.diag D (pairNormal B D ξ η w)=pairNormal B D ξ η (1,w.1::w.2) := by
  simp only [pairNormal,PairCyclic.diag_apply,WithLp.toLp_fst,WithLp.toLp_snd,creationWord_create]

include hκ in
theorem pairNormal_semicircle_mem (ξ η : E)
    (hξ : ∀ a : B,star D ((a : (E →L[ℂ] E)) ξ)=0) (hη : ∀ a : B,star D ((a : (E →L[ℂ] E)) η)=0)
    (w : B × List B) : PairCyclic.diag (D+star D) (pairNormal B D ξ η w)∈creationWordSpan B D ξ η := by
  have hcreate : PairCyclic.diag D (pairNormal B D ξ η w)∈creationWordSpan B D ξ η := by
    rw [pairNormal_create]
    exact Submodule.subset_span (Set.mem_range_self _)
  have hann : PairCyclic.diag (star D) (pairNormal B D ξ η w)∈creationWordSpan B D ξ η := by
    rcases w with ⟨a,w⟩
    cases w with
    | nil =>
      have hz : PairCyclic.diag (star D) (pairNormal B D ξ η (a,[]))=0 := by
        simp only [pairNormal,PairCyclic.diag_apply,WithLp.toLp_fst,WithLp.toLp_snd,
          creationWord_annihilate_nil B D ξ hξ,creationWord_annihilate_nil B D η hη]
        rfl
      rw [hz]
      exact (creationWordSpan B D ξ η).zero_mem
    | cons b w =>
      have he : PairCyclic.diag (star D) (pairNormal B D ξ η (a,b::w))=
          pairNormal B D ξ η (κ a*b,w) := by
        simp only [pairNormal,PairCyclic.diag_apply,WithLp.toLp_fst,WithLp.toLp_snd,
          creationWord_annihilate_cons B D κ hκ]
      rw [he]
      exact Submodule.subset_span (Set.mem_range_self _)
  exact (creationWordSpan B D ξ η).add_mem hcreate hann

theorem span_invariant_of_family (ξ η : E) (T : (E →L[ℂ] E))
    (hT : ∀ w,PairCyclic.diag T (pairNormal B D ξ η w)∈creationWordSpan B D ξ η)
    (z : Pair) (hz : z∈creationWordSpan B D ξ η) : PairCyclic.diag T z∈creationWordSpan B D ξ η := by
  have hh : creationWordSpan B D ξ η≤(creationWordSpan B D ξ η).comap (PairCyclic.diag T).toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨w,rfl⟩
    exact hT w
  exact hh hz

theorem closure_invariant_of_family (ξ η : E) (T : (E →L[ℂ] E))
    (hT : ∀ w,PairCyclic.diag T (pairNormal B D ξ η w)∈creationWordSpan B D ξ η)
    (z : Pair) (hz : z∈(creationWordSpan B D ξ η).topologicalClosure) :
    PairCyclic.diag T z∈(creationWordSpan B D ξ η).topologicalClosure := by
  exact closure_minimal (t := {z : Pair | PairCyclic.diag T z∈(creationWordSpan B D ξ η).topologicalClosure})
    (fun z hz => (creationWordSpan B D ξ η).le_topologicalClosure (span_invariant_of_family B D ξ η T hT z hz))
    ((creationWordSpan B D ξ η).isClosed_topologicalClosure.preimage (PairCyclic.diag T).continuous) hz

include hκ in
theorem bicommutant_pair_creationWord (ξ η : E)
    (hξ : ∀ a : B,star D ((a : (E →L[ℂ] E)) ξ)=0) (hη : ∀ a : B,star D ((a : (E →L[ℂ] E)) η)=0)
    (T : (E →L[ℂ] E))
    (hT : T∈StarSubalgebra.centralizer ℂ
      (StarSubalgebra.centralizer ℂ (insert (D+star D) (B : Set (E →L[ℂ] E))) : Set (E →L[ℂ] E))) :
    PairCyclic.diag T (WithLp.toLp 2 (ξ,η))∈(creationWordSpan B D ξ η).topologicalClosure := by
  have hS (U : (E →L[ℂ] E)) (hU : U∈insert (D+star D) (B : Set (E →L[ℂ] E))) :
      ∀ z∈(creationWordSpan B D ξ η).topologicalClosure,
      PairCyclic.diag U z∈(creationWordSpan B D ξ η).topologicalClosure := by
    apply closure_invariant_of_family B D ξ η U
    intro w
    rcases hU with rfl|hU
    · exact pairNormal_semicircle_mem B D κ hκ ξ η hξ hη w
    · rw [pairNormal_coeff B D ξ η ⟨U,hU⟩]
      exact Submodule.subset_span (Set.mem_range_self _)
  have hSs (U : (E →L[ℂ] E)) (hU : U∈insert (D+star D) (B : Set (E →L[ℂ] E))) :
      star U∈insert (D+star D) (B : Set (E →L[ℂ] E)) := by
    rcases hU with rfl|hU
    · rw [(IsSelfAdjoint.add_star_self D).star_eq]
      exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ (star_mem hU)
  apply PairCyclic.invariant_bicommutant _ (creationWordSpan B D ξ η).topologicalClosure hS
    (fun U hU => hS (star U) (hSs U hU)) T hT
  apply (creationWordSpan B D ξ η).le_topologicalClosure
  exact Submodule.subset_span ⟨(1,[]),rfl⟩

def constraint (ξ : E) (L : (E →L[ℂ] E)) (z : E) : Pair →L[ℂ] E :=
  (star L) ∘L WithLp.fstL 2 ℂ E E-
    (ContinuousLinearMap.toSpanSingleton ℂ z) ∘L (innerSL ℂ ξ) ∘L WithLp.sndL 2 ℂ E E

include hκ in

theorem covariance_extension (L R Q : (E →L[ℂ] E)) (ξ ζ : E)
    (hξ : ∀ a : B,star D ((a : (E →L[ℂ] E)) ξ)=0)
    (hζ : ∀ a : B,star D ((a : (E →L[ℂ] E)) ζ)=0)
    (hL : ∀ a : B,star L*(a : (E →L[ℂ] E))*D=0)
    (hR : ∀ a : B,star D*(a : (E →L[ℂ] E))*R=0)
    (hbase : ∀ a : B,star L*(a : (E →L[ℂ] E))*R=(inner ℂ ξ ((a : (E →L[ℂ] E)) ζ)) • Q)
    (T : (E →L[ℂ] E))
    (hT : T∈StarSubalgebra.centralizer ℂ
      (StarSubalgebra.centralizer ℂ (insert (D+star D) (B : Set (E →L[ℂ] E))) : Set (E →L[ℂ] E))) :
    star L*T*R=(inner ℂ ξ (T ζ)) • Q := by
  ext η
  let F := constraint ξ L (Q η)
  have hroot : ∀ a : B,star D ((a : (E →L[ℂ] E)) (R η))=0 := by
    intro a
    have hh := DFunLike.congr_fun (hR a) η
    exact hh
  have hfamily (w : B × List B) : F (pairNormal B D (R η) ζ w)=0 := by
    rcases w with ⟨a,w⟩
    cases w with
    | nil =>
      have hh := DFunLike.congr_fun (hbase a) η
      change star L ((a : (E →L[ℂ] E)) (R η))=(inner ℂ ξ ((a : (E →L[ℂ] E)) ζ)) • (Q η) at hh
      change star L ((a : (E →L[ℂ] E)) (R η))-(inner ℂ ξ ((a : (E →L[ℂ] E)) ζ)) • (Q η)=0
      exact sub_eq_zero.mpr hh
    | cons b w =>
      have hz : star L ((a : (E →L[ℂ] E)) (D (creationWord B D (R η) b w)))=0 :=
        DFunLike.congr_fun (hL a) _
      have hi : inner ℂ ξ ((a : (E →L[ℂ] E)) (D (creationWord B D ζ b w)))=0 := by
        rw [← ContinuousLinearMap.adjoint_inner_left,← ContinuousLinearMap.adjoint_inner_left]
        change inner ℂ (star D (((star a : B) : (E →L[ℂ] E)) ξ)) _=0
        rw [hξ (star a),inner_zero_left]
      change star L ((a : (E →L[ℂ] E)) (D (creationWord B D (R η) b w)))-
        (inner ℂ ξ ((a : (E →L[ℂ] E)) (D (creationWord B D ζ b w)))) • (Q η)=0
      rw [hz,hi,zero_smul,sub_self]
  have hspan : creationWordSpan B D (R η) ζ≤LinearMap.ker F.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨w,rfl⟩
    exact hfamily w
  have hclosure := (creationWordSpan B D (R η) ζ).topologicalClosure_minimal hspan
    F.isClosed_ker
  have hh := hclosure (bicommutant_pair_creationWord B D κ hκ (R η) ζ hroot hζ T hT)
  change star L (T (R η))-(inner ℂ ξ (T ζ)) • (Q η)=0 at hh
  exact sub_eq_zero.mp hh

end
variable {E : Type u_5} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (B : StarSubalgebra ℂ (E →L[ℂ] E)) (D : E →L[ℂ] E)
variable (κ : B → B) (hκ : ∀ a : B,star D*(a : E →L[ℂ] E)*D=(κ a : E →L[ℂ] E))
include hκ in

theorem annihilation_extension (L : E →L[ℂ] E) (ξ : E)
    (hDξ : ∀ a : B,star D ((a : E →L[ℂ] E) ξ)=0)
    (hLξ : ∀ a : B,star L ((a : E →L[ℂ] E) ξ)=0)
    (hLD : ∀ a : B,star L*(a : E →L[ℂ] E)*D=0)
    (T : E →L[ℂ] E)
    (hT : T∈StarSubalgebra.centralizer ℂ
      (StarSubalgebra.centralizer ℂ (insert (D+star D) (B : Set (E →L[ℂ] E))) : Set (E →L[ℂ] E))) :
    star L (T ξ)=0 := by
  let F := (star L) ∘L WithLp.fstL 2 ℂ E E
  have hspan : creationWordSpan B D ξ ξ≤LinearMap.ker F.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨a,w⟩,rfl⟩
    cases w with
    | nil => exact hLξ a
    | cons b w => exact DFunLike.congr_fun (hLD a) (creationWord B D ξ b w)
  have hclosure := (creationWordSpan B D ξ ξ).topologicalClosure_minimal hspan F.isClosed_ker
  exact hclosure (bicommutant_pair_creationWord B D κ hκ ξ ξ hDξ hDξ T hT)
end FreeGroupFactorMain.GaussianExtension

end

end OAI
end

section
namespace OAI

noncomputable section

universe u_1 u_2 u_3

namespace FreeGroupFactorMain.WeightedFock

section
open FreeFock
variable {ι : Type u_1} [DecidableEq ι]

theorem P_mem_old (u v : ℝ) (J : Set ι) : (P : Operator ι)∈oldAlgebra u v J :=
  Bicommutant.subset _ (Set.mem_insert _ _)

theorem S_mem_old (u v : ℝ) (J : Set ι) (i : ι) (hi : i∈J) : S u v i∈oldAlgebra u v J :=
  Bicommutant.subset _ (Set.mem_insert_of_mem _ ⟨i,hi,rfl⟩)

theorem offDiagonal_mem_old (u v : ℝ) (J : Set ι) (i : ι) (hi : i∈J) :
    offDiagonal u v i∈oldAlgebra u v J := by
  unfold offDiagonal
  exact mul_mem (mul_mem (P_mem_old u v J) (S_mem_old u v J i hi))
    (sub_mem (one_mem _) (P_mem_old u v J))

theorem edgeAlgebra_le_old (u v : ℝ) (J : Set ι) (i : ι) (hi : i∈J) :
    edgeAlgebra u v i≤oldAlgebra u v J := by
  apply Bicommutant.generated_le
  rintro T (rfl|hT)
  · exact P_mem_old u v J
  · have he : T=offDiagonal u v i+star (offDiagonal u v i) := hT
    rw [he]
    exact add_mem (offDiagonal_mem_old u v J i hi) (star_mem (offDiagonal_mem_old u v J i hi))

def weightedDefectCreation (u v : ℝ) (i j : ι) : Operator ι :=
  edgeDefect u v i*C u v j*edgeDefect u v i

def defectCovariance (u v : ℝ) (i : ι) (a : edgeAlgebra u v i) : edgeAlgebra u v i :=
  ⟨vacuumTrace u v (edgeDefect u v i*(a : Operator ι)*edgeDefect u v i) • edgeDefect u v i,
    (edgeAlgebra u v i).smul_mem (edgeDefect_mem_edge u v i) _⟩

theorem weightedDefect_contraction (u v : ℝ) (i j : ι) (hji : j≠i) (a : edgeAlgebra u v i) :
    star (weightedDefectCreation u v i j)*(a : Operator ι)*weightedDefectCreation u v i j=
      (defectCovariance u v i a : Operator ι) := by
  let d : edgeAlgebra u v i := ⟨edgeDefect u v i,edgeDefect_mem_edge u v i⟩
  let b : oldAlgebra u v {i} := ⟨(d*a*d : edgeAlgebra u v i),
    edgeAlgebra_le_old u v {i} i (Set.mem_singleton i) (d*a*d).property⟩
  have hc := fresh_C_contraction u v {i} j j hji hji b
  simp only [ite_true] at hc
  change star (C u v j)*(edgeDefect u v i*(a : Operator ι)*edgeDefect u v i)*C u v j=_ at hc
  calc
    _ = edgeDefect u v i*(star (C u v j)*(edgeDefect u v i*(a : Operator ι)*edgeDefect u v i)*
        C u v j)*edgeDefect u v i := by
      simp only [weightedDefectCreation,star_mul,(edgeDefect_projection u v i).isSelfAdjoint.star_eq]
      noncomm_ring
    _ = _ := by
      rw [hc,mul_smul_comm,smul_mul_assoc,mul_one,(edgeDefect_projection u v i).isIdempotentElem.eq]
      rfl

theorem weightedDefect_annihilates_edge (u v : ℝ) (i j : ι) (hji : j≠i) (a : edgeAlgebra u v i) :
    star (weightedDefectCreation u v i j) ((a : Operator ι) (vacuum u v))=0 := by
  let b : oldAlgebra u v {i} := ⟨edgeDefect u v i*(a : Operator ι),
    edgeAlgebra_le_old u v {i} i (Set.mem_singleton i)
      (mul_mem (edgeDefect_mem_edge u v i) a.property)⟩
  have hc := fresh_C_annihilates_old_vacuum u v {i} j hji b
  rw [weightedDefectCreation,star_mul,star_mul,(edgeDefect_projection u v i).isSelfAdjoint.star_eq]
  change edgeDefect u v i (star (C u v j) (edgeDefect u v i ((a : Operator ι) (vacuum u v))))=0
  rw [show star (C u v j) (edgeDefect u v i ((a : Operator ι) (vacuum u v)))=0 from hc,map_zero]

theorem fresh_C_weightedDefect (u v : ℝ) (i j n : ι) (hji : j≠i) (hni : n≠i) (hnj : n≠j)
    (a : edgeAlgebra u v i) : star (C u v n)*(a : Operator ι)*weightedDefectCreation u v i j=0 := by
  let b : oldAlgebra u v {i} := ⟨(a : Operator ι)*edgeDefect u v i,
    edgeAlgebra_le_old u v {i} i (Set.mem_singleton i)
      (mul_mem a.property (edgeDefect_mem_edge u v i))⟩
  have hc := fresh_C_contraction u v {i} n j hni hji b
  rw [ite_eq_right hnj] at hc
  change star (C u v n)*((a : Operator ι)*edgeDefect u v i)*C u v j=0 at hc
  rw [weightedDefectCreation]
  calc
    _ = (star (C u v n)*((a : Operator ι)*edgeDefect u v i)*C u v j)*edgeDefect u v i := by
      simp only [mul_assoc]
    _ = 0 := by rw [hc,zero_mul]

def filledEdgeAlgebra (u v : ℝ) (i j : ι) : StarSubalgebra ℂ (Operator ι) :=
  Bicommutant.algebra (insert (weightedDefectCreation u v i j+star (weightedDefectCreation u v i j))
    (edgeAlgebra u v i : Set (Operator ι)))

end
section
open FreeFock
variable {ι : Type u_2} [DecidableEq ι]

end

open FreeFock
variable {ι : Type u_3} [DecidableEq ι]

end FreeGroupFactorMain.WeightedFock

end

end OAI
end


