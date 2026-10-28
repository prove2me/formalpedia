-- Prove2me | Definitions.Def_OAIQ039C021
-- name    : OAIQ039C021
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T06:14:50.166111+00:00
-- url     : https://prove2.me/theorems/fe0c8af6-2d1b-46e4-8d3c-b71c67f43baa
-- title:
--   Definitions bundle OAIQ039C021 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 16 declarations of OpenAI's Lean: 2 definitions and 14 theorems. The definitions and types are `OAI.Kadison.TracialGNS.rightMul`, `OAI.Kadison.TracialGNS.rightMulPre`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Commutator, in whole or in part: `Commutator_KaplanskySelfAdjoint`, `Commutator_OperatorAmplification`, `Commutator_TracialDevelopment`.
--
--   **Imports.** It imports the bundles `OAIQ039C002` and `OAIQ039C003` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ039C032` and `OAIQ039C034`; the proofs of `OAI.Kadison.MatrixGNS.flatBalanced_commutator_dominates`, `OAI.Kadison.MatrixGNS.row_corner_commutator_bound` and `OAI.Kadison.WOTDistance.annihilator_bound`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Commutator at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ039C002
import Definitions.Def_OAIQ039C003

section
-- module Solutions.OAIQ039_CM.Commutator_OperatorAmplification
attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace

namespace Kadison.OperatorAmplification

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι : Type*) [Fintype ι] [DecidableEq ι]

lemma diagonal_single (T : H →L[ℂ] H) (i : ι) (x : H) :
    diagonal (H:=H) ι T (single ι i x)=single ι i (T x) := by
  ext j
  by_cases h : j=i <;> simp [h]

omit [CompleteSpace H] in
lemma sum_single (x : SumSpace (H:=H) ι) : ∑ i, single ι i (x i)=x := by
  ext j
  simp

omit [CompleteSpace H] in
lemma apply_eq_sum_entries (T : SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι)
    (x : SumSpace (H:=H) ι) (i : ι) : T x i=∑ j, entry ι T i j (x j) := by
  conv_lhs => rw [←sum_single ι x]
  simp

lemma entry_commutes (T : SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι)
    (a : H →L[ℂ] H) (h : diagonal (H:=H) ι a*T=T*diagonal (H:=H) ι a) (i j : ι) :
    a*entry ι T i j=entry ι T i j*a := by
  ext x
  have he := congrArg (fun R : SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι => R (single ι j x) i) h
  simpa only [mul_apply_eq_comp,diagonal_apply,diagonal_single,entry_apply] using he

lemma commutes_of_entries (T : SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι)
    (a : H →L[ℂ] H) (h : ∀ i j, a*entry ι T i j=entry ι T i j*a) :
    diagonal (H:=H) ι a*T=T*diagonal (H:=H) ι a := by
  ext x i
  change a (T x i)=T (diagonal (H:=H) ι a x) i
  rw [apply_eq_sum_entries ι T x,apply_eq_sum_entries ι T]
  simp only [map_sum,diagonal_apply]
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun R : H →L[ℂ] H => R (x j)) (h i j)

lemma diagonal_bicommutant (S : StarSubalgebra ℂ (H →L[ℂ] H))
    {T : H →L[ℂ] H} (hT : T ∈ Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H)))) :
    diagonal (H:=H) ι T ∈ Set.centralizer (Set.centralizer ((S.map (diagonal (H:=H) ι)) : Set (SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι))) := by
  intro R hR
  apply (commutes_of_entries ι R T ?_).symm
  intro i j
  apply (hT _ ?_).symm
  intro a ha
  exact entry_commutes ι R a (hR (diagonal (H:=H) ι a) ⟨a,ha,rfl⟩) i j

end Kadison.OperatorAmplification

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_KaplanskySelfAdjoint
attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace BigOperators

namespace Kadison.Kaplansky

open OperatorAmplification

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

attribute [local instance] OAI.Kadison.Kaplansky.kaplanskySelfAdjointRealInnerProductSpace
lemma symmetrize_selfAdjoint (a : H →L[ℂ] H) : IsSelfAdjoint (symmetrize a) := by
  simp [IsSelfAdjoint,symmetrize,star_smul,add_comm]

lemma symmetrize_mem (S : StarSubalgebra ℂ (H →L[ℂ] H)) {a : H →L[ℂ] H} (ha : a∈S) :
    symmetrize a∈S := by
  have h := S.smul_mem (S.add_mem ha (S.star_mem' ha)) ((1/2:ℝ):ℂ)
  simpa only [symmetrize, Complex.coe_smul] using h

lemma crossed_pairing (a : H →L[ℂ] H) (x z : H) :
    inner ℝ (pair z x) (diagonal (H:=H) (Fin 2) a (pair x z))=
      2*inner ℝ z (symmetrize a x) := by
  change (inner ℂ (pair z x) (diagonal (H:=H) (Fin 2) a (pair x z))).re =
    2 * (inner ℂ z (symmetrize a x)).re
  simp only [PiLp.inner_apply,Fin.sum_univ_two,diagonal_apply,pair_zero,pair_one,
    symmetrize,smul_apply,add_apply]
  rw [←Complex.coe_smul,inner_smul_right,inner_add_right]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
    Complex.add_re]
  rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]
  have hi := inner_re_symm (𝕜:=ℂ) (a z) x
  dsimp only [RCLike.re_eq_complex_re] at hi
  simpa only [smul_eq_mul] using (by linarith :
    (inner ℂ z (a x)).re + (inner ℂ x (a z)).re =
    2 * ((1/2:ℝ) * ((inner ℂ z (a x)).re + (inner ℂ (a z) x).re)))

lemma selfAdjoint_mem_orbit_closure (S : StarSubalgebra ℂ (H →L[ℂ] H))
    {T : H →L[ℂ] H} (hT : T∈Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))))
    (hsT : IsSelfAdjoint T) (x : H) :
    T x∈(selfAdjointOrbit S x).topologicalClosure := by
  rw [←Submodule.orthogonal_orthogonal_eq_closure]
  intro z hz
  let X := pair x z
  let Z := pair z x
  have horbit : ∀ b : H →L[ℂ] H, b∈S →
      inner ℝ Z (diagonal (H:=H) (Fin 2) b X)=0 := by
    intro b hb
    rw [crossed_pairing]
    have he := hz (symmetrize b x)
      ⟨symmetrize b,symmetrize_mem S hb,symmetrize_selfAdjoint b,rfl⟩
    rw [real_inner_comm] at he
    rw [he,mul_zero]
  have hcl := bicommutant_mem_cyclicSubspace (S.map (diagonal (H:=H) (Fin 2)))
    (diagonal_bicommutant (Fin 2) S hT) X
  change diagonal (H:=H) (Fin 2) T X∈closure
    (orbitSubmodule (S.map (diagonal (H:=H) (Fin 2))) X : Set (SumSpace (H:=H) (Fin 2))) at hcl
  have hzT : inner ℝ Z (diagonal (H:=H) (Fin 2) T X)=0 := by
    apply (closure_minimal ?_ (isClosed_eq (continuous_const.inner continuous_id) continuous_const)) hcl
    rintro y ⟨a,⟨b,hb,rfl⟩,rfl⟩
    exact horbit b hb
  rw [crossed_pairing] at hzT
  have hs : symmetrize T=T := symmetrize_eq hsT
  rw [hs] at hzT
  linarith

variable (ι : Type*) [Fintype ι] [DecidableEq ι]

theorem selfAdjoint_finite_approx (S : StarSubalgebra ℂ (H →L[ℂ] H))
    {T : H →L[ℂ] H} (hT : T∈Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))))
    (hsT : IsSelfAdjoint T) (x : SumSpace (H:=H) ι) (ε : ℝ) (hε : 0<ε) :
    ∃ a : H →L[ℂ] H, a∈S ∧ IsSelfAdjoint a ∧
      ‖diagonal (H:=H) ι a x-diagonal (H:=H) ι T x‖<ε := by
  have h := selfAdjoint_mem_orbit_closure (S.map (diagonal (H:=H) ι))
    (diagonal_bicommutant ι S hT) (hsT.map (diagonal (H:=H) ι)) x
  change diagonal (H:=H) ι T x∈closure
    (selfAdjointOrbit (S.map (diagonal (H:=H) ι)) x : Set (SumSpace (H:=H) ι)) at h
  obtain ⟨y,⟨a,⟨b,hb,hba⟩,hsa,hay⟩,hy⟩ := Metric.mem_closure_iff.mp h ε hε
  
  refine ⟨symmetrize b,symmetrize_mem S hb,symmetrize_selfAdjoint b,?_⟩
  change diagonal (H:=H) ι b=a at hba
  have he : diagonal (H:=H) ι (symmetrize b)=a := by
    have : diagonal (H:=H) ι (symmetrize b)=symmetrize (diagonal (H:=H) ι b) := by
      have hs : diagonal (H:=H) ι (star b)=star (diagonal (H:=H) ι b) := map_star _ _
      rw [symmetrize,symmetrize,←hs]
      ext v i
      simp only [diagonal_apply,smul_apply,add_apply,PiLp.smul_apply,PiLp.add_apply]
    rw [this,hba,symmetrize_eq hsa]
  rw [he,hay]
  rwa [dist_eq_norm,norm_sub_rev] at hy

end Kadison.Kaplansky

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_TracialDevelopment
attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion

namespace Kadison

namespace TracialGNS

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a))

noncomputable def rightMulPre (a : A) : τ.PreGNS →L[ℂ] τ.PreGNS :=
  (τ.toPreGNS.toLinearMap ∘ₗ LinearMap.mulRight ℂ a ∘ₗ τ.ofPreGNS.toLinearMap).mkContinuous
    ‖a‖ (fun x => by
      change ‖τ.toPreGNS (τ.ofPreGNS x * a)‖ ≤ ‖a‖ * ‖x‖
      calc
        _ = ‖τ.toPreGNS (star (τ.ofPreGNS x * a))‖ :=
          (norm_star_preGNS τ hτ _).symm
        _ = ‖τ.leftMulMapPreGNS (star a) (τ.toPreGNS (star (τ.ofPreGNS x)))‖ := by
          simp only [star_mul, PositiveLinearMap.leftMulMapPreGNS_apply,
            PositiveLinearMap.ofPreGNS_toPreGNS]
        _ ≤ ‖star a‖ * ‖τ.toPreGNS (star (τ.ofPreGNS x))‖ := by
          exact (ContinuousLinearMap.le_opNorm _ _).trans
            (mul_le_mul_of_nonneg_right
              (LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _) (norm_nonneg _))
        _ = ‖a‖ * ‖x‖ := by
          rw [norm_star, norm_star_preGNS τ hτ, PositiveLinearMap.toPreGNS_ofPreGNS])

@[simp] lemma rightMulPre_apply (a : A) (x : τ.PreGNS) :
    rightMulPre τ hτ a x = τ.toPreGNS (τ.ofPreGNS x * a) := rfl

noncomputable def rightMul (a : A) : τ.GNS →L[ℂ] τ.GNS :=
  (rightMulPre τ hτ a).completion

@[simp] lemma rightMul_coe (a : A) (x : τ.PreGNS) :
    rightMul τ hτ a (x : τ.GNS) = (τ.toPreGNS (τ.ofPreGNS x * a) : τ.GNS) := by
  simp [rightMul]

lemma rightMul_mul (a b : A) :
    rightMul τ hτ (a * b) = rightMul τ hτ b * rightMul τ hτ a := by
  ext x
  induction x using Completion.induction_on with
  | hp => apply isClosed_eq <;> fun_prop
  | ih x => simp [mul_apply_eq_comp, mul_assoc]

end TracialGNS

end Kadison
end

end OAI
end


