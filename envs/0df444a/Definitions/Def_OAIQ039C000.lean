-- Prove2me | Definitions.Def_OAIQ039C000
-- name    : OAIQ039C000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T06:11:05.450611+00:00
-- url     : https://prove2.me/theorems/4404dcbd-0cc4-44b0-8631-73244fc7f94a
-- title:
--   Definitions bundle OAIQ039C000 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 39 declarations of OpenAI's Lean: 16 definitions, 1 inductive type or structure and 22 theorems. The definitions and types are `OAI.Kadison.ActualHilbertSum.block`, `OAI.Kadison.ActualHilbertSum.insert`, `OAI.Kadison.ActualHilbertSum.project`, `OAI.Kadison.AtomicFactor.Decomposition`, `OAI.Kadison.AtomicFactor.Decomposition.finiteShift`, `OAI.Kadison.AtomicFactor.Decomposition.support`, `OAI.Kadison.AtomicFactor.IsMinimalProjection`, `OAI.Kadison.BalancedDilation.symmetry`, `OAI.Kadison.BicommutantRange.ofStarHom`, `OAI.Kadison.CStarContractiveLifts.radial`, `OAI.Kadison.HilbertBiprod.Space`, `OAI.Kadison.HilbertBiprod.block`, `OAI.Kadison.HilbertBiprod.inl`, `OAI.Kadison.HilbertBiprod.inlL`, `OAI.Kadison.HilbertBiprod.inr`, `OAI.Kadison.HilbertBiprod.inrL`, `OAI.Kadison.HilbertFiniteMaps.Copies`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Commutator, in whole or in part: `Commutator_AtomicCoefficients`, `Commutator_AtomicDecomposition`, `Commutator_AtomicShift`, `Commutator_BalancedDefect`, `Commutator_BalancedSymmetry`, `Commutator_BicommutantRange`, `Commutator_CFCIntertwiner`, `Commutator_CStarContractiveLifts`, `Commutator_FreeSymmetry15`, `Commutator_HilbertBiprod`, `Commutator_HilbertFiniteMaps`, `Commutator_MinimalProjection`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ039C020` and `OAIQ039C028`; the statements `OAI.Kadison.AtomicFactor.Decomposition.finite_dimensional`, `OAI.Kadison.AtomicFactor.Decomposition.two_isometries`, `OAI.Kadison.AtomicFactor.exists_decomposition`, `OAI_Kadison_MatrixCornerImplementation_exists_represented_local_module`, `OAI_Kadison_NormalRepresentation_traced_factor_bound` and `OAI_Kadison_OrbitStateHull_exists_faithful_normal_trace`; the proofs of `OAI.Kadison.AtomicFactor.Decomposition.two_isometries` and `OAI.Kadison.uniform_commutator_atomic_factor`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Commutator at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ039_CM.Commutator_MinimalProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace BigOperators

namespace Kadison

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace AtomicFactor

def IsMinimalProjection (M : VonNeumannAlgebra H) (p : H →L[ℂ] H) : Prop :=
  p∈M ∧ IsStarProjection p ∧ p≠0 ∧
    ∀ q∈M,IsStarProjection q → q≤p → q=0 ∨ q=p

end AtomicFactor

end Kadison

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_AtomicDecomposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace Topology BigOperators

open Filter

universe u

namespace Kadison.AtomicFactor

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

structure Decomposition (M : VonNeumannAlgebra H) (p : H →L[ℂ] H) where
  I : Type u
  v : I → H →L[ℂ] H
  mem : ∀ i,v i∈M
  initial : ∀ i,star (v i)*v i=p
  cross : ∀ i j,i≠j → star (v i)*v j=0
  source : ∀ i,v i*p=v i
  strong : ∀ x : H,Tendsto (fun s : Finset I => (∑ i∈s,v i*star (v i)) x) atTop (𝓝 x)

end Kadison.AtomicFactor

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_AtomicCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace Topology BigOperators

open Filter

namespace Kadison.AtomicFactor.Decomposition

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {M : VonNeumannAlgebra H} {p : H →L[ℂ] H} (D : Decomposition M p)

def support (s : Finset D.I) : H →L[ℂ] H := ∑ i∈s,D.v i*star (D.v i)

end Kadison.AtomicFactor.Decomposition

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_AtomicShift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace Topology BigOperators

open Filter

namespace Kadison.AtomicFactor.Decomposition

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {M : VonNeumannAlgebra H} {p : H →L[ℂ] H} (D : Decomposition M p)

def finiteShift (f : D.I → D.I) (s : Finset D.I) : H →L[ℂ] H :=
  ∑ i∈s,D.v (f i)*star (D.v i)

end Kadison.AtomicFactor.Decomposition

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_CFCIntertwiner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder ContinuousFunctionalCalculus

namespace Kadison.CFCIntertwiner

variable {A : Type*} [CStarAlgebra A]

local instance instContinuousFunctionalCalculusComplexProdIsStarNormal_solutions : ContinuousFunctionalCalculus ℂ (A × A) IsStarNormal :=
  IsStarNormal.instContinuousFunctionalCalculus

local instance instContinuousFunctionalCalculusRealProdIsSelfAdjoint_solutions : ContinuousFunctionalCalculus ℝ (A × A) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

lemma semiconj_cfc (x a b : A) (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b)
    (h : x*a=b*x) (f : ℝ → ℝ) (hf : Continuous f) :
    x*cfc f a=cfc f b*x := by
  have hab : IsSelfAdjoint (a,b) := Prod.ext ha hb
  have hc : ∀ g : C(spectrum ℝ (a,b),ℝ),
      x*(cfcHom hab g).1=(cfcHom hab g).2*x := by
    intro g
    induction g using ContinuousMap.induction_on_of_compact with
    | const r =>
      change x*((cfcHom hab) (algebraMap ℝ _ r)).1=((cfcHom hab) (algebraMap ℝ _ r)).2*x
      rw [AlgHomClass.commutes]
      change x*algebraMap ℝ A r=algebraMap ℝ A r*x
      exact (Algebra.commutes r x).symm
    | id => simpa only [cfcHom_id] using h
    | star_id => simpa only [map_star,cfcHom_id,Prod.fst_star,Prod.snd_star,ha.star_eq,hb.star_eq] using h
    | add g k hg hk => simp only [map_add,Prod.fst_add,Prod.snd_add,mul_add,add_mul,hg,hk]
    | mul g k hg hk =>
      simp only [map_mul,Prod.fst_mul,Prod.snd_mul]
      calc
        x*((cfcHom hab g).1*(cfcHom hab k).1)=
          (x*(cfcHom hab g).1)*(cfcHom hab k).1 := (mul_assoc ..).symm
        _=((cfcHom hab g).2*x)*(cfcHom hab k).1 := by rw [hg]
        _=(cfcHom hab g).2*((cfcHom hab k).2*x) := by rw [mul_assoc,hk]
        _=((cfcHom hab g).2*(cfcHom hab k).2)*x := (mul_assoc ..).symm
    | frequently g hg =>
      have closed : IsClosed {k : C(spectrum ℝ (a,b),ℝ) |
          x*(cfcHom hab k).1=(cfcHom hab k).2*x} :=
        isClosed_eq ((cfcHom_continuous hab).fst.const_mul x)
          ((cfcHom_continuous hab).snd.mul_const x)
      exact closed.mem_of_frequently_of_tendsto hg Filter.tendsto_id
  have hh : x*(cfc f (a,b)).1=(cfc f (a,b)).2*x := by
    rw [cfc_apply f (a,b) hab hf.continuousOn]
    exact hc _
  rw [cfc_map_prod (S := ℂ) f a b hf.continuousOn hab ha hb] at hh
  exact hh

end Kadison.CFCIntertwiner

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_BalancedDefect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder

namespace Kadison.BalancedDilation

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma sqrt_eq_real_cfc (a : A) (ha : 0≤a) : CFC.sqrt a=cfc Real.sqrt a := by
  rw [CFC.sqrt_eq_real_sqrt a ha,cfcₙ_eq_cfc (hf0 := Real.sqrt_zero)]

lemma defect_nonneg (x : A) (hx : ‖x‖≤1) : 0≤1-x*star x := by
  apply sub_nonneg.mpr
  apply (CStarAlgebra.norm_le_one_iff_of_nonneg (x*star x) (mul_star_self_nonneg x)).mp
  rw [CStarRing.norm_self_mul_star]
  exact (mul_le_mul_of_nonneg_right hx (norm_nonneg x)).trans (by simpa using hx)

lemma defect_intertwines (x : A) (hx : ‖x‖≤1) :
    CFC.sqrt (1-x*star x)*x=x*CFC.sqrt (1-star x*x) := by
  have h₁ := defect_nonneg x hx
  have h₂ : 0≤1-star x*x := by simpa only [star_star] using defect_nonneg (star x) (by simpa using hx)
  rw [sqrt_eq_real_cfc _ h₁,sqrt_eq_real_cfc _ h₂]
  exact (CFCIntertwiner.semiconj_cfc x (1-star x*x) (1-x*star x)
    (IsSelfAdjoint.of_nonneg h₂) (IsSelfAdjoint.of_nonneg h₁)
    (by noncomm_ring) Real.sqrt Real.continuous_sqrt).symm

end Kadison.BalancedDilation

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_BalancedSymmetry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder Matrix

namespace Kadison.BalancedDilation

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def symmetry (x : A) : CStarMatrix (Fin 2) (Fin 2) A :=
  CStarMatrix.ofMatrix !![CFC.sqrt (1-x*star x), x; star x, -CFC.sqrt (1-star x*x)]

lemma symmetry_selfAdjoint (x : A) : IsSelfAdjoint (symmetry x) := by
  apply CStarMatrix.ext
  intro i j
  have hl := (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg (1-x*star x))).star_eq
  have hr := (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg (1-star x*x))).star_eq
  fin_cases i <;> fin_cases j <;> simp [symmetry,CStarMatrix.star_apply,hl,hr]

lemma symmetry_mul_self (x : A) (hx : ‖x‖≤1) : symmetry x*symmetry x=1 := by
  have h₁ := defect_nonneg x hx
  have h₂ : 0≤1-star x*x := by
    simpa only [star_star] using defect_nonneg (star x) (by simpa using hx)
  have hl := CFC.sqrt_mul_sqrt_self (1-x*star x) h₁
  have hr := CFC.sqrt_mul_sqrt_self (1-star x*x) h₂
  have hi := defect_intertwines x hx
  have hi' := defect_intertwines (star x) (by simpa using hx)
  simp only [star_star] at hi'
  apply CStarMatrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [symmetry,CStarMatrix.mul_apply,Fin.sum_univ_two,hl,hr,hi,hi']

lemma symmetry_unitary (x : A) (hx : ‖x‖≤1) : symmetry x∈unitary (CStarMatrix (Fin 2) (Fin 2) A) := by
  rw [Unitary.mem_iff]
  rw [(symmetry_selfAdjoint x).star_eq,symmetry_mul_self x hx]
  exact ⟨rfl,rfl⟩

end Kadison.BalancedDilation

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_BicommutantRange
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexStarModule CStarAlgebra

open ComplexStarModule

namespace Kadison.BicommutantRange

variable {B : Type*} [CStarAlgebra B]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def ofStarHom {A : Type*} [CStarAlgebra A] (φ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hφ : Set.centralizer (Set.centralizer (Set.range φ))=Set.range φ) : VonNeumannAlgebra H where
  toStarSubalgebra := φ.range
  centralizer_centralizer' := hφ

end Kadison.BicommutantRange

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_CStarContractiveLifts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped CStarAlgebra

namespace Kadison.CStarContractiveLifts

def radial (t : ℝ) : ℝ := (Real.sqrt (max 1 |t|))⁻¹

end Kadison.CStarContractiveLifts

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeSymmetry15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open scoped InnerProductSpace TensorProduct ComplexOrder
open UniformSpace
open scoped InnerProductSpace _root_.Topology
open scoped TensorProduct
open UniformSpace
open scoped TensorProduct InnerProductSpace
open scoped InnerProductSpace ENNReal
open ContinuousLinearMap

namespace Kadison.ActualHilbertSum

variable {ι H : Type*} (E : ι → Type*)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]
  [∀ i, CompleteSpace (E i)]

variable (U : ∀ i, E i →ₗᵢ[ℂ] H)

abbrev insert (i : ι) := (U i).toContinuousLinearMap

def project (i : ι) : H →L[ℂ] E i := (insert E U i).adjoint

def block (T : H →L[ℂ] H) (i j : ι) : E j →L[ℂ] E i :=
  ((project E U i).comp T).comp (insert E U j)

@[simp] lemma project_insert (i : ι) : (project E U i).comp (insert E U i) = 1 := by
  ext x
  apply ext_inner_left ℂ
  intro y
  simp only [comp_apply, project, adjoint_inner_right, insert,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometry.inner_map_map,
    one_apply_eq_self]

@[simp] lemma block_adjoint (T : H →L[ℂ] H) (i j : ι) :
    block E U T.adjoint i j = (block E U T j i).adjoint := by
  simp only [block, project, adjoint_comp, adjoint_adjoint, comp_assoc]

variable (hU : IsHilbertSum ℂ E U)

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

omit [∀ i, CompleteSpace (E i)] in
include hU in
lemma map_ext (T R : H →L[ℂ] F)
    (h : ∀ i, T.comp (insert E U i)=R.comp (insert E U i)) : T=R := by
  classical
  have he : T.comp hU.linearIsometryEquiv.symm.toContinuousLinearEquiv.toContinuousLinearMap =
      R.comp hU.linearIsometryEquiv.symm.toContinuousLinearEquiv.toContinuousLinearMap := by
    apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
    intro i
    ext x
    have hi := congrArg (fun K : E i →L[ℂ] F => K x) (h i)
    change T (hU.linearIsometryEquiv.symm (lp.single 2 i x)) =
      R (hU.linearIsometryEquiv.symm (lp.single 2 i x))
    rw [hU.linearIsometryEquiv_symm_apply_single]
    exact hi
  ext x
  have hx := congrArg (fun K : lp E 2 →L[ℂ] F => K (hU.linearIsometryEquiv x)) he
  simpa only [comp_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    LinearIsometryEquiv.symm_apply_apply] using hx

end Kadison.ActualHilbertSum
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_HilbertBiprod
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology

namespace Kadison.HilbertBiprod

variable {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G]

abbrev Space (H G : Type*) := WithLp 2 (H × G)

def inlL : H →L[ℂ] Space H G :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ H G).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.id ℂ H).prod 0)

def inrL : G →L[ℂ] Space H G :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ H G).symm.toContinuousLinearMap.comp
    ((0 : G →L[ℂ] H).prod (ContinuousLinearMap.id ℂ G))

@[simp] lemma inlL_apply (x : H) : inlL (G:=G) x=WithLp.toLp 2 (x,0) := rfl

@[simp] lemma inrL_apply (y : G) : inrL (H:=H) y=WithLp.toLp 2 (0,y) := rfl

def inl : H →ₗᵢ[ℂ] Space H G :=
  (inlL (H:=H) (G:=G)).toLinearMap.isometryOfInner (by
    intro x y
    simp [WithLp.prod_inner_apply])

def inr : G →ₗᵢ[ℂ] Space H G :=
  (inrL (H:=H) (G:=G)).toLinearMap.isometryOfInner (by
    intro x y
    simp [WithLp.prod_inner_apply])

@[simp] lemma inl_apply (x : H) : inl (G:=G) x=WithLp.toLp 2 (x,0) := rfl

@[simp] lemma inr_apply (y : G) : inr (H:=H) y=WithLp.toLp 2 (0,y) := rfl

def block (S : H →L[ℂ] H) (T : G →L[ℂ] G) : Space H G →L[ℂ] Space H G :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ H G).symm.toContinuousLinearMap.comp
    ((S.prodMap T).comp (WithLp.prodContinuousLinearEquiv 2 ℂ H G).toContinuousLinearMap)

@[simp] lemma block_apply (S : H →L[ℂ] H) (T : G →L[ℂ] G) (x : Space H G) :
    block S T x=WithLp.toLp 2 (S x.ofLp.1,T x.ofLp.2) := rfl

lemma ext {S T : Space H G →L[ℂ] Space H G}
    (h : ∀ x,(S x).ofLp=(T x).ofLp) : S=T := by
  ext x
  exact WithLp.ofLp_injective 2 (h x)

@[simp] lemma block_zero : block (0:H →L[ℂ] H) (0:G →L[ℂ] G)=0 := by
  apply ext
  intro x
  rfl

@[simp] lemma block_one : block (1:H →L[ℂ] H) (1:G →L[ℂ] G)=1 := by
  apply ext
  intro x
  rfl

lemma block_mul (S S' : H →L[ℂ] H) (T T' : G →L[ℂ] G) :
    block (S*S') (T*T')=block S T*block S' T' := by
  apply ext
  intro x
  rfl

lemma block_add (S S' : H →L[ℂ] H) (T T' : G →L[ℂ] G) :
    block (S+S') (T+T')=block S T+block S' T' := by
  apply ext
  intro x
  rfl

end Kadison.HilbertBiprod

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_HilbertFiniteMaps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace Topology

namespace Kadison.HilbertFiniteMaps

variable {H G K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

variable (ι : Type*) [Fintype ι]

abbrev Copies (H ι : Type*) := PiLp 2 (fun _ : ι => H)

end Kadison.HilbertFiniteMaps

end

end
end

end OAI
end


