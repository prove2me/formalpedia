-- Prove2me | Definitions.Def_OAIQ039C027
-- name    : OAIQ039C027
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T06:17:01.496072+00:00
-- url     : https://prove2.me/theorems/6b296d58-888b-4c1f-a374-830db692c37a
-- title:
--   Definitions bundle OAIQ039C027 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 24 declarations of OpenAI's Lean: 9 definitions and 15 theorems. The definitions and types are `OAI.Kadison.HilbertPadding.amplifyIsometry`, `OAI.Kadison.HilbertPadding.doubleCopies`, `OAI.Kadison.HilbertPadding.leftCopies`, `OAI.Kadison.HilbertPadding.rightCopies`, `OAI.Kadison.HilbertTensor.multiplicityCompression`, `OAI.Kadison.HilbertTensor.scalarSlice`, `OAI.Kadison.InfiniteAmplification.algebra`, `OAI.Kadison.InfiniteAmplification.block`, `OAI.Kadison.InfiniteAmplification.zeroth`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Commutator, in whole or in part: `Commutator_AmplificationIsometry`, `Commutator_DoubleCopies`, `Commutator_HilbertModuleExtension`, `Commutator_HilbertPadding`, `Commutator_InfiniteDiagonalRange`, `Commutator_InfiniteReindex`, `Commutator_ProjectionPartition`, `Commutator_RightCopies`, `Commutator_TensorMultiplicity`, `Commutator_TensorMultiplicity2`, `Commutator_TracialDevelopment`.
--
--   **Imports.** It imports the bundles `OAIQ039C002`, `OAIQ039C003`, `OAIQ039C006`, `OAIQ039C011` and `OAIQ039C012` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ039C038` and `OAIQ039C056`; the statements `OAI.Kadison.CentralSpectral.central_indicators`, `OAI.Kadison.CentralSpectral.stable_model_bound`, `OAI.Kadison.CentralSpectral.stable_model_center`, `OAI.Kadison.HilbertPadding.diagonal_commutator_extend`, `OAI.Kadison.HilbertPadding.doubleCopies_commutator_norm`, `OAI.Kadison.HilbertPadding.doubleCopies_diagonal`, `OAI.Kadison.HilbertPadding.rightCopies_commutator_norm`, `OAI.Kadison.HilbertPadding.rightCopies_diagonal` and `OAI.Kadison.InfiniteAmplification.stable_center_range`; the proofs of `OAI.Kadison.CentralSpectral.central_indicators`, `OAI.Kadison.CentralSpectral.stable_model_bound`, `OAI.Kadison.CentralSpectral.stable_model_center`, `OAI.Kadison.HilbertPadding.amplified_extension_commutator_norm`, `OAI.Kadison.HilbertPadding.diagonal_commutator_extend`, `OAI.Kadison.HilbertPadding.doubleCopies_commutator_norm`, `OAI.Kadison.HilbertPadding.doubleCopies_diagonal`, `OAI.Kadison.HilbertPadding.matrix_padding_commutator_norm`, `OAI.Kadison.HilbertPadding.rightCopies_commutator_norm`, `OAI.Kadison.HilbertPadding.rightCopies_diagonal` and `OAI.Kadison.InfiniteAmplification.stable_center_range`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Commutator at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ039C002
import Definitions.Def_OAIQ039C003
import Definitions.Def_OAIQ039C006
import Definitions.Def_OAIQ039C011
import Definitions.Def_OAIQ039C012

section
-- module Solutions.OAIQ039_CM.Commutator_HilbertPadding
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

open ContinuousLinearMap

namespace Kadison.HilbertPadding

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

open OperatorAmplification

variable (ι κ : Type*) [Fintype ι] [Fintype κ]

def leftCopies : SumSpace (H:=H) ι →ₗᵢ[ℂ] SumSpace (H:=H) (ι⊕κ) where
  toFun v := WithLp.toLp 2 (Sum.elim (fun i => v i) (fun _ => 0))
  map_add' v w := by ext i; cases i <;> simp
  map_smul' z v := by ext i; cases i <;> simp
  norm_map' v := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp [PiLp.norm_sq_eq_of_L2, Fintype.sum_sum_type]

omit [CompleteSpace H] in
@[simp] lemma leftCopies_inl (v : SumSpace (H:=H) ι) (i : ι) :
    leftCopies ι κ v (Sum.inl i)=v i := rfl

omit [CompleteSpace H] in
@[simp] lemma leftCopies_inr (v : SumSpace (H:=H) ι) (k : κ) :
    leftCopies ι κ v (Sum.inr k)=0 := rfl

end Kadison.HilbertPadding

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_AmplificationIsometry
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

open ContinuousLinearMap

namespace Kadison.HilbertPadding

open OperatorAmplification

variable {A H K : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

variable (ι : Type*) [Fintype ι]

local instance instDecidableEq_solutions_2_rda4544_1 : DecidableEq ι := Classical.decEq ι
def amplifyIsometry (E : H →ₗᵢ[ℂ] K) : SumSpace (H:=H) ι →ₗᵢ[ℂ] SumSpace (H:=K) ι where
  toFun v := WithLp.toLp 2 (fun i => E (v i))
  map_add' v w := by ext i; simp
  map_smul' z v := by ext i; simp
  norm_map' v := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp [PiLp.norm_sq_eq_of_L2]

omit [CompleteSpace H] [CompleteSpace K] in
@[simp] lemma amplifyIsometry_apply (E : H →ₗᵢ[ℂ] K) (v : SumSpace (H:=H) ι) (i : ι) :
    amplifyIsometry ι E v i=E (v i) := rfl

end Kadison.HilbertPadding

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_DoubleCopies
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

open ContinuousLinearMap

namespace Kadison.HilbertPadding

open OperatorAmplification

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι : Type*) [Fintype ι]

local instance doubleCopiesIndexDecidableEq_rda4544_1 : DecidableEq ι := Classical.decEq ι
def doubleCopies : SumSpace (H:=H) ι →ₗᵢ[ℂ] SumSpace (H:=H) ((Fin 2)×ι) where
  toFun v := WithLp.toLp 2 (fun p => if p.1=0 then v p.2 else 0)
  map_add' v w := by ext p; by_cases h : p.1=0 <;> simp [h]
  map_smul' z v := by ext p; by_cases h : p.1=0 <;> simp [h]
  norm_map' v := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp [PiLp.norm_sq_eq_of_L2,Fintype.sum_prod_type,Fin.sum_univ_two]

omit [CompleteSpace H] in
@[simp] lemma doubleCopies_apply (v : SumSpace (H:=H) ι) (p : (Fin 2)×ι) :
    doubleCopies ι v p=if p.1=0 then v p.2 else 0 := rfl

end Kadison.HilbertPadding

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_HilbertModuleExtension
attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace ENNReal

open ContinuousLinearMap

namespace Kadison.HilbertModuleExtension

variable {ι E F K H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (V : ι → E →ₗᵢ[ℂ] K) (W : ι → F →ₗᵢ[ℂ] H)
  (hV : IsHilbertSum ℂ (fun _ : ι => E) V) (hW : IsHilbertSum ℂ (fun _ : ι => F) W)

omit [CompleteSpace E] [CompleteSpace F] in
@[simp] lemma extend_insert (T : E →L[ℂ] F) (i : ι) (x : E) :
    extend V W hV hW T (V i x)=W i (T x) := by
  classical
  change hW.linearIsometryEquiv.symm
    (lp.mapCLM 2 (fun _ : ι => T) (norm_nonneg T) (fun _ => le_rfl)
      (hV.linearIsometryEquiv (V i x))) = _
  rw [←hV.linearIsometryEquiv_symm_apply_single x,LinearIsometryEquiv.apply_symm_apply]
  have h : lp.mapCLM 2 (fun _ : ι => T) (norm_nonneg T) (fun _ => le_rfl)
      (lp.single 2 i x)=lp.single 2 i (T x) := by
    ext j
    by_cases hji : j=i
    · subst j; simp
    · simp [lp.single_apply,Pi.single_eq_of_ne hji]
  rw [h,hW.linearIsometryEquiv_symm_apply_single]

end Kadison.HilbertModuleExtension

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_InfiniteDiagonalRange
attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped InnerProductSpace Topology

namespace Kadison.InfiniteAmplification

local instance instDecidableEq_solutions_rda4544_1 {α : Sort*} : DecidableEq α := Classical.decEq α
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def block (i j : ℕ) : Space ℕ H →L[ℂ] Space ℕ H :=
  (lp.singleContinuousLinearMap ℂ (fun _ : ℕ => H) 2 i).comp (lp.evalCLM ℂ (fun _ : ℕ => H) 2 j)

omit [CompleteSpace H] in
lemma block_map_commute (T : H →L[ℂ] H) (i j : ℕ) :
    map T*block (H:=H) i j=block i j*map T := by
  ext x k
  change T (lp.single (E:=fun _ : ℕ => H) 2 i (x j) k)=lp.single (E:=fun _ : ℕ => H) 2 i (T (x j)) k
  by_cases hk : k=i <;> simp [lp.single_apply,hk]

def zeroth (T : Space ℕ H →L[ℂ] Space ℕ H) : H →L[ℂ] H :=
  (lp.evalCLM ℂ (fun _ : ℕ => H) 2 0).comp
    (T.comp (lp.singleContinuousLinearMap ℂ (fun _ : ℕ => H) 2 0))

omit [CompleteSpace H] in
lemma eq_map_of_blocks (T : Space ℕ H →L[ℂ] Space ℕ H)
    (hT : ∀ i j,block i j*T=T*block i j) : T=map (zeroth T) := by
  ext x i
  have he := congrArg (fun S : Space ℕ H →L[ℂ] Space ℕ H => S x 0) (hT 0 i)
  change lp.single (E:=fun _ : ℕ => H) 2 0 (T x i) 0=T (lp.single (E:=fun _ : ℕ => H) 2 0 (x i)) 0 at he
  change T x i=T (lp.single (E:=fun _ : ℕ => H) 2 0 (x i)) 0
  simpa only [lp.single_apply,Pi.single_eq_same] using he

lemma diagonal_bicommutant_range (M : VonNeumannAlgebra H) :
    Set.centralizer (Set.centralizer (Set.range ((diagonal (ι:=ℕ) (H:=H)).comp M.subtype)))=
      Set.range ((diagonal (ι:=ℕ) (H:=H)).comp M.subtype) := by
  apply Set.Subset.antisymm
  · intro T hT
    have hb : ∀ i j,block i j*T=T*block i j := fun i j => hT (block i j) (by
      rintro _ ⟨a,rfl⟩
      exact block_map_commute a.val i j)
    have he := eq_map_of_blocks T hb
    have hz : zeroth T∈M := by
      change zeroth T∈(M : Set (H →L[ℂ] H))
      rw [←M.centralizer_centralizer]
      intro b hb
      have hm : map b∈Set.centralizer (Set.range ((diagonal (ι:=ℕ) (H:=H)).comp M.subtype)) := by
        rintro _ ⟨a,rfl⟩
        change map (a : H →L[ℂ] H)*map b=map b*map a
        ext x i
        exact congrArg (fun R : H →L[ℂ] H => R (x i)) (hb a a.property)
      have hcomm := hT (map b) hm
      rw [he] at hcomm
      ext x
      have h := congrArg (fun R : Space ℕ H →L[ℂ] Space ℕ H => R (lp.single (E:=fun _ : ℕ => H) 2 0 x) 0) hcomm
      simpa only [mul_apply_eq_comp,map_apply,lp.single_apply,Pi.single_eq_same] using h
    exact ⟨⟨zeroth T,hz⟩,he.symm⟩
  · exact Set.subset_centralizer_centralizer

def algebra (M : VonNeumannAlgebra H) : VonNeumannAlgebra (Space ℕ H) where
  toStarSubalgebra := ((diagonal (ι:=ℕ) (H:=H)).comp M.subtype).range
  centralizer_centralizer' := diagonal_bicommutant_range M

end Kadison.InfiniteAmplification

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_InfiniteReindex
attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology InnerProductSpace ENNReal

namespace Kadison.InfiniteAmplification

variable {ι κ : Type*}

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
lemma norm_sq (x : Space ι H) : ‖x‖^2=∑' i,‖x i‖^2 := by
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
    lp.norm_rpow_eq_tsum (by norm_num : 0<(2:ℝ≥0∞).toReal) x

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
lemma reindex_mem (e : ι ↪ κ) (x : Space ι H) : Memℓp (Function.extend e x 0) 2 := by
  apply (memℓp_gen_iff (by norm_num : 0<(2:ℝ≥0∞).toReal)).mpr
  simp only [ENNReal.toReal_ofNat,Real.rpow_two,extend_sq]
  apply (summable_extend_zero e.injective).mpr
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using (lp.memℓp x).summable
    (by norm_num : 0<(2:ℝ≥0∞).toReal)

end Kadison.InfiniteAmplification

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_ProjectionPartition
attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators

namespace Kadison.SpectralPartition

variable {R : Type*} [Ring R] [StarRing R]

lemma splitPiece_projection {p : R} (hp : IsStarProjection p) (b : Bool) :
    IsStarProjection (splitPiece p b) := by
  cases b
  · exact hp.one_sub
  · exact hp

end Kadison.SpectralPartition

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_RightCopies
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

open ContinuousLinearMap

namespace Kadison.HilbertPadding

open OperatorAmplification

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι κ : Type*) [Fintype ι] [Fintype κ]

local instance rightCopiesSourceDecidableEq_rda4544_1 : DecidableEq ι := Classical.decEq ι
local instance rightCopiesPaddingDecidableEq_rda4544_1 : DecidableEq κ := Classical.decEq κ
def rightCopies : SumSpace (H:=H) ι →ₗᵢ[ℂ] SumSpace (H:=H) (κ⊕ι) where
  toFun v := WithLp.toLp 2 (Sum.elim (fun _ => 0) (fun i => v i))
  map_add' v w := by ext i; cases i <;> simp
  map_smul' z v := by ext i; cases i <;> simp
  norm_map' v := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp [PiLp.norm_sq_eq_of_L2,Fintype.sum_sum_type]

omit [CompleteSpace H] in
@[simp] lemma rightCopies_inl (v : SumSpace (H:=H) ι) (k : κ) :
    rightCopies ι κ v (Sum.inl k)=0 := rfl

omit [CompleteSpace H] in
@[simp] lemma rightCopies_inr (v : SumSpace (H:=H) ι) (i : ι) :
    rightCopies ι κ v (Sum.inr i)=v i := rfl

end Kadison.HilbertPadding

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_TensorMultiplicity
attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
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

namespace Kadison.HilbertTensor

variable {E F J K : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup J] [InnerProductSpace ℂ J]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

def scalarSlice [CompleteSpace F] (T : Completion (E ⊗[ℂ] J) →L[ℂ] Completion (F ⊗[ℂ] K))
    (a : J) (b : K) : E →L[ℂ] F :=
  ((insertRight b).adjoint.comp T).comp (insertRight a)

end Kadison.HilbertTensor
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_TensorMultiplicity2
attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
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

namespace Kadison.HilbertTensor

variable {E F J K : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup J] [InnerProductSpace ℂ J]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

def multiplicityCompression [CompleteSpace J]
    (T : Completion (E ⊗[ℂ] J) →L[ℂ] Completion (E ⊗[ℂ] J)) (v : E) : J →L[ℂ] J :=
  ((insertLeft v).adjoint.comp T).comp (insertLeft v)

end Kadison.HilbertTensor
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

lemma vacuum_norm_sq : ‖vacuum τ‖ ^ 2 = (τ 1).re := by
  simp only [vacuum, Completion.norm_coe, PositiveLinearMap.preGNS_norm_def,
    PositiveLinearMap.ofPreGNS_toPreGNS, star_one, one_mul]
  exact Real.sq_sqrt (τ.map_nonneg (show (0 : A) ≤ 1 from zero_le_one)).1

lemma vacuum_norm (h1 : τ 1 = 1) : ‖vacuum τ‖ = 1 := by
  have h := vacuum_norm_sq τ
  rw [h1] at h
  have := norm_nonneg (vacuum τ)
  change ‖vacuum τ‖ ^ 2 = 1 at h
  nlinarith

end TracialGNS

end Kadison
end

end OAI
end


