-- Prove2me | Definitions.Def_OAIQ039C020
-- name    : OAIQ039C020
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T06:14:33.288706+00:00
-- url     : https://prove2.me/theorems/081b1242-c8d5-45c5-ab10-476bf2ea2571
-- title:
--   Definitions bundle OAIQ039C020 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 43 declarations of OpenAI's Lean: 14 definitions and 29 theorems. The definitions and types are `OAI.Kadison.BiprodLinkColumn.Intertwiner`, `OAI.Kadison.BiprodLinkColumn.component`, `OAI.Kadison.BiprodLinkColumn.compression`, `OAI.Kadison.BiprodLinkColumn.finiteColumn`, `OAI.Kadison.BiprodLinkColumn.infiniteColumn`, `OAI.Kadison.CStarContractiveLifts.clip`, `OAI.Kadison.CentralAverage.pinch`, `OAI.Kadison.ConcreteCorner.inclusion`, `OAI.Kadison.HilbertBiprod.diagHom`, `OAI.Kadison.HilbertBiprod.left`, `OAI.Kadison.HilbertBiprod.right`, `OAI.Kadison.HilbertFiniteMaps.amplify`, `OAI.Kadison.HilbertFiniteMaps.column`, `OAI.Kadison.Kaplansky.kernel`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Commutator, in whole or in part: `Commutator_BiprodLinkColumn`, `Commutator_CStarContractiveLifts`, `Commutator_CentralPinching`, `Commutator_ConcreteCornerVonNeumann`, `Commutator_HilbertBiprod`, `Commutator_HilbertBiprodProjections`, `Commutator_HilbertFiniteMaps`, `Commutator_InfiniteLinkColumn`, `Commutator_KaplanskyRange`, `Commutator_KaplanskyRational`.
--
--   **Imports.** It imports the bundles `OAIQ039C000`, `OAIQ039C001`, `OAIQ039C002` and `OAIQ039C003` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ039C032` and `OAIQ039C037`; the statements `OAI.Kadison.BiprodLinkColumn.component_intertwines`, `OAI.Kadison.BiprodLinkColumn.compression_empty`, `OAI.Kadison.MatrixCornerImplementation.exists_local_module` and `OAI.Kadison.MatrixCornerImplementation.exists_matrix_corner_intertwiner`; the proofs of `OAI.Kadison.BiprodLinkColumn.component_intertwines`, `OAI.Kadison.BiprodLinkColumn.compression_empty`, `OAI.Kadison.CentralAverage.exists_finite_average` and `OAI.Kadison.IntertwinerCompression.pullback_matrix_commutator_norm_le`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Commutator at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ039C000
import Definitions.Def_OAIQ039C001
import Definitions.Def_OAIQ039C002
import Definitions.Def_OAIQ039C003

section
-- module Solutions.OAIQ039_CM.Commutator_HilbertBiprod
attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
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

lemma block_smul (z : ℂ) (S : H →L[ℂ] H) (T : G →L[ℂ] G) :
    block (z • S) (z • T)=z • block S T := by
  apply ext
  intro x
  rfl

variable [CompleteSpace H] [CompleteSpace G]

lemma block_star (S : H →L[ℂ] H) (T : G →L[ℂ] G) :
    block (star S) (star T)=star (block S T) := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℂ
  intro y
  simp only [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_left,
    block_apply,WithLp.prod_inner_apply]

variable {A : Type*} [CStarAlgebra A]

def diagHom (φ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ψ : A →⋆ₐ[ℂ] (G →L[ℂ] G)) :
    A →⋆ₐ[ℂ] (Space H G →L[ℂ] Space H G) where
  toFun a := block (φ a) (ψ a)
  map_one' := by simp
  map_mul' a b := by simp only [map_mul,block_mul]
  map_zero' := by simp
  map_add' a b := by simp only [map_add,block_add]
  commutes' z := by
    simp only [Algebra.algebraMap_eq_smul_one, map_smul, map_one, block_smul, block_one]
  map_star' a := by simp only [map_star,block_star]

@[simp] lemma diagHom_apply (φ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ψ : A →⋆ₐ[ℂ] (G →L[ℂ] G))
    (a : A) : diagHom φ ψ a=block (φ a) (ψ a) := rfl

end Kadison.HilbertBiprod

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_HilbertBiprodProjections
attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder

namespace Kadison.HilbertBiprod

variable {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

abbrev left : Space H G →L[ℂ] Space H G := block 1 0

abbrev right : Space H G →L[ℂ] Space H G := block 0 1

lemma left_projection : IsStarProjection (left (H:=H) (G:=G)) := by
  constructor
  · change block 1 0*block 1 0=block 1 0
    rw [←block_mul,one_mul,zero_mul]
  · change star (block (1:H →L[ℂ] H) (0:G →L[ℂ] G))=block 1 0
    rw [←block_star,star_one,star_zero]

lemma right_projection : IsStarProjection (right (H:=H) (G:=G)) := by
  constructor
  · change block 0 1*block 0 1=block 0 1
    rw [←block_mul,one_mul,zero_mul]
  · change star (block (0:H →L[ℂ] H) (1:G →L[ℂ] G))=block 0 1
    rw [←block_star,star_one,star_zero]

lemma adjoint_inlL : (inlL (H:=H) (G:=G)).adjoint=WithLp.fstL 2 ℂ H G := by
  ext x
  apply ext_inner_right ℂ
  intro y
  simp only [ContinuousLinearMap.adjoint_inner_left,inlL_apply,WithLp.prod_inner_apply,
    inner_zero_right,add_zero]
  rfl

lemma adjoint_inrL : (inrL (H:=H) (G:=G)).adjoint=WithLp.sndL 2 ℂ H G := by
  ext x
  apply ext_inner_right ℂ
  intro y
  simp only [ContinuousLinearMap.adjoint_inner_left,inrL_apply,WithLp.prod_inner_apply,
    inner_zero_right,zero_add]
  rfl

lemma inr_adjoint : (inrL (H:=H) (G:=G)).comp inrL.adjoint=right := by
  rw [adjoint_inrL]
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
attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
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

def column (T : ι → H →L[ℂ] G) : H →L[ℂ] Copies G ι :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => G)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi T)

omit [CompleteSpace H] [CompleteSpace G] [Fintype ι] in
@[simp] lemma column_apply (T : ι → H →L[ℂ] G) (x : H) (i : ι) : column ι T x i=T i x := rfl

lemma adjoint_column_apply (T : ι → H →L[ℂ] G) (y : Copies G ι) :
    (column ι T).adjoint y=∑ i,(T i).adjoint (y i) := by
  apply ext_inner_right ℂ
  intro x
  simp only [ContinuousLinearMap.adjoint_inner_left,PiLp.inner_apply,column_apply,sum_inner]

lemma adjoint_column_comp (T : ι → H →L[ℂ] G) :
    (column ι T).adjoint.comp (column ι T)=∑ i,(T i).adjoint.comp (T i) := by
  ext x
  simp only [ContinuousLinearMap.comp_apply,adjoint_column_apply,column_apply,sum_apply]

def amplify (T : H →L[ℂ] G) : Copies H ι →L[ℂ] Copies G ι :=
  column ι (fun i => T.comp (PiLp.proj 2 (fun _ : ι => H) i))

omit [CompleteSpace H] [CompleteSpace G] in
@[simp] lemma amplify_apply (T : H →L[ℂ] G) (x : Copies H ι) (i : ι) :
    amplify ι T x i=T (x i) := rfl

end Kadison.HilbertFiniteMaps

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_BiprodLinkColumn
attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace Topology

open Filter

namespace Kadison.BiprodLinkColumn

open HilbertBiprod PartialIsometryOrder HilbertFiniteMaps

variable {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

variable (N : VonNeumannAlgebra (Space H G))

abbrev Intertwiner := Link N (right (H:=H) (G:=G)) left

def component (v : Intertwiner N) : H →L[ℂ] G :=
  (inrL (H:=H) (G:=G)).adjoint.comp (v.val.adjoint.comp inlL)

lemma component_adjoint (v : Intertwiner N) :
    (component N v).adjoint=(inlL (H:=H) (G:=G)).adjoint.comp (v.val.comp inrL) := by
  simp only [component,ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_adjoint,
    ContinuousLinearMap.comp_assoc]

lemma source_adjoint (v : Intertwiner N) :
    (right (H:=H) (G:=G)).comp v.val.adjoint=v.val.adjoint := by
  have hv : v.val.comp (right (H:=H) (G:=G))=v.val := by
    simpa only [ContinuousLinearMap.mul_def] using v.mul_source right_projection
  have h := congrArg (fun T : Space H G →L[ℂ] Space H G => T.adjoint) hv
  rw [ContinuousLinearMap.adjoint_comp] at h
  have hr : (right (H:=H) (G:=G)).adjoint=right := right_projection.isSelfAdjoint.star_eq
  simpa only [hr] using h

lemma inr_component (v : Intertwiner N) :
    (inrL (H:=H) (G:=G)).comp (component N v)=v.val.adjoint.comp inlL := by
  rw [component,←ContinuousLinearMap.comp_assoc,inr_adjoint,
    ←ContinuousLinearMap.comp_assoc,source_adjoint N v]

lemma component_square (v : Intertwiner N) :
    (component N v).adjoint.comp (component N v)=
      (inlL (H:=H) (G:=G)).adjoint.comp (v.final.comp inlL) := by
  rw [component_adjoint,ContinuousLinearMap.comp_assoc,ContinuousLinearMap.comp_assoc,
    inr_component]
  rfl

variable (S : Set (Intertwiner N)) (hS : OrthogonalLinks N right left S)

def finiteColumn (s : Finset S) : H →L[ℂ] Copies G s :=
  column s (fun v => component N v.val.val)

def compression (s : Finset S) : H →L[ℂ] H :=
  (inlL (H:=H) (G:=G)).adjoint.comp ((finiteProjection N right left S s).comp inlL)

lemma column_square (s : Finset S) :
    (finiteColumn N S s).adjoint.comp (finiteColumn N S s)=compression N S s := by
  classical
  rw [finiteColumn,adjoint_column_comp]
  simp only [component_square]
  ext x
  simp [compression,finiteProjection,ContinuousLinearMap.comp_apply]
  exact Finset.sum_attach s (fun v => (inlL (H:=H) (G:=G)).adjoint (v.val.final (inlL x)))

include hS

lemma compression_tendsto (hspan : (familySpace N right left S).starProjection=left) (x : H) :
    Tendsto (fun s : Finset S => compression N S s x) atTop (𝓝 x) := by
  have h := (inlL (H:=H) (G:=G)).adjoint.continuous.tendsto
    (left (inlL (H:=H) (G:=G) x))
  have ht := h.comp (finiteProjection_tendsto N right left S hS left_projection hspan (inlL x))
  have he : (inlL (H:=H) (G:=G)).adjoint (left (inlL x))=x := by
    rw [adjoint_inlL]
    rfl
  rw [he] at ht
  exact ht

end Kadison.BiprodLinkColumn

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_CStarContractiveLifts
attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
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

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

def clip (a : A) : A := a*cfc radial (star a*a)

end Kadison.CStarContractiveLifts

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_CentralPinching
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace

namespace Kadison.CentralAverage

open UnitaryOrbit

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H)

lemma projectionElement_projection (p : CentralProjection M) : IsStarProjection (projectionElement M p) := by
  constructor
  · apply Subtype.ext
    exact p.property.2.1.isIdempotentElem.eq
  · apply Subtype.ext
    exact p.property.2.1.isSelfAdjoint.star_eq

def pinch (p : CentralProjection M) (T : H →L[ℂ] H) : H →L[ℂ] H :=
  (1/2:ℝ) • T+(1/2:ℝ) • conjugate M
    (reflection (projectionElement M p) (projectionElement_projection M p)) T

end Kadison.CentralAverage

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_ConcreteCornerVonNeumann
attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace

namespace Kadison.ConcreteCorner

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H)

def inclusion : Algebra M →⋆ₐ[ℂ] (H →L[ℂ] H) := M.toStarSubalgebra.subtype

end Kadison.ConcreteCorner

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_InfiniteLinkColumn
attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology InnerProductSpace ENNReal NNReal

open Filter

namespace Kadison.BiprodLinkColumn

open HilbertBiprod PartialIsometryOrder HilbertFiniteMaps

variable {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

variable (N : VonNeumannAlgebra (Space H G))

variable (S : Set (Intertwiner N)) (hS : OrthogonalLinks N right left S)

variable (hspan : (familySpace N right left S).starProjection=left)

lemma finite_sum_norm_sq (s : Finset S) (x : H) :
    ∑ v∈s,‖component N v.val x‖^2=(inner ℂ x (compression N S s x)).re := by
  have he := congrArg (fun T : H →L[ℂ] H => inner ℂ x (T x)) (column_square N S s)
  rw [ContinuousLinearMap.comp_apply,ContinuousLinearMap.adjoint_inner_right] at he
  rw [←he]
  change _ = RCLike.re (inner ℂ (finiteColumn N S s x) (finiteColumn N S s x))
  rw [←norm_sq_eq_re_inner (𝕜:=ℂ)]
  rw [PiLp.norm_sq_eq_of_L2]
  exact (Finset.sum_attach s (fun v => ‖component N v.val x‖^2)).symm

include hS hspan

lemma column_hasSum (x : H) :
    HasSum (fun v : S => ‖component N v.val x‖^2) (‖x‖^2) := by
  have hc : Continuous (fun y : H => (inner ℂ x y).re) :=
    Complex.continuous_re.comp (continuous_const.inner continuous_id)
  have ht := (hc.tendsto x).comp (compression_tendsto N S hS hspan x)
  have hn : (inner ℂ x x).re=‖x‖^2 := (norm_sq_eq_re_inner (𝕜:=ℂ) x).symm
  change Tendsto (fun s : Finset S => ∑ v∈s,‖component N v.val x‖^2) atTop (𝓝 (‖x‖^2))
  convert ht using 1
  · ext s
    exact finite_sum_norm_sq N S s x
  · rw [hn]

lemma column_memℓp (x : H) : Memℓp (fun v : S => component N v.val x) 2 := by
  apply (memℓp_gen_iff (by norm_num : (0:ℝ)<(2:ℝ≥0∞).toReal)).mpr
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using (column_hasSum N S hS hspan x).summable

def infiniteColumn : H →ₗᵢ[ℂ] lp (fun _ : S => G) 2 where
  toFun x := ⟨fun v => component N v.val x,column_memℓp N S hS hspan x⟩
  map_add' x y := by ext v; exact map_add _ _ _
  map_smul' c x := by ext v; exact map_smul _ _ _
  norm_map' x := by
    let v : lp (fun _ : S => G) 2 := ⟨fun v => component N v.val x,column_memℓp N S hS hspan x⟩
    have hn : ‖v‖^2=‖x‖^2 := by
      have he := lp.norm_rpow_eq_tsum (by norm_num : (0:ℝ)<(2:ℝ≥0∞).toReal) v
      simp only [ENNReal.toReal_ofNat,Real.rpow_two] at he
      exact he.trans (column_hasSum N S hS hspan x).tsum_eq
    exact (sq_eq_sq₀ (norm_nonneg v) (norm_nonneg x)).mp hn

@[simp] lemma infiniteColumn_apply (x : H) (v : S) :
    infiniteColumn N S hS hspan x v=component N v.val x := rfl

end Kadison.BiprodLinkColumn

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_KaplanskyRational
attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace

namespace Kadison.Kaplansky

lemma continuous_rationalKernel : Continuous rationalKernel := by
  unfold rationalKernel
  exact (continuous_const.add (continuous_id.pow 2)).inv₀ (fun t => ne_of_gt (denom_pos t))

lemma rationalKernel_bound (t : ℝ) : ‖rationalKernel t‖≤1 := by
  rw [rationalKernel,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (denom_pos t))]
  exact (inv_le_one₀ (denom_pos t)).mpr (by nlinarith [sq_nonneg t])

variable {A : Type*} [CStarAlgebra A]

def kernel (a : A) : A := cfc rationalKernel a

lemma kernel_selfAdjoint (a : A) : IsSelfAdjoint (kernel a) := cfc_predicate _ _

lemma clip_formula {a : A} (ha : IsSelfAdjoint a) :
    clip a=(2:ℝ) • (a*kernel a) := by
  unfold clip rationalClip kernel
  have he : (fun t : ℝ => 2*t/(1+t^2))=(fun t => 2*(t*rationalKernel t)) := by
    funext t
    simp only [rationalKernel,div_eq_mul_inv,mul_assoc]
  rw [he,cfc_const_mul (2:ℝ) (fun t => t*rationalKernel t) a
    (continuous_id.mul continuous_rationalKernel).continuousOn,
    cfc_mul (fun t:ℝ=>t) rationalKernel a continuous_id.continuousOn
      continuous_rationalKernel.continuousOn,cfc_id' ℝ a ha]

lemma kernel_commute {a : A} (ha : IsSelfAdjoint a) : Commute a (kernel a) := by
  have h := cfc_commute_cfc (fun t : ℝ => t) rationalKernel a
  rwa [cfc_id' ℝ a ha] at h

end Kadison.Kaplansky

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_KaplanskyRange
attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace CStarAlgebra ComplexStarModule

namespace Kadison.Kaplansky

open OperatorAmplification ComplexStarModule

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι : Type*) [Fintype ι] [DecidableEq ι]

variable {A : Type*} [CStarAlgebra A]

variable (φ : A →⋆ₐ[ℂ] (H →L[ℂ] H))

lemma clip_mem_range {b : H →L[ℂ] H} (hb : IsSelfAdjoint b)
    (hr : b∈φ.range) : clip b∈φ.range := by
  obtain ⟨a,ha⟩ := hr
  change φ a=b at ha
  let a₀ : A := ℜ a
  have ha₀ : IsSelfAdjoint a₀ := (ℜ a).property
  have he : φ a₀=b := by rw [show a₀=(ℜ a:A) from rfl,map_realPart,ha,hb.coe_realPart]
  refine ⟨clip a₀,?_⟩
  change φ (clip a₀)=clip b
  rw [clip,φ.map_cfc rationalClip a₀ continuous_rationalClip.continuousOn
    (by fun_prop) ha₀ (ha₀.map φ),he]
  rfl

end Kadison.Kaplansky

end

end
end

end OAI
end


