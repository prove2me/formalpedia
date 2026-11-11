-- Prove2me | Definitions.Def_OAIQ239Tc000
-- name    : OAIQ239Tc000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T22:09:55.038915+00:00
-- url     : https://prove2.me/theorems/2103a7e0-550b-497c-b98e-bc2d9f03190d
-- title:
--   Definitions bundle OAIQ239Tc000 of the split of OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 137 declarations of OpenAI's Lean: 40 definitions, 1 inductive type or structure, 7 instances and 89 theorems. The definitions and types are `OAI.InjectiveLinearLift.continuousLift`, `OAI.InjectiveLinearLift.lift`, `OAI.QuadraticShell.profile`, `OAI.ResolventTaylor.second`, `OAI.TamingCompatibility.AntiInvariantFrame.covectorWedge`, `OAI.TamingCompatibility.AntiInvariantFrame.imagPart`, `OAI.TamingCompatibility.AntiInvariantFrame.realPart`, `OAI.TamingCompatibility.ClosureLinear.toClosure`, `OAI.TamingCompatibility.ExteriorForms.Form`, `OAI.TamingCompatibility.ExteriorForms.volumeSquare`, `OAI.TamingCompatibility.ExteriorForms.wedgeOne`, `OAI.TamingCompatibility.ExteriorForms.wedgeOneBilinear`, `OAI.TamingCompatibility.ExteriorForms.wedgeOneRight`, `OAI.TamingCompatibility.FormMetric.pairLeft`, `OAI.TamingCompatibility.FormMetric.pairRight`, `OAI.TamingCompatibility.FormMetric.pairing`, `OAI.TamingCompatibility.FormMetric.pairingCLM`, `OAI.TamingCompatibility.FormMetric.sharp`, `OAI.TamingCompatibility.FormMetric.sharpCLM`, `OAI.TamingCompatibility.FormMetric.singleBasis`, `OAI.TamingCompatibility.FormMetric.singleFamily`, `OAI.TamingCompatibility.FormMetric.tripleBasis`, `OAI.TamingCompatibility.FormMetric.tripleFamily`, `OAI.TamingCompatibility.FormMetric.tripleIndices`, `OAI.TamingCompatibility.FormMetric.wedgeBasis`, `OAI.TamingCompatibility.FormMetric.wedgeFamily`, `OAI.TamingCompatibility.HodgeThree.star`, `OAI.TamingCompatibility.MetricForms.Form`, `OAI.TamingCompatibility.MetricForms.basisOfFrame`, `OAI.TamingCompatibility.MetricForms.isometryEquiv`, `OAI.TamingCompatibility.MetricForms.pairing`, `OAI.TamingCompatibility.MetricHodge.formEquiv`, `OAI.TamingCompatibility.MetricHodge.starThree`, `OAI.TamingCompatibility.MetricModel.Metric`, `OAI.TamingCompatibility.MetricModel.Model`, `OAI.TamingCompatibility.MetricModel.equiv`, `OAI.TamingCompatibility.MetricModel.isometry`, `OAI.TamingCompatibility.MetricModel.linearEquiv`, `OAI.TamingCompatibility.MetricModel.ofOriginal`, `OAI.TamingCompatibility.MetricModel.toOriginal` and 1 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `TamingCompatibility_Charts_LocalFrameOperator`, `TamingCompatibility_Concentration_ActivationScales`, `TamingCompatibility_DifferentialForms_AntiInvariantFrame`, `TamingCompatibility_DifferentialForms_ClosedGraphLift`, `TamingCompatibility_DifferentialForms_ComplexEquiv`, `TamingCompatibility_DifferentialForms_ContDiffApply`, `TamingCompatibility_DifferentialForms_Form`, `TamingCompatibility_DifferentialForms_FormEquiv`, `TamingCompatibility_DifferentialForms_FormPairing`, `TamingCompatibility_DifferentialForms_FramePairing`, `TamingCompatibility_DifferentialForms_JAction`, `TamingCompatibility_DifferentialForms_Linear`, `TamingCompatibility_DifferentialForms_SingleFamily`, `TamingCompatibility_DifferentialForms_SmoothGeometricInverse`, `TamingCompatibility_DifferentialForms_Star`, `TamingCompatibility_Functional_QuadraticShell`, `TamingCompatibility_HeatFlow_ResolventTaylor`, `TamingCompatibility_Hodge_ClosureLinear`, `TamingCompatibility_Hodge_LocalCodifferential`.
--
--   **Imports.** It imports the published bundle `Def_TamingCompatibility`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ239Tc005`, `OAIQ239Tc006`, `OAIQ239Tc007`, `OAIQ239Tc008` and `OAIQ239Tc009`.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Definitions.Def_TamingCompatibility

section
-- module Solutions.OAIQ239_TC.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
section OAIVecLookup
variable {α : Type _}
@[simp] theorem vecCons3_one (a b c : α) : (![a, b, c] : Fin 3 → α) 1 = b := rfl
@[simp] theorem vecCons3_two (a b c : α) : (![a, b, c] : Fin 3 → α) 2 = c := rfl
@[simp] theorem vecCons4_one (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 1 = b := rfl
@[simp] theorem vecCons4_two (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 2 = c := rfl
@[simp] theorem vecCons4_three (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 3 = d := rfl
end OAIVecLookup
section OAIVecTail
variable {α : Type _}
@[simp] theorem vecConsTail1_1 (x : α) (f : Fin 1 → α) : (Matrix.vecCons x f : Fin 2 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail2_1 (x : α) (f : Fin 2 → α) : (Matrix.vecCons x f : Fin 3 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail2_2 (x : α) (f : Fin 2 → α) : (Matrix.vecCons x f : Fin 3 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail3_1 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail3_2 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail3_3 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 3 = f 2 := rfl
@[simp] theorem vecConsTail4_1 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail4_2 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail4_3 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 3 = f 2 := rfl
@[simp] theorem vecConsTail4_4 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 4 = f 3 := rfl
end OAIVecTail
@[simp] theorem fin3_mk_0 (h : 0 < 3) : (⟨0, h⟩ : Fin 3) = 0 := rfl
@[simp] theorem fin3_mk_1 (h : 1 < 3) : (⟨1, h⟩ : Fin 3) = 1 := rfl
@[simp] theorem fin3_mk_2 (h : 2 < 3) : (⟨2, h⟩ : Fin 3) = 2 := rfl
@[simp] theorem fin4_mk_0 (h : 0 < 4) : (⟨0, h⟩ : Fin 4) = 0 := rfl
@[simp] theorem fin4_mk_1 (h : 1 < 4) : (⟨1, h⟩ : Fin 4) = 1 := rfl
@[simp] theorem fin4_mk_2 (h : 2 < 4) : (⟨2, h⟩ : Fin 4) = 2 := rfl
@[simp] theorem fin4_mk_3 (h : 3 < 4) : (⟨3, h⟩ : Fin 4) = 3 := rfl
@[simp] theorem fin5_mk_0 (h : 0 < 5) : (⟨0, h⟩ : Fin 5) = 0 := rfl
@[simp] theorem fin5_mk_1 (h : 1 < 5) : (⟨1, h⟩ : Fin 5) = 1 := rfl
@[simp] theorem fin5_mk_2 (h : 2 < 5) : (⟨2, h⟩ : Fin 5) = 2 := rfl
@[simp] theorem fin5_mk_3 (h : 3 < 5) : (⟨3, h⟩ : Fin 5) = 3 := rfl
@[simp] theorem fin5_mk_4 (h : 4 < 5) : (⟨4, h⟩ : Fin 5) = 4 := rfl
@[simp] theorem fin4_lit_0_2 : ((0 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin4_lit_0_3 : ((0 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_1_2 : ((1 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin4_lit_1_3 : ((1 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_2_0 : ((2 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_2_1 : ((2 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_2_3 : ((2 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_3_0 : ((3 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_3_1 : ((3 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_3_2 : ((3 : Fin 4) = 2) ↔ False := by decide
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_ContDiffApply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

section

section

noncomputable section
namespace TamingCompatibility.FormSmooth
open ContinuousAlternatingMap
variable {E D F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {n : WithTop ℕ∞} {U : Set D}

lemma contDiffOn_of_basis {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E)
    {k : ℕ} {α : D → E [⋀^Fin k]→L[ℝ] ℝ}
    (h : ∀ a : Fin k → ι, ContDiffOn ℝ n (fun x => α x (fun i => b (a i))) U) :
    ContDiffOn ℝ n α U := by
  let L : (E [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ((Fin k → ι) → ℝ) :=
    ContinuousLinearMap.pi (fun a => ContinuousAlternatingMap.apply ℝ E ℝ (fun i => b (a i)))
  have hL : Function.Injective L := by
    intro a c hac
    apply ContinuousAlternatingMap.toAlternatingMap_injective
    apply b.ext_alternating
    intro v _
    exact congrArg (fun f => f v) hac
  let R := L.toLinearMap.leftInverse.toContinuousLinearMap
  have hr : ∀ a, R (L a) = a :=
    LinearMap.leftInverse_apply_of_inj (LinearMap.ker_eq_bot.mpr hL)
  have hl : ContDiffOn ℝ n (fun x => L (α x)) U := contDiffOn_pi.mpr h
  simpa only [Function.comp_def,hr] using R.contDiff.comp_contDiffOn hl

end TamingCompatibility.FormSmooth
noncomputable section
namespace TamingCompatibility.ExteriorForms
open ContinuousAlternatingMap
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {degree : ℕ}

abbrev Form (k : ℕ) := E [⋀^Fin k]→L[ℝ] ℝ

def wedgeOne (a : E →L[ℝ] ℝ) (b : Form (E := E) degree) : Form (E := E) (degree+1) :=
  alternatizeUncurryFin (a.smulRight b)

def wedgeOneRight (b : Form (E := E) degree) :
    (E →L[ℝ] ℝ) →L[ℝ] Form (E := E) (degree+1) :=
  alternatizeUncurryFinCLM ℝ E ℝ ∘L
    (ContinuousLinearMap.smulRightL ℝ E (Form (E := E) degree)).flip b

lemma wedgeOneRight_apply (b : Form (E := E) degree) (a : E →L[ℝ] ℝ) :
    wedgeOneRight b a = wedgeOne a b := rfl

lemma wedgeOne_apply_two (a : E →L[ℝ] ℝ) (b : Form (E := E) 1) (u v : E) :
    wedgeOne a b ![u,v] = a u * b ![v] - a v * b ![u] := by
  rw [wedgeOne, alternatizeUncurryFin_apply]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
    pow_zero, pow_one, zero_add, one_smul, neg_smul, add_zero]
  have h0 : Fin.removeNth (0 : Fin 2) ![u,v] = ![v] := by ext i; fin_cases i; rfl
  have h1 : Fin.removeNth (1 : Fin 2) ![u,v] = ![u] := by ext i; fin_cases i; rfl
  change a u * b (Fin.removeNth (0 : Fin 2) ![u,v]) -
    a v * b (Fin.removeNth (1 : Fin 2) ![u,v]) = _
  rw [h0,h1]

lemma wedgeOne_apply_three (a : E →L[ℝ] ℝ) (b : Form (E := E) 2) (u v w : E) :
    wedgeOne a b ![u,v,w] = a u * b ![v,w] - a v * b ![u,w] + a w * b ![u,v] := by
  rw [wedgeOne, alternatizeUncurryFin_apply]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
    pow_zero, pow_one, zero_add, one_smul, neg_smul, add_zero]
  have h0 : Fin.removeNth (0 : Fin 3) ![u,v,w] = ![v,w] := by ext i; fin_cases i <;> rfl
  have h1 : Fin.removeNth (1 : Fin 3) ![u,v,w] = ![u,w] := by ext i; fin_cases i <;> rfl
  have h2 : Fin.removeNth (2 : Fin 3) ![u,v,w] = ![u,v] := by ext i; fin_cases i <;> rfl
  simp [h0, h1, h2, ContinuousLinearMap.smulRight_apply, sub_eq_add_neg]
  ring

def volumeSquare (F : Form (E := E) 2) : Form (E := E) 4 :=
  (1/4 : ℝ) • alternatizeUncurryFin
    (wedgeOneRight F ∘L (ofSubsingletonLIE (0 : Fin 1)).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L F.curryLeft)

lemma two_swap (F : Form (E := E) 2) (u v : E) : F ![v,u] = -F ![u,v] := by
  have hv : ![u,v] ∘ Equiv.swap (0 : Fin 2) 1 = ![v,u] := by
    ext i
    fin_cases i <;> simp
  simpa only [hv, ContinuousAlternatingMap.coe_toAlternatingMap] using F.map_swap ![u,v] (by decide : (0 : Fin 2) ≠ 1)

lemma volumeSquare_apply (F : Form (E := E) 2) (u v w z : E) :
    volumeSquare F ![u,v,w,z] = F ![u,v] * F ![w,z] -
      F ![u,w] * F ![v,z] + F ![u,z] * F ![v,w] := by
  rw [volumeSquare, ContinuousAlternatingMap.smul_apply, alternatizeUncurryFin_apply]
  have h0 : Fin.removeNth (0 : Fin 4) ![u,v,w,z] = ![v,w,z] := by ext i; fin_cases i <;> rfl
  have h1 : Fin.removeNth (1 : Fin 4) ![u,v,w,z] = ![u,w,z] := by ext i; fin_cases i <;> rfl
  have h2 : Fin.removeNth (2 : Fin 4) ![u,v,w,z] = ![u,v,z] := by ext i; fin_cases i <;> rfl
  have h3 : Fin.removeNth (3 : Fin 4) ![u,v,w,z] = ![u,v,w] := by ext i; fin_cases i <;> rfl
  have hv (a b : E) : F (Matrix.vecCons a (fun _ : Fin 1 => b)) = F ![a,b] := by
    congr 1
    ext i
    fin_cases i <;> rfl
  have huv := two_swap F u v
  have huw := two_swap F u w
  have huz := two_swap F u z
  have hvw := two_swap F v w
  have hvz := two_swap F v z
  have hwz := two_swap F w z
  simp [Fin.sum_univ_succ, h0,h1,h2,h3, wedgeOneRight_apply,
    wedgeOne_apply_three, hv, huv,huw,huz,hvw,hvz,hwz]
  ring

end TamingCompatibility.ExteriorForms
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_FormPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Manifold ContDiff
open scoped Manifold ContDiff Topology
open Filter Set
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
open scoped Manifold ContDiff Topology
open Bundle Filter Set
open Set
open Bundle Set Filter
open scoped Topology
open Set _root_.MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology
open scoped BigOperators
namespace TamingCompatibility.FormMetric
open RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {k : ℕ}

def sharp : (E [⋀^Fin k]→L[ℝ] ℝ) →ₗ[ℝ] ⋀[ℝ]^k E :=
  (InnerProductSpace.toDual ℝ (⋀[ℝ]^k E)).symm.toLinearEquiv.toLinearMap ∘ₗ
    LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ
    exteriorPower.alternatingMapLinearEquiv.toLinearMap ∘ₗ
    ContinuousAlternatingMap.toAlternatingMapLinear

lemma sharp_inner (α : E [⋀^Fin k]→L[ℝ] ℝ) (v : Fin k → E) :
    ⟪sharp α, exteriorPower.ιMulti ℝ k v⟫ = α v := by
  simp [sharp, InnerProductSpace.toDual_symm_apply]

lemma sharp_injective : Function.Injective (sharp (E := E) (k := k)) := by
  intro α β h
  ext v
  simpa only [sharp_inner] using congrArg (fun a => ⟪a, exteriorPower.ιMulti ℝ k v⟫) h

def pairing (α β : E [⋀^Fin k]→L[ℝ] ℝ) : ℝ := ⟪sharp α, sharp β⟫

def pairLeft : Fin 6 → Fin 4 := ![0, 0, 0, 1, 1, 2]
def pairRight : Fin 6 → Fin 4 := ![1, 2, 3, 2, 3, 3]

def wedgeFamily (b : OrthonormalBasis (Fin 4) ℝ E) (i : Fin 6) : ⋀[ℝ]^2 E :=
  exteriorPower.ιMulti ℝ 2 ![b (pairLeft i), b (pairRight i)]

lemma wedgeFamily_orthonormal (b : OrthonormalBasis (Fin 4) ℝ E) :
    Orthonormal ℝ (wedgeFamily b) := by
  rw [orthonormal_iff_ite]
  intro i j
  simp only [wedgeFamily, exteriorPower.inner_ιMulti_ιMulti, Matrix.det_fin_two]
  have hb := orthonormal_iff_ite.mp b.orthonormal
  fin_cases i <;> fin_cases j <;>
    simp [pairLeft, pairRight, hb]

def wedgeBasis (b : OrthonormalBasis (Fin 4) ℝ E) :
    OrthonormalBasis (Fin 6) ℝ (⋀[ℝ]^2 E) :=
  OrthonormalBasis.mk (wedgeFamily_orthonormal b)
    ((wedgeFamily_orthonormal b).linearIndependent.span_eq_top_of_card_eq_finrank (by
      rw [exteriorPower.finrank_eq, Module.finrank_eq_card_basis b.toBasis]
      norm_num [Nat.choose])).ge

lemma wedgeBasis_apply (b : OrthonormalBasis (Fin 4) ℝ E) (i : Fin 6) :
    wedgeBasis b i = wedgeFamily b i := by
  simp only [wedgeBasis, OrthonormalBasis.coe_mk]

lemma wedgeBasis_repr (b : OrthonormalBasis (Fin 4) ℝ E)
    (α : E [⋀^Fin 2]→L[ℝ] ℝ) (i : Fin 6) :
    (wedgeBasis b).repr (sharp α) i = α ![b (pairLeft i), b (pairRight i)] := by
  rw [OrthonormalBasis.repr_apply_apply, real_inner_comm, wedgeBasis_apply]
  exact sharp_inner _ _

lemma pairing_eq_sum (b : OrthonormalBasis (Fin 4) ℝ E)
    (α β : E [⋀^Fin 2]→L[ℝ] ℝ) :
    pairing α β = ∑ i, α ![b (pairLeft i), b (pairRight i)] *
      β ![b (pairLeft i), b (pairRight i)] := by
  have h := (wedgeBasis b).repr.inner_map_map (sharp α) (sharp β)
  rw [pairing, ← h]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, wedgeBasis_repr]
  congr 1
  ext i
  exact mul_comm _ _

end TamingCompatibility.FormMetric

namespace TamingCompatibility.FormMetric
open RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {k : ℕ}

instance formFiniteDimensional : FiniteDimensional ℝ (E [⋀^Fin k]→L[ℝ] ℝ) :=
  FiniteDimensional.of_injective (sharp (E := E) (k := k)) sharp_injective

def sharpCLM : (E [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ⋀[ℝ]^k E :=
  LinearMap.toContinuousLinearMap sharp

def pairingCLM : (E [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] (E [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ :=
  (innerSL ℝ).bilinearComp sharpCLM sharpCLM

def tripleIndices : Fin 4 → Fin 3 → Fin 4 := ![![1,2,3], ![0,2,3], ![0,1,3], ![0,1,2]]

def tripleFamily (b : OrthonormalBasis (Fin 4) ℝ E) (i : Fin 4) : ⋀[ℝ]^3 E :=
  exteriorPower.ιMulti ℝ 3 (fun j => b (tripleIndices i j))

lemma tripleFamily_orthonormal (b : OrthonormalBasis (Fin 4) ℝ E) :
    Orthonormal ℝ (tripleFamily b) := by
  rw [orthonormal_iff_ite]
  intro i j
  simp only [tripleFamily, exteriorPower.inner_ιMulti_ιMulti, Matrix.det_fin_three]
  have hb := orthonormal_iff_ite.mp b.orthonormal
  fin_cases i <;> fin_cases j <;> simp [tripleIndices, hb]

def tripleBasis (b : OrthonormalBasis (Fin 4) ℝ E) :
    OrthonormalBasis (Fin 4) ℝ (⋀[ℝ]^3 E) :=
  OrthonormalBasis.mk (tripleFamily_orthonormal b)
    ((tripleFamily_orthonormal b).linearIndependent.span_eq_top_of_card_eq_finrank (by
      rw [exteriorPower.finrank_eq, Module.finrank_eq_card_basis b.toBasis]
      norm_num [Nat.choose])).ge

lemma tripleBasis_repr (b : OrthonormalBasis (Fin 4) ℝ E)
    (α : E [⋀^Fin 3]→L[ℝ] ℝ) (i : Fin 4) :
    (tripleBasis b).repr (sharp α) i = α (fun j => b (tripleIndices i j)) := by
  rw [OrthonormalBasis.repr_apply_apply, real_inner_comm]
  simp only [tripleBasis, OrthonormalBasis.coe_mk, tripleFamily]
  exact sharp_inner _ _

lemma pairing_three (b : OrthonormalBasis (Fin 4) ℝ E)
    (α β : E [⋀^Fin 3]→L[ℝ] ℝ) :
    pairing α β = ∑ i, α (fun j => b (tripleIndices i j)) *
      β (fun j => b (tripleIndices i j)) := by
  have h := (tripleBasis b).repr.inner_map_map (sharp α) (sharp β)
  rw [pairing, ← h]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, tripleBasis_repr]
  congr 1
  ext i
  exact mul_comm _ _

end TamingCompatibility.FormMetric

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_JAction
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Manifold ContDiff
namespace TamingCompatibility

variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X]

lemma AlmostComplexStructure.injective (J : AlmostComplexStructure X) (x : X) :
    Function.Injective (J.endomorphism x) := by
  intro u v h
  have h' := congrArg (J.endomorphism x) h
  simpa only [J.square, neg_inj] using h'

lemma AlmostComplexStructure.surjective (J : AlmostComplexStructure X) (x : X) :
    Function.Surjective (J.endomorphism x) := by
  intro v
  refine ⟨-J.endomorphism x v, ?_⟩
  rw [map_neg, J.square, neg_neg]

end TamingCompatibility

open scoped Manifold ContDiff Topology
open Filter Set

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_Star
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Manifold ContDiff
open scoped Manifold ContDiff Topology
open Filter Set
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
open scoped Manifold ContDiff Topology
open Bundle Filter Set
open Set
open Bundle Set Filter
open scoped Topology
open Set _root_.MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology
open scoped BigOperators
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open ContinuousAlternatingMap
namespace TamingCompatibility.HodgeThree
open RealInnerProductSpace FormMetric ExteriorForms ContinuousAlternatingMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def star (F : Form (E := E) 2) (α : Form (E := E) 3) : Form (E := E) 1 :=
  ofSubsingletonLIE (0 : Fin 1)
    (-(pairingCLM (E := E) (k := 3) α ∘L (volumeSquare F).curryLeft))

lemma star_apply (F : Form (E := E) 2) (α : Form (E := E) 3) (u : E) :
    star F α ![u] = -pairing α ((volumeSquare F).curryLeft u) := by
  rfl

end TamingCompatibility.HodgeThree

namespace TamingCompatibility.MetricModel
open RealInnerProductSpace
variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

structure Metric where
  bilinear : E →L[ℝ] E →L[ℝ] ℝ
  symm : ∀ u v, bilinear u v = bilinear v u
  positive : ∀ u, u ≠ 0 → 0 < bilinear u u

variable {E}

def Model (_g : Metric E) := E

instance instAddCommGroupModel (g : Metric E) : AddCommGroup (Model g) := inferInstanceAs (AddCommGroup E)
instance instModuleRealModel (g : Metric E) : Module ℝ (Model g) := inferInstanceAs (Module ℝ E)
instance instFiniteDimensionalRealModel (g : Metric E) [FiniteDimensional ℝ E] : FiniteDimensional ℝ (Model g) :=
  inferInstanceAs (FiniteDimensional ℝ E)

instance core (g : Metric E) : InnerProductSpace.Core ℝ (Model g) where
  inner := fun u v => g.bilinear u v
  conj_inner_symm u v := by exact g.symm v u
  add_left u v w := by
    exact congrArg (fun f : E →L[ℝ] ℝ => f w) (map_add g.bilinear (u : E) (v : E))
  smul_left u v c := by
    change g.bilinear (c • (u : E)) (v : E) = c * g.bilinear u v
    exact congrArg (fun f : E →L[ℝ] ℝ => f v) (map_smul g.bilinear c (u : E))
  re_inner_nonneg u := by
    change 0 ≤ g.bilinear u u
    by_cases hu : u = 0
    · rw [hu]
      change 0 ≤ g.bilinear (0 : E) (0 : E)
      simp
    · exact (g.positive u hu).le
  definite u hu := by
    by_contra hn
    exact (ne_of_gt (g.positive u hn)) hu

instance instNormedAddCommGroupModel (g : Metric E) : NormedAddCommGroup (Model g) :=
  InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)

instance instInnerProductSpaceRealModel (g : Metric E) : InnerProductSpace ℝ (Model g) :=
  InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℝ (Model g))

def ofOriginal (g : Metric E) (u : E) : Model g := u

def toOriginal (g : Metric E) (u : Model g) : E := u

def linearEquiv (g : Metric E) : Model g ≃ₗ[ℝ] E := LinearEquiv.refl ℝ E

def equiv [FiniteDimensional ℝ E] (g : Metric E) : Model g ≃L[ℝ] E :=
  (linearEquiv g).toContinuousLinearEquiv

@[simp] lemma equiv_apply [FiniteDimensional ℝ E] (g : Metric E) (u : Model g) : equiv g u = u := rfl
@[simp] lemma equiv_symm_apply [FiniteDimensional ℝ E] (g : Metric E) (u : E) : (equiv g).symm u = u := rfl

lemma finrank_model [FiniteDimensional ℝ E] (g : Metric E) :
    Module.finrank ℝ (Model g) = Module.finrank ℝ E := (linearEquiv g).finrank_eq

def isometry (g : Metric E) (J : E →L[ℝ] E)
    (hJ : ∀ u v, g.bilinear (J u) (J v) = g.bilinear u v) :
    Model g →ₗᵢ[ℝ] Model g where
  toLinearMap :=
    { toFun := fun u => ofOriginal g (J (toOriginal g u))
      map_add' := J.map_add
      map_smul' := J.map_smul }
  norm_map' u := by
    have h : ‖ofOriginal g (J (toOriginal g u))‖ ^ 2 = ‖u‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq (x := ofOriginal g (J (toOriginal g u))),
        ← real_inner_self_eq_norm_sq (x := u)]
      exact hJ u u
    exact (sq_eq_sq₀ (norm_nonneg (ofOriginal g (J (toOriginal g u)))) (norm_nonneg u)).mp h

@[simp] lemma isometry_apply (g : Metric E) (J : E →L[ℝ] E)
    (hJ : ∀ u v, g.bilinear (J u) (J v) = g.bilinear u v) (u : Model g) :
    isometry g J hJ u = J u := rfl

end TamingCompatibility.MetricModel

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_Form
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Manifold ContDiff
open scoped Manifold ContDiff Topology
open Filter Set
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
open scoped Manifold ContDiff Topology
open Bundle Filter Set
open Set
open Bundle Set Filter
open scoped Topology
open Set _root_.MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology
open scoped BigOperators
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open ContinuousAlternatingMap
namespace TamingCompatibility.MetricForms
open scoped BigOperators
open RealInnerProductSpace ContinuousAlternatingMap
open MetricModel
variable {E D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup D] [NormedSpace ℝ D]
  [FiniteDimensional ℝ D]

abbrev Form (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (k : ℕ) :=
  E [⋀^Fin k]→L[ℝ] ℝ

def pairing (g : Metric E) {k : ℕ} (α β : Form E k) : ℝ :=
  FormMetric.pairing (α.compContinuousLinearMap (equiv g).toContinuousLinearMap)
    (β.compContinuousLinearMap (equiv g).toContinuousLinearMap)

def basisOfFrame (g : Metric E) (hdim : Module.finrank ℝ E = 4) (b : Fin 4 → E)
    (hb : ∀ i j, g.bilinear (b i) (b j) = if i = j then 1 else 0) :
    OrthonormalBasis (Fin 4) ℝ (MetricModel.Model g) := by
  let v : Fin 4 → MetricModel.Model g := fun i => ofOriginal g (b i)
  have hv : Orthonormal ℝ v := orthonormal_iff_ite.mpr hb
  exact OrthonormalBasis.mk hv
    (hv.linearIndependent.span_eq_top_of_card_eq_finrank (by
      rw [finrank_model, hdim]; rfl)).ge

@[simp] lemma basisOfFrame_apply (g : Metric E) (hdim : Module.finrank ℝ E = 4)
    (b : Fin 4 → E) (hb : ∀ i j, g.bilinear (b i) (b j) = if i = j then 1 else 0)
    (i : Fin 4) : basisOfFrame g hdim b hb i = ofOriginal g (b i) := by
  simp only [basisOfFrame, OrthonormalBasis.coe_mk]

lemma pairing_two_eq_sum (g : Metric E) (hdim : Module.finrank ℝ E = 4)
    (b : Fin 4 → E) (hb : ∀ i j, g.bilinear (b i) (b j) = if i = j then 1 else 0)
    (α β : Form E 2) :
    pairing g α β = ∑ i, α ![b (FormMetric.pairLeft i), b (FormMetric.pairRight i)] *
      β ![b (FormMetric.pairLeft i), b (FormMetric.pairRight i)] := by
  rw [pairing, FormMetric.pairing_eq_sum (basisOfFrame g hdim b hb)]
  simp only [basisOfFrame_apply, compContinuousLinearMap_apply]
  rfl

lemma pairing_three_eq_sum (g : Metric E) (hdim : Module.finrank ℝ E = 4)
    (b : Fin 4 → E) (hb : ∀ i j, g.bilinear (b i) (b j) = if i = j then 1 else 0)
    (α β : Form E 3) :
    pairing g α β = ∑ i, α (fun j => b (FormMetric.tripleIndices i j)) *
      β (fun j => b (FormMetric.tripleIndices i j)) := by
  rw [pairing, FormMetric.pairing_three (basisOfFrame g hdim b hb)]
  simp only [basisOfFrame_apply, compContinuousLinearMap_apply]
  rfl

def isometryEquiv (g : Metric E) (h : Metric D) (L : E ≃L[ℝ] D)
    (hL : ∀ u v, h.bilinear (L u) (L v) = g.bilinear u v) :
    MetricModel.Model g ≃ₗᵢ[ℝ] MetricModel.Model h :=
  (((equiv g).trans L).trans (equiv h).symm).toLinearEquiv.isometryOfInner hL

@[simp] lemma isometryEquiv_apply (g : Metric E) (h : Metric D) (L : E ≃L[ℝ] D)
    (hL : ∀ u v, h.bilinear (L u) (L v) = g.bilinear u v) (u : MetricModel.Model g) :
    isometryEquiv g h L hL u = L u := rfl

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ D] in
lemma comp_two (α : Form D 2) (L : E →L[ℝ] D) (u v : E) :
    (α.compContinuousLinearMap L) ![u,v] = α ![L u,L v] := by
  change α (fun i => L (![u,v] i)) = _
  congr 1
  ext i
  fin_cases i <;> rfl

end TamingCompatibility.MetricForms

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_AntiInvariantFrame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.AntiInvariantFrame
open ContinuousAlternatingMap MetricModel MetricForms ExteriorForms
open scoped ContDiff
variable {E D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup D] [NormedSpace ℝ D]

omit [FiniteDimensional ℝ E] in
def covectorWedge (a b : E →L[ℝ] ℝ) : MetricForms.Form E 2 :=
  wedgeOne a (ofSubsingletonLIE (0 : Fin 1) b)
omit [FiniteDimensional ℝ E] in
lemma covectorWedge_apply (a b : E →L[ℝ] ℝ) (u v : E) :
    covectorWedge a b ![u,v] = a u * b v - a v * b u := by
  rw [covectorWedge,wedgeOne_apply_two]
  rfl

def realPart (g : Metric E) (b : Fin 4 → E) : MetricForms.Form E 2 :=
  covectorWedge (g.bilinear (b 0)) (g.bilinear (b 2)) -
    covectorWedge (g.bilinear (b 1)) (g.bilinear (b 3))
def imagPart (g : Metric E) (b : Fin 4 → E) : MetricForms.Form E 2 :=
  covectorWedge (g.bilinear (b 0)) (g.bilinear (b 3)) +
    covectorWedge (g.bilinear (b 1)) (g.bilinear (b 2))

omit [FiniteDimensional ℝ E] in
lemma realPart_apply (g : Metric E) (b : Fin 4 → E) (u v : E) :
    realPart g b ![u,v] =
      (g.bilinear (b 0) u * g.bilinear (b 2) v - g.bilinear (b 0) v * g.bilinear (b 2) u) -
      (g.bilinear (b 1) u * g.bilinear (b 3) v - g.bilinear (b 1) v * g.bilinear (b 3) u) := by
  simp only [realPart,ContinuousAlternatingMap.sub_apply,covectorWedge_apply]
omit [FiniteDimensional ℝ E] in
lemma imagPart_apply (g : Metric E) (b : Fin 4 → E) (u v : E) :
    imagPart g b ![u,v] =
      (g.bilinear (b 0) u * g.bilinear (b 3) v - g.bilinear (b 0) v * g.bilinear (b 3) u) +
      (g.bilinear (b 1) u * g.bilinear (b 2) v - g.bilinear (b 1) v * g.bilinear (b 2) u) := by
  simp only [imagPart,ContinuousAlternatingMap.add_apply,covectorWedge_apply]

lemma frame_ext (g : Metric E) (hdim : Module.finrank ℝ E = 4) (b : Fin 4 → E)
    (hb : ∀ i j, g.bilinear (b i) (b j) = if i = j then 1 else 0)
    {a c : MetricForms.Form E 2} (h : ∀ i j, a ![b i,b j] = c ![b i,b j]) : a = c := by
  let B := (basisOfFrame g hdim b hb).toBasis.map (equiv g).toLinearEquiv
  have hB (i : Fin 4) : B i = b i := by
    simp only [B,Module.Basis.map_apply,OrthonormalBasis.coe_toBasis,basisOfFrame_apply]
    rfl
  apply ContinuousAlternatingMap.toContinuousMultilinearMap_injective
  apply ContinuousMultilinearMap.toMultilinearMap_injective
  apply Module.Basis.ext_multilinear (fun _ => B)
  intro v
  change a (fun i => B (v i)) = c (fun i => B (v i))
  have hv : (fun i => B (v i)) = ![b (v 0),b (v 1)] := by
    ext i
    rw [hB]
    fin_cases i <;> rfl
  rw [hv]
  exact h _ _

omit [FiniteDimensional ℝ E] in
lemma eval_neg_left (a : MetricForms.Form E 2) (u v : E) : a ![-u,v] = -a ![u,v] := by
  simpa only [neg_one_smul,smul_eq_mul,neg_one_mul] using a.vecCons_smul ![v] (-1 : ℝ) u
omit [FiniteDimensional ℝ E] in
lemma eval_neg_right (a : MetricForms.Form E 2) (u v : E) : a ![u,-v] = -a ![u,v] := by
  rw [two_swap,eval_neg_left,two_swap,neg_neg]
omit [FiniteDimensional ℝ E] in
lemma eval_self (a : MetricForms.Form E 2) (u : E) : a ![u,u] = 0 :=
  a.map_eq_zero_of_eq ![u,u] (i := 0) (j := 1) rfl (by decide : (0 : Fin 2) ≠ 1)

section Unitary
variable (g : Metric E) (hdim : Module.finrank ℝ E = 4) (b : Fin 4 → E)
  (hb : ∀ i j, g.bilinear (b i) (b j) = if i = j then 1 else 0)
  (J : E →L[ℝ] E) (h0 : J (b 0) = b 1) (h1 : J (b 1) = -b 0)
  (h2 : J (b 2) = b 3) (h3 : J (b 3) = -b 2)

include hdim hb h0 h1 h2 h3 in
lemma expansion (a : MetricForms.Form E 2) (ha : a.compContinuousLinearMap J = -a) :
    a = a ![b 0,b 2] • realPart g b + a ![b 0,b 3] • imagPart g b := by
  have h01 := congrArg (fun c : MetricForms.Form E 2 => c ![b 0,b 1]) ha
  have h23 := congrArg (fun c : MetricForms.Form E 2 => c ![b 2,b 3]) ha
  have h02 := congrArg (fun c : MetricForms.Form E 2 => c ![b 0,b 2]) ha
  have h03 := congrArg (fun c : MetricForms.Form E 2 => c ![b 0,b 3]) ha
  simp only [MetricForms.comp_two,h0,h1,h2,h3,eval_neg_right,
    ContinuousAlternatingMap.neg_apply] at h01 h23 h02 h03
  rw [two_swap] at h01 h23
  have hz01 : a ![b 0,b 1] = 0 := by linarith
  have hz23 : a ![b 2,b 3] = 0 := by linarith
  have he12 : a ![b 1,b 2] = a ![b 0,b 3] := by linarith
  apply frame_ext g hdim b hb
  intro i j
  simp only [ContinuousAlternatingMap.add_apply,ContinuousAlternatingMap.smul_apply,
    smul_eq_mul,realPart_apply,imagPart_apply,hb]
  fin_cases i <;> fin_cases j
  all_goals simp [eval_self, hz01, hz23, h02, he12]
  all_goals first | rw [two_swap a (b 0) (b 1), hz01] <;> simp
                  | rw [two_swap a (b 0) (b 2)]
                  | rw [two_swap a (b 0) (b 3)]
                  | rw [two_swap a (b 1) (b 2), he12]
                  | rw [two_swap a (b 1) (b 3), h02] <;> simp
                  | rw [two_swap a (b 2) (b 3), hz23]; simp

end Unitary

lemma realPart_smooth {g : D → Metric E} {b : Fin 4 → D → E} {U : Set D}
    (hg : ContDiffOn ℝ ∞ (fun x => (g x).bilinear) U)
    (hb : ∀ i, ContDiffOn ℝ ∞ (b i) U) :
    ContDiffOn ℝ ∞ (fun x => realPart (g x) (fun i => b i x)) U := by
  apply FormSmooth.contDiffOn_of_basis (Module.finBasis ℝ E)
  intro a
  have hv : (fun i => Module.finBasis ℝ E (a i)) =
      ![Module.finBasis ℝ E (a 0),Module.finBasis ℝ E (a 1)] := by ext i; fin_cases i <;> rfl
  simp only [hv,realPart_apply]
  exact (((hg.clm_apply (hb 0)).clm_apply contDiffOn_const).mul
    ((hg.clm_apply (hb 2)).clm_apply contDiffOn_const)).sub
    (((hg.clm_apply (hb 0)).clm_apply contDiffOn_const).mul
    ((hg.clm_apply (hb 2)).clm_apply contDiffOn_const)) |>.sub
    ((((hg.clm_apply (hb 1)).clm_apply contDiffOn_const).mul
    ((hg.clm_apply (hb 3)).clm_apply contDiffOn_const)).sub
    (((hg.clm_apply (hb 1)).clm_apply contDiffOn_const).mul
    ((hg.clm_apply (hb 3)).clm_apply contDiffOn_const)))
lemma imagPart_smooth {g : D → Metric E} {b : Fin 4 → D → E} {U : Set D}
    (hg : ContDiffOn ℝ ∞ (fun x => (g x).bilinear) U)
    (hb : ∀ i, ContDiffOn ℝ ∞ (b i) U) :
    ContDiffOn ℝ ∞ (fun x => imagPart (g x) (fun i => b i x)) U := by
  apply FormSmooth.contDiffOn_of_basis (Module.finBasis ℝ E)
  intro a
  have hv : (fun i => Module.finBasis ℝ E (a i)) =
      ![Module.finBasis ℝ E (a 0),Module.finBasis ℝ E (a 1)] := by ext i; fin_cases i <;> rfl
  simp only [hv,imagPart_apply]
  exact (((hg.clm_apply (hb 0)).clm_apply contDiffOn_const).mul
    ((hg.clm_apply (hb 3)).clm_apply contDiffOn_const)).sub
    (((hg.clm_apply (hb 0)).clm_apply contDiffOn_const).mul
    ((hg.clm_apply (hb 3)).clm_apply contDiffOn_const)) |>.add
    ((((hg.clm_apply (hb 1)).clm_apply contDiffOn_const).mul
    ((hg.clm_apply (hb 2)).clm_apply contDiffOn_const)).sub
    (((hg.clm_apply (hb 1)).clm_apply contDiffOn_const).mul
    ((hg.clm_apply (hb 2)).clm_apply contDiffOn_const)))
end TamingCompatibility.AntiInvariantFrame

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_Linear
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace TamingCompatibility.ExteriorForms
open ContinuousAlternatingMap
open scoped ContDiff
variable {E D P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup P] [NormedSpace ℝ P]
  {k : ℕ}

def wedgeOneBilinear : Form (E := E) 1 →L[ℝ] Form (E := E) k →L[ℝ] Form (E := E) (k+1) :=
  ((ContinuousLinearMap.compL ℝ (Form (E := E) k) (E →L[ℝ] Form (E := E) k)
    (Form (E := E) (k+1))) (alternatizeUncurryFinCLM ℝ E ℝ)) ∘L
    ContinuousLinearMap.smulRightL ℝ E (Form (E := E) k) ∘L
      (ofSubsingletonLIE (0 : Fin 1)).symm.toContinuousLinearEquiv.toContinuousLinearMap

end TamingCompatibility.ExteriorForms

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_FormEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Manifold ContDiff
open scoped Manifold ContDiff Topology
open Filter Set
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
open scoped Manifold ContDiff Topology
open Bundle Filter Set
open Set
open Bundle Set Filter
open scoped Topology
open Set _root_.MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology
open scoped BigOperators
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open ContinuousAlternatingMap
namespace TamingCompatibility.MetricHodge
open ContinuousAlternatingMap MetricForms MetricModel ExteriorForms
variable {E D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup D] [NormedSpace ℝ D]
  [FiniteDimensional ℝ D]

def formEquiv (g : Metric E) (k : ℕ) :
    MetricForms.Form E k ≃L[ℝ] MetricForms.Form (MetricModel.Model g) k :=
  (equiv g).symm.continuousAlternatingMapCongrLeft

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ D] in
lemma volumeSquare_comp (F : MetricForms.Form D 2) (L : E →L[ℝ] D) :
    volumeSquare (F.compContinuousLinearMap L) = (volumeSquare F).compContinuousLinearMap L := by
  ext v
  have hv : v = ![v 0,v 1,v 2,v 3] := by ext i; fin_cases i <;> rfl
  rw [hv, volumeSquare_apply]
  have hc : ((volumeSquare F).compContinuousLinearMap L) ![v 0,v 1,v 2,v 3] =
      volumeSquare F ![L (v 0), L (v 1), L (v 2), L (v 3)] := by
    change volumeSquare F (fun i => L (![v 0,v 1,v 2,v 3] i)) = _
    congr 1
    ext i
    fin_cases i <;> rfl
  rw [hc,volumeSquare_apply]
  simp only [MetricForms.comp_two]

def starThree (g : Metric E) (F : MetricForms.Form E 2) (α : MetricForms.Form E 3) :
    MetricForms.Form E 1 :=
  (formEquiv g 1).symm (HodgeThree.star (formEquiv g 2 F) (formEquiv g 3 α))

lemma starThree_apply (g : Metric E) (F : MetricForms.Form E 2) (α : MetricForms.Form E 3) (u : E) :
    starThree g F α ![u] = -pairing g α ((volumeSquare F).curryLeft u) := by
  change HodgeThree.star (formEquiv g 2 F) (formEquiv g 3 α)
    ((fun i => (equiv g).symm (![u] i))) = _
  have hv : (fun i => (equiv g).symm (![u] i)) = ![(equiv g).symm u] := by
    ext i; fin_cases i; rfl
  rw [hv,HodgeThree.star_apply]
  congr 1
  change FormMetric.pairing _ _ = FormMetric.pairing _ _
  congr 1
  change (volumeSquare (F.compContinuousLinearMap (equiv g))).curryLeft ((equiv g).symm u) =
    ((volumeSquare F).curryLeft u).compContinuousLinearMap (equiv g)
  rw [volumeSquare_comp]
  ext v
  change volumeSquare F (fun i => (equiv g) ((Matrix.vecCons ((equiv g).symm u) v) i)) =
    volumeSquare F (Matrix.vecCons u (fun i => (equiv g) (v i)))
  congr 1

end TamingCompatibility.MetricHodge

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_SingleFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped Manifold ContDiff
open scoped Manifold ContDiff Topology
open Filter Set
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
open scoped Manifold ContDiff Topology
open Bundle Filter Set
open Set
open Bundle Set Filter
open scoped Topology
open Set _root_.MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology
open scoped BigOperators
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open ContinuousAlternatingMap
namespace TamingCompatibility.FormMetric
open RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def singleFamily (b : OrthonormalBasis (Fin 4) ℝ E) (i : Fin 4) : ⋀[ℝ]^1 E :=
  exteriorPower.ιMulti ℝ 1 ![b i]

lemma singleFamily_orthonormal (b : OrthonormalBasis (Fin 4) ℝ E) : Orthonormal ℝ (singleFamily b) := by
  rw [orthonormal_iff_ite]
  intro i j
  simpa [singleFamily,exteriorPower.inner_ιMulti_ιMulti,Matrix.det_fin_one] using
    orthonormal_iff_ite.mp b.orthonormal i j

def singleBasis (b : OrthonormalBasis (Fin 4) ℝ E) : OrthonormalBasis (Fin 4) ℝ (⋀[ℝ]^1 E) :=
  OrthonormalBasis.mk (singleFamily_orthonormal b)
    ((singleFamily_orthonormal b).linearIndependent.span_eq_top_of_card_eq_finrank (by
      rw [exteriorPower.finrank_eq,Module.finrank_eq_card_basis b.toBasis]
      norm_num)).ge

lemma singleBasis_repr (b : OrthonormalBasis (Fin 4) ℝ E) (a : E [⋀^Fin 1]→L[ℝ] ℝ) (i : Fin 4) :
    (singleBasis b).repr (sharp a) i = a ![b i] := by
  rw [OrthonormalBasis.repr_apply_apply,real_inner_comm]
  simp only [singleBasis,OrthonormalBasis.coe_mk,singleFamily]
  exact sharp_inner _ _

lemma pairing_one (b : OrthonormalBasis (Fin 4) ℝ E) (a c : E [⋀^Fin 1]→L[ℝ] ℝ) :
    pairing a c = ∑ i, a ![b i] * c ![b i] := by
  have h := (singleBasis b).repr.inner_map_map (sharp a) (sharp c)
  rw [pairing,← h]
  simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,singleBasis_repr]
  congr 1
  ext i
  exact mul_comm _ _
end TamingCompatibility.FormMetric

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_ComplexEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped Manifold ContDiff
open scoped Manifold ContDiff Topology
open Filter Set
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
open scoped Manifold ContDiff Topology
open Bundle Filter Set
open Set
open Bundle Set Filter
open scoped Topology
open Set _root_.MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology
open scoped BigOperators
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open ContinuousAlternatingMap

namespace TamingCompatibility.MetricForms
open ContinuousAlternatingMap MetricModel
variable {E D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup D] [NormedSpace ℝ D]
  [FiniteDimensional ℝ D]
lemma pairing_one_eq_sum (g : Metric E) (hdim : Module.finrank ℝ E = 4)
    (b : Fin 4 → E) (hb : ∀ i j, g.bilinear (b i) (b j) = if i = j then 1 else 0)
    (α β : Form E 1) : pairing g α β = ∑ i, α ![b i] * β ![b i] := by
  rw [pairing,FormMetric.pairing_one (basisOfFrame g hdim b hb)]
  simp only [basisOfFrame_apply,compContinuousLinearMap_apply]
  rfl
end TamingCompatibility.MetricForms

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_LocalCodifferential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section

section

noncomputable section
namespace TamingCompatibility.MetricForms
open MetricModel ContinuousAlternatingMap
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
lemma pairing_add_left (g : Metric E) {k : ℕ} (a b c : Form E k) :
    pairing g (a+b) c = pairing g a c + pairing g b c := by
  change FormMetric.pairing (MetricHodge.formEquiv g k (a+b)) (MetricHodge.formEquiv g k c) = _
  rw [_root_.map_add]
  simp only [FormMetric.pairing,_root_.map_add,inner_add_left]
  rfl
end TamingCompatibility.MetricForms

namespace TamingCompatibility.MetricHodge
open MetricModel MetricForms ContinuousAlternatingMap
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

lemma starThree_add (g : Metric E) (F : MetricForms.Form E 2) (a b : MetricForms.Form E 3) :
    starThree g F (a+b) = starThree g F a + starThree g F b := by
  ext v
  have hv : v = ![v 0] := by ext i; fin_cases i; rfl
  rw [hv,ContinuousAlternatingMap.add_apply,starThree_apply,starThree_apply,starThree_apply,
    pairing_add_left]
  ring
end TamingCompatibility.MetricHodge

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_LocalFrameOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.AntiInvariantFrame
open MetricModel MetricForms MetricHodge ExteriorForms ContinuousAlternatingMap
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable (g : Metric E) (hdim : Module.finrank ℝ E = 4) (b : Fin 4 → E)
  (hb : ∀ i j, g.bilinear (b i) (b j) = if i = j then 1 else 0)
  (J : E →L[ℝ] E) (h0 : J (b 0) = b 1) (h1 : J (b 1) = -b 0)
  (h2 : J (b 2) = b 3) (h3 : J (b 3) = -b 2)
  (F : MetricForms.Form E 2) (hF : ∀ u v, F ![u,v] = g.bilinear (J u) v)

include hb h0 h1 h2 h3 hF in
omit [FiniteDimensional ℝ E] in
lemma volume_on_frame (i j : Fin 4) :
    (volumeSquare F).curryLeft (b i) (fun l => b (FormMetric.tripleIndices j l)) =
      if i = j then (-1 : ℝ) ^ (i : ℕ) else 0 := by
  have ht : (volumeSquare F).curryLeft (b i) (fun l => b (FormMetric.tripleIndices j l)) =
      (volumeSquare F) ![b i, b (FormMetric.tripleIndices j 0), b (FormMetric.tripleIndices j 1),
        b (FormMetric.tripleIndices j 2)] := by
    change (volumeSquare F) (Matrix.vecCons (b i) (fun l => b (FormMetric.tripleIndices j l))) = _
    congr 1
    ext l
    fin_cases l <;> rfl
  rw [ht, volumeSquare_apply]
  fin_cases i <;> fin_cases j <;>
    simp [FormMetric.tripleIndices, hF, h0, h1, h2, h3, hb]
  norm_num

include hdim hb h0 h1 h2 h3 hF in
lemma starThree_on_frame (a : MetricForms.Form E 3) (i : Fin 4) :
    starThree g F a ![b i] =
      -((-1 : ℝ) ^ (i : ℕ) * a (fun l => b (FormMetric.tripleIndices i l))) := by
  rw [starThree_apply, pairing_three_eq_sum g hdim b hb]
  simp_rw [volume_on_frame g b hb J h0 h1 h2 h3 F hF]
  simp [mul_comm]

include hdim hb h0 h1 h2 h3 hF in
lemma star_wedge_real (ξ : E →L[ℝ] ℝ) (i : Fin 4) :
    starThree g F (wedgeOne ξ (realPart g b)) ![b i] =
      ![-ξ (b 2), ξ (b 3), ξ (b 0), -ξ (b 1)] i := by
  rw [starThree_on_frame g hdim b hb J h0 h1 h2 h3 F hF]
  have ht (i : Fin 4) : (fun l => b (FormMetric.tripleIndices i l)) =
      ![b (FormMetric.tripleIndices i 0),b (FormMetric.tripleIndices i 1),b (FormMetric.tripleIndices i 2)] := by
    ext l
    fin_cases l <;> rfl
  rw [ht, wedgeOne_apply_three]
  fin_cases i <;> simp [FormMetric.tripleIndices, realPart_apply, hb]
  norm_num

include hdim hb h0 h1 h2 h3 hF in
lemma star_wedge_imag (ξ : E →L[ℝ] ℝ) (i : Fin 4) :
    starThree g F (wedgeOne ξ (imagPart g b)) ![b i] =
      ![-ξ (b 3), -ξ (b 2), ξ (b 1), ξ (b 0)] i := by
  rw [starThree_on_frame g hdim b hb J h0 h1 h2 h3 F hF]
  have ht (i : Fin 4) : (fun l => b (FormMetric.tripleIndices i l)) =
      ![b (FormMetric.tripleIndices i 0),b (FormMetric.tripleIndices i 1),b (FormMetric.tripleIndices i 2)] := by
    ext l
    fin_cases l <;> rfl
  rw [ht, wedgeOne_apply_three]
  fin_cases i <;> simp [FormMetric.tripleIndices, imagPart_apply, hb]
  norm_num
end TamingCompatibility.AntiInvariantFrame

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Concentration_ActivationScales
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Filter _root_.MeasureTheory
open scoped Topology ENNReal
namespace TamingCompatibility.SummableCutoff

def stepSize (n : ℕ) : ℝ := (1/2)^n
end TamingCompatibility.SummableCutoff

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_FramePairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section

section

noncomputable section
namespace TamingCompatibility.AntiInvariantFrame
open ContinuousAlternatingMap MetricModel MetricForms
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

lemma pairing_combination (g : Metric E) (hdim : Module.finrank ℝ E = 4)
    (b : Fin 4 → E) (hb : ∀ i j, g.bilinear (b i) (b j) = if i=j then 1 else 0)
    (A B : ℝ) :
    pairing g (A • realPart g b + B • imagPart g b) (A • realPart g b + B • imagPart g b) =
      2 * (A^2+B^2) := by
  rw [pairing_two_eq_sum g hdim b hb]
  simp only [ContinuousAlternatingMap.add_apply,ContinuousAlternatingMap.smul_apply,smul_eq_mul,
    realPart_apply,imagPart_apply,hb]
  simp [Fin.sum_univ_succ,FormMetric.pairLeft,FormMetric.pairRight]
  ring
end TamingCompatibility.AntiInvariantFrame

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_ClosureLinear
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.ClosureLinear
open Set
variable {E F : Type*} [AddCommGroup E] [Module ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
def toClosure (f : E →ₗ[ℝ] F) : E →ₗ[ℝ] f.range.topologicalClosure :=
  f.codRestrict _ (fun x => Submodule.le_topologicalClosure _ (LinearMap.mem_range_self f x))
end TamingCompatibility.ClosureLinear

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_SmoothGeometricInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace InjectiveLinearLift
variable {R E F G : Type*} [Semiring R] [AddCommMonoid E] [AddCommMonoid F]
  [AddCommMonoid G] [Module R E] [Module R F] [Module R G]

def lift (i : E →ₗ[R] F) (hi : Function.Injective i) (j : G →ₗ[R] F)
    (h : ∀ g, ∃ e, i e = j g) : G →ₗ[R] E where
  toFun g := Classical.choose (h g)
  map_add' a b := hi (by rw [Classical.choose_spec (h (a+b)),map_add,map_add,
    Classical.choose_spec (h a),Classical.choose_spec (h b)])
  map_smul' r a := hi (by rw [Classical.choose_spec (h (r • a)),map_smul,map_smul,
    Classical.choose_spec (h a)]; rfl)

lemma lift_spec (i : E →ₗ[R] F) (hi : Function.Injective i) (j : G →ₗ[R] F)
    (h : ∀ g, ∃ e, i e = j g) (g : G) : i (lift i hi j h g) = j g :=
  Classical.choose_spec (h g)
end InjectiveLinearLift


end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_ClosedGraphLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace InjectiveLinearLift
variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] [CompleteSpace G]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [T2Space F]

def continuousLift (i : E →L[𝕜] F) (hi : Function.Injective i)
    (j : G →L[𝕜] F) (h : ∀ g, ∃ e, i e = j g) : G →L[𝕜] E := by
  let l := lift i.toLinearMap hi j.toLinearMap h
  apply ContinuousLinearMap.ofIsClosedGraph (g := l)
  have he : (l.graph : Set (G × E)) = {p | i p.2 = j p.1} := by
    ext p
    change p.2 = l p.1 ↔ i p.2 = j p.1
    constructor
    · intro hp
      rw [hp]
      exact lift_spec i.toLinearMap hi j.toLinearMap h p.1
    · intro hp
      apply hi
      exact hp.trans (lift_spec i.toLinearMap hi j.toLinearMap h p.1).symm
  rw [he]
  exact isClosed_eq (i.continuous.comp continuous_snd) (j.continuous.comp continuous_fst)

lemma continuousLift_spec (i : E →L[𝕜] F) (hi : Function.Injective i)
    (j : G →L[𝕜] F) (h : ∀ g, ∃ e, i e = j g) (g : G) :
    i (continuousLift i hi j h g) = j g :=
  lift_spec i.toLinearMap hi j.toLinearMap h g
end InjectiveLinearLift


end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_QuadraticShell
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open _root_.MeasureTheory Set Filter
open scoped ENNReal Topology
namespace QuadraticShell

def profile (r : ℝ) (d : ℝ≥0∞) : ℝ≥0∞ := (1 + d / ENNReal.ofReal r)⁻¹ ^ 6

end QuadraticShell

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_HeatFlow_ResolventTaylor
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
namespace ResolventTaylor
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
open scoped BigOperators

def second (L : E →ₗ[ℝ] E) (t : ℝ) (a : E) : E :=
  a-(3*t) • L a+(6*t^2) • ((L^2) a)

end ResolventTaylor

end
end

end
end

end OAI
end


