-- Prove2me | Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_H1
-- name    : RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_H1
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T19:33:21.399166+00:00
-- url     : https://prove2.me/theorems/11698d4d-ca60-412b-92a9-c26acc2a5c7d
-- title:
--   H1
-- statement:
--   Definitions and structural lemmas for H1, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/upstream-config/patches/rellich-kondrachov-lean4341.patch

import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Topology.Algebra.Support
set_option autoImplicit true
namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean
open scoped ENNReal MeasureTheory
open MeasureTheory
section
variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
local instance instMeasurableSpaceH1 : MeasurableSpace E := borel E
local instance instBorelSpaceH1 : BorelSpace E := ⟨rfl⟩
local instance instOpensMeasurableSpaceH1 : OpensMeasurableSpace E := by infer_instance
variable (μ : Measure E) [IsFiniteMeasureOnCompacts μ]
abbrev L2ℝ : Type _ := ↥(E →₂[μ] ℝ)
abbrev L2E : Type _ := ↥(E →₂[μ] E)
abbrev H1Target : Type _ := L2ℝ (μ := μ) × L2E (μ := μ)
def C1c : Submodule ℝ (E → ℝ) where
  carrier := {f | ContDiff ℝ 1 f ∧ HasCompactSupport f}
  zero_mem' := by
    refine ⟨contDiff_const, ?_⟩
    simpa using (HasCompactSupport.zero : HasCompactSupport (fun _ : E => (0 : ℝ)))
  add_mem' := by
    intro f g hf hg
    refine ⟨hf.1.add hg.1, hf.2.add hg.2⟩
  smul_mem' := by
    intro c f hf
    refine ⟨hf.1.const_smul c, ?_⟩
    -- `HasCompactSupport` is stable under pointwise scalar multiplication.
    exact (HasCompactSupport.smul_left (f := fun _ : E => c) hf.2)
noncomputable def grad (f : E → ℝ) : E → E :=
  fun x => (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x)
lemma continuous_grad {f : E → ℝ} (hf : ContDiff ℝ 1 f) : Continuous (grad (E := E) f) := by
  have hcont : Continuous (fderiv ℝ f) := hf.continuous_fderiv one_ne_zero
  have : Continuous fun x => (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x) :=
    (InnerProductSpace.toDual ℝ E).symm.continuous.comp hcont
  exact this
lemma hasCompactSupport_grad {f : E → ℝ} (hf : HasCompactSupport f) :
    HasCompactSupport (grad (E := E) f) := by
  -- Outside the support of `f`, `fderiv` is identically `0`, hence so is `grad`.
  have hf' : HasCompactSupport (fderiv ℝ f) := hf.fderiv ℝ
  -- `grad` is composition with a linear map sending `0` to `0`.
  exact
    (HasCompactSupport.comp_left (f := fderiv ℝ f) (g := (InnerProductSpace.toDual ℝ E).symm)
      hf' (by simp))
omit [CompleteSpace E] in
lemma memLp_of_mem_C1c {f : E → ℝ} (hf : f ∈ C1c (E := E)) : MemLp f 2 μ := by
  exact (hf.1.continuous.memLp_of_hasCompactSupport (μ := μ) (p := (2 : ℝ≥0∞)) hf.2)
lemma memLp_grad_of_mem_C1c {f : E → ℝ} (hf : f ∈ C1c (E := E)) :
    MemLp (grad (E := E) f) 2 μ := by
  have hcont : Continuous (grad (E := E) f) := continuous_grad (E := E) (f := f) hf.1
  have hcs : HasCompactSupport (grad (E := E) f) := hasCompactSupport_grad (E := E) (f := f) hf.2
  exact hcont.memLp_of_hasCompactSupport (μ := μ) (p := (2 : ℝ≥0∞)) hcs
noncomputable def toL2 (f : ↥(C1c (E := E))) : L2ℝ (μ := μ) :=
  (memLp_of_mem_C1c (μ := μ) (E := E) f.2).toLp f.1
noncomputable def toL2Grad (f : ↥(C1c (E := E))) : L2E (μ := μ) :=
  (memLp_grad_of_mem_C1c (μ := μ) (E := E) f.2).toLp (grad (E := E) f.1)
omit [CompleteSpace E] in
lemma toL2_add (f g : ↥(C1c (E := E))) :
    toL2 (μ := μ) (E := E) (f + g) =
      toL2 (μ := μ) (E := E) f + toL2 (μ := μ) (E := E) g := by
  apply Lp.ext
  have hf : (toL2 (μ := μ) (E := E) f : E → ℝ) =ᵐ[μ] f.1 :=
    (memLp_of_mem_C1c (μ := μ) (E := E) f.2).coeFn_toLp
  have hg : (toL2 (μ := μ) (E := E) g : E → ℝ) =ᵐ[μ] g.1 :=
    (memLp_of_mem_C1c (μ := μ) (E := E) g.2).coeFn_toLp
  have hfg : (toL2 (μ := μ) (E := E) (f + g) : E → ℝ) =ᵐ[μ] (f.1 + g.1) :=
    (memLp_of_mem_C1c (μ := μ) (E := E) (f + g).2).coeFn_toLp
  -- Both sides agree a.e. with `f + g`.
  refine hfg.trans ?_
  filter_upwards [Lp.coeFn_add (toL2 (μ := μ) (E := E) f) (toL2 (μ := μ) (E := E) g), hf, hg]
    with x hxadd hxf hxg
  -- Rewrite both sides in terms of pointwise evaluation.
  calc
    f.1 x + g.1 x =
        (toL2 (μ := μ) (E := E) f : E → ℝ) x +
          (toL2 (μ := μ) (E := E) g : E → ℝ) x := by
      simp [hxf, hxg]
    _ = ((toL2 (μ := μ) (E := E) f + toL2 (μ := μ) (E := E) g : L2ℝ (μ := μ)) : E → ℝ) x := by
      simpa [Pi.add_apply] using hxadd.symm
omit [CompleteSpace E] in
lemma toL2_smul (c : ℝ) (f : ↥(C1c (E := E))) :
    toL2 (μ := μ) (E := E) (c • f) = c • toL2 (μ := μ) (E := E) f := by
  apply Lp.ext
  have hf : (toL2 (μ := μ) (E := E) f : E → ℝ) =ᵐ[μ] f.1 :=
    (memLp_of_mem_C1c (μ := μ) (E := E) f.2).coeFn_toLp
  have hcf : (toL2 (μ := μ) (E := E) (c • f) : E → ℝ) =ᵐ[μ] (c • f.1) :=
    (memLp_of_mem_C1c (μ := μ) (E := E) (c • f).2).coeFn_toLp
  refine hcf.trans ?_
  filter_upwards [Lp.coeFn_smul c (toL2 (μ := μ) (E := E) f), hf] with x hxsmul hxf
  simp [Pi.smul_apply, hxsmul, hxf]
noncomputable def toL2Linear : ↥(C1c (E := E)) →ₗ[ℝ] L2ℝ (μ := μ) where
  toFun := toL2 (μ := μ) (E := E)
  map_add' := by exact toL2_add (μ := μ) (E := E)
  map_smul' := by exact toL2_smul (μ := μ) (E := E)
lemma toL2Grad_add (f g : ↥(C1c (E := E))) :
    toL2Grad (μ := μ) (E := E) (f + g) =
      toL2Grad (μ := μ) (E := E) f + toL2Grad (μ := μ) (E := E) g := by
  apply Lp.ext
  have hf : (toL2Grad (μ := μ) (E := E) f : E → E) =ᵐ[μ] grad (E := E) f.1 :=
    (memLp_grad_of_mem_C1c (μ := μ) (E := E) f.2).coeFn_toLp
  have hg : (toL2Grad (μ := μ) (E := E) g : E → E) =ᵐ[μ] grad (E := E) g.1 :=
    (memLp_grad_of_mem_C1c (μ := μ) (E := E) g.2).coeFn_toLp
  have hfg :
      (toL2Grad (μ := μ) (E := E) (f + g) : E → E) =ᵐ[μ] grad (E := E) (f.1 + g.1) :=
    (memLp_grad_of_mem_C1c (μ := μ) (E := E) (f + g).2).coeFn_toLp
  refine hfg.trans ?_
  filter_upwards [Lp.coeFn_add (toL2Grad (μ := μ) (E := E) f) (toL2Grad (μ := μ) (E := E) g), hf,
    hg] with x hxadd hxf hxg
  have hdf : DifferentiableAt ℝ f.1 x :=
    (f.2.1.differentiable one_ne_zero).differentiableAt
  have hdg : DifferentiableAt ℝ g.1 x :=
    (g.2.1.differentiable one_ne_zero).differentiableAt
  -- Rewrite in terms of pointwise evaluation and use linearity of `grad`.
  have hgrad :
      grad (E := E) (f.1 + g.1) x = grad (E := E) f.1 x + grad (E := E) g.1 x := by
    simp [grad, fderiv_add hdf hdg, map_add]
  calc
    grad (E := E) (f.1 + g.1) x = grad (E := E) f.1 x + grad (E := E) g.1 x := hgrad
    _ =
        (toL2Grad (μ := μ) (E := E) f : E → E) x +
          (toL2Grad (μ := μ) (E := E) g : E → E) x := by
        simp [hxf, hxg]
    _ = ((toL2Grad (μ := μ) (E := E) f +
            toL2Grad (μ := μ) (E := E) g : L2E (μ := μ)) :
            E → E) x := by
        simpa [Pi.add_apply] using hxadd.symm
lemma toL2Grad_smul (c : ℝ) (f : ↥(C1c (E := E))) :
    toL2Grad (μ := μ) (E := E) (c • f) = c • toL2Grad (μ := μ) (E := E) f := by
  apply Lp.ext
  have hf : (toL2Grad (μ := μ) (E := E) f : E → E) =ᵐ[μ] grad (E := E) f.1 :=
    (memLp_grad_of_mem_C1c (μ := μ) (E := E) f.2).coeFn_toLp
  have hcf :
      (toL2Grad (μ := μ) (E := E) (c • f) : E → E) =ᵐ[μ] grad (E := E) (c • f.1) :=
    (memLp_grad_of_mem_C1c (μ := μ) (E := E) (c • f).2).coeFn_toLp
  refine hcf.trans ?_
  filter_upwards [Lp.coeFn_smul c (toL2Grad (μ := μ) (E := E) f), hf] with x hxsmul hxf
  have hdf : DifferentiableAt ℝ f.1 x :=
    (f.2.1.differentiable one_ne_zero).differentiableAt
  have hgrad : grad (E := E) (c • f.1) x = c • grad (E := E) f.1 x := by
    simp [grad, fderiv_const_smul hdf, map_smul]
  calc
    grad (E := E) (c • f.1) x = c • grad (E := E) f.1 x := hgrad
    _ = c • (toL2Grad (μ := μ) (E := E) f : E → E) x := by
      simp [hxf]
    _ = ((c • toL2Grad (μ := μ) (E := E) f : L2E (μ := μ)) : E → E) x := by
      -- `Lp.coeFn_smul` gives the pointwise evaluation of `c • f` in `L²`.
      simpa [Pi.smul_apply] using hxsmul.symm
noncomputable def toL2GradLinear : ↥(C1c (E := E)) →ₗ[ℝ] L2E (μ := μ) where
  toFun := toL2Grad (μ := μ) (E := E)
  map_add' := by exact toL2Grad_add (μ := μ) (E := E)
  map_smul' := by exact toL2Grad_smul (μ := μ) (E := E)
noncomputable def graph : ↥(C1c (E := E)) →ₗ[ℝ] H1Target (μ := μ) :=
  (toL2Linear (μ := μ) (E := E)).prod (toL2GradLinear (μ := μ) (E := E))
noncomputable def h1 : Submodule ℝ (H1Target (μ := μ)) :=
  (LinearMap.range (graph (μ := μ) (E := E))).topologicalClosure
theorem isClosed_h1 : IsClosed (h1 (μ := μ) (E := E) : Set (H1Target (μ := μ))) := by
  delta h1
  exact Submodule.isClosed_topologicalClosure (LinearMap.range (graph (μ := μ) (E := E)))
instance instCompleteSpaceh1 : CompleteSpace (↥(h1 (μ := μ) (E := E))) := by
  classical
  exact (isClosed_h1 (μ := μ) (E := E)).isComplete.completeSpace_coe
noncomputable def h1ToL2 : (↥(h1 (μ := μ) (E := E))) →L[ℝ] L2ℝ (μ := μ) :=
  (ContinuousLinearMap.fst ℝ (L2ℝ (μ := μ)) (L2E (μ := μ))).comp
    (Submodule.subtypeL (h1 (μ := μ) (E := E)))
noncomputable def h1ToL2Grad : (↥(h1 (μ := μ) (E := E))) →L[ℝ] L2E (μ := μ) :=
  (ContinuousLinearMap.snd ℝ (L2ℝ (μ := μ)) (L2E (μ := μ))).comp
    (Submodule.subtypeL (h1 (μ := μ) (E := E)))
end
end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov


