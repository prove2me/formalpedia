-- Prove2me | Definitions.Def_OAI_Analysis_ModularRecovery_StrongLimits
-- name    : OAI_Analysis_ModularRecovery_StrongLimits
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T14:39:58.834917+00:00
-- url     : https://prove2.me/theorems/388809cd-15c6-48f8-931f-ea6e75253104
-- title:
--   Strong limits of spectral multipliers
-- statement:
--   These notions belong to a formal proof of a bounded recovery theorem in Tomita–Takesaki theory. Let $M$ be a von Neumann algebra on a Hilbert space $H$ with a cyclic and separating unit vector $\xi$, and let $\varphi(a)=\langle\xi,a\xi\rangle$. The modular data are encoded by a nondegenerate $*$-homomorphism $f\mapsto f(D)$ from bounded continuous functions on $\mathbb R$ to bounded operators, thought of as the functional calculus of $D=\log\Delta$. It comes with the unitary group $\Delta^{it}=e^{itD}$, the modular automorphisms $\sigma_t(a)=\Delta^{it}a\Delta^{-it}$, and an antiunitary involution $J$. The Tomita relation requires the closure of $\{(a\xi,a^*\xi):a\in M\}$ to be the graph of $J\Delta^{1/2}$. The theorem says that when $\varphi$ has trivial centralizer, a vector in a narrow spectral band of $D$ on which an operator $T$ is not small can be replaced by $v\xi$, with $v\in M$ uniformly bounded and $v\xi$ in a comparable band.
--
--   This module has no new definitions. It proves two strong-limit facts. First, bounded functions $f_n$ with $f_nq\to gq$ uniformly, for every compactly supported $q$, have $f_n(D)h\to g(D)h$ for every vector $h$; this uses nondegeneracy of the calculus. Second, the Gaussian kernel multipliers converge strongly:
--   $$
--   \Bigl(\int g_n(r)e^{itr}\kappa(r-\cdot)\,dr\Bigr)(D)\ \longrightarrow\ \hat\kappa(t)\,\Delta^{it} .
--   $$
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/ModularRecovery/StrongLimits.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ModularRecovery/StrongLimits.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the BoundedRecovery mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_BoundedRecovery
import Definitions.Def_OAI_Analysis_ModularRecovery_Model
import Definitions.Def_OAI_Analysis_ModularRecovery_SpectralCalculus
import Definitions.Def_OAI_Analysis_ModularRecovery_TomitaResolvent
import Definitions.Def_OAI_Analysis_ModularRecovery_PolarCutoff
import Definitions.Def_OAI_Analysis_ModularRecovery_TomitaFundamental
import Definitions.Def_OAI_Analysis_ModularRecovery_RealGraph
import Definitions.Def_OAI_Analysis_ModularRecovery_Commutant
import Definitions.Def_OAI_Analysis_ModularRecovery_PositiveKernels
import Definitions.Def_OAI_Analysis_ModularRecovery_KernelContinuity
import Definitions.Def_OAI_Analysis_ModularRecovery_StrongIntegrals
import Definitions.Def_OAI_Analysis_ModularRecovery_GaussianAverages
import Definitions.Def_OAI_Analysis_ModularRecovery_FourierKernels

namespace OAI

/-! Strong spectral limits and orbit limits. -/

universe u

open Filter MeasureTheory Set
open scoped Topology ComplexConjugate

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ComplexConjugate
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace RealSpectralCalculus

lemma tendsto_calculus_of_compact (D : RealSpectralCalculus H)
    (f : ℕ → BoundedContinuousFunction ℝ ℂ) (g : BoundedContinuousFunction ℝ ℂ)
    {C : ℝ} (hC : 0 ≤ C) (hf : ∀ n, ‖f n‖ ≤ C)
    (he : ∀ q : BoundedContinuousFunction ℝ ℂ, HasCompactSupport (q : ℝ → ℂ) →
      Tendsto (fun n => f n*q) atTop (𝓝 (g*q))) (h : H) :
    Tendsto (fun n => D.calculus (f n) h) atTop (𝓝 (D.calculus g h)) := by
  rw [Metric.tendsto_atTop]
  intro eps heps
  obtain ⟨v,⟨q,hq,k,rfl⟩,hv⟩ := D.nondegenerate.exists_dist_lt h
    (show 0 < eps / (3*(C + ‖g‖ + 1)) by positivity)
  have hv' : ‖h-D.calculus q k‖ < eps / (3*(C+‖g‖+1)) := by
    simpa only [dist_eq_norm] using hv
  have hqconv : Tendsto (fun n => D.calculus (f n) (D.calculus q k)) atTop
      (𝓝 (D.calculus g (D.calculus q k))) := by
    have hc : Continuous (fun p : BoundedContinuousFunction ℝ ℂ => D.calculusCLM p k) :=
      D.calculusCLM.continuous.clm_apply continuous_const
    have ht := (hc.tendsto (g*q)).comp (he q hq)
    simpa only [Function.comp_def,calculusCLM_apply,map_mul,mul_apply_eq_comp] using ht
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp hqconv (eps/3) (by positivity)
  refine ⟨N,fun n hn => ?_⟩
  have hmid : ‖D.calculus (f n) (D.calculus q k)-D.calculus g (D.calculus q k)‖ < eps/3 := by
    simpa only [dist_eq_norm] using hN n hn
  rw [dist_eq_norm]
  have heq : D.calculus (f n) h-D.calculus g h =
      (D.calculus (f n) (h-D.calculus q k)-D.calculus g (h-D.calculus q k))+
      (D.calculus (f n) (D.calculus q k)-D.calculus g (D.calculus q k)) := by
    simp only [map_sub]
    abel
  rw [heq]
  calc
    _ ≤ ‖D.calculus (f n) (h-D.calculus q k)-D.calculus g (h-D.calculus q k)‖+
        ‖D.calculus (f n) (D.calculus q k)-D.calculus g (D.calculus q k)‖ := norm_add_le _ _
    _ ≤ C*‖h-D.calculus q k‖+‖g‖*‖h-D.calculus q k‖+
        ‖D.calculus (f n) (D.calculus q k)-D.calculus g (D.calculus q k)‖ := by
      gcongr
      exact (norm_sub_le _ _).trans (add_le_add
        ((D.norm_calculus_apply_le _ _).trans (mul_le_mul_of_nonneg_right (hf n) (norm_nonneg _)))
        (D.norm_calculus_apply_le _ _))
    _ ≤ (C+‖g‖+1)*‖h-D.calculus q k‖+
        ‖D.calculus (f n) (D.calculus q k)-D.calculus g (D.calculus q k)‖ := by
      nlinarith [norm_nonneg (h-D.calculus q k)]
    _ < (C+‖g‖+1)*(eps/(3*(C+‖g‖+1)))+eps/3 :=
      add_lt_add (mul_lt_mul_of_pos_left hv' (by positivity)) hmid
    _ < eps := by
      field_simp
      nlinarith [norm_nonneg g]

lemma kernelMultiplier_strong_tendsto (D : RealSpectralCalculus H) (t : ℝ) (h : H) :
    Tendsto (fun n => D.calculus (kernelMultiplier n t) h) atTop
      (𝓝 (kernelFourier t • D.unitary t h)) := by
  have ht := D.tendsto_calculus_of_compact (fun n => kernelMultiplier n t)
    (kernelFourier t • spectralCharacter t) kernelMass_pos.le
    (fun n => norm_kernelMultiplier_le n t) (kernelMultiplier_mul_tendsto t) h
  simpa only [map_smul,smul_apply,unitary] using ht

end RealSpectralCalculus
end BoundedRecovery

noncomputable section
open Set Filter
open scoped Topology ComplexConjugate
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace StandardModularData

end StandardModularData
end BoundedRecovery

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ComplexConjugate
namespace BoundedRecovery

end BoundedRecovery

end
end
end

end OAI


