-- Prove2me | Definitions.Def_OAI_Analysis_ModularRecovery_ErgodicAverages
-- name    : OAI_Analysis_ModularRecovery_ErgodicAverages
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T14:49:54.220178+00:00
-- url     : https://prove2.me/theorems/5706a9cc-b464-4482-8412-c750d1434633
-- title:
--   The modular action as linear maps
-- statement:
--   These notions belong to a formal proof of a bounded recovery theorem in Tomita–Takesaki theory. Let $M$ be a von Neumann algebra on a Hilbert space $H$ with a cyclic and separating unit vector $\xi$, and let $\varphi(a)=\langle\xi,a\xi\rangle$. The modular data are encoded by a nondegenerate $*$-homomorphism $f\mapsto f(D)$ from bounded continuous functions on $\mathbb R$ to bounded operators, thought of as the functional calculus of $D=\log\Delta$. It comes with the unitary group $\Delta^{it}=e^{itD}$, the modular automorphisms $\sigma_t(a)=\Delta^{it}a\Delta^{-it}$, and an antiunitary involution $J$. The Tomita relation requires the closure of $\{(a\xi,a^*\xi):a\in M\}$ to be the graph of $J\Delta^{1/2}$. The theorem says that when $\varphi$ has trivial centralizer, a vector in a narrow spectral band of $D$ on which an operator $T$ is not small can be replaced by $v\xi$, with $v\in M$ uniformly bounded and $v\xi$ in a comparable band.
--
--   1. **Modular action.** For $t\in\mathbb R$, the linear map
--   $$
--   a\mapsto\sigma_t(a)=\Delta^{it}a\Delta^{-it}
--   $$
--   on bounded operators. It satisfies $\sigma_t(a)\xi=\Delta^{it}a\xi$, preserves norms, and is strongly continuous in $t$.
--
--   Convex combinations of the orbit $\{\Delta^{it}a\xi\}$ are used to reach the fixed vector $\varphi(a)\xi$ when the centralizer of $\varphi$ is trivial.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/ModularRecovery/ErgodicAverages.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ModularRecovery/ErgodicAverages.lean by skeleton subtraction
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
import Definitions.Def_OAI_Analysis_ModularRecovery_StrongLimits
import Definitions.Def_OAI_Analysis_ModularRecovery_FourierOperators
import Definitions.Def_OAI_Analysis_ModularRecovery_ModularCovariance

namespace OAI

/-! Hilbert-space and predual ergodic averaging for the modular action. -/

universe u uE uF uι

open Filter MeasureTheory Set
open scoped Topology ComplexConjugate

noncomputable section
open Filter MeasureTheory Set
open scoped Topology ComplexConjugate
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace StandardModularData

@[simp] lemma sigma_apply_xi (S : StandardModularData H) (t : ℝ) (a : H →L[ℂ] H) :
    S.sigma t a S.xi = S.D.unitary t (a S.xi) := by
  simp [sigma, S.fixes_xi]

@[simp] lemma sigma_one (S : StandardModularData H) (t : ℝ) :
    S.sigma t 1 = 1 := by simp [sigma]

lemma sigma_add (S : StandardModularData H) (t : ℝ) (a b : H →L[ℂ] H) :
    S.sigma t (a + b) = S.sigma t a + S.sigma t b := by simp [sigma, mul_add, add_mul]

lemma sigma_smul (S : StandardModularData H) (t : ℝ) (c : ℂ) (a : H →L[ℂ] H) :
    S.sigma t (c • a) = c • S.sigma t a := by simp [sigma]

lemma norm_sigma (S : StandardModularData H) (t : ℝ) (a : H →L[ℂ] H) :
    ‖S.sigma t a‖ = ‖a‖ := by
  have hle (r : ℝ) (b : H →L[ℂ] H) : ‖S.sigma r b‖ ≤ ‖b‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro v
    simp only [sigma, mul_apply_eq_comp, S.D.norm_unitary_apply]
    simpa only [S.D.norm_unitary_apply] using b.le_opNorm (S.D.unitary (-r) v)
  apply le_antisymm (hle t a)
  simpa only [← S.sigma_add_time, neg_add_cancel, S.sigma_zero] using hle (-t) (S.sigma t a)

lemma continuous_sigma_apply (S : StandardModularData H) (a : H →L[ℂ] H) (h : H) :
    Continuous (fun t => S.sigma t a h) := by
  exact S.D.continuous_unitary_apply_varying
    (a.continuous.comp ((S.D.continuous_unitary_apply h).comp continuous_neg))

end StandardModularData

end BoundedRecovery

noncomputable section
open Set Filter
open scoped Topology
namespace BoundedRecovery

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

end BoundedRecovery

noncomputable section
open Set Filter
open scoped Topology
namespace BoundedRecovery

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

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
open scoped ComplexConjugate
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

end BoundedRecovery

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ComplexConjugate
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace StandardModularData

def sigmaLinear (S : StandardModularData H) (t : ℝ) : (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H) where
  toFun := S.sigma t
  map_add' := S.sigma_add t
  map_smul' := S.sigma_smul t

@[simp] lemma sigmaLinear_apply (S : StandardModularData H) (t : ℝ) (a : H →L[ℂ] H) :
    S.sigmaLinear t a = S.sigma t a := rfl

end StandardModularData
end BoundedRecovery

end
end
end
end
end
end

end OAI


