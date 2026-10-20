-- Prove2me | Definitions.Def_OAI_Analysis_ModularRecovery_FourierOperators
-- name    : OAI_Analysis_ModularRecovery_FourierOperators
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T14:42:29.987366+00:00
-- url     : https://prove2.me/theorems/157b1591-2f8d-4385-96e9-f53ef3e5d2f7
-- title:
--   Fourier kernels and normalized Fourier operators
-- statement:
--   These notions belong to a formal proof of a bounded recovery theorem in Tomita–Takesaki theory. Let $M$ be a von Neumann algebra on a Hilbert space $H$ with a cyclic and separating unit vector $\xi$, and let $\varphi(a)=\langle\xi,a\xi\rangle$. The modular data are encoded by a nondegenerate $*$-homomorphism $f\mapsto f(D)$ from bounded continuous functions on $\mathbb R$ to bounded operators, thought of as the functional calculus of $D=\log\Delta$. It comes with the unitary group $\Delta^{it}=e^{itD}$, the modular automorphisms $\sigma_t(a)=\Delta^{it}a\Delta^{-it}$, and an antiunitary involution $J$. The Tomita relation requires the closure of $\{(a\xi,a^*\xi):a\in M\}$ to be the graph of $J\Delta^{1/2}$. The theorem says that when $\varphi$ has trivial centralizer, a vector in a narrow spectral band of $D$ on which an operator $T$ is not small can be replaced by $v\xi$, with $v\in M$ uniformly bounded and $v\xi$ in a comparable band.
--
--   1. **Fourier kernel.** For $t\in\mathbb R$ and $b\in M'$, an element $F_t(b)\in M$ with $\|F_t(b)\|\le4\|\kappa\|_1\|b\|$ and
--   $$
--   F_t(b)\xi=\hat\kappa(t)\,\Delta^{it}Jb^*\xi ,
--   $$
--   obtained as a strong limit of the Gaussian kernel averages.
--   2. **Normalized Fourier operator.** $N_t(b)=\hat\kappa(t)^{-1}F_t(b)$ where $\hat\kappa(t)\ne0$. When $\mathrm{Re}\,\hat\kappa(t)>0$ it is multiplicative and $*$-preserving in $b$, by a Schwarz inequality argument.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/ModularRecovery/FourierOperators.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ModularRecovery/FourierOperators.lean by skeleton subtraction
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

namespace OAI

/-! Normalized Fourier operators, Schwarz inequalities, and multiplication. -/

universe u uA uB uM

open Filter MeasureTheory Set
open scoped Topology ComplexConjugate

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ComplexConjugate
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace StandardModularData

lemma exists_fourierKernel_lift (S : StandardModularData H) (t : ℝ)
    (b : S.M.commutant.toStarSubalgebra) :
    ∃ a : H →L[ℂ] H, a ∈ S.M ∧ ‖a‖ ≤ 4*kernelMass*‖b‖ ∧
      a S.xi = kernelFourier t • S.D.unitary t (S.J ((↑(star b):H →L[ℂ] H) S.xi)) := by
  have ht : Tendsto (fun n => (S.kernelAverage n t b:H →L[ℂ] H) S.xi) atTop
      (𝓝 (kernelFourier t • S.D.unitary t (S.J ((↑(star b):H →L[ℂ] H) S.xi)))) := by
    simpa only [S.kernelAverage_xi] using S.D.kernelMultiplier_strong_tendsto t
      (S.J ((↑(star b):H →L[ℂ] H) S.xi))
  exact (isClosed_bounded_orbit S.M S.xi S.separating
    (mul_nonneg (mul_nonneg (by norm_num) kernelMass_pos.le) (norm_nonneg b))).mem_of_tendsto ht
    (Filter.Eventually.of_forall fun n => ⟨S.kernelAverage n t b,(S.kernelAverage n t b).property,
      S.norm_kernelAverage_le n t b,rfl⟩)

def fourierKernel (S : StandardModularData H) (t : ℝ)
    (b : S.M.commutant.toStarSubalgebra) : S.M.toStarSubalgebra :=
  ⟨Classical.choose (S.exists_fourierKernel_lift t b),
    (Classical.choose_spec (S.exists_fourierKernel_lift t b)).1⟩

end StandardModularData
end BoundedRecovery

noncomputable section
open Set Filter
open scoped Topology ComplexConjugate
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace StandardModularData

def normalizedFourier (S : StandardModularData H) (t : ℝ)
    (b : S.M.commutant.toStarSubalgebra) : S.M.toStarSubalgebra :=
  (kernelFourier t)⁻¹ • S.fourierKernel t b

end StandardModularData
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
open Set Filter
open scoped Topology ComplexConjugate
namespace BoundedRecovery

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace StandardModularData

end StandardModularData
end BoundedRecovery

end
end
end
end

end OAI


