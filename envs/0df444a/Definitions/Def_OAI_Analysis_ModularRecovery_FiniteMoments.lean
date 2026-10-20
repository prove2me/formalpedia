-- Prove2me | Definitions.Def_OAI_Analysis_ModularRecovery_FiniteMoments
-- name    : OAI_Analysis_ModularRecovery_FiniteMoments
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T14:54:14.516175+00:00
-- url     : https://prove2.me/theorems/c8b92533-78f2-4d1b-acd2-ff9c7d100407
-- title:
--   Finite modular averages
-- statement:
--   These notions belong to a formal proof of a bounded recovery theorem in Tomita–Takesaki theory. Let $M$ be a von Neumann algebra on a Hilbert space $H$ with a cyclic and separating unit vector $\xi$, and let $\varphi(a)=\langle\xi,a\xi\rangle$. The modular data are encoded by a nondegenerate $*$-homomorphism $f\mapsto f(D)$ from bounded continuous functions on $\mathbb R$ to bounded operators, thought of as the functional calculus of $D=\log\Delta$. It comes with the unitary group $\Delta^{it}=e^{itD}$, the modular automorphisms $\sigma_t(a)=\Delta^{it}a\Delta^{-it}$, and an antiunitary involution $J$. The Tomita relation requires the closure of $\{(a\xi,a^*\xi):a\in M\}$ to be the graph of $J\Delta^{1/2}$. The theorem says that when $\varphi$ has trivial centralizer, a vector in a narrow spectral band of $D$ on which an operator $T$ is not small can be replaced by $v\xi$, with $v\in M$ uniformly bounded and $v\xi$ in a comparable band.
--
--   1. **Modular average.** For finitely many probabilities $p_i$, times $t_i$ and an operator $a$,
--   $$
--   \mathcal A_{p,t}(a)=\sum_ip_i\,\sigma_{t_i}(a).
--   $$
--   It lies in $M$ when $a$ does, has norm at most $\|a\|$, and sends $\xi$ to $\sum_ip_i\Delta^{it_i}a\xi$.
--
--   Such averages approximate the conditional expectation onto the centralizer, which is scalar under the hypothesis of the theorem.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/ModularRecovery/FiniteMoments.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ModularRecovery/FiniteMoments.lean by skeleton subtraction
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
import Definitions.Def_OAI_Analysis_ModularRecovery_ErgodicAverages

namespace OAI

/-! Simultaneous finite approximations of modular moments. -/

universe u uE uι

open Filter MeasureTheory Set
open scoped Topology ComplexConjugate

noncomputable section
namespace BoundedRecovery
variable {ι : Type uι} [Fintype ι]
end BoundedRecovery

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ComplexConjugate
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace StandardModularData
variable {ι : Type uι} [Fintype ι]

def modularAverage (S : StandardModularData H) (p t : ι → ℝ) (a : H →L[ℂ] H) : H →L[ℂ] H :=
  ∑ i, p i • S.sigma (t i) a

end StandardModularData
end BoundedRecovery

end
end

end OAI


