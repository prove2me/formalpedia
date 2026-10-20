-- Prove2me | Definitions.Def_OAI_Analysis_ModularRecovery_ModularCovariance
-- name    : OAI_Analysis_ModularRecovery_ModularCovariance
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T14:45:31.401152+00:00
-- url     : https://prove2.me/theorems/29bef188-5bf5-4519-a4c3-3593fef917f2
-- title:
--   Spatial conjugation by the modular conjugation
-- statement:
--   These notions belong to a formal proof of a bounded recovery theorem in Tomita–Takesaki theory. Let $M$ be a von Neumann algebra on a Hilbert space $H$ with a cyclic and separating unit vector $\xi$, and let $\varphi(a)=\langle\xi,a\xi\rangle$. The modular data are encoded by a nondegenerate $*$-homomorphism $f\mapsto f(D)$ from bounded continuous functions on $\mathbb R$ to bounded operators, thought of as the functional calculus of $D=\log\Delta$. It comes with the unitary group $\Delta^{it}=e^{itD}$, the modular automorphisms $\sigma_t(a)=\Delta^{it}a\Delta^{-it}$, and an antiunitary involution $J$. The Tomita relation requires the closure of $\{(a\xi,a^*\xi):a\in M\}$ to be the graph of $J\Delta^{1/2}$. The theorem says that when $\varphi$ has trivial centralizer, a vector in a narrow spectral band of $D$ on which an operator $T$ is not small can be replaced by $v\xi$, with $v\in M$ uniformly bounded and $v\xi$ in a comparable band.
--
--   1. **$J$-conjugate.** For an operator $a$, the operator
--   $$
--   jC(a)=JaJ,\qquad h\mapsto J\bigl(a(Jh)\bigr).
--   $$
--   It is involutive in $a$.
--
--   The modular automorphisms satisfy $\sigma_0=\mathrm{id}$ and $\sigma_{s+t}=\sigma_s\circ\sigma_t$. Conjugation by $J$ exchanges $M$ and its commutant $M'$, which yields modular covariance $\sigma_t(M)=M$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/ModularRecovery/ModularCovariance.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ModularRecovery/ModularCovariance.lean by skeleton subtraction
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

namespace OAI

/-! Spatial Tomita conjugation and modular covariance. -/

universe u

open Filter MeasureTheory Set
open scoped Topology ComplexConjugate

noncomputable section
open Set Filter
open scoped Topology ComplexConjugate
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace StandardModularData

def jConjugate (S : StandardModularData H) (a : H →L[ℂ] H) : H →L[ℂ] H where
  toFun h := S.J (a (S.J h))
  map_add' _ _ := by simp only [map_add]
  map_smul' z h := by
    simp only [map_smulₛₗ,starRingEnd_self_apply,RingHom.id_apply]
  cont := S.J.continuous.comp (a.continuous.comp S.J.continuous)

@[simp] lemma jConjugate_apply (S : StandardModularData H) (a : H →L[ℂ] H) (h : H) :
    S.jConjugate a h = S.J (a (S.J h)) := rfl

@[simp] lemma jConjugate_involutive (S : StandardModularData H) (a : H →L[ℂ] H) :
    S.jConjugate (S.jConjugate a) = a := by
  ext h
  simp only [S.jConjugate_apply]
  rw [S.conjugation h,S.conjugation (a h)]

@[simp] lemma sigma_zero (S : StandardModularData H) (a : H →L[ℂ] H) : S.sigma 0 a = a := by
  simp only [sigma,neg_zero,S.D.unitary_zero,one_mul,mul_one]

end StandardModularData
end BoundedRecovery

noncomputable section
open Set Filter
open scoped Topology ComplexConjugate
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace StandardModularData

lemma sigma_add_time (S : StandardModularData H) (s t : ℝ) (a : H →L[ℂ] H) :
    S.sigma (s+t) a = S.sigma s (S.sigma t a) := by
  simp only [sigma,S.D.unitary_add,neg_add_rev,mul_assoc]

end StandardModularData
end BoundedRecovery

end
end

end OAI


