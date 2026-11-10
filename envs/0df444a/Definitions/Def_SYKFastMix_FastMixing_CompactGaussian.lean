-- Prove2me | Definitions.Def_SYKFastMix_FastMixing_CompactGaussian
-- name    : SYKFastMix_FastMixing_CompactGaussian
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T14:05:33.024777+00:00
-- url     : https://prove2.me/theorems/e3c5dc5b-889c-4058-895a-5a87dfae0fa7
-- title:
--   Continuous compact Gaussian processes and symmetric polynomial forms
-- statement:
--   For a real process $(X_t)_{t\in T}$ on a probability space $(\Omega,P)$, define its ordinary pointwise supremum and supremum of coordinate variances by
--   $$S_X(\omega)=\sup_{t\in T}X_t(\omega),\qquad v_X^2=\sup_{t\in T}\int X_t^2\,dP.$$
--   The compact Gaussian predicate records finite-dimensional Gaussianity, zero coordinate means, and almost-sure continuity of the sample paths. The support theorems supply nonemptiness of the compact metric index, boundedness of sample suprema, and integrability; these properties are not assumed in this definition. The pointwise supremum is distinct from the published supremum of expectations of finite maxima.
--
--   For the polynomial support, $E_n=\mathbb R^n$ has its Euclidean norm. A symmetric continuous $r$-linear map $T$ is invariant under every permutation of its $r$ arguments. Its diagonal polynomial is
--   $$P_T(x)=T(x,\ldots,x).$$
--   Symmetric multilinear maps describe all homogeneous real polynomial maps of degree $r$. These reusable objects express the appendix results at arbitrary degree and on compact, potentially uncountable index sets.
-- source:
--   Yiyi Cai, Yongtao Zhan, Alexander Zlokapa, Fast mixing of the SYK model at high temperatures, STOC 2027 submission #1050 (October 2026), p.33, Appendix A preamble and Facts 16–18

import Mathlib
import Definitions.Def_HighDimProb_RandomProcesses_ProcessESup

noncomputable section
open MeasureTheory ProbabilityTheory

namespace SYKFastMix.FastMixing

/-- The ordinary pointwise supremum, distinguished from the published finite-marginal
 expected supremum. The support theorems prove its a.e. boundedness and integrability. -/
def sampleSup {T Ω : Type} (X : T → Ω → ℝ) (ω : Ω) : ℝ := ⨆ t, X t ω

def varianceSup {T Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (X : T → Ω → ℝ) : ℝ :=
  ⨆ t, ∫ ω, (X t ω)^2 ∂P

/-- Centering and almost-sure sample continuity are the source assumptions, not bounds on
 the supremum or its integral. Gaussianity is Mathlib's finite-dimensional definition. -/
def CompactGaussian {T Ω : Type} [TopologicalSpace T] [MeasurableSpace Ω]
    (P : Measure Ω) (X : T → Ω → ℝ) : Prop :=
  IsGaussianProcess X P ∧ (∀ t, ∫ ω, X t ω ∂P = 0) ∧
    ∀ᵐ ω ∂P, Continuous (fun t => X t ω)

abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

def IsSymmetricForm {r n : ℕ} {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin r => E n) F) : Prop :=
  ∀ (u : Fin r → E n) (π : Equiv.Perm (Fin r)), T (u ∘ π) = T u

def diagonalPolynomial {r n a : ℕ}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin r => E n) (E a)) (x : E n) : E a :=
  T (fun _ => x)

end SYKFastMix.FastMixing


