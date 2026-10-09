-- Prove2me | Definitions.Def_MHSpectralGap_GlobalLip_PCN
-- name    : MHSpectralGap_GlobalLip_PCN
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T23:03:31.883029+00:00
-- url     : https://prove2.me/theorems/8eadff2b-6b6a-4375-9183-8daa14b40225
-- title:
--   Equations (1.2), (1.5)–(1.6): projected Gaussian and pCN kernel
-- statement:
--   Let $K_m$ be the span of the first $m$ covariance eigenvectors in the Hilbert space $H$, and let $\gamma_m$ be the law of the orthogonal projection of a $\gamma$-distributed vector onto $K_m$. The pCN proposal from $x$ is the law of
--
--   $$y=\sqrt{1-2\delta}\,x+\sqrt{2\delta}\,\xi,\qquad \xi\sim\gamma,$$
--
--   and its acceptance probability is $\alpha(x,y)=1\wedge\exp(\Phi(x)-\Phi(y))$. The pCN kernel applies the Metropolis–Hastings accept–reject rule to this proposal. The file also defines $\rho=1-\sqrt{1-2\delta}$.
--
--   **Formalization Note** $K_m$ is a subspace type and $\gamma_m$ is a measure on that type. This realizes the paper's finite dimensional chain on $P_mH$; $m=0$ is the zero dimensional subspace.
-- source:
--   Hairer, Stuart and Vollmer, Spectral gaps for a Metropolis–Hastings algorithm in infinite dimensions, arXiv:1112.1392v4, pp. 2–3 and 11, (1.2), (1.5)–(1.6) and the definition of rho

import Mathlib
import Definitions.Def_MHSpectralGap_GlobalLip_MHKernel

namespace MHSpectralGap.GlobalLip

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Span of the first m covariance eigenvectors. -/
def Km {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (e : HilbertBasis ℕ ℝ H) (m : ℕ) : Submodule ℝ H :=
  Submodule.span ℝ (Set.range (fun i : Fin m => e i))

/-- Projected Gaussian measure γ_m of (1.2). -/
noncomputable def gammaM {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] [MeasurableSpace H]
    [BorelSpace H] (γ : Measure H) (e : HilbertBasis ℕ ℝ H) (m : ℕ) :
    Measure (Km e m) :=
  letI : FiniteDimensional ℝ (Km e m) :=
    FiniteDimensional.span_of_finite ℝ (Set.finite_range _)
  letI : CompleteSpace (Km e m) := FiniteDimensional.complete ℝ _
  γ.map ((Km e m).orthogonalProjectionOnto : H →L[ℝ] Km e m)

instance gammaM_probability {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] [MeasurableSpace H]
    [BorelSpace H] (γ : Measure H) [IsProbabilityMeasure γ]
    (e : HilbertBasis ℕ ℝ H) (m : ℕ) :
    IsProbabilityMeasure (gammaM γ e m) := by
  unfold gammaM
  letI : FiniteDimensional ℝ (Km e m) :=
    FiniteDimensional.span_of_finite ℝ (Set.finite_range _)
  letI : CompleteSpace (Km e m) := FiniteDimensional.complete ℝ _
  exact Measure.isProbabilityMeasure_map
    ((Km e m).orthogonalProjectionOnto.continuous.measurable.aemeasurable)

/-- pCN proposal law, (1.5). -/
noncomputable def pcnProposal {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [MeasurableSpace H] [BorelSpace H]
    [SecondCountableTopology H]
    (γ : Measure H) (δ : ℝ) : Kernel H H :=
  ((Kernel.id : Kernel H H) ×ₖ Kernel.const H γ).map
    (fun p => Real.sqrt (1 - 2 * δ) • p.1 + Real.sqrt (2 * δ) • p.2)

/-- pCN acceptance probability, (1.6). -/
noncomputable def pcnAccept {H : Type} (Φ : H → ℝ) (x y : H) : ℝ≥0∞ :=
  ENNReal.ofReal (min 1 (Real.exp (Φ x - Φ y)))

/-- pCN transition kernel of Algorithm 1. -/
noncomputable def pcnKernel {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [MeasurableSpace H] [BorelSpace H]
    [SecondCountableTopology H]
    (γ : Measure H) [IsProbabilityMeasure γ] (Φ : H → ℝ) (δ : ℝ) : Kernel H H :=
  letI : IsMarkovKernel (pcnProposal γ δ) :=
    Kernel.IsMarkovKernel.map _
      ((measurable_const.smul measurable_fst).add
        (measurable_const.smul measurable_snd))
  mhKernel (pcnProposal γ δ) (pcnAccept Φ)

/-- ρ of §2.3. -/
noncomputable def rho (δ : ℝ) : ℝ := 1 - Real.sqrt (1 - 2 * δ)

end MHSpectralGap.GlobalLip


