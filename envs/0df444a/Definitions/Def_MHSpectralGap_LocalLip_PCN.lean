-- Prove2me | Definitions.Def_MHSpectralGap_LocalLip_PCN
-- name    : MHSpectralGap_LocalLip_PCN
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T23:54:42.41949+00:00
-- url     : https://prove2.me/theorems/9c6823f7-af70-4337-98d5-8466e1eb95ca
-- title:
--   (1.2), (1.5)–(1.6), Algorithm 1, pp. 2–3, 8, 11 — P_mH, γ_m, ρ and the pCN kernels P and P_m
-- statement:
--   Let $H$ be a real Hilbert space with orthonormal basis $(e_i)_{i\ge0}$ and $\gamma$ a measure on $H$.
--
--   1. $P_mH=\operatorname{span}\{e_0,\dots,e_{m-1}\}$ is the span of the first $m$ basis vectors, and $\gamma_m$ is the image of $\gamma$ under the orthogonal projection $P_m$ onto $P_mH$; it is a probability measure on $P_mH$ whenever $\gamma$ is one.
--   2. For a step size $\delta$, $\rho=1-(1-2\delta)^{1/2}$ (§2.3).
--   3. The **pCN proposal** (1.5) with reference measure $\gamma'$ on a normed space $X$ is
--   $$Q(x,\cdot)=\mathcal L\bigl((1-2\delta)^{1/2}x+\sqrt{2\delta}\,\xi\bigr),\qquad \xi\sim\gamma',$$
--   and the **pCN acceptance probability** (1.6) for a potential $\Phi$ is $\alpha(x,y)=1\wedge\exp(\Phi(x)-\Phi(y))$.
--   4. The **pCN kernel** is the Metropolis–Hastings kernel (1.3) with this $Q$ and $\alpha$ (Algorithm 1). With $\gamma'=\gamma$ on $X=H$ it is the paper's $\mathcal P$; with $\gamma'=\gamma_m$ on $X=P_mH$ and the potential $\Phi$ restricted to $P_mH$ it is the paper's $\mathcal P_m$.
--
--   The pCN algorithm is a Metropolis–Hastings method whose proposal preserves the Gaussian reference measure, so that its acceptance probability involves only $\Phi$; this is what makes dimension-independent bounds possible.
--
--   **Formalization Note** The paper writes $\gamma_m=\mathcal L(\sum_{i\le m}\lambda_ie_i\xi_i)$ through the Karhunen–Loève expansion; when $(e_i)$ diagonalises the covariance of a centred Gaussian $\gamma$ (as in the theorems of this mission) this is the law of $P_m$ under $\gamma$, which is the encoding used. Basis vectors are indexed from $0$, so the paper's $e_1,\dots,e_m$ are $e_0,\dots,e_{m-1}$. The chain $\mathcal P_m$ lives on the subspace $P_mH$ itself. Two typeclass instances are provided: $\gamma_m$ is a probability measure, and the proposal kernel is s-finite.
-- source:
--   Hairer, Stuart and Vollmer, Spectral gaps for a Metropolis–Hastings algorithm in infinite dimensions, arXiv:1112.1392v4, pp. 2–3, (1.2), (1.5), (1.6); p. 8, Algorithm 1; p. 11, §2.3 (ρ)

import Mathlib
import Definitions.Def_MHSpectralGap_LocalLip_MHKernel
import Definitions.Def_MHSpectralGap_GlobalLip_PCN

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MHSpectralGap.LocalLip

/-- `P_m H`: the span of the first `m` basis vectors `e 0, …, e (m-1)`. -/
def Km {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (e : HilbertBasis ℕ ℝ H)
    (m : ℕ) : Submodule ℝ H :=
  Submodule.span ℝ (Set.range (fun i : Fin m => e i))

instance Km.finiteDimensional {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (e : HilbertBasis ℕ ℝ H) (m : ℕ) : FiniteDimensional ℝ (Km e m) :=
  FiniteDimensional.span_of_finite ℝ (Set.finite_range _)

/-- `γ_m`: the image of `γ` under the orthogonal projection `P_m` onto `Km e m`. -/
noncomputable def gammaM {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasurableSpace H] (γ : Measure H) (e : HilbertBasis ℕ ℝ H) (m : ℕ) : Measure (Km e m) :=
  γ.map ((Km e m).orthogonalProjectionOnto)

instance gammaM.isProbabilityMeasure {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasurableSpace H] [BorelSpace H] (γ : Measure H) [IsProbabilityMeasure γ]
    (e : HilbertBasis ℕ ℝ H) (m : ℕ) : IsProbabilityMeasure (gammaM γ e m) :=
  Measure.isProbabilityMeasure_map (ContinuousLinearMap.continuous _).measurable.aemeasurable

/-- `ρ = 1 − (1 − 2δ)^{1/2}` (§2.3, p. 11). -/
noncomputable def ρ (δ : ℝ) : ℝ := 1 - Real.sqrt (1 - 2 * δ)

/-- The pCN proposal (1.5): `x ↦ L((1 − 2δ)^{1/2} x + √(2δ) ξ)`, `ξ ∼ γ'`. -/
noncomputable def pcnProposal {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [MeasurableSpace X] (γ' : Measure X) [SFinite γ'] (δ : ℝ) : Kernel X X :=
  (Kernel.id ×ₖ Kernel.const X γ').map
    (fun p : X × X => Real.sqrt (1 - 2 * δ) • p.1 + Real.sqrt (2 * δ) • p.2)

instance pcnProposal.isSFiniteKernel {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [MeasurableSpace X] (γ' : Measure X) [SFinite γ'] (δ : ℝ) :
    IsSFiniteKernel (pcnProposal γ' δ) := by
  unfold pcnProposal; infer_instance

/-- The pCN Markov kernel (Algorithm 1): Metropolis–Hastings with proposal (1.5) and
acceptance (1.6). -/
noncomputable def pcnKernel {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [MeasurableSpace X] (γ' : Measure X) [SFinite γ'] (Φ : X → ℝ) (δ : ℝ) : Kernel X X :=
  mhKernel (pcnProposal γ' δ) (MHSpectralGap.GlobalLip.pcnAccept Φ)

end MHSpectralGap.LocalLip


