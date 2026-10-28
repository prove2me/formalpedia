-- Prove2me | Definitions.Def_RetroCorr_Separation_Holevo
-- name    : RetroCorr_Separation_Holevo
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-24T09:26:30.894217+00:00
-- url     : https://prove2.me/theorems/45de9f9d-7eb7-4085-b237-396d6dacb0df
-- title:
--   Introduction, p. 1 — one-shot Holevo capacity C_H of a channel with a classical output: supremum over finite input ensembles of the flag-averaged Holevo quantity (bits)
-- statement:
--   Let $\mathcal N=(\mathcal N_k)_k$ be a family of quantum channels from an input space $\mathcal H_I$ to an output space $\mathcal H_O$, indexed by the value $k$ of a classical output drawn from a probability law $\mu$ that does not depend on the input. One use of the channel on input $\rho$ produces $k\sim\mu$ together with the quantum state $\mathcal N_k(\rho)$.
--
--   For a finite input ensemble $\{p_x,\rho_x\}_{x=1}^n$ (probabilities $p_x\ge0$ with $\sum_xp_x=1$, density matrices $\rho_x$ on $\mathcal H_I$), its **Holevo quantity** is
--   $$\chi(\{p_x,\rho_x\})=\int\Big[S\Big(\sum_xp_x\,\mathcal N_k(\rho_x)\Big)-\sum_xp_x\,S\big(\mathcal N_k(\rho_x)\big)\Big]\,d\mu(k),$$
--   where $S(\sigma)=-\operatorname{Tr}\sigma\log_2\sigma$ is the von Neumann entropy in bits. The **one-shot Holevo capacity** is
--   $$C_H(\mathcal N)=\sup_{n,\;\{p_x,\rho_x\}_{x=1}^n}\chi(\{p_x,\rho_x\})\in[0,\infty],$$
--   the supremum over every finite ensemble of arbitrary (mixed or entangled) density matrices on the full input space.
--
--   This is the paper's "maximum, over input distributions for a single use of the channel, of the entropy of the average output minus the average of the output entropies", applied to the full output (classical flag together with quantum output). Because the flag is independent of the input, the entropy difference of the full output equals the flag-average of the conditional entropy differences: for a finite flag the joint output $\sum_k\mu_k|k\rangle\langle k|\otimes\mathcal N_k(\rho)$ has entropy $H(\mu)+\sum_k\mu_kS(\mathcal N_k(\rho))$, and $H(\mu)$ cancels; for a continuous flag the integral is the mutual information $I(X;KD)=I(X;D\mid K)$. This is the paper's remark that the control outputs "do not contribute to the Holevo capacity because they are uncorrelated with the input".
--
--   **Formalization Note** `flaggedHolevo μ N p ρ` is the lower Lebesgue integral `∫⁻ k, ENNReal.ofReal (…) ∂μ` of the conditional Holevo quantity, and `holevoCapacity μ N` is an `iSup` in `ℝ≥0∞` over `n : ℕ`, `p : Fin n → ℝ`, `ρ : Fin n → Matrix I I ℂ` with $p\ge0$, $\sum p=1$ and every `ρ x` a density matrix (`QAlgorithms.IsDensityMatrix`). Using `ℝ≥0∞` and the lower integral means no non-integrability default and no truncation of an unbounded supremum. The conditional Holevo quantity is nonnegative on density-matrix ensembles through channels, so `ENNReal.ofReal` changes no value there. Entropies are `QAlgorithms.vnEntropy` (base 2).
-- source:
--   Bennett, Devetak, Shor & Smolin, Inequalities and separations among assisted capacities of quantum channels, arXiv:quant-ph/0406086v1, p. 1, Introduction (definition of C_H); p. 2, §2 (control outputs uncorrelated with the input)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_Channel

namespace RetroCorr.Separation

noncomputable section

open MeasureTheory

/-- Introduction, p. 1: the Holevo quantity, in bits, of the finite input ensemble
`{p_x, ρ_x}` sent once through a channel with a classical output. For each value `k` of the
classical output the quantum output is `N k (ρ_x)`; the integrand is the Holevo quantity
`S(Σ_x p_x N_k(ρ_x)) − Σ_x p_x S(N_k(ρ_x))` of the conditional output ensemble, and it is
averaged over the law `μ` of the classical output (which does not depend on the input). The
integrand is nonnegative on density-matrix ensembles; `ENNReal.ofReal` only fixes the type. -/
def flaggedHolevo {K : Type*} [MeasurableSpace K] (μ : Measure K)
    {I O : Type*} [Fintype I] [Fintype O] [DecidableEq O]
    (N : K → QAlgorithms.Superop I O) {n : ℕ} (p : Fin n → ℝ) (ρ : Fin n → Matrix I I ℂ) :
    ENNReal :=
  ∫⁻ k, ENNReal.ofReal
    (QAlgorithms.vnEntropy (∑ x, (p x : ℂ) • N k (ρ x)) -
      ∑ x, p x * QAlgorithms.vnEntropy (N k (ρ x))) ∂μ

/-- Introduction, p. 1: the one-shot Holevo capacity `C_H`, in bits: the supremum, over every
finite input ensemble for a single use of the channel (any number of signals, any probability
vector, any density matrices on the full input space), of the Holevo quantity
`flaggedHolevo`. -/
def holevoCapacity {K : Type*} [MeasurableSpace K] (μ : Measure K)
    {I O : Type*} [Fintype I] [Fintype O] [DecidableEq O]
    (N : K → QAlgorithms.Superop I O) : ENNReal :=
  ⨆ (n : ℕ) (p : Fin n → ℝ) (ρ : Fin n → Matrix I I ℂ)
    (_ : (∀ x, 0 ≤ p x) ∧ ∑ x, p x = 1 ∧ ∀ x, QAlgorithms.IsDensityMatrix (ρ x)),
    flaggedHolevo μ N p ρ

end

end RetroCorr.Separation


