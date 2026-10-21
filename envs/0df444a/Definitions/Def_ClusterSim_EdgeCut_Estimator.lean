-- Prove2me | Definitions.Def_ClusterSim_EdgeCut_Estimator
-- name    : ClusterSim_EdgeCut_Estimator
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T05:54:49.828978+00:00
-- url     : https://prove2.me/theorems/af248d03-2280-48c0-9ce5-874a846d4558
-- title:
--   The one-sample law of 8^K c_s t_s, the sample size N = ⌈4·2^{4K}/ε²⌉ of eq. (37) and the sample average (p. 10)
-- statement:
--   Fix a clustering of a tensor network with $K=|E_{\mathrm{cut}}|$ cut edges, and for every $s\in[8]^{E_{\mathrm{cut}}}$ a probability law $\mathrm{run}(s)$ on $\mathbb R$: the law of the outcome $t_s$ of eq. (34) obtained by running the pieces of the cut network $(G',\mathcal A_s)$ on the quantum device.
--
--   1. **One sample.** Draw $s$ uniformly from $[8]^{E_{\mathrm{cut}}}$, then $t_s\sim\mathrm{run}(s)$, and output $8^K c_s t_s$. Its law is the mixture
--   $$\mu=\sum_{s\in[8]^{E_{\mathrm{cut}}}}8^{-K}\cdot\big(\text{law of }8^K c_s t\text{ for }t\sim\mathrm{run}(s)\big).$$
--   2. **Sample size.** With $a=2^{2K}$ (eq. (36)),
--   $$N=\Big\lceil\frac{4a^2}{\varepsilon^2}\Big\rceil=\Big\lceil\frac{4\cdot 2^{4K}}{\varepsilon^2}\Big\rceil .$$
--   3. **Estimate.** The estimate of $T(G,\mathcal A)$ is the average $\frac1N\sum_{i=1}^N x_i$ of $N$ samples.
--
--   These are the ingredients of the simulation algorithm in the proof of Theorem 1: it produces $N$ samples $(s_i,t_{s_i})$ and outputs $\frac1N\sum_i 8^K c_{s_i}t_{s_i}$.
--
--   **Formalization Note** The paper's $N=4a^2/\varepsilon^2$ need not be an integer; it is rounded up (`Nat.ceil`). For $\varepsilon=0$ the formula gives $N=0$, a junk value; the theorems assume $\varepsilon>0$. The mixture is a finite sum of pushforward measures with weights $8^{-K}$ in $[0,\infty]$.
-- source:
--   Peng, Harrow, Ozols & Wu, Simulating Large Quantum Circuits on a Small Quantum Computer, arXiv:1904.00102v2, p. 10, proof of Theorem 1, eqs. (34)–(37)

import Mathlib
import Definitions.Def_ClusterSim_EdgeCut_Clustering

namespace ClusterSim.EdgeCut

open MeasureTheory ENNReal

noncomputable section

variable {G : TensorNetwork} {r : ℕ}

/-- The law of one sample `8^K c_s t_s` of the estimator (proof of Theorem 1, p. 10, eqs. (35)–(36)),
`K = |E_cut|`: `s` is drawn uniformly from `[8]^{E_cut}` (each of the `8^K` strings with weight
`8^{-K}`), then `t_s` is drawn from the device law `run s` (the outcome (34) of running the pieces
of `(G′, A_s)`), and the sample is `8^K · c_s · t_s`. -/
def sampleLaw (P : Clustering G r) (run : (P.Ecut → Fin 8) → Measure ℝ) : Measure ℝ :=
  ∑ s : P.Ecut → Fin 8, ((8 : ℝ≥0∞) ^ P.Ecut.card)⁻¹ •
    (run s).map (fun t => (8 : ℝ) ^ P.Ecut.card * coefS s * t)

/-- The number of samples of eq. (37) with `a = 2^{2K}` (eq. (36)): `N = ⌈4a²/ε²⌉ = ⌈4·2^{4K}/ε²⌉`
(the paper's `N = 4a²/ε²`, rounded up to an integer). -/
def numSamples (K : ℕ) (ε : ℝ) : ℕ := ⌈4 * (2 : ℝ) ^ (4 * K) / ε ^ 2⌉₊

/-- The estimate `(1/N) Σ_{i=1}^N x_i`, the plain average of `N` samples (p. 10). -/
def average {N : ℕ} (x : Fin N → ℝ) : ℝ := (∑ i, x i) / N

end

end ClusterSim.EdgeCut


