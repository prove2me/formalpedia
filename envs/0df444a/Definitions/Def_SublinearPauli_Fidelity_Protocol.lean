-- Prove2me | Definitions.Def_SublinearPauli_Fidelity_Protocol
-- name    : SublinearPauli_Fidelity_Protocol
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:47:31.987024+00:00
-- url     : https://prove2.me/theorems/d6fd184b-915e-4de7-aadb-b315916062c3
-- title:
--   P1 with median-of-means — batch size $b$, batch count $k$, batch output, median and the success probability
-- statement:
--   Protocol P1 receives the description of a known target $\rho$ and copies of an unknown lab state $\sigma$. On each copy it samples a basis $B$ uniformly from the $3^N$ Pauli bases, independently of everything else, and measures the copy in $B$; one copy's record $(B,x)$ therefore has probability
--   $$\Pr[(B,x)]=3^{-N}\operatorname{Tr}[\sigma M_x^B].$$
--   On a batch of $b$ copies with records $(B_i,x_i)$ it outputs
--   $$\tilde F(\rho,\sigma)=\frac{3^N}{b}\sum_{i=1}^b s_\rho(B_i,x_i).$$
--
--   The amplified protocol uses $k$ independent batches and outputs the median of the $k$ batch outputs, with
--   $$b=\Bigl\lceil\frac{3A_N}{\varepsilon^2}\Bigr\rceil,\qquad k=2\Bigl\lceil 9\log\frac1\delta\Bigr\rceil+1,$$
--   $A_N=2^{\lambda N}(\sqrt3)^{(1-\lambda)N}$, for a total of $n=bk$ copies. The **success probability** is the probability, under the product law of the $n$ independent records, that the median lies within $\varepsilon$ of $\operatorname{Tr}[\rho\sigma]$.
--
--   The sampling of bases, $b$ and $k$ depend only on $N$, $\varepsilon$ and $\delta$; only the classical postprocessing reads $\rho$.
--
--   **Formalization Note** The probability is a finite sum over all arrays of $k\times b$ records of the product of the single-copy probabilities, restricted to the success event. The median is the published `ClassicalShadow.Linear.median` (the middle element of the sorted list, exact for odd $k$). The constants $3$ and $9$ and the ceilings make the $O(\cdot)$ of Theorem 1 explicit: $3$ is the batch constant of the proof on p.12, and $9$ is the Hoeffding constant of the median step.
-- source:
--   Abhilash Dharmavarapu, Jayadev Acharya, Nengkun Yu, Yuhan Liu, STOC 2027 submission #230 (October 2026), PDF sha256 a007d4d449494d7b3589233107d1fc0190d256341e1bcbb1b95965363d6e10c4, protocol P1 p.6, §1.1 p.2 (success criterion), proof of Theorem 1 p.12 (n = 3·2^{λN}√3^{(1−λ)N}/ε², Chebyshev, Median-of-Means amplification)

import Mathlib
import Definitions.Def_SublinearPauli_Fidelity_Measurement
import Definitions.Def_SublinearPauli_Fidelity_Energies

open ClassicalShadow.Linear

namespace SublinearPauli.Fidelity

/-- One copy's record: the sampled basis `B` and the outcome `x ∈ {−1, 1}^N`. -/
abbrev Record (N : ℕ) := PauliBasis N × PSDPolyApprox.Cube N

/-- The law of one copy's record in P1 (p.6): `B` uniform on the `3^N` bases, then `x` by Born's
rule, `Pr[(B, x)] = 3^{−N} Tr[σ M_x^B]`. -/
noncomputable def recordProb {N : ℕ} (σ : Op N) (r : Record N) : ℝ :=
  bornProb σ r.1 r.2 / (3 : ℝ) ^ N

/-- The batch size `b = ⌈3 A_N / ε²⌉` (proof of Theorem 1, p.12). -/
noncomputable def blockSize (N : ℕ) (ε : ℝ) : ℕ :=
  ⌈3 * rateA N / ε ^ 2⌉₊

/-- The number of batches `k = 2 ⌈9 log(1/δ)⌉ + 1` of the median-of-means amplification. -/
noncomputable def numBlocks (δ : ℝ) : ℕ :=
  2 * ⌈9 * Real.log (1 / δ)⌉₊ + 1

/-- The output of P1 on one batch of `b` copies (p.6): `F̃ = (3^N / b) Σ_{i=1}^b s_ρ(B_i, x_i)`.
It reads only the target `ρ` and the records. -/
noncomputable def blockMean {N b : ℕ} (ρ : Op N) (ω : Fin b → Record N) : ℝ :=
  ((3 : ℝ) ^ N / b) * ∑ i, overlapStat ρ (ω i).1 (ω i).2

/-- The median of the `k` batch outputs (median-of-means, proof of Theorem 1, p.12), using the
published median `ClassicalShadow.Linear.median`. -/
noncomputable def estimate {N b k : ℕ} (ρ : Op N) (ω : Fin k → Fin b → Record N) : ℝ :=
  median fun i => blockMean ρ (ω i)

/-- The probability that the amplified protocol P1 with `k` batches of `b` copies of `σ` outputs a
value within `ε` of `Tr[ρσ]`: the sum, over all record arrays, of the product Born law
`∏_{i,j} Pr[ω i j]` of the `n = bk` independent copies, restricted to the success event. -/
noncomputable def successProb {N : ℕ} (ρ σ : Op N) (b k : ℕ) (ε : ℝ) : ℝ :=
  ∑ ω : Fin k → Fin b → Record N,
    (∏ i, ∏ j, recordProb σ (ω i j)) *
      (if |estimate ρ ω - (ρ * σ).trace.re| ≤ ε then 1 else 0)

end SublinearPauli.Fidelity


