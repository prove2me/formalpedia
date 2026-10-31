-- Prove2me | Definitions.Def_Ironclad_ClosedForms
-- name    : Ironclad_ClosedForms
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:25:38.089365+00:00
-- url     : https://prove2.me/theorems/0596cd18-3965-4f4d-82cb-7284c5071d68
-- title:
--   Closed forms $\mathbb P(\sigma_i)$, $\mathbb E|\sigma_i|$, $P_{ij}$, $l_{ij}$, $\pi_i$, $\mu_i$, $\alpha$ of (4) and $\mathcal R$
-- statement:
--   With $q_h=(1-q)p_h$ and $q_H=qp_h$, the module defines the explicit functions of $(p_h,q,\Delta,\theta)$ used in §3.1 and Appendix .2:
--
--   1. the pattern probabilities and expected lengths (p.9)
--   $$
--   \mathbb P(\sigma_1)=q_h[1-(1-p_h)^\Delta],\quad \mathbb P(\sigma_2)=q_h(1-p_h)^\Delta,\quad \mathbb P(\sigma_3)=q_H[1-(1-q_H)^\Delta],\quad \mathbb P(\sigma_4)=q_H(1-q_H)^\Delta,
--   $$
--   $$
--   \mathbb E|\sigma_1|=\frac1{p_h}-\frac{\Delta(1-p_h)^\Delta}{1-(1-p_h)^\Delta},\quad \mathbb E|\sigma_2|=\mathbb E|\sigma_4|=\frac1{p_h}+\Delta,\quad \mathbb E|\sigma_3|=\frac1{q_H}-\frac{\Delta(1-q_H)^\Delta}{1-(1-q_H)^\Delta};
--   $$
--   2. the transition matrix (3): rows $0$ and $1$ equal $\big((\mathbb P(\sigma_2)+\mathbb P(\sigma_4))/p_h,\ \mathbb P(\sigma_1)/p_h,\ \mathbb P(\sigma_3)/p_h\big)$, and row $2$ is $\big(\mathbb P(\sigma_4)/q_H,\ 0,\ \mathbb P(\sigma_3)/q_H\big)$;
--   3. the expected edge lengths $l_{ij}$ of App. .2.1: $l_{00}=l_{10}=\frac{\mathbb P(\sigma_2)\mathbb E|\sigma_2|+\mathbb P(\sigma_4)\mathbb E|\sigma_4|}{\mathbb P(\sigma_2)+\mathbb P(\sigma_4)}$, $l_{01}=l_{11}=\mathbb E|\sigma_1|$, $l_{02}=l_{12}=l_{22}=\mathbb E|\sigma_3|$, $l_{20}=\mathbb E|\sigma_4|$, $l_{21}=0$;
--   4. the stationary vector $\pi$ of App. .2.2, with $c=1/(q_H+q_h(1-q_H)^\Delta)$:
--   $\pi_0=c\,(q_H(1-q_H)^\Delta+q_h(1-q_H)^\Delta(1-p_h)^\Delta)$, $\pi_1=c\,q_h(1-q_H)^\Delta(1-(1-p_h)^\Delta)$, $\pi_2=c\,q_H(1-(1-q_H)^\Delta)$;
--   5. the expected sojourn times $\mu_i=\sum_jP_{ij}l_{ij}$ and their stationary mean $\sum_i\pi_i\mu_i$;
--   6. the first expression of $\alpha$ in Lemma 3.1,
--   $$
--   \frac{\pi_0P_{00}\mathbb P(\sigma_2)}{[\mathbb P(\sigma_2)+\mathbb P(\sigma_4)]\sum_i\pi_i\mu_i}\Big(1-\frac{\pi_2P_{20}}{\sum_i\pi_iP_{i0}}\Big)+\theta\,\frac{\pi_0P_{00}\mathbb P(\sigma_4)+\pi_1P_{10}\mathbb P(\sigma_4)}{[\mathbb P(\sigma_2)+\mathbb P(\sigma_4)]\sum_i\pi_i\mu_i};
--   $$
--   7. the exact expression (4),
--   $$
--   \alpha(p_h,q,\Delta,\theta)=\frac1{p_h}\Big[(1-q_H)^\Delta\big(q_h^2(1-p_h)^{2\Delta}+q_Hq_h(1-p_h)^\Delta(1-q_H)^\Delta+\theta p_hq_H(1-q_H)^\Delta\big)\Big],
--   $$
--   whose value at $q=0$ is Nakamoto's $\alpha_0=p_h(1-p_h)^{2\Delta}$;
--   8. the relative performance of a value $\alpha$,
--   $$
--   \mathcal R=\frac{\alpha/(\theta q+1-q)}{\alpha_0/1},
--   $$
--   the requirement normalized by the mean block weight $\theta q+1-q$, divided by Nakamoto's normalized by its mean block weight $1$.
--
--   These closed forms are the targets of the milestones; they carry no claim by themselves.
--
--   **Formalization Note** States $S_0,S_1,S_2$ are the indices $0,1,2$. The formulas are total functions: outside the parameter range $0<p_h,q<1$, $\Delta\ge1$ some denominators vanish and Lean's $x/0=0$ applies; every theorem of the mission assumes that range.
-- source:
--   Zhang, Gong, Li, Wu & Zhang, Improving Blockchain Consistency by Assigning Weights to Random Blocks, arXiv:2107.10467v2, p.9 (q_h, q_H, P(σ_i), E|σ_i|), Proposition 3.1 Eq. (3), p.10, Lemma 3.1 and Eq. (4), p.13, α₀ and R, p.14, Appendix .2.1–.2.3, pp.30–31

import Mathlib
import Definitions.Def_Ironclad_Decomposition

namespace Ironclad

/-- `q_h = (1 − q) p_h`, arXiv:2107.10467v2, p.9: the probability that a slot holds an honest
regular block. -/
def qh (ph q : ℝ) : ℝ := (1 - q) * ph

/-- `q_H = q p_h`, arXiv:2107.10467v2, p.9: the probability that a slot holds an honest iron
block. -/
def qH (ph q : ℝ) : ℝ := q * ph

/-- The occurrence probabilities `P(σᵢ)` of the patterns, arXiv:2107.10467v2, p.9:
`P(σ₁) = q_h[1 − (1 − p_h)^Δ]`, `P(σ₂) = q_h(1 − p_h)^Δ`, `P(σ₃) = q_H[1 − (1 − q_H)^Δ]`,
`P(σ₄) = q_H(1 − q_H)^Δ`. -/
def patProb (ph q : ℝ) (Δ : ℕ) : Pat → ℝ
  | .s1 => qh ph q * (1 - (1 - ph) ^ Δ)
  | .s2 => qh ph q * (1 - ph) ^ Δ
  | .s3 => qH ph q * (1 - (1 - qH ph q) ^ Δ)
  | .s4 => qH ph q * (1 - qH ph q) ^ Δ

/-- The expected lengths `E[|σᵢ|]` of the patterns, arXiv:2107.10467v2, p.9:
`E[|σ₁|] = 1/p_h − Δ(1 − p_h)^Δ/(1 − (1 − p_h)^Δ)`, `E[|σ₂|] = 1/p_h + Δ`,
`E[|σ₃|] = 1/q_H − Δ(1 − q_H)^Δ/(1 − (1 − q_H)^Δ)`, `E[|σ₄|] = 1/p_h + Δ`. -/
noncomputable def patMeanLen (ph q : ℝ) (Δ : ℕ) : Pat → ℝ
  | .s1 => 1 / ph - Δ * (1 - ph) ^ Δ / (1 - (1 - ph) ^ Δ)
  | .s2 => 1 / ph + Δ
  | .s3 => 1 / qH ph q - Δ * (1 - qH ph q) ^ Δ / (1 - (1 - qH ph q) ^ Δ)
  | .s4 => 1 / ph + Δ

/-- The transition matrix (3) of the embedded chain, Proposition 3.1, arXiv:2107.10467v2, p.10:
`P₀₀ = P₁₀ = (P(σ₂) + P(σ₄))/p_h`, `P₀₁ = P₁₁ = P(σ₁)/p_h`, `P₀₂ = P₁₂ = P(σ₃)/p_h`,
`P₂₀ = P(σ₄)/q_H`, `P₂₁ = 0`, `P₂₂ = P(σ₃)/q_H`. -/
noncomputable def Pmat (ph q : ℝ) (Δ : ℕ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![(patProb ph q Δ .s2 + patProb ph q Δ .s4) / ph, patProb ph q Δ .s1 / ph,
      patProb ph q Δ .s3 / ph;
    (patProb ph q Δ .s2 + patProb ph q Δ .s4) / ph, patProb ph q Δ .s1 / ph,
      patProb ph q Δ .s3 / ph;
    patProb ph q Δ .s4 / qH ph q, 0, patProb ph q Δ .s3 / qH ph q]

/-- The expected edge lengths `l_ij`, arXiv:2107.10467v2, Appendix .2.1, p.30:
`l₀₀ = l₁₀ = (P(σ₂)E[|σ₂|] + P(σ₄)E[|σ₄|])/(P(σ₂) + P(σ₄))`, `l₀₁ = l₁₁ = E[|σ₁|]`,
`l₀₂ = l₁₂ = l₂₂ = E[|σ₃|]`, `l₂₀ = E[|σ₄|]`, `l₂₁ = 0`. -/
noncomputable def lmat (ph q : ℝ) (Δ : ℕ) : Matrix (Fin 3) (Fin 3) ℝ :=
  let P := patProb ph q Δ
  let E := patMeanLen ph q Δ
  !![(P .s2 * E .s2 + P .s4 * E .s4) / (P .s2 + P .s4), E .s1, E .s3;
    (P .s2 * E .s2 + P .s4 * E .s4) / (P .s2 + P .s4), E .s1, E .s3;
    E .s4, 0, E .s3]

/-- The stationary distribution `π` of the embedded chain, arXiv:2107.10467v2, Appendix .2.2,
p.30, with `c = 1/(q_H + q_h(1 − q_H)^Δ)`:
`π₀ = c(q_H(1 − q_H)^Δ + q_h(1 − q_H)^Δ(1 − p_h)^Δ)`, `π₁ = c(q_h(1 − q_H)^Δ(1 − (1 − p_h)^Δ))`,
`π₂ = c(q_H(1 − (1 − q_H)^Δ))`. -/
noncomputable def piStat (ph q : ℝ) (Δ : ℕ) : Fin 3 → ℝ :=
  let c := 1 / (qH ph q + qh ph q * (1 - qH ph q) ^ Δ)
  ![c * (qH ph q * (1 - qH ph q) ^ Δ + qh ph q * (1 - qH ph q) ^ Δ * (1 - ph) ^ Δ),
    c * (qh ph q * (1 - qH ph q) ^ Δ * (1 - (1 - ph) ^ Δ)),
    c * (qH ph q * (1 - (1 - qH ph q) ^ Δ))]

/-- The expected sojourn time in state `S_i`, `μ_i = Σ_j P_ij l_ij`, arXiv:2107.10467v2,
Appendix .2.3, p.31. -/
noncomputable def muSoj (ph q : ℝ) (Δ : ℕ) (i : Fin 3) : ℝ :=
  ∑ j, Pmat ph q Δ i j * lmat ph q Δ i j

/-- `Σᵢ πᵢ μᵢ`, the mean pattern length under the stationary distribution. -/
noncomputable def meanCycle (ph q : ℝ) (Δ : ℕ) : ℝ :=
  ∑ i, piStat ph q Δ i * muSoj ph q Δ i

/-- The first expression of `α` in Lemma 3.1, arXiv:2107.10467v2, p.13:
`α = π₀P₀₀P(σ₂)/([P(σ₂) + P(σ₄)] Σπᵢμᵢ) · (1 − π₂P₂₀/Σπᵢ P_{i0})
  + θ(π₀P₀₀P(σ₄) + π₁P₁₀P(σ₄))/([P(σ₂) + P(σ₄)] Σπᵢμᵢ)`. -/
noncomputable def alphaPiMu (ph q : ℝ) (Δ : ℕ) (θ : ℝ) : ℝ :=
  let P := patProb ph q Δ
  let π := piStat ph q Δ
  let M := Pmat ph q Δ
  π 0 * M 0 0 * P .s2 / ((P .s2 + P .s4) * meanCycle ph q Δ) *
      (1 - π 2 * M 2 0 / ∑ i, π i * M i 0) +
    θ * (π 0 * M 0 0 * P .s4 + π 1 * M 1 0 * P .s4) / ((P .s2 + P .s4) * meanCycle ph q Δ)

/-- The exact expression (4) of `α`, arXiv:2107.10467v2, Lemma 3.1, p.13:
`α = (1/p_h)[(1 − q_H)^Δ(q_h²(1 − p_h)^{2Δ} + q_H q_h(1 − p_h)^Δ(1 − q_H)^Δ + θ p_h q_H(1 − q_H)^Δ)]`.
With `q = 0` it is Nakamoto's `α₀ = p_h(1 − p_h)^{2Δ}` (p.14). -/
noncomputable def alphaClosed (ph q : ℝ) (Δ : ℕ) (θ : ℝ) : ℝ :=
  1 / ph * ((1 - qH ph q) ^ Δ * (qh ph q ^ 2 * (1 - ph) ^ (2 * Δ) +
    qH ph q * qh ph q * (1 - ph) ^ Δ * (1 - qH ph q) ^ Δ + θ * ph * qH ph q * (1 - qH ph q) ^ Δ))

/-- The relative performance `R = (α/(θq + 1 − q))/(α₀/1)`, arXiv:2107.10467v2, p.14, of a value
`α` of the minimal mining-power requirement: `α` normalized by the mean block weight `θq + 1 − q`,
divided by Nakamoto's `α₀` (equation (4) at `q = 0`) normalized by its mean block weight `1`. -/
noncomputable def relPerf (ph q : ℝ) (Δ : ℕ) (θ α : ℝ) : ℝ :=
  (α / (θ * q + 1 - q)) / (alphaClosed ph 0 Δ θ / 1)

end Ironclad


