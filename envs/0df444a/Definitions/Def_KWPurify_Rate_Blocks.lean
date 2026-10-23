-- Prove2me | Definitions.Def_KWPurify_Rate_Blocks
-- name    : KWPurify_Rate_Blocks
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T17:29:05.906483+00:00
-- url     : https://prove2.me/theorems/fc7bd71a-13ea-4b6f-89c8-5680fd493139
-- title:
--   Spin weights $w_N(s)$, multiplicities $\dim\mathcal K_{N,s}$, Bose states $\rho_s(\beta)$, the optimal block maps $\hat Q_{2s*}$ and the closed form $f_{\mathrm{all}}$ (pp. 7–15, 21)
-- statement:
--   This file collects the explicit objects of the proof of the purification rate, in the "pseudo-temperature" parametrization $\lambda = \tanh\beta$, $\beta > 0$, and with $q = e^{-2\beta}$.
--
--   **Spin labels.** For $N$ qubits the spins are $s \in I[N] = \{N/2, N/2-1, \dots\} \cap [0,\infty)$. They are encoded by $k = N/2 - s \in \{0,1,\dots,\lfloor N/2\rfloor\}$, so that $2s = N - 2k$ is a natural number.
--
--   1. **Multiplicities.** $\dim\mathcal K_{N,s} = \dfrac{2s+1}{N/2+s+1}\dbinom{N}{N/2-s} = \dfrac{N-2k+1}{N-k+1}\dbinom{N}{k}$.
--   2. **Weights** (eq. (14)):
--   $$w_N(s) = \frac{\sinh((2s+1)\beta)}{\sinh(\beta)\,(2\cosh\beta)^N}\,\dim\mathcal K_{N,s}.$$
--   3. **Bose states.** On $n = 2s$ qubits, with $\psi = (1,0)$, $L_3 = \tfrac12\sum_i \sigma_3^{(i)}$ and $S_n$ the orthogonal projector onto the symmetric subspace,
--   $$\rho_s(\beta) = \frac{\sinh\beta}{\sinh((n+1)\beta)}\, S_n\, e^{2\beta L_3};$$
--   $e^{2\beta L_3}$ is diagonal in the product basis with entry $e^{\beta(\#0\text{'s} - \#1\text{'s})}$ on a word.
--   4. **Optimal block maps** $\hat Q_{n*}$ from $n$ to $M$ qubits (eqs. (17), (18)): for $M \le n$ the partial trace over the first $n - M$ tensor factors; for $M > n$ the optimal cloner $\theta \mapsto \frac{n+1}{M+1} S_M(\theta\otimes\mathbb 1^{\otimes(M-n)})S_M$.
--   5. **Closed form** (eq. (32), corrected):
--   $$f_{\mathrm{all}}(M,\beta,s) = \begin{cases} \dfrac{n+1}{M+1}\,\dfrac{1-q}{1-q^{n+1}} & M > n,\\[2mm] \dfrac{1-q}{1-q^{n+1}}\dbinom{n}{M}^{-1}\displaystyle\sum_{K=M}^{n}\binom{K}{M} q^{\,n-K} & M \le n.\end{cases}$$
--   6. **Binomial ratio sum** (Lemma 6.2): for natural $M, K$ and $z \in \mathbb C$, $\displaystyle \Phi(K,M,z) = \binom{K}{M}^{-1}\sum_{R=M}^{K}\binom{R}{M} z^{K-R}$, renamed `binomRatioSum` to avoid a clash with the rate function.
--
--   These objects describe the optimal purifier block by block; the weights $w_N$ form a probability vector concentrating at $2s/N \approx \lambda$, which is what turns the finite-$N$ formula into the rate function.
--
--   **Formalization Note** In (32) the printed case labels are swapped and the exponent is printed as $e^{2\beta(K-s)}$; the definition uses the corrected form ($e^{2\beta(K-2s)} = q^{n-K}$, cloner branch for $M > 2s$), see the corrected milestones. Junk values: $\binom{n}{M}^{-1}$ is only used for $M \le n$, where it is nonzero; at $\beta = 0$ the normalizations divide by $\sinh 0 = 0$ and $1 - q^{n+1} = 0$, so every statement assumes $\beta > 0$. The cloner is the published `canonicalCloner`, which also compresses its input to the input symmetric subspace; $\rho_s(\beta)$ lives there, so this is harmless. The symmetric projector is the published `boseProjector`.
-- source:
--   Keyl & Werner, The Rate of Optimal Purification procedures, arXiv:quant-ph/9910124v1, p. 7 (I[N]), p. 8 eqs. (12)–(14), p. 9 (dim K_{N,s}), p. 10 Theorem 3.1 eqs. (17)–(18), pp. 14–15 eq. (32), p. 21 Lemma 6.2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P45
import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P16

namespace KWPurify.Rate

open QAlgorithms
open QAlgorithms.Papers.Independent.Renew46.P45 (boseProjector)
open QAlgorithms.Papers.Independent.Support21.P16 (canonicalCloner)

/-! Spin labels `s ∈ I[N]` (p. 7) are encoded by `k = N/2 − s ∈ {0, …, ⌊N/2⌋}`, so that
`2s = N − 2k` is a natural number; sums over `I[N]` are sums over `Finset.range (N / 2 + 1)`. -/

/-- pp. 8–9: the multiplicity `dim K_{N,s} = (2s+1)/(N/2+s+1) · binom(N, N/2−s)`, written with
`k = N/2 − s`: `(N − 2k + 1)/(N − k + 1) · binom(N, k)`. -/
noncomputable def spinMult (N k : ℕ) : ℝ :=
  ((N - 2 * k : ℕ) + 1 : ℝ) / ((N - k : ℕ) + 1 : ℝ) * (N.choose k : ℝ)

/-- p. 8, eq. (14): the weight
`w_N(s) = sinh((2s+1)β) / (sinh(β)(2cosh β)^N) · dim K_{N,s}`, with `2s = N − 2k`. -/
noncomputable def spinWeight (β : ℝ) (N k : ℕ) : ℝ :=
  Real.sinh (((N - 2 * k : ℕ) + 1 : ℝ) * β) / (Real.sinh β * (2 * Real.cosh β) ^ N) *
    spinMult N k

/-- p. 8, eq. (13): `exp(2β L_3)` on `n` qubits, diagonal in the product basis with entry
`exp(β Σ_i ε(x_i))`, `ε(0) = +1`, `ε(1) = −1` (basis vector `0` is `ψ = (1, 0)`). -/
noncomputable def expL3 (β : ℝ) (n : ℕ) : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  Matrix.diagonal fun x => (Real.exp (β * ∑ i, (if x i = 0 then (1 : ℝ) else -1)) : ℂ)

/-- p. 8: the state `ρ_s(β) = sinh β / sinh((2s+1)β) · exp(2β L_3^{(s)})` on the Bose subspace of
`n = 2s` qubits, as an operator on all `n` qubits: `sinh β / sinh((n+1)β) · S_n exp(2βL_3)`, with
`S_n` the projector onto the symmetric subspace. -/
noncomputable def boseState (β : ℝ) (n : ℕ) : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  ((Real.sinh β / Real.sinh (((n : ℝ) + 1) * β) : ℝ) : ℂ) • (boseProjector 2 n * expL3 β n)

/-- The one-qubit pure state `|ψ⟩⟨ψ|`, `ψ = (1, 0)` (p. 8, eq. (12)). -/
noncomputable def psiDensity : Matrix (Fin 2) (Fin 2) ℂ :=
  pureDensity (EuclideanSpace.single (0 : Fin 2) (1 : ℂ))

/-- Concatenation of a word on the first `n − M` qubits and a word on the last `M` qubits. -/
def joinWord {n M : ℕ} (h : M ≤ n) (z : Fin (n - M) → Fin 2) (y : Fin M → Fin 2) :
    Fin n → Fin 2 :=
  fun i => Fin.append z y (Fin.cast (by omega) i)

/-- p. 10, eq. (18): `tr_{n−M}`, the partial trace over the first `n − M` tensor factors. -/
noncomputable def traceFirst {n M : ℕ} (h : M ≤ n)
    (θ : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) :
    Matrix (Fin M → Fin 2) (Fin M → Fin 2) ℂ :=
  Matrix.of fun y y' => ∑ z : Fin (n - M) → Fin 2, θ (joinWord h z y) (joinWord h z y')

/-- p. 10, Theorem 3.1 items 3–4: the predual `Q̂_{n*}` of the optimal map from `n = 2s` to `M`
qubits: for `M ≤ n` the partial trace (18); for `M > n` the optimal cloner (17),
`(n+1)/(M+1) · S_M (θ ⊗ 𝟙^{⊗(M−n)}) S_M` (`canonicalCloner`, which also compresses `θ` to the
input Bose subspace; `ρ_s(β)` lives there). -/
noncomputable def optimalBlockMap (n M : ℕ) (θ : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) :
    Matrix (Fin M → Fin 2) (Fin M → Fin 2) ℂ :=
  if h : M ≤ n then traceFirst h θ
  else canonicalCloner (d := 2) (N := n) (M := M) (by omega) θ

/-- pp. 14–15, eq. (32), corrected: with `q = e^{−2β}` and `n = 2s`,
`f_all(M, β, s) = (n+1)/(M+1) · (1−q)/(1−q^{n+1})` if `M > n`, and
`(1−q)/(1−q^{n+1}) · binom(n, M)^{−1} Σ_{K=M}^{n} binom(K, M) q^{n−K}` if `M ≤ n`. -/
noncomputable def fAll (M : ℕ) (β : ℝ) (n : ℕ) : ℝ :=
  if n < M then
    ((n : ℝ) + 1) / ((M : ℝ) + 1) *
      ((1 - Real.exp (-2 * β)) / (1 - Real.exp (-2 * β) ^ (n + 1)))
  else
    (1 - Real.exp (-2 * β)) / (1 - Real.exp (-2 * β) ^ (n + 1)) *
      ((n.choose M : ℝ)⁻¹ *
        ∑ K ∈ Finset.Icc M n, (K.choose M : ℝ) * Real.exp (-2 * β) ^ (n - K))

/-- p. 21, Lemma 6.2: `Φ(K, M, z) = binom(K, M)^{−1} Σ_{R=M}^{K} binom(R, M) z^{K−R}` (renamed to
avoid a clash with the rate function). -/
noncomputable def binomRatioSum (K M : ℕ) (z : ℂ) : ℂ :=
  ((K.choose M : ℂ))⁻¹ * ∑ R ∈ Finset.Icc M K, (R.choose M : ℂ) * z ^ (K - R)

end KWPurify.Rate


