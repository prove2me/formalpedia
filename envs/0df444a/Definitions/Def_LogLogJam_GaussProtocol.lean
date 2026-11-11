-- Prove2me | Definitions.Def_LogLogJam_GaussProtocol
-- name    : LogLogJam_GaussProtocol
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:25:16.587685+00:00
-- url     : https://prove2.me/theorems/2654b99a-b2cd-4b3b-a515-6b9c319e9a36
-- title:
--   Adaptive protocols with randomized Gaussian measurements; success probability for Task 5.1; copy bound; $J_t$, $\bar J_t$, $\mathbb E[G(H_T)]$
-- statement:
--   A **$T$-adaptive protocol with Gaussian measurements** consists of
--
--   1. a measurement map: at each history $H$ of length $t<T$, a probability law on seeds $(k,W)$ with $W\in\mathrm{Cov}_k$ almost surely (a randomized Gaussian measurement on $k$ fresh copies);
--   2. an output map: from a history of length $T$, an estimate $\hat\theta$ of the squeezing angle.
--
--   Run on copies of $\rho_{\lambda,\theta}$, round $t+1$ draws the seed from the measurement map at $H_t$ and then the outcome $y$ with density $f^W_\theta$. With $\theta$ uniform on $\mathbb T$ (Task 5.1) the **success probability** is
--
--   $$
--   p_{\mathrm{succ}}=\frac1\pi\int_0^\pi\Pr_\theta\big[D_{\mathrm{tr}}(\rho_{\hat\theta},\rho_\theta)\le\varepsilon\big]\,d\theta .
--   $$
--
--   The protocol **uses at most $S$ copies** if, for every $\theta$, almost every length-$T$ history consumes at most $S$ copies. Its Fisher information up to time $t$ is $J_t(\theta)=\mathbb E_{H_t}[(\partial_\theta\log q_\theta(H_t))^2]$, the expected Fisher information is $\bar J_t=\mathbb E_{\theta\sim\mathrm{Unif}(\mathbb T)}J_t(\theta)$, and $\mathbb E[G(H_T)]$ is the expected final potential.
--
--   This is the model of Definition 4.4 in which Theorem 1.1 is a statement about every protocol: adaptive, entangled across copies, randomized, with any number of rounds.
--
--   **Formalization Note** Expectations over histories are computed round by round with lower Lebesgue integrals, so no measurability side condition can turn a probability into a junk $0$. The number of copies may itself be random given the history (Definition 4.4's protocols are the case of a deterministic $k$). The kernels and the output map are measurable, which excludes only protocols whose success probability is undefined. The copy bound is the almost-sure form of "the maximum over consistent histories".
-- source:
--   Chen, Gong, Ye, Zhang, The log log jam in Gaussian state tomography, arXiv:2607.12983 (version of November 3, 2026, sha256 97b751ca…), Definition 4.4, pp.17–18 (PDF pp.20–21); §4.2, p.17 (randomized measurements); Task 5.1, p.22 (PDF p.25); §5.2–5.3, pp.23–24; §6.2, eqs. (14), (18), pp.30–32

import Mathlib
import Definitions.Def_LogLogJam_postFisher

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LogLogJam

/-- A **`T`-adaptive learning protocol with (randomized, possibly entangled) Gaussian
measurements** for the squeezed family (arXiv:2607.12983, version of November 3, 2026, sha256
97b751ca…, Definition 4.4, pp.17–18, and §4.2, p.17).

* `seed t` is the measurement map `P_M` at round `t + 1`: given the history `H` of length `t`, it is
  the law of the next seed `(k, W)`, a randomized Gaussian measurement (an ensemble of seeds,
  continuous ensembles allowed). Its draws lie in `Cov_k` almost surely.
* `out` is the output map `P_O`: from a history of length `T` it outputs an estimate `θ̂ ∈ ℝ` of the
  squeezing angle (Task 5.1, p.22).

**Formalization Note**
1. The seed choice is a Markov kernel and the drawn seed is recorded in the observation; the number
   of copies `k` may itself be random given the history (Definition 4.4 has `k` a function of the
   history: the Dirac case).
2. Seeds are given for every round `t`; only rounds `t < T` are used.
3. The kernels and the output map are measurable; otherwise the success probability is undefined.
4. `k = 0` (null measurements, p.18) is allowed. -/
structure GaussProtocol (T : ℕ) where
  /-- The law of the next seed `(k, W)` given the history. -/
  seed : (t : ℕ) → Kernel (Hist t) Seed
  /-- Each seed law is a probability measure. -/
  isMarkov : ∀ t, IsMarkovKernel (seed t)
  /-- The seed matrices are valid covariance matrices, almost surely. -/
  seed_cov : ∀ (t : ℕ) (H : Hist t), ∀ᵐ s ∂(seed t H), IsCov s.1 (Matrix.of s.2)
  /-- The output map: an estimate `θ̂` of the squeezing angle. -/
  out : Hist T → ℝ
  /-- The output map is measurable. -/
  measurable_out : Measurable out

/-- The expectation `E_θ[Φ(H_t)]` of a nonnegative function of the history of length `t` when the
protocol `P` runs on copies of `ρ_{λ,θ}` (arXiv:2607.12983, version of November 3, 2026, sha256
97b751ca…, §5.2, p.23: the next observation `h_t = (M_t, y_t)` has conditional density
`f^{M_t}_θ(y_t)` given `θ` and `H_{t−1}`).

**Formalization Note** Defined round by round: the last round is integrated first (the seed against
the protocol's kernel, the outcome against Lebesgue measure with density `f^W_θ`), then the earlier
rounds. Lower Lebesgue integrals of nonnegative functions, so no measurability or integrability
side condition can turn the value into a junk `0`. -/
noncomputable def histInt (lam θ : ℝ) {T : ℕ} (P : GaussProtocol T) :
    (t : ℕ) → (Hist t → ℝ≥0∞) → ℝ≥0∞
  | 0, Φ => Φ Fin.elim0
  | t + 1, Φ => histInt lam θ P t (fun H =>
      ∫⁻ s, ∫⁻ y, ENNReal.ofReal (outDens s.1 (VsqK lam θ s.1 + Matrix.of s.2) y) *
        Φ (Fin.snoc H ⟨s.1, (s.2, y)⟩) ∂volume ∂(P.seed t H))

/-- The success probability of `P` on Task 5.1 (arXiv:2607.12983, version of November 3, 2026,
sha256 97b751ca…, Task 5.1, p.22, and §5.2, p.23): `θ` is drawn uniformly from `𝕋 = [0, π)`, the
protocol runs on copies of `ρ_{λ,θ}`, and it succeeds when `D_tr(ρ_{θ̂}, ρ_θ) ≤ ε`. -/
noncomputable def succProb (lam ε : ℝ) {T : ℕ} (P : GaussProtocol T) : ℝ≥0∞ :=
  ENNReal.ofReal (1 / Real.pi) * ∫⁻ θ in Set.Ico 0 Real.pi,
    histInt lam θ P T (Set.indicator {H | trDist lam (P.out H) θ ≤ ε} 1)

/-- `P` uses at most `S` copies (arXiv:2607.12983, version of November 3, 2026, sha256 97b751ca…,
Definition 4.4, p.18: "The sample complexity of the protocol P is defined as the maximum total
number of samples consumed in any consistent length-T history").

**Formalization Note** Read as: for every `θ`, almost every length-`T` history consumes at most `S`
copies. This is implied by the bound on every consistent history. -/
def CopiesLe (lam : ℝ) {T : ℕ} (P : GaussProtocol T) (S : ℕ) : Prop :=
  ∀ θ : ℝ, histInt lam θ P T (Set.indicator {H | S < copies H} 1) = 0

/-- The Fisher information of `P` up to time `t` at `θ`:
`J_t(θ) = E_{H_t}[(∂_θ log q_θ(H_t))²]` (arXiv:2607.12983, version of November 3, 2026, sha256
97b751ca…, §5.3, p.23). -/
noncomputable def protoFisher (lam : ℝ) {T : ℕ} (P : GaussProtocol T) (t : ℕ) (θ : ℝ) : ℝ≥0∞ :=
  histInt lam θ P t (fun H => ENNReal.ofReal ((deriv (fun θ' => Real.log (histDens lam θ' H)) θ) ^ 2))

/-- The expected Fisher information `J̄_t = E_{θ∼Unif(𝕋)}[J_t(θ)]` (arXiv:2607.12983, version of
November 3, 2026, sha256 97b751ca…, §5.3, p.24). -/
noncomputable def Jbar (lam : ℝ) {T : ℕ} (P : GaussProtocol T) (t : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (1 / Real.pi) * ∫⁻ θ in Set.Ico 0 Real.pi, protoFisher lam P t θ

/-- `E[G(H_T)]`, the expected potential of §6.2 at the end of the protocol, with `θ` uniform on `𝕋`
(arXiv:2607.12983, version of November 3, 2026, sha256 97b751ca…, eqs. (14), (18), pp.30–32). -/
noncomputable def expG (lam : ℝ) {T : ℕ} (P : GaussProtocol T) : ℝ≥0∞ :=
  ENNReal.ofReal (1 / Real.pi) * ∫⁻ θ in Set.Ico 0 Real.pi, histInt lam θ P T (Gpot lam)

end LogLogJam


