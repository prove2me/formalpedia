-- Prove2me | Definitions.Def_LogLogJam_Supplement_SCGaussProtocol
-- name    : LogLogJam_Supplement_SCGaussProtocol
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:51:54.143284+00:00
-- url     : https://prove2.me/theorems/75b15bff-92d0-4b91-8d1a-f449badf1a9a
-- title:
--   $T$-round protocols with single-copy Gaussian measurements on single-mode Gaussian states
-- statement:
--   A seed $W\in\mathbb R^{2k\times 2k}$ for a $k$-copy Gaussian measurement (q-then-p order) is **single-copy** when $W=W_1\oplus\cdots\oplus W_k$ with every $W_i\in\mathrm{Cov}_1=\{W\in\mathbb R^{2\times2}:W=W^\top,\ W+i\Omega\succeq0\}$: each copy is measured separately.
--
--   A **$T$-round protocol with single-copy Gaussian measurements** (Definition 4.4) consists of
--
--   1. for each round $t<T$, a (possibly randomized) choice of the next seed $(k,W)$ given the history $H$ of earlier seeds and outcomes, whose draws are single-copy seeds;
--   2. an output map giving, from the full history, a (possibly randomized) estimate $\hat\rho$, a density operator on the single-mode Fock space.
--
--   Run on copies of a single-mode Gaussian state $\rho(m,V)$, a measurement with seed $W$ on $k$ copies returns $y\in\mathbb R^{2k}$ distributed as $N\big(m\otimes1_k,(V\otimes I_k+W)/2\big)$. The **success probability** at accuracy $\varepsilon$ is the probability that $D_{\mathrm{tr}}(\hat\rho,\rho)\le\varepsilon$, with $D_{\mathrm{tr}}=\tfrac12\|\cdot\|_1$. The protocol **uses at most $N$ copies** if every history it can produce consumes at most $N$ copies in total. The **energy** of $\rho(m,V)$ is
--
--   $$
--   E(\rho)=\tfrac14\operatorname{tr}V+\tfrac12\|m\|_2^2 .
--   $$
--
--   These objects state the bounded-adaptivity upper bound, Theorem 7.7.
--
--   **Formalization Note** Histories, seeds and observations are the base mission's `LogLogJam.Hist`, `Seed`, `Obs`, and the outcome density is its `outDens` (the density of $N(0,D/2)$) at $D=V\otimes I_k+W$, evaluated at $y-m\otimes1_k$. The seed choices and the output are Markov kernels; the number of copies $k$ may be random given the history, and $k=0$ (a null measurement) is allowed. The copy bound is required at every round, for every history using at most $N$ copies so far, for almost every drawn seed; it does not depend on the state.
-- source:
--   Chen, Gong, Ye, Zhang, The log log jam in Gaussian state tomography, arXiv:2607.12983 (version of November 3, 2026, sha256 97b751ca…), Definition 4.4, pp.17–18 (PDF pp.20–21); §4.2, p.15 and p.17 (PDF pp.18, 20); §7, p.34 (PDF p.37); Algorithm 1, p.36 (PDF p.39)

import Mathlib
import Definitions.Def_LogLogJam_Obs
import Definitions.Def_LogLogJam_Supplement_IsGaussQP
import Definitions.Def_BosonicLearn_traceDist

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)

namespace LogLogJam.Supplement

open LogLogJam

/-- A `k`-copy seed `W ∈ ℝ^{2k×2k}` (q-then-p ordering `Q k = Fin 2 × Fin k`) is **single-copy**:
`W = W₁ ⊕ ⋯ ⊕ W_k` is block diagonal across copies and every block `W_i` lies in `Cov_1`
(arXiv:2607.12983, version of November 3, 2026, sha256 97b751ca…, §4.2, p.17: single-copy Gaussian
measurements are the direct sums of single-copy seeds). -/
def IsSingleCopySeed (k : ℕ) (W : Q k → Q k → ℝ) : Prop :=
  (∀ (a b : Fin 2) (i j : Fin k), i ≠ j → W (a, i) (b, j) = 0) ∧
    ∀ i : Fin k, IsCov 1 (Matrix.of fun (x y : Q 1) => W (x.1, i) (y.1, i))

/-- The covariance `V ⊗ I_k` of `ρ(m, V)^{⊗k}` in the q-then-p ordering, for a single-mode
covariance `V` (arXiv:2607.12983, version of November 3, 2026, sha256 97b751ca…, §4.2, p.15: "The
tensored state ρ(m, V)^{⊗k} will become ρ(m ⊗ 1_k, V ⊗ I_k)"). Entry `((a,i),(b,j))` is
`V((a,0),(b,0)) δ_ij`. -/
noncomputable def covK (V : Matrix (Q 1) (Q 1) ℝ) (k : ℕ) : Matrix (Q k) (Q k) ℝ :=
  Matrix.of fun x y => if x.2 = y.2 then V (x.1, 0) (y.1, 0) else 0

/-- The mean `m ⊗ 1_k` of `ρ(m, V)^{⊗k}` in the q-then-p ordering (arXiv:2607.12983, version of
November 3, 2026, sha256 97b751ca…, §4.2, p.15). -/
def meanK (m : Q 1 → ℝ) (k : ℕ) : Q k → ℝ :=
  fun x => m (x.1, 0)

/-- The energy `E(ρ) = ¼ Tr V + ½ ‖m‖²` of the single-mode Gaussian state `ρ(m, V)`
(arXiv:2607.12983, version of November 3, 2026, sha256 97b751ca…, §4.2, p.15, and §7, p.34). -/
noncomputable def energyGen (m : Q 1 → ℝ) (V : Matrix (Q 1) (Q 1) ℝ) : ℝ :=
  Matrix.trace V / 4 + (∑ x, m x ^ 2) / 2

/-- A **`T`-round protocol with (randomized) single-copy Gaussian measurements** for single-mode
states, outputting a description of a state (arXiv:2607.12983, version of November 3, 2026, sha256
97b751ca…, Definition 4.4, pp.17–18; §4.2, p.17; Theorem 7.7, p.35; Algorithm 1, p.36).

* `seed t` is the measurement map at round `t + 1`: given the history of length `t`, the law of
  the next seed `(k, W)`; its draws are single-copy seeds (`IsSingleCopySeed`) almost surely.
* `out` is the output map: from a history of length `T`, a (possibly randomized) estimate `ρ̂`, a
  density operator on the single-mode Fock space.

**Formalization Note**
1. Histories, seeds and observations are the base mission's `Hist`, `Seed`, `Obs`; the drawn seed
   is recorded in the observation and `k` may be random given the history (`k = 0` allowed, the null
   measurement of p.18).
2. Seeds are given for every round `t`; only rounds `t < T` are used.
3. Randomized seeds and a randomized output are Markov kernels (measurable); Definition 4.4 notes
   the randomness can be absorbed, so this is the same class. -/
structure SCGaussProtocol (T : ℕ) where
  /-- The law of the next seed `(k, W)` given the history. -/
  seed : (t : ℕ) → Kernel (Hist t) Seed
  /-- Each seed law is a probability measure. -/
  isMarkov : ∀ t, IsMarkovKernel (seed t)
  /-- The drawn seeds are single-copy seeds, almost surely. -/
  seed_sc : ∀ (t : ℕ) (H : Hist t), ∀ᵐ s ∂(seed t H), IsSingleCopySeed s.1 s.2
  /-- The output map: the law of the estimated state `ρ̂` given the full history. -/
  out : Kernel (Hist T) (State (Occupation (Fin 1)))
  /-- The output law is a probability measure. -/
  isMarkov_out : IsMarkovKernel out

/-- The expectation of a nonnegative function of the history of length `t` when the protocol `P`
runs on copies of the single-mode Gaussian state `ρ(m, V)` (arXiv:2607.12983, version of
November 3, 2026, sha256 97b751ca…, §4.2, p.17: a measurement with seed `W` on `k` copies of
`ρ(m, V)` has outcome law `N(m ⊗ 1_k, (V ⊗ I_k + W)/2)`).

**Formalization Note** Round by round, as the base mission's `histInt`: the outcome density is the
base `outDens k D` (the density of `N(0, D/2)`) at `D = V ⊗ I_k + W`, evaluated at `y − m ⊗ 1_k`.
Lower Lebesgue integrals, so no junk value from non-integrability. -/
noncomputable def histIntGen (m : Q 1 → ℝ) (V : Matrix (Q 1) (Q 1) ℝ) {T : ℕ}
    (P : SCGaussProtocol T) : (t : ℕ) → (Hist t → ℝ≥0∞) → ℝ≥0∞
  | 0, Φ => Φ Fin.elim0
  | t + 1, Φ => histIntGen m V P t (fun H =>
      ∫⁻ s, ∫⁻ y, ENNReal.ofReal (outDens s.1 (covK V s.1 + Matrix.of s.2) (y - meanK m s.1)) *
        Φ (Fin.snoc H ⟨s.1, (s.2, y)⟩) ∂volume ∂(P.seed t H))

/-- The probability that `P`, run on copies of `ρ(m, V)`, outputs `ρ̂` with
`D_tr(ρ̂, ρ) ≤ ε`, where `ρ` is the density operator of `ρ(m, V)` (arXiv:2607.12983, version of
November 3, 2026, sha256 97b751ca…, Theorem 7.7, p.35). `D_tr = ½‖·‖₁` is the published
`BosonicLearn.traceDist`. -/
noncomputable def scSuccProb (m : Q 1 → ℝ) (V : Matrix (Q 1) (Q 1) ℝ)
    (ρ : State (Occupation (Fin 1))) (ε : ℝ) {T : ℕ} (P : SCGaussProtocol T) : ℝ≥0∞ :=
  histIntGen m V P T (fun H =>
    P.out H {σ | BosonicLearn.traceDist σ.coefficients ρ.coefficients ≤ ENNReal.ofReal ε})

/-- `P` uses at most `N` copies (arXiv:2607.12983, version of November 3, 2026, sha256 97b751ca…,
Definition 4.4, p.18: "The sample complexity of the protocol P is defined as the maximum total number
of samples consumed in any consistent length-T history").

**Formalization Note** Read round by round and independently of the state: at every round `t < T`
and every history `H` that has used at most `N` copies, almost every seed drawn by the protocol keeps
the total at most `N`. Hence every history the protocol can produce uses at most `N` copies, whatever
the outcomes. -/
def SCCopiesLe {T : ℕ} (P : SCGaussProtocol T) (N : ℕ) : Prop :=
  ∀ t : ℕ, t < T → ∀ H : Hist t, copies H ≤ N → ∀ᵐ s ∂(P.seed t H), copies H + s.1 ≤ N

end LogLogJam.Supplement


