-- Prove2me | Definitions.Def_IoTFusion_KnownQuality_Model
-- name    : IoTFusion_KnownQuality_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T22:18:42.204842+00:00
-- url     : https://prove2.me/theorems/67bbcff4-6b0b-460b-988e-42b9c32e5f65
-- title:
--   §3–§5, pp. 9–15, 20 — sensors, qualities, initial familiarities (12), stickiness factor (14), variance criterion (10)–(11), familiarity/target recursion, long-run contacts (20)
-- statement:
--   The deterministic core of the known-quality model of Saghafian, Tomlin and Biller.
--
--   There are $n$ sensors $N = \{1,\dots,n\}$. Sensor $i$ has a **quality** $q_i$ (its measurement noise has variance $1/q_i^2$), and for every other sensor $j$ two **initial familiarities** $v_{ij0}, w_{ij0}$, the precisions of $i$'s initial beliefs about $j$'s inference parameters. A **sample path** is a sequence of realized states $S_\infty = (s_0, s_1, s_2, \dots)$ of real numbers.
--
--   1. **Initial familiarity** (12): $\displaystyle \psi_{ij1}(s) = \frac{v_{ij0}^2 w_{ij0}^2}{w_{ij0}^2 + v_{ij0}^2 s^2}$.
--   2. **Stickiness factor** (14), receiver first: $\displaystyle f(q_i,q_j) = \frac{1+q_i^2}{q_j^2(1+q_i^2+q_j^2)}$.
--   3. **Signal variance** (10): $\displaystyle \sigma^2_t(i,j,s_{t-1}) = \frac{q_j^2 + 1/\psi_{ijt}(s_{t-1})}{q_j^4}$.
--   4. **Target rule** (11): in period $t$, sensor $i$ targets
--   $$j^*_{it} = \arg\min_{j \in N\setminus\{i\}} \sigma^2_t(i,j,s_{t-1}),$$
--   ties broken in favour of the lower index (footnote 11). Write $a_{ijt} = 1$ if $j^*_{it} = j$ and $0$ otherwise.
--   5. **Familiarity dynamics** (Proposition 2(i), (14)): $\psi_{ij,t+1}(s) = \psi_{ijt}(s) + f(q_i,q_j)\,a_{ijt}$ for every $s \in \mathbb R$. Together with item 4 this is a joint recursion: the target of period $t$ is computed from the familiarities $\psi_{ijt}$ at the latest state $s_{t-1}$, and the familiarities of period $t+1$ from that target.
--   6. **Target counts**: $\sum_{l=1}^{t} a_{ijl}$, the number of the first $t$ periods in which $i$ targets $j$.
--   7. **Long-run contacts** (Definition 2, (20)):
--   $$T_i(S_\infty) = \{\, j \in N\setminus\{i\} : \lim_{t\to\infty} \psi_{ijt}(s_{t-1}) = \infty \,\}.$$
--
--   The whole trajectory of sensor $i$ — its familiarities, targets and long-run contacts — is a function of the instance $(q, v, w)$, the sensor $i$ and the path only. These objects carry every statement of the mission.
--
--   **Formalization Note** Sensors are `Fin n` (0-based). Periods are 0-based: Lean step $k$ is the paper's period $k+1$; the target at step $k$ uses the state $s_k$, and `fam P i s k j x` is $\psi_{ij,k+1}(x)$, so step $0$ is the initial familiarity (12) and `count P i s j k` is $\sum_{l=1}^{k} a_{ijl}$. The familiarity is **defined** by (12) and the update (14), the paper's familiarity dynamics: the paper derives the increment $f$ from Gaussian updating of the scalar $\hat\alpha_j + \hat\beta_j s_{t-1}$, which is exact at the realized state $s_{t-1}$ but not at other states. The target is the least-index minimizer over $j \ne i$; when there is no $j \ne i$ (only for $n \le 1$) it returns the junk value $i$, and every theorem needing a genuine target assumes $n \ge 2$. "$\lim = \infty$" is `Filter.Tendsto … atTop atTop`. The positivity assumptions $q_i > 0$, $v_{ij0}, w_{ij0} > 0$ are hypotheses of the theorems, not fields of the structure. The AR(1) dynamics of the state and the Gaussian signals motivate the rule but enter no statement.
-- source:
--   Saghafian, Tomlin, Biller, The Internet of Things and Information Fusion: Who Talks to Who?, SSRN 3124417 (version of October 16, 2020), pp. 9–15, 20, §3–§5: (10)–(12), (14), footnote 11 (p. 13), Proposition 2(i) (p. 15), Definition 2 (20) (p. 20)

import Mathlib

/-!
# Who talks to who: sensors, familiarity dynamics and long-run contacts

Saghafian, Tomlin, Biller, The Internet of Things and Information Fusion: Who Talks to Who?,
SSRN 3124417 (version of October 16, 2020), pp. 9–15 and 20: the sensors and their qualities
(§3, pp. 9–11), the initial familiarity (12), the stickiness factor f (14), the signal variance
(10), the target rule (11) with the tie-break of footnote 11 (p. 13), the familiarity dynamics of
Proposition 2 (p. 15), and the long-run contacts of Definition 2, (20) (p. 20).

**Formalization Note.**
* Sensors are `Fin n` (0-based); the paper's `N = {1, …, n}`.
* Periods are 0-based: Lean step `k` is the paper's period `k + 1`. The target chosen at step `k`
  uses the state `s k` (the paper's `s_{(k+1)-1}`), and `fam P i s k j x` is the paper's
  `ψ_{ij,k+1}(x)`. In particular `fam P i s 0 = ψ_{ij1}`, the initial familiarity (12).
* The familiarity `ψ` is *defined* by the initial condition (12) and the update (14) of
  Proposition 2(i), the paper's familiarity dynamics; the paper's Bayesian derivation of the
  increment is exact only at the realized state `s_{t-1}`.
* The target is the least-index minimizer of the signal variance (10) over `j ≠ i`
  (equation (11) and footnote 11). If no `j ≠ i` exists (`n ≤ 1`), it returns the junk value `i`;
  every theorem that needs a genuine target assumes `2 ≤ n`.
* The standing positivity assumptions (`q_i > 0`, `v_{ij0} > 0`, `w_{ij0} > 0`) are hypotheses of
  the theorems, not fields of `Instance`.
-/

namespace IoTFusion.KnownQuality

/-- An instance of the known-quality model with `n` sensors (pp. 9–11): the quality `q i` of
sensor `i` (its measurement noise has variance `1 / (q i)^2`, eq. (2)), and sensor `i`'s initial
familiarities `v i j = v_{ij0}`, `w i j = w_{ij0}` with sensor `j`'s inference parameters
(initial beliefs `N(α̂_j, 1/v_{ij0}^2)` and `N(β̂_j, 1/w_{ij0}^2)`, p. 11). -/
structure Instance (n : ℕ) where
  /-- `q i`: quality of sensor `i`. -/
  q : Fin n → ℝ
  /-- `v i j = v_{ij0}`: initial familiarity of `i` with `j`'s intercept `α̂_j`. -/
  v : Fin n → Fin n → ℝ
  /-- `w i j = w_{ij0}`: initial familiarity of `i` with `j`'s slope `β̂_j`. -/
  w : Fin n → Fin n → ℝ

/-- The stickiness factor (14), receiver first:
`f(q_i, q_j) = (1 + q_i^2) / (q_j^2 (1 + q_i^2 + q_j^2))`. -/
noncomputable def stick (qi qj : ℝ) : ℝ :=
  (1 + qi ^ 2) / (qj ^ 2 * (1 + qi ^ 2 + qj ^ 2))

/-- The initial familiarity function (12):
`ψ_{ij1}(x) = v_{ij0}^2 w_{ij0}^2 / (w_{ij0}^2 + v_{ij0}^2 x^2)`. -/
noncomputable def psi1 {n : ℕ} (P : Instance n) (i j : Fin n) (x : ℝ) : ℝ :=
  P.v i j ^ 2 * P.w i j ^ 2 / (P.w i j ^ 2 + P.v i j ^ 2 * x ^ 2)

/-- The signal-noise variance (10) of target `j` given familiarity value `ψ`:
`σ^2 = (q_j^2 + 1/ψ) / q_j^4`. -/
noncomputable def sigma2 (qj ψ : ℝ) : ℝ :=
  (qj ^ 2 + 1 / ψ) / qj ^ 4

/-- The minimizers of `c` over the sensors other than `i`. -/
noncomputable def minimizersExcept {n : ℕ} (i : Fin n) (c : Fin n → ℝ) : Finset (Fin n) :=
  by classical exact Finset.univ.filter (fun j : Fin n => j ≠ i ∧ ∀ k : Fin n, k ≠ i → c j ≤ c k)

/-- The target rule (11) with footnote 11 (p. 13): the **least-index** `j ≠ i` minimizing `c`
over all `k ≠ i`. Junk value `i` when there is no `j ≠ i` (i.e. `n ≤ 1`). -/
noncomputable def lowArgmin {n : ℕ} (i : Fin n) (c : Fin n → ℝ) : Fin n :=
  if h : (minimizersExcept i c).Nonempty then (minimizersExcept i c).min' h else i

/-- The familiarity dynamics along a state path `s : ℕ → ℝ` (`s k = s_k`, `s 0 = s_0`), for a
receiving sensor `i`. `fam P i s k j x` is the paper's `ψ_{ij,k+1}(x)`: at step `0` it is the
initial familiarity (12); from step `k` to `k + 1` the familiarity with `j` grows by the
stickiness factor `f(q_i, q_j)` exactly when `j` is the target chosen at step `k`, i.e. the
least-index minimizer over `j' ≠ i` of `σ^2(q_{j'}, ψ_{ij',k+1}(s_k))` (Proposition 2(i), (14)). -/
noncomputable def fam {n : ℕ} (P : Instance n) (i : Fin n) (s : ℕ → ℝ) : ℕ → Fin n → ℝ → ℝ
  | 0 => fun j x => psi1 P i j x
  | k + 1 => fun j x =>
      fam P i s k j x + stick (P.q i) (P.q j) *
        (if lowArgmin i (fun j' => sigma2 (P.q j') (fam P i s k j' (s k))) = j then 1 else 0)

/-- The target of sensor `i` at Lean step `k` (paper's `j*_{i,k+1}`, eq. (11)): the least-index
minimizer over `j ≠ i` of the signal variance at the latest realized state `s k`. -/
noncomputable def target {n : ℕ} (P : Instance n) (i : Fin n) (s : ℕ → ℝ) (k : ℕ) : Fin n :=
  lowArgmin i (fun j => sigma2 (P.q j) (fam P i s k j (s k)))

/-- The number of the first `k` steps (`0, …, k-1`) at which `i` targets `j`; the paper's
`Σ_{l=1}^{k} a_{ijl}`. -/
noncomputable def count {n : ℕ} (P : Instance n) (i : Fin n) (s : ℕ → ℝ) (j : Fin n) (k : ℕ) : ℕ :=
  ((Finset.range k).filter (fun l => target P i s l = j)).card

/-- The long-run contacts of sensor `i` along the path `s` (Definition 2, (20)):
`T_i(S∞) = {j ≠ i : ψ_{ijt}(s_{t-1}) → ∞}`; with `t = k + 1` this is `fam P i s k j (s k) → ∞`. -/
def longRunContacts {n : ℕ} (P : Instance n) (i : Fin n) (s : ℕ → ℝ) : Set (Fin n) :=
  {j | j ≠ i ∧ Filter.Tendsto (fun k => fam P i s k j (s k)) Filter.atTop Filter.atTop}

end IoTFusion.KnownQuality


