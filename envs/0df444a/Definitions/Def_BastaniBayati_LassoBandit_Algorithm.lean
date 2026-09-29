-- Prove2me | Definitions.Def_BastaniBayati_LassoBandit_Algorithm
-- name    : BastaniBayati_LassoBandit_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T09:07:00.181377+00:00
-- url     : https://prove2.me/theorems/6dbdc303-1463-4f72-ad0d-90be6fe48efc
-- title:
--   The LASSO Bandit algorithm and its cumulative expected regret
-- statement:
--   The LASSO Bandit of Bastani and Bayati (§3.3 and the algorithm box on p. 284), with input parameters $q\in\mathbb Z^+$, $h>0$, $\lambda_1$, $\lambda_{2,0}$.
--
--   **Forced-sample sets** (Eq. (2)). For arm $i\in[K]$,
--   $$\mathcal T_i=\{(2^n-1)\cdot Kq+j \mid n\in\{0,1,2,\dots\},\ j\in\{q(i-1)+1,\dots,qi\}\},$$
--   and $\mathcal T_{i,t}=\mathcal T_i\cap[t]$. The all-sample set is $\mathcal S_{i,t}=\{t'\in[t] : \pi_{t'}=i\}$. For a set of past times $\mathcal S'$, $\hat\beta(\mathcal S',\lambda)$ is the LASSO estimator on the covariates and observed rewards at the times in $\mathcal S'$, and $0$ when $\mathcal S'=\emptyset$.
--
--   **Round $t\ge 1$.** Observe $X_t$. If $t\in\mathcal T_i$ for some $i$, play $\pi_t=i$. Otherwise let
--   $$\hat{\mathcal K}=\{i\in[K] : X_t^\top\hat\beta(\mathcal T_{i,t-1},\lambda_1)\ge\max_{j\in[K]}X_t^\top\hat\beta(\mathcal T_{j,t-1},\lambda_1)-h/2\}$$
--   and play $\pi_t\in\arg\max_{i\in\hat{\mathcal K}}X_t^\top\hat\beta(\mathcal S_{i,t-1},\lambda_{2,t-1})$, where $\lambda_{2,t}=\lambda_{2,0}\sqrt{(\log t+\log d)/t}$ for $t\ge1$. Then observe $Y(t)=X_t^\top\beta_{\pi_t}+\varepsilon_{\pi_t,t}$.
--
--   **Regret.** The cumulative expected regret at time $T$ is
--   $$R_T=\sum_{t=1}^T\mathbb E\Big[\max_jX_t^\top\beta_j-X_t^\top\beta_{\pi_t}\Big].$$
--
--   The algorithm and its regret are the subject of Theorem 1 and Proposition 3.
--
--   **Formalization Note** The LASSO minimizer and the arg max may be non-unique; the algorithm is parameterized by a selection rule `sel` (returning a LASSO minimizer from the rows of the chosen times in increasing time order) and a tie-breaking rule `tb`, and the theorems hold for every such pair. Arms are `Fin K` (arm $i$ of the paper is `i.val + 1`). The trajectory is computed round by round: round $t$ reads only $X_1,\dots,X_t$, the arms played before $t$ and their observed rewards.
-- source:
--   Bastani & Bayati, Online Decision Making with High-Dimensional Covariates, Operations Research 68(1):276–294 (2020), doi:10.1287/opre.2019.1902, p. 280 (regret r_t, R_T), p. 283 (§3.1), p. 284 (§3.2.1, §3.3, Eq. (2), algorithm box)

import Mathlib
import Definitions.Def_BastaniBayati_LassoBandit_Basic

open MeasureTheory Finset

namespace BastaniBayati.LassoBandit

/-- The forced-sample set of arm `i`, Eq. (2), p. 284:
`𝒯ᵢ ≡ {(2ⁿ − 1)·Kq + j | n ∈ {0,1,2,…}, j ∈ {q(i−1)+1, …, qi}}`.
Arms are `Fin K`; the paper's arm `i ∈ [K]` is `i.val + 1`, so `q(i−1)+1 … qi` becomes
`q·i.val + 1 … q·(i.val+1)`. -/
def forcedSet (K q : ℕ) (i : Fin K) : Set ℕ :=
  {t | ∃ n j : ℕ, q * i.val + 1 ≤ j ∧ j ≤ q * (i.val + 1) ∧ t = (2 ^ n - 1) * K * q + j}

/-- `𝒯_{i,t} ≡ 𝒯ᵢ ∩ [t]`, the forced-sample times of arm `i` up to time `t` (§3.3.1). -/
noncomputable def forcedUpTo (K q : ℕ) (i : Fin K) (t : ℕ) : Finset ℕ :=
  by classical exact (Finset.Icc 1 t).filter (fun s => s ∈ forcedSet K q i)

/-- The all-sample regularization path of the algorithm: `λ₂,₀` at `t = 0` and
`λ₂,ₜ = λ₂,₀ √((log t + log d)/t)` for `t ≥ 1` (natural logarithms). -/
noncomputable def lam2 (lam20 : ℝ) (d t : ℕ) : ℝ :=
  if t = 0 then lam20 else lam20 * Real.sqrt ((Real.log t + Real.log d) / t)

/-- A LASSO selection rule: given `n` rows `Z : Fin n → ℝᵈ`, responses `W : Fin n → ℝ` and `λ`,
it returns a vector in `ℝᵈ`. It sees only the data of the chosen rows. -/
abbrev LassoSelector (d : ℕ) := (n : ℕ) → (Fin n → Fin d → ℝ) → (Fin n → ℝ) → ℝ → (Fin d → ℝ)

/-- The selection rule always returns a minimizer of the LASSO objective (1) for `λ ≥ 0`. -/
def IsLassoSelector {d : ℕ} (sel : LassoSelector d) : Prop :=
  ∀ (n : ℕ) (Z : Fin n → Fin d → ℝ) (W : Fin n → ℝ) (lam : ℝ), 0 ≤ lam →
    IsLassoMinimizer Z W lam (sel n Z W lam)

/-- A tie-breaking rule for `arg max_{i ∈ S} sᵢ`: given scores `s` and a set of arms `S`. -/
abbrev ArgmaxRule (K : ℕ) := (Fin K → ℝ) → Finset (Fin K) → Fin K

/-- The rule returns, for every nonempty `S`, an element of `S` maximizing the score over `S`. -/
def IsArgmaxRule {K : ℕ} (tb : ArgmaxRule K) : Prop :=
  ∀ (s : Fin K → ℝ) (S : Finset (Fin K)), S.Nonempty → tb s S ∈ S ∧ ∀ j ∈ S, s j ≤ s (tb s S)

/-- The LASSO estimate `β̂(𝒮', λ)` on the samples at the times in `𝒮'` (§3.2.1), with the rows
taken in increasing time order: `0 ∈ ℝᵈ` when `𝒮' = ∅` (the algorithm's initialisation), and
otherwise the selection rule applied to the rows `x_s` and responses `y_s`, `s ∈ 𝒮'`. -/
noncomputable def lassoEst {d : ℕ} (sel : LassoSelector d) (S : Finset ℕ) (x : ℕ → Fin d → ℝ)
    (y : ℕ → ℝ) (lam : ℝ) : Fin d → ℝ :=
  if S = ∅ then 0 else
    sel S.card (fun k => x (S.orderEmbOfFin rfl k)) (fun k => y (S.orderEmbOfFin rfl k)) lam

/-- One round `t ≥ 1` of the **LASSO Bandit** (algorithm box, p. 284). Its inputs are the
algorithm's parameters `q, h, λ₁, λ₂,₀`, the observed covariates `x` (only `x_s`, `s ≤ t`, are
read), the observed rewards `y` (only `y_s`, `s < t`, are read) and the arms `past` played before
`t` (only `past s`, `s < t`, are read).
* If `t ∈ 𝒯ᵢ` for some `i`, arm `i` is played (forced sampling; the sets `𝒯ᵢ` are disjoint).
* Otherwise `𝒦̂ = {i | x_tᵀβ̂(𝒯_{i,t−1}, λ₁) ≥ maxⱼ x_tᵀβ̂(𝒯_{j,t−1}, λ₁) − h/2}` and the arm
  played is `arg max_{i ∈ 𝒦̂} x_tᵀβ̂(𝒮_{i,t−1}, λ₂,ₜ₋₁)`, with
  `𝒮_{i,t−1} = {s ∈ [t−1] | past s = i}`. -/
noncomputable def banditStep {d K : ℕ} [NeZero K] (sel : LassoSelector d) (tb : ArgmaxRule K)
    (q : ℕ) (h lam1 lam20 : ℝ) (t : ℕ) (x : ℕ → Fin d → ℝ) (y : ℕ → ℝ) (past : ℕ → Fin K) :
    Fin K := by
  classical
  exact
    if hf : ∃ i : Fin K, t ∈ forcedSet K q i then Classical.choose hf
    else
      let fs : Fin K → Fin d → ℝ := fun i => lassoEst sel (forcedUpTo K q i (t - 1)) x y lam1
      let as : Fin K → Fin d → ℝ := fun i =>
        lassoEst sel ((Finset.Icc 1 (t - 1)).filter (fun s => past s = i)) x y
          (lam2 lam20 d (t - 1))
      let Khat : Finset (Fin K) :=
        Finset.univ.filter (fun i => (⨆ j, x t ⬝ᵥ fs j) - h / 2 ≤ x t ⬝ᵥ fs i)
      tb (fun i => x t ⬝ᵥ as i) Khat

/-- The arms played by the LASSO Bandit in rounds `1, …, t`, computed round by round: `r s i` is
the reward arm `i` would yield at time `s`, and round `t+1` is given only the rewards
`r s (π_s)` of the arms actually played before it. Entry `s` is meaningful for `1 ≤ s ≤ t`. -/
noncomputable def armHistory {d K : ℕ} [NeZero K] (sel : LassoSelector d) (tb : ArgmaxRule K)
    (q : ℕ) (h lam1 lam20 : ℝ) (x : ℕ → Fin d → ℝ) (r : ℕ → Fin K → ℝ) : ℕ → ℕ → Fin K
  | 0 => fun _ => 0
  | t + 1 =>
    Function.update (armHistory sel tb q h lam1 lam20 x r t) (t + 1)
      (banditStep sel tb q h lam1 lam20 (t + 1) x
        (fun s => r s (armHistory sel tb q h lam1 lam20 x r t s))
        (armHistory sel tb q h lam1 lam20 x r t))

/-- The arm `π_t` played by the LASSO Bandit at time `t ≥ 1` on the sample path `ω`, when the
covariates are `X_t(ω)` and pulling arm `i` at time `t` yields `X_t(ω)ᵀβᵢ + ε_{i,t}(ω)`. -/
noncomputable def lassoBanditArm {Ω : Type*} {d K : ℕ} [NeZero K] (sel : LassoSelector d)
    (tb : ArgmaxRule K) (q : ℕ) (h lam1 lam20 : ℝ) (X : ℕ → Ω → Fin d → ℝ)
    (ε : Fin K → ℕ → Ω → ℝ) (β : Fin K → Fin d → ℝ) (ω : Ω) (t : ℕ) : Fin K :=
  armHistory sel tb q h lam1 lam20 (fun s => X s ω) (fun s i => X s ω ⬝ᵥ β i + ε i s ω) t t

/-- The all-sample set `𝒮_{i,t} = {t' | π_{t'} = i, 1 ≤ t' ≤ t}` (§3.3.2) of a sequence of arms. -/
noncomputable def allSampleSet {K : ℕ} (arm : ℕ → Fin K) (i : Fin K) (t : ℕ) : Finset ℕ :=
  by classical exact (Finset.Icc 1 t).filter (fun s => arm s = i)

/-- The cumulative expected regret `R_T ≡ ∑_{t=1}^T E[maxⱼ X_tᵀβⱼ − X_tᵀβ_{π_t}]` (p. 280), the
expectation being over the covariates and the noise. -/
noncomputable def cumRegret {Ω : Type*} [MeasurableSpace Ω] {d K : ℕ} (P : Measure Ω)
    (X : ℕ → Ω → Fin d → ℝ) (β : Fin K → Fin d → ℝ) (arm : Ω → ℕ → Fin K) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.Icc 1 T, ∫ ω, ((⨆ j, X t ω ⬝ᵥ β j) - X t ω ⬝ᵥ β (arm ω t)) ∂P

end BastaniBayati.LassoBandit


