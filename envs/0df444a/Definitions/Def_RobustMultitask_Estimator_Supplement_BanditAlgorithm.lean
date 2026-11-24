-- Prove2me | Definitions.Def_RobustMultitask_Estimator_Supplement_BanditAlgorithm
-- name    : RobustMultitask_Estimator_Supplement_BanditAlgorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T06:59:58.591282+00:00
-- url     : https://prove2.me/theorems/25444eca-82d7-4c53-a1b8-f4f23e257f3c
-- title:
--   Algorithm 2 and (35), pp. 25–26, 55 — the RMBandit trajectory, its batches and estimators, and the event 𝒜
-- statement:
--   RMBandit (Algorithm 2) over a total horizon $H$.
--
--   1. **Batches.** $\mathcal B_0=\{1,\dots,|\mathcal B_0|\}$ and $\mathcal B_m=\{t: 2^{m-1}|\mathcal B_0|<t\le 2^m|\mathcal B_0|\}$ for $m\ge1$, all intersected with $[H]$; $\mathcal B_{\bar m}=\mathcal B_0\cup\dots\cup\mathcal B_m$. Here $|\mathcal B_0|=\lceil q\log H\rceil$.
--   2. **Sample sets.** $\mathcal B^i(S)$ are the arrivals at instance $i$ among the times $S$, and $\mathcal B^i_k(S)$ those at which arm $k$ was pulled.
--   3. **RMEstimator on samples.** For donor instances $D$, OLS on each $\mathcal B^i_k(\cdot)$, $i\in D$, the componentwise trimmed mean with level $\omega$, then the shifted LASSO with level $\lambda$ on the target's samples, centred at the trimmed mean.
--   4. **Forced-sample estimator** $\widehat\beta^j_{k,0}=\widehat\beta^j_k(\mathcal B_0,\lambda_{0,j},\omega_0)$ with $\lambda_{0,j}=\lambda_0^{(j)}/\sqrt{|\mathcal B^j_0|}$.
--   5. **All-sample estimator** $\widehat\beta^j_{k,\bar m}=\widehat\beta^j_k(\mathcal B_{\bar m},\lambda_{1,j,\bar m},\omega_{1,m})$: Step 1 uses only the samples of arm $k$ in $\mathcal B_m$ from donors that have such samples; Step 2 uses the target's samples of arm $k$ in $\mathcal B_{\bar m}$; $\omega_{1,m}=\zeta_{1,0}+\eta_{1,0}\sqrt{\log(d\min_{i\in D,|\mathcal B^i_m|>0}|\mathcal B^i_m|)}$ and $\lambda_{1,j,\bar m}=\lambda_{1,0}^{(j)}\sqrt{\log(d|\mathcal B^j_{\bar m}|)/|\mathcal B^j_{\bar m}|}$.
--   6. **Arms.** For $t\in\mathcal B_0$, arm $((\sum_{r\le t}\mathbf 1\{Z_r=Z_t\})-1)\bmod K$. For $t\in\mathcal B_m$, $m\ge1$, $j=Z_t$: the screen $\mathcal K=\{k: X_t^\top\widehat\beta^j_{k,0}\ge\max_iX_t^\top\widehat\beta^j_{i,0}-h/2\}$ and the arm of $\mathcal K$ maximizing $X_t^\top\widehat\beta^j_{k,\overline{m-1}}$.
--   7. **Event $\mathcal A$ (35).** $\|\widehat\beta^j_{k,0}-\beta^j_k\|_1\le h/(4x_{\max})$ for all $j,k$.
--
--   The LASSO minimizer and the tie among maximizing arms are produced by arbitrary selection rules that see only their data, so the policy is non-anticipating; the theorems hold for every such rule.
--
--   **Formalization Note** Arms are $0$-based. Rounding $|\mathcal B_0|$ up keeps at least $q\log H$ forced steps. As in Algorithm 2, $\mathcal B_0=[q\log(T)]$ is not intersected with the horizon, so the forced-sample estimator is always formed on the full forced batch (the policy consults it only after $\mathcal B_0$); the batches $\mathcal B_m=\{t\in[H]\mid\dots\}$, $m\ge1$, are intersected with $[H]$ as printed, so no divisibility is assumed. The all-sample hyperparameters at $m=0$ (used in $\mathcal B_1$) follow the same formulas. A minimum over an empty set of donors is $0$, and $x/0=0$. The regularization inputs are per instance (`lam0 j`, `lam10 j`), which contains Algorithm 2's common inputs as the constant case.
-- source:
--   Xu & Bastani, Multitask Learning and Bandits via Robust Statistics, arXiv:2112.14233v5, pp. 25–26, (9) and Algorithm 2; p. 55, (35); notation pp. 57, 60

import Mathlib
import Definitions.Def_RobustMultitask_Estimator_VectorNotation
import Definitions.Def_RobustMultitask_Estimator_TrimmedMean
import Definitions.Def_RobustMultitask_Estimator_Algorithm
import Definitions.Def_RobustMultitask_Estimator_Supplement_DataPoor

namespace RobustMultitask.Estimator.Supplement

open Matrix

/-- The inputs of RMBandit (Algorithm 2, p. 26). `H` is the total time horizon (the source's
`T` in §5.3 and Appendix D), `b0 = |B₀|` the length of the forced-sampling batch, `h` the
screening margin, `ω0` the forced trimming level, `lam0 j` the forced regularization level of
instance `j` (so `λ_{0,j} = lam0 j / √|Bʲ₀|`), `ζ10, η10` the all-sample trimming inputs,
`lam10 j` the all-sample regularization input of instance `j`, and `donors` the set of instances
whose OLS estimates enter the shared trimmed mean (all instances in the standard regime; all
but the data-poor instance in the data-poor regime, Remark 4). -/
structure BanditParams (N : ℕ) where
  H : ℕ
  b0 : ℕ
  h : ℝ
  ω0 : ℝ
  lam0 : Fin N → ℝ
  ζ10 : ℝ
  η10 : ℝ
  lam10 : Fin N → ℝ
  donors : Finset (Fin N)

/-- The forced-sampling batch length `|B₀| = ⌈q log H⌉` (`B₀ = [q log(T)]` in Algorithm 2;
the count is rounded up). -/
noncomputable def forcedLength (q : ℝ) (H : ℕ) : ℕ :=
  ⌈q * Real.log H⌉₊

/-- The batch `B_m ∩ [H]` (Algorithm 2): `B₀ = {1, …, |B₀|}` and
`B_m = {t | 2^{m−1}|B₀| < t ≤ 2^m|B₀|}` for `m ≥ 1`, intersected with `[H] = {1, …, H}`. -/
def batch (b0 H m : ℕ) : Finset ℕ :=
  (Finset.Icc 1 H).filter (fun t => if m = 0 then t ≤ b0 else 2 ^ (m - 1) * b0 < t ∧ t ≤ 2 ^ m * b0)

/-- The cumulative batch `B_{m̄} = B₀ ∪ ⋯ ∪ B_m = {t ∈ [H] | t ≤ 2^m |B₀|}`. -/
def cumBatch (b0 H m : ℕ) : Finset ℕ :=
  (Finset.Icc 1 H).filter (fun t => t ≤ 2 ^ m * b0)

/-- The index `m ≥ 1` of the batch `B_m` containing a time `t > |B₀|`: the least `m` with
`t ≤ 2^m |B₀|`, i.e. `⌈log₂ ⌈t/|B₀|⌉⌉`. -/
def batchIndex (b0 t : ℕ) : ℕ :=
  Nat.clog 2 ((t + b0 - 1) / b0)

/-- `Bⁱ(S) = {t ∈ S | Z_t = i}`: the arrivals at instance `i` among the times `S`. -/
def arrivalsIn {N : ℕ} (z : ℕ → Fin N) (S : Finset ℕ) (i : Fin N) : Finset ℕ :=
  S.filter (fun t => z t = i)

/-- `Bⁱ_k(S) = {t ∈ S | Z_t = i, π_t = k}`: the samples of arm `k` at instance `i` among `S`. -/
def armSamplesIn {N K : ℕ} (z : ℕ → Fin N) (a : ℕ → Fin K) (S : Finset ℕ) (i : Fin N)
    (k : Fin K) : Finset ℕ :=
  S.filter (fun t => z t = i ∧ a t = k)

/-- The design matrix of the samples at the times in `S`, rows in increasing time order. -/
noncomputable def rowsOf {d : ℕ} (S : Finset ℕ) (x : ℕ → Fin d → ℝ) :
    Matrix (Fin S.card) (Fin d) ℝ :=
  fun r => x (S.orderEmbOfFin rfl r)

/-- The response vector of the samples at the times in `S`, in increasing time order. -/
noncomputable def valsOf (S : Finset ℕ) (y : ℕ → ℝ) : Fin S.card → ℝ :=
  fun r => y (S.orderEmbOfFin rfl r)

/-- A shifted-LASSO selection rule: given `n` rows `X`, responses `Y`, a level `λ` and a centre
`b`, it returns a vector of `ℝᵈ`. It sees only these data. -/
abbrev LassoSelector (d : ℕ) :=
  (n : ℕ) → Matrix (Fin n) (Fin d) ℝ → (Fin n → ℝ) → ℝ → (Fin d → ℝ) → (Fin d → ℝ)

/-- The selection rule always returns a global minimizer of
`(1/n)‖Xβ − Y‖₂² + λ‖β − b‖₁` (Step 2 of Algorithm 1) when `λ ≥ 0`. -/
def IsLassoSelector {d : ℕ} (sel : LassoSelector d) : Prop :=
  ∀ (n : ℕ) (X : Matrix (Fin n) (Fin d) ℝ) (Y : Fin n → ℝ) (lam : ℝ) (b : Fin d → ℝ),
    0 ≤ lam → IsLassoMinimizer X Y lam b (sel n X Y lam b)

/-- A tie-breaking rule for `arg max_{k ∈ S} score_k`. -/
abbrev ArgmaxRule (K : ℕ) := (Fin K → ℝ) → Finset (Fin K) → Fin K

/-- The rule returns, for every nonempty `S`, an element of `S` of maximal score in `S`. -/
def IsArgmaxRule {K : ℕ} (tb : ArgmaxRule K) : Prop :=
  ∀ (sc : Fin K → ℝ) (S : Finset (Fin K)), S.Nonempty → tb sc S ∈ S ∧ ∀ k ∈ S, sc k ≤ sc (tb sc S)

/-- The RMEstimator (Algorithm 1) on sample sets: Step 1 forms, for each instance `i ∈ D`, the
OLS estimate on the samples `Ssh i`, and takes the componentwise trimmed mean with level `ω`
over `i ∈ D`; Step 2 returns the selected shifted-LASSO minimizer on the samples `Sj` with level
`lam`, centred at that trimmed mean. -/
noncomputable def rmEstimateOn {N d : ℕ} (sel : LassoSelector d) (D : Finset (Fin N))
    (Ssh : Fin N → Finset ℕ) (Sj : Finset ℕ) (x : ℕ → Fin d → ℝ) (y : ℕ → ℝ) (ω lam : ℝ) :
    Fin d → ℝ :=
  sel Sj.card (rowsOf Sj x) (valsOf Sj y) lam
    (fun c => trimmedMeanOn D (fun i => ols (rowsOf (Ssh i) x) (valsOf (Ssh i) y) c) ω)

/-- The forced-sample estimator `β̂ʲ_k(B₀, λ_{0,j}, ω₀)`: RMEstimator on the forced samples of
arm `k` in `B₀ = {1, …, |B₀|}`, with `λ_{0,j} = lam0 j / √|Bʲ₀|`. As in Algorithm 2,
`B₀ = [q log(T)]` is not intersected with the horizon (only the batches `B_m`, `m ≥ 1`, are), so
this is the estimator formed at the end of the full forced batch; RMBandit consults it only at
times `t > |B₀|`. -/
noncomputable def forcedEst {N K d : ℕ} (sel : LassoSelector d) (prm : BanditParams N)
    (z : ℕ → Fin N) (x : ℕ → Fin d → ℝ) (y : ℕ → ℝ) (a : ℕ → Fin K) (j : Fin N) (k : Fin K) :
    Fin d → ℝ :=
  let B0 := Finset.Icc 1 prm.b0
  rmEstimateOn sel prm.donors (fun i => armSamplesIn z a B0 i k) (armSamplesIn z a B0 j k) x y
    prm.ω0 (prm.lam0 j / Real.sqrt (arrivalsIn z B0 j).card)

/-- `min_{i ∈ donors, |Bⁱ_m| > 0} |Bⁱ_m|` (`0` if no donor has an arrival in `B_m`). -/
noncomputable def minArrivals {N : ℕ} (prm : BanditParams N) (z : ℕ → Fin N) (m : ℕ) : ℕ :=
  sInf (((prm.donors.filter (fun i => 0 < (arrivalsIn z (batch prm.b0 prm.H m) i).card)).image
    (fun i => (arrivalsIn z (batch prm.b0 prm.H m) i).card) : Finset ℕ) : Set ℕ)

/-- The all-sample trimming level `ω_{1,m} = ζ_{1,0} + η_{1,0} √(log(d min_{i, |Bⁱ_m|>0} |Bⁱ_m|))`
(Algorithm 2, the minimum over the donor instances). -/
noncomputable def allOmega {N : ℕ} (d : ℕ) (prm : BanditParams N) (z : ℕ → Fin N) (m : ℕ) : ℝ :=
  prm.ζ10 + prm.η10 * Real.sqrt (Real.log (d * minArrivals prm z m))

/-- The all-sample regularization level `λ_{1,j,m̄} = λ_{1,0} √(log(d|Bʲ_{m̄}|)/|Bʲ_{m̄}|)`. -/
noncomputable def allLam {N : ℕ} (d : ℕ) (prm : BanditParams N) (z : ℕ → Fin N) (m : ℕ)
    (j : Fin N) : ℝ :=
  let c : ℝ := (arrivalsIn z (cumBatch prm.b0 prm.H m) j).card
  prm.lam10 j * Real.sqrt (Real.log (d * c) / c)

/-- The all-sample estimator `β̂ʲ_k(B_{m̄}, λ_{1,j,m̄}, ω_{1,m})`: Step 1 uses only the samples of
arm `k` in the batch `B_m`, from the donor instances that have such samples; Step 2 uses all the
samples of arm `k` at instance `j` in `B_{m̄}`. -/
noncomputable def allEst {N K d : ℕ} (sel : LassoSelector d) (prm : BanditParams N)
    (z : ℕ → Fin N) (x : ℕ → Fin d → ℝ) (y : ℕ → ℝ) (a : ℕ → Fin K) (m : ℕ) (j : Fin N)
    (k : Fin K) : Fin d → ℝ :=
  let Bm := batch prm.b0 prm.H m
  let Ssh : Fin N → Finset ℕ := fun i => armSamplesIn z a Bm i k
  rmEstimateOn sel (prm.donors.filter (fun i => (Ssh i).Nonempty)) Ssh
    (armSamplesIn z a (cumBatch prm.b0 prm.H m) j k) x y (allOmega d prm z m) (allLam d prm z m j)

/-- One round `t ≥ 1` of RMBandit (Algorithm 2). It reads the arrivals `z` and contexts `x` up to
time `t`, and the rewards `y` and arms `a` of earlier rounds.
* `t ∈ B₀`: the arm `((∑_{r ≤ t} 1(Z_r = Z_t)) − 1) mod K` (0-based arms).
* `t ∈ B_m`, `m ≥ 1`, `j = Z_t`: with the forced-sample estimates `β̂ʲ_{k,0}`, the screen
  `𝒦 = {k | X_tᵀβ̂ʲ_{k,0} ≥ max_i X_tᵀβ̂ʲ_{i,0} − h/2}`, and the arm of largest
  `X_tᵀβ̂ʲ_k(B_{m̄−1}, λ_{1,j,m̄−1}, ω_{1,m−1})` in `𝒦` (ties broken by `tb`). -/
noncomputable def banditStep {N K d : ℕ} [NeZero K] (sel : LassoSelector d) (tb : ArgmaxRule K)
    (prm : BanditParams N) (t : ℕ) (z : ℕ → Fin N) (x : ℕ → Fin d → ℝ) (y : ℕ → ℝ)
    (a : ℕ → Fin K) : Fin K := by
  classical
  exact
    if t ≤ prm.b0 then
      ⟨((Finset.Icc 1 t).filter (fun r => z r = z t)).card.pred % K,
        Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne K))⟩
    else
      let m := batchIndex prm.b0 t
      let j := z t
      let fs : Fin K → Fin d → ℝ := fun k => forcedEst sel prm z x y a j k
      let as : Fin K → Fin d → ℝ := fun k => allEst sel prm z x y a (m - 1) j k
      let screen : Finset (Fin K) :=
        Finset.univ.filter (fun k => (⨆ i, x t ⬝ᵥ fs i) - prm.h / 2 ≤ x t ⬝ᵥ fs k)
      tb (fun k => x t ⬝ᵥ as k) screen

/-- The arms played by RMBandit in rounds `1, …, t`, computed round by round; `r s k` is the reward
arm `k` would yield at time `s`, and round `t + 1` is given only the rewards of the arms actually
played before it. Entry `s` is meaningful for `1 ≤ s ≤ t`. -/
noncomputable def armHistory {N K d : ℕ} [NeZero K] (sel : LassoSelector d) (tb : ArgmaxRule K)
    (prm : BanditParams N) (z : ℕ → Fin N) (x : ℕ → Fin d → ℝ) (r : ℕ → Fin K → ℝ) :
    ℕ → ℕ → Fin K
  | 0 => fun _ => 0
  | t + 1 =>
    Function.update (armHistory sel tb prm z x r t) (t + 1)
      (banditStep sel tb prm (t + 1) z x (fun s => r s (armHistory sel tb prm z x r t s))
        (armHistory sel tb prm z x r t))

section Path

variable {Ω : Type*} {N K d : ℕ} [NeZero K]

/-- The arm `π_t` played by RMBandit at time `t ≥ 1` on the sample path `ω`, when instance
`Z_t(ω)` receives the context `X_t(ω)` and pulling arm `k` yields `X_t(ω)ᵀβ^{Z_t}_k + ε_t(ω)`. -/
noncomputable def banditArm (sel : LassoSelector d) (tb : ArgmaxRule K) (prm : BanditParams N)
    (β : Fin N → Fin K → Fin d → ℝ) (Z : ℕ → Ω → Fin N) (Xc : ℕ → Ω → Fin d → ℝ)
    (ε : ℕ → Ω → ℝ) (ω : Ω) (t : ℕ) : Fin K :=
  armHistory sel tb prm (fun s => Z s ω) (fun s => Xc s ω)
    (fun s k => Xc s ω ⬝ᵥ β (Z s ω) k + ε s ω) t t

/-- The observed reward `Y_t = X_tᵀβ^{Z_t}_{π_t} + ε_t` on the path `ω`. -/
noncomputable def banditReward (sel : LassoSelector d) (tb : ArgmaxRule K) (prm : BanditParams N)
    (β : Fin N → Fin K → Fin d → ℝ) (Z : ℕ → Ω → Fin N) (Xc : ℕ → Ω → Fin d → ℝ)
    (ε : ℕ → Ω → ℝ) (ω : Ω) (t : ℕ) : ℝ :=
  Xc t ω ⬝ᵥ β (Z t ω) (banditArm sel tb prm β Z Xc ε ω t) + ε t ω

/-- The forced-sample estimator `β̂ʲ_{k,0} = β̂ʲ_k(B₀, λ_{0,j}, ω₀)` computed by RMBandit on `ω`. -/
noncomputable def forcedEstimate (sel : LassoSelector d) (tb : ArgmaxRule K)
    (prm : BanditParams N) (β : Fin N → Fin K → Fin d → ℝ) (Z : ℕ → Ω → Fin N)
    (Xc : ℕ → Ω → Fin d → ℝ) (ε : ℕ → Ω → ℝ) (ω : Ω) (j : Fin N) (k : Fin K) : Fin d → ℝ :=
  forcedEst sel prm (fun s => Z s ω) (fun s => Xc s ω) (banditReward sel tb prm β Z Xc ε ω)
    (banditArm sel tb prm β Z Xc ε ω) j k

/-- The all-sample estimator `β̂ʲ_{k,m̄} = β̂ʲ_k(B_{m̄}, λ_{1,j,m̄}, ω_{1,m})` computed by RMBandit
on `ω`. -/
noncomputable def allEstimate (sel : LassoSelector d) (tb : ArgmaxRule K)
    (prm : BanditParams N) (β : Fin N → Fin K → Fin d → ℝ) (Z : ℕ → Ω → Fin N)
    (Xc : ℕ → Ω → Fin d → ℝ) (ε : ℕ → Ω → ℝ) (ω : Ω) (m : ℕ) (j : Fin N) (k : Fin K) :
    Fin d → ℝ :=
  allEst sel prm (fun s => Z s ω) (fun s => Xc s ω) (banditReward sel tb prm β Z Xc ε ω)
    (banditArm sel tb prm β Z Xc ε ω) m j k

/-- The event `A` of (35), p. 55: every forced-sample estimator is within `h/(4x_max)` in `ℓ¹`,
`‖β̂ʲ_k(B₀, λ_{0,j}, ω₀) − βʲ_k‖₁ ≤ h/(4x_max)` for all `j ∈ [N]`, `k ∈ [K]`. -/
def forcedGood (sel : LassoSelector d) (tb : ArgmaxRule K) (prm : BanditParams N)
    (β : Fin N → Fin K → Fin d → ℝ) (Z : ℕ → Ω → Fin N) (Xc : ℕ → Ω → Fin d → ℝ)
    (ε : ℕ → Ω → ℝ) (h xmax : ℝ) : Set Ω :=
  {ω | ∀ j k, l1 (forcedEstimate sel tb prm β Z Xc ε ω j k - β j k) ≤ h / (4 * xmax)}

end Path

end RobustMultitask.Estimator.Supplement


