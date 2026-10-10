-- Prove2me | Definitions.Def_BlindProphetSec_Blind_Setting
-- name    : BlindProphetSec_Blind_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T22:37:07.502025+00:00
-- url     : https://prove2.me/theorems/0dd17f29-e56f-4e73-9df9-ae66a9497af7
-- title:
--   §1.2, §3, §4, pp. 3–4, 7, 13–14 — random-order threshold stopping, blind strategies, deterministic blind strategies, α_{α₁…α_m}, g_{m,p}, f_j
-- statement:
--   **The prophet secretary model.** An instance is a list of $n$ probability laws $F_1,\dots,F_n$ on $\mathbb R$; the values $V_1,\dots,V_n$ are independent with $V_i\sim F_i$. A uniformly random permutation $\sigma$ of $[n]=\{1,\dots,n\}$, independent of the values, is the arrival order: at time $j$ the gambler sees $V_{\sigma_j}$. For an acceptance rule, $T$ is the first time at which the rule fires ($T=\infty$ if it never fires) and the gambler's reward is $V_{\sigma_T}\mathbf 1_{T<\infty}$, written $V_{\sigma_T}$.
--
--   This file defines:
--
--   1. $F_{\max}(x)=\mathbb P(\max_i V_i\le x)$ and $\mathbb P(\max_i V_i> x)$, as probabilities of the events $\{\forall i,\ V_i\le x\}$ and $\{\exists i,\ V_i>x\}$ under the product law.
--   2. The first stopping time, the reward $V_{\sigma_T}\mathbf 1_{T<\infty}$, and the events $\{T\le k\}$ and $\{T\ge k\}$.
--   3. The **time threshold algorithm** $\mathrm{TTA}_{\tau_1,\dots,\tau_n}$ (Algorithm 1): stop at the first time $j$ with $V_{\sigma_j}>\tau_j$.
--   4. Probabilities over the values and the order, $\mathbb P(E)=\frac1{n!}\sum_\sigma \mathbb P(E\mid\sigma)$.
--   5. The **blind strategy** given by $\alpha:[0,1]\to[0,1]$: draw $u_1,\dots,u_n$ i.i.d. uniform on $[0,1]$, let $u_{[j]}$ be the $j$-th smallest, and stop at the first time $j$ with $V_{\sigma_j}>\tau_j$, where $\mathbb P(\max_i V_i\le\tau_j)=\alpha(u_{[j]})$. Its value $\mathbb E(V_{\sigma_T})$ is $\mathrm{blindValue}(\alpha)$.
--   6. The **deterministic blind strategy** (Definition 3.1): the same with $\mathbb P(\max_i V_i\le\tau_j)=\alpha(j/n)$; its value is $\mathrm{detBlindValue}(\alpha)$.
--   7. The instance padded with $m$ variables identically $0$, and the prophet's value $\mathbb E(\max_i V_i)$.
--   8. The piecewise-constant function $\alpha_{\alpha_1,\dots,\alpha_m}(x)=\sum_{j\in[m]}\alpha_j\mathbf 1_{[\frac{j-1}m,\frac jm)}(x)$, the function
--   $$g_{m,p}(k)=\begin{cases}\dfrac1{1-\frac km(1-p)} & k\le \frac m2,\\[2mm] \dfrac2{1+p} & k>\frac m2,\end{cases}$$
--   and the functions $f_j(\alpha_1,\dots,\alpha_m)$, $j\in[m+1]$, of Lemma 4.3:
--   $$f_j=\begin{cases}\sum_{k=1}^m\big(\prod_{l\in[k-1]}\alpha_l\big)^{1/m}\dfrac{1-\alpha_k^{1/m}}{-\ln\alpha_k} & j=1,\\[2mm] \sum_{k\in[j-1]}\dfrac{1-\alpha_k}{m(1-\alpha_j)}+\sum_{k=j}^m\big(\prod_{l\in[k-1]}\alpha_l\big)^{1/m}g_{m,\alpha_1}(k-1)\dfrac{1-\alpha_k^{1/m}}{-\ln\alpha_k} & j\in\{2,\dots,m\},\\[2mm] \dfrac1m\sum_{k\in[m]}(1-\alpha_k) & j=m+1.\end{cases}$$
--
--   These objects are the vocabulary of every statement of the mission.
--
--   **Formalization Note.** Variables and times are 0-based (`Fin n`); the paper's time $j$ is Lean's `j.val + 1`. Independence is built in by taking the values as the coordinates of the product measure. The uniform order is the average over all $n!$ permutations. Expectations are lower Lebesgue integrals of the nonnegative part (`lintegral` of `ENNReal.ofReal`), so an infinite mean is allowed and no integrability hypothesis is needed. The blind and deterministic rules do not compute thresholds: "stop at $j$ iff $V_{\sigma_j}>\tau_j$ with $F_{\max}(\tau_j)=\beta_j$" is encoded as $\beta_j<F_{\max}(V_{\sigma_j})$. For continuous laws and $\beta_j\in(0,1]$ the two agree almost surely for every choice of $\tau_j$ (a flat stretch of $F_{\max}$ at a positive level carries no mass of any $V_i$), and $\beta_j=1$ means "never stop", as $\tau_j=+\infty$. At $\beta_j=0$ the paper's threshold is not unique; the encoding uses the largest one. The order statistics are $u_{[j]}$ = `u (Tuple.sort u j)`, ascending. The coefficients $\alpha_1,\dots,\alpha_m$ are a 1-based sequence `a : ℕ → ℝ`. In $f_j$, Lean's `Real.log`, division and `rpow` return junk values at $\alpha_k\in\{0,1\}$ or $\alpha_j=1$; the theorems that use $f_j$ exclude those inputs. The empty maximum ($n=0$) is $0$. As on p. 13, $g_{m,p}$ and $f_j$ are meant for $m\ge1$; at $m=0$ their values are junk. Because the intervals $[\frac{j-1}m,\frac jm)$ are half-open, $\alpha_{\alpha_1,\dots,\alpha_m}(1)=0$, exactly as printed.
-- source:
--   Correa, Saona & Ziliotto, Prophet Secretary Through Blind Strategies, arXiv:1807.07483v2, p. 3 (§1.2, model), p. 4 (§1.2, blind strategies, Algorithm 1, definition of T), p. 7 (Definition 3.1 and the zero-padded instance), p. 13 (α_{α1,…,αm}, g_{m,p}), p. 14 (f_j in Lemma 4.3)

import Mathlib

namespace BlindProphetSec.Blind

open MeasureTheory

/-! # Random-order threshold stopping, blind strategies (Correa, Saona & Ziliotto, arXiv:1807.07483v2)

An instance is `n` laws `μ : Fin n → Measure ℝ`; the values `v : Fin n → ℝ` are the coordinates of
the product measure `Measure.pi μ` (independence). A permutation `σ` of `Fin n` is the arrival order:
at (0-based) time `j` the gambler sees `v (σ j)`. The paper's time `j ∈ [n]` is Lean's `j.val + 1`. -/

/-- `P(max_i V_i ≤ x)`, as the probability of the event `{∀ i, V_i ≤ x}`. -/
noncomputable def Fmax {n : ℕ} (μ : Fin n → Measure ℝ) (x : ℝ) : ℝ :=
  ((Measure.pi μ) {v : Fin n → ℝ | ∀ i, v i ≤ x}).toReal

/-- `P(max_i V_i > x)`, as the probability of the event `{∃ i, V_i > x}`. -/
noncomputable def PmaxGT {n : ℕ} (μ : Fin n → Measure ℝ) (x : ℝ) : ℝ :=
  ((Measure.pi μ) {v : Fin n → ℝ | ∃ i, x < v i}).toReal

/-- The first (0-based) time at which the acceptance rule `acc` fires; `none` encodes `T = ∞`. -/
noncomputable def firstStop {n : ℕ} (acc : Fin n → Prop) : Option (Fin n) := by
  classical
  exact if h : ∃ j, acc j then
    some ((Finset.univ.filter acc).min' ⟨h.choose, by simp [h.choose_spec]⟩)
  else none

/-- The gambler's reward `X_T 1_{T<∞}`: the value `x j` seen at the first stop, `0` if she never
stops. -/
noncomputable def stopReward {n : ℕ} (acc : Fin n → Prop) (x : Fin n → ℝ) : ℝ :=
  match firstStop acc with
  | some j => x j
  | none => 0

/-- The event `T ≤ k` (paper's 1-based times): the rule fires at some time `j.val + 1 ≤ k`. -/
def stopLE {n : ℕ} (acc : Fin n → Prop) (k : ℕ) : Prop :=
  ∃ j : Fin n, j.val < k ∧ acc j

/-- The event `T ≥ k` (paper's 1-based times): the rule fires at no time `j.val + 1 < k`. -/
def stopGE {n : ℕ} (acc : Fin n → Prop) (k : ℕ) : Prop :=
  ∀ j : Fin n, j.val + 1 < k → ¬ acc j

/-- Acceptance rule of `TTA_{τ₁,…,τₙ}` (Algorithm 1) in arrival order `σ`: stop at time `j` iff
`V_{σ_j} > τ_j`. -/
def ttaAcc {n : ℕ} (τ : Fin n → ℝ) (v : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) : Fin n → Prop :=
  fun j => τ j < v (σ j)

/-- Reward of `TTA_{τ₁,…,τₙ}` in arrival order `σ`. -/
noncomputable def ttaReward {n : ℕ} (τ : Fin n → ℝ) (v : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) : ℝ :=
  stopReward (ttaAcc τ v σ) (fun j => v (σ j))

/-- Threshold rule specified by levels `β j` of `P(max ≤ τ_j)`: stop at time `j` iff
`β j < P(max ≤ V_{σ_j})`. For continuous laws and `β j ∈ (0, 1]` this is, almost surely,
`V_{σ_j} > τ_j` for any `τ_j` with `P(max ≤ τ_j) = β j` (and "never" when `β j = 1`); at `β j = 0`
it uses the largest such threshold. -/
noncomputable def levelAcc {n : ℕ} (μ : Fin n → Measure ℝ) (β : Fin n → ℝ) (v : Fin n → ℝ)
    (σ : Equiv.Perm (Fin n)) : Fin n → Prop :=
  fun j => β j < Fmax μ (v (σ j))

/-- Probability over the values and the uniform random order `σ` (independent of the values) of the
event `E v σ`: the average over the `n!` permutations of `P(E(·, σ))`. -/
noncomputable def probVS {n : ℕ} (μ : Fin n → Measure ℝ)
    (E : (Fin n → ℝ) → Equiv.Perm (Fin n) → Prop) : ℝ :=
  (1 / (n.factorial : ℝ)) * ∑ σ : Equiv.Perm (Fin n), ((Measure.pi μ) {v | E v σ}).toReal

/-- The uniform law on `[0, 1]`. -/
noncomputable def unif01 : Measure ℝ := (volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) 1)

/-- Acceptance rule of the blind strategy `α` (§1.2, p. 4): with `u₁,…,uₙ` uniform on `[0,1]` and
`u_{[j]}` their `j`-th order statistic (ascending, `u (Tuple.sort u j)`), stop at time `j` iff
`V_{σ_j} > τ_j` where `P(max ≤ τ_j) = α(u_{[j]})`, encoded as `α(u_{[j]}) < P(max ≤ V_{σ_j})`. -/
noncomputable def blindAcc {n : ℕ} (α : ℝ → ℝ) (μ : Fin n → Measure ℝ) (u : Fin n → ℝ)
    (v : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) : Fin n → Prop :=
  levelAcc μ (fun j => α (u (Tuple.sort u j))) v σ

/-- The blind strategy's reward `V_{σ_T} 1_{T<∞}`. -/
noncomputable def blindReward {n : ℕ} (α : ℝ → ℝ) (μ : Fin n → Measure ℝ) (v : Fin n → ℝ)
    (σ : Equiv.Perm (Fin n)) (u : Fin n → ℝ) : ℝ :=
  stopReward (blindAcc α μ u v σ) (fun j => v (σ j))

/-- `E(V_{σ_T})` for the blind strategy `α`: `σ` uniform, `V ∼ ⊗ μ_i`, `u ∼ U[0,1]^n`, all
independent. -/
noncomputable def blindValue {n : ℕ} (α : ℝ → ℝ) (μ : Fin n → Measure ℝ) : ENNReal :=
  (1 / (n.factorial : ENNReal)) * ∑ σ : Equiv.Perm (Fin n),
    ∫⁻ p, ENNReal.ofReal (blindReward α μ p.1 σ p.2)
      ∂((Measure.pi μ).prod (Measure.pi fun _ : Fin n => unif01))

/-- Acceptance rule of the deterministic blind strategy `α` (Definition 3.1, p. 7): the level at
paper time `j` is `α(j/n)`. -/
noncomputable def detAcc {n : ℕ} (α : ℝ → ℝ) (μ : Fin n → Measure ℝ) (v : Fin n → ℝ)
    (σ : Equiv.Perm (Fin n)) : Fin n → Prop :=
  levelAcc μ (fun j => α (((j.val : ℝ) + 1) / n)) v σ

/-- `E(V_{σ_T})` for the deterministic blind strategy `α`. -/
noncomputable def detBlindValue {n : ℕ} (α : ℝ → ℝ) (μ : Fin n → Measure ℝ) : ENNReal :=
  (1 / (n.factorial : ENNReal)) * ∑ σ : Equiv.Perm (Fin n),
    ∫⁻ v, ENNReal.ofReal (stopReward (detAcc α μ v σ) (fun j => v (σ j))) ∂(Measure.pi μ)

/-- The instance `F₁,…,Fₙ` padded with `m` variables equal to `0` (p. 7). -/
noncomputable def padZero {n : ℕ} (μ : Fin n → Measure ℝ) (m : ℕ) : Fin (n + m) → Measure ℝ :=
  Fin.append μ (fun _ => Measure.dirac 0)

/-- The prophet's value `E(max_i V_i)` (the empty maximum is `0`). -/
noncomputable def Emax {n : ℕ} (μ : Fin n → Measure ℝ) : ENNReal :=
  ∫⁻ v, ENNReal.ofReal (⨆ i, v i) ∂(Measure.pi μ)

/-- The piecewise-constant function `α_{α₁,…,α_m}(x) = Σ_{j∈[m]} α_j 1_{[(j−1)/m, j/m)}(x)` (§4,
p. 13), with the 1-based coefficients `a j = α_j`. -/
noncomputable def pieceAlpha (m : ℕ) (a : ℕ → ℝ) : ℝ → ℝ := fun x =>
  ∑ j ∈ Finset.Icc 1 m, if ((j : ℝ) - 1) / m ≤ x ∧ x < (j : ℝ) / m then a j else 0

/-- `g_{m,p}(k) = 1/(1 − (k/m)(1 − p))` for `k ≤ m/2`, `2/(1 + p)` for `k > m/2` (p. 13). -/
noncomputable def gFun (m : ℕ) (p : ℝ) (k : ℕ) : ℝ :=
  if (k : ℝ) ≤ (m : ℝ) / 2 then 1 / (1 - (k : ℝ) / m * (1 - p)) else 2 / (1 + p)

/-- The functions `f_j(α₁,…,α_m)`, `j ∈ [m+1]`, of Lemma 4.3 (p. 14), with 1-based `a`. -/
noncomputable def fFun (m : ℕ) (a : ℕ → ℝ) (j : ℕ) : ℝ :=
  if j = 1 then
    ∑ k ∈ Finset.Icc 1 m, (∏ l ∈ Finset.Ico 1 k, a l) ^ ((1 : ℝ) / m) *
      ((1 - a k ^ ((1 : ℝ) / m)) / (-Real.log (a k)))
  else if j ≤ m then
    ∑ k ∈ Finset.Ico 1 j, (1 - a k) / (m * (1 - a j)) +
      ∑ k ∈ Finset.Icc j m, (∏ l ∈ Finset.Ico 1 k, a l) ^ ((1 : ℝ) / m) * gFun m (a 1) (k - 1) *
        ((1 - a k ^ ((1 : ℝ) / m)) / (-Real.log (a k)))
  else
    (1 / (m : ℝ)) * ∑ k ∈ Finset.Icc 1 m, (1 - a k)

end BlindProphetSec.Blind


