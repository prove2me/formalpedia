-- Prove2me | Definitions.Def_BypassMonster_Falcon_Model
-- name    : BypassMonster_Falcon_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T17:24:59.88375+00:00
-- url     : https://prove2.me/theorems/d489f266-280b-421f-a6ce-a96c6503ff2a
-- title:
--   §1.2, Assumption 2, Algorithm 2, Setup 2 — the contextual bandit model, the offline oracle guarantee, the FALCON+ run and its regret
-- statement:
--   This file sets up the stochastic contextual bandit model of §1.2, the offline regression oracle of Assumption 2, the algorithm FALCON+ (Algorithm 2) run on a canonical probability space, and the standing assumptions of Setup 2.
--
--   **Model.** There are $K\ge1$ actions $\mathcal A=\{0,\dots,K-1\}$ and a finite context set $\mathcal X$. In every round nature draws a context $x_t\sim\mathcal D_{\mathcal X}$ and a reward vector $r_t\sim\nu(\cdot\mid x_t)$ in $\mathbb R^{\mathcal A}$; the joint law is $\mathcal D=\mathcal D_{\mathcal X}\otimes\nu$. The conditional mean reward is $f^*(x,a)=\mathbb E[r(a)\mid x]=\int r(a)\,\nu(dr\mid x)$. An *action selection kernel* is a map $p:\mathcal X\times\mathcal A\to[0,1]$ with $\sum_a p(a\mid x)=1$ for every $x$.
--
--   **Offline oracle (Assumption 2).** The oracle $\mathrm{OffReg}_{\mathcal F}$ maps $n$ samples $(x_i,a_i,r_i(a_i))$ to a predictor $\hat f:\mathcal X\times\mathcal A\to\mathbb R$, deterministically. For a kernel $p$, write $P_p$ for the law of $(x,a,r(a))$ when $(x,r)\sim\mathcal D$ and $a\sim p(\cdot\mid x)$, and
--   $$\mathrm{err}_p(g)=\mathbb E_{x\sim\mathcal D_{\mathcal X},\,a\sim p(\cdot\mid x)}\big[(g(x,a)-f^*(x,a))^2\big].$$
--   The oracle satisfies Assumption 2 with error function $\mathcal E_{\mathcal F,\delta}(n)$ if for every kernel $p$, every $n\ge1$ and every $\delta'>0$,
--   $$P_p^{\otimes n}\Big(\big\{S:\ \mathrm{err}_p(\mathrm{OffReg}_{\mathcal F}(S))>\mathcal E_{\mathcal F,\delta'}(n)\big\}\Big)\le\delta'.$$
--
--   **FALCON+.** Given the epoch schedule $0=\tau_0<\tau_1<\tau_2<\cdots$, the confidence parameter $\delta$ and $c=1/2$: in epoch $m$, the learning rate is $\gamma_1=1$ and $\gamma_m=\tfrac12\sqrt{K/\mathcal E_{\mathcal F,\delta/(2m^2)}(\tau_{m-1}-\tau_{m-2})}$ for $m\ge2$; the predictor is $\hat f_1\equiv0$ and, for $m\ge2$, $\hat f_m$ is the oracle's output on (only) the $\tau_{m-1}-\tau_{m-2}$ records of epoch $m-1$. In round $t$ of epoch $m$, with $\hat a_t$ a maximizer of $\hat f_m(x_t,\cdot)$ (chosen by a fixed tie-breaking rule), the action $a_t$ is drawn from
--   $$p_t(a)=\frac{1}{K+\gamma_m\big(\hat f_m(x_t,\hat a_t)-\hat f_m(x_t,a)\big)}\ (a\ne\hat a_t),\qquad p_t(\hat a_t)=1-\sum_{a\ne\hat a_t}p_t(a).$$
--   The epoch of round $t$ is $m(t)=\min\{m\ge1: t\le\tau_m\}$. With $\pi_{f^*}$ a policy maximizing $f^*(x,\cdot)$ for every $x$, the regret after $T$ rounds is $\sum_{t=1}^T\big(r_t(\pi_{f^*}(x_t))-r_t(a_t)\big)$.
--
--   **Setup 2.** The bundle of standing assumptions used by every theorem of the mission: rewards in $[0,1]$; Assumption 2 with a measurable oracle and $\mathcal E_{\mathcal F,\delta'}(n)>0$; the schedule starts at $\tau_0=0$, is strictly increasing and has $\tau_m\ge 2^m$ for $1\le m\le M$; the learning rates satisfy $\gamma_1\le\cdots\le\gamma_M$; the tie-breaking rule picks a maximizer and is measurable; $\pi_{f^*}$ maximizes $f^*$; and $\delta>0$. Here $M$ is an epoch horizon; Theorem 2 uses $M=m(T)$.
--
--   These objects are the common vocabulary of the mission: the goal theorem bounds the regret of exactly this run.
--
--   **Formalization Note** Contexts form a finite type with the discrete σ-algebra, the setting of the paper's detailed proof (App. A.1–A.6). Actions are `Fin K` with `K ≥ 1`. The run lives on the canonical space $\Omega=\mathbb N\to(\mathcal X\times\mathbb R^{\mathcal A})\times[0,1]$ with the product law of $\mathcal D\otimes\mathrm{Uniform}[0,1]$; coordinate $t\ge1$ carries $(x_t,r_t)$ and the uniform number $u_t$ from which $a_t$ is drawn by the inverse CDF; coordinate $0$ is unused. The algorithm's inputs (oracle, error function $\mathcal E$, $\delta$, schedule, tie-breaking rule) are bundled in `Params`. The paper's "with probability at least $1-\delta$" is written as "the failure set has (outer) measure at most $\delta$". Added relative to the page, and recorded: $\mathcal E>0$ (Algorithm 2 divides by it), measurability of the oracle and of the tie-breaking rule (App. A.7, p. 1929: such conditions "are directly assumed here"). Assumption 2 is required for every sample size $n\ge1$.
-- source:
--   Simchi-Levi & Xu, Math. Oper. Res. 47(3) (2022), §1.2 pp. 1906–1907, §1.5 p. 1910, Assumption 2 p. 1913, Algorithm 2 p. 1914, Setup 2 pp. 1921–1922, App. A.1 p. 1922; endnote 2 p. 1930

import Mathlib

namespace BypassMonster.Falcon

open MeasureTheory ProbabilityTheory

variable {X : Type*} {K : ℕ}

/-- An action selection kernel on a finite context set and the action set `𝒜 = Fin K` (§1.5,
p. 1910): `p x a` is the probability of selecting action `a` given context `x`; entries are
nonnegative and sum to one over the actions, for every context. -/
def IsSelKernel (p : X → Fin K → ℝ) : Prop :=
  (∀ x a, 0 ≤ p x a) ∧ ∀ x, ∑ a, p x a = 1

/-- The action selection rule of step 6 of Algorithm 2 (p. 1914), for a vector of predicted
rewards `g : Fin K → ℝ` (`g a = f̂_m(x_t, a)`), a learning rate `γ`, and a tie-breaking rule
`amax` picking the greedy action `â = amax g`:
`p(a) = 1 / (K + γ (g â − g a))` for `a ≠ â`, and `p(â) = 1 − ∑_{a ≠ â} p(a)`. -/
noncomputable def igw (γ : ℝ) (amax : (Fin K → ℝ) → Fin K) (g : Fin K → ℝ) (a : Fin K) : ℝ :=
  if a = amax g then
    1 - ∑ b ∈ Finset.univ.erase (amax g), 1 / ((K : ℝ) + γ * (g (amax g) - g b))
  else
    1 / ((K : ℝ) + γ * (g (amax g) - g a))

/-- Draw an action from a distribution `p` on `Fin K` using a number `u ∈ [0,1]`, by the inverse
CDF: the action is the number of `b` with `∑_{c ≤ b} p(c) < u` (capped at `K − 1`). When `p` is a
probability vector and `u` is uniform on `[0,1]`, the result is `a` with probability `p(a)`. -/
noncomputable def drawAction [NeZero K] (p : Fin K → ℝ) (u : ℝ) : Fin K :=
  ⟨min (Finset.univ.filter (fun b : Fin K => ∑ c ∈ Finset.Iic b, p c < u)).card (K - 1), by
    have := NeZero.pos K
    omega⟩

/-- The conditional mean reward `f*(x, a) = E[r(a) | x]` (§1.2.2, p. 1906), for nature's law
`𝒟 = D_X ⊗ ν` given by a context marginal and a reward kernel `ν : X → (Fin K → ℝ)`. -/
noncomputable def fstar [MeasurableSpace X] (ν : Kernel X (Fin K → ℝ)) (x : X) (a : Fin K) : ℝ :=
  ∫ r, r a ∂(ν x)

/-- The law of one training sample `(x, a, r(a))` of Assumption 2 (p. 1913): `(x, r) ∼ 𝒟 = D_X ⊗ ν`
and `a ∼ p(· | x)`. -/
noncomputable def sampleLaw [MeasurableSpace X] (DX : Measure X) (ν : Kernel X (Fin K → ℝ))
    (p : X → Fin K → ℝ) : Measure (X × Fin K × ℝ) :=
  (DX ⊗ₘ ν).bind
    (fun z => ∑ a : Fin K, ENNReal.ofReal (p z.1 a) • Measure.dirac (z.1, a, z.2 a))

/-- The out-of-sample squared error of a predictor `g` under the kernel `p` (Assumption 2,
p. 1913): `E_{x ∼ D_X, a ∼ p(·|x)}[(g(x,a) − f*(x,a))²] = ∫ ∑_a p(a|x) (g(x,a) − f*(x,a))² dD_X`. -/
noncomputable def popSqErr [MeasurableSpace X] (DX : Measure X) (ν : Kernel X (Fin K → ℝ))
    (p : X → Fin K → ℝ) (g : X → Fin K → ℝ) : ℝ :=
  ∫ x, ∑ a, p x a * (g x a - fstar ν x a) ^ 2 ∂DX

/-- **Assumption 2** (p. 1913), the statistical guarantee of the offline regression oracle
`OffReg_ℱ`, with estimation error `ℰ_{ℱ,δ}(n) = E δ n`: for every action selection kernel `p`,
every sample size `n ≥ 1` and every `δ' > 0`, if the `n` samples `(x_i, a_i, r_i(a_i))` are i.i.d.
from `sampleLaw D_X ν p`, then with probability at least `1 − δ'` the returned predictor `f̂`
satisfies `E_{x∼D_X, a∼p(·|x)}[(f̂(x,a) − f*(x,a))²] ≤ ℰ_{ℱ,δ'}(n)`. It is stated in failure
form: the outer measure of the failure set is at most `δ'`. The oracle is a deterministic
function of its input (endnote 2, p. 1930). -/
def OfflineGuarantee [MeasurableSpace X] (DX : Measure X) (ν : Kernel X (Fin K → ℝ))
    (OffReg : (n : ℕ) → (Fin n → X × Fin K × ℝ) → X → Fin K → ℝ) (E : ℝ → ℕ → ℝ) : Prop :=
  ∀ p : X → Fin K → ℝ, IsSelKernel p → ∀ n : ℕ, 1 ≤ n → ∀ δ' : ℝ, 0 < δ' →
    Measure.pi (fun _ : Fin n => sampleLaw DX ν p)
        {S | E δ' n < popSqErr DX ν p (OffReg n S)} ≤ ENNReal.ofReal δ'

/-- The epoch `m(t) = min {m ∈ ℕ, m ≥ 1 : t ≤ τ_m}` of round `t` (App. A.1, p. 1922); `m(T)` is the
number of epochs Algorithm 2 runs in `T` rounds (p. 1912). -/
noncomputable def epochOf (τ : ℕ → ℕ) (t : ℕ) : ℕ :=
  sInf {m : ℕ | 1 ≤ m ∧ t ≤ τ m}

/-- The inputs of FALCON+ (Algorithm 2, p. 1914) and its free choices:
* `OffReg n S` — the offline regression oracle `OffReg_ℱ`, a deterministic function of the `n`
  training samples `S` (endnote 2), returning a predictor `X → Fin K → ℝ`;
* `E δ n` — the oracle's estimation error guarantee `ℰ_{ℱ,δ}(n)`;
* `δ` — the confidence parameter;
* `τ` — the epoch schedule `0 = τ_0 < τ_1 < τ_2 < ⋯`;
* `amax` — the tie-breaking rule for the greedy action `â_t ∈ argmax_a f̂_m(x_t, a)`. -/
structure Params (X : Type*) (K : ℕ) where
  OffReg : (n : ℕ) → (Fin n → X × Fin K × ℝ) → X → Fin K → ℝ
  E : ℝ → ℕ → ℝ
  δ : ℝ
  τ : ℕ → ℕ
  amax : (Fin K → ℝ) → Fin K

namespace Params

/-- The learning rate of step 2 of Algorithm 2 with tuning parameter `c = 1/2` (Setup 2):
`γ_1 = 1` and `γ_m = (1/2) √(K / ℰ_{ℱ,δ/(2m²)}(τ_{m−1} − τ_{m−2}))` for `m ≥ 2`. (The value at
`m = 0` is unused.) -/
noncomputable def gamma (A : Params X K) (m : ℕ) : ℝ :=
  if m ≤ 1 then 1
  else (1 / 2) * Real.sqrt ((K : ℝ) / A.E (A.δ / (2 * (m : ℝ) ^ 2)) (A.τ (m - 1) - A.τ (m - 2)))

/-- The sample space: `Ω = ℕ → (X × (Fin K → ℝ)) × [0,1]`. Coordinate `t ≥ 1` holds nature's
context and reward vector `(x_t, r_t)` and the algorithm's uniform random number `u_t` for round
`t`; coordinate `0` is unused. -/
abbrev Omega (X : Type*) (K : ℕ) := ℕ → (X × (Fin K → ℝ)) × unitInterval

/-- The record `(x_s, a_s, r_s(a_s))` of round `s` played with predictor `g` and learning rate
`γm` (steps 5–7 of Algorithm 2): `a_s` is drawn from the step-6 kernel `igw γm amax (g x_s ·)`
by the inverse CDF with the uniform number `u_s`. -/
noncomputable def record [NeZero K] (A : Params X K) (γm : ℝ) (g : X → Fin K → ℝ) (s : ℕ)
    (ω : Omega X K) : X × Fin K × ℝ :=
  let x := (ω s).1.1
  let a := drawAction (igw γm A.amax (g x)) ((ω s).2 : ℝ)
  (x, a, (ω s).1.2 a)

/-- The predictors `f̂_m` of Algorithm 2 on the outcome `ω` (step 3): `f̂_1 ≡ 0`, and for `m ≥ 1`,
`f̂_{m+1} = OffReg_ℱ` applied to (only) the `τ_m − τ_{m−1}` records of epoch `m`, i.e. of rounds
`τ_{m−1} + 1, …, τ_m`, which were played with `f̂_m` and `γ_m`. (The value at `m = 0` is unused.) -/
noncomputable def fhat [NeZero K] (A : Params X K) : ℕ → Omega X K → X → Fin K → ℝ
  | 0 => fun _ => 0
  | m + 1 => fun ω =>
      if m = 0 then 0
      else A.OffReg (A.τ m - A.τ (m - 1))
        (fun i => A.record (A.gamma m) (A.fhat m ω) (A.τ (m - 1) + 1 + (i : ℕ)) ω)

/-- The action selection kernel `p_m(a | x)` of epoch `m` (step 6 of Algorithm 2 with `x_t`
replaced by `x`, §4 p. 1916): `p_m(· | x) = igw γ_m amax (f̂_m(x, ·))`. -/
noncomputable def pm [NeZero K] (A : Params X K) (m : ℕ) (ω : Omega X K) (x : X) : Fin K → ℝ :=
  igw (A.gamma m) A.amax (A.fhat m ω x)

/-- The action `a_t` of Algorithm 2 in round `t ≥ 1` (step 7): drawn from `p_{m(t)}(· | x_t)`
with the uniform number `u_t`. -/
noncomputable def action [NeZero K] (A : Params X K) (t : ℕ) (ω : Omega X K) : Fin K :=
  drawAction (A.pm (epochOf A.τ t) ω (ω t).1.1) ((ω t).2 : ℝ)

/-- The regret of Algorithm 2 after `T` rounds (§1.2.2, p. 1907):
`∑_{t=1}^T (r_t(π_{f*}(x_t)) − r_t(a_t))`, for a reward-maximizing policy `πstar = π_{f*}`. -/
noncomputable def regret [NeZero K] (A : Params X K) (πstar : X → Fin K) (T : ℕ)
    (ω : Omega X K) : ℝ :=
  ∑ t ∈ Finset.Icc 1 T, ((ω t).1.2 (πstar (ω t).1.1) - (ω t).1.2 (A.action t ω))

end Params

/-- The law of the canonical process: the coordinates `ω t` are i.i.d., each with law
`𝒟 ⊗ Uniform[0,1]` where `𝒟 = D_X ⊗ ν` is nature's joint law of `(x_t, r_t)`. -/
noncomputable def canonMeasure [MeasurableSpace X] (DX : Measure X) [IsProbabilityMeasure DX]
    (ν : Kernel X (Fin K → ℝ)) [IsMarkovKernel ν] : Measure (Params.Omega X K) :=
  Measure.infinitePi (fun _ : ℕ => (DX ⊗ₘ ν).prod (volume : Measure unitInterval))

/-- **Setup 2** (pp. 1921–1922) together with the standing model of §1.2 and the hypotheses of
Theorem 2 (p. 1914), for an epoch horizon `M` (Theorem 2 uses `M = m(T)`):
* rewards lie in `[0,1]` (§1.2);
* the oracle is measurable and satisfies Assumption 2 with error `E`, and `E δ' n > 0`
  (Algorithm 2 divides by it);
* `0 = τ_0 < τ_1 < ⋯` and `τ_m ≥ 2^m` for `1 ≤ m ≤ M`;
* `γ_1 ≤ ⋯ ≤ γ_M` (the paper's "without loss of generality");
* `amax` picks a maximizer and is measurable; `πstar` maximizes `f*(x, ·)`;
* `0 < δ`. -/
structure Setup2 [MeasurableSpace X] (DX : Measure X) (ν : Kernel X (Fin K → ℝ))
    (A : Params X K) (πstar : X → Fin K) (M : ℕ) : Prop where
  hr : ∀ x, ∀ᵐ r ∂(ν x), ∀ a, r a ∈ Set.Icc (0 : ℝ) 1
  hOffMeas : ∀ n, Measurable (A.OffReg n)
  hA2 : OfflineGuarantee DX ν A.OffReg A.E
  hEpos : ∀ δ' : ℝ, ∀ n : ℕ, 0 < δ' → 1 ≤ n → 0 < A.E δ' n
  hτ0 : A.τ 0 = 0
  hτ : StrictMono A.τ
  hτ2 : ∀ m, 1 ≤ m → m ≤ M → 2 ^ m ≤ A.τ m
  hmono : ∀ i j, 1 ≤ i → i ≤ j → j ≤ M → A.gamma i ≤ A.gamma j
  hamax : ∀ (g : Fin K → ℝ) (a : Fin K), g a ≤ g (A.amax g)
  hamax_meas : Measurable A.amax
  hπstar : ∀ x a, fstar ν x a ≤ fstar ν x (πstar x)
  hδ : 0 < A.δ

end BypassMonster.Falcon


