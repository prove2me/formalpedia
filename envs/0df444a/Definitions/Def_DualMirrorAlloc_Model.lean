-- Prove2me | Definitions.Def_DualMirrorAlloc_Model
-- name    : DualMirrorAlloc_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T14:02:31.603963+00:00
-- url     : https://prove2.me/theorems/fb79d21b-5815-4a46-b610-43e3e4aa8bef
-- title:
--   Online allocation model, $\mathrm{OPT}$, dual function and Algorithm 1 (dual mirror descent)
-- statement:
--   This module defines the online allocation problem of Balseiro, Lu and Mirrokni and the run of their dual mirror descent algorithm.
--
--   1. **Requests.** A set $S$ of requests; request $s$ has a feasible set $X_s\subseteq\mathbb R^d$, a reward $f_s$ and a consumption $b_s$ with values in $\mathbb R^m$. **The model of p.8**: $X_s\subseteq\mathbb R^d_+$ is compact, $0\in X_s$, $b_s(0)=0$, $f_s\ge0$, $b_s\ge0$, and the resource vector $\rho$ has $\rho_j>0$. **Assumption 1** (items 1–3): $0\in X_s$, $0\le f_s\le\bar f$, $b_s\ge0$, $\|b_s\|_\infty\le\bar b$ on $X_s$.
--   2. **Offline optimum** (1): for $\vec\gamma=(\gamma_1,\dots,\gamma_T)$,
--   $$
--   \mathrm{OPT}(\vec\gamma)=\max\Big\{\sum_{t=1}^T f_t(x_t): x_t\in X_t,\ \sum_{t=1}^T b_t(x_t)\le T\rho\Big\}.
--   $$
--   3. **Dual objects** (2): $f^*_s(\mu)=\sup_{x\in X_s}\{f_s(x)-\mu^\top b_s(x)\}$, $D(\mu|\vec\gamma)=\sum_t f^*_t(\mu)+T\rho^\top\mu$, and $\bar D(\mu|P)=\mathbb E_{s\sim P}[f^*_s(\mu)]+\rho^\top\mu$.
--   4. **Algorithm 1.** Given an argmax selection for (3) (Assumption 1.4), a mirror-step selection for (4), $\mu_1$ and $B_1=T\rho$: at period $t$, $\tilde x_t\in\arg\max_{x\in X_t}\{f_t(x)-\mu_t^\top b_t(x)\}$; $x_t=\tilde x_t$ if $b_t(\tilde x_t)\le B_t$ and $x_t=0$ otherwise; $B_{t+1}=B_t-b_t(x_t)$; $g_t=\rho-b_t(\tilde x_t)$; $\mu_{t+1}=\arg\min_{\mu\ge0}g_t^\top\mu+\frac1\eta V_h(\mu,\mu_t)$. The reward is $R(A|\vec\gamma)=\sum_t f_t(x_t)$.
--   5. **Constants and proof objects.** $\underline\rho=\min_j\rho_j$, $\bar\rho=\max_j\rho_j$; $C_1=\bar f\bar b/\underline\rho$, $C_2=(\bar b+\bar\rho)^2/(2\sigma)$, $C_3=\max\{V_h(\mu,\mu_1):\mu\in\{0,(\bar f/\rho_1)e_1,\dots,(\bar f/\rho_m)e_m\}\}$; the stopping time $\tau_A$; $w_t(\mu)=\mu^\top(\rho-b_t(x_t))$; the average dual variable $\bar\mu_\tau$; and $E(t,\mu)=\frac1{2\sigma}(\bar b+\bar\rho)^2\eta t+\frac1\eta V_h(\mu,\mu_1)$.
--
--   These are the objects of Theorem 1 and of its proof.
--
--   **Formalization Note** Periods are 0-based: the state at index $t$ is $(\mu_{t+1},B_{t+1})$, and the recursion reads the request sequence only at earlier indices. The budget check is coordinatewise; the budget is updated with the action played $x_t$, the subgradient with the proposed action $\tilde x_t$. $\mathrm{OPT}$ and $f^*$ are real suprema (`sSup`), which are the true values under the model and Assumption 1. $\tau_A$ is the least $t\in\{0,\dots,T-1\}$ with $\sum_{s=1}^t(b_s(x_s))_j+\bar b\ge\rho_jT$ for some $j$, and $T$ if none. The page's $\bar D(\mu|P)=\mathbb E[f^*(\mu_t)]+\mu_t^\top\rho$ (p.15) has $\mu$ for the misprinted $\mu_t$. $\bar\mu_0$ is $0$ (it only appears multiplied by $\tau=0$). $\underline\rho,\bar\rho$ and the max in $C_3$ are `⨅`/`⨆` over the finite index set.
-- source:
--   Balseiro–Lu–Mirrokni, The Best of Many Worlds: Dual Mirror Descent for Online Allocation Problems, arXiv:2011.10124v3, §2 (1), pp.8–9; §2.1 (2), p.10; Algorithm 1, p.11; Assumption 1, p.13; p.14 (ρ̲, ρ̄, Theorem 1 constants); proof of Theorem 1, pp.14–16

import Mathlib
import Definitions.Def_DualMirrorAlloc_Bregman

open MeasureTheory

namespace DualMirrorAlloc

/-- **Requests.** Balseiro–Lu–Mirrokni, *The Best of Many Worlds: Dual Mirror Descent for Online
Allocation Problems*, arXiv:2011.10124v3, §2, p.8: a request `γ = (f, b, X) ∈ S` consists of a
feasible set `X ⊂ ℝ^d`, a reward function `f : X → ℝ` and a resource consumption function
`b : X → ℝ^m`. `S` is the set of all possible requests.

**Formalization Note.** `S` is an arbitrary type (with a σ-algebra wherever laws on `S` are
used), and a request `s : S` carries its data `X s`, `f s`, `b s`. `f s` and `b s` are typed on all
of `ℝ^d`; their values off `X s` are never used. -/
structure Requests (S : Type*) (d m : ℕ) where
  /-- The feasible set `X_s ⊆ ℝ^d` of request `s`. -/
  X : S → Set (Fin d → ℝ)
  /-- The reward function `f_s`. -/
  f : S → (Fin d → ℝ) → ℝ
  /-- The resource consumption function `b_s`, with values in `ℝ^m`. -/
  b : S → (Fin d → ℝ) → (Fin m → ℝ)

variable {S : Type*} {d m : ℕ}

/-- **The model of §2, p.8.** For every request `s`: `X_s ⊂ ℝ^d_+` is compact, `0 ∈ X_s`,
`b_s(0) = 0`, `f_s ≥ 0` and `b_s ≥ 0` on `X_s`; and the resource vector `ρ ∈ ℝ^m_+` has `ρ_j > 0`
for all `j`.

**Formalization Note.** "`f_t : X_t → ℝ_+`" and "`b_t : X_t → ℝ^m_+`" are `0 ≤ f s x` and
`0 ≤ b s x` for `x ∈ X s`. -/
structure IsModel (R : Requests S d m) (ρ : Fin m → ℝ) : Prop where
  X_nonneg : ∀ s, R.X s ⊆ Set.Ici 0
  X_compact : ∀ s, IsCompact (R.X s)
  zero_mem : ∀ s, (0 : Fin d → ℝ) ∈ R.X s
  b_zero : ∀ s, R.b s 0 = 0
  f_nonneg : ∀ s, ∀ x ∈ R.X s, 0 ≤ R.f s x
  b_nonneg : ∀ s, ∀ x ∈ R.X s, 0 ≤ R.b s x
  rho_pos : ∀ j, 0 < ρ j

/-- **Assumption 1 (assumptions on the requests), items 1–3, p.13**, with `f̄, b̄ ∈ ℝ_+`: for every
request `(f, b, X) ∈ S`, `0 ∈ X`, `0 ≤ f(x) ≤ f̄` and `b(x) ≥ 0`, `‖b(x)‖∞ ≤ b̄` for every `x ∈ X`.

**Formalization Note.** `‖b(x)‖∞ ≤ b̄` with `b(x) ≥ 0` is written `∀ j, b(x)_j ≤ b̄`. Item 4 (the
maximization problems (3) have an optimal solution) is the existence of the argmax selection
`act` of `IsArgmaxSelection`. -/
def Assumption1 (R : Requests S d m) (fbar bbar : ℝ) : Prop :=
  0 ≤ fbar ∧ 0 ≤ bbar ∧
    ∀ s, (0 : Fin d → ℝ) ∈ R.X s ∧
      ∀ x ∈ R.X s, (0 ≤ R.f s x ∧ R.f s x ≤ fbar) ∧ (0 ≤ R.b s x ∧ ∀ j, R.b s x j ≤ bbar)

/-- **The offline (hindsight) optimum `OPT(γ⃗)`, (1), p.8**:
`OPT(γ⃗) = max { Σ_{t=1}^T f_t(x_t) : x_t ∈ X_t, Σ_{t=1}^T b_t(x_t) ≤ Tρ }`.

**Formalization Note.** Periods are `Fin T` (0-based). The maximum is the real `sSup`. Under the
model of p.8 the set is nonempty (`x ≡ 0`) and, under Assumption 1, bounded above by `T f̄`, so
`sSup` is the supremum (equal to the maximum when it is attained). The constraint is
coordinatewise. -/
noncomputable def OPT (R : Requests S d m) (ρ : Fin m → ℝ) {T : ℕ} (γ : Fin T → S) : ℝ :=
  sSup {v | ∃ x : Fin T → Fin d → ℝ, (∀ t, x t ∈ R.X (γ t)) ∧
    (∑ t, R.b (γ t) (x t)) ≤ (T : ℝ) • ρ ∧ v = ∑ t, R.f (γ t) (x t)}

/-- **The opportunity-cost-adjusted reward `f*_s(µ) = sup_{x ∈ X_s} {f_s(x) − µᵀb_s(x)}`, (2),
p.10.**

**Formalization Note.** Real `sSup`. Under Assumption 1 and `µ ≥ 0` the set is nonempty and
bounded above by `f̄`, so this is the supremum. -/
noncomputable def fstar (R : Requests S d m) (s : S) (mu : Fin m → ℝ) : ℝ :=
  sSup ((fun x => R.f s x - mu ⬝ᵥ R.b s x) '' R.X s)

/-- **The Lagrangian dual function `D(µ|γ⃗) = Σ_{t=1}^T f*_t(µ) + Tρᵀµ`, §2.1, p.10.** -/
noncomputable def dualFn (R : Requests S d m) (ρ : Fin m → ℝ) {T : ℕ} (mu : Fin m → ℝ)
    (γ : Fin T → S) : ℝ :=
  ∑ t, fstar R (γ t) mu + (T : ℝ) * (ρ ⬝ᵥ mu)

/-- **The expected dual objective `D̄(µ|P) = E_{(f,b)∼P}[f*(µ)] + µᵀρ`, proof of Theorem 1,
Step 1, p.15.**

**Formalization Note.** The page writes `E_{(f,b)∼P}[f*(µ_t)] + µ_tᵀρ` for `D̄(µ|P)`; the `µ_t`
is a slip for `µ` (the left side is a function of `µ`). The expectation is the Bochner integral of
`s ↦ f*_s(µ)` under `P`. -/
noncomputable def dualBar (R : Requests S d m) (ρ : Fin m → ℝ) [MeasurableSpace S]
    (P : Measure S) (mu : Fin m → ℝ) : ℝ :=
  ∫ s, fstar R s mu ∂P + ρ ⬝ᵥ mu

/-- **An argmax selection for (3), Algorithm 1, p.11** (Assumption 1.4, p.13): for every request
`s` and every `µ ∈ ℝ^m_+`, `act s µ ∈ X_s` maximizes `f_s(x) − µᵀb_s(x)` over `X_s`.

**Formalization Note.** "`x̃_t ∈ arg max`" is a choice among maximizers; the theorems of the
mission hold for every such selection. Its existence is Assumption 1.4. Values at `µ ∉ ℝ^m_+` are
never used: the dual iterates stay in `ℝ^m_+`. -/
def IsArgmaxSelection (R : Requests S d m) (act : S → (Fin m → ℝ) → (Fin d → ℝ)) : Prop :=
  ∀ s, ∀ mu ∈ orthant m, act s mu ∈ R.X s ∧
    ∀ x ∈ R.X s, R.f s x - mu ⬝ᵥ R.b s x ≤ R.f s (act s mu) - mu ⬝ᵥ R.b s (act s mu)

/-- **A mirror-descent step selection for (4), Algorithm 1, p.11**: for every `g ∈ ℝ^m` and every
`µ ∈ ℝ^m_+` at which `h` is differentiable within `ℝ^m_+`, `md g µ ∈ ℝ^m_+` minimizes
`gᵀν + V_h(ν, µ)/η` over `ν ∈ ℝ^m_+`.

**Formalization Note.** "`µ_{t+1} = arg min`" is a choice of minimizer; the theorems hold for every
such selection. The property is required only where `V_h(·, µ)` is defined, i.e. where `∇h(µ)`
exists. -/
def IsMirrorStep (h : (Fin m → ℝ) → ℝ) (η : ℝ)
    (md : (Fin m → ℝ) → (Fin m → ℝ) → (Fin m → ℝ)) : Prop :=
  ∀ g, ∀ mu ∈ orthant m, DifferentiableWithinAt ℝ h (orthant m) mu →
    md g mu ∈ orthant m ∧
      ∀ ν ∈ orthant m, g ⬝ᵥ md g mu + bregman (orthant m) h (md g mu) mu / η ≤
        g ⬝ᵥ ν + bregman (orthant m) h ν mu / η

open scoped Classical in
/-- **The state `(µ_t, B_t)` of Algorithm 1 (Dual Mirror Descent), p.11**, run on the request
sequence `γ⃗ = (γ_1, …, γ_T)` with argmax selection `act`, mirror step `md`, initial dual solution
`µ_1` and initial resources `B_1 = Tρ`. At period `t`:
`x̃_t = act(γ_t, µ_t)`; `x_t = x̃_t` if `b_t(x̃_t) ≤ B_t` and `x_t = 0` otherwise;
`B_{t+1} = B_t − b_t(x_t)`; `g_t = −b_t(x̃_t) + ρ`; `µ_{t+1} = md(g_t, µ_t)`.

**Formalization Note.** Time is 0-based: `runState … γ t` is the paper's `(µ_{t+1}, B_{t+1})`,
`runState … γ 0 = (µ_1, Tρ)`, and `γ ⟨t, _⟩` is the paper's `γ_{t+1}`. The recursion reads `γ` only
at index `t` when computing index `t + 1`, so `(µ_t, B_t)` depends on the past requests only. The
state is frozen after index `T`. The budget check `b_t(x̃_t) ≤ B_t` is coordinatewise. The budget is
updated with the action played `x_t`, the subgradient `g_t` with the proposed action `x̃_t`. -/
noncomputable def runState (R : Requests S d m) (ρ : Fin m → ℝ)
    (act : S → (Fin m → ℝ) → (Fin d → ℝ)) (md : (Fin m → ℝ) → (Fin m → ℝ) → (Fin m → ℝ))
    (mu₁ : Fin m → ℝ) {T : ℕ} (γ : Fin T → S) : ℕ → (Fin m → ℝ) × (Fin m → ℝ)
  | 0 => (mu₁, (T : ℝ) • ρ)
  | t + 1 =>
    if ht : t < T then
      let st := runState R ρ act md mu₁ γ t
      let s := γ ⟨t, ht⟩
      let xt := act s st.1
      let x := if R.b s xt ≤ st.2 then xt else 0
      (md (ρ - R.b s xt) st.1, st.2 - R.b s x)
    else runState R ρ act md mu₁ γ t

/-- The dual iterate `µ_{t+1}` of Algorithm 1 (0-based index `t`; `dualIter … γ 0 = µ_1`). -/
noncomputable def dualIter (R : Requests S d m) (ρ : Fin m → ℝ)
    (act : S → (Fin m → ℝ) → (Fin d → ℝ)) (md : (Fin m → ℝ) → (Fin m → ℝ) → (Fin m → ℝ))
    (mu₁ : Fin m → ℝ) {T : ℕ} (γ : Fin T → S) (t : ℕ) : Fin m → ℝ :=
  (runState R ρ act md mu₁ γ t).1

/-- The remaining resources `B_{t+1}` of Algorithm 1 (0-based index `t`; `budget … γ 0 = Tρ`). -/
noncomputable def budget (R : Requests S d m) (ρ : Fin m → ℝ)
    (act : S → (Fin m → ℝ) → (Fin d → ℝ)) (md : (Fin m → ℝ) → (Fin m → ℝ) → (Fin m → ℝ))
    (mu₁ : Fin m → ℝ) {T : ℕ} (γ : Fin T → S) (t : ℕ) : Fin m → ℝ :=
  (runState R ρ act md mu₁ γ t).2

/-- The proposed action `x̃_t = act(γ_t, µ_t)` of (3) at period `t` (0-based `t : Fin T`). -/
noncomputable def proposed (R : Requests S d m) (ρ : Fin m → ℝ)
    (act : S → (Fin m → ℝ) → (Fin d → ℝ)) (md : (Fin m → ℝ) → (Fin m → ℝ) → (Fin m → ℝ))
    (mu₁ : Fin m → ℝ) {T : ℕ} (γ : Fin T → S) (t : Fin T) : Fin d → ℝ :=
  act (γ t) (dualIter R ρ act md mu₁ γ t)

open scoped Classical in
/-- The action played `x_t` at period `t` (0-based `t : Fin T`): `x̃_t` if `b_t(x̃_t) ≤ B_t`
coordinatewise, and the void action `0` otherwise. -/
noncomputable def played (R : Requests S d m) (ρ : Fin m → ℝ)
    (act : S → (Fin m → ℝ) → (Fin d → ℝ)) (md : (Fin m → ℝ) → (Fin m → ℝ) → (Fin m → ℝ))
    (mu₁ : Fin m → ℝ) {T : ℕ} (γ : Fin T → S) (t : Fin T) : Fin d → ℝ :=
  if R.b (γ t) (proposed R ρ act md mu₁ γ t) ≤ budget R ρ act md mu₁ γ t then
    proposed R ρ act md mu₁ γ t
  else 0

/-- **The reward of Algorithm 1, `R(A|γ⃗) = Σ_{t=1}^T f_t(x_t)`, p.9.** -/
noncomputable def reward (R : Requests S d m) (ρ : Fin m → ℝ)
    (act : S → (Fin m → ℝ) → (Fin d → ℝ)) (md : (Fin m → ℝ) → (Fin m → ℝ) → (Fin m → ℝ))
    (mu₁ : Fin m → ℝ) {T : ℕ} (γ : Fin T → S) : ℝ :=
  ∑ t, R.f (γ t) (played R ρ act md mu₁ γ t)

/-- **The lowest and largest resource parameters `ρ̲ = min_j ρ_j`, `ρ̄ = max_j ρ_j = ‖ρ‖∞`, p.14.**

**Formalization Note.** Real `⨅`/`⨆` over the finite index set `Fin m`; for `m ≥ 1` (assumed by
every theorem) they are the minimum and the maximum. -/
noncomputable def rhoMin (ρ : Fin m → ℝ) : ℝ := ⨅ j, ρ j

/-- `ρ̄ = max_j ρ_j`, p.14 (see `rhoMin`). -/
noncomputable def rhoMax (ρ : Fin m → ℝ) : ℝ := ⨆ j, ρ j

/-- **The constant `C₁ = f̄ b̄ / ρ̲` of Theorem 1, p.14.** -/
noncomputable def C1 (ρ : Fin m → ℝ) (fbar bbar : ℝ) : ℝ := fbar * bbar / rhoMin ρ

/-- **The constant `C₂ = (b̄ + ρ̄)² / (2σ)` of Theorem 1, p.14.** -/
noncomputable def C2 (ρ : Fin m → ℝ) (bbar σ : ℝ) : ℝ := (bbar + rhoMax ρ) ^ 2 / (2 * σ)

/-- **The constant `C₃ = max {V_h(µ, µ_1) : µ ∈ {0, (f̄/ρ_1)e_1, …, (f̄/ρ_m)e_m}}` of Theorem 1,
p.14**, `e_j` the `j`-th unit vector.

**Formalization Note.** `(f̄/ρ_j)e_j` is `Pi.single j (f̄ / ρ j)`; the maximum over the `m + 1`
points is `max (V_h(0, µ_1)) (⨆_j V_h((f̄/ρ_j)e_j, µ_1))`, the `⨆` over the finite set `Fin m`. -/
noncomputable def C3 (h : (Fin m → ℝ) → ℝ) (ρ : Fin m → ℝ) (fbar : ℝ) (mu₁ : Fin m → ℝ) : ℝ :=
  max (bregman (orthant m) h 0 mu₁)
    (⨆ j, bregman (orthant m) h (Pi.single j (fbar / ρ j)) mu₁)

/-- The cumulative consumption `Σ_{s=1}^{t} b_s(x_s)` of the first `t` periods (0-based: periods
with index `< t`). -/
noncomputable def consumed (R : Requests S d m) (ρ : Fin m → ℝ)
    (act : S → (Fin m → ℝ) → (Fin d → ℝ)) (md : (Fin m → ℝ) → (Fin m → ℝ) → (Fin m → ℝ))
    (mu₁ : Fin m → ℝ) {T : ℕ} (γ : Fin T → S) (t : ℕ) : Fin m → ℝ :=
  ∑ s ∈ Finset.univ.filter (fun s : Fin T => s.val < t), R.b (γ s) (played R ρ act md mu₁ γ s)

open scoped Classical in
/-- **The stopping time `τ_A`, proof of Theorem 1, Step 1, p.14**: "the first time less than `T`
that there exists resource `j` such that `Σ_{t=1}^{τ_A} (b_t(x_t))_j + b̄ ≥ ρ_j T`", and `τ_A = T`
if there is no such time (used in Step 3, p.16).

**Formalization Note.** `τ_A` is the least `t ∈ {0, …, T − 1}` with
`∃ j, Σ_{s=1}^{t} (b_s(x_s))_j + b̄ ≥ ρ_j T` (the sum over the first `t` periods; empty at `t = 0`),
and `T` if there is none. The search starts at `t = 0`: with a start at `t = 1` the claim of Step 1
that no resource constraint is violated before `τ_A` fails (m = T = 1, ρ = 1, b̄ = 2, a request
with `b(x̃_1) = 2`). -/
noncomputable def tauA (R : Requests S d m) (ρ : Fin m → ℝ)
    (act : S → (Fin m → ℝ) → (Fin d → ℝ)) (md : (Fin m → ℝ) → (Fin m → ℝ) → (Fin m → ℝ))
    (mu₁ : Fin m → ℝ) (bbar : ℝ) {T : ℕ} (γ : Fin T → S) : ℕ :=
  if hex : ∃ t, t < T ∧ ∃ j, ρ j * T ≤ consumed R ρ act md mu₁ γ t j + bbar then Nat.find hex
  else T

/-- **The complementary-slackness functions `w_t(µ) = µᵀ(ρ − b_t(x_t))`, proof of Theorem 1,
Step 2, p.15** (0-based `t : Fin T`). -/
noncomputable def wFn (R : Requests S d m) (ρ : Fin m → ℝ)
    (act : S → (Fin m → ℝ) → (Fin d → ℝ)) (md : (Fin m → ℝ) → (Fin m → ℝ) → (Fin m → ℝ))
    (mu₁ : Fin m → ℝ) {T : ℕ} (γ : Fin T → S) (t : Fin T) (mu : Fin m → ℝ) : ℝ :=
  mu ⬝ᵥ (ρ - R.b (γ t) (played R ρ act md mu₁ γ t))

/-- **The average dual variable `µ̄_τ = (1/τ) Σ_{t=1}^{τ} µ_t`, proof of Theorem 1, Step 1, (10),
p.15.**

**Formalization Note.** At `τ = 0` the paper's average is undefined; here it is `0`. It only
appears multiplied by `τ`. -/
noncomputable def dualAvg (R : Requests S d m) (ρ : Fin m → ℝ)
    (act : S → (Fin m → ℝ) → (Fin d → ℝ)) (md : (Fin m → ℝ) → (Fin m → ℝ) → (Fin m → ℝ))
    (mu₁ : Fin m → ℝ) {T : ℕ} (γ : Fin T → S) (τ : ℕ) : Fin m → ℝ :=
  (τ : ℝ)⁻¹ • ∑ t ∈ Finset.range τ, dualIter R ρ act md mu₁ γ t

/-- **The online-mirror-descent error term `E(t, µ) = (1/2σ)(b̄ + ρ̄)²η·t + (1/η)V_h(µ, µ_1)`, proof
of Theorem 1, Step 2, p.16.** -/
noncomputable def errTerm (h : (Fin m → ℝ) → ℝ) (ρ : Fin m → ℝ) (bbar σ η : ℝ)
    (mu₁ : Fin m → ℝ) (t : ℝ) (mu : Fin m → ℝ) : ℝ :=
  (bbar + rhoMax ρ) ^ 2 * η * t / (2 * σ) + bregman (orthant m) h mu mu₁ / η

end DualMirrorAlloc


