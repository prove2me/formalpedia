-- Prove2me | Definitions.Def_QueueSignal_SignalingGame
-- name    : QueueSignal_SignalingGame
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:05:01.567989+00:00
-- url     : https://prove2.me/theorems/6a73eaad-dd87-455a-aa6d-e2442b471187
-- title:
--   Two-type, two-signal signaling game: pure sequential equilibrium, credible updating rule (Definition 2) and perfect sequential equilibrium
-- statement:
--   This module sets up the signaling game of §3 of Guo, Haviv, Luo and Wang in a general two-type, two-signal form.
--
--   1. **Types and signals.** The server's type is $t\in\mathbb T=\{H,L\}$ (high or low quality), with prior $w(H)=\delta$, $w(L)=1-\delta$. Its signal is $s\in\mathbb S=\{R,C\}$ (reveal or conceal the queue).
--   2. **Pure profiles.** A pure signaling profile $(s',s'')$ means that the high-quality server always sends $s'$ and the low-quality server always sends $s''$. A signal is **on the equilibrium path** if some type sends it.
--   3. **Beliefs.** After each signal $s$ the customers hold a belief $\delta^s\in[0,1]$, the probability that the server is of high quality. On the path it follows Bayes' rule (Definition 1(ii)):
--   $$\delta^s=\frac{\delta f(s\mid H)}{\delta f(s\mid H)+(1-\delta)f(s\mid L)},\qquad f(s\mid H)=[s'=s],\ f(s\mid L)=[s''=s].$$
--   Off the path it is unrestricted.
--   4. **Payoffs.** A payoff function $\pi(t,s,d)$ gives the payoff of a type-$t$ server that sends $s$ while the customers believe, after $s$, that it is of high quality with probability $d$. The customers' sequentially rational play is thereby already accounted for.
--   5. **Pure sequential equilibrium** (Definition 1). The profile $(s',s'')$ with beliefs $(\delta^R,\delta^C)$ is a sequential equilibrium if the beliefs are in $[0,1]$, Bayes-consistent on the path, and no type gains by switching signal: $\pi(t,s,\delta^s)\le u^*_t$ for all $t,s$, where $u^*_t=\pi(t,\sigma(t),\delta^{\sigma(t)})$ is type $t$'s equilibrium payoff.
--   6. **Credible belief** (Definition 2, credible updating rule). For a signal $s$ and a candidate posterior $\gamma$, let $\mathbb T'(\gamma)=\{t:\pi(t,s,\gamma)>u^*_t\}$ (types strictly better off deviating to $s$) and $\mathbb T''(\gamma)=\{t:\pi(t,s,\gamma)=u^*_t\}$ (indifferent types). The posterior $\gamma$ is credible if $\mathbb T'\cup\mathbb T''\neq\emptyset$ and there are deviation probabilities $h(t)$ with $h=1$ on $\mathbb T'$, $h\in[0,1]$ on $\mathbb T''$, $h=0$ elsewhere, $\sum_t h(t)>0$, and
--   $$\gamma=\frac{w(H)h(H)}{\sum_{t'}w(t')h(t')}.$$
--   The sets $\mathbb T',\mathbb T''$ are evaluated at $\gamma$ itself (clause (b): they "remain unchanged under the above posterior belief").
--   7. **Pure perfect sequential equilibrium** (Grossman and Perry 1986). A pure sequential equilibrium such that, at every off-path signal $s$, no credible posterior $\gamma$ makes some type strictly better off by deviating to $s$.
--
--   These objects carry the equilibrium analysis of §4 (Proposition 1 and the four profiles of §4.2).
--
--   **Formalization Note** Only pure signaling rules are modelled. The customers' strategies are not separate objects: the payoff function evaluates their equilibrium behaviour under each belief, which is the reduction the paper makes on p.548. Perfect sequential equilibrium is taken in the Grossman–Perry form "not upset by any credible belief", the test the paper applies in the paragraph after Definition 2; the alternative reading "the equilibrium's own off-path belief must be credible" is not used (under it Proposition 1 fails). A separating profile has no off-path signal.
-- source:
--   Guo, Haviv, Luo, Wang, Signaling Service Quality Through Queue Disclosure, MSOM 25(2) (2023), doi:10.1287/msom.2022.1170, §3.1, p.546; Definition 1, p.547; Definition 2, p.547; §4.2, p.548 (pure strategies (s′, s″))

import Mathlib

namespace QueueSignal

/-- The server's quality types `𝕋 = {H, L}` (Guo, Haviv, Luo, Wang, *Signaling Service Quality
Through Queue Disclosure*, MSOM 25(2) (2023), doi:10.1287/msom.2022.1170, §3.1, p.546, PDF p.5):
`H` is high quality (prior probability `δ`), `L` is low quality (prior probability `1 − δ`). -/
inductive QType
  | H
  | L
  deriving DecidableEq

instance : Fintype QType :=
  ⟨{QType.H, QType.L}, fun t => by cases t <;> simp⟩

/-- The server's signal set `𝕊 = {R, C}` (§3.1, p.546, PDF p.5): `R` reveals the queue, `C`
conceals it. -/
inductive Sig
  | R
  | C
  deriving DecidableEq

instance : Fintype Sig :=
  ⟨{Sig.R, Sig.C}, fun s => by cases s <;> simp⟩

/-- A pure signaling profile `(s′, s″)` (§4.2, p.548, PDF p.7): the high-quality server always
sends `s′` and the low-quality server always sends `s″`, i.e. `f(s′ | H) = 1` and `f(s″ | L) = 1`.
The first component is `H`'s signal, the second `L`'s. -/
abbrev Profile := Sig × Sig

/-- The signal that type `t` sends under the pure profile `σ = (s′, s″)`. -/
def Profile.sig (σ : Profile) : QType → Sig
  | .H => σ.1
  | .L => σ.2

/-- The prior `w(·)` of Definition 2 (p.547, PDF p.6): `w(H) = δ`, `w(L) = 1 − δ`. -/
def prior (δ : ℝ) : QType → ℝ
  | .H => δ
  | .L => 1 - δ

/-- The signal `s` is on the equilibrium path of the pure profile `σ`: some type sends it
(§3.2, p.547, PDF p.6, "if the server sends a signal with a positive probability, we say that
this signal is on the equilibrium path"). -/
def OnPath (σ : Profile) (s : Sig) : Prop :=
  σ.1 = s ∨ σ.2 = s

instance (σ : Profile) (s : Sig) : Decidable (OnPath σ s) := by
  unfold OnPath; infer_instance

/-- Bayes' rule of Definition 1(ii) (p.547, PDF p.6) for a pure profile `σ = (s′, s″)`:
`δ^s = δ f(s | H) / (δ f(s | H) + (1 − δ) f(s | L))` with `f(s | H) = [s′ = s]` and
`f(s | L) = [s″ = s]`. It is used only for signals on the path, where the denominator is
positive when `0 < δ < 1`. -/
noncomputable def bayes (δ : ℝ) (σ : Profile) (s : Sig) : ℝ :=
  δ * (if σ.1 = s then 1 else 0) /
    (δ * (if σ.1 = s then 1 else 0) + (1 - δ) * (if σ.2 = s then 1 else 0))

/-- The customers' beliefs `(δ^R, δ^C)` as a function of the signal: the probability the
customers assign to the high-quality type after observing `R` (resp. `C`). -/
def beliefs (dR dC : ℝ) : Sig → ℝ
  | .R => dR
  | .C => dC

/-- **Pure sequential equilibrium** of the two-type, two-signal signaling game (Definition 1,
p.547, PDF p.6, for a pure signaling rule, with the customers' sequentially rational play
encoded in the payoff, as on p.548, §4.2).

`pay t s d` is the payoff of a type-`t` server that sends `s` when the customers, after
observing `s`, believe the server is of high quality with probability `d`. A pure profile
`σ` with beliefs `b` (`b s = δ^s`) is a sequential equilibrium when

1. every belief lies in `[0, 1]`;
2. (consistency, Definition 1(ii)) on-path beliefs follow Bayes' rule; off-path beliefs are
   unrestricted;
3. (sequential rationality, Definition 1(i)) no type gains by sending the other signal:
   `pay t s (b s) ≤ pay t σ(t) (b σ(t))` for every type `t` and signal `s`.

**Formalization Note.** Only pure signaling rules are covered (Proposition 1 is about
pure-strategy equilibria). The customers' subgame is not modelled: the payoff function already
evaluates their equilibrium joining behaviour under each belief, as the paper's reduction on
p.548 does. -/
def IsPureSE (δ : ℝ) (pay : QType → Sig → ℝ → ℝ) (σ : Profile) (b : Sig → ℝ) : Prop :=
  (∀ s, 0 ≤ b s ∧ b s ≤ 1) ∧
  (∀ s, OnPath σ s → b s = bayes δ σ s) ∧
  ∀ t s, pay t s (b s) ≤ pay t (σ.sig t) (b (σ.sig t))

/-- The equilibrium payoff `u*_t` of type `t` under the profile `σ` with beliefs `b`. -/
def eqPay (pay : QType → Sig → ℝ → ℝ) (σ : Profile) (b : Sig → ℝ) (t : QType) : ℝ :=
  pay t (σ.sig t) (b (σ.sig t))

/-- **Credible belief** at a signal `s` (Definition 2, Credible Updating Rule, p.547, PDF p.6).

Given the equilibrium `(σ, b)`, a posterior `γ` after `s` is credible when, with the sets
computed **at `γ` itself** (clause (b): "the sets `𝕋′` and `𝕋″` remain unchanged under the
above posterior belief"),

* `𝕋′(γ) = {t : pay t s γ > u*_t}` (types strictly better off deviating to `s`),
* `𝕋″(γ) = {t : pay t s γ = u*_t}` (indifferent types),

the set `𝕋′ ∪ 𝕋″` is nonempty and there are deviation probabilities `h : 𝕋 → ℝ` with
`h = 1` on `𝕋′`, `h ∈ [0, 1]` on `𝕋″`, `h = 0` off `𝕋′ ∪ 𝕋″`, `Σ h > 0`, and
(clause (a)) `γ = w(H)h(H) / Σ_t w(t)h(t)` with `w(H) = δ`, `w(L) = 1 − δ`.

**Formalization Note.** The posterior of clause (a) is the belief in the high-quality type,
`γ = δh(H)/(δh(H) + (1 − δ)h(L))`; the sums over `𝕋′ ∪ 𝕋″` equal the sums over `𝕋` because
`h` vanishes off `𝕋′ ∪ 𝕋″`. -/
def IsCredible (δ : ℝ) (pay : QType → Sig → ℝ → ℝ) (σ : Profile) (b : Sig → ℝ) (s : Sig)
    (γ : ℝ) : Prop :=
  (∃ t, eqPay pay σ b t < pay t s γ ∨ pay t s γ = eqPay pay σ b t) ∧
  ∃ h : QType → ℝ,
    (∀ t, eqPay pay σ b t < pay t s γ → h t = 1) ∧
    (∀ t, pay t s γ = eqPay pay σ b t → 0 ≤ h t ∧ h t ≤ 1) ∧
    (∀ t, ¬ eqPay pay σ b t < pay t s γ → pay t s γ ≠ eqPay pay σ b t → h t = 0) ∧
    0 < h .H + h .L ∧
    γ = prior δ .H * h .H / (prior δ .H * h .H + prior δ .L * h .L)

/-- **Pure perfect sequential equilibrium** (Grossman and Perry 1986, as adopted in §3.2,
p.547, PDF p.6): a pure sequential equilibrium `(σ, b)` that no credible belief upsets, i.e.
for every off-path signal `s` and every credible posterior `γ` at `s` (Definition 2), no type
is strictly better off deviating to `s` under `γ` (`𝕋′(γ) = ∅`).

**Formalization Note.** This is the reading "an equilibrium fails the refinement when some
credible off-path belief makes a deviation strictly profitable" (the Grossman–Perry test, which
the paragraph after Definition 2 applies). The other reading, "the equilibrium's own off-path
belief must be credible whenever a credible belief exists", is not used. A separating profile
has no off-path signal, so it is perfect as soon as it is sequential. -/
def IsPurePSE (δ : ℝ) (pay : QType → Sig → ℝ → ℝ) (σ : Profile) (b : Sig → ℝ) : Prop :=
  IsPureSE δ pay σ b ∧
  ∀ s, ¬ OnPath σ s → ∀ γ, IsCredible δ pay σ b s γ → ∀ t, ¬ eqPay pay σ b t < pay t s γ

end QueueSignal


