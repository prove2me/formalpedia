-- Prove2me | Definitions.Def_IntCapAlloc_OrgChoice_Model
-- name    : IntCapAlloc_OrgChoice_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-23T08:39:40.15799+00:00
-- url     : https://prove2.me/theorems/20c75a2c-5e5d-427b-8cd4-18d2cf13fd74
-- title:
--   §2, pp. 5–8 — two-project costly-disclosure financing game: beliefs, break-even investment (1)–(3), payoffs (4)–(5), PBE, investment efficiency
-- statement:
--   This file sets up the model of Hwang, *Internal Capital Allocation, Voluntary Disclosure, and Investment Efficiency* (§2).
--
--   A founder owns two projects $i \in \{1,2\}$. Each needs one unit of capital and yields cash flow $\theta_i X$, where $X > 1$ and $\theta_i \in \{0,1\}$; the $\theta_i$ are independent with $\Pr(\theta_i = 1) = p$. Disclosing $\theta_i$ (choice $d_i = D$) is truthful and raises project $i$'s capital requirement by $c > 0$; silence is $d_i = ND$. Write $\#D = I(d_1) + I(d_2)$ for the number of disclosures.
--
--   **Multi-divisional firm ($o = m$).** One manager observes $(\theta_1,\theta_2)$ and chooses $(d_1,d_2)$ by a pure strategy $\sigma$. Investors observe the disclosed values and hold a belief $\mu$ over $(\theta_1,\theta_2)$ after each message. A belief system is *admissible* if after every message it is a probability vector supported on the profiles that agree with every disclosed $\theta_i$; it is *Bayes-consistent* with $\sigma$ if after every message sent by some type it is the prior conditioned on the set of types sending it. Investors choose $k \in \{0,1,2\}$ (PBE item 3):
--   $$
--   k = 2 \text{ if } \exists \alpha\in[0,1]:\ (E[\theta_1] + E[\theta_2])\,\alpha X = 2 + c\,\#D \quad (1),
--   $$
--   otherwise $k = 1$ if some $\alpha \in [0,1]$ solves $E[\theta_\lambda]\,\alpha X = 1 + c\,\#D$ (3), otherwise $k = 0$; $\alpha$ is the corresponding (unique) share. With one unit the manager implements project 1 iff $\theta_1 \ge \theta_2$ (p. 11), so $\theta_\lambda = \max(\theta_1,\theta_2)$. The manager's payoff (4) is $q(\theta_1+\theta_2)(1-\alpha)X + 2\beta$ if $k = 2$, $q\max(\theta_1,\theta_2)(1-\alpha)X + \beta$ if $k = 1$, and $0$ if $k = 0$, evaluated at the true types.
--
--   A **pure-strategy PBE** is a pair $(\sigma,\mu)$ with $\mu$ admissible and Bayes-consistent with $\sigma$, such that (item 2) no type gains by any other disclosure vector, and (item 5, the tie rule) whenever a type discloses project $i$, withholding project $i$ alone gives it a strictly lower payoff. Its **investment efficiency** is the expected net cash flow
--   $$
--   \sum_{\theta} \Pr(\theta)\,\mathrm{NCF}(\theta), \qquad \mathrm{NCF} = \begin{cases} (\theta_1+\theta_2)X - (2 + c\,\#D), & k = 2,\\ \max(\theta_1,\theta_2)X - (1 + c\,\#D), & k = 1,\\ 0, & k = 0,\end{cases}
--   $$
--   and $\mathcal V_m$ (`effSetM`) is the set of efficiencies of all such equilibria.
--
--   **Stand-alone firms ($o = s$).** Each firm $i$ has its own manager, who observes $\theta_i$ only; investors invest ($k_i = 1$) iff some $\alpha_i \in [0,1]$ solves $E[\theta_i \mid d_i]\,\alpha_i X = 1 + c\,I(d_i)$ (2), and the manager's payoff (5) is $q\theta_i(1-\alpha_i)X + \beta$ if $k_i = 1$ and $0$ otherwise. Equilibria, the tie rule and efficiency ($\theta_i X - (1 + c\,I(d_i))$ if $k_i = 1$) are defined in the same way. Since the two firms' games are separate, $\mathcal V_s$ (`effSetS`) is the set of sums of the efficiencies of an equilibrium of firm 1 and an equilibrium of firm 2.
--
--   These objects carry every result of the mission: the paper's "equilibrium with the highest investment efficiency" for a structure is the greatest element of $\mathcal V_m$ or $\mathcal V_s$.
--
--   **Formalization Note.** Project 1 is index `0`, project 2 is index `1`; a type `true` is $\theta_i = 1$ and a disclosure `true` is $D$. Messages are `Fin 2 → Option Bool` (`some b` = disclosed value $b$). Off-path beliefs are arbitrary admissible beliefs. Parameters are plain reals; the standing hypotheses $0<p<1$, $X>1$, $c>0$, $0<q<1$, $\beta>qX$ and the focus $X \ge 1+c$ are hypotheses of the theorems. The share is defined as $(k + c\,\#D)/(E\,X)$ for the realized $k$, which is the unique solution of the break-even equation. The paper's β is written `bet`.
-- source:
--   Hwang, Internal Capital Allocation, Voluntary Disclosure, and Investment Efficiency, author manuscript (March 2025) of Management Science doi:10.1287/mnsc.2022.01295, pp. 5–8, (1)–(5), Equilibrium Definition; p. 11 (λ rule)

import Mathlib

namespace IntCapAlloc.OrgChoice

/-! # Hwang, *Internal Capital Allocation, Voluntary Disclosure, and Investment Efficiency*, §2

Two projects; project 1 of the paper is index `0`, project 2 is index `1`. A type `true` means
θᵢ = 1 (profitable, cash flow `X`), `false` means θᵢ = 0. A disclosure `true` means dᵢ = D,
`false` means dᵢ = ND. Parameters: success probability `p`, cash flow `X`, disclosure cost `c`,
manager's residual share `q`, empire-building benefit `bet` (the paper's β). The standing
hypotheses (0 < p < 1, X > 1, c > 0, 0 < q < 1, β > qX, X ≥ 1 + c) are binders of the theorems. -/

/-- A type profile (θ₁, θ₂); index `0` is project 1. -/
abbrev Profile := Fin 2 → Bool

/-- A disclosure vector (d₁, d₂); `true` = D (disclose), `false` = ND. -/
abbrev Disc := Fin 2 → Bool

/-- What investors observe: `some b` if θᵢ = b was disclosed, `none` if project i is silent. -/
abbrev Msg := Fin 2 → Option Bool

/-- The value of a type: θ = 1 for `true`, θ = 0 for `false`. -/
def th (b : Bool) : ℝ := if b then 1 else 0

/-- The prior probability of a type profile: θ₁, θ₂ independent with Pr(θᵢ = 1) = p. -/
def prior (p : ℝ) (t : Profile) : ℝ := ∏ i, if t i then p else 1 - p

/-- Truthful disclosure: the message sent by type `t` with disclosure vector `d`. -/
def msg (t : Profile) (d : Disc) : Msg := fun i => if d i then some (t i) else none

/-- The number of disclosures in a message, I(d₁) + I(d₂). -/
def nD (m : Msg) : ℕ := (Finset.univ.filter fun i => (m i).isSome).card

/-- A type profile is consistent with a message if it agrees with every disclosed θᵢ. -/
def Consistent (m : Msg) (t : Profile) : Prop := ∀ i b, m i = some b → t i = b

/-- Investors' beliefs: a weight on each type profile after each message. -/
abbrev Belief := Msg → Profile → ℝ

/-- A belief system is admissible if after every message (on or off path) it is a probability
vector supported on the type profiles consistent with the message (disclosure is truthful). -/
def Admissible (μ : Belief) : Prop :=
  ∀ m, (∀ t, 0 ≤ μ m t) ∧ (∑ t, μ m t = 1) ∧ ∀ t, μ m t ≠ 0 → Consistent m t

/-- A message is on the path of the pure disclosure strategy `σ` if some type sends it. -/
def OnPath (σ : Profile → Disc) (m : Msg) : Prop := ∃ t, msg t (σ t) = m

/-- The prior mass of the types that send message `m` under `σ`. -/
def pathMass (p : ℝ) (σ : Profile → Disc) (m : Msg) : ℝ :=
  ∑ t, if msg t (σ t) = m then prior p t else 0

/-- Bayes' rule on the equilibrium path: after every on-path message the belief is the prior
conditioned on the set of types that send it. Off-path beliefs are unrestricted (beyond
admissibility). -/
def BayesConsistent (p : ℝ) (σ : Profile → Disc) (μ : Belief) : Prop :=
  ∀ m, OnPath σ m → ∀ t', μ m t' = (if msg t' (σ t') = m then prior p t' else 0) / pathMass p σ m

/-- The implemented project's θ when one unit is raised (k = 1): by the λ rule of p. 11 the
manager implements project 1 iff θ₁ ≥ θ₂, so the implemented θ is max(θ₁, θ₂). -/
def implemented (t : Profile) : ℝ := max (th (t 0)) (th (t 1))

/-- E[θ₁ + θ₂ | m] under the belief, the left factor of (1). -/
def E2 (μ : Belief) (m : Msg) : ℝ := ∑ t, μ m t * (th (t 0) + th (t 1))

/-- E[θ_λ | m] under the belief and the λ rule, the left factor of (3). -/
def E1 (μ : Belief) (m : Msg) : ℝ := ∑ t, μ m t * implemented t

open Classical in
/-- Investors' choice k (PBE item 3, p. 8): k = 2 if some α ∈ [0,1] solves the break-even
condition (1); otherwise k = 1 if some α ∈ [0,1] solves (3); otherwise k = 0. -/
noncomputable def invest (X c : ℝ) (μ : Belief) (m : Msg) : ℕ :=
  if ∃ α ∈ Set.Icc (0 : ℝ) 1, E2 μ m * α * X = 2 + c * nD m then 2
  else if ∃ α ∈ Set.Icc (0 : ℝ) 1, E1 μ m * α * X = 1 + c * nD m then 1
  else 0

/-- The investors' break-even share α(k, d₁, d₂) solving (1) (k = 2) or (3) (k = 1); it is
unique because the right-hand side is positive. It is `0` (unused) when k = 0. -/
noncomputable def share (X c : ℝ) (μ : Belief) (m : Msg) : ℝ :=
  if invest X c μ m = 2 then (2 + c * nD m) / (E2 μ m * X)
  else if invest X c μ m = 1 then (1 + c * nD m) / (E1 μ m * X)
  else 0

/-- The multi-divisional manager's payoff (4) for true type `t` after message `m`, with the
λ rule for k = 1. -/
noncomputable def mgrPayoff (X c q bet : ℝ) (μ : Belief) (t : Profile) (m : Msg) : ℝ :=
  if invest X c μ m = 2 then q * (th (t 0) + th (t 1)) * (1 - share X c μ m) * X + 2 * bet
  else if invest X c μ m = 1 then q * implemented t * (1 - share X c μ m) * X + bet
  else 0

/-- A pure-strategy perfect Bayesian equilibrium of the multi-divisional firm (p. 8, items 2–6):
an admissible belief system, Bayes-consistent on path with the disclosure strategy `σ`; investors
act by `invest` (item 3); no type gains from another disclosure vector (item 2); and tie rule 5
per coordinate: if type `t` discloses project `i`, withholding it alone gives a strictly lower
payoff. -/
def IsEquilibrium (p X c q bet : ℝ) (σ : Profile → Disc) (μ : Belief) : Prop :=
  Admissible μ ∧ BayesConsistent p σ μ ∧
  (∀ t d, mgrPayoff X c q bet μ t (msg t d) ≤ mgrPayoff X c q bet μ t (msg t (σ t))) ∧
  (∀ t i, σ t i = true →
    mgrPayoff X c q bet μ t (msg t (Function.update (σ t) i false)) <
      mgrPayoff X c q bet μ t (msg t (σ t)))

/-- Realized net cash flow for true type `t`, message `m` and investment `k` (pp. 5, 7):
k = 2: (θ₁ + θ₂)X − (2 + c·#D); k = 1: max(θ₁, θ₂)X − (1 + c·#D); k = 0: 0. -/
def netCF (X c : ℝ) (t : Profile) (m : Msg) (k : ℕ) : ℝ :=
  if k = 2 then (th (t 0) + th (t 1)) * X - (2 + c * nD m)
  else if k = 1 then implemented t * X - (1 + c * nD m)
  else 0

/-- Investment efficiency of the multi-divisional firm: the prior-expected net cash flow. -/
noncomputable def efficiency (p X c : ℝ) (σ : Profile → Disc) (μ : Belief) : ℝ :=
  ∑ t, prior p t * netCF X c t (msg t (σ t)) (invest X c μ (msg t (σ t)))

/-- The investment efficiencies of all pure-strategy PBE of the multi-divisional firm. -/
def effSetM (p X c q bet : ℝ) : Set ℝ :=
  {v | ∃ σ μ, IsEquilibrium p X c q bet σ μ ∧ v = efficiency p X c σ μ}

/-! ## A stand-alone firm (o = s): one project, break-even condition (2), payoff (5) -/

/-- The prior of a single firm's type. -/
def prior1 (p : ℝ) (t : Bool) : ℝ := if t then p else 1 - p

/-- Truthful single-firm message: `some t` if disclosed (`d = true`), `none` if silent. -/
def msg1 (t : Bool) (d : Bool) : Option Bool := if d then some t else none

/-- I(dᵢ): one if the message is a disclosure. -/
def nD1 (m : Option Bool) : ℕ := if m.isSome then 1 else 0

/-- A type is consistent with a message if it agrees with the disclosed θ, if any. -/
def Consistent1 (m : Option Bool) (t : Bool) : Prop := ∀ b, m = some b → t = b

/-- A single firm's investors' beliefs. -/
abbrev Belief1 := Option Bool → Bool → ℝ

/-- Admissible single-firm beliefs: a probability vector on types consistent with the message. -/
def Admissible1 (μ : Belief1) : Prop :=
  ∀ m, (∀ t, 0 ≤ μ m t) ∧ (∑ t, μ m t = 1) ∧ ∀ t, μ m t ≠ 0 → Consistent1 m t

/-- The prior mass of the types that send `m` under `σ`. -/
def pathMass1 (p : ℝ) (σ : Bool → Bool) (m : Option Bool) : ℝ :=
  ∑ t, if msg1 t (σ t) = m then prior1 p t else 0

/-- Bayes' rule on the path of the single-firm strategy `σ`. -/
def BayesConsistent1 (p : ℝ) (σ : Bool → Bool) (μ : Belief1) : Prop :=
  ∀ m, (∃ t, msg1 t (σ t) = m) →
    ∀ t', μ m t' = (if msg1 t' (σ t') = m then prior1 p t' else 0) / pathMass1 p σ m

/-- E[θᵢ | dᵢ] under the belief. -/
def Eθ1 (μ : Belief1) (m : Option Bool) : ℝ := ∑ t, μ m t * th t

open Classical in
/-- Investors' choice kᵢ (PBE item 3): kᵢ = 1 iff some αᵢ ∈ [0,1] solves (2). -/
noncomputable def invest1 (X c : ℝ) (μ : Belief1) (m : Option Bool) : ℕ :=
  if ∃ α ∈ Set.Icc (0 : ℝ) 1, Eθ1 μ m * α * X = 1 + c * nD1 m then 1 else 0

/-- The break-even share αᵢ(dᵢ) solving (2) when kᵢ = 1 (`0`, unused, when kᵢ = 0). -/
noncomputable def share1 (X c : ℝ) (μ : Belief1) (m : Option Bool) : ℝ :=
  if invest1 X c μ m = 1 then (1 + c * nD1 m) / (Eθ1 μ m * X) else 0

/-- The stand-alone manager's payoff (5) for true type `t` after message `m`. -/
noncomputable def mgrPayoff1 (X c q bet : ℝ) (μ : Belief1) (t : Bool) (m : Option Bool) : ℝ :=
  if invest1 X c μ m = 1 then q * th t * (1 - share1 X c μ m) * X + bet else 0

/-- A pure-strategy PBE of a stand-alone firm (p. 8, items 2, 3, 5, 6), with tie rule 5. -/
def IsEquilibrium1 (p X c q bet : ℝ) (σ : Bool → Bool) (μ : Belief1) : Prop :=
  Admissible1 μ ∧ BayesConsistent1 p σ μ ∧
  (∀ t d, mgrPayoff1 X c q bet μ t (msg1 t d) ≤ mgrPayoff1 X c q bet μ t (msg1 t (σ t))) ∧
  (∀ t, σ t = true → mgrPayoff1 X c q bet μ t (msg1 t false) < mgrPayoff1 X c q bet μ t (msg1 t (σ t)))

/-- Realized net cash flow of a stand-alone firm: θᵢX − (1 + c·I(dᵢ)) if kᵢ = 1, else 0. -/
def netCF1 (X c : ℝ) (t : Bool) (m : Option Bool) (k : ℕ) : ℝ :=
  if k = 1 then th t * X - (1 + c * nD1 m) else 0

/-- Investment efficiency of one stand-alone firm. -/
noncomputable def efficiency1 (p X c : ℝ) (σ : Bool → Bool) (μ : Belief1) : ℝ :=
  ∑ t, prior1 p t * netCF1 X c t (msg1 t (σ t)) (invest1 X c μ (msg1 t (σ t)))

/-- The investment efficiencies of all pure-strategy PBE of one stand-alone firm. -/
def effSet1 (p X c q bet : ℝ) : Set ℝ :=
  {v | ∃ σ μ, IsEquilibrium1 p X c q bet σ μ ∧ v = efficiency1 p X c σ μ}

/-- The investment efficiencies of the stand-alone structure (o = s): two independent firms,
each in a PBE of its own game; the structure's efficiency is the sum of the two firms'. -/
def effSetS (p X c q bet : ℝ) : Set ℝ :=
  {v | ∃ σ₁ μ₁ σ₂ μ₂, IsEquilibrium1 p X c q bet σ₁ μ₁ ∧ IsEquilibrium1 p X c q bet σ₂ μ₂ ∧
    v = efficiency1 p X c σ₁ μ₁ + efficiency1 p X c σ₂ μ₂}

end IntCapAlloc.OrgChoice


