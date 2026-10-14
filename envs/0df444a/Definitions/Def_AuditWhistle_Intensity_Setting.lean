-- Prove2me | Definitions.Def_AuditWhistle_Intensity_Setting
-- name    : AuditWhistle_Intensity_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T05:16:50.756791+00:00
-- url     : https://prove2.me/theorems/15fcba35-a8ab-4842-ad5a-9cdbe814ad91
-- title:
--   §2 and §3.1, (3)–(6) — the audit–whistleblowing–enforcement game: posteriors, best responses, equilibrium, and the threshold r*
-- statement:
--   This file fixes the game of Nan, Tang and Ye between an auditor, a whistleblower and an enforcer.
--
--   A **model** consists of real parameters $p,\beta,R,\gamma,D,k$ with
--   $$0<p<1,\qquad \tfrac12<\beta<1,\qquad R,\gamma,D,k>0,\qquad \frac{R}{\gamma}<\frac{1}{1-p},\qquad \frac{D}{k}<\frac{1}{1-p}.$$
--   The firm is good ($G$) with probability $p$ and bad ($B$) with probability $1-p$. The auditor chooses audit quality $a$; she always issues a clean opinion $g$ on a good firm and detects a bad firm with probability $a$. After a clean opinion the whistleblower receives a signal with $\Pr(s_l\mid B)=\Pr(s_h\mid G)=\beta$ and, on $s_l$, blows the whistle ($W_1$) with probability $\tau$, the **whistleblowing intensity**; otherwise the enforcer observes silence ($W_0$).
--
--   1. **Joint probabilities and posteriors.** For audit quality $a$ and intensity $\tau$,
--   $$\Pr(B,g,W_1)=(1-p)(1-a)\beta\tau,\quad \Pr(G,g,W_1)=p(1-\beta)\tau,$$
--   $$\Pr(B,g,W_0)=(1-p)(1-a)(1-\beta\tau),\quad \Pr(G,g,W_0)=p\,[1-(1-\beta)\tau],$$
--   and the enforcer's posteriors $\Pr(B\mid g,W_1)$, $\Pr(B\mid g,W_0)$ are given by Bayes' rule from these.
--   2. **Enforcer.** At posterior $q$ the enforcer's objective (3) is $qeR-\tfrac12\gamma e^2$; a best response is a maximizer of it over efforts $e\in[0,1]$ (effort is a detection probability).
--   3. **Detection probability** (6): $\Pr(r_b\mid B,g)=\beta\tau e_1+(1-\beta\tau)e_0$, where $e_1,e_0$ are the efforts after a tip and after silence.
--   4. **Auditor.** At detection probability $P$ the auditor's loss (4) is $(1-p)(1-a)PD+\tfrac12ka^2$; a best response is a minimizer of it over $a\in(0,1)$.
--   5. **Equilibrium.** $(a,e_1,e_0)$ is an equilibrium at intensity $\tau$ if $a$ is a best response of the auditor to $\Pr(r_b\mid B,g)=\beta\tau e_1+(1-\beta\tau)e_0$, and $e_1$, $e_0$ are best responses of the enforcer to the posteriors $\Pr(B\mid g,W_1)$, $\Pr(B\mid g,W_0)$ computed at that same $a$ (rational expectations).
--   6. **Equilibrium path.** A function $A$ of $\tau$ is an equilibrium path if for every $\tau\in(0,1)$ there are $e_1,e_0$ with $(A(\tau),e_1,e_0)$ an equilibrium.
--   7. **The threshold $r^*$** of the proof of Proposition 2:
--   $$r^*(p,\beta,\tau)=\frac{\beta\,[\tau(\beta-2\beta p+p)-1]^2}{(p-1)(\beta\tau-1)\,[\beta-\beta^2\tau+(2\beta-1)p(\beta\tau+1)]}.$$
--
--   These objects are what Propositions 1 and 2 of the paper are about; every statement of this mission is phrased through them.
--
--   **Formalization Note** The firm's cash flow $X$, investment $I$, audit fee $F$, the investors (Lemma 1) and the restrictions $R<I$, $D\le I-R$ of p. 9 are omitted: none of them enters the programs (3)–(4) or the equilibrium conditions (7)–(9). The posteriors are defined from the joint probabilities, not from the simplified closed forms, so that the enforcer's best responses are a theorem and not a definition. The intensity $\tau$ is an explicit argument, not a model field.
-- source:
--   Nan, Tang & Ye, Auditing with a Chance of Whistleblowing, author manuscript dated December 30, 2024 (Management Science, DOI 10.1287/mnsc.2024.04808), pp. 6–13, §2, §3.1, (3)–(9), and p. 33

import Mathlib

namespace AuditWhistle.Intensity

/-- The primitives of the audit–whistleblowing–enforcement game (Nan, Tang & Ye, §2, pp. 6–10):
prior probability `p` of a good firm, whistleblower signal quality `β ∈ (1/2, 1)`, the
enforcer's benefit `R` and cost coefficient `γ`, the auditor's damage payment `D` and cost
coefficient `k`, with the parameter restrictions `R/γ < 1/(1-p)` and `D/k < 1/(1-p)` of p. 10. -/
structure Model where
  p : ℝ
  β : ℝ
  R : ℝ
  γ : ℝ
  D : ℝ
  k : ℝ
  hp0 : 0 < p
  hp1 : p < 1
  hβ0 : 1 / 2 < β
  hβ1 : β < 1
  hR : 0 < R
  hγ : 0 < γ
  hD : 0 < D
  hk : 0 < k
  hRγ : R / γ < 1 / (1 - p)
  hDk : D / k < 1 / (1 - p)

/-- Pr(B, g, W₁): bad firm, clean opinion, whistle blown (audit quality `a`, intensity `τ`). -/
def jointBW1 (M : Model) (τ a : ℝ) : ℝ := (1 - M.p) * (1 - a) * (M.β * τ)

/-- Pr(G, g, W₁): good firm, clean opinion, whistle blown. -/
def jointGW1 (M : Model) (τ : ℝ) : ℝ := M.p * ((1 - M.β) * τ)

/-- Pr(B, g, W₀): bad firm, clean opinion, no whistleblowing. -/
def jointBW0 (M : Model) (τ a : ℝ) : ℝ := (1 - M.p) * (1 - a) * (1 - M.β * τ)

/-- Pr(G, g, W₀): good firm, clean opinion, no whistleblowing. -/
def jointGW0 (M : Model) (τ : ℝ) : ℝ := M.p * (1 - (1 - M.β) * τ)

/-- The enforcer's posterior Pr(B | g, W₁) (Bayes' rule). -/
noncomputable def postW1 (M : Model) (τ a : ℝ) : ℝ :=
  jointBW1 M τ a / (jointBW1 M τ a + jointGW1 M τ)

/-- The enforcer's posterior Pr(B | g, W₀) (Bayes' rule). -/
noncomputable def postW0 (M : Model) (τ a : ℝ) : ℝ :=
  jointBW0 M τ a / (jointBW0 M τ a + jointGW0 M τ)

/-- The enforcer's objective (3) at posterior `q` and effort `e`. -/
noncomputable def enforcerObj (M : Model) (q e : ℝ) : ℝ := q * e * M.R - M.γ / 2 * e ^ 2

/-- `e` is an optimal investigative effort in `[0, 1]` for the enforcer at posterior `q`. -/
def IsEnforcerBR (M : Model) (q e : ℝ) : Prop :=
  e ∈ Set.Icc (0:ℝ) 1 ∧ ∀ e' ∈ Set.Icc (0:ℝ) 1, enforcerObj M q e' ≤ enforcerObj M q e

/-- The detection probability Pr(r_b | B, g) = βτ e₁ + (1 - βτ) e₀ of (6). -/
def detectProb (M : Model) (τ e1 e0 : ℝ) : ℝ := M.β * τ * e1 + (1 - M.β * τ) * e0

/-- The auditor's expected cost (4) at detection probability `P` and audit quality `a`. -/
noncomputable def auditorLoss (M : Model) (P a : ℝ) : ℝ := (1 - M.p) * (1 - a) * P * M.D + M.k / 2 * a ^ 2

/-- `a` is an optimal audit quality in `(0, 1)` for the auditor at detection probability `P`. -/
def IsAuditorBR (M : Model) (P a : ℝ) : Prop :=
  a ∈ Set.Ioo (0:ℝ) 1 ∧ ∀ a' ∈ Set.Ioo (0:ℝ) 1, auditorLoss M P a ≤ auditorLoss M P a'

/-- An equilibrium `(a, e₁, e₀)` at intensity `τ`: mutual best responses with correct
conjectures (rational expectations, p. 13). -/
def IsEquilibrium (M : Model) (τ a e1 e0 : ℝ) : Prop :=
  IsAuditorBR M (detectProb M τ e1 e0) a ∧ IsEnforcerBR M (postW1 M τ a) e1 ∧
    IsEnforcerBR M (postW0 M τ a) e0

/-- The threshold `r*` of the proof of Proposition 2 (p. 33). -/
noncomputable def rStar (p β τ : ℝ) : ℝ :=
  β * (τ * (β - 2 * β * p + p) - 1) ^ 2 /
    ((p - 1) * (β * τ - 1) * (β - β ^ 2 * τ + (2 * β - 1) * p * (β * τ + 1)))

/-- `A` gives an equilibrium audit quality at every intensity `τ ∈ (0, 1)`. -/
def IsEquilibriumPath (M : Model) (A : ℝ → ℝ) : Prop :=
  ∀ τ ∈ Set.Ioo (0:ℝ) 1, ∃ e1 e0 : ℝ, IsEquilibrium M τ (A τ) e1 e0

end AuditWhistle.Intensity


