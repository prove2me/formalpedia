-- Prove2me | Definitions.Def_PubFrequency_PublishingGame
-- name    : PubFrequency_PublishingGame
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:29:52.173151+00:00
-- url     : https://prove2.me/theorems/7dc80a70-bcc3-419d-8b8f-7f86ed3929d6
-- title:
--   The publishing game (10): closed-form payoffs (EC.3), Lemma EC.5, (EC.48), (EC.55) at $\beta=1$, feasible cycles, and its pure equilibria
-- statement:
--   This module defines the publishing game (10) of Chen and Roels (p. 12), in which two identical publishers choose publication cycles anticipating their pricing-equilibrium profits. Parameters: decay rate $\alpha>0$ and fixed cost $k>0$.
--
--   **Closed-form profits.** For a fast cycle $u_f$ and a slow cycle $u_s$:
--   1. (EC.3), Lemma EC.2: $\pi^{3}_f=\dfrac{\alpha(u_f-2u_s)^2}{16u_s}-\dfrac{k}{u_f}$ if $u_f\le\dfrac{4-2\alpha u_s}{\alpha}$, else $\dfrac{(2-\alpha u_f)(\alpha u_s-1)}{2\alpha u_s}-\dfrac{k}{u_f}$; and $\pi^{3}_s=\dfrac{\alpha(u_f+2u_s)^4}{512u_s^3}-\dfrac{k}{u_s}$ if $u_s\le\dfrac{4-\alpha u_f}{2\alpha}$, else $\dfrac{(\alpha u_f+2\alpha u_s-2)^2}{8\alpha^3u_s^3}-\dfrac{k}{u_s}$;
--   2. Lemma EC.5: $\pi^{5}_f=\dfrac{\alpha(u_f-2u_s)^2}{16u_s}-\dfrac{k}{u_f}$ and $\pi^{5}_s=\dfrac{\alpha(u_f+2u_s)^4}{512u_s^3}-\dfrac{k}{u_s}$;
--   3. (EC.48) at $\beta=1$: $\pi^{48}_f=\dfrac1{2\alpha}\Bigl(\dfrac1{u_f}-\dfrac1{u_s}\Bigr)-\dfrac{k}{u_f}$ and $\pi^{48}_s=\dfrac1{2\alpha}\,\dfrac{u_s-u_f}{u_s^2}-\dfrac{k}{u_s}$.
--
--   **Payoffs.** The fast firm earns $\pi^5_f$ if $\alpha u_s\le1$, $\pi^3_f$ if $\alpha u_f\le1<\alpha u_s$, and $\pi^{48}_f$ if $\alpha u_f>1$; the slow firm likewise earns $\pi^5_s$, $\pi^3_s$ or $\pi^{48}_s$. A firm with cycle $u$ facing a rival with cycle $u'$ earns
--   $$\pi(u;u')=\begin{cases}\text{fast payoff}(u,u'),&u<u',\\ \text{slow payoff}(u,u'),&u'<u,\\ -k/u,&u=u'\ \text{((EC.55) at }\beta=1).\end{cases}$$
--
--   **Feasible cycles and equilibrium.** Facing $u'$, a firm may choose any $u>0$ with $u=u'$ or $\max\{u,u'\}/\min\{u,u'\}\ge2$. A pair $(u_1,u_2)$ of positive, mutually feasible cycles is an **equilibrium of (10)** if $\pi(u;u_2)\le\pi(u_1;u_2)$ for every $u$ feasible against $u_2$, and $\pi(u;u_1)\le\pi(u_2;u_1)$ for every $u$ feasible against $u_1$.
--
--   **Formalization Note** The game (10) relaxes the integer-ratio constraint of the pricing game, which is undefined at non-integer ratios; the payoffs are therefore the paper's closed-form pricing-equilibrium profits at $\beta=1$, which its proof of Theorem 3 uses for all cycles (pp. ec21–ec22). Lemmas EC.2 and EC.5 tie these closed forms to the pricing game at integer ratios. On the boundary $\alpha u_f=1$, where (EC.3) and (EC.48) give different slow-firm profits, the (EC.3) branch is used. The ratio condition is written $2u\le u'\lor 2u'\le u$. The argmax in (10) is read as "is a maximizer".
-- source:
--   Chen–Roels, Fast or Slow? Competing on Publication Frequency, SSRN 3986163 (INSEAD WP 2021/74/TOM, 2021), §3.3 eq. (10), p.12 (PDF 13); Lemma EC.2 (EC.3), p.ec1 (PDF 30); Lemma EC.5, p.ec2 (PDF 31); (EC.48), p.ec18 (PDF 47); (EC.55), p.ec22 (PDF 51)

import Mathlib

namespace PubFrequency

/-- **The fast firm's profit (EC.3), first display**, Chen–Roels, *Fast or Slow? Competing on
Publication Frequency*, SSRN 3986163 (INSEAD WP 2021/74/TOM), Lemma EC.2, p. ec1 (PDF 30), for
fast cycle `uf` and slow cycle `us`:
`α(uf − 2us)²/(16us) − k/uf` if `uf ≤ (4 − 2α us)/α`, else
`(2 − α uf)(α us − 1)/(2α us) − k/uf`. -/
noncomputable def fastEC3 (α k uf us : ℝ) : ℝ :=
  if uf ≤ (4 - 2 * α * us) / α then α * (uf - 2 * us) ^ 2 / (16 * us) - k / uf
  else (2 - α * uf) * (α * us - 1) / (2 * α * us) - k / uf

/-- **The slow firm's profit (EC.3), second display**, Chen–Roels, SSRN 3986163, Lemma EC.2,
p. ec1 (PDF 30), for fast cycle `uf` and slow cycle `us`:
`α(uf + 2us)⁴/(512 us³) − k/us` if `us ≤ (4 − α uf)/(2α)`, else
`(α uf + 2α us − 2)²/(8α³ us³) − k/us`. (The paper labels it `π₂(u₁; u₂)`, a typo for
`π₂(u₂; u₁)`.) -/
noncomputable def slowEC3 (α k uf us : ℝ) : ℝ :=
  if us ≤ (4 - α * uf) / (2 * α) then α * (uf + 2 * us) ^ 4 / (512 * us ^ 3) - k / us
  else (α * uf + 2 * α * us - 2) ^ 2 / (8 * α ^ 3 * us ^ 3) - k / us

/-- **The fast firm's profit of Lemma EC.5**, Chen–Roels, SSRN 3986163, p. ec2 (PDF 31):
`α(uf − 2us)²/(16us) − k/uf`. -/
noncomputable def fastEC5 (α k uf us : ℝ) : ℝ :=
  α * (uf - 2 * us) ^ 2 / (16 * us) - k / uf

/-- **The slow firm's profit of Lemma EC.5**, Chen–Roels, SSRN 3986163, p. ec2 (PDF 31):
`α(uf + 2us)⁴/(512 us³) − k/us`. -/
noncomputable def slowEC5 (α k uf us : ℝ) : ℝ :=
  α * (uf + 2 * us) ^ 4 / (512 * us ^ 3) - k / us

/-- **The fast firm's profit (EC.48) at `β = 1`**, Chen–Roels, SSRN 3986163, proof of
Lemma EC.12, p. ec18 (PDF 47), case `u₁ < β u₂`: `(1/(2α))(1/uf − 1/us) − k/uf`. -/
noncomputable def fastEC48 (α k uf us : ℝ) : ℝ :=
  1 / (2 * α) * (1 / uf - 1 / us) - k / uf

/-- **The slow firm's profit (EC.48) at `β = 1`**, Chen–Roels, SSRN 3986163, proof of
Lemma EC.12, p. ec18 (PDF 47), case `u₂ > u₁/β`: `(1/(2α))(us − uf)/us² − k/us`. -/
noncomputable def slowEC48 (α k uf us : ℝ) : ℝ :=
  1 / (2 * α) * ((us - uf) / us ^ 2) - k / us

/-- **The fast firm's payoff in the publishing game (10)**, Chen–Roels, SSRN 3986163, §3.3,
p. 12 (PDF 13): the pricing-equilibrium profit `π(uf; us)` of the faster publisher, as the
paper's closed forms at `β = 1`:
* `α us ≤ 1` (both cycles short): Lemma EC.5;
* `α uf ≤ 1 < α us`: (EC.3);
* `α uf > 1`: (EC.48).

**Formalization Note.** (10) relaxes the integer-ratio constraint, so the payoff is needed at
cycles where the pricing game (which needs `u₂/u₁ ∈ ℕ`) is not defined; the paper's proof of
Theorem 3 (pp. ec21–ec22) uses exactly these closed forms, which are taken as the definition
for every real pair `uf < us`. On the boundary `α uf = 1` the (EC.3) branch is used (the
(EC.3)/(EC.5) branch covers `α uf ≤ 1`, as in that proof). -/
noncomputable def fastPay (α k uf us : ℝ) : ℝ :=
  if α * us ≤ 1 then fastEC5 α k uf us
  else if α * uf ≤ 1 then fastEC3 α k uf us
  else fastEC48 α k uf us

/-- **The slow firm's payoff in the publishing game (10)**, Chen–Roels, SSRN 3986163, §3.3,
p. 12 (PDF 13), for slow cycle `us` against fast cycle `uf` (own cycle first):
* `α us ≤ 1`: Lemma EC.5;
* `α uf ≤ 1 < α us`: (EC.3);
* `α uf > 1`: (EC.48) at `β = 1`.

**Formalization Note.** As for `fastPay`; at `α uf = 1` (EC.3) and (EC.48) give different slow-firm
profits, and the (EC.3) branch is used. -/
noncomputable def slowPay (α k us uf : ℝ) : ℝ :=
  if α * us ≤ 1 then slowEC5 α k uf us
  else if α * uf ≤ 1 then slowEC3 α k uf us
  else slowEC48 α k uf us

/-- **Firm payoff `π(u; u')` in the publishing game (10)**, Chen–Roels, SSRN 3986163, §3.3,
p. 12 (PDF 13): a firm with cycle `u` facing a rival with cycle `u'` earns `fastPay u u'` if it is
the faster publisher (`u < u'`), `slowPay u u'` if it is the slower (`u' < u`), and `−k/u` on
equal cycles ((EC.55) at `β = 1`, p. ec22, PDF 51). The two firms are symmetric. -/
noncomputable def pay (α k u u' : ℝ) : ℝ :=
  if u < u' then fastPay α k u u'
  else if u' < u then slowPay α k u u'
  else -k / u

/-- **Feasible cycle in the publishing game (10)**, Chen–Roels, SSRN 3986163, p. 12 (PDF 13):
a firm facing a rival with cycle `u'` may choose `u > 0` with `u = u'` or
`max{u, u'}/min{u, u'} ≥ 2`.

**Formalization Note.** For positive cycles the ratio condition is written
`2u ≤ u' ∨ 2u' ≤ u` (no division). -/
def Feasible (u u' : ℝ) : Prop :=
  0 < u ∧ (u = u' ∨ 2 * u ≤ u' ∨ 2 * u' ≤ u)

/-- **Pure-strategy Nash equilibrium of the publishing game (10)**, Chen–Roels, SSRN 3986163,
§3.3, p. 12 (PDF 13): positive cycles `(u₁, u₂)`, feasible against each other, such that each
firm's cycle maximizes its payoff `pay` over all cycles feasible against the rival's.

**Formalization Note.** (10) writes `u*ᵢ = argmax …`; it is read as "`u*ᵢ` is a maximizer"
(no uniqueness of the best response is required). The payoffs are the closed forms of
`pay`. -/
def IsPubEq (α k u₁ u₂ : ℝ) : Prop :=
  Feasible u₁ u₂ ∧ Feasible u₂ u₁ ∧
    (∀ u : ℝ, Feasible u u₂ → pay α k u u₂ ≤ pay α k u₁ u₂) ∧
    (∀ u : ℝ, Feasible u u₁ → pay α k u u₁ ≤ pay α k u₂ u₁)

end PubFrequency


