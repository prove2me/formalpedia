-- Prove2me | Definitions.Def_RobustObedientPersuasion_Saddle_Supplement_Unrestricted
-- name    : RobustObedientPersuasion_Saddle_Supplement_Unrestricted
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:26:32.001688+00:00
-- url     : https://prove2.me/theorems/abc52989-9e46-4fe5-92f9-24add5ba1a93
-- title:
--   §4 — the unrestricted persuasion problem, values W(α) and W_RO(α), obedience margins, L_R, M_v, the ℓ1 radius r_1 and Receiver Action Stability
-- statement:
--   Let $\Omega$ and $A$ be finite, $u,v:\Omega\times A\to\mathbb R$ the Receiver's and Sender's utilities, $\alpha\in\Delta(A)$ with support $B$, and let $\mathcal P(\alpha)$, $\Pi_B$, $\Pi_{RO}(\alpha)$ and $V(\pi\mid\mu)$ be the identified set, the supported direct policies, the robustly obedient policies and the robust Sender payoff of the base model.
--
--   1. A **signaling policy** with finite message set $S$ is $\pi:\Omega\to\Delta(S)$, written $\pi(s\mid\omega)$.
--   2. For a prior $\mu$ and message $s$, the Receiver's **best-response set** is
--   $$BR(\pi,s,\mu)=\arg\max_{a\in A}\sum_{\omega}\pi(s\mid\omega)\mu(\omega)u(a,\omega).$$
--   For a message of positive probability this is the argmax of the posterior expected utility; for a message of probability zero it is all of $A$.
--   3. The Sender's **unrestricted payoff**, with the Sender-preferred selection from the best-response set, is
--   $$V_{\mathrm{unr}}(\pi\mid\mu)=\sum_{s\in S}\ \max_{a\in BR(\pi,s,\mu)}\ \sum_{\omega}\pi(s\mid\omega)\mu(\omega)v(a,\omega).$$
--   4. The **unrestricted value** and the **robustly obedient value** are
--   $$W(\alpha)=\sup_{S,\ \pi}\ \inf_{\mu\in\mathcal P(\alpha)}V_{\mathrm{unr}}(\pi\mid\mu),\qquad W_{RO}(\alpha)=\max_{\pi\in\Pi_{RO}(\alpha)}\ \min_{\mu\in\mathcal P(\alpha)}V(\pi\mid\mu).$$
--   5. A direct policy $\pi\in\Pi_B$ (messages $=$ actions) is **unrestricted maxmin-optimal** if $\inf_{\mu\in\mathcal P(\alpha)}V_{\mathrm{unr}}(\pi\mid\mu)=W(\alpha)$.
--   6. The **obedience margin** of $\pi$ for recommendation $a$ against $a'$ at prior $p$ is $D^\pi_{a,a'}(p)=\sum_\omega\pi(a\mid\omega)p(\omega)[u(a,\omega)-u(a',\omega)]$, and the **incentive margin** is $\gamma=\min_{a\in B,\,a'\in A\setminus\{a\}}D^\pi_{a,a'}(p)$.
--   7. The constants $L_R=\max_{a\in B,\,a'\in A\setminus\{a\},\,\omega}|u(a,\omega)-u(a',\omega)|$ and $M_v=\max_{a\in B,\,\omega}|v(a,\omega)|$, and the **prior uncertainty radius** $r_1(\mathcal P(\alpha),\bar p)=\sup_{p\in\mathcal P(\alpha)}\|p-\bar p\|_1$ with $\|x\|_1=\sum_\omega|x(\omega)|$.
--   8. **Receiver Action Stability** of $\pi^*$ under $\pi'$ across $\mathcal P(\alpha)$: for every $a\in B$ and $p\in\mathcal P(\alpha)$, under both $\pi'$ and $\pi^*$, the Receiver's action after recommendation $a$ is $a$, i.e. $a\in BR(\cdot,a,p)$ and $a$ attains the Sender's maximum over that best-response set.
--
--   These are the objects of §4, in which Theorems 4.3 and 4.4 compare robust obedience with unrestricted signaling.
--
--   **Formalization Note** States come first in every array: `u ω a` is $u(a,\omega)$ and `π ω s` is $\pi(s\mid\omega)$. Message sets in $W(\alpha)$ are $\mathrm{Fin}\,m$ for $m\in\mathbb N$; every finite message set is in bijection with one of these, and $V_{\mathrm{unr}}$ does not change under relabelling messages. All maxima, minima, suprema and infima are real `sSup`/`sInf`; they are applied to finite sets or to nonempty bounded sets on the instances of the theorems, and an empty finite index set gives $0$. The ℓ1 distance is written out, not taken from Mathlib's sup norm on functions.
-- source:
--   Shabab Neel, Robustly Obedient Data Driven Persuasion under State-dependent Sender Payoffs, STOC 2027 submission #51 (October 2026), PDF SHA-256 c8d16d8d566dd78eea1f7db42ce72f49000256f933311c4daac2de1df952b40d, §2 setup display (PDF p. 2), footnote 3 (PDF p. 3), W_RO(α) ≤ W(α) (PDF p. 4), Theorems 4.3 and 4.4 (PDF p. 5), Appendix B (PDF p. 8)

import Mathlib
import Definitions.Def_RobustObedientPersuasion_Saddle_Model

namespace RobustObedientPersuasion.Saddle.Supplement

variable {Ω A : Type*} [Fintype Ω] [Fintype A]

/-! Objects of §4 of Neel, *Robustly Obedient Data Driven Persuasion under State-dependent
Sender Payoffs*: the unrestricted signaling problem, its value `W(α)`, the robust value
`W_RO(α)`, obedience margins, the constants `L_R`, `M_v` and the radius `r_1`.
Indexing is state-first as in `RobustObedientPersuasion.Saddle.Model`: `u ω a = u(a, ω)`,
`π ω s = π(s | ω)`. -/

/-- A signaling policy with message set `S`: `π ω s = π(s | ω)`, each row a probability vector. -/
def IsSignalingPolicy {S : Type*} [Fintype S] (π : Ω → S → ℝ) : Prop :=
  (∀ ω s, 0 ≤ π ω s) ∧ ∀ ω, ∑ s, π ω s = 1

/-- The Receiver's unnormalized expected utility of action `a` jointly with message `s`:
`∑_ω π(s | ω) μ(ω) u(a, ω)` (Appendix B). -/
noncomputable def receiverObj {S : Type*} (u : Ω → A → ℝ) (π : Ω → S → ℝ) (μ : Ω → ℝ)
    (s : S) (a : A) : ℝ :=
  ∑ ω, π ω s * μ ω * u ω a

/-- The Sender's unnormalized expected utility of action `a` jointly with message `s`:
`∑_ω π(s | ω) μ(ω) v(a, ω)`. -/
noncomputable def senderObj {S : Type*} (v : Ω → A → ℝ) (π : Ω → S → ℝ) (μ : Ω → ℝ)
    (s : S) (a : A) : ℝ :=
  ∑ ω, π ω s * μ ω * v ω a

/-- The Receiver's best-response set `BR(π, s, μ) = argmax_{a ∈ A} ∑_ω π(s|ω) μ(ω) u(a, ω)`.
For a message of positive probability this is the argmax of posterior expected utility; for a
message of probability zero every action is a best response. -/
def bestResponses {S : Type*} (u : Ω → A → ℝ) (π : Ω → S → ℝ) (μ : Ω → ℝ) (s : S) : Set A :=
  {a | ∀ a' : A, receiverObj u π μ s a' ≤ receiverObj u π μ s a}

/-- The Sender's payoff in the unrestricted problem under the Sender-preferred selection from the
Receiver's best-response set (footnote 3, [Ros26]):
`V_unr(π | μ) = ∑_{s ∈ S} max_{a ∈ BR(π, s, μ)} ∑_ω π(s | ω) μ(ω) v(a, ω)`.
The maximum is the real `sSup` of a finite set (nonempty whenever `A` is nonempty). -/
noncomputable def unrestrictedPayoff {S : Type*} [Fintype S] (u v : Ω → A → ℝ)
    (π : Ω → S → ℝ) (μ : Ω → ℝ) : ℝ :=
  ∑ s, sSup ((fun a => senderObj v π μ s a) '' bestResponses u π μ s)

/-- The unrestricted maxmin value
`W(α) = sup_{S finite, π : Ω → Δ(S)} inf_{μ ∈ P(α)} V_unr(π | μ)`.
Message sets are `Fin m`, `m ∈ ℕ`; every finite message set is in bijection with some `Fin m`
and `V_unr` is invariant under relabelling messages. -/
noncomputable def unrestrictedValue (u v : Ω → A → ℝ) (α : A → ℝ) : ℝ :=
  sSup {x | ∃ (m : ℕ) (π : Ω → Fin m → ℝ), IsSignalingPolicy π ∧
    x = sInf ((fun μ => unrestrictedPayoff u v π μ) '' identifiedSet u α)}

/-- The robustly obedient value `W_RO(α) = max_{π ∈ Π_RO(α)} min_{μ ∈ P(α)} V(π | μ)`. -/
noncomputable def robustValue (u v : Ω → A → ℝ) (α : A → ℝ) : ℝ :=
  sSup {x | ∃ π ∈ robustlyObedientPolicies u α,
    x = sInf ((fun μ => senderPayoff v α π μ) '' identifiedSet u α)}

/-- An unrestricted maxmin-optimal direct policy: `π ∈ Π_B` (messages = actions, recommending
only actions in `B`) whose unrestricted worst-case value attains the unrestricted optimum,
`inf_{μ ∈ P(α)} V_unr(π | μ) = W(α)`. -/
def IsUnrestrictedMaxminOptimalDirect (u v : Ω → A → ℝ) (α : A → ℝ) (π : Ω → A → ℝ) : Prop :=
  π ∈ supportedPolicies α ∧
    sInf ((fun μ => unrestrictedPayoff u v π μ) '' identifiedSet u α) = unrestrictedValue u v α

/-- The obedience margin
`D^π_{a,a'}(p) = ∑_ω π(a | ω) p(ω) [u(a, ω) - u(a', ω)]`. -/
noncomputable def obedienceMargin (u : Ω → A → ℝ) (π : Ω → A → ℝ) (a a' : A) (p : Ω → ℝ) : ℝ :=
  ∑ ω, π ω a * p ω * (u ω a - u ω a')

/-- The strict Receiver incentive margin `γ = min_{a ∈ B, a' ∈ A \ {a}} D^π_{a,a'}(p)`
(real `sInf` of a finite set; `0` when the index set is empty). -/
noncomputable def incentiveMargin (u : Ω → A → ℝ) (α : A → ℝ) (π : Ω → A → ℝ)
    (p : Ω → ℝ) : ℝ :=
  sInf {x | ∃ a ∈ supp α, ∃ a' : A, a' ≠ a ∧ x = obedienceMargin u π a a' p}

/-- The utility range `L_R = max_{a ∈ B, a' ∈ A \ {a}, ω ∈ Ω} |u(a, ω) - u(a', ω)|`
(real `sSup` of a finite set; `0` when the index set is empty). -/
noncomputable def utilityRange (u : Ω → A → ℝ) (α : A → ℝ) : ℝ :=
  sSup {x | ∃ a ∈ supp α, ∃ a' : A, a' ≠ a ∧ ∃ ω : Ω, x = |u ω a - u ω a'|}

/-- The Sender payoff bound `M_v = max_{a ∈ B, ω ∈ Ω} |v(a, ω)|`
(real `sSup` of a finite set; `0` when the index set is empty). -/
noncomputable def senderBound (v : Ω → A → ℝ) (α : A → ℝ) : ℝ :=
  sSup {x | ∃ a ∈ supp α, ∃ ω : Ω, x = |v ω a|}

/-- The ℓ1 distance `‖p - q‖_1 = ∑_ω |p(ω) - q(ω)|`. -/
noncomputable def l1Dist (p q : Ω → ℝ) : ℝ :=
  ∑ ω, |p ω - q ω|

/-- The prior uncertainty radius `r_1(P(α), p̄) = sup_{p ∈ P(α)} ‖p - p̄‖_1` (ℓ1 norm). -/
noncomputable def uncertaintyRadius (u : Ω → A → ℝ) (α : A → ℝ) (pbar : Ω → ℝ) : ℝ :=
  sSup ((fun p => l1Dist p pbar) '' identifiedSet u α)

/-- `a*(s, p; π) = a`: in the unrestricted problem, after message `s` under prior `p` and policy
`π`, the Receiver takes action `a` under the Sender-preferred selection, i.e. `a` is a best
response and attains the Sender's maximum over the best-response set. -/
def ReceiverTakes {S : Type*} (u v : Ω → A → ℝ) (π : Ω → S → ℝ) (p : Ω → ℝ) (s : S) (a : A) :
    Prop :=
  a ∈ bestResponses u π p s ∧
    senderObj v π p s a = sSup ((fun a' => senderObj v π p s a') '' bestResponses u π p s)

/-- Receiver Action Stability of `π*` under `π'` across `P(α)`:
`a*(a, p; π') = a*(a, p; π*) = a` for all `a ∈ B`, `p ∈ P(α)` (direct policies, message `a` =
recommendation `a`). -/
def ReceiverActionStable (u v : Ω → A → ℝ) (α : A → ℝ) (πstar π' : Ω → A → ℝ) : Prop :=
  ∀ a ∈ supp α, ∀ p ∈ identifiedSet u α,
    ReceiverTakes u v π' p a a ∧ ReceiverTakes u v πstar p a a

end RobustObedientPersuasion.Saddle.Supplement


