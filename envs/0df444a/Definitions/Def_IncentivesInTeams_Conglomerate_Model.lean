-- Prove2me | Definitions.Def_IncentivesInTeams_Conglomerate_Model
-- name    : IncentivesInTeams_Conglomerate_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T21:21:45.792623+00:00
-- url     : https://prove2.me/theorems/6ae99125-799c-4109-a422-0609388824ff
-- title:
--   Conglomerate organization model: independent finite component states, observation/message/decision strategies, payoffs, Assumption A, optimal incentive structures, the class 𝒥 and $W^{II}$
-- statement:
--   This file sets up the conglomerate organization of T. Groves, *Incentives in Teams* (1973), and every object Theorem 1 of that paper speaks about.
--
--   **Components and states.** A conglomerate has a head (component $0$) and subunits $i \in \iota$ (the paper's $1,\dots,n$), where $\iota$ is a finite index type. Component $k$ has a finite state space $S_k$ carrying weights $P_k$; `WeightsOK` requires every $P_k$ to be nonnegative with total mass $1$. A state of the environment is $s = (s_0, (s_i)_{i\in\iota})$, distributed according to the product law (Condition S.2)
--   $$P(s) = P_0(s_0)\prod_{i\in\iota} P_i(s_i), \qquad E[X] = \sum_s P(s)\,X(s).$$
--
--   **Strategies (Condition S.3).** A subunit strategy $\beta_i = (\zeta_i, \gamma_i, \delta_i)$ consists of an observation strategy $\zeta_i : S_i \to Z_i$, a message strategy $\gamma_i : Y_i \to M_i$ and a decision strategy $\delta_i : Y_i \to D_i$ on the information set $Y_i = Z_i \times M^0_i$. A head strategy $\beta_0 = (\zeta_0, \gamma_0, \delta_0)$ consists of $\zeta_0 : S_0 \to Z_0$, messages $\gamma_0^i : Z_0 \to M^0_i$ to each subunit, and $\delta_0 : Y_0 \to D_0$ on $Y_0 = Z_0 \times \prod_i M_i$. A joint strategy $\beta$ is a head strategy together with one strategy per subunit; $\beta \in B$ means $\beta_0 \in B_0$ and $\beta_i \in B_i$ for all $i$. For a subunit strategy $b$, $\beta/b$ replaces $\beta_i$ by $b$.
--
--   **Information (3.1).** Messages are exchanged once: the head sends $\gamma_0^i(\zeta_0(s_0))$ to subunit $i$, the subunits answer, and decisions are taken:
--   $$y_i(s) = [\zeta_i(s_i), \gamma_0^i(\zeta_0(s_0))], \qquad y_0(s) = [\zeta_0(s_0), \{\gamma_i(y_i(s))\}_{i}].$$
--
--   **Payoffs (Condition S.4).** With components $v_0[d_0, s_0]$ and $v_i[d_i, d_0; s_i]$,
--   $$\omega_0(\beta, s) = \sum_i v_i[\delta_i(y_i(s)), \delta_0(y_0(s)); s_i] + v_0[\delta_0(y_0(s)), s_0], \qquad \bar\omega_0(\beta) = E[\omega_0(\beta,\cdot)].$$
--
--   **Equivalence and Assumption A.** Two strategies $b_1, b_2$ of subunit $i$ are equivalent if $\bar\omega_0(\beta/b_1) = \bar\omega_0(\beta/b_2)$ for all $\beta \in B$ (footnote 5). $\beta^*$ satisfies Assumption A if $\beta^* \in B$, $\bar\omega_0(\beta^*) \ge \bar\omega_0(\beta)$ for all $\beta \in B$ (2.3a), and $\bar\omega_0(\beta^*) > \bar\omega_0(\beta^*/\beta_i)$ for every $i$ and every $\beta_i \in B_i$ not equivalent to $\beta_i^*$ (2.3b).
--
--   **Incentive structures.** An incentive structure $W = \{\omega_i\}$ assigns each subunit a payoff $\omega_i(\beta, s)$. It is *optimal* for $\beta^*$ (2.6 with footnote 6) if for every $i$ and every $\beta_i \in B_i$, $\bar\omega_i(\beta^*/\beta_i) \le \bar\omega_i(\beta^*)$, with strict inequality whenever $\beta_i$ is not equivalent to $\beta_i^*$. The class $\mathscr{J}$ of (3.2) consists of the structures $\omega_i(\beta,s) = v_i[\delta_i(y_i(s)), \delta_0(y_0(s)); s_i] + C_i(y_0(s))$ with $C_i : Y_0 \to \mathbb{R}$.
--
--   **The compensation $C_i^{II}$ (3.3) and $W^{II}$ (3.5).** For $y_0 = (z_0, m)$ and the joint strategy $\beta^*$, let
--   $$h_j(y_0) = E\big[v_j[\delta_j^*(\zeta_j^*(t), \gamma_0^{j*}(z_0)), \delta_0^*(y_0); t] \,\big|\, \gamma_j^*(\zeta_j^*(t), \gamma_0^{j*}(z_0)) = m_j\big], \qquad h_0(y_0) = E\big[v_0[\delta_0^*(y_0), t] \,\big|\, \zeta_0^*(t) = z_0\big],$$
--   elementary conditional averages over the component state $t$ of subunit $j$ (resp. the head) under $P_j$ (resp. $P_0$). Then
--   $$C_i^{II}(y_0) = h_0(y_0) + \sum_{j \ne i} h_j(y_0) - A_i, \qquad \omega_i^{II}(\beta, s) = v_i[\delta_i(y_i(s)), \delta_0(y_0(s)); s_i] + C_i^{II}(y_0(s)).$$
--   The file also defines the literal conditional expectations of (3.3), $E[v_j[\delta_j^*(y_j^*(s)), \delta_0^*(y_0^*(s)); s_j] \mid y_0^*(s) = y_0]$ and its analogue for $v_0$, as elementary conditional averages under the product law.
--
--   These objects are shared by every statement of the mission: Theorem 1 states that $W^{II}$ lies in $\mathscr{J}$ and is optimal.
--
--   **Formalization Note.** (1) The paper allows general probability spaces; here every component state space is finite, which makes footnote 4's integrability automatic and gives the point value of a conditional expectation an elementary meaning. (2) As printed, (3.1) is circular ($y_i$ uses $\gamma_0^i(y_0)$ and $y_0$ uses $\gamma_i(y_i)$). It is resolved by the paper's own protocol of §4.A, p. 627: "Based on the supply observation, the resource manager sends messages to the enterprise managers who each then return some message to the resource manager. At the conclusion of this single exchange of messages, the managers make their decisions." The head's message is therefore a function of his observation. (3) Observation, message and decision spaces are fixed types per component. (4) $C_i^{II}$ is the factorized form of (3.3): each subunit's factor is conditioned on its own message only, and the head's factor on his observation. By independence (S.2) it coincides with the literal conditional expectation whenever the conditioning event has positive probability (a separate theorem of the mission); unlike the literal quotient, it does not take the division-by-zero value $0$ on the null events reached when a subunit sends a message $\gamma_i^*$ never sends. (5) The sum $\sum_{j \ne i}$ in (3.3) runs over $I = \{0,\dots,n\}$ and so includes the head's component $h_0$. (6) `condAvg` divides by the event's weight and returns $0$ on an event of weight $0$; decidability of events uses classical logic. (7) Condition S.5 ("accrues directly to the $i$th subunit") is interpretive; it is encoded by the shape $v_i + C_i$ of $\mathscr{J}$ and $W^{II}$.
-- source:
--   Groves, Incentives in Teams, Econometrica 41(4), 1973, pp. 619–620, §2.A ((2.2), Assumption A (2.3a)–(2.3b), (2.6), footnotes 4–6); p. 623, §3.A (Conditions S.1–S.5, (3.1)); pp. 624–625, §3.B ((3.2)–(3.5)); p. 627, §4.A (single exchange of messages)

import Mathlib

namespace IncentivesInTeams.Conglomerate

open Finset

/-! # The conglomerate model of Groves, *Incentives in Teams* (Econometrica 1973), §2.A and §3.A–B

Subunits `1, …, n` are the elements of a finite index type `ι`; the head (`i = 0`) is a separate
component with its own types. Every component has a finite state space with probability weights,
and the joint law of the state is the product law (Condition S.2). -/

/-- Probability weights on a finite set: nonnegative and summing to one. -/
def IsProbWeights {α : Type*} [Fintype α] (w : α → ℝ) : Prop :=
  (∀ a, 0 ≤ w a) ∧ ∑ a, w a = 1

open Classical in
/-- The elementary conditional average of `X` given the event `E` under the weights `w`:
`(∑_{a ∈ E} w a * X a) / (∑_{a ∈ E} w a)`. On an event of weight `0` its value is `0`
(real division by zero). -/
noncomputable def condAvg {α : Type*} [Fintype α] (w : α → ℝ) (E : Set α) (X : α → ℝ) : ℝ :=
  (∑ a ∈ univ.filter (fun a => a ∈ E), w a * X a) / (∑ a ∈ univ.filter (fun a => a ∈ E), w a)

/-- A strategy `β_i = (ζ_i, γ_i, δ_i)` of subunit `i` (Condition S.3): an observation strategy on
the component state space `Sᵢ`, and a message and a decision strategy on the information set
`Yᵢ = Zᵢ × M₀ᵢ` (own observation, message received from the head). -/
structure SubStrategy (Sᵢ Zᵢ M₀ᵢ Mᵢ Dᵢ : Type*) where
  /-- observation strategy `ζ_i : S_i → Z_i` -/
  obs : Sᵢ → Zᵢ
  /-- message strategy `γ_i : Y_i → M_i` (message to the head) -/
  msg : Zᵢ × M₀ᵢ → Mᵢ
  /-- decision strategy `δ_i : Y_i → D_i` -/
  dec : Zᵢ × M₀ᵢ → Dᵢ

/-- A strategy `β_0 = (ζ_0, γ_0, δ_0)` of the head (Condition S.3): an observation strategy on
`S₀`, messages `γ_0^i` to each subunit `i` computed from the head's observation (one exchange of
messages, §4.A), and a decision strategy on the head's information set
`Y₀ = Z₀ × ∏ᵢ Mᵢ` (own observation, the subunits' messages). -/
structure HeadStrategy {ι : Type*} (S₀ Z₀ : Type*) (M₀ M : ι → Type*) (D₀ : Type*) where
  /-- observation strategy `ζ_0 : S_0 → Z_0` -/
  obs : S₀ → Z₀
  /-- message strategies `γ_0^i`, the message sent to subunit `i` -/
  msg : ∀ i, Z₀ → M₀ i
  /-- decision strategy `δ_0 : Y_0 → D_0` -/
  dec : Z₀ × (∀ i, M i) → D₀

/-- A joint strategy `β = (β_0, β_1, …, β_n)`. -/
structure JointStrategy {ι : Type*} (S₀ : Type*) (S : ι → Type*) (Z₀ : Type*) (Z M₀ M : ι → Type*)
    (D₀ : Type*) (D : ι → Type*) where
  /-- the head's strategy `β_0` -/
  head : HeadStrategy S₀ Z₀ M₀ M D₀
  /-- the subunits' strategies `β_i` -/
  sub : ∀ i, SubStrategy (S i) (Z i) (M₀ i) (M i) (D i)

/-- An organization model `T = [I, (S, 𝒮, P), {B_i}, ω_0]` with the conglomerate specification
S.1–S.4: component probability weights `P₀`, `Pᵢ`, strategy sets `B₀`, `Bᵢ`, and payoff components
`v₀[d₀, s₀]`, `vᵢ[dᵢ, d₀; sᵢ]`. -/
structure Model {ι : Type*} (S₀ : Type*) (S : ι → Type*) (Z₀ : Type*) (Z M₀ M : ι → Type*)
    (D₀ : Type*) (D : ι → Type*) where
  /-- probability weights of the head's component state `s_0` -/
  P₀ : S₀ → ℝ
  /-- probability weights of subunit `i`'s component state `s_i` -/
  P : ∀ i, S i → ℝ
  /-- the head's strategy set `B_0` -/
  B₀ : Set (HeadStrategy S₀ Z₀ M₀ M D₀)
  /-- subunit `i`'s strategy set `B_i` -/
  B : ∀ i, Set (SubStrategy (S i) (Z i) (M₀ i) (M i) (D i))
  /-- the head's payoff component `v_0[d_0, s_0]` -/
  v₀ : D₀ → S₀ → ℝ
  /-- subunit `i`'s payoff component `v_i[d_i, d_0; s_i]` -/
  v : ∀ i, D i → D₀ → S i → ℝ

/-- An incentive structure `W = {ω_i}`: a payoff function `ω_i(β, s)` for every subunit. -/
abbrev IncentiveStructure {ι : Type*} (S₀ : Type*) (S : ι → Type*) (Z₀ : Type*) (Z M₀ M : ι → Type*)
    (D₀ : Type*) (D : ι → Type*) :=
  ι → JointStrategy S₀ S Z₀ Z M₀ M D₀ D → (S₀ × ∀ i, S i) → ℝ

variable {ι : Type*} {S₀ : Type*} {S : ι → Type*} {Z₀ : Type*} {Z M₀ M : ι → Type*}
  {D₀ : Type*} {D : ι → Type*}

namespace JointStrategy

/-- Subunit `i`'s information `y_i(s) = [ζ_i(s_i), γ_0^i(ζ_0(s_0))]` (3.1), one exchange of
messages. -/
def subInfo (β : JointStrategy S₀ S Z₀ Z M₀ M D₀ D) (s : S₀ × ∀ i, S i) (i : ι) : Z i × M₀ i :=
  ((β.sub i).obs (s.2 i), β.head.msg i (β.head.obs s.1))

/-- The head's information `y_0(s) = [ζ_0(s_0), {γ_i(y_i(s))}_{i=1}^n]` (3.1). -/
def headInfo (β : JointStrategy S₀ S Z₀ Z M₀ M D₀ D) (s : S₀ × ∀ i, S i) : Z₀ × (∀ i, M i) :=
  (β.head.obs s.1, fun i => (β.sub i).msg (β.subInfo s i))

/-- `β/b`: the joint strategy `β` with subunit `i`'s strategy replaced by `b`. -/
def update [DecidableEq ι] (β : JointStrategy S₀ S Z₀ Z M₀ M D₀ D) (i : ι)
    (b : SubStrategy (S i) (Z i) (M₀ i) (M i) (D i)) : JointStrategy S₀ S Z₀ Z M₀ M D₀ D :=
  ⟨β.head, Function.update β.sub i b⟩

end JointStrategy

namespace Model

variable (T : Model S₀ S Z₀ Z M₀ M D₀ D)

/-- All component weights are probability weights. -/
def WeightsOK [Fintype S₀] [∀ i, Fintype (S i)] : Prop :=
  IsProbWeights T.P₀ ∧ ∀ i, IsProbWeights (T.P i)

/-- The product law of the state (Condition S.2): `P(s) = P₀(s₀) · ∏ᵢ Pᵢ(sᵢ)`. -/
def prob [Fintype ι] (s : S₀ × ∀ i, S i) : ℝ :=
  T.P₀ s.1 * ∏ i, T.P i (s.2 i)

/-- Expectation of a function of the state under the product law. -/
def expect [Fintype ι] [DecidableEq ι] [Fintype S₀] [∀ i, Fintype (S i)]
    (X : (S₀ × ∀ i, S i) → ℝ) : ℝ :=
  ∑ s, T.prob s * X s

/-- `β ∈ B`: every component of the joint strategy lies in its strategy set. -/
def Mem (β : JointStrategy S₀ S Z₀ Z M₀ M D₀ D) : Prop :=
  β.head ∈ T.B₀ ∧ ∀ i, β.sub i ∈ T.B i

/-- Subunit `i`'s payoff component `v_i[δ_i(y_i(s)), δ_0(y_0(s)); s_i]` under `β`. -/
def subPayoff (β : JointStrategy S₀ S Z₀ Z M₀ M D₀ D) (i : ι) (s : S₀ × ∀ i, S i) : ℝ :=
  T.v i ((β.sub i).dec (β.subInfo s i)) (β.head.dec (β.headInfo s)) (s.2 i)

/-- The head's payoff component `v_0[δ_0(y_0(s)), s_0]` under `β`. -/
def headPayoff (β : JointStrategy S₀ S Z₀ Z M₀ M D₀ D) (s : S₀ × ∀ i, S i) : ℝ :=
  T.v₀ (β.head.dec (β.headInfo s)) s.1

/-- The organization payoff `ω_0(β, s) = ∑ᵢ vᵢ[…] + v₀[…]` (Condition S.4). -/
def orgPayoff [Fintype ι] (β : JointStrategy S₀ S Z₀ Z M₀ M D₀ D) (s : S₀ × ∀ i, S i) : ℝ :=
  ∑ i, T.subPayoff β i s + T.headPayoff β s

/-- The expected organization payoff `ω̄_0(β)` (2.2). -/
def expOrgPayoff [Fintype ι] [DecidableEq ι] [Fintype S₀] [∀ i, Fintype (S i)]
    (β : JointStrategy S₀ S Z₀ Z M₀ M D₀ D) : ℝ :=
  T.expect (T.orgPayoff β)

/-- Footnote 5: `b₁` and `b₂` are equivalent strategies of subunit `i` iff
`ω̄_0(β/b₁) = ω̄_0(β/b₂)` for all `β ∈ B`. -/
def Equiv [Fintype ι] [DecidableEq ι] [Fintype S₀] [∀ i, Fintype (S i)] (i : ι)
    (b₁ b₂ : SubStrategy (S i) (Z i) (M₀ i) (M i) (D i)) : Prop :=
  ∀ β, T.Mem β → T.expOrgPayoff (β.update i b₁) = T.expOrgPayoff (β.update i b₂)

/-- Assumption A (2.3a)–(2.3b), with `β_i ≠ β_i*` read up to equivalence (footnote 5). -/
def AssumptionA [Fintype ι] [DecidableEq ι] [Fintype S₀] [∀ i, Fintype (S i)]
    (βs : JointStrategy S₀ S Z₀ Z M₀ M D₀ D) : Prop :=
  T.Mem βs ∧
  (∀ β, T.Mem β → T.expOrgPayoff β ≤ T.expOrgPayoff βs) ∧
  (∀ i, ∀ b ∈ T.B i, ¬ T.Equiv i b (βs.sub i) →
    T.expOrgPayoff (βs.update i b) < T.expOrgPayoff βs)

/-- (2.6) with footnote 6: `W` is optimal for `β*` iff, for every subunit `i`, `β_i*` maximizes
`ω̄_i(β*/β_i)` over `β_i ∈ B_i`, uniquely up to equivalence. -/
def IsOptimal [Fintype ι] [DecidableEq ι] [Fintype S₀] [∀ i, Fintype (S i)]
    (W : IncentiveStructure S₀ S Z₀ Z M₀ M D₀ D) (βs : JointStrategy S₀ S Z₀ Z M₀ M D₀ D) :
    Prop :=
  ∀ i, ∀ b ∈ T.B i,
    T.expect (W i (βs.update i b)) ≤ T.expect (W i βs) ∧
    (¬ T.Equiv i b (βs.sub i) → T.expect (W i (βs.update i b)) < T.expect (W i βs))

/-- The class `𝒥` of (3.2): incentive structures `ω_i(β, s) = v_i[…] + C_i(y_0(s))` with
`C_i : Y₀ → ℝ`. -/
def InClassJ (W : IncentiveStructure S₀ S Z₀ Z M₀ M D₀ D) : Prop :=
  ∃ C : ι → Z₀ × (∀ i, M i) → ℝ, ∀ i β s, W i β s = T.subPayoff β i s + C i (β.headInfo s)

/-- Factor `j` of the head's conditional expectation under `β*` at `y_0 = (z₀, m)`: the average of
`v_j[δ_j*(ζ_j*(t), γ_0^{j*}(z₀)), δ_0*(y_0); t]` over the states `t` of component `j` whose
message under `β*` is `m_j`. -/
noncomputable def subFactor [Fintype ι] [∀ i, Fintype (S i)]
    (βs : JointStrategy S₀ S Z₀ Z M₀ M D₀ D) (j : ι) (y₀ : Z₀ × (∀ i, M i)) : ℝ :=
  condAvg (T.P j)
    {t | (βs.sub j).msg ((βs.sub j).obs t, βs.head.msg j y₀.1) = y₀.2 j}
    (fun t => T.v j ((βs.sub j).dec ((βs.sub j).obs t, βs.head.msg j y₀.1)) (βs.head.dec y₀) t)

/-- The head's own factor under `β*` at `y_0 = (z₀, m)`: the average of `v_0[δ_0*(y_0), t]` over
the states `t` of component `0` with `ζ_0*(t) = z₀`. -/
noncomputable def headFactor [Fintype S₀] (βs : JointStrategy S₀ S Z₀ Z M₀ M D₀ D)
    (y₀ : Z₀ × (∀ i, M i)) : ℝ :=
  condAvg T.P₀ {t | βs.head.obs t = y₀.1} (fun t => T.v₀ (βs.head.dec y₀) t)

/-- The compensation function `C_i^II` of (3.3), in factorized form: the head's conditional
expectation, under `β*`, of every payoff component other than subunit `i`'s (the head's own
component included), minus the constant `A_i`. -/
noncomputable def CII [Fintype ι] [DecidableEq ι] [Fintype S₀] [∀ i, Fintype (S i)]
    (βs : JointStrategy S₀ S Z₀ Z M₀ M D₀ D) (A : ι → ℝ) (i : ι) (y₀ : Z₀ × (∀ i, M i)) : ℝ :=
  T.headFactor βs y₀ + ∑ j ∈ univ.erase i, T.subFactor βs j y₀ - A i

/-- The incentive structure `W^II` of (3.5): `ω_i^II(β, s) = v_i[…] + C_i^II(y_0(s))`. -/
noncomputable def WII [Fintype ι] [DecidableEq ι] [Fintype S₀] [∀ i, Fintype (S i)]
    (βs : JointStrategy S₀ S Z₀ Z M₀ M D₀ D) (A : ι → ℝ) :
    IncentiveStructure S₀ S Z₀ Z M₀ M D₀ D :=
  fun i β s => T.subPayoff β i s + T.CII βs A i (β.headInfo s)

/-- The literal conditional expectation of (3.3) for subunit `j`:
`E[v_j[δ_j*(y_j*(s)), δ_0*(y_0*(s)); s_j] | y_0*(s) = y_0]`, as an elementary conditional average
under the product law (value `0` on a null event). -/
noncomputable def literalSubCondExp [Fintype ι] [DecidableEq ι] [Fintype S₀]
    [∀ i, Fintype (S i)] (βs : JointStrategy S₀ S Z₀ Z M₀ M D₀ D) (j : ι)
    (y₀ : Z₀ × (∀ i, M i)) : ℝ :=
  condAvg T.prob {s | βs.headInfo s = y₀} (T.subPayoff βs j)

/-- The literal conditional expectation of (3.3) for the head's component:
`E[v_0[δ_0*(y_0*(s)), s_0] | y_0*(s) = y_0]` (value `0` on a null event). -/
noncomputable def literalHeadCondExp [Fintype ι] [DecidableEq ι] [Fintype S₀]
    [∀ i, Fintype (S i)] (βs : JointStrategy S₀ S Z₀ Z M₀ M D₀ D) (y₀ : Z₀ × (∀ i, M i)) : ℝ :=
  condAvg T.prob {s | βs.headInfo s = y₀} (T.headPayoff βs)

end Model

end IncentivesInTeams.Conglomerate


