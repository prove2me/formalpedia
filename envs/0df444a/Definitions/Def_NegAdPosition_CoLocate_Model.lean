-- Prove2me | Definitions.Def_NegAdPosition_CoLocate_Model
-- name    : NegAdPosition_CoLocate_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:35:39.038058+00:00
-- url     : https://prove2.me/theorems/c6d68a58-6390-4a8d-80f4-1cc68c51e3d0
-- title:
--   §2, pp. 8–13 — entry-positioning-advertising game: correlated attributes, truthful positive/negative ads, Bayes beliefs, two-location demand, PBE
-- statement:
--   This file sets up the incumbent–entrant game of Bostanci, Yildirim and Jerath, in which an entrant chooses where to position its product and then both firms choose between positive advertising, negative advertising and no advertising.
--
--   **Locations and consumers.** There are two locations $L$ and $R$, each holding a unit mass of consumers whose ideal product sits at that location. The incumbent (firm $1$) is at $L$; the entrant (firm $2$) chooses $x_2 \in \{L, R\}$. A consumer at $\chi$ buying product $i$ located at $x_i$ gets utility
--   $$U_{ij} = \gamma_j - |x_i - \chi| + A_i,$$
--   where the distance is $0$ at the own location and $\delta > 0$ at the other, and the reservation value $\gamma_j$ is uniform on $[\underline\gamma, \bar\gamma]$ with cdf $\Gamma(t) = \max\{0, \min\{1, (t - \underline\gamma)/(\bar\gamma - \underline\gamma)\}\}$. Not buying gives utility $0$.
--
--   **Attributes and prior.** Product $i$ has a positive attribute $P_i \in \{\Pi, 0\}$, present with probability $\sigma_\Pi$, and a negative attribute $N_i \in \{-\beta, 0\}$, present with probability $\sigma_\beta$; its vertical attribute is $A_i = P_i + N_i$. A type profile is $\theta = (P_1, P_2, N_1, N_2)$ (16 profiles). The pairs $(P_1, P_2)$ and $(N_1, N_2)$ are independent; within each pair the two indicators are Bernoulli with correlation $\rho$ when the products are co-located ($x_2 = L$) and $0$ when they are apart ($x_2 = R$). Explicitly, for success probability $\sigma$ and correlation $r$,
--   $$\Pr(1,1) = \sigma^2 + r\sigma(1-\sigma),\quad \Pr(1,0) = \Pr(0,1) = \sigma(1-\sigma)(1-r),\quad \Pr(0,0) = (1-\sigma)^2 + r\sigma(1-\sigma).$$
--
--   **Standing assumptions** (§2): $\delta, \Pi, \beta > 0$; $\sigma_\Pi, \sigma_\beta \in (0,1)$; $\rho \in (0,1)$; $\underline\gamma < \bar\gamma$; and the normalization $\sigma_\Pi \Pi = \sigma_\beta \beta$ (so $E[A_i] = 0$). **Assumption 1′** is $\underline\gamma < -\Pi$ and $\bar\gamma > \delta + \sigma_\Pi\Pi + (1-\sigma_\beta)\beta$. The parameter conditions of the proof of Proposition 2 are
--   $$\text{(A1a)}\ \beta > (1-\sigma_\Pi)\Pi + \delta,\qquad \text{(A1b)}\ \bar\gamma + \sigma_\beta\beta \ge (1-\sigma_\Pi)\Pi + \delta,\qquad \text{(A1c)}\ \Pi > (1-\rho)(1-\sigma_\beta)\beta,$$
--   and the corrected location condition
--   $$\text{(A1d′)}\ \ \sigma_\beta(1-\sigma_\beta)(1-\sigma_\Pi)(1-\rho)(1-\sigma_\Pi+\rho\sigma_\Pi)\beta + (1-\sigma_\Pi)\sigma_\Pi(1-\rho)\Pi - \tfrac{\delta}{2} \ \ge\ \sigma_\beta(1-\sigma_\beta)\beta + (1-\sigma_\Pi)\sigma_\Pi(1-\sigma_\beta)^2\Pi - (1-\sigma_\beta)\big(\sigma_\beta + (1-\sigma_\beta)\sigma_\Pi(1-\sigma_\Pi)\big)\delta.$$
--
--   **Advertising.** After nature draws $\theta$ (seen by the firms only), each firm $i$ chooses simultaneously $a_i \in \{P_i, N_{-i}, \varnothing\}$: advertise its own positive attribute, advertise the rival's negative attribute, or nothing. Advertising is truthful: $P_i$ is feasible only if $P_i = \Pi$, and $N_{-i}$ only if $N_{-i} = -\beta$. An advertising strategy gives each firm's ad as a function of $x_2$ and $\theta$.
--
--   **Beliefs and demand.** A belief system assigns to every location $x_2$ and observed outcome $(a_1, a_2)$ a function on type profiles. The Bayes posterior of a strategy profile at an outcome is the prior restricted to the profiles producing that outcome, divided by the outcome's prior mass. Given the expected attributes $e_i = E[A_i]$ under the consumers' belief, a consumer at $\chi$ compares $B_i = e_i - |x_i - \chi|$, buys iff $\gamma_j \ge -\max_i B_i$ (a mass $1 - \Gamma(-\max_i B_i)$), and buys the product with the larger $B_i$. Ties follow footnote 11: co-located products split the buyers equally; products located apart leave each location to the closer product. The price is normalized to $1$, so a firm's payoff is its total demand over both locations; the entrant's location payoff is its expected demand under the prior at that location.
--
--   **Perfect Bayesian equilibrium.** A profile (entrant location, advertising strategies, beliefs) is a PBE when: (1) every prescribed ad is truthful; (2) every belief is a probability mass function supported on type profiles consistent with the observed ads; (3) beliefs equal the Bayes posterior at every outcome of positive prior mass; (4) at both locations and for every $\theta$, each firm's prescribed ad is a best response among its feasible ads, given the rival's ad and the consumers' beliefs; (5) the entrant's location maximizes its expected demand. Sequential rationality of consumers is built into the demand.
--
--   **The profile of the proof.** Finally the file defines the strategies used in the proof of Proposition 2. Under co-location firm $i$ plays $P_i$ if $P_i = \Pi$, else $N_{-i}$ if $N_{-i} = -\beta$, else nothing. Apart, firm $i$ plays $P_i$ against a weak opponent ($N_i = 0$, $P_{-i} = 0$) when $P_i = \Pi$; otherwise $N_{-i}$ if available, else $P_i$ if available, else nothing. It also names $E[A_j \mid a_i = a, a_{-i} = b]$ and firm $i$'s demand $D_i(a, b)$ at location $x_2$ under the Bayes beliefs of this profile.
--
--   These objects carry every statement of the mission: Table 1's posteriors, Lemmas 1–5 and Proposition 2.
--
--   **Formalization Note.** Everything is finite and real-valued. Firms, locations and ads are small inductive types; a type profile is a pair of Boolean functions on the firms. The purchase rule counts consumers with $\gamma_j \ge -\max_i B_i$; a consumer exactly at zero utility is a null set. The Bayes posterior divides by the outcome's prior mass, so it is only meaningful (and is only used by the PBE definition) where that mass is positive. Off-path beliefs are constrained only to be probability mass functions consistent with the truthful ads. Two hypotheses differ from the page and are disclosed: the first clause of Assumption 1 is $\underline\gamma < -\Pi$ (printed $\underline\gamma < \Pi$; the paper's linear demand formulas need it), and $\rho < 1$ is added (so all advertising outcomes of the profile are on path). (A1d′) replaces the printed (A1d), whose $\Pi$-coefficient and $\beta$-factor carry slips.
-- source:
--   Bostanci, Yildirim & Jerath, Negative Advertising and Competitive Product Positioning, authors' manuscript (Nov. 2021; Management Science 2023, doi:10.1287/mnsc.2022.4439), pp. 8–13 (PDF 8–13), §2, footnote 11, Assumption 1 (corrected); p. A4 (PDF 47), strategies and conditions (A1a)–(A1d) of the proof of Proposition 2

import Mathlib

namespace NegAdPosition.CoLocate

/-- The two firms: the incumbent (firm 1, located at `L`) and the entrant (firm 2). -/
inductive Firm
  | inc
  | ent
  deriving DecidableEq

instance : Fintype Firm := ⟨{.inc, .ent}, fun x => by cases x <;> simp⟩

/-- The opponent `−i` of firm `i`. -/
def Firm.other : Firm → Firm
  | .inc => .ent
  | .ent => .inc

/-- The two locations `L` and `R`. -/
inductive Loc
  | L
  | R
  deriving DecidableEq

instance : Fintype Loc := ⟨{.L, .R}, fun x => by cases x <;> simp⟩

/-- Advertising choices of firm `i`: `pos` advertises `P_i = Π` (its own positive attribute),
`neg` advertises `N_{−i} = −β` (the rival's negative attribute), `none` is no advertising `∅`. -/
inductive Ad
  | pos
  | neg
  | none
  deriving DecidableEq

instance : Fintype Ad := ⟨{.pos, .neg, .none}, fun x => by cases x <;> simp⟩

/-- A type profile `θ = (P₁, P₂, N₁, N₂)`: `P i = true` means `P_i = Π` (positive attribute present),
`N i = true` means `N_i = −β` (negative attribute present). -/
structure Types where
  P : Firm → Bool
  N : Firm → Bool

/-- `Types` is equivalent to a pair of Boolean functions on the firms. -/
def Types.equivPair : Types ≃ (Firm → Bool) × (Firm → Bool) where
  toFun θ := (θ.P, θ.N)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype Types := Fintype.ofEquiv _ Types.equivPair.symm

/-- The primitives of the model (§2): `δ` distance, `Pi` = Π, `β`, `σP` = σ_Π, `σB` = σ_β,
`ρ` the correlation under co-location, and the support `[γlo, γhi]` of the reservation value. -/
structure Params where
  δ : ℝ
  Pi : ℝ
  β : ℝ
  σP : ℝ
  σB : ℝ
  ρ : ℝ
  γlo : ℝ
  γhi : ℝ

/-- Standing assumptions of §2 (pp. 8–10), with `ρ < 1` added. -/
def Params.Standing (P : Params) : Prop :=
  0 < P.δ ∧ 0 < P.Pi ∧ 0 < P.β ∧ 0 < P.σP ∧ P.σP < 1 ∧ 0 < P.σB ∧ P.σB < 1 ∧
    0 < P.ρ ∧ P.ρ < 1 ∧ P.γlo < P.γhi ∧ P.σP * P.Pi = P.σB * P.β

/-- Assumption 1′ (p. 13, first clause corrected from `γ < Π` to `γ < −Π`). -/
def Params.Assumption1 (P : Params) : Prop :=
  P.γlo < -P.Pi ∧ P.δ + P.σP * P.Pi + (1 - P.σB) * P.β < P.γhi

/-- (A1a), p. A4: `β > (1 − σ_Π)Π + δ`. -/
def Params.A1a (P : Params) : Prop := (1 - P.σP) * P.Pi + P.δ < P.β

/-- (A1b), p. A4: `γ̄ + σ_β β ≥ (1 − σ_Π)Π + δ`. -/
def Params.A1b (P : Params) : Prop := (1 - P.σP) * P.Pi + P.δ ≤ P.γhi + P.σB * P.β

/-- (A1c), p. A4: `Π > (1 − ρ)(1 − σ_β)β`. -/
def Params.A1c (P : Params) : Prop := (1 - P.ρ) * (1 - P.σB) * P.β < P.Pi

/-- (A1d′), the corrected form of (A1d), p. A4. -/
def Params.A1dCorr (P : Params) : Prop :=
  P.σB * (1 - P.σB) * P.β + (1 - P.σP) * P.σP * (1 - P.σB) ^ 2 * P.Pi
      - (1 - P.σB) * (P.σB + (1 - P.σB) * P.σP * (1 - P.σP)) * P.δ
    ≤ P.σB * (1 - P.σB) * (1 - P.σP) * (1 - P.ρ) * (1 - P.σP + P.ρ * P.σP) * P.β
      + (1 - P.σP) * P.σP * (1 - P.ρ) * P.Pi - P.δ / 2

/-- Joint law of two Bernoulli(σ) indicators with correlation `r`. -/
def pairPmf (σ r : ℝ) : Bool → Bool → ℝ
  | true, true => σ ^ 2 + r * σ * (1 - σ)
  | true, false => σ * (1 - σ) * (1 - r)
  | false, true => σ * (1 - σ) * (1 - r)
  | false, false => (1 - σ) ^ 2 + r * σ * (1 - σ)

/-- Correlation of the attributes: `ρ` under co-location (`x₂ = L`), `0` apart (`x₂ = R`). -/
def corrAt (P : Params) : Loc → ℝ
  | .L => P.ρ
  | .R => 0

/-- The common prior of the type profile when the entrant is at `x`: the `P`-pair and the
`N`-pair are independent, each pair correlated with coefficient `corrAt P x`. -/
def prior (P : Params) (x : Loc) (θ : Types) : ℝ :=
  pairPmf P.σP (corrAt P x) (θ.P .inc) (θ.P .ent) *
    pairPmf P.σB (corrAt P x) (θ.N .inc) (θ.N .ent)

/-- The vertical attribute `A_i = P_i + N_i` of product `i` at type profile `θ`. -/
def attr (P : Params) (θ : Types) (i : Firm) : ℝ :=
  (if θ.P i then P.Pi else 0) - (if θ.N i then P.β else 0)

/-- Truthful advertising: firm `i` may advertise `P_i` only if `P_i = Π`, and `N_{−i}` only if
`N_{−i} = −β`. -/
def Feasible (θ : Types) (i : Firm) : Ad → Prop
  | .pos => θ.P i = true
  | .neg => θ.N i.other = true
  | .none => True

/-- An advertising strategy profile: `s i x θ` is firm `i`'s ad when the entrant is at `x`. -/
abbrev AdStrategy := Firm → Loc → Types → Ad

/-- A belief system: `μ x a₁ a₂` is the consumers' belief over type profiles after observing the
location `x` and the ads `a₁` (incumbent), `a₂` (entrant). -/
abbrev Belief := Loc → Ad → Ad → Types → ℝ

/-- Prior probability of the advertising outcome `(a₁, a₂)` at location `x` under strategies `s`. -/
noncomputable def outcomeMass (P : Params) (s : AdStrategy) (x : Loc) (a1 a2 : Ad) : ℝ :=
  ∑ θ, if s .inc x θ = a1 ∧ s .ent x θ = a2 then prior P x θ else 0

/-- Bayes' rule: the posterior over type profiles given the outcome `(a₁, a₂)` at `x`.
(Only meaningful where `outcomeMass` is positive.) -/
noncomputable def bayes (P : Params) (s : AdStrategy) : Belief := fun x a1 a2 θ =>
  (if s .inc x θ = a1 ∧ s .ent x θ = a2 then prior P x θ else 0) / outcomeMass P s x a1 a2

/-- Expected attribute `E[A_i]` under a belief `μ` over type profiles. -/
noncomputable def expAttr (P : Params) (μ : Types → ℝ) (i : Firm) : ℝ :=
  ∑ θ, μ θ * attr P θ i

/-- The uniform cdf on `[γlo, γhi]`. -/
noncomputable def Γ (P : Params) (t : ℝ) : ℝ :=
  max 0 (min 1 ((t - P.γlo) / (P.γhi - P.γlo)))

/-- Location of firm `i` when the entrant is at `x₂`. -/
def position (x2 : Loc) : Firm → Loc
  | .inc => .L
  | .ent => x2

/-- Distance `|x_i − χ|` between firm `i`'s product and a consumer located at `χ`. -/
def dist (P : Params) (x2 : Loc) (i : Firm) (χ : Loc) : ℝ :=
  if position x2 i = χ then 0 else P.δ

/-- Demand of firm `i` among the unit mass of consumers located at `χ`, when the expected
attributes are `e`. Consumers pick the product maximising `e j − dist`, buy iff their reservation
value is at least minus that maximum, and break ties as in footnote 11. -/
noncomputable def locDemand (P : Params) (x2 : Loc) (e : Firm → ℝ) (i : Firm) (χ : Loc) : ℝ :=
  let B := fun j => e j - dist P x2 j χ
  let buyers := 1 - Γ P (-(max (B .inc) (B .ent)))
  let share : ℝ :=
    if B i.other < B i then 1
    else if B i < B i.other then 0
    else if x2 = .L then 1 / 2
    else if position x2 i = χ then 1 else 0
  share * buyers

/-- Total demand (= payoff, the price being normalised to 1) of firm `i`. -/
noncomputable def demand (P : Params) (x2 : Loc) (e : Firm → ℝ) (i : Firm) : ℝ :=
  locDemand P x2 e i .L + locDemand P x2 e i .R

/-- Firm `i`'s demand after the outcome `(a₁, a₂)` at `x` when consumers hold beliefs `μ`. -/
noncomputable def outcomeDemand (P : Params) (μ : Belief) (x : Loc) (a1 a2 : Ad) (i : Firm) : ℝ :=
  demand P x (fun j => expAttr P (μ x a1 a2) j) i

/-- The outcome in `(a₁, a₂)` order when firm `i` plays `a` and its opponent plays `b`. -/
def outcomeOf (i : Firm) (a b : Ad) : Ad × Ad :=
  match i with
  | .inc => (a, b)
  | .ent => (b, a)

/-- A candidate assessment: entrant location, advertising strategies, consumer beliefs. -/
structure Profile where
  x2 : Loc
  ad : AdStrategy
  belief : Belief

/-- The entrant's expected demand from locating at `x`, over the prior at `x`. -/
noncomputable def expEntrantDemand (P : Params) (s : AdStrategy) (μ : Belief) (x : Loc) : ℝ :=
  ∑ θ, prior P x θ * outcomeDemand P μ x (s .inc x θ) (s .ent x θ) .ent

/-- Perfect Bayesian equilibrium (§2.2, pp. 12–13). Consumer sequential rationality is built into
`locDemand`. -/
def IsPBE (P : Params) (σ : Profile) : Prop :=
  (∀ i x θ, Feasible θ i (σ.ad i x θ)) ∧
  (∀ x a1 a2, (∀ θ, 0 ≤ σ.belief x a1 a2 θ) ∧ ∑ θ, σ.belief x a1 a2 θ = 1 ∧
      ∀ θ, σ.belief x a1 a2 θ ≠ 0 → Feasible θ .inc a1 ∧ Feasible θ .ent a2) ∧
  (∀ x a1 a2, 0 < outcomeMass P σ.ad x a1 a2 →
      ∀ θ, σ.belief x a1 a2 θ = bayes P σ.ad x a1 a2 θ) ∧
  (∀ x θ i a, Feasible θ i a →
      outcomeDemand P σ.belief x (outcomeOf i a (σ.ad i.other x θ)).1
          (outcomeOf i a (σ.ad i.other x θ)).2 i
        ≤ outcomeDemand P σ.belief x (σ.ad .inc x θ) (σ.ad .ent x θ) i) ∧
  (∀ x, expEntrantDemand P σ.ad σ.belief x ≤ expEntrantDemand P σ.ad σ.belief σ.x2)

/-- The advertising strategies of the proof of Proposition 2 (p. A4, item 2). -/
def copnAd : AdStrategy := fun i x θ =>
  match x with
  | .R =>
    if θ.N i = false ∧ θ.P i.other = false ∧ θ.P i = true then .pos
    else if θ.N i.other = true then .neg
    else if θ.P i = true then .pos
    else .none
  | .L =>
    if θ.P i = true then .pos
    else if θ.N i.other = true then .neg
    else .none

/-- Posterior expected attribute `E[A_j | a_i = a, a_{−i} = b]` at location `x` under the Bayes
beliefs of `copnAd`. -/
noncomputable def copnPost (P : Params) (x : Loc) (i : Firm) (a b : Ad) (j : Firm) : ℝ :=
  expAttr P (bayes P copnAd x (outcomeOf i a b).1 (outcomeOf i a b).2) j

/-- Firm `i`'s demand `D_i(a_i = a, a_{−i} = b)` at location `x` when consumers hold the Bayes
beliefs of `copnAd`. -/
noncomputable def copnDemand (P : Params) (x : Loc) (i : Firm) (a b : Ad) : ℝ :=
  outcomeDemand P (bayes P copnAd) x (outcomeOf i a b).1 (outcomeOf i a b).2 i

end NegAdPosition.CoLocate


