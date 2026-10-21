-- Prove2me | Definitions.Def_CommonAgencyVCG_Algorithmic_Setting
-- name    : CommonAgencyVCG_Algorithmic_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T00:22:14.760239+00:00
-- url     : https://prove2.me/theorems/30666cb9-b907-4e58-9460-3169dec99158
-- title:
--   §2–§3.2, pp. 7–11 — common agency setting, declared welfare, a*(b), agent best response, IIVCG, LL, IR, truthfulness
-- statement:
--   This file fixes the common agency model of Alon, Lavi, Shamash and Talgam-Cohen (§2) and the contract properties studied in the paper.
--
--   A **common agency setting** consists of a finite set $\mathcal A$ of actions available to a single agent, a cost $\psi(a)$ for each action, a finite set $\mathcal O$ of outcomes, for each action $a$ a probability distribution $F_{|a}$ over outcomes, and $n$ principals, principal $\ell$ having a valuation domain $\mathcal V^\ell \subseteq \mathbb R^{\mathcal O}$. The standing assumptions of the paper are imposed: costs are pairwise distinct, each $F_{|a}$ is a probability vector, and each domain $\mathcal V^\ell$ is nonempty, convex and consists of non-negative valuations. A bid profile $b = (b^1,\dots,b^n)$ is in the domain $\mathcal V$ when $b^\ell \in \mathcal V^\ell$ for every $\ell$; $(b^{-\ell}, w)$ denotes $b$ with principal $\ell$'s bid replaced by $w$.
--
--   Write $\mathbb E_{o\sim F_{|a}}[w(o)] = \sum_o F_{|a}(o)\,w(o)$. The **declared welfare** of action $a$ at profile $b$ is
--   $$\mathrm{Wel}^a(b) = \sum_{\ell\in[n]} \mathbb E_{o\sim F_{|a}}[b^\ell(o)] - \psi(a),$$
--   and $a^*(b)$ is the welfare-maximizing action of highest cost (footnotes 7 and 9).
--
--   A **contract** $t = (t^1,\dots,t^n)$ assigns to each bid profile $b$ and outcome $o$ a payment $t^\ell(b,o)$ from each principal. The agent's utility from action $a$ is $\sum_\ell \mathbb E_{o\sim F_{|a}}[t^\ell(b,o)] - \psi(a)$; the agent's choice $x^*(b)$ maximizes it, and among utility maximizers the agent takes the one of highest declared welfare and, among those, of highest cost (footnote 7).
--
--   1. **IIVCG** (Definition 2): for every $b \in \mathcal V$ the agent's choice is $a^*(b)$, and there are functions $h^\ell$ of $b^{-\ell}$ alone with $\mathbb E_{o\sim F_{|a^*(b)}}[t^\ell(b,o)] = h^\ell(b^{-\ell}) - \mathrm{Wel}^{a^*(b)}(b^{-\ell},\mathbf 0)$.
--   2. **Limited liability (LL)** (Definition 1): $t^\ell(b,o) \ge 0$ for all $\ell$, $b\in\mathcal V$, $o$.
--   3. **Individual rationality (IR)**: $\mathbb E_{o\sim F_{|x^*(b^{-\ell},v^\ell)}}[v^\ell(o) - t^\ell((b^{-\ell},v^\ell),o)] \ge 0$ for all $\ell$, $b^{-\ell}$, $v^\ell\in\mathcal V^\ell$.
--   4. **Truthfulness**: bidding one's true valuation maximizes each principal's expected utility, whatever the others bid.
--
--   These are the objects about which every statement of the mission is made.
--
--   **Formalization Note** Principals are `Fin n`; a bid profile is `Fin n → O → ℝ` and $(b^{-\ell},w)$ is `Function.update b ℓ w`. A contract is `t b ℓ o`. The assumption $n \ge 1$ is added to the standing assumptions (with no principals the weights $x^b_\ell$ of Claim 3 cannot sum to $1$). Convexity of the domains is kept as on p. 7 although the results of this mission do not use it; the polynomial description of the domains serves only complexity claims and is dropped. The paper's $x^*(b) = a^*(b)$ is read with the canonical $a^*(b)$ (welfare-maximal, then cost-maximal), the reading under which footnote 9 says $a^*(b)$ is uniquely defined. `agentChoice` is a predicate; under distinct costs it holds for exactly one action. $h^\ell : \mathcal V^{-\ell}\to\mathbb R$ is a function of the whole profile that ignores coordinate $\ell$.
-- source:
--   Alon, Lavi, Shamash, Talgam-Cohen, Incomplete Information VCG Contracts for Common Agency, arXiv:2105.14998v1, pp. 7–11, §2 (setting, contracts, the game, footnotes 7 and 9, truthfulness, IR, Definition 1, welfare), §3.2 Definition 2

import Mathlib

namespace CommonAgencyVCG.Algorithmic

/-- A common agency setting `(A, ψ, O, V, F)` with `n` principals (§2, p. 7): `psi a` is the cost
ψ(a) of action `a`, `F a o` is the probability `p_{o∼F|a}(o)` of outcome `o` under action `a`, and
`V ℓ` is principal `ℓ`'s valuation domain `V^ℓ ⊆ ℝ^O`. -/
structure Setting (n : ℕ) (A O : Type) where
  /-- action costs ψ -/
  psi : A → ℝ
  /-- outcome distributions: `F a o` = p_{o∼F|a}(o) -/
  F : A → O → ℝ
  /-- valuation domains V^ℓ -/
  V : Fin n → Set (O → ℝ)

variable {n : ℕ} {A O : Type} [Fintype A] [Fintype O]

/-- The standing assumptions of §2, p. 7: at least one principal (added), pairwise distinct costs,
each `F|a` a probability vector, each domain nonempty, convex and made of non-negative valuations. -/
def Setting.Standing (S : Setting n A O) : Prop :=
  0 < n ∧ Function.Injective S.psi ∧ (∀ a o, 0 ≤ S.F a o) ∧ (∀ a, ∑ o, S.F a o = 1) ∧
    (∀ ℓ, (S.V ℓ).Nonempty) ∧ (∀ ℓ, ∀ v ∈ S.V ℓ, ∀ o, 0 ≤ v o) ∧ (∀ ℓ, Convex ℝ (S.V ℓ))

/-- A bid profile `b = (b^1, …, b^n)` lies in `V = V^1 × ⋯ × V^n`. -/
def InDom (S : Setting n A O) (b : Fin n → O → ℝ) : Prop := ∀ ℓ, b ℓ ∈ S.V ℓ

/-- Expectation `E_{o∼F|a}[w(o)] = ∑_o F|a(o) w(o)`. -/
def E (S : Setting n A O) (a : A) (w : O → ℝ) : ℝ := ∑ o, S.F a o * w o

/-- Declared welfare `Wel^a(b) = ∑_ℓ E_{o∼F|a}[b^ℓ(o)] − ψ(a)` (p. 9). -/
def Wel (S : Setting n A O) (a : A) (b : Fin n → O → ℝ) : ℝ := ∑ ℓ, E S a (b ℓ) - S.psi a

/-- `a` is the canonical welfare maximizer `a*(b)`: it maximizes `Wel^·(b)`, and among welfare
maximizers it has the highest cost (footnotes 7 and 9, pp. 8–9). -/
def IsAStar (S : Setting n A O) (b : Fin n → O → ℝ) (a : A) : Prop :=
  (∀ a', Wel S a' b ≤ Wel S a b) ∧ (∀ a', Wel S a' b = Wel S a b → S.psi a' ≤ S.psi a)

/-- The canonical welfare-maximizing action `a*(b)`. -/
noncomputable def aStar [Nonempty A] (S : Setting n A O) (b : Fin n → O → ℝ) : A :=
  Classical.epsilon (IsAStar S b)

/-- A contract profile `t = (t^1, …, t^n)` with `t b ℓ o = t^ℓ(b, o)` (p. 8). -/
abbrev Contract (n : ℕ) (O : Type) := (Fin n → O → ℝ) → Fin n → O → ℝ

/-- The agent's expected utility `∑_ℓ E_{o∼F|a}[t^ℓ(b, o)] − ψ(a)` (p. 8). -/
def agentUtil (S : Setting n A O) (t : Contract n O) (b : Fin n → O → ℝ) (a : A) : ℝ :=
  ∑ ℓ, E S a (t b ℓ) - S.psi a

/-- `a` is the agent's choice `x*(b)` under contract `t` at bid profile `b` (p. 8 and footnote 7):
it maximizes the agent's expected utility, and every other utility maximizer has strictly lower
declared welfare, or equal declared welfare and no higher cost. -/
def agentChoice (S : Setting n A O) (t : Contract n O) (b : Fin n → O → ℝ) (a : A) : Prop :=
  (∀ a', agentUtil S t b a' ≤ agentUtil S t b a) ∧
    ∀ a', agentUtil S t b a' = agentUtil S t b a →
      Wel S a' b < Wel S a b ∨ (Wel S a' b = Wel S a b ∧ S.psi a' ≤ S.psi a)

/-- Definition 2, p. 11 (IIVCG): (1) at every in-domain bid profile the agent's choice is `a*(b)`;
(2) there are `h^ℓ`, depending on `b^{−ℓ}` only, with
`E_{o∼F|a*(b)}[t^ℓ(b, o)] = h^ℓ(b^{−ℓ}) − Wel^{a*(b)}(b^{−ℓ}, 0)`. -/
def IsIIVCG [Nonempty A] (S : Setting n A O) (t : Contract n O) : Prop :=
  (∀ b, InDom S b → agentChoice S t b (aStar S b)) ∧
    ∃ h : Fin n → (Fin n → O → ℝ) → ℝ,
      (∀ ℓ b b', (∀ k, k ≠ ℓ → b k = b' k) → h ℓ b = h ℓ b') ∧
        ∀ b, InDom S b → ∀ ℓ,
          E S (aStar S b) (t b ℓ) = h ℓ b - Wel S (aStar S b) (Function.update b ℓ 0)

/-- Definition 1, p. 9 (limited liability): `t^ℓ(b, o) ≥ 0` for every `ℓ`, `b ∈ V`, `o`. -/
def IsLL (S : Setting n A O) (t : Contract n O) : Prop :=
  ∀ b, InDom S b → ∀ ℓ o, 0 ≤ t b ℓ o

/-- Individual rationality, p. 9:
`E_{o∼F|x*(b^{−ℓ},v^ℓ)}[v^ℓ(o) − t^ℓ((b^{−ℓ}, v^ℓ), o)] ≥ 0` for every `ℓ`, `b^{−ℓ}`, `v^ℓ ∈ V^ℓ`. -/
def IsIR (S : Setting n A O) (t : Contract n O) : Prop :=
  ∀ ℓ b v, InDom S b → v ∈ S.V ℓ → ∀ a, agentChoice S t (Function.update b ℓ v) a →
    0 ≤ E S a v - E S a (t (Function.update b ℓ v) ℓ)

/-- Truthfulness, p. 9: for every principal `ℓ`, true valuation `v^ℓ ∈ V^ℓ`, others' bids
`b^{−ℓ}` and alternative bid `b'^ℓ ∈ V^ℓ`, bidding `v^ℓ` gives `ℓ` at least the expected utility of
bidding `b'^ℓ`. -/
def IsTruthful (S : Setting n A O) (t : Contract n O) : Prop :=
  ∀ ℓ b v b', InDom S b → v ∈ S.V ℓ → b' ∈ S.V ℓ → ∀ a a',
    agentChoice S t (Function.update b ℓ v) a → agentChoice S t (Function.update b ℓ b') a' →
      E S a' v - E S a' (t (Function.update b ℓ b') ℓ) ≤
        E S a v - E S a (t (Function.update b ℓ v) ℓ)

end CommonAgencyVCG.Algorithmic


