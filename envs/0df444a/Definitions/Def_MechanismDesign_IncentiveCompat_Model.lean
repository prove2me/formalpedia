-- Prove2me | Definitions.Def_MechanismDesign_IncentiveCompat_Model
-- name    : MechanismDesign_IncentiveCompat_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T01:59:22.622874+00:00
-- url     : https://prove2.me/theorems/2eed004f-f798-4e6e-b74a-5c6b29b85566
-- title:
--   Single-agent mechanism design: direct mechanisms, incentive compatibility, weak and cyclical monotonicity, one-dimensional, bounded and rich type spaces
-- statement:
--   One agent and a mechanism designer choose an alternative $a$ from an arbitrary set $A$. The agent's type $\theta$ lies in an arbitrary set $\Theta$, and her utility from alternative $a$ when she pays the transfer $t$ is $u(a,\theta) - t$ for a given function $u : A \times \Theta \to \mathbb R$.
--
--   1. A **direct mechanism** $(q,t)$ (Definition 5.1) is a *decision rule* $q : \Theta \to A$ together with a transfer rule $t : \Theta \to \mathbb R$ (the agent pays $t(\theta)$; a negative value is a payment to her).
--   2. $(q,t)$ is **incentive-compatible** (Definition 5.2) if for all $\theta,\theta' \in \Theta$
--   $$u(q(\theta),\theta) - t(\theta) \ge u(q(\theta'),\theta) - t(\theta').$$
--   3. A decision rule $q$ is **implementable** (Definition 5.3) if some $t$ makes $(q,t)$ incentive-compatible.
--   4. $q$ is **weakly monotone** (Definition 5.4) if for all $\theta_1,\theta_2$, writing $a_i = q(\theta_i)$, $u(a_1,\theta_1) - u(a_2,\theta_1) \ge u(a_1,\theta_2) - u(a_2,\theta_2)$.
--   5. $q$ is **cyclically monotone** (Definition 5.5) if for every $k \in \mathbb N$ and every sequence $(\theta^1,\dots,\theta^k) \in \Theta^k$ with $\theta^k = \theta^1$,
--   $$\sum_{\kappa=1}^{k-1}\bigl(u(a^\kappa,\theta^{\kappa+1}) - u(a^\kappa,\theta^\kappa)\bigr) \le 0, \qquad a^\kappa = q(\theta^\kappa).$$
--
--   For a complete and transitive order $R$ of $A$, with strict part $P$ ($aPb$ iff $aRb$ and not $bRa$) and indifference part $I$ ($aIb$ iff $aRb$ and $bRa$):
--
--   6. $\theta \succ_R \theta'$ (Definition 5.6) if $u(a,\theta) - u(a',\theta) > u(a,\theta') - u(a',\theta')$ whenever $aPa'$, and $u(a,\theta) - u(a',\theta) = u(a,\theta') - u(a',\theta') = 0$ whenever $aIa'$.
--   7. $q$ is **monotone with respect to $R$** (Definition 5.7) if $\theta \succ_R \theta'$ implies $q(\theta)\,R\,q(\theta')$.
--   8. $\Theta$ is **one-dimensional with respect to $R$** (Definition 5.8) if any two distinct types satisfy $\theta \succ_R \theta'$ or $\theta' \succ_R \theta$.
--   9. $\Theta$ is **bounded** (Definition 5.9) if there is $c > 0$ with $-c < u(a',\theta) - u(a,\theta) < c$ for all $a,a' \in A$, $\theta \in \Theta$.
--
--   For a relation $R$ on $A$, a function $v : A \to \mathbb R$ **represents** $R$ if $aRb$ implies $v(a) \ge v(b)$.
--
--   10. $\Theta$ is **rich** (Definition 5.10) if there is a reflexive and transitive, possibly incomplete, relation $R$ on $A$ such that every $v$ representing $R$ is the utility function of some type: $u(a,\theta) = v(a)$ for all $a$. The domain is **consistent with $R$** if, conversely, every type's utility function $u(\cdot,\theta)$ represents $R$ (Bikhchandani et al. 2006).
--   11. $(q,t)$ is **individually rational with outside option $a$** (Definition 5.11) if $u(q(\theta),\theta) - t(\theta) \ge u(a,\theta)$ for all $\theta$.
--
--   For lotteries over a finite outcome set $\Omega$: the alternatives are the probability vectors $p \in \Delta(\Omega) \subseteq \mathbb R^\Omega$, a type is a vector $\theta \in \mathbb R^\Omega$ of Bernoulli utilities, and the utility is the expected utility $p \cdot \theta$. A vector $x^*$ is a **subgradient** of $U$ at $x$ relative to a set $S$ if $U(z) \ge U(x) + x^*\cdot(z - x)$ for all $z \in S$ (Rockafellar's definition, quoted on p.103).
--
--   These are the objects of every statement of Chapter 5.
--
--   **Formalization Note** A sequence of length $k = m+1$ is a map `Fin (m+1) → Θ`; the $k-1 = m$ summands of cyclical monotonicity are indexed by `Fin m`. The case $k = 1$ (an empty sum) is included and trivially satisfied, as on the page. Relations are predicates `A → A → Prop`. Consistency with $R$ is not part of the book's Definition 5.10; it is defined separately and used only in Proposition 5.7.
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, pp.95–110, §§5.2–5.9, Definitions 5.1–5.11; p.102 (lotteries), p.103 (subgradient)

import Mathlib

/-!
# Incentive compatibility with one agent (Börgers, Ch. 5, pp.95–110)

One agent, an arbitrary set `A` of alternatives, an arbitrary set `Θ` of types, and a utility
`u : A → Θ → ℝ`; the agent's payoff from alternative `a` and transfer `t` is `u a θ - t`
(§5.2, pp.95–96). No structure on `A` or `Θ` is assumed here; the theorems add exactly the
hypotheses of each proposition (`Θ` nonempty is the standing assumption of §5.2).
-/

namespace MechanismDesign.IncentiveCompat

/-- Definition 5.1 (p.96). A direct mechanism: a decision rule `q : Θ → A` and a transfer rule
`t : Θ → ℝ` (the agent pays `t θ`; a negative value is a payment to the agent). -/
structure DirectMechanism (A Θ : Type*) where
  /-- the decision rule -/
  q : Θ → A
  /-- the transfer the agent makes -/
  t : Θ → ℝ

variable {A Θ : Type*}

/-- Definition 5.2 (p.96). `(q, t)` is incentive-compatible if for all `θ, θ'`,
`u(q(θ), θ) - t(θ) ≥ u(q(θ'), θ) - t(θ')`. -/
def IsIC (u : A → Θ → ℝ) (M : DirectMechanism A Θ) : Prop :=
  ∀ θ θ' : Θ, u (M.q θ') θ - M.t θ' ≤ u (M.q θ) θ - M.t θ

/-- Definition 5.3 (p.96). A decision rule `q` is implementable if some transfer rule `t` makes
`(q, t)` incentive-compatible. -/
def Implementable (u : A → Θ → ℝ) (q : Θ → A) : Prop :=
  ∃ t : Θ → ℝ, IsIC u ⟨q, t⟩

/-- Definition 5.4 (p.97). `q` is weakly monotone if for all `θ₁, θ₂`, with `a₁ = q θ₁` and
`a₂ = q θ₂`, `u(a₁, θ₁) - u(a₂, θ₁) ≥ u(a₁, θ₂) - u(a₂, θ₂)`. -/
def WeaklyMonotone (u : A → Θ → ℝ) (q : Θ → A) : Prop :=
  ∀ θ₁ θ₂ : Θ, u (q θ₁) θ₂ - u (q θ₂) θ₂ ≤ u (q θ₁) θ₁ - u (q θ₂) θ₁

/-- Definition 5.5 (p.99). `q` is cyclically monotone if for every finite sequence of types
`(θ¹, …, θᵏ)` with `θᵏ = θ¹`, `∑_{κ=1}^{k-1} (u(aᵏ, θ^{κ+1}) - u(aᵏ, θᵏ)) ≤ 0` where
`a^κ = q(θ^κ)`. A sequence of length `k = m + 1 ≥ 1` is `θs : Fin (m + 1) → Θ` (`θs 0` is `θ¹`,
`θs (Fin.last m)` is `θᵏ`), and the `k - 1 = m` summands are indexed by `κ : Fin m`, the summand
for `κ` using the consecutive pair `θs κ.castSucc`, `θs κ.succ`. -/
def CyclicallyMonotone (u : A → Θ → ℝ) (q : Θ → A) : Prop :=
  ∀ (m : ℕ) (θs : Fin (m + 1) → Θ), θs 0 = θs (Fin.last m) →
    ∑ κ : Fin m, (u (q (θs κ.castSucc)) (θs κ.succ) - u (q (θs κ.castSucc)) (θs κ.castSucc)) ≤ 0

/-! ### Orders on alternatives and types (§5.6, pp.103–106) -/

/-- `R` is a complete and transitive order of `A` (p.104 and note 2, p.236). -/
def IsCompleteTransitive (R : A → A → Prop) : Prop :=
  (∀ a b, R a b ∨ R b a) ∧ (∀ a b c, R a b → R b c → R a c)

/-- The strict order `P` derived from `R`: `aPb ↔ aRb ∧ ¬ bRa` (p.104). -/
def StrictPart (R : A → A → Prop) (a b : A) : Prop := R a b ∧ ¬ R b a

/-- The indifference relation `I` derived from `R`: `aIb ↔ aRb ∧ bRa` (p.104). -/
def Indiff (R : A → A → Prop) (a b : A) : Prop := R a b ∧ R b a

/-- Definition 5.6 (p.104). `θ ≻_R θ'` ("θ is a higher type than θ' relative to R"):
`u(a, θ) - u(a', θ) > u(a, θ') - u(a', θ')` for all `a P a'`, and
`u(a, θ) - u(a', θ) = u(a, θ') - u(a', θ') = 0` for all `a I a'`. -/
def HigherType (u : A → Θ → ℝ) (R : A → A → Prop) (θ θ' : Θ) : Prop :=
  (∀ a a', StrictPart R a a' → u a θ' - u a' θ' < u a θ - u a' θ) ∧
  (∀ a a', Indiff R a a' → u a θ - u a' θ = u a θ' - u a' θ' ∧ u a θ' - u a' θ' = 0)

/-- Definition 5.7 (p.105). `q` is monotone with respect to `R`: `θ ≻_R θ' → q(θ) R q(θ')`. -/
def MonotoneWRT (u : A → Θ → ℝ) (R : A → A → Prop) (q : Θ → A) : Prop :=
  ∀ θ θ' : Θ, HigherType u R θ θ' → R (q θ) (q θ')

/-- Definition 5.8 (p.105). `Θ` is one-dimensional with respect to `R`: any two distinct types
are ordered by `≻_R` (in at least one direction). -/
def OneDimensional (u : A → Θ → ℝ) (R : A → A → Prop) : Prop :=
  ∀ θ θ' : Θ, θ ≠ θ' → HigherType u R θ θ' ∨ HigherType u R θ' θ

/-- Definition 5.9 (p.106). `Θ` is bounded: there is `c > 0` with `-c < u(a', θ) - u(a, θ) < c`
for all `a, a' ∈ A` and all `θ ∈ Θ`. -/
def IsBoundedTypeSpace (u : A → Θ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (a a' : A) (θ : Θ), -c < u a' θ - u a θ ∧ u a' θ - u a θ < c

/-! ### Rich type spaces (§5.7, pp.108–109) -/

/-- A function `v : A → ℝ` represents the relation `R`: `a R b → v(a) ≥ v(b)` (p.108). -/
def Represents (R : A → A → Prop) (v : A → ℝ) : Prop :=
  ∀ a b, R a b → v b ≤ v a

/-- The richness clause of Definition 5.10 for a given relation `R`: every `v : A → ℝ` that
represents `R` is the utility function `u(·, θ)` of some type `θ`. -/
def IsRichWRT (u : A → Θ → ℝ) (R : A → A → Prop) : Prop :=
  ∀ v : A → ℝ, Represents R v → ∃ θ : Θ, ∀ a, u a θ = v a

/-- Definition 5.10 (p.108). `Θ` is rich: there is a reflexive and transitive, possibly
incomplete, relation `R` on `A` such that every `v : A → ℝ` representing `R` is the utility
function of some type. -/
def IsRich (u : A → Θ → ℝ) : Prop :=
  ∃ R : A → A → Prop, (∀ a, R a a) ∧ (∀ a b c, R a b → R b c → R a c) ∧ IsRichWRT u R

/-- Every type's utility function represents `R` ("the domain is consistent with `R`",
Bikhchandani et al. 2006, §3; not part of the book's Definition 5.10, see Proposition 5.7). -/
def IsConsistentWRT (u : A → Θ → ℝ) (R : A → A → Prop) : Prop :=
  ∀ θ : Θ, Represents R (fun a => u a θ)

/-! ### Individual rationality (§5.9, p.110) -/

/-- Definition 5.11 (p.110). `(q, t)` is individually rational with outside option `a`:
`u(q(θ), θ) - t(θ) ≥ u(a, θ)` for all `θ`. -/
def IsIRWith (u : A → Θ → ℝ) (M : DirectMechanism A Θ) (a : A) : Prop :=
  ∀ θ : Θ, u a θ ≤ u (M.q θ) θ - M.t θ

/-! ### Lotteries over finitely many outcomes (§5.5, pp.102–103) -/

/-- The expected utility `p · θ = ∑_ℓ p_ℓ θ_ℓ` of the lottery `p ∈ Δ(Ω)` for the vector `θ` of
Bernoulli utilities of the outcomes (p.102). -/
def lotteryUtility {Ω : Type*} [Fintype Ω] (p : stdSimplex ℝ Ω) (θ : Ω → ℝ) : ℝ :=
  dotProduct (p : Ω → ℝ) θ

/-- Rockafellar's subgradient (quoted p.103), relative to the domain `S`: `x*` is a subgradient
of `U` at `x` if `U(z) ≥ U(x) + x* · (z - x)` for all `z ∈ S`. -/
def IsSubgradientOn {Ω : Type*} [Fintype Ω] (S : Set (Ω → ℝ)) (U : (Ω → ℝ) → ℝ)
    (x xstar : Ω → ℝ) : Prop :=
  ∀ z ∈ S, U x + dotProduct xstar (z - x) ≤ U z

end MechanismDesign.IncentiveCompat


