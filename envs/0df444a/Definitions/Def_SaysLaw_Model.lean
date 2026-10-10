-- Prove2me | Definitions.Def_SaysLaw_Model
-- name    : SaysLaw_Model
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-09T21:28:44.331976+00:00
-- url     : https://prove2.me/theorems/9c6a54a5-e357-48ba-865a-1f4907aead04
-- title:
--   Exchange economy: bundle values, excess demand, Say's budget, general glut, monetary budget
-- statement:
--   This file fixes the vocabulary of a minimal exchange economy in which Say's law can be stated.
--
--   Let $\iota$ be a finite set of agents and $G$ a finite set of goods. A price vector is $p\in\mathbb R^G$; agent $i$ brings the bundle $s_i\in\mathbb R^G$ to market (his supply) and plans to buy the bundle $d_i\in\mathbb R^G$ (his demand).
--
--   1. **Bundle value.** $\langle p,x\rangle=\sum_{g\in G}p_g\,x_g$.
--   2. **Aggregate excess demand.** $z_g=\sum_{i\in\iota}(d_{i,g}-s_{i,g})$ for each good $g$.
--   3. **Say's budget principle** ("products are paid for with products"): for every agent $i$, $$\langle p,d_i\rangle=\langle p,s_i\rangle,$$ i.e. the proceeds of what is sold are spent in full on other products.
--   4. **General glut.** A vector $z\in\mathbb R^G$ is a general glut when $z_g<0$ for every $g\in G$ (every good is in excess supply).
--   5. **Monetary budget.** With initial money balances $m_i$ and planned money balances $m'_i$, $$\langle p,d_i\rangle+m'_i=\langle p,s_i\rangle+m_i\quad\text{for every }i.$$
--   6. **Aggregate excess demand for money.** $\sum_{i\in\iota}(m'_i-m_i)$; it is positive when agents in aggregate hoard money.
--
--   These notions formalize the article's sections "Formulation", "Keynesian", "Role of money" and J. S. Mill's treatment of money as a commodity (section "Immediate reception").
--
--   **Formalization Note** Quantities are real numbers with no sign restriction, so $s_i,d_i$ may be read as gross supplies and demands or as net trades. No sign restriction is placed on prices in the definitions; theorems that need positive prices assume them explicitly.
-- source:
--   Wikipedia, "Say's law" (PDF export supplied with the request); https://en.wikipedia.org/wiki/Say%27s_law, sections "Formulation", "Keynesian", "Role of money", "Immediate reception"

import Mathlib

namespace SaysLaw

/-- Market value `∑ g, p g * x g` of a bundle of goods `x` at the price vector `p`. -/
def bundleValue {G : Type*} [Fintype G] (p x : G → ℝ) : ℝ :=
  ∑ g, p g * x g

/-- Aggregate excess demand for each good: the total quantity of good `g` that the agents
plan to buy, minus the total quantity of `g` that they bring to market (their supply). -/
def excessDemand {ι G : Type*} [Fintype ι] (supply demand : ι → G → ℝ) : G → ℝ :=
  fun g => ∑ i, (demand i g - supply i g)

/-- Say's budget principle ("products are paid for with products"): at prices `p`, every
agent plans to buy goods of exactly the market value of the goods he supplies, so that no
proceeds of a sale remain unspent. -/
def SaysBudget {ι G : Type*} [Fintype G] (p : G → ℝ) (supply demand : ι → G → ℝ) : Prop :=
  ∀ i, bundleValue p (demand i) = bundleValue p (supply i)

/-- A *general glut*: every good is in excess supply, i.e. aggregate excess demand is
strictly negative for every good. -/
def GeneralGlut {G : Type*} (z : G → ℝ) : Prop :=
  ∀ g, z g < 0

/-- Budget constraint of a monetary economy: agent `i` enters with money balance `m i` and
plans to end with money balance `m' i`; spending on goods plus planned money holdings
equals the value of goods supplied plus initial money holdings. -/
def MonetaryBudget {ι G : Type*} [Fintype G] (p : G → ℝ) (supply demand : ι → G → ℝ)
    (m m' : ι → ℝ) : Prop :=
  ∀ i, bundleValue p (demand i) + m' i = bundleValue p (supply i) + m i

/-- Aggregate excess demand for money: planned money holdings minus initial money
holdings, summed over all agents (positive when agents in aggregate hoard money). -/
def excessMoneyDemand {ι : Type*} [Fintype ι] (m m' : ι → ℝ) : ℝ :=
  ∑ i, (m' i - m i)

end SaysLaw


