-- Prove2me | Definitions.Def_RefMNLPricing_Myopic_Model
-- name    : RefMNLPricing_Myopic_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T04:09:28.802426+00:00
-- url     : https://prove2.me/theorems/531ec2b4-093d-4f04-8fda-09961b68bc78
-- title:
--   §2, pp. 7–11 — kinked MNL utility (2), shares (3), revenue (4), price box, myopic policies (7), reference path (1), ceiling equation (9)
-- statement:
--   This file sets up the multi-product pricing model with reference effects under multinomial logit (MNL) demand.
--
--   A seller offers products $i \in N = \{1,\dots,n\}$. Each product has an intrinsic utility $a_i\in\mathbb R$, a price sensitivity $b_i$, and reference-price sensitivities $c_i^+$ (to gains) and $c_i^-$ (to losses). Given a price vector $p$ and a reference price vector $r$, the deterministic utility of product $i$ is
--
--   $$
--   u_i(p,r) = a_i - b_i p_i + c_i^+ (r_i - p_i)_+ - c_i^- (p_i - r_i)_+,\qquad (x)_+ := \max\{x,0\},
--   $$
--
--   the market share of product $i$ (the MNL purchase probability, with a no-purchase option of utility $0$) is
--
--   $$
--   q_i(p,r) = \frac{e^{u_i(p,r)}}{1 + \sum_{k\in N} e^{u_k(p,r)}},
--   $$
--
--   and the single-period revenue is $\Pi(p,r) = \sum_{i\in N} p_i\, q_i(p,r)$.
--
--   Prices and reference prices range over the box $\mathcal P^n = [0,p_H]^n$, where $p_H$ is the price ceiling. A price vector $p$ is a **maximiser over $\mathcal P^n$** at reference price $r$ if $p \in \mathcal P^n$ and $\Pi(p',r) \le \Pi(p,r)$ for all $p' \in \mathcal P^n$; its revenue $\Pi(p,r)$ is the optimal single-period revenue $\Pi^m(r)$. A **myopic pricing policy** is a map $p^m$ assigning to every $r \in \mathcal P^n$ such a maximiser. Since maximisers need not be unique, every choice is allowed.
--
--   The reference price evolves by exponential smoothing with memory $\alpha$: under a myopic policy $p^m$, starting from $r^0$,
--
--   $$
--   r^{t+1} = \alpha r^t + (1-\alpha)\, p^m(r^t),\qquad t \ge 0,
--   $$
--
--   and the myopic price path is $t \mapsto p^m(r^t)$.
--
--   Finally, with $\chi := \max_{i\in N} 1/(b_i + \min\{c_i^+,c_i^-\})$, the **ceiling equation** (9) is
--
--   $$
--   p = \chi + \sum_{i\in N} \frac{1}{b_i + c_i^+}\exp\big(a_i - b_i p + (b_i + c_i^+)\chi - 1\big),
--   $$
--
--   and the **ceiling assumption** says that some solution $\hat p_H$ of (9) satisfies $\hat p_H \le p_H$. The paper assumes it throughout §3–§4 (p. 11); it makes the ceiling non-binding for the myopic problem.
--
--   These objects are shared by every statement of the mission about the myopic policy.
--
--   **Formalization Note** Products are `Fin n` (0-based). Utilities (3) are defined directly; the Gumbel random-utility derivation is motivation only. $\chi$ is an indexed supremum over `Fin n`, which is $0$ when $n=0$; the unused argument `a` of `chi` only keeps the parameter list uniform. The standing hypotheses $b>0$, $c^\pm\ge0$, $\alpha\in[0,1]$, $p_H>0$ are not built in: each theorem states them.
-- source:
--   Guo, Jiang, Shen, Multi-Product Dynamic Pricing with Reference Effects Under Logit Demand, SSRN 4189049 (version of 2024-05-25), pp. 7–11, Definition 1 (1), (2)–(4), (7)–(8), Proposition 1.2 (9), §2.4 p. 11

import Mathlib

namespace RefMNLPricing.Myopic

/-! The model of Guo, Jiang, Shen, *Multi-Product Dynamic Pricing with Reference Effects Under Logit
Demand*, SSRN 4189049 (version of 2024-05-25), §2, pp. 7–11. Products are indexed by `Fin n`
(0-based: the paper's product `i` is index `i - 1`). The parameters are `a b cp cm : Fin n → ℝ`
for `a, b, c⁺, c⁻`; the standing hypotheses `b > 0`, `c⁺, c⁻ ≥ 0` (p. 7) are stated by every theorem
that uses them, not built into these definitions. -/

/-- Deterministic part of the utility (2), p. 8, of product `i` at price vector `p` and reference
price vector `r`: `a_i - b_i p_i + c_i⁺ (r_i - p_i)₊ - c_i⁻ (p_i - r_i)₊`. -/
noncomputable def util {n : ℕ} (a b cp cm : Fin n → ℝ) (p r : Fin n → ℝ) (i : Fin n) : ℝ :=
  a i - b i * p i + cp i * max (r i - p i) 0 - cm i * max (p i - r i) 0

/-- Market share (purchase probability) (3), p. 8, of product `i`:
`q_i(p, r) = exp(u_i) / (1 + ∑_k exp(u_k))`, the no-purchase option having utility `0`. -/
noncomputable def share {n : ℕ} (a b cp cm : Fin n → ℝ) (p r : Fin n → ℝ) (i : Fin n) : ℝ :=
  Real.exp (util a b cp cm p r i) / (1 + ∑ k, Real.exp (util a b cp cm p r k))

/-- Single-period revenue (4), p. 8: `Π(p, r) = ∑_i p_i q_i(p, r)`. -/
noncomputable def revenue {n : ℕ} (a b cp cm : Fin n → ℝ) (p r : Fin n → ℝ) : ℝ :=
  ∑ i, p i * share a b cp cm p r i

/-- The admissible box `Pⁿ = [0, p_H]ⁿ` (p. 9): every coordinate of `x` lies in `[0, p_H]`. -/
def InBox {n : ℕ} (pH : ℝ) (x : Fin n → ℝ) : Prop :=
  ∀ i, x i ∈ Set.Icc 0 pH

/-- `p` is a maximiser over `Pⁿ` of the single-period revenue `Π(·, r)` (the myopic problem (7),
p. 9): `p ∈ Pⁿ` and `Π(p', r) ≤ Π(p, r)` for every `p' ∈ Pⁿ`. -/
def IsBoxMax {n : ℕ} (a b cp cm : Fin n → ℝ) (pH : ℝ) (r p : Fin n → ℝ) : Prop :=
  InBox pH p ∧ ∀ p', InBox pH p' → revenue a b cp cm p' r ≤ revenue a b cp cm p r

/-- `χ := max_{i ∈ N} 1 / (b_i + min{c_i⁺, c_i⁻})` of (9), p. 10, as an indexed supremum over
`Fin n` (equal to `0` when `n = 0`). The intercepts `a` are not used; the argument is kept so
that every object of the model takes the same parameter list `a b cp cm`. -/
noncomputable def chi {n : ℕ} (_a b cp cm : Fin n → ℝ) : ℝ :=
  ⨆ i, 1 / (b i + min (cp i) (cm i))

/-- The right-hand side of (9), p. 10, as a function of `p`:
`χ + ∑_i 1/(b_i + c_i⁺) · exp(a_i - b_i p + (b_i + c_i⁺) χ - 1)`. -/
noncomputable def ceilRHS {n : ℕ} (a b cp cm : Fin n → ℝ) (p : ℝ) : ℝ :=
  chi a b cp cm +
    ∑ i, 1 / (b i + cp i) * Real.exp (a i - b i * p + (b i + cp i) * chi a b cp cm - 1)

/-- The standing ceiling assumption of §2.4, p. 11, `p_H ≥ p̂_H`: some solution `p̂_H` of (9) is at
most `p_H`. (Equation (9) has a unique solution, Proposition 1.2, so this is `p_H ≥ p̂_H`.) -/
def CeilingOK {n : ℕ} (a b cp cm : Fin n → ℝ) (pH : ℝ) : Prop :=
  ∃ pHat : ℝ, pHat = ceilRHS a b cp cm pHat ∧ pHat ≤ pH

/-- `pm` is a myopic pricing policy (7), p. 9: for every reference price `r ∈ Pⁿ`, `pm r` is a
maximiser of `Π(·, r)` over `Pⁿ`. Maximisers need not be unique, so a myopic policy is any such
selection. -/
def IsMyopicSel {n : ℕ} (a b cp cm : Fin n → ℝ) (pH : ℝ) (pm : (Fin n → ℝ) → (Fin n → ℝ)) :
    Prop :=
  ∀ r, InBox pH r → IsBoxMax a b cp cm pH r (pm r)

/-- The reference-price path under the myopic policy `pm` ((1) and (8), pp. 7, 10):
`r⁰ = r₀` and `r^{t+1} = α r^t + (1 - α) pm(r^t)`. The myopic price path is `t ↦ pm (r^t)`. -/
noncomputable def myopicRef {n : ℕ} (pm : (Fin n → ℝ) → (Fin n → ℝ)) (α : ℝ) (r₀ : Fin n → ℝ) :
    ℕ → Fin n → ℝ
  | 0 => r₀
  | t + 1 => fun i => α * myopicRef pm α r₀ t i + (1 - α) * pm (myopicRef pm α r₀ t) i

end RefMNLPricing.Myopic


