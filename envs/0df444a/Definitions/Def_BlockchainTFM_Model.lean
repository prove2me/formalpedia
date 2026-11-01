-- Prove2me | Definitions.Def_BlockchainTFM_Model
-- name    : BlockchainTFM_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T14:02:02.928619+00:00
-- url     : https://prove2.me/theorems/ac5fc30f-41ec-4928-8f78-f40e4afe1e1e
-- title:
--   Transaction fee mechanisms, quasi-linear utility, the bid box $[0,1]^n$ and $c_\rho=\mathbb E[v^2]$
-- statement:
--   This module fixes the basic objects of the paper's model (§3.2–3.3).
--
--   1. **Bid box.** There are $n$ users; bids and valuations lie in $[0,1]$, so a bid vector is a point of $[0,1]^n$.
--   2. **Transaction fee mechanism** (Definition 1). A TFM $M(\mathbf a,\mathbf p,r)$ consists of an allocation rule $\mathbf a$ (the probability $a_i(\mathbf b)$ that user $i$'s transaction is confirmed), a payment rule $\mathbf p$ (the payment $p_i(\mathbf b)$ of user $i$ *if her transaction is confirmed*) and a miner revenue rule $r$.
--   3. **Quasi-linear utility** (2). When user $i$ has valuation $v_i$ and the bid vector is $(b_i,\mathbf b_{-i})$,
--   $$u_i(b_i,\mathbf b_{-i};v_i)=a_i(b_i,\mathbf b_{-i})\,\bigl(v_i-p_i(b_i,\mathbf b_{-i})\bigr).$$
--   4. **The constant $c_\rho$.** For the valuation law $V_0$,
--   $$c_\rho=\mathbb E_{v\sim V_0}[v^2]=\int t^2\,dV_0(t).$$
--
--   The paper's (18) prints $c_\rho=\int_0^1\rho^2(t)\,dt$, but every use of $c_\rho$ needs the second moment: the proof of Lemma 2 substitutes $\mathbb E[b_j^2]=c_\rho$, §7.2 gives $c_\rho=1/3$ for the uniform law, and (EC.71) uses $c_\rho\le 1$. With $\int\rho^2$, Lemma 2 and Theorem 4 fail.
--
--   **Formalization Note** Users are indexed by `Fin n` (Lean's user $i$ is the paper's user $i+1$). The three rules are total functions on $\mathbb R^n$; all properties quantify only over bid vectors in $[0,1]^n$. No bound on $\mathbf a$ is bundled into the structure. $V_0$ is any measure on $\mathbb R$; the theorems assume a probability measure carried by $[0,1]$.
-- source:
--   Chen, Simchi-Levi, Zhao, Zhou, Bayesian Mechanism Design for Blockchain Transaction Fee Allocation, arXiv:2209.13099v7, §3.2 Definition 1 p.16; (2) p.17; (18) p.26 (corrected: c_ρ = E[v²], see §7.2 p.33, §8 p.35, (EC.44)–(EC.45) p.ec11, (EC.71))

import Mathlib

open MeasureTheory

namespace BlockchainTFM

/-- **The bid box `[0,1]ⁿ`**, Chen–Simchi-Levi–Zhao–Zhou, *Bayesian Mechanism Design for
Blockchain Transaction Fee Allocation*, arXiv:2209.13099v7, §3.2, Definition 1, p.16: bids and
valuations lie in `[0,1]`, so a bid vector of `n` users is a point of `[0,1]ⁿ`.

**Formalization Note.** Users are `Fin n`; Lean index `i` is the paper's user `i+1`. -/
def bidBox (n : ℕ) : Set (Fin n → ℝ) :=
  Set.univ.pi fun _ => Set.Icc (0 : ℝ) 1

/-- **Transaction Fee Mechanism** `M(a, p, r)`, arXiv:2209.13099v7, Definition 1, p.16: an
allocation rule `a` (the probability that each user's transaction is confirmed), a payment rule
`p` (the payment of a user *if her transaction is confirmed*) and a miner revenue rule `r`.

**Formalization Note.** The three rules are total functions on `Fin n → ℝ`; every property of a
TFM in this development quantifies only over bid vectors in `bidBox n`, so the values outside
`[0,1]ⁿ` never matter. No bound on `a` (such as `a ∈ [0,1]` or `∑ a ≤ k`) is bundled: the
theorems are about specific mechanisms or state what they use. -/
structure TFM (n : ℕ) where
  /-- allocation rule `a : [0,1]ⁿ → [0,1]ⁿ` -/
  alloc : (Fin n → ℝ) → Fin n → ℝ
  /-- payment rule `p : [0,1]ⁿ → ℝⁿ` (payment if confirmed) -/
  pay : (Fin n → ℝ) → Fin n → ℝ
  /-- miner revenue rule `r : [0,1]ⁿ → ℝ` -/
  rev : (Fin n → ℝ) → ℝ

/-- **Quasi-linear utility** (2), arXiv:2209.13099v7, p.17:
`u_i(b_i, b_{-i}; v_i) = a_i(b_i, b_{-i}) · (v_i − p_i(b_i, b_{-i}))`.
Here `b` is the whole bid vector (user `i`'s own bid is `b i`) and `v` is user `i`'s value. -/
def utility {n : ℕ} (M : TFM n) (i : Fin n) (b : Fin n → ℝ) (v : ℝ) : ℝ :=
  M.alloc b i * (v - M.pay b i)

/-- **The constant `c_ρ`**, arXiv:2209.13099v7, (18), p.26, *as corrected*:
`c_ρ = E_{v∼V₀}[v²] = ∫ t² dV₀(t)`.

**Formalization Note.** The paper prints `c_ρ = ∫₀¹ ρ²(t) dt`; every use of `c_ρ` in the paper
(the proof of Lemma 2 at (EC.44)–(EC.45), §7.2 "the uniform distribution … leads to
`c_ρ = 1/3`", §8 "`c_ρ = E[b_i²]`", (EC.71) "`c_ρ ≤ 1`") needs the second moment, and with
`∫ρ²` Lemma 2 and Theorem 4 are false (for the uniform law `∫ρ² = 1` but `E[v²] = 1/3`). The
valuation law is any measure `V₀` on `ℝ`; the theorems assume it is a probability measure
carried by `[0,1]`. -/
noncomputable def crho (V₀ : Measure ℝ) : ℝ :=
  ∫ t, t ^ 2 ∂V₀

end BlockchainTFM


