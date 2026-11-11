-- Prove2me | Definitions.Def_PostedPriceLimits_FullRevelation_BiasedXOS
-- name    : PostedPriceLimits_FullRevelation_BiasedXOS
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:39:47.58413+00:00
-- url     : https://prove2.me/theorems/3a1caa75-e035-43df-aaa9-b75bac7b7eab
-- title:
--   Biased XOS representations, biased clause oracles and XOS clause-oracle responses (Definitions 3.3, 3.7)
-- statement:
--   A **biased clause** is a pair $c=(u_0,u)$ of a bias $u_0$ and item values $u\in\mathbb R^m$; it values a bundle $S\subseteq M$ at $u(S)+u_0\mathbf 1(S\neq\varnothing)$, so the bias is earned once for any nonempty bundle.
--
--   1. **Biased XOS representation** (Definition 3.7). A finite nonempty set $U$ of biased clauses with $u_0\ge0$ and $u\ge0$ (that is, $U\subseteq\mathbb R_+^{m+1}$) represents $v$ if $v(S)=\max_{c\in U}\{u(S)+u_0\mathbf 1(S\ne\varnothing)\}$ for every $S\subseteq M$.
--   2. **Biased clause oracle** (Definition 3.7). A function answering each price query $p\in[0,\infty]^m$ with the lexicographically smallest utility-maximizing set $S$ (the demand-oracle answer of Definition 3.2) and a clause $c\in U$ supporting it, $v(S)=u(S)+u_0\mathbf 1(S\neq\varnothing)$, chosen by an arbitrary fixed deterministic rule; when $S=\varnothing$ the clause returned is $0$.
--   3. **XOS clause oracle** (Definition 3.3). For a fixed XOS representation $E$ of $v$, the response to $p$ is the pair $(S,u)$ where $S$ is the lexicographically smallest utility-maximizing set and $u$ is the lexicographically smallest clause of $E$ (comparing item values in item order) with $v(S)=u(S)$. Both oracles take price vectors, not bundles, as queries.
--
--   These notions are used in Proposition 3.8, which reduces biased representations to ordinary XOS ones without making the clause oracle more informative.
-- source:
--   Frederick Qiu, Aviad Rubinstein, STOC 2027 submission #1596 (October 2026), Definitions 3.3 and 3.7, p.5 (PDF 6); PDF SHA-256 5be77a250fd554b42d30cff15c46dafe3e43c75a2d90968fae98c61ff1113bb3; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1596.pdf

import Mathlib
import Definitions.Def_ComplementFreeCA_XOSGreedy_Model
import Definitions.Def_PostedPriceLimits_FullRevelation_Model

open scoped ENNReal

namespace PostedPriceLimits.FullRevelation

open ComplementFreeCA.XOSGreedy

/-! ## Clause oracles and biased XOS representations (Definitions 3.3 and 3.7)

A biased clause is a pair `(u₀, u)` of a bias `u₀` and item values `u : M → ℝ`; it values a
bundle `S` at `u(S) + u₀ · 1(S ≠ ∅)`. -/

/-- The value `u(S) + u₀·1(S ≠ ∅)` of the bundle `S` under the biased clause `c = (u₀, u)`. -/
noncomputable def biasedClauseValue {d : ℕ} (c : ℝ × (Fin d → ℝ)) (S : Finset (Fin d)) : ℝ :=
  ∑ x ∈ S, c.2 x + (if S = ∅ then 0 else c.1)

/-- Definition 3.7: `U` is a biased XOS representation of `v` — a finite nonempty set of
clauses in `ℝ₊^{m+1}` (nonnegative bias and nonnegative item values) with
`v(S) = max_{u ∈ U} {u(S) + u₀ 1(S ≠ ∅)}` for every `S ⊆ M`. -/
def IsBiasedXOSRep {d : ℕ} (U : Finset (ℝ × (Fin d → ℝ))) (v : Finset (Fin d) → ℝ) : Prop :=
  ∃ hU : U.Nonempty,
    (∀ c ∈ U, 0 ≤ c.1 ∧ ∀ x, 0 ≤ c.2 x) ∧
    ∀ S, v S = U.sup' hU (fun c => biasedClauseValue c S)

/-- Definition 3.7: `orc` is a biased clause oracle for the valuation `v` and the biased
representation `U`. On a price query `p ∈ [0,∞]^m` it returns the lexicographically smallest
utility-maximizing set `S` (the demand-oracle answer) together with a clause of `U` that
supports `S` (`v(S) = u(S) + u₀ 1(S ≠ ∅)`, hence utility-maximizing), chosen by an arbitrary
fixed deterministic rule; when `S = ∅` it returns the clause `0`. -/
def IsBiasedClauseOracle {d : ℕ} (U : Finset (ℝ × (Fin d → ℝ))) (v : Finset (Fin d) → ℝ)
    (orc : (Fin d → ℝ≥0∞) → Finset (Fin d) × (ℝ × (Fin d → ℝ))) : Prop :=
  ∀ p, (orc p).1 = demandSet v p ∧
    ((orc p).1 = ∅ → (orc p).2 = 0) ∧
    ((orc p).1 ≠ ∅ → (orc p).2 ∈ U ∧ v (orc p).1 = biasedClauseValue (orc p).2 (orc p).1)

/-- Definition 3.3: `r = (S, u)` is the response of the XOS clause oracle of the fixed
representation `E` to the price query `p ∈ [0,∞]^m`: `S` is the lexicographically smallest
utility-maximizing set of `v = E.val`, and `u` is the lexicographically smallest clause of `E`
(comparing item values in item order) with `v(S) = u(S)`. -/
def IsXOSClauseResponse {d : ℕ} (E : XOSExpr d) (p : Fin d → ℝ≥0∞)
    (r : Finset (Fin d) × (Fin d → ℝ)) : Prop :=
  r.1 = demandSet E.val p ∧ r.2 ∈ E.clauses ∧ ∑ x ∈ r.1, r.2 x = E.val r.1 ∧
    ∀ w ∈ E.clauses, ∑ x ∈ r.1, w x = E.val r.1 → toLex r.2 ≤ toLex w

end PostedPriceLimits.FullRevelation


