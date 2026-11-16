-- Prove2me | Definitions.Def_NashOrTriangle_Supplement_PMFGame
-- name    : NashOrTriangle_Supplement_PMFGame
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:47:33.018663+00:00
-- url     : https://prove2.me/theorems/d5904408-171b-47eb-a4d3-9009bcfb6fc9
-- title:
--   Countably additive mixed strategies: $M(p,q)$, $U$, $L$, $\varepsilon$-Nash equilibria and the value
-- statement:
--   Let $M:A\times B\to\mathbb Q$ be the payoff of a zero-sum game with countable strategy sets. Mixed strategies are countably additive probability distributions $p$ on $A$ and $q$ on $B$, and $M$ extends to them by taking expectations:
--   $$M(a,q)=\sum_{b}q(b)M(a,b),\qquad M(p,b)=\sum_a p(a)M(a,b),\qquad M(p,q)=\sum_a p(a)M(a,q).$$
--   Write $U(q)=\sup_{a\in A}M(a,q)$ and $L(p)=\inf_{b\in B}M(p,b)$.
--
--   1. The pair $(p,q)$ is an **$\varepsilon$-Nash equilibrium** if $U(q)-M(p,q)\le\varepsilon$ and $M(p,q)-L(p)\le\varepsilon$.
--   2. The game **has a value** if
--   $$\sup_p L(p)=\inf_q U(q),$$
--   the supremum and the infimum ranging over all countably additive mixed strategies.
--
--   On a finite game the mixed strategies are the probability vectors. These notions are used by Theorem 4.1 (equilibria of a finite game) and by Theorems B.2 and B.3 (equilibria and the value of a countable game).
--
--   **Formalization Note** Probabilities are the real parts of the probability mass functions, and the sums are infinite series. For payoffs in $[0,1]$, as in every game of the paper, the series converge and the suprema and infima are over nonempty families bounded in $[0,1]$, so they are the true ones.
-- source:
--   Daskalakis–Papadimitriou–Yannakakis, On the Complexity of Infinite Zero-Sum Games, STOC 2027 submission (manuscript sha256 4f8d0962cc2efb135d3833e902fa4e861e03acf9d2df3fe8140a50b646da66f7), §1.1, p.3 (PDF p.4)

import Mathlib

namespace NashOrTriangle.Supplement

/-!
Countably additive mixed strategies of a game `M : A → B → ℚ` (`PMF A`, `PMF B`) and the
quantities of §1.1 for them.

Source: Daskalakis–Papadimitriou–Yannakakis, *On the Complexity of Infinite Zero-Sum Games*,
STOC 2027 submission manuscript (sha256 4f8d0962…66f7), §1.1, printed p. 3 (PDF p. 4): "Mixed
strategies are countably additive probability distributions, and M extends to them by taking
expectations. … U(q) = sup_{a∈A} M(a, q), L(p) = inf_{b∈B} M(p, b) … The game has a value if
sup_p L(p) = inf_q U(q) … A pair (p, q) is a 1/k-Nash equilibrium if … U(q) − M(p, q) ≤ 1/k,
M(p, q) − L(p) ≤ 1/k."

**Formalization Note** Payoffs are cast to `ℝ` and expectations are `tsum`s against the
probabilities `(p a).toReal`. For a payoff function with values in `[0, 1]` (every game of the
paper) all these series converge absolutely and every `⨆`/`⨅` is over a nonempty family bounded in
`[0, 1]` (the strategy types are nonempty), so the junk values of `tsum`, `⨆` and `⨅` never occur.
On a finite type `PMF A` is the set of probability vectors.
-/

/-- `M(a, q) = ∑_b q(b) M(a, b)`. -/
noncomputable def pmfRow {A B : Type*} (M : A → B → ℚ) (a : A) (q : PMF B) : ℝ :=
  ∑' b, (q b).toReal * (M a b : ℝ)

/-- `M(p, b) = ∑_a p(a) M(a, b)`. -/
noncomputable def pmfCol {A B : Type*} (M : A → B → ℚ) (p : PMF A) (b : B) : ℝ :=
  ∑' a, (p a).toReal * (M a b : ℝ)

/-- `M(p, q) = ∑_a p(a) M(a, q)`. -/
noncomputable def pmfMix {A B : Type*} (M : A → B → ℚ) (p : PMF A) (q : PMF B) : ℝ :=
  ∑' a, (p a).toReal * pmfRow M a q

/-- `U(q) = sup_{a ∈ A} M(a, q)`. -/
noncomputable def pmfUpper {A B : Type*} (M : A → B → ℚ) (q : PMF B) : ℝ :=
  ⨆ a, pmfRow M a q

/-- `L(p) = inf_{b ∈ B} M(p, b)`. -/
noncomputable def pmfLower {A B : Type*} (M : A → B → ℚ) (p : PMF A) : ℝ :=
  ⨅ b, pmfCol M p b

/-- `(p, q)` is an `ε`-Nash equilibrium: `U(q) − M(p, q) ≤ ε` and `M(p, q) − L(p) ≤ ε`. -/
def IsNashPMF {A B : Type*} (M : A → B → ℚ) (ε : ℝ) (p : PMF A) (q : PMF B) : Prop :=
  pmfUpper M q - pmfMix M p q ≤ ε ∧ pmfMix M p q - pmfLower M p ≤ ε

/-- The game has a **value**: `sup_p L(p) = inf_q U(q)`, over all countably additive mixed
strategies. -/
def HasValuePMF {A B : Type*} (M : A → B → ℚ) : Prop :=
  (⨆ p : PMF A, pmfLower M p) = ⨅ q : PMF B, pmfUpper M q

end NashOrTriangle.Supplement


