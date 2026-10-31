-- Prove2me | Definitions.Def_CongestionApproxPNE_IsPolyGame
-- name    : CongestionApproxPNE_IsPolyGame
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:15:56.924429+00:00
-- url     : https://prove2.me/theorems/b0dba149-62f1-4828-85ac-0f8387893280
-- title:
--   Polynomial congestion game of degree $d$
-- statement:
--   A congestion game is a **polynomial congestion game of degree $d$** ($d$ a nonnegative integer) if every resource cost $c_e$ is a polynomial of degree at most $d$ with nonnegative coefficients:
--
--   $$
--   c_e(x)=\sum_{j=0}^{d} a_{e,j}\,x^j,\qquad a_{e,j}\ge 0 .
--   $$
--
--   Such costs are automatically nonnegative and nondecreasing on loads $x\ge 0$, as the model of §2 requires. Theorem 1 is a statement about this class.
--
--   **Formalization Note** Costs are functions of the load $x\in\mathbb R_{\ge 0}$ (the paper's domain is $\mathbb R_{>0}$); the polynomial must agree with the cost at every $x\ge 0$. The value at load $0$ never enters a player's cost, since a resource she uses carries at least her positive weight.
-- source:
--   Christodoulou et al., Existence and Complexity of Approximate Equilibria in Weighted Congestion Games, arXiv:2002.07466v3, §2, p.3 (PDF p.4), definition of a polynomial congestion game of degree d

import Mathlib
import Definitions.Def_HarksKlimm_Consistency_Game

set_option autoImplicit false
open scoped NNReal

namespace CongestionApproxPNE

open HarksKlimm.Consistency

/-- **Polynomial congestion game of degree `d`.**
Christodoulou, Gairing, Giannakopoulos, Poças, Waldmann, arXiv:2002.07466v3, §2, p.3: "A
polynomial congestion game of degree d, for d a nonnegative integer, is a congestion game such that
all its cost functions are polynomials of degree at most d with nonnegative coefficients."

Every resource cost `c_f` agrees with a real polynomial `P` of degree at most `d` whose
coefficients are all nonnegative.

**Formalization Note** Costs are functions of the load `x ∈ ℝ≥0` (the paper's domain is `ℝ>0`);
the agreement is required at every `x ≥ 0`, which is at least as restrictive as on `ℝ>0`. The
value at load `0` never enters a player's cost (a resource a player uses carries at least her
positive weight). Nondecreasing and nonnegative costs (p.3) follow from nonnegative coefficients
and are not separate conditions. -/
def IsPolyGame {n m : ℕ} (d : ℕ) (G : Game n m) : Prop :=
  ∀ f : Fin m, ∃ P : Polynomial ℝ, P.natDegree ≤ d ∧ (∀ j, 0 ≤ P.coeff j) ∧
    ∀ x : ℝ≥0, G.cost f x = P.eval (x : ℝ)

end CongestionApproxPNE


