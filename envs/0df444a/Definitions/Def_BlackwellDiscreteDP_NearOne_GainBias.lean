-- Prove2me | Definitions.Def_BlackwellDiscreteDP_NearOne_GainBias
-- name    : BlackwellDiscreteDP_NearOne_GainBias
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T18:04:29.922976+00:00
-- url     : https://prove2.me/theorems/8ead0d2b-081c-4453-ac18-8d5213f392c4
-- title:
--   Q*(f), H(f), x(f) = Q*(f)r(f), y(f) = H(f)r(f) and the §4 sets G(s, f), E(s, f)
-- statement:
--   This file defines the quantities of Blackwell's Theorem 4 for a decision rule $f\in F$ of the finite model of §2.
--
--   1. $Q^*(f)$ is the limit matrix $Q^*$ of the Markov matrix $Q(f)$, and $H(f)=(I-Q(f)+Q^*(f))^{-1}-Q^*(f)$ its deviation matrix.
--   2. $x(f)=Q^*(f)\,r(f)$, the long-run average income of $f^{(\infty)}$ from each initial state.
--   3. $y(f)=H(f)\,r(f)$, the bias of $f^{(\infty)}$.
--   4. For a state $s$, $G(s,f)$ is the set of actions $a$ for which either
--   $$p(s,a)x(f)>x_s(f)\quad\text{or}\quad p(s,a)x(f)=x_s(f)\ \text{and}\ i(s,a)+p(s,a)y(f)>x_s(f)+y_s(f),$$
--   where $p(s,a)w=\sum_{s'}q(s'\mid s,a)\,w_{s'}$ and $x_s(f),y_s(f)$ are the $s$th coordinates.
--   5. $E(s,f)$ is the set of actions $a$ with $p(s,a)x(f)=x_s(f)$ and $i(s,a)+p(s,a)y(f)=x_s(f)+y_s(f)$.
--
--   $G(s,f)$ is the improvement set of the policy improvement routine for $\beta=1$, and $E(s,f)$ the set of actions that tie with $f(s)$ to the first two orders as $\beta\to1$.
--
--   **Formalization Note** The paper defines $x(f)$ and $y(f)$ as the unique solutions of the linear systems of Theorem 4(a); its proof of (a) identifies them as $Q^*(f)r(f)$ and $H(f)r(f)$. These closed forms are taken as definitions, and the theorem formalizing Theorem 4(a) asserts that they are exactly the solutions of the two systems. The §4 set $G(s,f)$ involves no discount factor and is named `gainBiasImprovementSet`, distinct from Theorem 3's `betaImprovementSet`.
-- source:
--   Blackwell, Discrete Dynamic Programming, Ann. Math. Statist. 33(2):719–726 (1962), DOI 10.1214/aoms/1177704593, pp. 722–723, Theorem 4(a)–(c) and proof of (a)

import Mathlib
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_BlackwellDiscreteDP_NearOne_Model
open Filter Topology Matrix

namespace BlackwellDiscreteDP.NearOne

namespace Model

variable {St Act : Type*} [Fintype St] [DecidableEq St] (M : Model St Act)

/-- `Q*(f)`: the limit matrix `Q*` associated with `Q(f)`. Blackwell (1962), p. 722,
Theorem 4. -/
noncomputable def Qstar (f : St → Act) : Matrix St St ℝ := limitMatrix (M.Q f)

/-- `H(f)`: the matrix `H = (I − Q(f) + Q*(f))⁻¹ − Q*(f)` of Lemma 1(d) associated with `Q(f)`.
Blackwell (1962), p. 723, proof of Theorem 4(a). -/
noncomputable def Hf (f : St → Act) : Matrix St St ℝ := deviationMatrix (M.Q f)

/-- `x(f) = Q*(f) r(f)` (the gain, or average income, of `f^(∞)`).

Blackwell (1962), p. 722, Theorem 4(a), and p. 723, proof of (a).

**Formalization Note.** The paper defines `x(f)` as the unique solution of
`(I − Q(f))x = 0, Q*(f)x = Q*(f)r(f)`; its proof of (a) identifies it as `Q*(f)r(f)`. The
closed form is taken as the definition, and the theorem formalizing Theorem 4(a) asserts that it
is the unique solution of that system. -/
noncomputable def x (f : St → Act) : St → ℝ := M.Qstar f *ᵥ M.r f

/-- `y(f) = H(f) r(f)` (the bias of `f^(∞)`).

Blackwell (1962), p. 722, Theorem 4(a), and p. 723, proof of (a).

**Formalization Note.** The paper defines `y(f)` as the unique solution of
`(I − Q(f))y = r(f) − x(f), Q*(f)y = 0`; its proof of (a) identifies it as `H(f)r(f)`. The
closed form is taken as the definition, and the theorem formalizing Theorem 4(a) asserts that it
is the unique solution of that system. -/
noncomputable def y (f : St → Act) : St → ℝ := M.Hf f *ᵥ M.r f

/-- Theorem 4(b)'s set `G(s, f)` (no `β`): the actions `a` for which either
`p(s, a)x(f) > x_s(f)`, or `p(s, a)x(f) = x_s(f)` and
`i(s, a) + p(s, a)y(f) > x_s(f) + y_s(f)`. Blackwell (1962), pp. 722–723, Theorem 4(b).

**Formalization Note.** Distinct from Theorem 3's β-dependent `G(s, f)`
(`betaImprovementSet`). -/
def gainBiasImprovementSet (f : St → Act) (s : St) : Set Act :=
  {a | M.pDot s a (M.x f) > M.x f s ∨
        (M.pDot s a (M.x f) = M.x f s ∧ M.i s a + M.pDot s a (M.y f) > M.x f s + M.y f s)}

/-- Theorem 4(c)'s set `E(s, f)`: the actions `a` with `p(s, a)x(f) = x_s(f)` and
`i(s, a) + p(s, a)y(f) = x_s(f) + y_s(f)`. Blackwell (1962), p. 723, Theorem 4(c). -/
def gainBiasEqualSet (f : St → Act) (s : St) : Set Act :=
  {a | M.pDot s a (M.x f) = M.x f s ∧ M.i s a + M.pDot s a (M.y f) = M.x f s + M.y f s}

end Model

end BlackwellDiscreteDP.NearOne


