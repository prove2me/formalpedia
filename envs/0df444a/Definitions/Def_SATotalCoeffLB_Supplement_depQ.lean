-- Prove2me | Definitions.Def_SATotalCoeffLB_Supplement_depQ
-- name    : SATotalCoeffLB_Supplement_depQ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:28:40.005789+00:00
-- url     : https://prove2.me/theorems/32a2e4cc-9e6d-449b-af7a-75fb496e1f41
-- title:
--   $\mathrm{Dep}(a)$ without extension variables: the $Q$-variables appearing in $a$
-- statement:
--   Let $W$ and $Q$ be finite, disjoint sets of variables ($Q$ the random variables), and let $a$ be an element of the Boolean quotient ring $\mathbb R[W, Q]/\langle y^2 - 1 : y \in W \cup Q\rangle$. Without extension variables, $\mathrm{Dep}(a) \subseteq Q$ is the set of variables $q_j \in Q$ that **appear in** $a$: those for which some monomial containing $q_j$ has a nonzero coefficient in the multilinear representative of $a$.
--
--   **Formalization Note** The variable set $W \cup Q$ is the disjoint sum `W ⊕ Q`, and coefficients are the published multilinear coefficients `SATotalCoeffLB.coeff`.
-- source:
--   Chen–Jin, Non-signaling PCPs as Algebraic Proofs, and Total Coefficients Lower Bounds for Sherali–Adams, STOC 2027 submission (manuscript sha256 da19ece6…9d9178), p.6 (Averaging kernel); Appendix D, p.74

import Mathlib
import Definitions.Def_SATotalCoeffLB_coeff

namespace SATotalCoeffLB.Supplement

open SATotalCoeffLB

/-- **`Dep(a)` without extension variables**: for `a` in the Boolean quotient ring over the
variables `W ∪ Q`, the set of random variables `q_j ∈ Q` that appear in `a`, i.e. occur in some
monomial with a nonzero coefficient of the multilinear representative of `a` (p.6 and Appendix D,
p.74: "Without extension variables, Dep(a) is the set of variables of Q that appear in a", of
Chen–Jin, *Non-signaling PCPs as Algebraic Proofs, and Total Coefficients Lower Bounds for
Sherali–Adams*, STOC 2027 submission manuscript
(sha256 da19ece6898e20b159d01408327de710d69219772cc1f088c80301a6679d9178)).

**Formalization Note** The variable set `W ∪ Q` is the disjoint sum `W ⊕ Q`; `q_j` is
`Sum.inr j`. -/
def depQ {W Q : Type*} [Fintype W] [Fintype Q] [DecidableEq W] [DecidableEq Q]
    (a : CubeFn (W ⊕ Q)) : Set Q :=
  {j | ∃ S : Finset (W ⊕ Q), Sum.inr j ∈ S ∧ coeff a S ≠ 0}

end SATotalCoeffLB.Supplement


