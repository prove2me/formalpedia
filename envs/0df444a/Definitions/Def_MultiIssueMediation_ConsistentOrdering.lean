-- Prove2me | Definitions.Def_MultiIssueMediation_ConsistentOrdering
-- name    : MultiIssueMediation_ConsistentOrdering
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:18:33.832617+00:00
-- url     : https://prove2.me/theorems/6671dca4-1cbc-4bf7-980b-2d12c210c55d
-- title:
--   Definition 1 — consistent orderings and the extension map $\Lambda$
-- statement:
--   An ordering is a complete and transitive relation $R$ on $X\times Y$, with strict part $P$: $b\,P\,b'$ iff $b\,R\,b'$ holds and $b'\,R\,b$ does not. An ordering is **consistent** for the type $\theta_i$ of negotiator $i$ when:
--
--   1. (Monotonicity) for $(x,y)\ne(x',y')$, $(x,y)\,P_i\,(x',y')$ whenever [$x\ \theta_i^X\ x'$ or $x=x'$] and [$y\ \theta_i^Y\ y'$ or $y=y'$];
--   2. (Deal Breakers) for $y,y'\in Y\setminus\{o_Y\}$, $(x,y)\,R_i\,(x',y')$ whenever $x\in A(\theta_i)\cup\{o_X\}$, $x'\notin A(\theta_i)$ and $x\ne x'$;
--   3. (Logrolling) for all $x,x'\in A(\theta_i)$ with $x\ \theta_i\ x'$, $(x',t(x'))\,R_i\,(x,t(x))$.
--
--   The extension map assigns to a type the set $\Lambda(\theta_i)$ of all its consistent orderings.
--
--   These are the orderings over which strategy-proofness, individual rationality and efficiency quantify.
--
--   **Formalization Note** Definition 1 restricts $\Lambda$ from one side only, and Theorem 1 is false for smaller maps. The proof uses the full set (pp.28–29), so $\Lambda$ is a definition and not a parameter. The logrolling map is the fixed $t$ of Example 1. Sanity checks prove that $\Lambda(\theta_i)$ is non-empty and not a singleton.
-- source:
--   Kesten, Özyurt, Efficient and Incentive Compatible Mediation: An Ordinal Market Design Approach, working paper, 4 October 2018, Definition 1, p.13, footnote 8, p.12

import Mathlib
import Definitions.Def_MultiIssueMediation_Model

namespace MultiIssueMediation

/-- The strict counterpart `P` of an ordering `R` (working paper of 4 October 2018, p.12,
footnote 8): "`b P b'` if and only if `b R b'` holds but `b' R b` does not". -/
def StrictlyPrefers {m : ℕ} (R : Bundle m → Bundle m → Prop) (b b' : Bundle m) : Prop :=
  R b b' ∧ ¬ R b' b

/-- `R` is a complete and transitive relation on `X × Y` (p.12) satisfying conditions i, ii, iii of
Definition 1 (Kesten, Özyurt, *Efficient and Incentive Compatible Mediation: An Ordinal Market
Design Approach*, working paper, 4 October 2018, Definition 1, p.13) for the type `t` of negotiator
`i`.

**Formalization Note.** The logrolling condition uses the fixed map `logroll`,
`t(x_k) = y_{m+1−k}` (Example 1, pp.13–14), instead of "there exists a one-to-one mapping". -/
structure IsConsistentOrdering {m : ℕ} (i : Negotiator) (t : Fin m)
    (R : Bundle m → Bundle m → Prop) : Prop where
  /-- `R` is complete. -/
  complete : ∀ b b' : Bundle m, R b b' ∨ R b' b
  /-- `R` is transitive. -/
  transitive : ∀ b b' b'' : Bundle m, R b b' → R b' b'' → R b b''
  /-- Definition 1(i), Monotonicity. -/
  monotonicity : ∀ (x x' : Option (Fin m)) (y y' : Option (Fin m)), (x, y) ≠ (x', y') →
    (issueXPrefers i t x x' ∨ x = x') → (issueYPrefers i y y' ∨ y = y') →
    StrictlyPrefers R (x, y) (x', y')
  /-- Definition 1(ii), Deal Breakers, for `y, y' ∈ Y ∖ {o_Y}`. -/
  dealBreakers : ∀ (x x' : Option (Fin m)) (y y' : Option (Fin m)), y ≠ none → y' ≠ none →
    (x ∈ acceptable i t ∨ x = none) → x' ∉ acceptable i t → x ≠ x' → R (x, y) (x', y')
  /-- Definition 1(iii), Logrolling. -/
  logrolling : ∀ x x' : Option (Fin m), x ∈ acceptable i t → x' ∈ acceptable i t →
    issueXPrefers i t x x' → R (x', logroll x') (x, logroll x)

/-- The extension map `Λ`: `Λ(θ_i)` is the set of **all** consistent orderings of the type `t` of
negotiator `i` (working paper of 4 October 2018, Definition 1, p.13).

**Formalization Note.** Definition 1 restricts `Λ` from one side only. The proof of Theorem 1 uses
the maximal map ("the consistency assumption puts no restriction on how negotiators compare bundle
`b` with `c`", pp.28–29), and Theorem 1 is false for smaller maps, so `Λ` is defined and is not a
parameter. -/
def admissibleOrderings {m : ℕ} (i : Negotiator) (t : Fin m) :
    Set (Bundle m → Bundle m → Prop) :=
  {R | IsConsistentOrdering i t R}

end MultiIssueMediation


