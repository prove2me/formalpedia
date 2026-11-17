-- Prove2me | Definitions.Def_PhyloCSP_Supplement_Algorithms
-- name    : PhyloCSP_Supplement_Algorithms
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T12:23:51.913617+00:00
-- url     : https://prove2.me/theorems/ad503f01-a41f-4171-a789-2961713d8cff
-- title:
--   Polynomial tractability, and randomized polynomial-time approximation on completely satisfiable instances
-- statement:
--   Fix a constraint language $\Pi$; instances are read in the binary code of `Encoding`, and machines are Mathlib's multi-stack Turing machines with a polynomial time bound in the input length.
--
--   1. $\mathrm{CSP}(\Pi)$ is **polynomially tractable** if a single deterministic polynomial-time machine maps the code of every instance $I$ to (the code of) a solution satisfying all constraints of $I$ when $I$ is completely satisfiable, and to the empty word when it is not. This is the notion of p.2: "a polynomial-time algorithm that distinguishes satisfiable from unsatisfiable instances and finds a solution satisfying all constraints whenever the instance is satisfiable"; one machine handles the whole language.
--   2. $\mathrm{CSP}(\Pi)$ **admits a randomized polynomial-time approximation with guarantee $\alpha$ on completely satisfiable instances** if there are a polynomial $p$ and a deterministic polynomial-time machine $A$ reading an instance $I$ and a seed $s\in\{0,1\}^m$, $m=p(|\mathrm{code}(I)|)$, such that for every instance $I$:
--      1. for every seed, $A(I,s)$ is either the empty word (failure) or the output word of a solution $T_s$ on the variables of $I$;
--      2. at least half of the $2^m$ seeds succeed;
--      3. if $I$ is completely satisfiable, then, for $s$ uniform among the successful seeds,
--      $$
--      \mathbb E\big[\mathrm{sat}(I,T_s)\big]\ \ge\ \alpha\cdot\#\text{constraints of }I .
--      $$
--      The algorithm runs $A$ with fresh seeds until it succeeds; its output has exactly this conditional law and its expected running time is at most twice a polynomial.
--
--   **Formalization Note** The paper fixes no model of randomized computation. Allowing failure (rejection) lets the algorithm sample exactly the uniform random permutations ("At each edge labeled u, we sample a uniformly random permutation", proof of Theorem 6.2) and rational mixture weights its transformations use; a worst-case seeded machine without failures could only produce dyadic probabilities. The guarantee is stated for the expected number of satisfied constraints, i.e. the expected value of Proposition 1.7 times the number of constraints, which needs no special case for instances without constraints.
-- source:
--   Makarychev, Approximation Algorithms for Satisfiable Phylogenetic CSPs, STOC 2027 submission (manuscript sha256 3444b6c029bce73ce9a6ad0ae6bc8386c291dcb0b1e504e8216c60cd4d682dac), Section 1, p.2 (PDF p.4); Proposition 1.7, p.5 (PDF p.7); Theorem 6.2 and its proof, p.16 (PDF p.18); Appendix A, p.44 (PDF p.46)

import Mathlib
import Definitions.Def_PhyloCSP_Supplement_Encoding

set_option autoImplicit false

namespace PhyloCSP

namespace Supplement

/-- **Polynomial tractability of `CSP(Π)`.**

Makarychev, *Approximation Algorithms for Satisfiable Phylogenetic CSPs*, STOC 2027 submission
(manuscript sha256 3444b6c0…682dac), Section 1, p.2 (PDF p.4): "There is a polynomial-time
algorithm that distinguishes satisfiable from unsatisfiable instances and finds a solution
satisfying all constraints whenever the instance is satisfiable. Accordingly, we refer to
phylogenetic CSPs as either NP-hard or polynomially tractable." Appendix A, p.44 (PDF p.46):
"Importantly, the algorithm handles all the split predicates together, so this proves tractability
of the whole constraint language."

`CSP(L)` is polynomially tractable if one deterministic polynomial-time machine (Mathlib's
multi-stack Turing machine `Turing.TM2ComputableInPolyTime`) maps the code of every instance `I`
of `CSP(L)` to `treeWord T` for a solution `T` satisfying all constraints of `I` when `I` is
completely satisfiable, and to the empty word otherwise.

**Formalization Note.** Instances are read in the code `encInstance` (number of variables in
unary); the output is over the alphabet `Bool`. -/
def IsPolyTractable (L : ConstraintLanguage) : Prop :=
  ∃ A : Instance L → List Bool,
    Nonempty (Turing.TM2ComputableInPolyTime (encInstance (L := L)) id A) ∧
    ∀ I : Instance L,
      (CompletelySatisfiable I →
        ∃ T : Pattern (Fin I.n), (∀ c ∈ I.constraints, Satisfies I T c) ∧ A I = treeWord T) ∧
      (¬ CompletelySatisfiable I → A I = [])

/-- The input of a seeded run: the instance code and the seed, over `Option Bool` with `none` as
separator. -/
noncomputable def seededInput {L : ConstraintLanguage} (q : Instance L × List Bool) :
    List (Option Bool) :=
  (encInstance q.1).map some ++ [none] ++ q.2.map some

open Classical in
/-- **A randomized polynomial-time approximation with expected guarantee `α` on completely
satisfiable instances.**

Makarychev, *Approximation Algorithms for Satisfiable Phylogenetic CSPs*, STOC 2027 submission
(manuscript sha256 3444b6c0…682dac), Proposition 1.7, p.5 (PDF p.7): "Given a completely
satisfiable instance of CSP(Π), the algorithm above finds a solution of expected value at least
p(Π, F). If we can sample the output of F in polynomial time, then the algorithm runs in polynomial
time." Theorem 6.2, p.16 (PDF p.18): "admits, on completely satisfiable instances, a randomized
polynomial-time approximation with the indicated guarantee"; proof: "At each edge labeled u, we
sample a uniformly random permutation of the assigned leaves."

A randomized algorithm is a deterministic polynomial-time machine `A` that reads an instance `I`
together with a uniformly random seed of `m = p(|enc I|)` bits and outputs either a tree
(`treeWord T`) or the empty word (failure); the algorithm repeats with fresh seeds until it does
not fail. Required, for every instance `I`:

1. every seed gives a failure or a tree on the variables of `I`;
2. at least half of the `2^m` seeds succeed;
3. if `I` is completely satisfiable, the expected number of satisfied constraints of the output,
   conditional on success (that is, the output law of the repeated algorithm), is at least
   `α · (number of constraints)`:
   `α · |constraints| · #successful seeds ≤ Σ_{successful seeds} (constraints satisfied by the
   output)`.

**Formalization Note.** The paper fixes no machine model. This is a Las Vegas algorithm with
expected running time at most twice a polynomial, whose output law is the uniform seed law
conditioned on success; rejection lets it sample exactly the uniform permutations and rational
mixture weights the paper's transformations use (a probability `1/3!` is not a dyadic rational, so
a worst-case seeded machine without failures could not). Expected *value* is stated as expected
number of satisfied constraints, which is the expected value times the number of constraints and
needs no special case for an instance without constraints. -/
def RandApproxOnSat (L : ConstraintLanguage) (α : ℝ) : Prop :=
  ∃ (A : Instance L × List Bool → List Bool) (p : Polynomial ℕ),
    Nonempty (Turing.TM2ComputableInPolyTime (seededInput (L := L)) id A) ∧
    ∀ I : Instance L,
      (∀ s : Fin (p.eval (encInstance I).length) → Bool,
        A (I, List.ofFn s) = [] ∨ ∃ T : Pattern (Fin I.n), A (I, List.ofFn s) = treeWord T) ∧
      2 ^ (p.eval (encInstance I).length) ≤
        2 * (Finset.univ.filter (fun s : Fin (p.eval (encInstance I).length) → Bool =>
          A (I, List.ofFn s) ≠ [])).card ∧
      (CompletelySatisfiable I →
        α * (I.constraints.length : ℝ) *
            ((Finset.univ.filter (fun s : Fin (p.eval (encInstance I).length) → Bool =>
              A (I, List.ofFn s) ≠ [])).card : ℝ) ≤
          ∑ s : Fin (p.eval (encInstance I).length) → Bool, ∑ T : Pattern (Fin I.n),
            if A (I, List.ofFn s) = treeWord T then (satCount I T : ℝ) else 0)

end Supplement

end PhyloCSP


