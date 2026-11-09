-- Prove2me | Definitions.Def_RandomCNFDeficiency_LowerBound_PolynomialCalculus
-- name    : RandomCNFDeficiency_LowerBound_PolynomialCalculus
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:32:11.959191+00:00
-- url     : https://prove2.me/theorems/028a046c-5cfd-49f8-953e-fb00bf245ba8
-- title:
--   Finite ordinary polynomial calculus refutations
-- statement:
--   Fix a CNF $F$ and an arbitrary field $K$. A polynomial calculus line is an input polynomial $p_C$ for $C\in F$, a Boolean axiom $x_i^2-x_i$, a linear combination of two earlier lines, or a variable times an earlier line. A refutation is an actual finite list whose last line is one. Its degree is
--
--   $$\deg(\pi)=\max_{p\text{ a line of }\pi}\deg(p).$$
--
--   The ordinary total degree is measured before quotienting by Boolean axioms. The predicate that $F$ is hard above $D$ quantifies simultaneously over every field and every such refutation, requiring $\deg(\pi)>D$. The universe of fields is arbitrary. There is no minimum over an empty set of proofs. The module also records the three operational properties of a pseudo-reduction operator from Definition 2.3 for CNF inputs; it assumes none of their consequences.
--
--   These rules provide the proof-system interface used by the deterministic criterion and the main random event.
-- source:
--   Jonas Conneryd, STOC 2027 submission #332 (October 2026), Section 2.2, rules (7a)-(7b), and Definition 2.3, printed p. 7, PDF p. 9; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/332.pdf; printed p. 8, PDF p. 10

import Definitions.Def_RandomCNFDeficiency_LowerBound_ClauseAlgebra
set_option autoImplicit false
universe u

namespace RandomCNFDeficiency.LowerBound

/-- Exactly the two PC rules on an earlier list, plus input and Boolean axioms. -/
inductive PCStep {n : ℕ} {K : Type u} [Field K]
    (F : CNF n) (earlier : List (MvPolynomial (Fin n) K)) :
    MvPolynomial (Fin n) K → Prop
  | input (C : Clause n) (hC : C ∈ F) : PCStep F earlier (clausePolynomial C)
  | boolean (i : Fin n) : PCStep F earlier (MvPolynomial.X i ^ 2 - MvPolynomial.X i)
  | linear (p q : MvPolynomial (Fin n) K) (hp : p ∈ earlier) (hq : q ∈ earlier)
      (a b : K) : PCStep F earlier (MvPolynomial.C a * p + MvPolynomial.C b * q)
  | multiply (p : MvPolynomial (Fin n) K) (hp : p ∈ earlier) (i : Fin n) :
      PCStep F earlier (MvPolynomial.X i * p)

def IsPCRefutation {n : ℕ} {K : Type u} [Field K]
    (F : CNF n) (π : List (MvPolynomial (Fin n) K)) : Prop :=
  π.getLast? = some 1 ∧
    ∀ (j : ℕ) (p : MvPolynomial (Fin n) K),
      π[j]? = some p → PCStep F (π.take j) p

def pcDegree {n : ℕ} {K : Type u} [Field K]
    (π : List (MvPolynomial (Fin n) K)) : ℕ :=
  (π.map MvPolynomial.totalDegree).foldr max 0

/-- Simultaneously every field in an arbitrary universe, in ONE event. -/
def AllFieldsHard {n : ℕ} (F : CNF n) (D : ℝ) : Prop :=
  ∀ (K : Type u) [Field K] (π : List (MvPolynomial (Fin n) K)),
    IsPCRefutation F π → D < (pcDegree π : ℝ)

/-- Definition 2.3 specialized to CNF input, retaining all three operational clauses. -/
def IsPseudoReduction {n : ℕ} {K : Type u} [Field K]
    (F : CNF n) (D : ℕ) (R : BooleanAlgebra n K →ₗ[K] BooleanAlgebra n K) : Prop :=
  0 < D ∧ ¬ Satisfiable F ∧ R 1 = 1 ∧
    (∀ C ∈ F, R (multilinearize (clausePolynomial C)) = 0) ∧
    ∀ (S : Finset (Fin n)) (i : Fin n), S.card ≤ D - 1 →
      R (booleanMonomial ({i} ∪ S)) =
        R (booleanMonomial ({i} : Finset (Fin n)) * R (booleanMonomial S))

end RandomCNFDeficiency.LowerBound


