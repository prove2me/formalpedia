-- Prove2me | Definitions.Def_MinCostMaj_normBin
-- name    : MinCostMaj_normBin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T06:15:25.742298+00:00
-- url     : https://prove2.me/theorems/fb120227-9566-4243-b7c9-fcf6ab8187dd
-- title:
--   The normalized structure and the two sides of the combinatorial condition
-- statement:
--   Starting from a finite structure $\mathbf A$ with a conservative majority polymorphism, §3 first adds all unary relations, then all binary relations pp-definable from the result, and keeps only binary relations, a unary relation $U$ being represented by the diagonal $\{(a,a):a\in U\}$. The **normalized structure** is thus the set of binary relations on $A$ that are primitive-positively definable from the relations of $\mathbf A$ together with all unary relations on $A$. An instance is **over the normalized structure** if all its constraints are such relations.
--
--   - The **hard-side condition** holds if there is an ac-leq-cycle pair $(I,J)$ of instances over the normalized structure, on a finite set of variables, such that $I$ has no solution.
--   - The **tractable-side condition** holds if for every such pair $(I,J)$ the instance $I$ has a solution. It is the negation of the hard-side condition.
--
--   Theorem 3.2 shows that these two conditions separate the two alternatives of the main theorem.
--
--   **Formalization Note** pp-definability is the published `FunctionAlgebras.PPFormula` with `PPFormula.toRel`. The binary projections of the relations of $\mathbf A$ and the diagonals of unary relations are pp-definable, so the set is the normalized structure of §3. Instances follow the opposite-readings convention.
-- source:
--   Kozik, Živný, Constant-factor approximation of MinCostCSP with a conservative majority polymorphism, arXiv:2607.10667 (held version, sha256 ec17e13c…), §3, pp.5–6, and Theorem 3.2, p.6 (PDF pp.6–7)

import Mathlib
import Definitions.Def_FunctionAlgebras_defs
import Definitions.Def_MinCostMaj_Struct
import Definitions.Def_MinCostMaj_BinInst
import Definitions.Def_MinCostMaj_Pattern

namespace MinCostMaj

/-- The relations of `A` together with **all** unary relations on the domain, as a family of
relations by arity (the expansion of §3, p.5: "We first add all unary relations"). -/
def expRels {d : ℕ} (A : Struct d) : ∀ h : ℕ, Set (Set (Fin h → Fin d)) :=
  fun h => {R | (∃ (i : Fin A.p) (e : A.ar i = h),
      ∀ t : Fin h → Fin d, t ∈ R ↔ (fun j => t (Fin.cast e j)) ∈ A.rel i) ∨ h = 1}

/-- **The normalized structure** (§3, pp.5–6): the binary relations primitive-positively
definable from `A` expanded by all unary relations.

Kozik, Živný, *Constant-factor approximation of MinCostCSP with a conservative majority
polymorphism*, arXiv:2607.10667, §3, pp.5–6: "We first add all unary relations and then all binary
relations pp-definable over the resulting structure. … we can replace every relation in A by its
binary projections … We replace A with this equivalent structure and, from this point on, assume
that all relations in A are binary, representing each unary relation U by the diagonal binary
relation {(a, a) : a ∈ U}."

**Formalization Note.** pp-definability is the published `FunctionAlgebras.PPFormula` /
`PPFormula.toRel` (relational atoms, equality atoms, existential variables). The binary
projections of the relations of `A` and the diagonals of unary relations are pp-definable, so this
set is exactly the relations of the normalized structure. -/
def normBin {d : ℕ} (A : Struct d) : Set (Set (Fin d × Fin d)) :=
  {R | ∃ φ : FunctionAlgebras.PPFormula (expRels A) 2,
    ∀ a b : Fin d, (a, b) ∈ R ↔ ![a, b] ∈ φ.toRel}

/-- An instance of CSP over the normalized structure: every constraint is in `normBin A`. -/
def OverNorm {d : ℕ} {V : Type*} (A : Struct d) (I : BinInst V (Fin d)) : Prop :=
  ∀ u v, I.rels u v ⊆ normBin A

/-- **The hard-side condition of Theorem 3.2** (p.6): "there exists an ac-leq-cycle pair (I, J)
such that I has no solution", with `I`, `J` instances of CSP over the normalized structure on a
finite variable set `Fin n`. -/
def HardCond {d : ℕ} (A : Struct d) : Prop :=
  ∃ (n : ℕ) (I J : BinInst (Fin n) (Fin d)),
    I.IsSymm ∧ J.IsSymm ∧ OverNorm A I ∧ OverNorm A J ∧ I.AcLeqCycle J ∧
      ¬ ∃ α : Fin n → Fin d, I.IsSolution α

/-- **The tractable-side condition of Theorem 3.2** (p.6): "for every ac-leq-cycle pair (I, J),
the instance I has a solution" (instances over the normalized structure on a finite variable set
`Fin n`). It is the negation of `HardCond`. -/
def TractCond {d : ℕ} (A : Struct d) : Prop :=
  ∀ (n : ℕ) (I J : BinInst (Fin n) (Fin d)),
    I.IsSymm → J.IsSymm → OverNorm A I → OverNorm A J → I.AcLeqCycle J →
      ∃ α : Fin n → Fin d, I.IsSolution α

end MinCostMaj


