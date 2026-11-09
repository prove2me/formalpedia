-- Prove2me | Definitions.Def_MinCostMaj_Struct
-- name    : MinCostMaj_Struct
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T06:06:05.331201+00:00
-- url     : https://prove2.me/theorems/5f6257fc-3b89-4405-9150-bf5607a0bb0c
-- title:
--   Finite relational structure $\mathbf A=(A;R_1,\dots,R_p)$
-- statement:
--   A **finite relational structure** $\mathbf A=(A;R_1,\dots,R_p)$ consists of a finite domain $A$ and finitely many relations $R_i\subseteq A^{m_i}$, where $m_i=\mathrm{ar}(R_i)$ is the arity of $R_i$.
--
--   The structure is the template of the constraint problems of the mission: constraints of an instance of $\mathrm{MinCostCSP}(\mathbf A)$ apply the relations $R_i$ to tuples of variables.
--
--   **Formalization Note** The domain is $\{0,\dots,d-1\}$ (`Fin d`); every finite set is in bijection with such a set. The number of relations and their arities are arbitrary, including arity $0$ and arities larger than $2$.
-- source:
--   Kozik, Živný, Constant-factor approximation of MinCostCSP with a conservative majority polymorphism, arXiv:2607.10667 (held version, sha256 ec17e13c…), §2 Preliminaries, p.5 (PDF p.6)

import Mathlib

namespace MinCostMaj

/-- **Finite relational structure** `A = (A; R₁, …, R_p)`.

Kozik, Živný, *Constant-factor approximation of MinCostCSP with a conservative majority
polymorphism*, arXiv:2607.10667, §2 "Preliminaries", p.5: "We call R ⊆ A^m a relation on A of
arity m = ar(R) … A relational structure A = (A; R1, . . . , Rp) is a collection of relations Ri,
1 ≤ i ≤ p, on the same domain A. … All relational structures in this paper are finite."

`p` relations; relation `i` has arity `ar i` and is a set of tuples `Fin (ar i) → Fin d`.

**Formalization Note.** The finite domain is `Fin d` (every finite set is in bijection with one).
Any number of relations and any arities (including `0` and arities `> 2`) are allowed. -/
structure Struct (d : ℕ) where
  /-- number of relations -/
  p : ℕ
  /-- arity of each relation -/
  ar : Fin p → ℕ
  /-- the relations -/
  rel : (i : Fin p) → Set (Fin (ar i) → Fin d)

end MinCostMaj


