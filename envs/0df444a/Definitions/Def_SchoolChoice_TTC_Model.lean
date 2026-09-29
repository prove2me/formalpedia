-- Prove2me | Definitions.Def_SchoolChoice_TTC_Model
-- name    : SchoolChoice_TTC_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T07:14:01.372991+00:00
-- url     : https://prove2.me/theorems/db7fe3aa-9874-43b8-87fb-3d7989583618
-- title:
--   School choice problem: strict preferences, strict priorities, matchings, Pareto efficiency
-- statement:
--   This file fixes the primitives of a **school choice problem** in the sense of Abdulkadiroğlu and Sönmez.
--
--   There is a finite set $I$ of students and a finite set $S$ of schools. Each school $s$ has a capacity $q_s\in\mathbb N$.
--
--   1. A **strict preference** of a student over all schools is a ranking $p : S \to \{0,\dots,|S|-1\}$ that is a bijection; rank $0$ is the student's favourite school. School $a$ is weakly preferred to $b$ when $p(a)\le p(b)$ and strictly preferred when $p(a)<p(b)$. Ties are impossible and every school is ranked (every school is acceptable).
--   2. A **strict priority ordering** of a school over all students is, likewise, a bijective ranking $r : I \to \{0,\dots,|I|-1\}$; rank $0$ is the student with the highest priority.
--   3. A **matching** is a map $\mu : I \to S$ assigning each student exactly one school such that no school exceeds its capacity:
--   $$\#\{i\in I : \mu(i)=s\}\le q_s \qquad\text{for every } s\in S.$$
--   4. A matching $\mu$ is **Pareto efficient** with respect to a preference profile $P=(P_i)_{i\in I}$ if there is no other matching $\nu$ with
--   $$P_i(\nu(i))\le P_i(\mu(i))\ \text{ for all } i \qquad\text{and}\qquad P_j(\nu(j))< P_j(\mu(j))\ \text{ for some } j,$$
--   i.e. no other matching assigns each student a weakly better school and at least one student a strictly better school.
--
--   These are the objects in terms of which Propositions 3 and 4 of the paper are stated.
--
--   **Formalization Note** Preferences and priorities are encoded as bijections onto `Fin`, so strictness and completeness hold by construction. The competitor $\nu$ in Pareto efficiency ranges over capacity-respecting matchings only, as in the paper.
-- source:
--   Abdulkadiroğlu and Sönmez, School Choice: A Mechanism Design Approach, Columbia Univ. Economics Discussion Paper No. 0203-18 (July 2003), p. 8, Section I (model, matching, Pareto efficiency)

import Mathlib

namespace SchoolChoice.TTC

/-- A strict preference of a student over all schools, encoded as a ranking:
`p s` is the rank of school `s`, rank `0` is the favourite. Since `p` is a bijection
onto `Fin (card S)`, ties are impossible and every school is ranked
(Abdulkadiroğlu–Sönmez 2003, Section I, p. 8). "`a` is weakly preferred to `b`"
is `p a ≤ p b`; "`a` is strictly preferred to `b`" is `p a < p b`. -/
abbrev Pref (S : Type) [Fintype S] : Type := S ≃ Fin (Fintype.card S)

/-- A strict priority ordering of a school over all students, encoded as a ranking:
`r i` is the rank of student `i`, rank `0` is the highest priority (Section I, p. 8). -/
abbrev Priority (I : Type) [Fintype I] : Type := I ≃ Fin (Fintype.card I)

variable {I S : Type} [Fintype I] [DecidableEq I] [Fintype S] [DecidableEq S]

/-- A matching (Section I, p. 8): every student is assigned exactly one school
(`μ : I → S`) and no school `s` is assigned to more students than its capacity `q s`. -/
def IsMatching (q : S → ℕ) (μ : I → S) : Prop :=
  ∀ s, (Finset.univ.filter (fun i => μ i = s)).card ≤ q s

/-- Pareto efficiency of a matching `μ` with respect to the preference profile `P`
(Section I, p. 8): there is no other matching `ν` (capacity-respecting) that assigns
every student a weakly better school and at least one student a strictly better school. -/
def IsParetoEfficient (q : S → ℕ) (P : I → Pref S) (μ : I → S) : Prop :=
  ¬ ∃ ν : I → S, IsMatching q ν ∧ (∀ i, P i (ν i) ≤ P i (μ i)) ∧ ∃ i, P i (ν i) < P i (μ i)

end SchoolChoice.TTC


