-- Prove2me | Definitions.Def_SchoolChoice_TTCQuota_Model
-- name    : SchoolChoice_TTCQuota_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T07:53:04.917615+00:00
-- url     : https://prove2.me/theorems/f07a06f7-7859-43fc-85b5-d90ee912a7aa
-- title:
--   School choice with student types: strict preferences, strict priorities, controlled choice constraints, constrained efficiency
-- statement:
--   This file fixes the primitives of a school choice problem with **controlled choice constraints** in the sense of Abdulkadiroğlu and Sönmez.
--
--   There is a finite set $I$ of students, a finite set $S$ of schools and a finite set of student types; each student $i$ belongs to exactly one type $\tau(i)$. Each school $s$ has a capacity $q_s\in\mathbb N$ and, for each type $t$, a type-specific quota $q_s^t\in\mathbb N$.
--
--   1. A **strict preference** of a student over all schools is a ranking $p : S \to \{0,\dots,|S|-1\}$ that is a bijection; rank $0$ is the favourite. School $a$ is weakly preferred to $b$ when $p(a)\le p(b)$ and strictly preferred when $p(a)<p(b)$. Ties are impossible and every school is ranked.
--   2. A **strict priority ordering** of a school over all students is, likewise, a bijective ranking $r : I \to \{0,\dots,|I|-1\}$; rank $0$ is the highest priority.
--   3. An **assignment** is a map $\nu : I \to S\cup\{\varnothing\}$, where $\nu(i)=\varnothing$ means that $i$ receives no school. Its value to student $i$ is compared through the extended rank
--   $$\bar p(s) = p(s)\ \ (s\in S),\qquad \bar p(\varnothing) = |S|,$$
--   so that receiving no school is strictly worse than every school.
--   4. An assignment $\nu$ **satisfies the controlled choice constraints** when for every school $s$ and type $t$
--   $$\#\{i : \nu(i)=s\}\le q_s,\qquad \#\{i : \nu(i)=s,\ \tau(i)=t\}\le q_s^t .$$
--   5. An assignment $\mu$ is **constrained efficient** with respect to a preference profile $P=(P_i)_{i\in I}$ when it satisfies the controlled choice constraints and there is no other assignment $\nu$ satisfying them with $\bar P_i(\nu(i))\le \bar P_i(\mu(i))$ for every $i$ and $\bar P_i(\nu(i))<\bar P_i(\mu(i))$ for some $i$.
--
--   These are the objects in terms of which Propositions 6 and 7 of the paper are stated.
--
--   **Formalization Note** The paper's matchings assign a school to every student. Here assignments may leave a student unassigned ($\varnothing$, ranked below every school), because the modified algorithm, under the convention adopted in this mission for a gap in the paper, can leave a student with no school. When the compared assignment $\mu$ assigns every student, a competitor $\nu$ that weakly improves every student must also assign every student, so the definition then agrees with the paper's notion over matchings. No relation between $q_s$ and $q_s^t$ is imposed.
-- source:
--   Abdulkadiroğlu and Sönmez, School Choice: A Mechanism Design Approach, Columbia Univ. Economics Discussion Paper No. 0203-18 (July 2003), p. 8, Section I (model); p. 19, Section III.A (types); pp. 22–23, Section III.B (constrained efficiency)

import Mathlib

namespace SchoolChoice.TTCQuota

/-- A strict preference of a student over all schools, encoded as a ranking:
`p s` is the rank of school `s`, rank `0` is the favourite. Since `p` is a bijection
onto `Fin (card S)`, ties are impossible and every school is ranked
(Abdulkadiroğlu–Sönmez 2003, Section I, p. 8). "`a` is weakly preferred to `b`"
is `p a ≤ p b`; "`a` is strictly preferred to `b`" is `p a < p b`. -/
abbrev Pref (S : Type) [Fintype S] : Type := S ≃ Fin (Fintype.card S)

/-- A strict priority ordering of a school over all students, encoded as a ranking:
`r i` is the rank of student `i`, rank `0` is the highest priority (Section I, p. 8). -/
abbrev Priority (I : Type) [Fintype I] : Type := I ≃ Fin (Fintype.card I)

variable {I S Ty : Type} [Fintype I] [DecidableEq I] [Fintype S] [DecidableEq S]
  [Fintype Ty] [DecidableEq Ty]

/-- The rank of a possibly empty assignment `o : Option S` under the preference `p`:
`some s` has rank `p s < card S`, and `none` (no school) has rank `card S`, so being
unassigned is strictly worse than every school. "`a` is weakly better than `b`" is
`orank p a ≤ orank p b`, "strictly better" is `orank p a < orank p b`. -/
def orank (p : Pref S) : Option S → ℕ
  | some s => (p s : ℕ)
  | none => Fintype.card S

/-- The controlled choice constraints (Section III, pp. 19–22) for a (possibly partial)
assignment `ν : I → Option S` of schools to students, where `τ i` is the type of student
`i`, `q s` is the capacity of school `s` and `qt s t` is the quota of school `s` for
students of type `t`: every school `s` is assigned to at most `q s` students, and to at
most `qt s t` students of each type `t`. -/
def SatisfiesCC (q : S → ℕ) (qt : S → Ty → ℕ) (τ : I → Ty) (ν : I → Option S) : Prop :=
  ∀ s, (Finset.univ.filter (fun i => ν i = some s)).card ≤ q s ∧
    ∀ t, (Finset.univ.filter (fun i => ν i = some s ∧ τ i = t)).card ≤ qt s t

/-- Constrained efficiency (Section III.B, pp. 22–23) of an assignment `μ` with respect to
the preference profile `P`: `μ` satisfies the controlled choice constraints, and there is
no other assignment `ν` satisfying them which assigns every student a weakly better
school and at least one student a strictly better school (being unassigned, `none`, is
worse than every school). -/
def IsConstrainedEfficient (q : S → ℕ) (qt : S → Ty → ℕ) (τ : I → Ty) (P : I → Pref S)
    (μ : I → Option S) : Prop :=
  SatisfiesCC q qt τ μ ∧
    ¬ ∃ ν : I → Option S, SatisfiesCC q qt τ ν ∧
      (∀ i, orank (P i) (ν i) ≤ orank (P i) (μ i)) ∧ ∃ i, orank (P i) (ν i) < orank (P i) (μ i)

end SchoolChoice.TTCQuota


