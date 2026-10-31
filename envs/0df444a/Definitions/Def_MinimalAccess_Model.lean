-- Prove2me | Definitions.Def_MinimalAccess_Model
-- name    : MinimalAccess_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:41:24.277323+00:00
-- url     : https://prove2.me/theorems/57f78b34-55fb-45a5-8d26-7b53f68775eb
-- title:
--   Extended school choice problems, matchings, justified max/min envy, (minimal-access) stability
-- statement:
--   An **extended school choice problem** $(I,S,q,P,\succ,r)$ consists of a finite set $I$ of students; a finite set $S$ of schools; capacities $q_s\in\mathbb N$; strict preferences $P_i$ of each student over $S\cup\{\emptyset\}$, where $\emptyset$ is the no-school option; strict (absolute) priority relations $\succ_s$ of each school over $I$; and **minimal-access rights** $r(i)\subseteq S$. Write $s\,R_i\,s'$ if $s\,P_i\,s'$ or $s=s'$; school $s$ is **acceptable** for $i$ if $s\,P_i\,\emptyset$.
--
--   A **matching** assigns each student a school or $\emptyset$ so that each school $s$ receives a set $\mu(s)$ of at most $q_s$ students. A matching $\mu$ is
--
--   1. **individually rational** if $\mu(i)\,R_i\,\emptyset$ for all $i$;
--   2. **non-wasteful** if $s\,P_i\,\mu(i)$ implies $|\mu(s)|=q_s$.
--
--   Student $i$ has **justified max envy** at $\mu$ if there are $j\in I$, $s\in S$ with $\mu(j)=s\,P_i\,\mu(i)$ and (1) $s\notin r(i)$, $s\notin r(j)$, $i\succ_s j$; or (2) $s\in r(i)$, $s\in r(j)$, $i\succ_s j$; or (3) $s\in r(i)$, $s\notin r(j)$. A matching is **stable** if it is individually rational, non-wasteful, and no student has justified max envy.
--
--   Student $i$ has **justified min envy** at $\mu$ if there are $j$, $s$ with $\mu(j)=s\,P_i\,\mu(i)$ and (1) or (2) as above, or (3a) $s\in r(i)$, $s\notin r(j)$, $i\succ_s j$; or (3b) $s\in r(i)$, $s\notin r(j)$, $j\succ_s i$, and there is no school $s'\in r(i)$ with $\mu(i)\,R_i\,s'$. A matching is **minimal-access stable** if it is individually rational, non-wasteful, and no student has justified min envy.
--
--   These are the basic objects of every statement of the mission. Minimal-access stability differs from stability only through (3b): a minimal-access right yields justified envy against a higher-priority student only if the student is not yet matched to a school at least as good as one of her minimal-access schools.
--
--   **Formalization Note** Students are `Fin n`, schools `Fin m`, and $\emptyset$ is `none`. $P_i$ is a rank bijection `Option (Fin m) ≃ Fin (m+1)` and $\succ_s$ a rank bijection `Fin n ≃ Fin n`, rank $0$ being most preferred / highest priority; so $x\,P_i\,y$ is `P i x < P i y`, $x\,R_i\,y$ is `P i x ≤ P i y`, and $i\succ_s j$ is `pri s i < pri s j`. A matching is an assignment `Fin n → Option (Fin m)` (the published `GaleShapley1962.Admissions.Assignment`) with `IsMatching q μ`; stability predicates are stated for assignments. `MaxEnvyAt`/`MinEnvyAt` are the envy relations for a fixed pair $(j,s)$.
-- source:
--   Klaus–Klijn, Minimal-Access Rights in School Choice and the Deferred Acceptance Mechanism, BSE Working Paper 1264 (rev. July 2023), §2, pp.4–5 (problem, matching, individual rationality, non-wastefulness, justified max envy, stability) and pp.7–8 (justified min envy, minimal-access stability)

import Mathlib
import Definitions.Def_GaleShapley1962_Admissions_Assignments

namespace MinimalAccess

/-!
Klaus–Klijn, *Minimal-Access Rights in School Choice and the Deferred Acceptance Mechanism*,
BSE Working Paper 1264 (rev. July 2023), §2, pp.4–5 and pp.7–8: the extended school choice
problem `(I, S, q, P, ≻, r)`, matchings, individual rationality, non-wastefulness, justified max
envy, stability, justified min envy and minimal-access stability.

**Formalization Note.** Students are `I = Fin n`, schools `S = Fin m` (a finite relabelling).
The no-school option `∅` is `none : Option (Fin m)`. A strict preference `P_i` over `S ∪ {∅}`
is a rank bijection `Option (Fin m) ≃ Fin (m + 1)` with rank `0` the most preferred, so
`x P_i y :⇔ P i x < P i y` and `x R_i y :⇔ P i x ≤ P i y` (`x P_i y` or `x = y`, by
injectivity). A strict priority `≻_s` over `I` is a rank bijection `Fin n ≃ Fin n` with rank `0`
the highest priority, so `i ≻_s j :⇔ pri s i < pri s j`. Every such bijection is a strict total
order and every strict total order is one, so there are no junk problems. A matching is an
assignment `Fin n → Option (Fin m)` (the published `GaleShapley1962.Admissions.Assignment`);
condition (iii) of p.5 holds by construction, and condition (ii) is `IsMatching`.
-/

open GaleShapley1962.Admissions

/-- A strict preference of a student over `S ∪ {∅}` (p.4), as a rank bijection
`Option (Fin m) ≃ Fin (m + 1)`; a smaller rank is more preferred and `none` is `∅`. -/
abbrev Pref (m : ℕ) := Option (Fin m) ≃ Fin (m + 1)

/-- A strict (absolute) priority relation `≻_s` of a school over the students (p.5), as a rank
bijection `Fin n ≃ Fin n`; a smaller rank is a higher priority. -/
abbrev Prio (n : ℕ) := Fin n ≃ Fin n

/-- School `s` is acceptable for student `i` (p.5): `s P_i ∅`. -/
def Acceptable {n m : ℕ} (P : Fin n → Pref m) (i : Fin n) (s : Fin m) : Prop :=
  P i (some s) < P i none

instance {n m : ℕ} (P : Fin n → Pref m) (i : Fin n) (s : Fin m) :
    Decidable (Acceptable P i s) := by
  unfold Acceptable; infer_instance

/-- `μ(s)`: the set of students matched to school `s` (p.5). -/
def schoolMatch {n m : ℕ} (μ : Assignment n m) (s : Fin m) : Finset (Fin n) :=
  Finset.univ.filter fun i => μ i = some s

/-- `μ` is a matching (p.5, condition (ii)): `|μ(s)| ≤ q_s` for every school `s`. -/
def IsMatching {n m : ℕ} (q : Fin m → ℕ) (μ : Assignment n m) : Prop :=
  ∀ s, (schoolMatch μ s).card ≤ q s

/-- Individual rationality (p.5): for all `i ∈ I`, `μ(i) R_i ∅`. -/
def IsIndividuallyRational {n m : ℕ} (P : Fin n → Pref m) (μ : Assignment n m) : Prop :=
  ∀ i, P i (μ i) ≤ P i none

/-- Non-wastefulness (p.5): for all `i ∈ I` and `s ∈ S`, `s P_i μ(i)` implies `|μ(s)| = q_s`. -/
def IsNonWasteful {n m : ℕ} (q : Fin m → ℕ) (P : Fin n → Pref m) (μ : Assignment n m) : Prop :=
  ∀ i s, P i (some s) < P i (μ i) → (schoolMatch μ s).card = q s

/-- Student `i` has justified max envy at `μ` with respect to student `j` and school `s` (p.5):
`μ(j) = s P_i μ(i)` and (1) `s ∉ r(i)`, `s ∉ r(j)`, `i ≻_s j`; or (2) `s ∈ r(i)`, `s ∈ r(j)`,
`i ≻_s j`; or (3) `s ∈ r(i)` and `s ∉ r(j)`. The priorities are the absolute ones `≻_s`. -/
def MaxEnvyAt {n m : ℕ} (P : Fin n → Pref m) (pri : Fin m → Prio n) (r : Fin n → Finset (Fin m))
    (μ : Assignment n m) (i j : Fin n) (s : Fin m) : Prop :=
  μ j = some s ∧ P i (some s) < P i (μ i) ∧
    ((s ∉ r i ∧ s ∉ r j ∧ pri s i < pri s j) ∨
      (s ∈ r i ∧ s ∈ r j ∧ pri s i < pri s j) ∨
      (s ∈ r i ∧ s ∉ r j))

/-- Student `i` has justified max envy at `μ` (p.5): there are `j ∈ I` and `s ∈ S` with
`MaxEnvyAt P pri r μ i j s`. -/
def HasJustifiedMaxEnvy {n m : ℕ} (P : Fin n → Pref m) (pri : Fin m → Prio n)
    (r : Fin n → Finset (Fin m)) (μ : Assignment n m) (i : Fin n) : Prop :=
  ∃ j s, MaxEnvyAt P pri r μ i j s

/-- Stability (p.5): `μ` is individually rational, non-wasteful, and no student has justified
max envy. (That `μ` is a matching, `IsMatching q μ`, is stated separately.) -/
def IsStable {n m : ℕ} (q : Fin m → ℕ) (P : Fin n → Pref m) (pri : Fin m → Prio n)
    (r : Fin n → Finset (Fin m)) (μ : Assignment n m) : Prop :=
  IsIndividuallyRational P μ ∧ IsNonWasteful q P μ ∧ ∀ i, ¬ HasJustifiedMaxEnvy P pri r μ i

/-- Student `i` has justified min envy at `μ` with respect to student `j` and school `s`
(pp.7–8): `μ(j) = s P_i μ(i)` and (1) `s ∉ r(i)`, `s ∉ r(j)`, `i ≻_s j`; or (2) `s ∈ r(i)`,
`s ∈ r(j)`, `i ≻_s j`; or (3a) `s ∈ r(i)`, `s ∉ r(j)`, `i ≻_s j`; or (3b) `s ∈ r(i)`,
`s ∉ r(j)`, `j ≻_s i`, and there is no school `s′ ∈ S` with `s′ ∈ r(i)` and `μ(i) R_i s′`
(weak preference `R_i`). -/
def MinEnvyAt {n m : ℕ} (P : Fin n → Pref m) (pri : Fin m → Prio n) (r : Fin n → Finset (Fin m))
    (μ : Assignment n m) (i j : Fin n) (s : Fin m) : Prop :=
  μ j = some s ∧ P i (some s) < P i (μ i) ∧
    ((s ∉ r i ∧ s ∉ r j ∧ pri s i < pri s j) ∨
      (s ∈ r i ∧ s ∈ r j ∧ pri s i < pri s j) ∨
      (s ∈ r i ∧ s ∉ r j ∧ pri s i < pri s j) ∨
      (s ∈ r i ∧ s ∉ r j ∧ pri s j < pri s i ∧ ¬ ∃ s' ∈ r i, P i (μ i) ≤ P i (some s')))

/-- Student `i` has justified min envy at `μ` (pp.7–8): there are `j ∈ I` and `s ∈ S` with
`MinEnvyAt P pri r μ i j s`. -/
def HasJustifiedMinEnvy {n m : ℕ} (P : Fin n → Pref m) (pri : Fin m → Prio n)
    (r : Fin n → Finset (Fin m)) (μ : Assignment n m) (i : Fin n) : Prop :=
  ∃ j s, MinEnvyAt P pri r μ i j s

/-- Minimal-access stability (p.8): `μ` is individually rational, non-wasteful, and no student
has justified min envy. -/
def IsMinimalAccessStable {n m : ℕ} (q : Fin m → ℕ) (P : Fin n → Pref m) (pri : Fin m → Prio n)
    (r : Fin n → Finset (Fin m)) (μ : Assignment n m) : Prop :=
  IsIndividuallyRational P μ ∧ IsNonWasteful q P μ ∧ ∀ i, ¬ HasJustifiedMinEnvy P pri r μ i

end MinimalAccess


