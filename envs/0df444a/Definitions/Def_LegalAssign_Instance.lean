-- Prove2me | Definitions.Def_LegalAssign_Instance
-- name    : LegalAssign_Instance
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:20:19.156033+00:00
-- url     : https://prove2.me/theorems/2c1cf8b9-08c4-4154-bc9d-fbb90e75e25d
-- title:
--   The stable assignment problem: instances, subinstances, assignments, the blocks relation, stability, the legal property
-- statement:
--   An **instance** $(G,<,q)$ of the stable assignment problem consists of a finite bipartite graph $G=(A\cup B,E)$ with **students** $A$ and **schools** $B$, a strict ordering $<_v$ of the neighbours of every vertex $v$, and **quotas** $q_b\in\mathbb N$ for $b\in B$. Every neighbour is preferred to being unmatched: $y>_x\emptyset$ for $xy\in E$. For $F\subseteq E$, the **subinstance** $(G[F],<,q)$ has the same vertices, the edges $F$, the induced preferences and the same quotas.
--
--   An **assignment** is a set $M\subseteq E$ with at most one edge at every student and at most $q_b$ edges at every school $b$; $\mathcal M(G,q)$ is the set of all assignments, and $M(x)=\{y:xy\in M\}$. An edge $ab\in E$ is a **blocking pair** for $M$ if $b>_a M(a)$ and either $a>_b a'$ for some $a'\in M(b)$ or $|M(b)|<q_b$. An assignment $M'$ **blocks** $M$ if some edge of $M'$ is a blocking pair for $M$. An assignment is **stable** if no edge of $G$ is a blocking pair for it, and $\mathcal S(G,<,q)$ is the set of stable assignments. The pair $ab$ is a **stable pair** if it lies in some stable assignment.
--
--   For $\mathcal M'\subseteq\mathcal M(G,q)$, let $\mathcal I(\mathcal M')$ be the set of assignments blocked by some member of $\mathcal M'$. The set $\mathcal M'$ has the **legal property** if
--   $$\mathcal I(\mathcal M')=\mathcal M(G,q)\setminus\mathcal M'.$$
--
--   For assignments $M,M'$, write $M\succeq M'$ if $M(a)\ge_a M'(a)$ for every student $a$, an unmatched student being worst, and $M\succ M'$ if moreover $M\ne M'$. The **student-optimal** stable assignment is a stable $M$ with $M\succeq M'$ for all stable $M'$; the **school-optimal** one is a stable $M$ with $M'\succeq M$ for all stable $M'$.
--
--   These are the objects of every statement of the mission. Blocking between assignments is the notion of Morrill, and the legal property is von Neumann–Morgenstern stability for that relation.
--
--   **Formalization Note** Preferences are strict total orders on the whole other side; only their restriction to neighbours enters any definition, and acceptability is the edge set alone, so `restrict` changes nothing but `E`. `prefA a b b'` is $b>_a b'$, `prefB b a a'` is $a>_b a'$. Families of assignments are `Set (Finset (A × B))`, and `edgeUnion` is $\bigcup\{M:M\in\mathcal M'\}$. `PrefersToPartner M a b` is $b>_a M(a)$, stated as "$b$ beats every element of $M(a)$", which is the convention $y>_x\emptyset$.
-- source:
--   Faenza–Zhang, arXiv:1809.08506v2, §2.1, p.6 (instance, assignment, blocking pair, stability); §3, p.7 (legal property); §4, p.8 (dominance); Theorem 4.1, p.9 (optimal stable assignments)

import Mathlib

namespace LegalAssign

/-- An instance `(G, <, q)` of the stable assignment problem (Faenza–Zhang, arXiv:1809.08506v2,
§2.1, p.6): a bipartite graph with students `A`, schools `B` and edge set `E ⊆ A × B`, strict
preferences of every vertex, and quotas `q : B → ℕ` (`q b = 0` is allowed).
`prefA a b b'` reads `b >_a b'` and `prefB b a a'` reads `a >_b a'`.

**Formalization Note** The source orders only the neighbours of a vertex. Here each vertex carries
a strict total order on the whole other side; only its restriction to neighbours ever enters a
definition, and every strict order on the neighbours extends, so this is an encoding. Acceptability
is the edge set `E`, never part of the preferences: subinstances delete edges and keep `<` and `q`. -/
structure Instance (A B : Type*) where
  /-- The edge set `E(G)`. -/
  E : Finset (A × B)
  /-- `prefA a b b'` is `b >_a b'`. -/
  prefA : A → B → B → Prop
  /-- `prefB b a a'` is `a >_b a'`. -/
  prefB : B → A → A → Prop
  prefA_strict : ∀ a, IsStrictTotalOrder B (prefA a)
  prefB_strict : ∀ b, IsStrictTotalOrder A (prefB b)
  /-- The quota `q_b` of school `b`. -/
  q : B → ℕ

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- `M(a) = {b : ab ∈ M}` for a student `a` (arXiv:1809.08506v2, §2.1, p.6). -/
def studentPartners (M : Finset (A × B)) (a : A) : Finset B :=
  Finset.univ.filter fun b => (a, b) ∈ M

/-- `M(b) = {a : ab ∈ M}` for a school `b` (arXiv:1809.08506v2, §2.1, p.6). -/
def schoolPartners (M : Finset (A × B)) (b : B) : Finset A :=
  Finset.univ.filter fun a => (a, b) ∈ M

/-- `⋃ {M : M ∈ S}`, the set of edges used by some member of the family `S`
(arXiv:1809.08506v2, Theorem 3.1, p.7). -/
noncomputable def edgeUnion (S : Set (Finset (A × B))) : Finset (A × B) :=
  open Classical in Finset.univ.filter fun e => ∃ M ∈ S, e ∈ M

namespace Instance

/-- The subinstance `(G[F], <, q)` (arXiv:1809.08506v2, §2, p.6): same vertices, edge set `F`, same
preferences and same quotas. -/
def restrict (G : Instance A B) (F : Finset (A × B)) : Instance A B :=
  { G with E := F }

/-- `M` is an assignment of `(G, <, q)` (arXiv:1809.08506v2, §2.1, p.6): a set of edges of `G` with
at most one edge at every student and at most `q_b` edges at every school. -/
structure IsAssignment (G : Instance A B) (M : Finset (A × B)) : Prop where
  subset : M ⊆ G.E
  student_le : ∀ a, (studentPartners M a).card ≤ 1
  school_le : ∀ b, (schoolPartners M b).card ≤ G.q b

/-- `𝓜(G, q)`, the set of all assignments (arXiv:1809.08506v2, §2.1, p.6). -/
def assignments (G : Instance A B) : Set (Finset (A × B)) :=
  {M | G.IsAssignment M}

/-- `b >_a M(a)` (arXiv:1809.08506v2, §2.1, p.6).

**Formalization Note** `b` beats every element of `M(a)`, which is vacuous when `a` is unmatched:
this is the convention `y >_x ∅`. On assignments `M(a)` has at most one element. -/
def PrefersToPartner (G : Instance A B) (M : Finset (A × B)) (a : A) (b : B) : Prop :=
  ∀ b' ∈ studentPartners M a, G.prefA a b b'

/-- `ab` is a blocking pair for `M` (arXiv:1809.08506v2, §2.1, p.6): `ab ∈ E`, `b >_a M(a)`, and
either `a >_b a'` for some `a' ∈ M(b)` or `|M(b)| < q_b`. -/
def IsBlockingPair (G : Instance A B) (M : Finset (A × B)) (a : A) (b : B) : Prop :=
  (a, b) ∈ G.E ∧ G.PrefersToPartner M a b ∧
    ((∃ a' ∈ schoolPartners M b, G.prefB b a a') ∨ (schoolPartners M b).card < G.q b)

/-- `M'` blocks `M` if some edge of `M'` is a blocking pair for `M` (arXiv:1809.08506v2, §2.1, p.6
and footnote 5, Morrill's notion). -/
def Blocks (G : Instance A B) (M' M : Finset (A × B)) : Prop :=
  ∃ e ∈ M', G.IsBlockingPair M e.1 e.2

/-- `𝓢(G, <, q)`, the assignments blocked by no edge of `G` (arXiv:1809.08506v2, §2.1, p.6). -/
def stable (G : Instance A B) : Set (Finset (A × B)) :=
  {M | G.IsAssignment M ∧ ∀ a b, ¬ G.IsBlockingPair M a b}

/-- `ab` is a stable pair: `ab ∈ M` for some `M ∈ 𝓢(G, <, q)` (arXiv:1809.08506v2, §2.1, p.6). -/
def IsStablePair (G : Instance A B) (a : A) (b : B) : Prop :=
  ∃ M ∈ G.stable, (a, b) ∈ M

/-- `𝓘(𝓜')`, the assignments blocked by some member of `𝓜'` (arXiv:1809.08506v2, §3, p.7). -/
def blockedBy (G : Instance A B) (S : Set (Finset (A × B))) : Set (Finset (A × B)) :=
  {M | M ∈ G.assignments ∧ ∃ M' ∈ S, G.Blocks M' M}

/-- The legal property `𝓘(𝓜') = 𝓜(G, q) \ 𝓜'` (arXiv:1809.08506v2, §3, p.7).

**Formalization Note** The source defines this for `𝓜' ⊆ 𝓜(G, q)`; every statement of the mission
assumes or asserts that inclusion separately. -/
def HasLegalProperty (G : Instance A B) (S : Set (Finset (A × B))) : Prop :=
  G.blockedBy S = G.assignments \ S

/-- `M(a) >_a M'(a)`: student `a` strictly prefers `M` to `M'`, an unmatched student being worst
(arXiv:1809.08506v2, §2.1, p.6 and Lemma A.4, p.26). -/
def StudentStrictlyPrefers (G : Instance A B) (M M' : Finset (A × B)) (a : A) : Prop :=
  ∃ b ∈ studentPartners M a, G.PrefersToPartner M' a b

/-- School `b` strictly prefers `M` to `M'`, for instances with quotas one, an unmatched school
being worst (arXiv:1809.08506v2, Lemma A.4, p.26). -/
def SchoolStrictlyPrefers (G : Instance A B) (M M' : Finset (A × B)) (b : B) : Prop :=
  ∃ a ∈ schoolPartners M b, ∀ a' ∈ schoolPartners M' b, G.prefB b a a'

/-- `M(a) ≥_a M'(a)` (arXiv:1809.08506v2, §2.1, p.6): strict preference, or the same partner. -/
def StudentWeaklyPrefers (G : Instance A B) (M M' : Finset (A × B)) (a : A) : Prop :=
  G.StudentStrictlyPrefers M M' a ∨ studentPartners M a = studentPartners M' a

/-- `M ⪰ M'`: `M(a) ≥_a M'(a)` for every student (arXiv:1809.08506v2, §4, p.8). -/
def Dominates (G : Instance A B) (M M' : Finset (A × B)) : Prop :=
  ∀ a, G.StudentWeaklyPrefers M M' a

/-- `M ≻ M'`: `M ⪰ M'` and `M ≠ M'` (arXiv:1809.08506v2, §4, p.8). -/
def StrictlyDominates (G : Instance A B) (M M' : Finset (A × B)) : Prop :=
  G.Dominates M M' ∧ M ≠ M'

/-- `M` is the student-optimal stable assignment: stable, and `M ⪰ M'` for every stable `M'`
(arXiv:1809.08506v2, Theorem 4.1, p.9). -/
def IsStudentOptimal (G : Instance A B) (M : Finset (A × B)) : Prop :=
  M ∈ G.stable ∧ ∀ M' ∈ G.stable, G.Dominates M M'

/-- `M` is the school-optimal stable assignment: stable, and `M' ⪰ M` for every stable `M'`
(arXiv:1809.08506v2, Theorem 4.1, p.9). -/
def IsSchoolOptimal (G : Instance A B) (M : Finset (A × B)) : Prop :=
  M ∈ G.stable ∧ ∀ M' ∈ G.stable, G.Dominates M' M

end Instance

end LegalAssign


