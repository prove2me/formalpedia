-- Prove2me | Definitions.Def_Disjunctive_NormalForms_Basic
-- name    : Disjunctive_NormalForms_Basic
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T16:27:07.938369+00:00
-- url     : https://prove2.me/theorems/a2a9fb9a-330c-434b-8b53-a83fd86a8bfc
-- title:
--   Regular form, hull relaxation, basic steps, and extreme directions
-- statement:
--   This definition fixes the vocabulary of Chapter 4: regular form, elementary and improper
--   conjuncts, the hull-relaxation operator, the basic step, and extreme direction vectors.
--
--   A disjunctive set is in **regular form (RF)** if it is written $F = \bigcap_{j \in T} S_j$ with
--   each $S_j = \bigcup_{i \in Q_j} P_i$ a union of polyhedra. $S_j$ is **elementary** if every
--   $P_i$ is a halfspace (the RF is then the **CNF**); $S_j$ is **improper** if it literally equals a
--   single polyhedron $P_i$. For $F$'s polyhedral part, $P_0 := \bigcap_{j \in T^*} S_j$ over the
--   improper indices $T^*$. The **hull-relaxation** is
--
--   $$
--   h\text{-}\mathrm{rel}(F) := \bigcap_{j \in T} \mathrm{cl}\,\mathrm{conv}(S_j).
--   $$
--
--   A regular form $(S_j)_{j \in T'}$ is obtained from $(S_j)_{j \in T}$ by a **basic step** if two
--   conjuncts $S_k, S_l$ ($k \ne l$) are replaced by their intersection $S_k \cap S_l$ and every
--   other conjunct is carried over unchanged — this reduces the number of conjuncts by exactly one.
--   Finally, the **extreme direction vectors** of a convex set $S$ are the extreme rays of its
--   recession cone $\{y : \forall x \in S,\ t \ge 0,\ x + ty \in S\}$.
--
--   **Formalization Note.** `IsBasicStepOf` states the merge abstractly (via an equivalence
--   `Tnext ≃ {removed two elements} ⊕ Unit`) rather than fixing a specific index-relabeling, since a
--   basic step's only content is *which two conjuncts merge and into what*, not a canonical
--   renumbering scheme.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 49-55, Section 4.1-4.3

import Mathlib

namespace Disjunctive.NormalForms

/-- The polyhedron `{x : A x ≥ b}` (restated locally, as in earlier chunks of the series). -/
def Poly {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) : Set (Fin n → ℝ) :=
  {x | ∀ i, b i ≤ (A.mulVec x) i}

/-- The halfspaces `{x : dx ≤ d₀}` and `{x : dx ≥ d₀}` (used throughout Chapters 1-4). -/
def HalfspaceLE {n : ℕ} (d : Fin n → ℝ) (d0 : ℝ) : Set (Fin n → ℝ) := {x | dotProduct d x ≤ d0}

def HalfspaceGE {n : ℕ} (d : Fin n → ℝ) (d0 : ℝ) : Set (Fin n → ℝ) := {x | d0 ≤ dotProduct d x}

/-- `S` is a (finite) union of polyhedra, i.e. a disjunctive set in DNF (Balas §4.1, p. 49). -/
def IsDisjunctiveUnion {n : ℕ} (S : Set (Fin n → ℝ)) : Prop :=
  ∃ (Q : Type) (_ : Fintype Q) (m : Q → ℕ) (A : (i : Q) → Matrix (Fin (m i)) (Fin n) ℝ)
    (b : (i : Q) → Fin (m i) → ℝ), S = ⋃ i : Q, Poly (A i) (b i)

/-- `S` is elementary: a union of halfspaces (Balas §4.1, p. 49, "the CNF is the RF in which
every `S_j` is elementary, i.e. every polyhedron `P_i` is a halfspace"). -/
def IsElementaryDisjunction {n : ℕ} (S : Set (Fin n → ℝ)) : Prop :=
  ∃ (Q : Type) (_ : Fintype Q) (d : Q → Fin n → ℝ) (d0 : Q → ℝ), S = ⋃ i : Q, HalfspaceGE (d i) (d0 i)

/-- The indices `j` at which the conjunct `S_j` is improper, i.e. is literally a single
polyhedron (Balas §4.1, p. 49: "`S_j` in DNF is improper if `S_j = P_i` for some `i ∈ Q_j`"). -/
def ImproperIndices {n : ℕ} {T : Type*} (S : T → Set (Fin n → ℝ)) : Set T :=
  {j | ∃ (m : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ), S j = Poly A b}

/-- `P₀ := ⋂_{j ∈ T*} S_j`, the "polyhedral part" of a regular form `F = ⋂_{j∈T} S_j` (Balas
§4.2, p. 52-53). -/
def P0Set {n : ℕ} {T : Type*} [Fintype T] (S : T → Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  ⋂ j ∈ ImproperIndices S, S j

/-- The hull-relaxation `h-rel F := ⋂_{j∈T} cl conv S_j` of a regular form `F = ⋂_{j∈T} S_j`
(Balas §4.2, p. 52). -/
def HRel {n : ℕ} {T : Type*} [Fintype T] (S : T → Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  ⋂ j : T, closure (convexHull ℝ (S j))

/-- `Snext` is obtained from `Sprev` by a basic step (Balas §4.1, p. 49-50, Theorem 4.1): some
two conjuncts `k ≠ l` of `Sprev` are merged into one new conjunct `S_k ∩ S_l` (in DNF, via
(4.2)), every other conjunct carried over unchanged. -/
def IsBasicStepOf {n : ℕ} {Tprev Tnext : Type*} [Fintype Tprev] [Fintype Tnext]
    (Sprev : Tprev → Set (Fin n → ℝ)) (Snext : Tnext → Set (Fin n → ℝ)) : Prop :=
  ∃ (k l : Tprev), k ≠ l ∧
    ∃ e : Tnext ≃ {x : Tprev // x ≠ k ∧ x ≠ l} ⊕ Unit,
      (∀ t, Snext (e.symm (Sum.inl t)) = Sprev t.1) ∧
        Snext (e.symm (Sum.inr ())) = Sprev k ∩ Sprev l

/-- The recession cone of an arbitrary convex set `S` (Balas §4.3, p. 55, "extreme direction
vectors" are extreme rays of this cone). -/
def RecessionCone2 {n : ℕ} (S : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  {y | ∀ x ∈ S, ∀ t : ℝ, 0 ≤ t → x + t • y ∈ S}

/-- `v` is an extreme ray of a cone `W` (restated locally, as in `02b-polarity`). -/
def IsExtremeRay {E : Type*} [AddCommGroup E] [Module ℝ E] (W : Set E) (v : E) : Prop :=
  v ≠ 0 ∧ v ∈ W ∧ IsExtreme ℝ W {x | ∃ t : ℝ, 0 ≤ t ∧ x = t • v}

/-- The extreme direction vectors of a convex set `S`: the extreme rays of its recession cone
(Balas §4.3, p. 55). -/
def ExtremeDirections {n : ℕ} (S : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  {y | IsExtremeRay (RecessionCone2 S) y}

/-- `i ∈ Q**_j` (Balas §2.1.2, p. 23, the `Q**` of Theorem 2.4) for the `j`-th conjunct
`S_j = ⋃_{i ∈ Q_j} P_i` of a regular form: `P_i` is feasible and maximal for inclusion among the
feasible disjuncts of that conjunct. Maximality is read in the inclusion *preorder*, so two
coinciding feasible disjuncts both stay in `Q**`. -/
def IsMaximalDisjunct {n : ℕ} {T : Type*} (Qj : T → Type*) (mA : (j : T) → Qj j → ℕ)
    (A : (j : T) → (i : Qj j) → Matrix (Fin (mA j i)) (Fin n) ℝ)
    (b : (j : T) → (i : Qj j) → Fin (mA j i) → ℝ) (j : T) (i : Qj j) : Prop :=
  (Poly (A j i) (b j i)).Nonempty ∧
    ∀ k : Qj j, (Poly (A j k) (b j k)).Nonempty →
      Poly (A j i) (b j i) ⊆ Poly (A j k) (b j k) →
        Poly (A j k) (b j k) ⊆ Poly (A j i) (b j i)

end Disjunctive.NormalForms


