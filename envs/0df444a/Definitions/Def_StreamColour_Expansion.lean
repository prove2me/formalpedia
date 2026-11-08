-- Prove2me | Definitions.Def_StreamColour_Expansion
-- name    : StreamColour_Expansion
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:52:52.954406+00:00
-- url     : https://prove2.me/theorems/d410db97-e223-4c68-8fef-f2692f2f977e
-- title:
--   §§5.2–5.4 — near pieces, complement matchings, expanded pieces, local colour classes
-- statement:
--   A set $C$ is **near** if $\Delta-Ah\le|C|\le\Delta+Ah$. A **complement matching** in $C$ is a collection of disjoint pairs of distinct nonadjacent vertices of $C$; it is **maximal** if no further pair can be added, i.e. the vertices of $C\setminus V(M)$ form a clique. For a set $Q$, the **expanded piece** is
--
--   $$X=\{v\in V(G):|N_G(v)\cap Q|\ge\tfrac{18}{25}\Delta\}.$$
--
--   A **class partition** of $X$ is a partition into at most $q$ nonempty independent sets. It has **minimum singletons** if no class partition has fewer singleton classes. Its **singleton core** $K$ is the set of vertices in singleton classes, and a **block** is a class of size at least two.
--
--   **Formalization Note** The comparisons are real, so nothing truncates. A matching is a finite set of ordered pairs in which disjointness rules out holding both orientations of a pair, so its cardinality is its number of pairs.
-- source:
--   Chakraborty, Chatterjee, Kundu, Mishra, Streaming Graph Colouring Meets Molloy–Reed via Kernelization (STOC 2027 submission, preprint, sha256 31a813b319e4af3fd96deb52ecd284fc2c478368ab1d9064bb951dcc884cc105), (8), p.50 (PDF 52); §§5.2–5.4, pp.51–54 (PDF 53–56)

import Mathlib
import Definitions.Def_StreamColour_GraphQuantities

namespace StreamColour

/-! # Near pieces, complement matchings, expanded pieces, local colour classes

Chakraborty, Chatterjee, Kundu, Mishra (STOC 2027 submission, sha256 31a813b3…), §3, p.20 (PDF 22), (8) p.50
(PDF 52), §5.2–5.4, pp.51–54 (PDF 53–56). `C` is near if `∆ − Ah ≤ |C| ≤ ∆ + Ah`. `Q = C \ V(M)` for a maximal
complement matching `M` of `C` with `|M| < L`, and `X = {v : |N_G(v) ∩ Q| ≥ (18/25)∆}`, (9).

**Formalization Note.** A complement matching is a finite set of ordered pairs. Disjointness forbids holding
both orientations of a pair, so its cardinality is the number of pairs. "Maximal" is the equivalent "no further
pair can be added": any two distinct unmatched vertices of `C` are adjacent. A partition into classes is a
finite set of finite sets, so `P.card` counts classes. -/

variable {V : Type} [Fintype V]

/-- `C` is near, (8): `∆ − Ah ≤ |C| ≤ ∆ + Ah`. The comparison is in `ℝ`, so nothing truncates. -/
def IsNear (A : ℝ) (h Δ : ℕ) (C : Finset V) : Prop :=
  (Δ : ℝ) - A * (h : ℝ) ≤ (C.card : ℝ) ∧ (C.card : ℝ) ≤ (Δ : ℝ) + A * (h : ℝ)

/-- `M` is a complement matching in `C`: disjoint pairs of distinct nonadjacent vertices of `C`. -/
structure IsComplementMatching (G : SimpleGraph V) (C : Finset V) (M : Finset (V × V)) : Prop where
  mem : ∀ p ∈ M, p.1 ∈ C ∧ p.2 ∈ C ∧ p.1 ≠ p.2 ∧ ¬ G.Adj p.1 p.2
  disj : ∀ p ∈ M, ∀ r ∈ M, p ≠ r → p.1 ≠ r.1 ∧ p.1 ≠ r.2 ∧ p.2 ≠ r.1 ∧ p.2 ≠ r.2

open Classical in
/-- `C \ V(M)`, the vertices of `C` covered by no pair of `M`. -/
noncomputable def unmatched (C : Finset V) (M : Finset (V × V)) : Finset V :=
  C.filter fun v => ∀ p ∈ M, v ≠ p.1 ∧ v ≠ p.2

/-- `M` is a maximal complement matching in `C`. -/
structure IsMaximalCM (G : SimpleGraph V) (C : Finset V) (M : Finset (V × V)) : Prop where
  matching : IsComplementMatching G C M
  maximal : ∀ a ∈ unmatched C M, ∀ b ∈ unmatched C M, a ≠ b → G.Adj a b

open Classical in
/-- The expanded piece of (9): `X = {v : |N_G(v) ∩ Q| ≥ (18/25)∆}`. -/
noncomputable def expanded (G : SimpleGraph V) (Δ : ℕ) (Q : Finset V) : Finset V :=
  Finset.univ.filter fun v => (18 / 25 : ℝ) * (Δ : ℝ) ≤ (dIn G Q v : ℝ)

/-- `P` partitions `X` into at most `q` nonempty independent sets. -/
structure IsClassPartition (G : SimpleGraph V) (X : Finset V) (q : ℕ) (P : Finset (Finset V)) : Prop where
  nonempty : ∀ D ∈ P, D.Nonempty
  subset : ∀ D ∈ P, D ⊆ X
  disjoint : ∀ D ∈ P, ∀ D' ∈ P, D ≠ D' → Disjoint D D'
  cover : ∀ v ∈ X, ∃ D ∈ P, v ∈ D
  independent : ∀ D ∈ P, ∀ a ∈ D, ∀ b ∈ D, ¬ G.Adj a b
  card_le : P.card ≤ q

/-- The number of singleton classes. -/
def singletonCount (P : Finset (Finset V)) : ℕ := (P.filter fun D => D.card = 1).card

open Classical in
/-- `K`, the singleton core: the vertices in singleton classes. -/
noncomputable def singletonCore (P : Finset (Finset V)) : Finset V :=
  Finset.univ.filter fun v => {v} ∈ P

/-- `P` has the fewest singleton classes among all partitions of `X` into at most `q` nonempty independent
sets. -/
def IsMinSingleton (G : SimpleGraph V) (X : Finset V) (q : ℕ) (P : Finset (Finset V)) : Prop :=
  IsClassPartition G X q P ∧ ∀ P', IsClassPartition G X q P' → singletonCount P ≤ singletonCount P'

end StreamColour


