-- Prove2me | Definitions.Def_KikuchiMoore_Moore_Even
-- name    : KikuchiMoore_Moore_Even
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T22:41:48.377485+00:00
-- url     : https://prove2.me/theorems/c9ece9c3-7f29-4940-8327-3d2b08400389
-- title:
--   Even Kikuchi graph, truncated parity lift, and window orientation
-- statement:
--   For $k=2r$, an edge $F$ is legal at a row $S$ when $|S\cap F|=r$ and joins $S$ to $S\triangle F$. The unsigned matrix sums these incidences. A lifted state is $(S,M)$, with $M\subseteq H$ and $|M|\le s$; an $F$ step toggles the row by $F$ and memory by $\{F\}$. Keep only components of empty-memory states and inherit the base normalization. Excluded states are zero rows and columns, an equivalent zero-padding representation. The window is $S\cup\bigcup_{F\in M}F$. Equal-window edges point toward the row containing the fixed representative of their label; unequal-window edges point toward the larger window. Incoming degree counts actual reachable lifted neighbors under this orientation, not an assumed bound. The representative choice comes from the core definition and is valid whenever its system exists.
-- source:
--   Schmidhuber and Hastings (2026), Sharp Spectral Bounds for Kikuchi Matrices: The Hypergraph Moore Bound and Optimal Trade-offs for kXOR, supplied STOC 2027 submission, Definitions and constructions, Sections 3–5, printed p. 13 = PDF p. 13, PDF SHA-256 44f00c2d419b40d2f4d664d6eedb7dda4c80a7da27e71ed4fccd6a5a613725ea

import Definitions.Def_KikuchiMoore_Moore_Core
import Definitions.Def_KikuchiMoore_Moore_Operators

noncomputable section
open scoped BigOperators symmDiff

namespace KikuchiMoore.Moore

def evenAdj {n l : ℕ} (H : Hypergraph n) (r : ℕ) : Matrix (Row n l) (Row n l) ℝ := by
  classical
  exact fun S T => ∑ F ∈ edges H,
    if (S.val ∩ F).card = r ∧ T.val = S.val ∆ F then 1 else 0

abbrev State (n l : ℕ) := Row n l × Finset (Finset (Fin n))

def permitted {n l : ℕ} (H : Hypergraph n) (s : ℕ) (x : State n l) : Prop :=
  x.2 ⊆ edges H ∧ x.2.card ≤ s

def evenStep {n l : ℕ} (H : Hypergraph n) (r s : ℕ) (x y : State n l) : Prop :=
  permitted H s x ∧ permitted H s y ∧
  ∃ F ∈ edges H, (x.1.val ∩ F).card = r ∧
    y.1.val = x.1.val ∆ F ∧ y.2 = x.2 ∆ {F}

def evenReachable {n l : ℕ} (H : Hypergraph n) (r s : ℕ) (x : State n l) : Prop :=
  ∃ S : Row n l, Relation.ReflTransGen (evenStep H r s) (S, ∅) x

/-- The restricted lift, extended by zero on all excluded states. -/
def evenLiftRaw {n l : ℕ} (H : Hypergraph n) (r s : ℕ) :
    Matrix (State n l) (State n l) ℝ := by
  classical
  exact fun x y => if evenReachable H r s x ∧ evenReachable H r s y ∧
    evenStep H r s x y then 1 else 0

def evenLift {n l : ℕ} (H : Hypergraph n) (r s : ℕ) :
    Matrix (State n l) (State n l) ℝ :=
  normalizedLift (evenAdj H r) Prod.fst (evenLiftRaw H r s)

def window {n l : ℕ} (x : State n l) : Finset (Fin n) :=
  x.1.val ∪ x.2.biUnion id

def evenToward {n l : ℕ} (H : Hypergraph n) (x y : State n l) : Prop :=
  if window x = window y then
    ∃ F ∈ edges H, y.2 = x.2 ∆ {F} ∧
      ∃ v ∈ y.1.val, representative H (window y) F = some v
  else window x ⊂ window y

def evenIncoming {n l : ℕ} (H : Hypergraph n) (r s : ℕ) (y : State n l) : ℕ := by
  classical
  exact (Finset.univ.filter fun x => evenReachable H r s x ∧ evenReachable H r s y ∧
    evenStep H r s x y ∧ evenToward H x y).card

end KikuchiMoore.Moore


