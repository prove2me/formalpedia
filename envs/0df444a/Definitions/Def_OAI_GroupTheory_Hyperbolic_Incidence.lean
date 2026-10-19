-- Prove2me | Definitions.Def_OAI_GroupTheory_Hyperbolic_Incidence
-- name    : OAI_GroupTheory_Hyperbolic_Incidence
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T06:34:52.057248+00:00
-- url     : https://prove2.me/theorems/cbba6c9c-8ff5-4dcf-bd88-d2836e074c09
-- title:
--   Marked lines, short-cycle deletion and marked-line data
-- statement:
--   Incidence geometry over a finite field $K$ in a $K$-vector space $V$, used to produce a point–line incidence structure of large girth.
--
--   1. **Punctured incidence.** A line is given by a mark $a\in V$ and a projective direction $d$; a point $z$ is on it if $z=a+t\,\hat d$ for some $t\in K$, where $\hat d$ is the chosen representative of $d$. The incidence is *punctured* when moreover $z\ne a$.
--   2. **Short cycles.** For a cyclic shift $\sigma$ of $A$, a cycle candidate consists of distinct points $p$ with $p(\sigma a)\ne p(a)$ and parameters $t$ such that the attempted marks $p(a)+t_a(p(\sigma a)-p(a))$ are distinct and lie in the mark set $S$. It occurs for a random direction assignment $\omega:S\to\mathbb P(V)$ when each such mark receives the direction of $p(\sigma a)-p(a)$. The marks of every occurring candidate of length $2,\dots,6$ are deleted; the remaining marks are retained.
--   3. **Degrees and exceptional points.** The point degree counts marks $a$ with $z$ punctured-incident to $(a,\omega(a))$, and its mean is
--   $$
--   \sum_{a\in S}\frac{[z\ne a]}{|\mathbb P(V)|}.
--   $$
--   Exceptional points are those of degree below a threshold $T$ together with all points on lines of deleted marks.
--   4. **Bipartite graphs.** A relation $R\subseteq A\times B$ gives a simple bipartite graph on $A\sqcup B$ with its two-colouring.
--   5. **Marked-line data.** For a prime $q$ and $r\in\mathbb N$, a `MarkedLineData q r` consists of a set of $q/100$ scalars, a finite label type with injective marks in the grid $\text{scalars}^{20}\subseteq\mathbb F_q^{20}$ and projective directions, and a set $E$ of exceptional points. Every non-exceptional point has at least $4r^2$ punctured incidences, the budget $4(2q^{20}+r|E|)<|\text{labels}|\cdot r$ holds, and every cycle in the point–label incidence graph has length greater than $12$. Consequently there are at most $q^{20}$ labels and some point is not exceptional.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/Incidence.lean

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/Incidence.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TorsionFreeHyperbolic mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace Release075
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

section ProjectiveLines
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- A line through a mark, chosen by its projective direction. -/
def OnChosenLine (a z : V) (d : Projectivization K V) : Prop :=
  ∃ t : K, a + t • d.rep = z

/-- Only the chosen line's own mark is punctured. -/
def PuncturedIncidence (a z : V) (d : Projectivization K V) : Prop :=
  z ≠ a ∧ OnChosenLine a z d

end ProjectiveLines

section CycleCount
variable {A K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- An attempted mark on the geometric line joining consecutive point vertices. -/
def candidateMark (σ : A → A) (p : A → V) (t : A → K) (a : A) : V :=
  p a + t a • (p (σ a) - p a)

/-- An over-count of short cycles: parameters, rather than marks, are enumerated.
Marks at punctured endpoints are deliberately permitted for the upper bound. -/
def CycleCandidate (S : Finset V) (σ : A → A) :=
  {c : (A → V) × (A → K) // Function.Injective c.1 ∧
    (∀ a, c.1 (σ a) ≠ c.1 a) ∧
    (∀ a, candidateMark σ c.1 c.2 a ∈ S) ∧
    Function.Injective (candidateMark σ c.1 c.2)}

instance [Fintype A] [Fintype K] [Fintype V] (S : Finset V) (σ : A → A) :
    Fintype (CycleCandidate (K := K) S σ) := by unfold CycleCandidate; infer_instance

namespace CycleCandidate
variable {S : Finset V} {σ : A → A}

def marks (c : CycleCandidate (K := K) S σ) : A ↪ S where
  toFun a := ⟨candidateMark σ c.val.1 c.val.2 a,c.property.2.2.1 a⟩
  inj' := fun _ _ h => c.property.2.2.2 (congrArg Subtype.val h)

def direction (c : CycleCandidate (K := K) S σ) (a : A) : Projectivization K V :=
  Projectivization.mk K (c.val.1 (σ a) - c.val.1 a) (sub_ne_zero.mpr (c.property.2.1 a))

def Occurs (c : CycleCandidate (K := K) S σ) (ω : S → Projectivization K V) : Prop :=
  ∀ a, ω (c.marks a) = c.direction a

end CycleCandidate

/-- All occurring encoded cycles for a given random outcome. -/
def badCycles [Fintype A] [Fintype K] [Fintype V]
    (S : Finset V) (σ : A → A) (ω : S → Projectivization K V) : Finset (CycleCandidate (K := K) S σ) :=
  Finset.univ.filter (fun c => c.Occurs ω)

end CycleCount

section Degrees
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Fintype (Projectivization K V)] [Nontrivial V]

/-- Incidence degree before alteration, with the marked point removed from its line. -/
def pointDegree (S : Finset V) (ω : S → Projectivization K V) (z : V) : ℕ :=
  (Finset.univ.filter (fun a : S => PuncturedIncidence a.val z (ω a))).card

/-- Exact mean, including the missing self-mark when the point belongs to the grid. -/
def pointMean (S : Finset V) (z : V) : ℝ :=
  ∑ a : S, if z ≠ a.val then 1 / (Fintype.card (Projectivization K V) : ℝ) else 0

end Degrees

/-- The simple bipartite graph of a relation (the same definition used by the links). -/
def relationGraph {A B : Type*} (R : A → B → Prop) : SimpleGraph (A ⊕ B) where
  Adj x y := match x,y with
    | .inl a, .inr b => R a b
    | .inr b, .inl a => R a b
    | _,_ => False
  symm := ⟨by intro x y; cases x <;> cases y <;> simp⟩
  loopless := ⟨by intro x; cases x <;> simp⟩

def relationColoring {A B : Type*} (R : A → B → Prop) : (relationGraph R).Coloring Bool :=
  {toFun := Sum.elim (fun _ => false) (fun _ => true)
   map_rel' := by intro x y h; cases x <;> cases y <;> simp_all [relationGraph]}

section EncodingIncidence
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

end EncodingIncidence

section Alteration
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

variable [Fintype K] [Fintype V]

/-- All marks lying on an occurring short-cycle attempt are discarded. -/
def deletedMarks (S : Finset V) (ω : S → Projectivization K V) : Finset S :=
  (Finset.Icc 2 6).biUnion fun s =>
    (badCycles S (finRotate s) ω).biUnion fun c => Finset.univ.image c.marks

def Retained (S : Finset V) (ω : S → Projectivization K V) := {a : S // a ∉ deletedMarks S ω}

end Alteration

section Exceptional
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [Fintype K] [Fintype V]

instance (S : Finset V) (ω : S → Projectivization K V) : Fintype (Retained S ω) := by
  unfold Retained
  infer_instance

def chosenLinePoints (a : V) (d : Projectivization K V) : Finset V :=
  Finset.univ.image (fun t : K => a+t • d.rep)

def deletedPoints (S : Finset V) (ω : S → Projectivization K V) : Finset V :=
  (deletedMarks S ω).biUnion (fun a => chosenLinePoints a.val (ω a))

def exceptionalPoints (S : Finset V) (ω : S → Projectivization K V) (T : ℕ) : Finset V :=
  Finset.univ.filter (fun z => pointDegree S ω z < T) ∪ deletedPoints S ω

def retainedIncidence (S : Finset V) (ω : S → Projectivization K V) (z : V) : Finset (Retained S ω) :=
  Finset.univ.filter (fun a => PuncturedIncidence a.val.val z (ω a.val))

end Exceptional

section AlterationMean
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Fintype K] [Fintype V] [Nontrivial V] [Fintype (Projectivization K V)]

end AlterationMean

section DimensionTwenty
variable (q : ℕ) [Fact q.Prime]

def gridMarks (S : Finset (ZMod q)) : Finset (Fin 20 → ZMod q) :=
  Fintype.piFinset (fun _ => S)

variable [Fintype (Projectivization (ZMod q) (Fin 20 → ZMod q))]

end DimensionTwenty

/-- Exact finite data fixed once for all before any finite quotient is chosen.
No geometric or group-theoretic conclusion is part of these data. -/
structure MarkedLineData (q r : ℕ) [Fact q.Prime] where
  scalarGrid : Finset (ZMod q)
  grid_card : scalarGrid.card = q/100
  Label : Type
  [labelFintype : Fintype Label]
  mark : Label → Fin 20 → ZMod q
  direction : Label → Projectivization (ZMod q) (Fin 20 → ZMod q)
  marks_mem : ∀ i t, mark i t ∈ scalarGrid
  marks_injective : Function.Injective mark
  exceptional : Finset (Fin 20 → ZMod q)
  degree : ∀ z, z ∉ exceptional → 4*r^2 ≤
    (Finset.univ.filter (fun i => PuncturedIncidence (mark i) z (direction i))).card
  budget : 4*(2*q^20+r*exceptional.card) < Fintype.card Label*r
  girth : ∀ a (w : (relationGraph (fun z i =>
    PuncturedIncidence (mark i) z (direction i))).Walk a a), w.IsCycle → 12 < w.length

attribute [instance] MarkedLineData.labelFintype

namespace MarkedLineData
variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r)

/-- The marking grid gives an a priori upper bound on the number of labels. -/
theorem card_labels_le : Fintype.card d.Label ≤ q^20 := by
  simpa only [Fintype.card_fun,Fintype.card_fin,ZMod.card] using
    Fintype.card_le_of_injective d.mark d.marks_injective

theorem exists_regular : ∃ z, z ∉ d.exceptional := by
  classical
  by_contra! h
  have hE : d.exceptional = Finset.univ := Finset.eq_univ_of_forall h
  have hc : d.exceptional.card = q^20 := by simp only [hE,Finset.card_univ,
      Fintype.card_fun,Fintype.card_fin,ZMod.card]
  have hd := d.budget
  rw [hc] at hd
  have hm := Nat.mul_le_mul_right r d.card_labels_le
  rw [Nat.mul_comm (q^20) r] at hm
  omega

end MarkedLineData

end
end Release075

end OAI


