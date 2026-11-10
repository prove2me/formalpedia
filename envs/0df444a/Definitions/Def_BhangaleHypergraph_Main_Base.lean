-- Prove2me | Definitions.Def_BhangaleHypergraph_Main_Base
-- name    : BhangaleHypergraph_Main_Base
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T14:05:24.995838+00:00
-- url     : https://prove2.me/theorems/fcc828cf-7c43-47c9-835d-2f9da31ed6f0
-- title:
--   Occurrence-valued base Label Cover and neighborhood assignments
-- statement:
--   A base instance consists of nonempty finite left and right parts, positive global alphabets, a finite indexed collection of edge occurrences, surjective projection tables, and occurrence-counting biregularity. Its value is the maximum satisfied fraction over actual assignments. Edgeless data have the explicit vacuous value $1$; a uniform edge experiment is used only when edges are present.
--
--   The radius at layer $i\in\{0,\ldots,\ell-1\}$ is $2(\ell-i-1)$. Neighborhoods are defined by bounded undirected walks. A local label is an assignment satisfying every internal occurrence of that neighborhood. The representation extends it by a fixed zero label outside the neighborhood, making the encoding one-to-one. Restriction compares only the target neighborhood.
--
--   For positive edge count, the pair law samples a right vertex uniformly and then two incident occurrences independently with replacement. Its acceptance probability is the explicit finite sum divided by $|B|d_B^2$. The empty-edge branch is defined separately and is excluded from the successful sampling branch. The definitions retain parallel occurrences and do not assume any soundness conclusion.
-- source:
--   Amey Bhangale, STOC 2027 submission #1052 (October 2026), §§2.1–2.2, pp. 5–8 (printed pages = PDF pages); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1052.pdf

import Mathlib

namespace BhangaleHypergraph.Main

/-- Biregular base Label Cover, with individual occurrences and surjective projections.
Zero-edge data are retained and use the explicit vacuous-value convention below. -/
structure BaseCover where
  A : ℕ
  B : ℕ
  E : ℕ
  L : ℕ
  R : ℕ
  posA : 0 < A
  posB : 0 < B
  posL : 0 < L
  posR : 0 < R
  left : Fin E → Fin A
  right : Fin E → Fin B
  proj : Fin E → Fin L → Fin R
  onto : ∀ e, Function.Surjective (proj e)
  degreeA : ℕ
  degreeB : ℕ
  regularA : ∀ a, (Finset.univ.filter fun e => left e = a).card = degreeA
  regularB : ∀ b, (Finset.univ.filter fun e => right e = b).card = degreeB

abbrev BaseVertex (B : BaseCover) := Fin B.A ⊕ Fin B.B

def BaseAlphabet (B : BaseCover) : BaseVertex B → ℕ
  | .inl _ => B.L
  | .inr _ => B.R

theorem BaseAlphabetPositive (B : BaseCover) (v : BaseVertex B) : 0 < BaseAlphabet B v := by
  cases v
  · exact B.posL
  · exact B.posR

abbrev BaseAssignment (B : BaseCover) := (v : BaseVertex B) → Fin (BaseAlphabet B v)

def BaseSatisfiable (B : BaseCover) : Prop :=
  ∃ σ : BaseAssignment B, ∀ e, B.proj e (σ (.inl (B.left e))) = σ (.inr (B.right e))

noncomputable def BaseFraction (B : BaseCover) (σ : BaseAssignment B) : ℝ := by
  classical
  exact if B.E = 0 then 1 else ((Finset.univ.filter fun e =>
    B.proj e (σ (.inl (B.left e))) = σ (.inr (B.right e))).card : ℝ) / B.E

/-- A finite, nonempty set of labelings; its supremum is its attained maximum. -/
noncomputable def BaseValue (B : BaseCover) : ℝ :=
  sSup (Set.range (BaseFraction B))

def BaseAdjacent (B : BaseCover) (u v : BaseVertex B) : Prop :=
  ∃ e, (u = .inl (B.left e) ∧ v = .inr (B.right e)) ∨
    (v = .inl (B.left e) ∧ u = .inr (B.right e))

/-- Bounded undirected walks also distinguish disconnected vertices from distance zero. -/
def InBall (B : BaseCover) (r : ℕ) (a : Fin B.A) (v : BaseVertex B) : Prop :=
  ∃ k ≤ r, ∃ walk : Fin (k + 1) → BaseVertex B,
    walk 0 = .inl a ∧ walk (Fin.last k) = v ∧
    ∀ j : Fin k, BaseAdjacent B (walk j.castSucc) (walk j.succ)

/-- Assignments outside the ball are fixed to zero, so each local assignment occurs once. -/
def LocalCondition (B : BaseCover) (r : ℕ) (a : Fin B.A) (σ : BaseAssignment B) : Prop :=
  (∀ v, ¬ InBall B r a v → σ v = ⟨0, BaseAlphabetPositive B v⟩) ∧
  ∀ e, InBall B r a (.inl (B.left e)) → InBall B r a (.inr (B.right e)) →
    B.proj e (σ (.inl (B.left e))) = σ (.inr (B.right e))

abbrev LocalAssignment (B : BaseCover) (r : ℕ) (a : Fin B.A) :=
  {σ : BaseAssignment B // LocalCondition B r a σ}

noncomputable instance (B : BaseCover) (r : ℕ) (a : Fin B.A) :
    Fintype (LocalAssignment B r a) := Fintype.ofFinite _

def Radius (ell : ℕ) (i : Fin ell) : ℕ := 2 * (ell - (i.val + 1))

abbrev NeighborhoodLabeling (B : BaseCover) (ell : ℕ) :=
  (i : Fin ell) → (a : Fin B.A) → LocalAssignment B (Radius ell i) a

def NeighborhoodProduced (B : BaseCover) (ell : ℕ) : Prop :=
  0 < B.E ∧ ∀ (i : Fin ell) (a : Fin B.A), Nonempty (LocalAssignment B (Radius ell i) a)

/-- Restriction equality on the target ball, for the two specified occurrences.
Outside-ball zeros play no role in restriction. -/
def RestrictionSatisfied (B : BaseCover) {ell : ℕ} (σ : NeighborhoodLabeling B ell)
    (i j : Fin ell) (e e' : Fin B.E) : Prop :=
  ∀ v, InBall B (Radius ell j) (B.left e') v →
    (σ i (B.left e)).val v = (σ j (B.left e')).val v

/-- Uniform `b`, then two independent uniform incident occurrences, with replacement. -/
noncomputable def NeighborhoodPairValue (B : BaseCover) {ell : ℕ}
    (σ : NeighborhoodLabeling B ell) (i j : Fin ell) : ℝ := by
  classical
  exact if B.E = 0 then 1 else (∑ b : Fin B.B, ∑ e : Fin B.E, ∑ e' : Fin B.E,
    if B.right e = b ∧ B.right e' = b ∧ RestrictionSatisfied B σ i j e e' then (1 : ℝ) else 0) /
    ((B.B : ℝ) * B.degreeB ^ 2)

end BhangaleHypergraph.Main


