-- Prove2me | Definitions.Def_GroupLabeledMatroid_Proximity_LabelModel
-- name    : GroupLabeledMatroid_Proximity_LabelModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:06:23.591937+00:00
-- url     : https://prove2.me/theorems/00a1af74-47f8-455e-abb0-ac81c30f9051
-- title:
--   Finite matroid label sums, costs, and global optimality
-- statement:
--   Let $M$ be a matroid on a finite ground set $E$, with labels $\ell:E\to G$ in an arbitrary abelian group and real costs $c:E\to\mathbb R$. For finite subsets define
--
--   $$\ell(X)=\sum_{e\in X}\ell(e),\qquad c(X)=\sum_{e\in X}c(e),\qquad d(A,B)=|A\setminus B|.$$
--
--   A minimum base minimizes cost over all bases. An $F$-avoiding base has label sum outside the finite set $F$, and a minimum avoiding base minimizes cost over the entire avoiding family. A unique minimum $\ell(B)$-base is a base $B$ minimizing cost in its label fiber, with equality only for $B$. This permits more expensive bases of the same label and permits ties outside this fiber.
--
--   The finite threshold label set and individual color classes are
--
--   $$\ell_{\le\theta}(M)=\{\ell(D):D\text{ is a base},\ c(D)\le\theta\},\qquad E_h=\{e\in E:\ell(e)=h\}.$$
--
--   A block pair consists of disjoint bases $A,B$ covering the ground, with $A$ minimum and $B$ unique minimum in its label fiber. These definitions provide the shared interface for proximity and its counting lemmas. **Formalization Note** Subsets are finite sets in a finite ambient type; the matroid's own ground can be a proper subset. Natural ranks are the finite values of Mathlib's extended natural rank. Decidable equality is a classical encoding choice, not a finiteness restriction on $G$.
-- source:
--   Siyue Liu, Taihei Oki, Chao Xu, Proximity Theorem and FPT Algorithm for Minimum Group-labeled Matroid Bases, STOC 2027 submission #554 (October 2026), pp. 1, 5–6, §2; p. 8, §3.2

import Mathlib

namespace GroupLabeledMatroid.Proximity

variable {E G : Type*} [Fintype E] [DecidableEq E] [AddCommGroup G] [DecidableEq G]

/-- Source pp. 1, 5–6: labels are summed, not imaged. -/
def labelSum (ℓ : E → G) (X : Finset E) : G := ∑ e ∈ X, ℓ e

def costSum (c : E → ℝ) (X : Finset E) : ℝ := ∑ e ∈ X, c e

noncomputable def ground (M : Matroid E) : Finset E := by
  classical
  exact M.E.toFinset

/-- A minimum over all bases, allowing ties. -/
def IsMinimumBase (M : Matroid E) (c : E → ℝ) (A : Finset E) : Prop :=
  M.IsBase (A : Set E) ∧
    ∀ D : Finset E, M.IsBase (D : Set E) → costSum c A ≤ costSum c D

def IsAvoidingBase (M : Matroid E) (ℓ : E → G) (F : Finset G) (B : Finset E) : Prop :=
  M.IsBase (B : Set E) ∧ labelSum ℓ B ∉ F

/-- Minimum over the entire avoiding family, with no distance restriction. -/
def IsMinimumAvoidingBase (M : Matroid E) (ℓ : E → G) (c : E → ℝ)
    (F : Finset G) (B : Finset E) : Prop :=
  IsAvoidingBase M ℓ F B ∧
    ∀ D : Finset E, IsAvoidingBase M ℓ F D → costSum c B ≤ costSum c D

/-- Uniqueness only inside B's label fiber; more expensive bases in that fiber are allowed. -/
def IsUniqueLabelMinimum (M : Matroid E) (ℓ : E → G) (c : E → ℝ)
    (B : Finset E) : Prop :=
  M.IsBase (B : Set E) ∧
    ∀ D : Finset E, M.IsBase (D : Set E) → labelSum ℓ D = labelSum ℓ B →
      costSum c B ≤ costSum c D ∧ (costSum c D = costSum c B → D = B)

def baseDistance (A B : Finset E) : ℕ := (A \ B).card

/-- Finite even when the label group is infinite. -/
noncomputable def labelsUnder (M : Matroid E) (ℓ : E → G) (c : E → ℝ)
    (θ : ℝ) : Finset G := by
  classical
  exact ((ground M).powerset.filter
    (fun (D : Finset E) => M.IsBase (D : Set E) ∧ costSum c D ≤ θ)).image (labelSum ℓ)

noncomputable def colorClass (M : Matroid E) (ℓ : E → G) (h : G) : Finset E := by
  classical
  exact (ground M).filter (fun e => ℓ e = h)

/-- All ranks here are finite, since the ambient type is finite. -/
noncomputable def rankOn (M : Matroid E) (X : Finset E) : ℕ :=
  (M.eRk (X : Set E)).toNat

/-- The source's local block assumptions, with no counting or proximity axiom. -/
def IsBlockPair (M : Matroid E) (ℓ : E → G) (c : E → ℝ)
    (A B : Finset E) : Prop :=
  IsMinimumBase M c A ∧ IsUniqueLabelMinimum M ℓ c B ∧
    Disjoint A B ∧ ((A ∪ B : Finset E) : Set E) = M.E

end GroupLabeledMatroid.Proximity


