-- Prove2me | Definitions.Def_SivanLPTensor_Recovery_geometryModel
-- name    : SivanLPTensor_Recovery_geometryModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T05:31:53.214116+00:00
-- url     : https://prove2.me/theorems/4b92ec80-bba6-41d6-88cd-6936f6d46e0a
-- title:
--   Generic frames, sections, partitions, and adapted bases
-- statement:
--   A full-row-rank covector frame represents its row space, and its kernel represents the corresponding codimension section. A property is generic if a nonzero coordinate polynomial has a nonempty nonvanishing locus in the frame domain and implies that property there. Frames in a subspace use the coordinates of a basis of that subspace; this is a mathematical parameterization, not an algorithmic sampling oracle.
--   For a subspace family $(\mathcal F_i)$ define
--   $$R(S)=\dim\sum_{i\in S}\mathcal F_i,\qquad\mathcal L_i=\ker P\cap\mathcal F_i.$$
--   Partitions have nonempty pairwise disjoint parts and union exactly $S$. The Dilworth formula uses an attained minimum over every such partition, with value $\sum_{B\in\Pi}(R(B)-d)$. Annihilators use the Euclidean coordinate pairing. Adapted bases concatenate two section vectors with $d$ complement vectors. The span of alternating pairs supported in a subspace gives its alternating square. This interface supplies no generic-section or separation theorem as a field.
--   The shared generic-section predicate records all dimension, directness, complement and ordered-pair separation conclusions. Dependent corollaries conjoin it as a conclusion, preventing a missing basis from making their claims vacuous.
-- source:
--   Shiri Sivan, STOC 2027 submission #1294 (October 2026), §3.2, printed pp. 6, 10–12 / PDF pp. 8, 12–14; Theorem 7.1, printed p. 18 / PDF p. 20

import Definitions.Def_SivanLPTensor_Recovery_alternatingModel

noncomputable section

namespace SivanLPTensor.Recovery
open scoped BigOperators

abbrev Vec (D : ℕ) := Fin D → ℝ

def frameSpace {I : Type} [Fintype I] {k : ℕ}
    (E : Matrix I (Fin k) ℝ) : Submodule ℝ (I → ℝ) :=
  Submodule.span ℝ (Set.range (fun j => fun x => E x j))

def IsBasisFrame {I : Type} [Fintype I] {k : ℕ}
    (E : Matrix I (Fin k) ℝ) (W : Submodule ℝ (I → ℝ)) : Prop :=
  LinearIndependent ℝ (fun j => fun x => E x j) ∧ frameSpace E = W

def FullRows {I : Type} [Fintype I] {d : ℕ} (P : Matrix (Fin d) I ℝ) : Prop :=
  LinearIndependent ℝ (fun t => P t)

def kernel {I J : Type} [Fintype I] [Fintype J]
    (P : Matrix J I ℝ) : Submodule ℝ (I → ℝ) :=
  LinearMap.ker (Matrix.mulVecLin P)

def image {I : Type} [Fintype I] (A : Matrix I I ℝ) : Submodule ℝ (I → ℝ) :=
  LinearMap.range (Matrix.mulVecLin A)

/-- A nonzero polynomial witnesses a proper exceptional algebraic set in frame coordinates.
The validity domain is explicit, and is not allowed to be empty. -/
def Generic {K : Type} [Fintype K] (domain property : (K → ℝ) → Prop) : Prop :=
  ∃ f : MvPolynomial K ℝ, f ≠ 0 ∧
    (∃ x, domain x ∧ MvPolynomial.eval x f ≠ 0) ∧
    ∀ x, domain x → MvPolynomial.eval x f ≠ 0 → property x

def GenericFrame {I : Type} [Fintype I] {d : ℕ}
    (property : Matrix (Fin d) I ℝ → Prop) : Prop :=
  Generic (fun x : (Fin d × I) → ℝ => FullRows (fun t i => x (t,i)))
    (fun x => property (fun t i => x (t,i)))

/-- Coordinates of covectors lying in a specified Euclidean subspace. -/
def frameIn {I : Type} [Fintype I] {d : ℕ} (W : Submodule ℝ (I → ℝ))
    (c : Fin d × Fin (Module.finrank ℝ W) → ℝ) : Matrix (Fin d) I ℝ :=
  fun t x => ∑ s, c (t,s) * ((Module.finBasis ℝ W) s : I → ℝ) x

def GenericIn {I : Type} [Fintype I] {d : ℕ} (W : Submodule ℝ (I → ℝ))
    (property : Matrix (Fin d) I ℝ → Prop) : Prop :=
  Generic (fun c => FullRows (frameIn W c)) (fun c => property (frameIn W c))

def annihilator {I : Type} [Fintype I]
    (W : Submodule ℝ (I → ℝ)) : Submodule ℝ (I → ℝ) :=
  ⨅ v : W, LinearMap.ker
    ({ toFun := fun p => ∑ x, p x * (v : I → ℝ) x
       map_add' := by intros; simp [add_mul, Finset.sum_add_distrib]
       map_smul' := by intros; simp [Finset.mul_sum, mul_assoc] } : (I → ℝ) →ₗ[ℝ] ℝ)

def familySum {I : Type} [Fintype I] {r : ℕ}
    (F : Fin r → Submodule ℝ (I → ℝ)) (S : Finset (Fin r)) :
    Submodule ℝ (I → ℝ) := ⨆ i ∈ S, F i

def sectionFamily {I : Type} [Fintype I] {r d : ℕ}
    (F : Fin r → Submodule ℝ (I → ℝ)) (P : Matrix (Fin d) I ℝ) :=
  fun i => kernel P ⊓ F i

def totalSection {I : Type} [Fintype I] {r d : ℕ}
    (F : Fin r → Submodule ℝ (I → ℝ)) (P : Matrix (Fin d) I ℝ) :=
  ⨆ i, sectionFamily F P i

/-- Genuine finite partitions, all parts nonempty, disjoint, with union exactly S. -/
def IsPartition {r : ℕ} (S : Finset (Fin r)) (parts : Finset (Finset (Fin r))) : Prop :=
  (∀ B ∈ parts, B.Nonempty) ∧ (parts : Set (Finset (Fin r))).Pairwise Disjoint ∧ parts.biUnion id = S

def partitionValue {I : Type} [Fintype I] {r : ℕ}
    (F : Fin r → Submodule ℝ (I → ℝ)) (d : ℕ) (parts : Finset (Finset (Fin r))) : ℕ :=
  ∑ B ∈ parts, Module.finrank ℝ (familySum F B) - d

/-- The attaining-minimum formulation avoids a default infimum on invalid partitions. -/
def DilworthFormula {I : Type} [Fintype I] {r d : ℕ}
    (F : Fin r → Submodule ℝ (I → ℝ)) (P : Matrix (Fin d) I ℝ) : Prop :=
  ∀ S : Finset (Fin r), S.Nonempty → ∃ parts, IsPartition S parts ∧
    Module.finrank ℝ (familySum (sectionFamily F P) S) = partitionValue F d parts ∧
    ∀ parts', IsPartition S parts' → partitionValue F d parts ≤ partitionValue F d parts'

/-- The alternating two-tensors supported on W. -/
def alternatingSquare {I : Type} [Fintype I] (W : Submodule ℝ (I → ℝ)) :
    Submodule ℝ (Matrix I I ℝ) :=
  Submodule.span ℝ { B | ∃ x ∈ W, ∃ y ∈ W, B = altTwo x y }

def concatenate {I : Type} {d : ℕ} (L : Matrix I (Fin 2) ℝ)
    (R : Matrix I (Fin d) ℝ) : Matrix I (Fin (d + 2)) ℝ :=
  fun x j => if h : j.val < 2 then L x ⟨j.val,h⟩ else R x ⟨j.val-2,by omega⟩

/-- All conclusions of the generic-section lemma, shared by its dependent statements. -/
def SectionGeometry {I : Type} [Fintype I] {r k : ℕ}
    (F : Fin r → Submodule ℝ (I → ℝ)) (d : ℕ)
    (P : Matrix (Fin k) I ℝ) : Prop :=
  (∀ i, Module.finrank ℝ (sectionFamily F P i) = 2) ∧
  (∀ (v : (i : Fin r) → sectionFamily F P i),
    (∑ i, (v i : I → ℝ)) = 0 → ∀ i, v i = 0) ∧
  ∀ R : Fin r → Submodule ℝ (I → ℝ),
    (∀ i, Disjoint (sectionFamily F P i) (R i) ∧
      sectionFamily F P i ⊔ R i = F i) →
    (∀ i, Module.finrank ℝ (R i) = d) ∧
    ∀ i j, i ≠ j → ∃ v : I → ℝ, v ≠ 0 ∧ v ∈ R j ∧
      Disjoint (R i) (Submodule.span ℝ {v} ⊔ totalSection F P) ∧
      Disjoint (Submodule.span ℝ {v}) (totalSection F P)

end SivanLPTensor.Recovery


