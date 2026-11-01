-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P94
-- name    : QAlgorithms_Papers_Independent_Intakenext100_P94
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-31T08:39:00.656747+00:00
-- url     : https://prove2.me/theorems/81612dbe-edd1-4832-8284-95369fa45e59
-- title:
--   Definitions for The general theory of permutation equivarant neural networks and higher order graph variational encoders
-- statement:
--   The objects the formalized statements of *The general theory of permutation equivarant neural networks and higher order graph variational encoders* (arXiv:2004.03990) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `Perm`
--   - `Tensor`
--   - `permutationTensorAction`: Simultaneous inverse reindexing, source PDF p.2, Eq.(2).
--   - `equivariantLinearMaps`: Linear intertwiners, source PDF pp.3–4; no bias or nonlinearity is counted.
--   - `supportedSpace`: Tensors supported on a specified equality pattern (PDF pp.3,15).
--   - `DistinctSpace`
--   - `distinctAction`: The distinct-index space is preserved under the source's action.
--   - `pointwise`: Shared pointwise nonlinearity; this is applied after the linear map (PDF p.3).
--   - `tensorRowSum`: Row, column, total and trace contractions (PDF pp.4–5).
--   - `colSum`
--   - `totalSum`
--   - `activationTraceSum`
--   - `sevenFormula`: Theorem 2's seven terms, evaluated only off the diagonal (PDF p.4).
--   - `fifteenFormula`: Corollary 4's fifteen terms, including the trace overbars (PDF p.5).
--   - `IsRealIrreducible`: A real irreducible model means a nonzero representation with no proper, nonzero invariant real linear subspace (PDF p.4).
--   - `ModelsInequivalent`: Models are inequivalent if no invertible intertwiner exists (PDF p.4).
--   - `FourierBlocks`
--   - `fourierColumnAction`: Each column is acted on by the same irreducible model (PDF p.4).
--   - `FourierWeights`
--   - `applyBlocks`: Fourier-space right multiplication; source PDF p.4, Theorem 3.
--   - `finalPoints`: The subgroup fixing the final k points individually, PDF p.12. The embedding is typed and the natural subtraction is protected by k≤n.
--   - `pointStabilizer`
--   - `Cosets`
--   - `quotientValues`: Representative formula with well-definedness asserted by Propositions 5–7; choosing out does not assume the desired bijection or intertwining conclusion.
--   - `cosetTranslate`
--   - `vectorValues`
--   - `realYoung`: Real Young symmetrizer: same concrete row/column permutation sets as the accepted Specht construction, with real scalars as required by PDF p.4.
--   - `realSpecht`
--   - `HasTensorType`: An actual equivariant isomorphism to copies of concrete real Specht ideals. The group acts by left translation inside each ideal. No Fourier coordinates or multiplicities are assumed as an input field (PDF p.4).
--   - `secondShapes`: Printed partition order, source PDF p.4.
--   - `thirdShapes`
--   - `pairPattern`: The three exactly-two-equal patterns are indexed by their singleton position.
--   - `IsRecipe`: A contraction partitions the three input slots into equality blocks; each block is named by its least slot. A selected subset of blocks is retained, and the others are summed. This is precisely the four contraction lists on pp.15–16.
--   - `Recipe`
--   - `Retained`
--   - `PlacedRecipe`: Every injection of the retained slots into the available output slots is used.
--   - `contractionKernel`: Coefficient kernel for one contraction: equal input indices within a block, retained blocks fixed to the selected output entries; other blocks summed freely. Distinct blocks are not required to receive distinct vertex labels.
--   - `ThirdIndex`: 77 generic terms, three sets of 37 pair-supported corrections, and 15 all-diagonal corrections (PDF p.16, Table 4).
--   - `thirdKernel`: Equality-supported corrections are added to the generic formula. The pair index names the singleton output slot; Fin 3 addition is cyclic.
--   - `thirdFormula`: Concrete weighted contraction construction, source PDF pp.15–16.
--   - `promote`: Zero-extension promotion along an injective correspondence, PDF p.6, Eq.(6). Off-image values are explicitly zero; overlapping children add their contributions.
--   - `relabelEmbedding`: The correspondence itself is relabelled, not held fixed (PDF pp.5–6).
--   - `tensorOuterProduct`: Outer product permits higher tensor order; no contraction or bias is implicit.
-- source:
--   The general theory of permutation equivarant neural networks and higher order graph variational encoders, arXiv:2004.03990v1, https://arxiv.org/abs/2004.03990v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_SpechtModules

/-!
The accepted-library basename matches reported by the previous check describe
different concepts: Dependency50.P09.tensorAction is a quantum superoperator
tensor product; Gap48.P28.intertwinerSpace is a complex three-representation
Clebsch–Gordan matrix space; Renew46.P15.rowSum is a GT-pattern row sum;
Information100.P53.traceSum is a pairwise discrimination trace-norm bound;
Information100.P26.Blocks is a positive coordinate-block decomposition;
Claimed50.P13.blockAction is a tensor power of a quantum channel;
Information100.P07.Weights is a probability predicate; and the outer products
in Information100.P19/P26 conjugate a complex vector. None is the real tensor,
two-action linear-map space, Fourier multiplicity data or order-raising product
of this paper. Their exact bodies were compared before retaining these local
constructions under distinct descriptive names. No frozen body is duplicated.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P94

open scoped BigOperators

attribute [local instance] Classical.propDecidable

abbrev Perm (n : ℕ) := Equiv.Perm (Fin n)

abbrev Tensor (n k : ℕ) := (Fin k → Fin n) → ℝ

/-- Simultaneous inverse reindexing, source PDF p.2, Eq.(2). -/
def permutationTensorAction {n k : ℕ} (s : Perm n) : Tensor n k →ₗ[ℝ] Tensor n k where
  toFun F := fun t => F (fun a => s.symm (t a))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

example {n k : ℕ} (F : Tensor n k) : permutationTensorAction (1 : Perm n) F = F := rfl

/-- Linear intertwiners, source PDF pp.3–4; no bias or nonlinearity is counted. -/
def equivariantLinearMaps {G E H : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup H] [Module ℝ H] (A : G → E →ₗ[ℝ] E)
    (B : G → H →ₗ[ℝ] H) : Submodule ℝ (E →ₗ[ℝ] H) where
  carrier := {L | ∀ s x, L (A s x) = B s (L x)}
  zero_mem' := by simp
  add_mem' := by
    intro L M hL hM s x
    simp only [LinearMap.add_apply, map_add, hL s x, hM s x]
  smul_mem' := by
    intro c L hL s x
    simp only [LinearMap.smul_apply, map_smul, hL s x]

/-- Tensors supported on a specified equality pattern (PDF pp.3,15). -/
def supportedSpace {n k : ℕ} (P : (Fin k → Fin n) → Prop) :
    Submodule ℝ (Tensor n k) where
  carrier := {F | ∀ t, ¬ P t → F t = 0}
  zero_mem' := by simp
  add_mem' := by intro F G hF hG t ht; simp [hF t ht, hG t ht]
  smul_mem' := by intro c F hF t ht; simp [hF t ht]

abbrev DistinctSpace (n k : ℕ) := supportedSpace (n := n) (k := k) Function.Injective

/-- The distinct-index space is preserved under the source's action. -/
def distinctAction {n k : ℕ} (s : Perm n) : DistinctSpace n k →ₗ[ℝ] DistinctSpace n k where
  toFun F := ⟨permutationTensorAction s F.val, by
    intro t ht
    apply F.property
    intro hi
    apply ht
    intro a b hab
    exact hi (congrArg s.symm hab)⟩
  map_add' _ _ := by rfl
  map_smul' _ _ := by rfl

/-- Shared pointwise nonlinearity; this is applied after the linear map (PDF p.3). -/
def pointwise {n k : ℕ} (xi : ℝ → ℝ) (F : Tensor n k) : Tensor n k := fun t => xi (F t)

/-- Row, column, total and trace contractions (PDF pp.4–5). -/
def tensorRowSum {n : ℕ} (F : Tensor n 2) (i : Fin n) : ℝ := ∑ j, F ![i,j]

def colSum {n : ℕ} (F : Tensor n 2) (i : Fin n) : ℝ := ∑ j, F ![j,i]

def totalSum {n : ℕ} (F : Tensor n 2) : ℝ := ∑ i, ∑ j, F ![i,j]

def activationTraceSum {n : ℕ} (F : Tensor n 2) : ℝ := ∑ i, F ![i,i]

/-- Theorem 2's seven terms, evaluated only off the diagonal (PDF p.4). -/
def sevenFormula {n : ℕ} (w : Fin 7 → ℝ) (F : Tensor n 2) (i j : Fin n) : ℝ :=
  w 0 * F ![i,j] + w 1 * F ![j,i] + w 2 * tensorRowSum F i + w 3 * colSum F i +
    w 4 * colSum F j + w 5 * tensorRowSum F j + w 6 * totalSum F

/-- Corollary 4's fifteen terms, including the trace overbars (PDF p.5). -/
def fifteenFormula {n : ℕ} (w : Fin 15 → ℝ) (F : Tensor n 2) (i j : Fin n) : ℝ :=
  w 0 * F ![i,j] + w 1 * F ![j,i] + w 2 * tensorRowSum F i + w 3 * colSum F i +
    w 4 * colSum F j + w 5 * tensorRowSum F j + w 6 * totalSum F + w 7 * activationTraceSum F +
    w 8 * F ![i,i] + w 9 * F ![j,j] +
    if i = j then w 10 * F ![i,i] + w 11 * activationTraceSum F + w 12 * totalSum F +
      w 13 * tensorRowSum F i + w 14 * colSum F i else 0

example {n : ℕ} (F : Tensor n 2) (i : Fin n) : tensorRowSum F i = ∑ j, F ![i,j] := rfl

/-- A real irreducible model means a nonzero representation with no proper,
nonzero invariant real linear subspace (PDF p.4). -/
def IsRealIrreducible {n d : ℕ}
    (rho : Perm n →* Module.End ℝ (Fin d → ℝ)) : Prop :=
  0 < d ∧ ∀ S : Submodule ℝ (Fin d → ℝ),
    (∀ s x, x ∈ S → rho s x ∈ S) → S = ⊥ ∨ S = ⊤

/-- Models are inequivalent if no invertible intertwiner exists (PDF p.4). -/
def ModelsInequivalent {n d e : ℕ}
    (rho : Perm n →* Module.End ℝ (Fin d → ℝ))
    (eta : Perm n →* Module.End ℝ (Fin e → ℝ)) : Prop :=
  ¬ ∃ U : (Fin d → ℝ) ≃ₗ[ℝ] (Fin e → ℝ), ∀ s x, U (rho s x) = eta s (U x)

abbrev FourierBlocks {I : Type*} (d tau : I → ℕ) :=
  (a : I) → Matrix (Fin (d a)) (Fin (tau a)) ℝ

/-- Each column is acted on by the same irreducible model (PDF p.4). -/
def fourierColumnAction {n : ℕ} {I : Type*} {d tau : I → ℕ}
    (rho : (a : I) → Perm n →* Module.End ℝ (Fin (d a) → ℝ))
    (s : Perm n) (F : FourierBlocks d tau) : FourierBlocks d tau :=
  fun a r c => rho a s (fun b => F a b c) r

abbrev FourierWeights {I : Type*} (tau upsilon : I → ℕ) :=
  (a : I) → Matrix (Fin (tau a)) (Fin (upsilon a)) ℝ

/-- Fourier-space right multiplication; source PDF p.4, Theorem 3. -/
def applyBlocks {I : Type*} {d tau upsilon : I → ℕ}
    (w : FourierWeights tau upsilon) (F : FourierBlocks d tau) : FourierBlocks d upsilon :=
  fun a => F a * w a

example {I : Type*} {d tau upsilon : I → ℕ} (F : FourierBlocks d tau)
    (w : FourierWeights tau upsilon) (a : I) : applyBlocks w F a = F a * w a := rfl

/-- The subgroup fixing the final k points individually, PDF p.12.
The embedding is typed and the natural subtraction is protected by k≤n. -/
def finalPoints {n k : ℕ} (hkn : k ≤ n) : Fin k ↪ Fin n where
  toFun a := ⟨n - 1 - a.val, by omega⟩
  inj' := by intro a b h; apply Fin.ext; have := congrArg Fin.val h; dsimp at this; omega

def pointStabilizer {n k : ℕ} (e : Fin k ↪ Fin n) : Subgroup (Perm n) where
  carrier := {s | ∀ a, s (e a) = e a}
  one_mem' := by intro a; rfl
  mul_mem' := by intro s t hs ht a; change s (t (e a)) = e a; rw [ht, hs]
  inv_mem' := by
    intro s hs a
    apply s.injective
    simpa using (hs a).symm

abbrev Cosets {n k : ℕ} (e : Fin k ↪ Fin n) :=
  Quotient (QuotientGroup.leftRel (pointStabilizer e))

/-- Representative formula with well-definedness asserted by Propositions 5–7;
choosing out does not assume the desired bijection or intertwining conclusion. -/
def quotientValues {n k : ℕ} (e : Fin k ↪ Fin n) (F : Tensor n k) : Cosets e → ℝ :=
  fun q => F (fun a => q.out (e a))

def cosetTranslate {n k : ℕ} (e : Fin k ↪ Fin n) (s : Perm n) (q : Cosets e) : Cosets e :=
  Quotient.mk _ (s * q.out)

def vectorValues {n : ℕ} (hn : 1 ≤ n) (f : Fin n → ℝ) :
    Cosets (finalPoints hn) → ℝ :=
  quotientValues (finalPoints hn) (fun t => f (t 0))

example {n k : ℕ} (e : Fin k ↪ Fin n) : (1 : Perm n) ∈ pointStabilizer e :=
  (pointStabilizer e).one_mem

/-- Real Young symmetrizer: same concrete row/column permutation sets as the
accepted Specht construction, with real scalars as required by PDF p.4. -/
def realYoung {n : ℕ} (lambda : QAlgorithms.Schur.Partition n n) :
    Matrix (Perm n) (Perm n) ℝ := fun g h =>
  ∑ a ∈ QAlgorithms.Schur.rowPermutations lambda,
    ∑ b ∈ QAlgorithms.Schur.columnPermutations lambda,
      if g = h * a * b then (((Equiv.Perm.sign b : ℤˣ) : ℤ) : ℝ) else 0

def realSpecht {n : ℕ} (lambda : QAlgorithms.Schur.Partition n n) :
    Submodule ℝ (Perm n → ℝ) := LinearMap.range (Matrix.toLin' (realYoung lambda))

/-- An actual equivariant isomorphism to copies of concrete real Specht ideals.
The group acts by left translation inside each ideal. No Fourier coordinates
or multiplicities are assumed as an input field (PDF p.4). -/
def HasTensorType {n k r : ℕ} (S : Submodule ℝ (Tensor n k))
    (lambda : Fin r → QAlgorithms.Schur.Partition n n) (tau : Fin r → ℕ) : Prop :=
  ∃ U : S ≃ₗ[ℝ] ((a : Fin r) → Fin (tau a) → realSpecht (lambda a)),
    ∀ (s : Perm n) (F : S), ∃ G : S,
      G.val = permutationTensorAction s F.val ∧
      ∀ a c g, (U G a c).val g = (U F a c).val (s.symm * g)

/-- Printed partition order, source PDF p.4. -/
def secondShapes (n : ℕ) : Fin 4 → List ℕ := ![[n], [n-1,1], [n-2,2], [n-2,1,1]]

def thirdShapes (n : ℕ) : Fin 7 → List ℕ :=
  ![[n], [n-1,1], [n-2,2], [n-2,1,1], [n-3,3], [n-3,2,1], [n-3,1,1,1]]

example {n : ℕ} (lambda : QAlgorithms.Schur.Partition n n) :
    realSpecht lambda = LinearMap.range (Matrix.toLin' (realYoung lambda)) := rfl

/-- The three exactly-two-equal patterns are indexed by their singleton position. -/
def pairPattern {n : ℕ} (a : Fin 3) (t : Fin 3 → Fin n) : Prop :=
  t (a+1) = t (a+2) ∧ t a ≠ t (a+1)

/-- A contraction partitions the three input slots into equality blocks; each
block is named by its least slot. A selected subset of blocks is retained, and
the others are summed. This is precisely the four contraction lists on pp.15–16. -/
def IsRecipe (p : (Fin 3 → Fin 3) × Finset (Fin 3)) : Prop :=
  (∀ a, p.1 a ≤ a ∧ p.1 (p.1 a) = p.1 a) ∧ ∀ a ∈ p.2, p.1 a = a

example : IsRecipe ((id : Fin 3 → Fin 3), Finset.univ) := by simp [IsRecipe]

abbrev Recipe := {p : (Fin 3 → Fin 3) × Finset (Fin 3) // IsRecipe p}

abbrev Retained (p : Recipe) := {a : Fin 3 // a ∈ p.val.2}

/-- Every injection of the retained slots into the available output slots is used. -/
abbrev PlacedRecipe (r : ℕ) := Σ p : Recipe, (Retained p ↪ Fin r)

/-- Coefficient kernel for one contraction: equal input indices within a block,
retained blocks fixed to the selected output entries; other blocks summed freely.
Distinct blocks are not required to receive distinct vertex labels. -/
def contractionKernel {n r : ℕ} (p : PlacedRecipe r)
    (t : Fin r → Fin n) (u : Fin 3 → Fin n) : ℝ :=
  if (∀ a b, p.1.val.1 a = p.1.val.1 b → u a = u b) ∧
      (∀ a : Retained p.1, u a.val = t (p.2 a)) then 1 else 0

/-- 77 generic terms, three sets of 37 pair-supported corrections, and 15
all-diagonal corrections (PDF p.16, Table 4). -/
abbrev ThirdIndex := PlacedRecipe 3 ⊕ ((Fin 3 × PlacedRecipe 2) ⊕ PlacedRecipe 1)

/-- Equality-supported corrections are added to the generic formula. The pair
index names the singleton output slot; Fin 3 addition is cyclic. -/
def thirdKernel {n : ℕ} (p : ThirdIndex) (t u : Fin 3 → Fin n) : ℝ :=
  match p with
  | .inl q => contractionKernel q t u
  | .inr (.inl (a,q)) =>
    if t (a+1) = t (a+2) then contractionKernel q ![t (a+1),t a] u else 0
  | .inr (.inr q) =>
    if ∀ a b, t a = t b then contractionKernel q ![t 0] u else 0

/-- Concrete weighted contraction construction, source PDF pp.15–16. -/
def thirdFormula {n : ℕ} (w : ThirdIndex → ℝ) (F : Tensor n 3) : Tensor n 3 :=
  fun t => ∑ p : ThirdIndex, w p * ∑ u : Fin 3 → Fin n, thirdKernel p t u * F u

example {n : ℕ} (F : Tensor n 3) : thirdFormula (fun _ => 0) F = 0 := by
  ext t
  simp [thirdFormula]

/-- Zero-extension promotion along an injective correspondence, PDF p.6, Eq.(6).
Off-image values are explicitly zero; overlapping children add their contributions. -/
def promote {m n k : ℕ} (chi : Fin m ↪ Fin n) (F : Tensor m k) : Tensor n k :=
  fun t => ∑ u : Fin k → Fin m, if (fun a => chi (u a)) = t then F u else 0

/-- The correspondence itself is relabelled, not held fixed (PDF pp.5–6). -/
def relabelEmbedding {m n : ℕ} (chi : Fin m ↪ Fin n) (s : Perm n) (p : Perm m) :
    Fin m ↪ Fin n where
  toFun i := s (chi (p.symm i))
  inj' := s.injective.comp (chi.injective.comp p.symm.injective)

/-- Outer product permits higher tensor order; no contraction or bias is implicit. -/
def tensorOuterProduct {n k l : ℕ} (F : Tensor n k) (G : Tensor n l) :
    ((Fin k ⊕ Fin l) → Fin n) → ℝ :=
  fun t => F (fun a => t (.inl a)) * G (fun b => t (.inr b))

example {m n : ℕ} (chi : Fin m ↪ Fin n) (s : Perm n) (p : Perm m) (i : Fin m) :
    relabelEmbedding chi s p i = s (chi (p.symm i)) := rfl

end QAlgorithms.Papers.Independent.Intakenext100.P94


