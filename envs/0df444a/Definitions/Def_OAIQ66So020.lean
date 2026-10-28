-- Prove2me | Definitions.Def_OAIQ66So020
-- name    : OAIQ66So020
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T02:23:48.454848+00:00
-- url     : https://prove2.me/theorems/5b77e17a-0358-4185-9776-eb3bd84381ab
-- title:
--   Definitions bundle OAIQ66So020 of the split of OpenAI, Simple F-infinity overgroups of groups with decidable word problem (OpenAI result)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SimpleFInftyOvergroups.main`, carved from OpenAI's openai/math development (OpenAI, *Simple F-infinity overgroups of groups with decidable word problem (OpenAI result)*, OpenAI Math Release, September 23, 2026, result family 250, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 145 declarations of OpenAI's Lean: 32 definitions, 11 instances and 102 theorems. The definitions and types are `OAI.NoncommElementary.diagonalKernel`, `OAI.NoncommElementary.exchange`, `OAI.SimpleFInftyOvergroups.ContextualEncoding.GroupFamily.test`, `OAI.SimpleFInftyOvergroups.ContextualEncoding.ProductFamily.grade`, `OAI.SimpleFInftyOvergroups.ContextualEncoding.ProductFamily.normal`, `OAI.SimpleFInftyOvergroups.ContextualEncoding.ProductFamily.test`, `OAI.SimpleFInftyOvergroups.ContextualEncoding.ProductFamily.value`, `OAI.SimpleFInftyOvergroups.ContextualEncoding.Source.raw`, `OAI.SimpleFInftyOvergroups.ContextualEncoding.Source.rel`, `OAI.SimpleFInftyOvergroups.EffectiveNames.MatrixWords.calculus`, `OAI.SimpleFInftyOvergroups.EffectiveNames.MatrixWords.grade`, `OAI.SimpleFInftyOvergroups.EffectiveNames.MatrixWords.groupLabel`, `OAI.SimpleFInftyOvergroups.EffectiveNames.MatrixWords.interpretation`, `OAI.SimpleFInftyOvergroups.EffectiveNames.MatrixWords.pointLabel`, `OAI.SimpleFInftyOvergroups.RingAssembly.binaryD`, `OAI.SimpleFInftyOvergroups.RingAssembly.binaryData`, `OAI.SimpleFInftyOvergroups.RingAssembly.binaryPhi`, `OAI.SimpleFInftyOvergroups.RingAssembly.binaryS`, `OAI.SimpleFInftyOvergroups.SemanticEncoding.NormalPresentation.sectionMap`, `OAI.SourceEnlargement.Double.W`, `OAI.SourceEnlargement.Double.W₁`, `OAI.SourceEnlargement.Double.Y`, `OAI.SourceEnlargement.Double.orbitSet`, `OAI.SourceEnlargement.enlargedGroup`, `OAI.SourceEnlargement.groupEmbedding`, `OAI.SourceEnlargement.j`, `OAI.Steinberg.column`, `OAI.Steinberg.columnRoot`, `OAI.Steinberg.row`, `OAI.Steinberg.rowRoot`, `OAI.Steinberg.transportWord`, `OAI.TwistedBrin.GermBrick.Restricts`.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory, in whole or in part: `FiniteType_ClassifyingSpacesFiniteExtensionGeometricFromProducts`, `FiniteType_NonunitalCompression`, `FiniteType_PrefixPermutation`, `FiniteType_PresentationGeometry`, `FiniteType_RingExchange`, `FiniteType_StageConstruction`, `FiniteType_SteinbergSixThree`, `FiniteType_TwistedBrin`, `SimpleOvergroups_BoundedFamilyTests`, `SimpleOvergroups_CodeEmbedding`, `SimpleOvergroups_ContextualCompiler`, `SimpleOvergroups_ContextualTables`, `SimpleOvergroups_ContractedNormalForms`, `SimpleOvergroups_EffectiveFamilies`, `SimpleOvergroups_EffectiveTables`, `SimpleOvergroups_FamilyProgram`, `SimpleOvergroups_FamilyTables`, `SimpleOvergroups_FirstFamilies`, `SimpleOvergroups_MatrixEffective`, `SimpleOvergroups_MatrixNames`, `SimpleOvergroups_MatrixWords`, `SimpleOvergroups_PolynomialNames`, `SimpleOvergroups_RingAssemblyTools`, `SimpleOvergroups_TwoEnlargements`.
--
--   **Imports.** It imports the bundles `OAIQ66So011`, `OAIQ66So012`, `OAIQ66So013`, `OAIQ66So014` and `OAIQ66So015` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ66So025` and `OAIQ66So026`.
-- source:
--   OpenAI, Simple F-infinity overgroups of groups with decidable word problem (OpenAI result), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 250; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/ComparatorChallenges/SimpleOvergroups.lean; Apache License 2.0); definitions carved from lean/OAI/GroupTheory at commit 1581d4c

import Mathlib
import Definitions.Def_OAIQ66So011
import Definitions.Def_OAIQ66So012
import Definitions.Def_OAIQ66So013
import Definitions.Def_OAIQ66So014
import Definitions.Def_OAIQ66So015

section
-- module Solutions.OAIQ066_SO.FiniteType_PresentationGeometry
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CoreDeck.action _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.groupHomology.chainsFunctor_additive _root_.OAI.groupHomology.functor_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Function Topology

noncomputable section

namespace PresentationGeometry

namespace Rose

instance instCWComplexSpaceUniv (k : ℕ) : CWComplex (univ : Set (Space k)) :=
  Cells.cwComplex (attaching k) point_dimension

instance instFiniteSpaceUnivEmptyCollectionSet (k : ℕ) : RelCWComplex.Finite (univ : Set (Space k)) :=
  Cells.cwComplex_finite (attaching k) point_dimension

instance instPathConnectedSpaceSpace (k : ℕ) : PathConnectedSpace (Space k) :=
  Cells.pathConnectedSpace (attaching k) (by decide)

theorem dimension (k n : ℕ) (i : RelCWComplex.cell (univ : Set (Space k)) n) : n < 2 := by
  change Cells.NewCell (X := Point) (k := k) (d := 1) n at i
  rcases i with i | ⟨i, ⟨h⟩⟩
  · have := point_dimension n i
    omega
  · omega

instance instNonemptySpace (k : ℕ) : Nonempty (Space k) := ⟨basepoint k⟩

end Rose

end PresentationGeometry

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_ClassifyingSpacesFiniteExtensionGeometricFromProducts
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped Pointwise

namespace NoncommElementary
variable {R n : Type*} [Ring R] [Fintype n] [DecidableEq n]

lemma diagonal_conjugate_root (d : n → Rˣ) (i j : n) (h : i≠j) (a : R) :
    diagonal d*root i j h a*(diagonal d)⁻¹=
      root i j h ((d i).val*a*(d j).inv) := by
  apply Units.ext
  change Matrix.diagonal (fun k => (d k).val)*(1+Matrix.single i j a)*
    Matrix.diagonal (fun k => (d k).inv)=1+_
  rw [mul_add,mul_one,add_mul,Matrix.diagonal_mul_diagonal',diagonal_single,single_diagonal]
  simp

lemma diagonal_normalizes (d : n → Rˣ) : diagonal d∈Subgroup.normalizer (elementary (R:=R) (n:=n) : Set (Matrix n n R)ˣ) := by
  have hn : (diagonal (R:=R) (n:=n)).range≤Subgroup.normalizer (elementary (R:=R) (n:=n) : Set (Matrix n n R)ˣ) := by
    apply Subgroup.le_normalizer_closure_iff.mpr
    rintro x ⟨d,rfl⟩ g ⟨i,j,h,a,rfl⟩
    rw [diagonal_conjugate_root]
    exact root_mem _ _ _ _
  exact hn ⟨d,rfl⟩

end NoncommElementary

open scoped commutatorElement

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_NonunitalCompression
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Pointwise
open scoped commutatorElement

namespace Steinberg

variable {n m R : Type*} [Ring R] [Fintype n] [DecidableEq n]

def columnRoot (f : n ↪ m) (k : m) (hk : ∀ i, f i ≠ k) (i : n) (a : R) :
    Group m R := root (f i) k (hk i) a

omit [Fintype n] [DecidableEq n] in
lemma columnRoot_commute (f : n ↪ m) (k : m) (hk : ∀ i, f i ≠ k)
    (i j : n) (a b : R) : Commute (columnRoot f k hk i a) (columnRoot f k hk j b) :=
  root_commute _ _ _ _ _ _ (hk i) (Ne.symm (hk j)) a b

def column (f : n ↪ m) (k : m) (hk : ∀ i, f i ≠ k) :
    (n → Multiplicative R) →* Group m R where
  toFun v := Finset.univ.noncommProd (fun i => columnRoot f k hk i (v i).toAdd)
    (by intro i _ j _ _; exact columnRoot_commute f k hk i j _ _)
  map_one' := by
    apply (Finset.noncommProd_eq_pow_card _ _ _ 1 ?_).trans (one_pow _)
    intro i _
    exact root_zero _ _ _
  map_mul' v w := by
    let c (u : n → Multiplicative R) := fun i => columnRoot f k hk i (u i).toAdd
    have he : c (v*w) = c v * c w := by
      ext i
      exact (root_add _ _ _ _ _).symm
    change Finset.univ.noncommProd (c (v*w)) _ = _
    simp only [he]
    exact Finset.noncommProd_mul_distrib _ _ _ _
      (by intro i _ j _ _; exact columnRoot_commute f k hk i j _ _)

lemma column_single (f : n ↪ m) (k : m) (hk : ∀ i, f i ≠ k) (i : n) (a : R) :
    column f k hk (Pi.mulSingle i (Multiplicative.ofAdd a)) = columnRoot f k hk i a := by
  let c : n → Group m R := fun j =>
    columnRoot f k hk j ((Pi.mulSingle i (Multiplicative.ofAdd a) : n → Multiplicative R) j).toAdd
  have hc : ((Finset.univ : Finset n) : Set n).Pairwise (fun a b => Commute (c a) (c b)) := by
    intro j _ l _ _
    exact columnRoot_commute f k hk j l _ _
  change Finset.univ.noncommProd c hc = _
  have he : (Finset.univ.erase i).noncommProd c
      (hc.mono (by intro j hj; exact Finset.mem_univ _)) = 1 := by
    apply (Finset.noncommProd_eq_pow_card _ _ _ 1 ?_).trans (one_pow _)
    intro j hj
    have hji := (Finset.mem_erase.mp hj).1
    simp only [c, Pi.mulSingle_eq_of_ne hji, toAdd_one, columnRoot, root_zero]
  exact (Finset.mul_noncommProd_erase Finset.univ (Finset.mem_univ i) c hc).symm.trans
    (by rw [he, mul_one]; simp [c])

omit [Fintype n] [DecidableEq n] in
lemma root_conjugate_columnRoot (f : n ↪ m) (k : m) (hk : ∀ i, f i ≠ k)
    (i j : n) (hij : i ≠ j) (a b : R) :
    root (f i) (f j) (f.injective.ne hij) a * columnRoot f k hk j b *
      (root (f i) (f j) (f.injective.ne hij) a)⁻¹ =
        columnRoot f k hk i (a*b) * columnRoot f k hk j b := by
  have h := root_commutator (f i) (f j) k (f.injective.ne hij) (hk j) (hk i) a b
  have := congrArg (fun z => z * root (f j) k (hk j) b) h
  simpa only [commutatorElement_def, mul_assoc, inv_mul_cancel, mul_one, columnRoot]
    using this

lemma matrixVector_root_single (i j : n) (hij : i ≠ j) (a : R) (t : n) (b : R) :
    matrixVector (NoncommElementary.root i j hij a).val
        (Pi.mulSingle t (Multiplicative.ofAdd b)) =
      Pi.mulSingle i (Multiplicative.ofAdd (if t=j then a*b else 0)) *
        Pi.mulSingle t (Multiplicative.ofAdd b) := by
  ext q
  change ((1 + Matrix.single i j a).mulVec (Pi.single t b)) q =
    ((Pi.single i (if t=j then a*b else 0) : n → R) + (Pi.single t b : n → R)) q
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec]
  simp [Function.update_apply, Pi.single_apply, eq_comm, add_comm]

lemma root_conjugate_column (f : n ↪ m) (k : m) (hk : ∀ i, f i ≠ k)
    (i j : n) (hij : i ≠ j) (a : R) (v : n → Multiplicative R) :
    root (f i) (f j) (f.injective.ne hij) a * column f k hk v *
      (root (f i) (f j) (f.injective.ne hij) a)⁻¹ =
        column f k hk (matrixVector (NoncommElementary.root i j hij a).val v) := by
  let x := root (f i) (f j) (f.injective.ne hij) a
  have he : (MulAut.conj x).toMonoidHom.comp (column f k hk) =
      (column f k hk).comp (matrixVector (NoncommElementary.root i j hij a).val) := by
    apply MonoidHom.pi_ext
    intro t b
    obtain ⟨b, rfl⟩ := Multiplicative.ofAdd.surjective b
    simp only [MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      MulAut.conj_apply, column_single, matrixVector_root_single, map_mul]
    by_cases ht : t = j
    · subst t
      simp only [ite_true]
      exact root_conjugate_columnRoot f k hk i j hij a b
    · simp only [ht, ite_false, columnRoot, root_zero, one_mul]
      change x * root (f t) k (hk t) b * x⁻¹ = _
      rw [(root_commute (f i) (f j) (f t) k (f.injective.ne hij) (hk t)
        (hk i) (f.injective.ne (Ne.symm ht)) a b).eq, mul_inv_cancel_right]
  exact DFunLike.congr_fun he v

lemma conjugate_column (f : n ↪ m) (k : m) (hk : ∀ i, f i ≠ k)
    (z : Group n R) (v : n → Multiplicative R) :
    reindex f z * column f k hk v * (reindex f z)⁻¹ =
      column f k hk (matrixVector (matrix z).val v) := by
  let H : Subgroup (Group n R) := {
    carrier := {z | ∀ v : n → Multiplicative R,
      reindex f z * column f k hk v * (reindex f z)⁻¹ =
        column f k hk (matrixVector (matrix z).val v)}
    one_mem' := by intro v; simp
    mul_mem' := by
      intro a b ha hb v
      simp only [map_mul, Units.val_mul]
      calc
        (reindex f a * reindex f b) * column f k hk v *
            (reindex f a * reindex f b)⁻¹ =
            reindex f a * (reindex f b * column f k hk v * (reindex f b)⁻¹) *
                (reindex f a)⁻¹ := by group
        _ = column f k hk (matrixVector (matrix a).val
              (matrixVector (matrix b).val v)) := by rw [hb, ha]
        _ = _ := by rw [matrixVector_mul]
    inv_mem' := by
      intro a ha v
      have h := ha (matrixVector (matrix a⁻¹).val v)
      have hv : matrixVector (matrix a).val (matrixVector (matrix a⁻¹).val v) = v := by
        rw [← matrixVector_mul, ← Units.val_mul, ← map_mul, mul_inv_cancel]
        simp
      rw [hv] at h
      simp only [map_inv] at h ⊢
      rw [← h]
      group }
  have hz : z ∈ H := by
    apply PresentedGroup.generated_by
    intro r v
    change reindex f (root r.i r.j r.different r.coefficient) * _ *
      (reindex f (root r.i r.j r.different r.coefficient))⁻¹ =
        column f k hk (matrixVector (matrix (root r.i r.j r.different r.coefficient)).val v)
    simpa only [reindex_root, matrix_root] using
      root_conjugate_column f k hk r.i r.j r.different r.coefficient v
  exact hz v

def rowRoot (f : n ↪ m) (k : m) (hk : ∀ i, f i ≠ k) (i : n) (a : R) :
    Group m R := root k (f i) (Ne.symm (hk i)) a

omit [Fintype n] [DecidableEq n] in
lemma rowRoot_commute (f : n ↪ m) (k : m) (hk : ∀ i, f i ≠ k)
    (i j : n) (a b : R) : Commute (rowRoot f k hk i a) (rowRoot f k hk j b) :=
  root_commute _ _ _ _ _ _ (Ne.symm (hk j)) (hk i) a b

def row (f : n ↪ m) (k : m) (hk : ∀ i, f i ≠ k) :
    (n → Multiplicative R) →* Group m R where
  toFun v := Finset.univ.noncommProd (fun i => rowRoot f k hk i (v i).toAdd)
    (by intro i _ j _ _; exact rowRoot_commute f k hk i j _ _)
  map_one' := by
    apply (Finset.noncommProd_eq_pow_card _ _ _ 1 ?_).trans (one_pow _)
    intro i _
    exact root_zero _ _ _
  map_mul' v w := by
    let c (u : n → Multiplicative R) := fun i => rowRoot f k hk i (u i).toAdd
    have he : c (v*w) = c v * c w := by
      ext i
      exact (root_add _ _ _ _ _).symm
    change Finset.univ.noncommProd (c (v*w)) _ = _
    simp only [he]
    exact Finset.noncommProd_mul_distrib _ _ _ _
      (by intro i _ j _ _; exact rowRoot_commute f k hk i j _ _)

lemma row_single (f : n ↪ m) (k : m) (hk : ∀ i, f i ≠ k) (i : n) (a : R) :
    row f k hk (Pi.mulSingle i (Multiplicative.ofAdd a)) = rowRoot f k hk i a := by
  let c : n → Group m R := fun j =>
    rowRoot f k hk j ((Pi.mulSingle i (Multiplicative.ofAdd a) : n → Multiplicative R) j).toAdd
  have hc : ((Finset.univ : Finset n) : Set n).Pairwise (fun a b => Commute (c a) (c b)) := by
    intro j _ l _ _
    exact rowRoot_commute f k hk j l _ _
  change Finset.univ.noncommProd c hc = _
  have he : (Finset.univ.erase i).noncommProd c
      (hc.mono (by intro j hj; exact Finset.mem_univ _)) = 1 := by
    apply (Finset.noncommProd_eq_pow_card _ _ _ 1 ?_).trans (one_pow _)
    intro j hj
    have hji := (Finset.mem_erase.mp hj).1
    simp only [c, Pi.mulSingle_eq_of_ne hji, toAdd_one, rowRoot, root_zero]
  exact (Finset.mul_noncommProd_erase Finset.univ (Finset.mem_univ i) c hc).symm.trans
    (by rw [he, mul_one]; simp [c])

omit [Fintype n] [DecidableEq n] in
lemma root_conjugate_rowRoot (f : n ↪ m) (k : m) (hk : ∀ i, f i ≠ k)
    (i j : n) (hij : i ≠ j) (a b : R) :
    root (f i) (f j) (f.injective.ne hij) a * rowRoot f k hk i b *
      (root (f i) (f j) (f.injective.ne hij) a)⁻¹ =
        rowRoot f k hk j (-(b*a)) * rowRoot f k hk i b := by
  have h := root_commutator_reverse k (f i) (f j) (Ne.symm (hk i))
    (f.injective.ne hij) (Ne.symm (hk j)) b a
  have := congrArg (fun z => z * root k (f i) (Ne.symm (hk i)) b) h
  simpa only [commutatorElement_def, mul_assoc, inv_mul_cancel, mul_one, rowRoot]
    using this

lemma vectorMatrix_root_single (i j : n) (hij : i ≠ j) (a : R) (t : n) (b : R) :
    vectorMatrix ((NoncommElementary.root i j hij a)⁻¹).val
        (Pi.mulSingle t (Multiplicative.ofAdd b)) =
      Pi.mulSingle j (Multiplicative.ofAdd (if t=i then -(b*a) else 0)) *
        Pi.mulSingle t (Multiplicative.ofAdd b) := by
  ext q
  change (Matrix.vecMul (Pi.single t b) (1 + Matrix.single i j (-a))) q =
    ((Pi.single j (if t=i then -(b*a) else 0) : n → R) + (Pi.single t b : n → R)) q
  rw [Matrix.vecMul_add, Matrix.vecMul_one]
  simp [Matrix.single, Pi.single_apply, eq_comm, add_comm]
  split_ifs <;> simp_all

lemma root_conjugate_row (f : n ↪ m) (k : m) (hk : ∀ i, f i ≠ k)
    (i j : n) (hij : i ≠ j) (a : R) (v : n → Multiplicative R) :
    root (f i) (f j) (f.injective.ne hij) a * row f k hk v *
      (root (f i) (f j) (f.injective.ne hij) a)⁻¹ =
        row f k hk (vectorMatrix ((NoncommElementary.root i j hij a)⁻¹).val v) := by
  let x := root (f i) (f j) (f.injective.ne hij) a
  have he : (MulAut.conj x).toMonoidHom.comp (row f k hk) =
      (row f k hk).comp (vectorMatrix ((NoncommElementary.root i j hij a)⁻¹).val) := by
    apply MonoidHom.pi_ext
    intro t b
    obtain ⟨b, rfl⟩ := Multiplicative.ofAdd.surjective b
    simp only [MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      MulAut.conj_apply, row_single, vectorMatrix_root_single, map_mul]
    by_cases ht : t = i
    · subst t
      simp only [ite_true]
      exact root_conjugate_rowRoot f k hk i j hij a b
    · simp only [ht, ite_false, rowRoot, root_zero, one_mul]
      change x * root k (f t) (Ne.symm (hk t)) b * x⁻¹ = _
      rw [(root_commute (f i) (f j) k (f t) (f.injective.ne hij) (Ne.symm (hk t))
        (f.injective.ne (Ne.symm ht)) (hk j) a b).eq, mul_inv_cancel_right]
  exact DFunLike.congr_fun he v

lemma conjugate_row (f : n ↪ m) (k : m) (hk : ∀ i, f i ≠ k)
    (z : Group n R) (v : n → Multiplicative R) :
    reindex f z * row f k hk v * (reindex f z)⁻¹ =
      row f k hk (vectorMatrix ((matrix z)⁻¹).val v) := by
  let H : Subgroup (Group n R) := {
    carrier := {z | ∀ v : n → Multiplicative R,
      reindex f z * row f k hk v * (reindex f z)⁻¹ =
        row f k hk (vectorMatrix ((matrix z)⁻¹).val v)}
    one_mem' := by intro v; simp
    mul_mem' := by
      intro a b ha hb v
      simp only [map_mul, mul_inv_rev, Units.val_mul]
      calc
        (reindex f a * reindex f b) * row f k hk v *
            ((reindex f b)⁻¹ * (reindex f a)⁻¹) =
            reindex f a * (reindex f b * row f k hk v * (reindex f b)⁻¹) *
                (reindex f a)⁻¹ := by group
        _ = row f k hk (vectorMatrix ((matrix a)⁻¹).val
              (vectorMatrix ((matrix b)⁻¹).val v)) := by rw [hb, ha]
        _ = _ := by rw [vectorMatrix_mul]
    inv_mem' := by
      intro a ha v
      have h := ha (vectorMatrix ((matrix a⁻¹)⁻¹).val v)
      have hv : vectorMatrix ((matrix a)⁻¹).val (vectorMatrix ((matrix a⁻¹)⁻¹).val v) = v := by
        rw [← vectorMatrix_mul, ← Units.val_mul]
        simp
      rw [hv] at h
      simp only [map_inv, inv_inv] at h ⊢
      rw [← h]
      group }
  have hz : z ∈ H := by
    apply PresentedGroup.generated_by
    intro r v
    change reindex f (root r.i r.j r.different r.coefficient) * _ *
      (reindex f (root r.i r.j r.different r.coefficient))⁻¹ =
        row f k hk (vectorMatrix ((matrix (root r.i r.j r.different r.coefficient))⁻¹).val v)
    simpa only [reindex_root, matrix_root] using
      root_conjugate_row f k hk r.i r.j r.different r.coefficient v
  exact hz v

variable [Fintype m] [DecidableEq m]

omit [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] in
lemma reindex_commute_disjoint (f : n ↪ m) (i j : m) (hij : i ≠ j)
    (hi : ∀ p, f p ≠ i) (hj : ∀ p, f p ≠ j) (z : Group n R) (a : R) :
    Commute (reindex f z) (root i j hij a) := by
  apply commute_of_roots (reindex f) (root i j hij a) _ z
  intro p q hpq b
  simp only [reindex_root]
  exact root_commute _ _ _ _ _ _ (hj p) (hi q) b a

end Steinberg

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_PrefixPermutation
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Pointwise
open scoped commutatorElement

namespace NoncommElementary
variable {R n : Type*} [Ring R] [Fintype n] [DecidableEq n]

lemma root_mulVec (i j : n) (h : i≠j) (a : R) (x : n → R) :
    Matrix.mulVec (root i j h a).val x = x+Pi.single i (a*x j) := by
  ext k
  simp [root_val,Matrix.add_mulVec,Matrix.single_mulVec,Pi.single]

def exchange (i j : n) (h : i≠j) (d : R) : (Matrix n n R)ˣ :=
  root i j h d * root j i h.symm (-d) * root i j h d

lemma exchange_mem (i j : n) (h : i≠j) (d : R) : exchange i j h d∈elementary :=
  (elementary (R:=R)).mul_mem
    ((elementary (R:=R)).mul_mem (root_mem _ _ _ _) (root_mem _ _ _ _))
    (root_mem _ _ _ _)

lemma exchange_fixes (i j : n) (h : i≠j) (d a : R) (ha : d*a=0) :
    Matrix.mulVec (exchange i j h d).val (Pi.single i a)=Pi.single i a := by
  simp only [exchange,Units.val_mul,← Matrix.mulVec_mulVec,root_mulVec]
  simp [Ne.symm h,ha]

end NoncommElementary

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_RingExchange
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Pointwise
open scoped commutatorElement

namespace Steinberg

section
variable {R n m : Type*} [Ring R]

lemma diagonalAction_mul (d e : n → Rˣ) :
    diagonalAction (d*e) = (diagonalAction d).comp (diagonalAction e) := by
  apply hom_ext
  intro i j hij a
  simp [mul_assoc]

variable [Fintype n] [DecidableEq n]

lemma conjugate_diagonal_column (f : n ↪ m) (z : Group n R) (d : n → Rˣ)
    (hz : matrix z=NoncommElementary.diagonal d) (k : m) (hk : ∀ i, f i ≠ k)
    (j : n) (a : R) :
    reindex f z * root (f j) k (hk j) a * (reindex f z)⁻¹ =
      root (f j) k (hk j) ((d j).val*a) := by
  have h := conjugate_column f k hk z (Pi.mulSingle j (Multiplicative.ofAdd a))
  have he : matrixVector (matrix z).val (Pi.mulSingle j (Multiplicative.ofAdd a)) =
      Pi.mulSingle j (Multiplicative.ofAdd ((d j).val*a)) := by
    funext i
    apply Multiplicative.toAdd.injective
    rw [matrixVector_single_apply,hz]
    change Matrix.diagonal (fun i => (d i).val) i j*a = _
    by_cases hi : i=j
    · subst i; simp
    · simp [hi]
  rw [he,column_single,column_single] at h
  exact h

lemma conjugate_diagonal_row (f : n ↪ m) (z : Group n R) (d : n → Rˣ)
    (hz : matrix z=NoncommElementary.diagonal d) (k : m) (hk : ∀ i, f i ≠ k)
    (j : n) (a : R) :
    reindex f z * root k (f j) (Ne.symm (hk j)) a * (reindex f z)⁻¹ =
      root k (f j) (Ne.symm (hk j)) (a*(d j).inv) := by
  have h := conjugate_row f k hk z (Pi.mulSingle j (Multiplicative.ofAdd a))
  have he : vectorMatrix ((matrix z)⁻¹).val (Pi.mulSingle j (Multiplicative.ofAdd a)) =
      Pi.mulSingle j (Multiplicative.ofAdd (a*(d j).inv)) := by
    funext i
    apply Multiplicative.toAdd.injective
    rw [vectorMatrix_single_apply,hz,← map_inv]
    change a*Matrix.diagonal (fun i => (d i).inv) j i = _
    by_cases hi : i=j
    · subst i; simp
    · simp [hi,Ne.symm hi]
  rw [he,row_single,row_single] at h
  exact h

lemma conjugate_block_diagonal (f : n ↪ m) (z : Group n R) (d : m → Rˣ)
    (hz : matrix z=NoncommElementary.diagonal (fun i => d (f i)))
    (k : m) (hk : ∀ i, f i≠k) (hd : ∀ j, (∀ i, f i≠j) → d j=1) :
    (MulAut.conj (reindex f z)).toMonoidHom = diagonalAction d := by
  apply hom_ext
  intro i j hij a
  simp only [MulEquiv.toMonoidHom_eq_coe,MonoidHom.coe_coe,MulAut.conj_apply,
    diagonalAction_root]
  by_cases hi : ∃ p, f p=i
  · obtain ⟨p,rfl⟩ := hi
    by_cases hj : ∃ q, f q=j
    · obtain ⟨q,rfl⟩ := hj
      have he : root (f p) (f q) hij a =
          ⁅root (f p) k (hk p) a,root k (f q) (Ne.symm (hk q)) 1⁆ := by
        rw [root_commutator _ _ _ (hk p) (Ne.symm (hk q)) hij,mul_one]
      rw [he]
      have hconj := map_commutatorElement (MulAut.conj (reindex f z)).toMonoidHom
        (root (f p) k (hk p) a) (root k (f q) (Ne.symm (hk q)) 1)
      change reindex f z * _ * (reindex f z)⁻¹ = _ at hconj
      rw [hconj]
      change ⁅reindex f z * root (f p) k (hk p) a * (reindex f z)⁻¹,
        reindex f z * root k (f q) (Ne.symm (hk q)) 1 * (reindex f z)⁻¹⁆ = _
      rw [conjugate_diagonal_column f z _ hz k hk p a,
        conjugate_diagonal_row f z _ hz k hk q 1,
        root_commutator (f p) k (f q) (hk p) (Ne.symm (hk q)) hij,one_mul]
    · have hj' : ∀ q, f q≠j := by simpa only [not_exists] using hj
      simpa [hd j hj'] using conjugate_diagonal_column f z _ hz j hj' p a
  · have hi' : ∀ p, f p≠i := by simpa only [not_exists] using hi
    by_cases hj : ∃ q, f q=j
    · obtain ⟨q,rfl⟩ := hj
      rw [hd i hi',Units.val_one,one_mul]
      exact conjugate_diagonal_row f z _ hz i hi' q a
    · have hj' : ∀ q, f q≠j := by simpa only [not_exists] using hj
      simp [(reindex_commute_disjoint f i j hij hi' hj' z a).mul_inv_cancel,
        hd i hi',hd j hj']

end

section
variable {R : Type*} [Ring R]

def transportWord (d s : R) : Group (Fin 2) R :=
  (root 0 1 (by decide) 1 * root 1 0 (by decide) (-1) * root 0 1 (by decide) 1)⁻¹ *
    (root 0 1 (by decide) d * root 1 0 (by decide) (-s) * root 0 1 (by decide) d)

lemma matrix_transportWord (d s : R) (hdsd : d*s*d=d) :
    (matrix (transportWord d s)).val = !![s, s*d-1; 1-d*s, d] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [transportWord, map_mul, map_inv, matrix_root, mul_inv_rev,
      NoncommElementary.root_inv, NoncommElementary.root_val, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.single, Matrix.one_apply] <;>
    noncomm_ring [hdsd]

end

variable {R m : Type*} [Ring R]

lemma constantPair_inner (u : Rˣ) (hu : u.inv=u.val) (f : Fin 2 ↪ m)
    (d : m → Rˣ) (hd : ∀ i, d (f i)=u) (t : m) (ht : ∀ i, f i≠t)
    (hout : ∀ j, (∀ i, f i≠j) → d j=1) :
    ∃ z : Group m R, (MulAut.conj z).toMonoidHom=diagonalAction d := by
  let z := transportWord u.inv u.val
  refine ⟨reindex f z,conjugate_block_diagonal f z d ?_ t ht hout⟩
  apply Units.ext
  change (matrix (transportWord u.inv u.val)).val = _
  rw [matrix_transportWord u.inv u.val (by simp)]
  have hu' : (u⁻¹).val=u.val := hu
  have hu2 : u.val*u.val=1 := (congrArg (fun x => u.val*x) hu).symm.trans u.val_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [NoncommElementary.diagonal,hd,hu',hu2]

lemma innerWeights_mul (d e : m → Rˣ)
    (hd : ∃ z : Group m R, (MulAut.conj z).toMonoidHom=diagonalAction d)
    (he : ∃ z : Group m R, (MulAut.conj z).toMonoidHom=diagonalAction e) :
    ∃ z : Group m R, (MulAut.conj z).toMonoidHom=diagonalAction (d*e) := by
  obtain ⟨x,hx⟩ := hd
  obtain ⟨y,hy⟩ := he
  refine ⟨x*y,?_⟩
  rw [diagonalAction_mul,← hx,← hy]
  ext v
  simp [MulAut.conj_apply,mul_assoc]

end Steinberg

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_SteinbergSixThree
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Pointwise
open scoped commutatorElement

namespace NoncommElementary
section
variable {R n : Type*} [Ring R] [Fintype n] [DecidableEq n]

lemma position_normalizes (i : n) (u : Rˣ) :
    position i u∈Subgroup.normalizer (elementary (R:=R) (n:=n) : Set (Matrix n n R)ˣ) :=
  diagonal_normalizes _

def diagonalKernel (i : n) : Subgroup Rˣ := elementary.comap (position i)

instance diagonalKernel_normal (i : n) : (diagonalKernel (R:=R) i).Normal where
  conj_mem u hu v := by
    change position i (v*u*v⁻¹)∈elementary
    simp only [map_mul,map_inv]
    exact (Subgroup.mem_normalizer_iff.mp (position_normalizes i v) (position i u)).mp hu

end

end NoncommElementary

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_StageConstruction
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Pointwise
open scoped commutatorElement

namespace NonunitalCompression
variable {R S : Type*} [Ring R] [Ring S]
lemma unitValue_mul_image (φ : R →ₙ+* S) (u x : R) :
    unitValue φ u*φ x=φ (u*x) := by
  have hp : φ 1*φ x=φ x := by rw [← map_mul,one_mul]
  simp only [unitValue,map_sub,map_mul]
  noncomm_ring [hp]
end NonunitalCompression

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_TwistedBrin
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
universe u v
namespace TwistedBrin

variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)
namespace GermBrick

def Restricts (c b : GermBrick ρ) : Prop :=
  ∃ (h : LocalEmbedding ρ) (p : Prefix S), b = mk ρ h ∧
    c = mk ρ (LocalEmbedding.comp ρ h (LocalEmbedding.ofPrefix ρ p))

end GermBrick

end TwistedBrin

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_FirstFamilies
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SimpleFInftyOvergroups.ContextualEncoding
open FiniteAlgebraicEnvelopes Bootstrap BoundedEncoding
noncomputable section
open scoped Classical

namespace GroupFamily
variable {G : Type*} [Group G] {k : ℕ} (s : Fin k → G)

def test (w : List (Fin k × Bool)) : Part (Option (List (Fin k × Bool))) :=
  Part.some (some (WordProblem.testedClass s w))

theorem context {u v : List (Fin k × Bool)} (h : WordProblem.testedClass s u = WordProblem.testedClass s v)
    (a b : List (Fin k × Bool)) :
    WordProblem.testedClass s (a++u++b) = WordProblem.testedClass s (a++v++b) := by
  apply (WordProblem.testedClass_eq_iff s _ _).mpr
  simp only [WordProblem.evalWord_append]
  rw [(WordProblem.testedClass_eq_iff s _ _).mp h]
end GroupFamily

namespace ProductFamily
variable {A : Type*}

variable [DecidableEq A]

def test (zero : List A) (f : List A → Part (List A)) (w : List (Letter A)) :
    Part (Option (Key A)) :=
  (f (Projection.left w)).map (fun u => combine zero (u,PartialAffine.testedClass (Projection.right w)))

variable {m : ℕ} (C : WordCalculus (FreeMonoid A) m)

def normal (w : List (Letter A)) : List A :=
  (C.normal (FreeMonoid.ofList (Projection.left w))).toList

def value (w : List (Letter A)) : Option (Key A) :=
  combine C.omega.toList (normal C w,PartialAffine.testedClass (Projection.right w))

def grade (w : List (Letter A)) : ℕ := C.grade (FreeMonoid.ofList (Projection.left w))

omit [DecidableEq A] in
@[simp] theorem grade_nil : grade C [] = 0 := C.grade_one
omit [DecidableEq A] in
@[simp] theorem grade_append (u v : List (Letter A)) : grade C (u++v) = grade C u + grade C v := by
  simp only [grade, Projection.left_append, FreeMonoid.ofList_append, C.grade_mul]

omit [DecidableEq A] in
theorem grade_cost (g : A → ℕ) (hg : ∀ u, C.grade (FreeMonoid.ofList u) = (u.map g).sum)
    (w : List (Letter A)) : grade C w = wordCost g w := by
  rw [grade, hg, wordCost_projection]

omit [DecidableEq A] in
theorem normal_context {u v : List (Letter A)} (h : normal C u = normal C v)
    (a b : List (Letter A)) (hu : grade C (a++u++b) ≤ m) (hv : grade C (a++v++b) ≤ m) :
    normal C (a++u++b) = normal C (a++v++b) := by
  apply congrArg FreeMonoid.toList
  simp only [grade, Projection.left_append, FreeMonoid.ofList_append] at hu hv ⊢
  exact C.context (FreeMonoid.toList.injective h) _ _ hu hv

omit [DecidableEq A] in
theorem normal_zero_context {u : List (Letter A)} (h : normal C u = C.omega.toList)
    (a b : List (Letter A)) (hu : grade C (a++u++b) ≤ m) :
    normal C (a++u++b) = C.omega.toList := by
  apply congrArg FreeMonoid.toList
  have he : C.normal (FreeMonoid.ofList (Projection.left u)) = C.normal C.omega := by
    rw [C.normal_omega]
    exact FreeMonoid.toList.injective h
  have hb : C.grade (FreeMonoid.ofList (Projection.left a) * C.omega * FreeMonoid.ofList (Projection.left b)) ≤ m := by
    simp only [grade, Projection.left_append, FreeMonoid.ofList_append, C.grade_mul] at hu
    simp only [C.grade_mul, C.grade_omega]
    omega
  simp only [grade, Projection.left_append, FreeMonoid.ofList_append] at hu ⊢
  exact (C.context he _ _ hu hb).trans (C.absorbs _ _)

theorem value_context {u v : List (Letter A)} (h : value C u = value C v)
    (a b : List (Letter A)) (hu : grade C (a++u++b) ≤ m) (hv : grade C (a++v++b) ≤ m) :
    value C (a++u++b) = value C (a++v++b) := by
  by_cases hz : normal C u = C.omega.toList
  · have hvz : normal C v = C.omega.toList := by
      by_contra hvz
      simp [value, combine, hz, hvz] at h
    simp only [value, combine, normal_zero_context C hz a b hu,
      normal_zero_context C hvz a b hv, ite_true]
  · have hvz : normal C v ≠ C.omega.toList := by
      intro hvz
      simp [value, combine, hz, hvz] at h
    have he : normal C u = normal C v ∧
        PartialAffine.testedClass (Projection.right u) = PartialAffine.testedClass (Projection.right v) := by
      simpa only [value,combine,ite_eq_right hz,ite_eq_right hvz,Option.some.injEq,Prod.mk.injEq] using h
    have hcontext : PartialAffine.testedClass (Projection.right (a++u++b)) =
        PartialAffine.testedClass (Projection.right (a++v++b)) := by
      apply (PartialAffine.testedClass_eq_iff _ _).mpr
      have hmaps := (PartialAffine.testedClass_eq_iff _ _).mp he.2
      simp only [PartialAffine.value] at hmaps
      simp only [Projection.right_append, PartialAffine.value, List.map_append, List.prod_append]
      rw [hmaps]
    simp only [value, normal_context C he.1 a b hu hv, hcontext]

theorem value_zero_context {u : List (Letter A)} (h : value C u = none)
    (a b : List (Letter A)) (hu : grade C (a++u++b) ≤ m) : value C (a++u++b) = none := by
  have hz : normal C u = C.omega.toList := by simpa [value,combine] using h
  simp only [value,combine,normal_zero_context C hz a b hu,ite_true]

@[simp] theorem value_nil : value C [] ≠ none := by
  have hn : normal C [] ≠ C.omega.toList := by
    intro h
    have he := FreeMonoid.toList.injective h
    exact C.omega_ne_one (by simpa only [Projection.left, List.filterMap_nil, FreeMonoid.ofList_nil, C.normal_one] using he.symm)
  simp only [value,combine,ite_eq_right hn,ne_eq,Option.some_ne_none,not_false_eq_true]

theorem test_full {f : List A → Part (List A)} {d : ℕ} (w : List (Letter A))
    (hw : grade C w ≤ d)
    (hf : ∀ u, C.grade (FreeMonoid.ofList u) ≤ d → (C.normal (FreeMonoid.ofList u)).toList ∈ f u) :
    value C w ∈ test C.omega.toList f w :=
  (Part.mem_map_iff _).mpr ⟨_,hf _ hw,rfl⟩

variable [Primcodable A]
theorem primrec_combine (zero : List A) : Primrec (combine zero) :=
  Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const _)) (Primrec.const none)
    (Primrec.option_some.comp Primrec.id)

omit [DecidableEq A] in
theorem primrec_cost {c : A → ℕ} (hc : Primrec c) : Primrec (cost c) :=
  Effect.primrec_sumElim hc (Primrec.const 0)

end ProductFamily
end
end SimpleFInftyOvergroups.ContextualEncoding

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_ContextualTables
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SimpleFInftyOvergroups.ContextualEncoding
open FiniteAlgebraicEnvelopes.Bootstrap Relation

namespace CodeTable
variable {A S Q : Type*} {r : S → S → Prop} [Std.Trichotomous r]
variable (C : DelimiterCode A S) (E : FiniteSearch C) (wf : WellFounded r)
  (q : List A → Option Q) (z : S)

theorem branch_normalizes {n : ℕ} {rs : List (List S × List S)}
    (hzero : q [] ≠ none) (hz : Absorbs rs z)
    (ht : ∀ p ∈ table C E wf q z n, p ∈ rs)
    (hc : Contextual C q n) (hi : ZeroIdeal C q n)
    {v : List A} {a b : List A} (hlen : (C.encode (a++v++b)).length ≤ n) :
    Steps rs (C.encode a++output C wf q z v++C.encode b) (output C wf q z (a++v++b)) := by
  by_cases hq : q v = none
  · have hzq := hi a b v hlen hq
    simp only [output, ite_eq_left hq, ite_eq_left hzq]
    exact absorbs_context hz _ _
  · let v' := EncodedCanonical.least C wf q v
    have hlen' : (C.encode (a++v'++b)).length ≤ n := by
      have hh := EncodedCanonical.least_length C wf q v
      simp only [DelimiterCode.encode_append, List.length_append] at hlen ⊢
      dsimp only [v']
      omega
    have hqq : q (a++v'++b) = q (a++v++b) :=
      hc a b v' v hlen' hlen (EncodedCanonical.least_class C wf q v)
    have hh := steps_mono ht (whole_steps C E wf q z hzero hlen')
    rw [output_congr C wf q z hqq] at hh
    simpa only [output, ite_eq_right hq, DelimiterCode.encode_append, v'] using hh

theorem occurrence_normalizes {n : ℕ} {rs : List (List S × List S)}
    (hzero : q [] ≠ none) (hz : Absorbs rs z)
    (ht : ∀ p ∈ table C E wf q z n, p ∈ rs)
    (hc : Contextual C q n) (hi : ZeroIdeal C q n)
    {w v : List A} {x y : List S} (hw : (C.encode w).length ≤ n) (hv : v ≠ [])
    (he : C.encode w = x++C.encode v++y) :
    Steps rs (x++output C wf q z v++y) (output C wf q z w) := by
  obtain ⟨a,b,rfl,rfl,rfl⟩ := C.occurrence_decode hv he
  exact branch_normalizes C E wf q z hzero hz ht hc hi hw

theorem critical_containment {n k l : ℕ} {rs : List (List S × List S)}
    (hzero : q [] ≠ none) (hz : Absorbs rs z)
    (ht : ∀ p ∈ table C E wf q z n, p ∈ rs)
    (hc : Contextual C q n) (hi : ZeroIdeal C q n)
    {u u' v v' x y : List S}
    (hu : (u,u') ∈ table C E wf q z k) (hv : (v,v') ∈ table C E wf q z l)
    (he : u = x++v++y) (hlen : u.length ≤ n) :
    Join (Steps rs) u' (x++v'++y) := by
  obtain ⟨a,_,_,_,rfl,rfl⟩ := (mem_table C E wf q z).mp hu
  obtain ⟨b,_,hbn,_,rfl,rfl⟩ := (mem_table C E wf q z).mp hv
  exact ⟨output C wf q z a, .refl,
    occurrence_normalizes C E wf q z hzero hz ht hc hi hlen hbn he⟩

theorem critical_overlap {n k l : ℕ} {rs : List (List S × List S)}
    (hzero : q [] ≠ none) (hz : Absorbs rs z)
    (ht : ∀ p ∈ table C E wf q z n, p ∈ rs)
    (hc : Contextual C q n) (hi : ZeroIdeal C q n)
    {u u' v v' x middle y : List S}
    (hu : (u,u') ∈ table C E wf q z k) (hv : (v,v') ∈ table C E wf q z l)
    (hm : middle ≠ []) (he : u = x++middle) (hf : v = middle++y)
    (hlen : (x++middle++y).length ≤ n) :
    Join (Steps rs) (u'++y) (x++v') := by
  obtain ⟨a,_,_,_,rfl,rfl⟩ := (mem_table C E wf q z).mp hu
  obtain ⟨b,_,_,_,rfl,rfl⟩ := (mem_table C E wf q z).mp hv
  obtain ⟨c,d,e,rfl,rfl,rfl,rfl,rfl⟩ := C.overlap_decode hm he hf
  have hlen' : (C.encode (c++d++e)).length ≤ n := by
    simpa only [DelimiterCode.encode_append] using hlen
  refine ⟨output C wf q z (c++d++e), ?_, ?_⟩
  · simpa only [List.nil_append, DelimiterCode.encode_nil] using
      branch_normalizes C E wf q z hzero hz ht hc hi (a := []) (v := c++d) (b := e)
        (by simpa only [List.nil_append] using hlen')
  · simpa only [List.append_nil, DelimiterCode.encode_nil, List.append_assoc] using
      branch_normalizes C E wf q z hzero hz ht hc hi (a := c) (v := d++e) (b := [])
        (by simpa only [List.append_nil, List.append_assoc] using hlen')

end CodeTable
end SimpleFInftyOvergroups.ContextualEncoding

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_FamilyTables
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SimpleFInftyOvergroups.ContextualEncoding
open FiniteAlgebraicEnvelopes.Bootstrap Relation

namespace Families
variable {I S : Type*} {A Q : I → Type*} [Fintype I] [Fintype S]
variable {r : S → S → Prop} [Std.Trichotomous r]
variable (C : ∀ i, DelimiterCode (A i) S) (E : ∀ i, FiniteSearch (C i))
  (wf : WellFounded r) (q : ∀ i, List (A i) → Option (Q i)) (z : S)

omit [Std.Trichotomous r] in
theorem mem_table [Std.Trichotomous r] {n : ℕ} {p : List S × List S} : p ∈ table C E wf q z n ↔
    p ∈ Base.absorption z ∨ ∃ i, p ∈ CodeTable.table (C i) (E i) wf (q i) z n := by
  classical
  simp [table, Static.letters]

theorem absorbs (n : ℕ) : Absorbs (table C E wf q z n) z := by
  classical
  intro a
  constructor <;> apply (mem_table C E wf q z).mpr <;> apply Or.inl <;>
    apply (Base.mem_absorption z).mpr
  · exact ⟨a, Or.inl rfl, rfl⟩
  · exact ⟨a, Or.inr rfl, rfl⟩

theorem preserves_zero (hz : ∀ i, z ∉ (C i).alphabet) (n : ℕ) :
    ∀ p ∈ table C E wf q z n, z ∈ p.1 → z ∈ p.2 := by
  classical
  intro ⟨u,v⟩ hp hu
  rcases (mem_table C E wf q z).mp hp with hp | ⟨i,hp⟩
  · obtain ⟨a,_,rfl⟩ := (Base.mem_absorption z).mp hp
    simp
  · obtain ⟨w,_,_,_,rfl,_⟩ := (CodeTable.mem_table (C i) (E i) wf (q i) z).mp hp
    exact ((hz i) ((C i).mem_alphabet_of_mem_encode hu)).elim

theorem critical (hz : ∀ i, z ∉ (C i).alphabet)
    (hd : ∀ i j, i ≠ j → Disjoint (C i).alphabet (C j).alphabet) {n : ℕ}
    (hzero : ∀ i, q i [] ≠ none)
    (hc : ∀ i, CodeTable.Contextual (C i) (q i) n)
    (hi : ∀ i, CodeTable.ZeroIdeal (C i) (q i) n) : Critical (table C E wf q z n) n := by
  classical
  let rs := table C E wf q z n
  have hza : Absorbs rs z := absorbs C E wf q z n
  have hp := preserves_zero C E wf q z hz n
  have ht (i) : ∀ p ∈ CodeTable.table (C i) (E i) wf (q i) z n, p ∈ rs :=
    fun _ h => (mem_table C E wf q z).mpr (.inr ⟨i,h⟩)
  have hzeroPeak {w u v : List S} (hw : z ∈ w) (hu : Step rs w u) (hv : Step rs w v) :
      Join (Steps rs) u v :=
    ⟨[z], absorbs_mem hza (step_preserves_letter hp hw hu),
      absorbs_mem hza (step_preserves_letter hp hw hv)⟩
  have hnabs {u v : List S} (h : z ∉ u) : (u,v) ∉ Base.absorption z := by
    intro hh
    obtain ⟨a,ha,_⟩ := (Base.mem_absorption z).mp hh
    rcases ha with rfl | rfl <;> simp at h
  constructor
  · intro u u' v v' hu hv x y he hlen
    by_cases huz : z ∈ u
    · apply hzeroPeak huz
      · simpa using Step.apply hu [] []
      · simpa only [he] using Step.apply hv x y
    have hvz : z ∉ v := fun hh => huz (by simp [he,hh])
    have hut := (mem_table C E wf q z).mp hu
    have hvt := (mem_table C E wf q z).mp hv
    simp only [hnabs huz, hnabs hvz, false_or] at hut hvt
    obtain ⟨i,hui⟩ := hut
    obtain ⟨j,hvj⟩ := hvt
    by_cases hij : i = j
    · subst j
      exact CodeTable.critical_containment (C i) (E i) wf (q i) z
        (hzero i) hza (ht i) (hc i) (hi i) hui hvj he hlen
    · obtain ⟨a,_,_,_,rfl,_⟩ := (CodeTable.mem_table (C i) (E i) wf (q i) z).mp hui
      obtain ⟨b,_,hb,_,rfl,_⟩ := (CodeTable.mem_table (C j) (E j) wf (q j) z).mp hvj
      exact ((C i).disjoint_infix (C j) (hd i j hij) hb ⟨x,y,he.symm⟩).elim
  · intro u u' v v' hu hv p m t hm he hh hlen
    by_cases hwz : z ∈ p++m++t
    · apply hzeroPeak hwz
      · simpa only [he, List.nil_append, List.append_assoc] using Step.apply hu [] t
      · simpa only [hh, List.append_nil, List.append_assoc] using Step.apply hv p []
    have huz : z ∉ u := fun h => hwz (by simp [←he,h])
    have hvz : z ∉ v := fun h => hwz (by simpa only [List.append_assoc,←hh,List.mem_append] using Or.inr h)
    have hut := (mem_table C E wf q z).mp hu
    have hvt := (mem_table C E wf q z).mp hv
    simp only [hnabs huz, hnabs hvz, false_or] at hut hvt
    obtain ⟨i,hui⟩ := hut
    obtain ⟨j,hvj⟩ := hvt
    by_cases hij : i = j
    · subst j
      exact CodeTable.critical_overlap (C i) (E i) wf (q i) z
        (hzero i) hza (ht i) (hc i) (hi i) hui hvj hm he hh hlen
    · obtain ⟨a,_,_,_,rfl,_⟩ := (CodeTable.mem_table (C i) (E i) wf (q i) z).mp hui
      obtain ⟨b,_,_,_,rfl,_⟩ := (CodeTable.mem_table (C j) (E j) wf (q j) z).mp hvj
      exact ((C i).disjoint_overlap (C j) (hd i j hij) hm he hh).elim

theorem decreasing (n : ℕ) : ∀ p ∈ table C E wf q z n, List.Shortlex r p.2 p.1 := by
  classical
  intro ⟨u,v⟩ hp
  rcases (mem_table C E wf q z).mp hp with hp | ⟨i,hp⟩
  · obtain ⟨a,ha,rfl⟩ := (Base.mem_absorption z).mp hp
    rcases ha with rfl | rfl <;> exact List.Shortlex.of_length_lt (by simp)
  · exact CodeTable.decreasing (C i) (E i) wf (q i) z n (u,v) hp

theorem stable {k n : ℕ} (hkn : k ≤ n) :
    Selectors.BoundedEq (table C E wf q z k) (table C E wf q z n) k := by
  intro p hp
  simp only [mem_table]
  exact or_congr Iff.rfl (exists_congr (fun i => CodeTable.stable (C i) (E i) wf (q i) z hkn p hp))

end Families
end SimpleFInftyOvergroups.ContextualEncoding

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_BoundedFamilyTests
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SimpleFInftyOvergroups.ContextualEncoding
open FiniteAlgebraicEnvelopes Bootstrap BoundedEncoding
noncomputable section
open scoped Classical

namespace TestCertificate
variable {A S Q : Type*} [DecidableEq A] [DecidableEq Q]
  (C : DelimiterCode A S) (f : List A → Part (Option Q)) {n : ℕ}

omit [DecidableEq A] [DecidableEq Q] in
theorem of_value (q : List A → Option Q)
    (hf : ∀ w, (C.encode w).length ≤ n → q w ∈ f w)
    (h0 : q [] ≠ none) (hc : CodeTable.Contextual C q n) (hz : CodeTable.ZeroIdeal C q n) :
    TestCertificate C f n := by
  have he (w : List A) (hw : (C.encode w).length ≤ n) : Search.value f w = q w :=
    Part.mem_unique (Search.value_mem (hf w hw).1) (hf w hw)
  refine ⟨fun w hw => (hf w hw).1, ?_, ?_, ?_⟩
  · rw [he [] (Nat.zero_le _)]
    exact h0
  · intro a b u v hu hv h
    have hlu : (C.encode u).length ≤ n := by
      simp only [DelimiterCode.encode_append,List.length_append] at hu
      omega
    have hlv : (C.encode v).length ≤ n := by
      simp only [DelimiterCode.encode_append,List.length_append] at hv
      omega
    rw [he u hlu,he v hlv] at h
    rw [he _ hu,he _ hv]
    exact hc a b u v hu hv h
  · intro a b u hu h
    have hlu : (C.encode u).length ≤ n := by
      simp only [DelimiterCode.encode_append,List.length_append] at hu
      omega
    rw [he u hlu] at h
    rw [he _ hu]
    exact hz a b u hu h
end TestCertificate

namespace GroupFamily
variable {G : Type*} [Group G] {k : ℕ} (s : Fin k → G)
theorem certificate (C : DelimiterCode (Fin k × Bool) ThreeCodes.Alphabet) (n : ℕ) :
    TestCertificate C (test s) n := by
  apply TestCertificate.of_value C (test s) (fun w => some (WordProblem.testedClass s w))
  · intro w hw; exact Part.mem_some _
  · exact Option.some_ne_none _
  · intro a b u v hu hv h
    exact congrArg some (context s (Option.some.inj h) a b)
  · intro a b u hu h
    cases h
end GroupFamily

namespace ProductFamily
variable {A : Type*} [DecidableEq A] {m n : ℕ} (C : WordCalculus (FreeMonoid A) m)
  (code : DelimiterCode (Letter A) ThreeCodes.Alphabet)
  (cost : A → ℕ) (hc : ∀ w, grade C w = wordCost cost w)
  (hp : ∀ a, 10 * ProductFamily.cost cost a + 2 ≤ (code.block a).length)
  (hm : n / 10 ≤ m) {f : List A → Part (List A)}
  (hf : ∀ u, C.grade (FreeMonoid.ofList u) ≤ n / 10 →
    (C.normal (FreeMonoid.ofList u)).toList ∈ f u)

include hc hp hm hf
theorem certificate : TestCertificate code (test C.omega.toList f) n := by
  have hb (w : List (Letter A)) (hw : (code.encode w).length ≤ n) : grade C w ≤ n / 10 := by
    rw [hc]
    exact code.cost_le_quota _ hp hw
  apply TestCertificate.of_value code (test C.omega.toList f) (value C)
  · intro w hw
    exact test_full C w (hb w hw) hf
  · exact value_nil C
  · intro a b u v hu hv h
    exact value_context C h a b ((hb _ hu).trans hm) ((hb _ hv).trans hm)
  · intro a b u hu h
    exact value_zero_context C h a b ((hb _ hu).trans hm)
end ProductFamily

namespace ActionFamily
open NamedAction
variable {G X V Y K L : Type*} [Group V] [MulAction V Y]
  [DecidableEq G] [DecidableEq X] [DecidableEq K] [DecidableEq L]
  {N : Operations G X} {m n : ℕ} {C : ActionCalculus V Y K L m}
  (I : Interpretation N C) (code : DelimiterCode (Letter G X) ThreeCodes.Alphabet)
  (hp : ∀ a, 10 * N.letterCost a + 2 ≤ (code.block a).length) (hm : 3 * (n / 10) ≤ m)
  (f : List (Letter G X) → Part (Result K L))
  (hf : ∀ w, N.wordCost w ≤ n / 10 → N.totalTest I.gkey I.xkey w ∈ f w)

include I hp hm hf
omit [DecidableEq G] [DecidableEq X] [DecidableEq K] in
theorem certificate : TestCertificate code f n := by
  have hb (w : List (Letter G X)) (hw : (code.encode w).length ≤ n) : N.wordCost w ≤ n / 10 :=
    code.cost_le_quota _ hp hw
  apply TestCertificate.of_value code f (N.totalTest I.gkey I.xkey)
  · intro w hw
    exact hf w (hb w hw)
  · exact I.totalTest_nil
  · intro a b u v hu hv h
    exact I.totalTest_context h (hb _ hu) (hb _ hv) hm
  · intro a b u hu h
    exact I.totalTest_zero_context h (hb _ hu) hm
end ActionFamily
end
end SimpleFInftyOvergroups.ContextualEncoding

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_CodeEmbedding
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SimpleFInftyOvergroups.ContextualEncoding
open FiniteAlgebraicEnvelopes.Bootstrap Relation

namespace Families
variable {I S : Type*} {A Q : I → Type*} [Fintype I] [Fintype S]
variable {r : S → S → Prop} [Std.Trichotomous r]
variable (C : ∀ i, DelimiterCode (A i) S) (E : ∀ i, FiniteSearch (C i))
  (wf : WellFounded r) (q : ∀ i, List (A i) → Option (Q i)) (z : S)

 theorem table_short {n : ℕ} {p : List S × List S} (hp : p ∈ table C E wf q z n) :
    1 < p.1.length := by
  classical
  rcases (mem_table C E wf q z).mp hp with hp | ⟨i,hp⟩
  · obtain ⟨a,ha,_⟩ := (Base.mem_absorption z).mp hp
    rcases ha with he | he <;> simp [he]
  · exact CodeTable.table_short (C i) (E i) wf (q i) z hp

 theorem isolate (i : I) (hz : z ∉ (C i).alphabet)
    (hd : ∀ j, i ≠ j → Disjoint (C i).alphabet (C j).alphabet)
    {n : ℕ} {p : List S × List S} (hp : p ∈ table C E wf q z n) :
    p ∈ CodeTable.table (C i) (E i) wf (q i) z n ∨ ∃ s ∈ p.1, s ∉ (C i).alphabet := by
  classical
  rcases (mem_table C E wf q z).mp hp with hp | ⟨j,hp⟩
  · obtain ⟨a,ha,_⟩ := (Base.mem_absorption z).mp hp
    exact Or.inr ⟨z,by rcases ha with he | he <;> simp [he],hz⟩
  · by_cases he : i = j
    · subst j; exact Or.inl hp
    · obtain ⟨w,_,hn,_,hl,_⟩ := (CodeTable.mem_table (C j) (E j) wf (q j) z).mp hp
      have hw : (C j).encode w ≠ [] := mt ((C j).encode_eq_nil _).mp hn
      obtain ⟨s,hs⟩ := List.exists_mem_of_ne_nil _ hw
      exact Or.inr ⟨s,hl ▸ hs,fun h => Set.disjoint_left.mp (hd j he) h
        ((C j).mem_alphabet_of_mem_encode hs)⟩
end Families

namespace CodeQuotient
open FiniteAlgebraicEnvelopes.Bootstrap.Quotient
variable {S : Type*} [DecidableEq S]
variable (T : ℕ → Part (List (List S × List S)))
variable {t : S → S → Prop} (wt : WellFounded t)
  (good : ∀ n, GoodTable (r:=t) T n)
  (stable : ∀ k n, k ≤ n → ∀ rk ∈ T k, ∀ rn ∈ T n, Selectors.BoundedEq rk rn k)
variable {A Q : Type*} {r : S → S → Prop} [Std.Trichotomous r]
variable (C : DelimiterCode A S) (E : FiniteSearch C) (wf : WellFounded r)
  (q : List A → Option Q) (z : S)
variable (hshort : ∀ n rs, rs ∈ T n → ∀ p ∈ rs, 1 < p.1.length)
variable (hiso : ∀ n rs, rs ∈ T n → ∀ p ∈ rs,
  p ∈ CodeTable.table C E wf q z n ∨ ∃ s ∈ p.1, s ∉ C.alphabet)
variable (hstatic : ∀ n rs, rs ∈ T n → ∀ p ∈ CodeTable.table C E wf q z n, p ∈ rs)
variable (hc : ∀ n, CodeTable.Contextual C q n) (hi : ∀ n, CodeTable.ZeroIdeal C q n)
  (hzero : q [] ≠ none)
include wt good stable hshort hiso hstatic hc hi hzero

 theorem normal_encode (w : List A) : normal T (C.encode w) = CodeTable.output C wf q z w := by
  have hfixed : normal T (CodeTable.output C wf q z w) = CodeTable.output C wf q z w := by
    by_cases hq : q w = none
    · rw [CodeTable.output,ite_eq_left hq]
      obtain ⟨rs,hrs,_⟩ := good 1
      exact normal_eq_self T wt good stable hrs
        (irreducible_of_short (fun p hp => hshort 1 rs hrs p hp))
    · rw [CodeTable.output,ite_eq_right hq]
      obtain ⟨rs,hrs,_⟩ := good (C.encode (EncodedCanonical.least C wf q w)).length
      exact normal_eq_self T wt good stable hrs
        (CodeTable.canonical_irreducible C E wf q z (hiso _ rs hrs) hc hi hq)
  have hpres : present T (C.encode w) = present T (CodeTable.output C wf q z w) := by
    obtain ⟨rs,hrs,hd,_⟩ := good (C.encode w).length
    exact present_steps T hrs hd le_rfl
      (steps_mono (hstatic _ rs hrs) (CodeTable.whole_steps C E wf q z hzero le_rfl))
  exact ((present_eq_iff T wt good stable _ _).mp hpres).trans hfixed

 theorem present_encode_iff (hz : z ∉ C.alphabet) (u v : List A) :
    present T (C.encode u) = present T (C.encode v) ↔ q u = q v := by
  rw [present_eq_iff T wt good stable,
    normal_encode T wt good stable C E wf q z hshort hiso hstatic hc hi hzero,
    normal_encode T wt good stable C E wf q z hshort hiso hstatic hc hi hzero]
  exact CodeTable.output_eq_iff C wf q z hz u v
end CodeQuotient

end SimpleFInftyOvergroups.ContextualEncoding

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_PolynomialNames
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace SimpleFInftyOvergroups.EffectiveNames.Polynomial
open BoundedEncoding
noncomputable section
open scoped Classical

variable {A k : Type*} [CommSemiring k]

variable {m : ℕ} (C : WordCalculus (FreeMonoid A) m)

theorem mem_ball (p : Name k A) :
    value p ∈ C.ball k (cost (fun w => C.grade (FreeMonoid.ofList w)) p) := by
  induction p with
  | nil => exact (C.ball k _).zero_mem
  | cons a p ih =>
    rw [value_cons]
    apply (C.ball k _).add_mem
    · exact C.single_mem_ball k (term_cost_le _ List.mem_cons_self) a.1
    · exact C.ball_mono k (by simp [cost]) ih

theorem value_collectName (p : Name k A) :
    value (collectName C.omega.toList (fun w => (C.normal (FreeMonoid.ofList w)).toList) p) =
      C.collect k (value p) := by
  induction p with
  | nil => simp [collectName]
  | cons a p ih =>
    change value ((if (C.normal (FreeMonoid.ofList a.2)).toList = C.omega.toList then []
      else [(a.1,(C.normal (FreeMonoid.ofList a.2)).toList)]) ++
      collectName C.omega.toList (fun w => (C.normal (FreeMonoid.ofList w)).toList) p) = _
    rw [value_append,ih,value_cons,map_add,C.collect_single]
    by_cases h : C.normal (FreeMonoid.ofList a.2) = C.omega
    · simp [h]
    · have h' : (C.normal (FreeMonoid.ofList a.2)).toList ≠ C.omega.toList := by
        intro he; exact h (by simpa using congrArg FreeMonoid.ofList he)
      simp [h,h']

variable [Primcodable A] [Primcodable k] [Finite k]

omit [Finite k] in
theorem partialKey_full (f : List A → Part (List A)) (p : Name k A)
    (h : ∀ a ∈ p, (C.normal (FreeMonoid.ofList a.2)).toList ∈ f a.2) :
    valueKey (C.collect k (value p)) ∈ partialKey C.omega.toList f p := by
  rw [← value_collectName C p,valueKey_value]
  exact Part.mem_map _ (partialCollect_full _ f _ p h)

end
end SimpleFInftyOvergroups.EffectiveNames.Polynomial

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_MatrixNames
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SimpleFInftyOvergroups.EffectiveNames.MatrixNames
open BoundedEncoding
noncomputable section
open scoped Classical
variable {A k : Type*} [CommRing k] {n : ℕ}

variable {m : ℕ} (C : WordCalculus (FreeMonoid A) m)
 theorem mem_ball (a : Name k A n) :
    C.MatrixBall k (cost (fun w => C.grade (FreeMonoid.ofList w)) a) (value a) :=
  fun i j => C.ball_mono k (entry_cost_le _ a i j) (Polynomial.mem_ball C (a i j))

 theorem column_mem_ball (x : Column k A n) :
    C.ColumnBall k (columnCost (fun w => C.grade (FreeMonoid.ofList w)) x) (columnValue x) :=
  fun i => C.ball_mono k (column_entry_cost_le _ x i) (Polynomial.mem_ball C (x i))

variable [Primcodable A] [Primcodable k] [Finite k]

omit [Finite k] in
 theorem partialColumnKey_full (f : List A → Part (List A)) (x : Column k A n) {d : ℕ}
    (hx : columnCost (fun w => C.grade (FreeMonoid.ofList w)) x ≤ d)
    (h : ∀ w, C.grade (FreeMonoid.ofList w) ≤ d → (C.normal (FreeMonoid.ofList w)).toList ∈ f w) :
    columnKey (C.columnCollect k (columnValue x)) ∈ partialColumnKey C.omega.toList f x := by
  apply Finite.traverse_full (Polynomial.partialKey C.omega.toList f)
    (fun p => Polynomial.valueKey (C.collect k (Polynomial.value p))) x
  intro i
  apply Polynomial.partialKey_full C
  intro a ha
  exact h a.2 ((Polynomial.term_cost_le _ ha).trans ((column_entry_cost_le _ x i).trans hx))

omit [Finite k] in
 theorem partialMatrixKey_full (f : List A → Part (List A)) (a : Name k A n) {d : ℕ}
    (hx : cost (fun w => C.grade (FreeMonoid.ofList w)) a ≤ d)
    (h : ∀ w, C.grade (FreeMonoid.ofList w) ≤ d → (C.normal (FreeMonoid.ofList w)).toList ∈ f w) :
    matrixKey (C.matrixCollect k (value a)) ∈ partialMatrixKey C.omega.toList f a := by
  apply Finite.traverse_full (partialColumnKey C.omega.toList f)
    (fun x => columnKey (C.columnCollect k (columnValue x))) a
  intro i
  exact partialColumnKey_full C f (a i) ((le_maximum (fun i => columnCost (fun w => C.grade (FreeMonoid.ofList w)) (a i)) i).trans hx) h

end
end SimpleFInftyOvergroups.EffectiveNames.MatrixNames

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_MatrixWords
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SimpleFInftyOvergroups.EffectiveNames.MatrixWords
open BoundedEncoding MatrixNames
noncomputable section
open scoped Classical
variable {A k : Type*} [CommRing k] {n : ℕ}

attribute [local instance] WordCalculus.rawMatrixAction

variable {m : ℕ} (C : WordCalculus (FreeMonoid A) m)

def grade (w : List A) : ℕ := C.grade (FreeMonoid.ofList w)

@[simp] theorem grade_nil : grade C [] = 0 := C.grade_one
@[simp] theorem grade_append (u v : List A) : grade C (u++v) = grade C u + grade C v := C.grade_mul _ _

 theorem groupValue_mem (w : Word k A n) : C.UnitBall k (gcost (grade C) w) (groupValue w) := by
  constructor
  · rw [← value_matrix]
    exact fun i j => C.ball_mono k (cost_matrix (grade C) (grade_nil C) (grade_append C) w)
      (MatrixNames.mem_ball C (matrix w) i j)
  · change C.MatrixBall k (gcost (grade C) w) (groupValue w)⁻¹.val
    rw [← groupValue_inverse,← value_matrix]
    have hh := cost_matrix (grade C) (grade_nil C) (grade_append C) (inverse w)
    rw [gcost_inverse] at hh
    exact fun i j => C.ball_mono k hh (MatrixNames.mem_ball C (matrix (inverse w)) i j)

 theorem pointValue_mem (x : Point k A n) : C.ColumnBall k (xcost (grade C) x) (pointValue x) := by
  rw [← value_column]
  exact fun i => C.ball_mono k (cost_column (grade C) (grade_nil C) (grade_append C) x)
    (column_mem_ball C (column x) i)

end
end SimpleFInftyOvergroups.EffectiveNames.MatrixWords

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_MatrixEffective
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SimpleFInftyOvergroups.EffectiveNames.MatrixWords
open BoundedEncoding MatrixNames
noncomputable section
open scoped Classical
variable {A k : Type*} [CommRing k] {n m : ℕ}
variable [Primcodable A] [Primcodable k] [Finite k]
attribute [local instance] WordCalculus.rawMatrixAction

def calculus (C : WordCalculus (FreeMonoid A) m) :=
  (C.matrixActionCalculus k (Fin n)).rekey pairedKey columnKey pairedKey_injective columnKey_injective

def groupLabel (C : WordCalculus (FreeMonoid A) m) (w : Word k A n) : (calculus (n:=n) (k:=k) C).GLabel :=
  ⟨groupValue w,gcost (grade C) w,groupValue_mem C w⟩

def pointLabel (C : WordCalculus (FreeMonoid A) m) (x : Point k A n) : (calculus (n:=n) (k:=k) C).XLabel :=
  ⟨pointValue x,xcost (grade C) x,pointValue_mem C x⟩

def interpretation (C : WordCalculus (FreeMonoid A) m) :
    NamedAction.Interpretation (nameOperations (n:=n) (k:=k) (grade C)) (calculus (k:=k) (n:=n) C) where
  group := groupLabel C
  point := pointLabel C
  group_cost w := rfl
  point_cost x := rfl
  one := WithBound.ext' groupValue_nil rfl
  mul a b := WithBound.ext' (groupValue_append a b) (gcost_append _ a b)
  inv w := WithBound.ext' (groupValue_inverse w) (gcost_inverse _ w)
  act g x := WithBound.ext' (pointValue_act g x)
    (by change gcost _ (g++x.1) + columnCost _ x.2 = gcost _ g + xcost _ x
        simp [gcost_append,xcost,Nat.add_assoc])

 theorem partialGroupKey_full (C : WordCalculus (FreeMonoid A) m)
    (f : List A → Part (List A)) (w : Word k A n) {d : ℕ}
    (hw : gcost (grade C) w ≤ d)
    (h : ∀ u, grade C u ≤ d → (C.normal (FreeMonoid.ofList u)).toList ∈ f u) :
    (interpretation (k:=k) (n:=n) C).gkey w ∈ partialGroupKey C.omega.toList f w := by
  have hp := partialMatrixKey_full C f (matrix w)
    ((cost_matrix (grade C) (grade_nil C) (grade_append C) w).trans hw) h
  have hi := partialMatrixKey_full C f (matrix (inverse w))
    ((cost_matrix (grade C) (grade_nil C) (grade_append C) (inverse w)).trans (by simpa using hw)) h
  change (matrixKey (C.matrixCollect k (groupValue w).val),
    matrixKey (C.matrixCollect k (groupValue w).inv)) ∈ _
  simp only [value_matrix,groupValue_inverse] at hp hi
  exact Part.mem_bind_iff.mpr ⟨_,hp,Part.mem_map _ hi⟩

 theorem partialPointKey_full (C : WordCalculus (FreeMonoid A) m)
    (f : List A → Part (List A)) (x : Point k A n) {d : ℕ}
    (hx : xcost (grade C) x ≤ d)
    (h : ∀ u, grade C u ≤ d → (C.normal (FreeMonoid.ofList u)).toList ∈ f u) :
    (interpretation (k:=k) (n:=n) C).xkey x ∈ partialPointKey C.omega.toList f x := by
  have hh := partialColumnKey_full C f (column x)
    ((cost_column (grade C) (grade_nil C) (grade_append C) x).trans hx) h
  change columnKey (C.columnCollect k (pointValue x)) ∈ partialColumnKey C.omega.toList f (column x)
  simpa only [value_column] using hh

end
end SimpleFInftyOvergroups.EffectiveNames.MatrixWords

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_EffectiveTables
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SimpleFInftyOvergroups.ContextualEncoding
open FiniteAlgebraicEnvelopes FiniteAlgebraicEnvelopes.Bootstrap

namespace CodedProgram
variable {P A S Q : Type*}
  [Primcodable P] [Primcodable A] [Primcodable S] [Primcodable Q]
  [DecidableEq S] [DecidableEq Q]

 theorem partrec_compute (words : P → ℕ → List (List A))
    (code : P → List A → List S) (lt : P → List A → List A → Bool) (z : S)
    (hw : Primrec₂ words) (hc : Primrec₂ code)
    (hl : Primrec (fun x : P × List A × List A => lt x.1 x.2.1 x.2.2))
    {f : P → List A → Part (Option Q)} (hf : Partrec₂ f) :
    Partrec₂ (compute words code lt z f) := by
  have hp : Partrec₂ (fun p w => (f p w).map (w,·)) :=
    (hf.map ((Computable.snd.comp Computable.fst).pair Computable.snd).to₂).to₂
  exact (((Effect.partrec_traverse_parameter hp).comp Computable.fst hw.to_comp).map
    ((Uniform.primrec_table code lt z hc hl).to_comp.comp
      ((Computable.fst.comp Computable.fst).pair Computable.snd)).to₂).to₂

 theorem partrec_search {r : S → S → Prop} [DecidableRel (List.Shortlex r)]
    (C : DelimiterCode A S) (E : FiniteSearch C) (z : S)
    (hw : Primrec E.words) (hc : Primrec C.encode)
    (hl : PrimrecRel (List.Shortlex r))
    {f : P → List A → Part (Option Q)} (hf : Partrec₂ f) :
    Partrec₂ (fun p => CodedSearch.compute (r := r) C E z (f p)) := by
  apply partrec_compute (fun _ => E.words) (fun _ => C.encode)
    (fun _ => CodedSearch.lt (r := r) C) z (hw.comp Primrec.snd).to₂
      (hc.comp Primrec.snd).to₂ _ hf
  exact hl.decide.comp
    (hc.comp (Primrec.fst.comp Primrec.snd))
    (hc.comp (Primrec.snd.comp Primrec.snd))

end CodedProgram
end SimpleFInftyOvergroups.ContextualEncoding

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_FamilyProgram
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SimpleFInftyOvergroups.ContextualEncoding
open FiniteAlgebraicEnvelopes FiniteAlgebraicEnvelopes.Bootstrap

namespace Families
variable {I S : Type*} {A Q : I → Type*} [Fintype I] [Fintype S]
variable {r : S → S → Prop} [Std.Trichotomous r]
variable (C : ∀ i, DelimiterCode (A i) S) (E : ∀ i, FiniteSearch (C i))
  (wf : WellFounded r) (q : ∀ i, List (A i) → Option (Q i)) (z : S)

theorem table_zero : table C E wf q z 0 = Base.absorption z := by
  simp [table, CodeTable.table_zero]
end Families

namespace FamilyProgram
variable {I S : Type*} {A Q : I → Type*} [Fintype I] [Fintype S]
  [DecidableEq S] [∀ i, DecidableEq (A i)] [∀ i, DecidableEq (Q i)]
variable {r : S → S → Prop} [DecidableRel (List.Shortlex r)]
variable (C : ∀ i, DelimiterCode (A i) S) (E : ∀ i, FiniteSearch (C i))
  (z : S) (f : ∀ i, List (A i) → Part (Option (Q i)))

variable (wf : WellFounded r) [Std.Trichotomous r]

theorem compute_full {n : ℕ} (q : ∀ i, List (A i) → Option (Q i))
    (h : ∀ i w, (C i |>.encode w).length ≤ n → q i w ∈ f i w) :
    Families.table C E wf q z n ∈ compute (r := r) C E z f n := by
  by_cases hn : n = 0
  · subst n
    simp [compute_zero, Families.table_zero]
  · rw [compute, ite_eq_right hn]
    apply (Part.mem_map_iff _).mpr
    refine ⟨(Static.letters I).map (fun i => CodeTable.table (C i) (E i) wf (q i) z n), ?_, ?_⟩
    · apply Search.traverse_map
      intro i hi
      exact CodedSearch.compute_full (C i) wf (q i) (E i) z (h i)
    · simp only [Families.table, List.flatMap_def]

theorem compute_eq {n : ℕ} {rs : List (List S × List S)}
    (h : rs ∈ compute (r := r) C E z f n) :
    rs = Families.table C E wf (fun i => Search.value (f i)) z n := by
  by_cases hn : n = 0
  · subst n
    simpa [compute_zero, Families.table_zero] using h
  · exact Part.mem_unique h (compute_full C E z f wf _
      (fun i w hw => Search.value_mem (compute_domain C E z f hn h.1 i w hw)))

include wf

theorem stable {k n : ℕ} (hkn : k ≤ n)
    {rk rn : List (List S × List S)}
    (hk : rk ∈ compute (r := r) C E z f k) (hn : rn ∈ compute (r := r) C E z f n) :
    Selectors.BoundedEq rk rn k := by
  rw [compute_eq C E z f wf hk, compute_eq C E z f wf hn]
  exact Families.stable C E wf _ z hkn

theorem good_zero : GoodTable (r := r) (compute (r := r) C E z f) 0 := by
  refine ⟨Base.absorption z, by simp, ?_, ?_⟩
  · have hh := Families.decreasing C E wf (fun i => Search.value (f i)) z 0
    simpa only [Families.table_zero] using hh
  · constructor
    · intro u u' v v' hu hv x y he hlen
      obtain ⟨a, ha, _⟩ := (Base.mem_absorption z).mp hu
      rcases ha with rfl | rfl <;> simp at hlen
    · intro u u' v v' hu hv p m t hm he hf hlen
      have hml : m.length = 0 := by simp only [List.length_append] at hlen; omega
      exact (hm (List.length_eq_zero_iff.mp hml)).elim

theorem good_at (hz : ∀ i, z ∉ (C i).alphabet)
    (hd : ∀ i j, i ≠ j → Disjoint (C i).alphabet (C j).alphabet) {n : ℕ}
    (ht : ∀ i w, (C i |>.encode w).length ≤ n → (f i w).Dom)
    (hzero : ∀ i, Search.value (f i) [] ≠ none)
    (hc : ∀ i, CodeTable.Contextual (C i) (Search.value (f i)) n)
    (hi : ∀ i, CodeTable.ZeroIdeal (C i) (Search.value (f i)) n) :
    GoodTable (r := r) (compute (r := r) C E z f) n :=
  ⟨_, compute_full C E z f wf _ (fun i w hw => Search.value_mem (ht i w hw)),
    Families.decreasing C E wf _ z n, Families.critical C E wf _ z hz hd hzero hc hi⟩

theorem bootstrap (normal : List S → Part (List S))
    (fixed : normal = tableNormal (compute (r := r) C E z f))
    (hz : ∀ i, z ∉ (C i).alphabet)
    (hd : ∀ i j, i ≠ j → Disjoint (C i).alphabet (C j).alphabet)
    (bounded : ∀ n, 0 < n → Compiler.PartialBudget normal (3 * (n / 10)) →
      (∀ i w, (C i |>.encode w).length ≤ n → (f i w).Dom) ∧
      (∀ i, Search.value (f i) [] ≠ none) ∧
      (∀ i, CodeTable.Contextual (C i) (Search.value (f i)) n) ∧
      (∀ i, CodeTable.ZeroIdeal (C i) (Search.value (f i)) n)) :
    ∀ n, GoodTable (r := r) (compute (r := r) C E z f) n ∧
      Compiler.PartialBudget normal n := by
  apply bootstrap_length_induction wf _ normal fixed
  · intro k n hkn rk hk rn hn
    exact stable C E z f wf hkn hk hn
  · intro n ih
    by_cases hn : n = 0
    · subst n
      exact good_zero C E z f wf
    · obtain ⟨ht, hzero, hc, hi⟩ := bounded n (Nat.pos_of_ne_zero hn)
        (ih _ (strict_dependency (Nat.pos_of_ne_zero hn)))
      exact good_at C E z f wf hz hd ht hzero hc hi
end FamilyProgram
end SimpleFInftyOvergroups.ContextualEncoding

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_EffectiveFamilies
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SimpleFInftyOvergroups.ContextualEncoding
open FiniteAlgebraicEnvelopes Bootstrap
noncomputable section
open scoped Classical

namespace FamilyProgram
variable {I P S : Type*} {A Q : I → Type*}
  [Fintype I] [Fintype S] [Primcodable I] [Primcodable P] [Primcodable S]
  [∀ i, Primcodable (A i)] [∀ i, Primcodable (Q i)]
  [DecidableEq I] [DecidableEq S] [∀ i, DecidableEq (A i)] [∀ i, DecidableEq (Q i)]
variable {r : S → S → Prop} [DecidableRel (List.Shortlex r)]
variable (C : ∀ i, DelimiterCode (A i) S) (E : ∀ i, FiniteSearch (C i)) (z : S)

omit [∀ index, DecidableEq (A index)] in
 theorem partrec_compute [∀ index, DecidableEq (A index)]
    (hw : ∀ i, Primrec (E i).words) (hc : ∀ i, Primrec (C i).encode)
    (hl : PrimrecRel (List.Shortlex r))
    {f : ∀ i, P → List (A i) → Part (Option (Q i))}
    (hf : ∀ i, Partrec₂ (f i)) :
    Partrec₂ (fun p => compute (r:=r) C E z (fun i => f i p)) := by
  have hi : Partrec₂ (fun i (x : P × ℕ) => CodedSearch.compute (r:=r) (C i) (E i) z (f i x.1) x.2) :=
    FiniteParameter.partrec₂ _ (fun i => CodedProgram.partrec_search (C i) (E i) z (hw i) (hc i) hl (hf i))
  have ht : Partrec₂ (fun x : P × ℕ => fun i => CodedSearch.compute (r:=r) (C i) (E i) z (f i x.1) x.2) :=
    hi.comp Computable.snd Computable.fst
  have hs : Partrec (fun x : P × ℕ =>
      (Effect.traverse (fun i => CodedSearch.compute (r:=r) (C i) (E i) z (f i x.1) x.2)
        (Static.letters I)).map (fun rs => Base.absorption z ++ rs.flatten)) :=
    ((Effect.partrec_traverse_parameter ht).comp Computable.id (Computable.const _)).map
      ((Primrec.list_append.comp (Primrec.const (Base.absorption z))
        (Primrec.list_flatten.comp Primrec.snd)).to_comp).to₂
  exact (Partrec.cond ((Primrec.eq.comp Primrec.snd (Primrec.const 0)).decide.to_comp)
    (Computable.const (Base.absorption z)).partrec hs).of_eq (by
      intro x
      simp only [compute]
      split <;> simp_all)
end FamilyProgram
end
end SimpleFInftyOvergroups.ContextualEncoding

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_ContextualCompiler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SimpleFInftyOvergroups.ContextualEncoding.Source
noncomputable section
open FiniteAlgebraicEnvelopes Bootstrap Compiler Compiler.Simulator MachineRealization
open BoundedEncoding NamedAction
open scoped Classical Compiler.HeadCodec

def rel (a b : Sigma) : Prop := Encodable.encode a < Encodable.encode b
local instance instDecidableRelSigmaRel_rbbe81b_1 : DecidableRel rel := fun _ _ => inferInstanceAs (Decidable (_ < _))
local instance instTrichotomousSigmaRel : Std.Trichotomous rel := ⟨fun a b hab hba => by
  apply Encodable.encode_injective
  change ¬Encodable.encode a < Encodable.encode b at hab
  change ¬Encodable.encode b < Encodable.encode a at hba
  omega⟩
theorem wf_rel : WellFounded rel := InvImage.wf Encodable.encode Nat.lt_wfRel.wf

theorem primrec_shortlex : PrimrecRel (List.Shortlex rel) := by
  let ord : LinearOrder Sigma := LinearOrder.lift' Encodable.encode Encodable.encode_injective
  exact @Search.primrec_shortlex _ _ _ ord ⟨inferInstance, Primrec.dom_finite _⟩

def raw (n : ℕ) (w : List Sigma) : Part (List Sigma) :=
  WordProgramming.eval ((Encodable.decode n : Option Nat.Partrec.Code).getD .zero) w

theorem raw_encode (c : Nat.Partrec.Code) : raw (Encodable.encode c) = WordProgramming.eval c := by
  funext w
  simp [raw]

theorem partrec_raw : Partrec₂ raw :=
  WordProgramming.partrec_eval.comp
    (Primrec.option_getD.comp (Primrec.decode.comp Primrec.fst) (Primrec.const .zero)).to_comp Computable.snd

end
end SimpleFInftyOvergroups.ContextualEncoding.Source

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_ContractedNormalForms
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.Contracted.countableAlgebra _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SimpleFInftyOvergroups.SemanticEncoding
noncomputable section
open FiniteAlgebraicEnvelopes
open scoped Classical

namespace NormalPresentation
variable {M K : Type*} [Monoid M] [MonoidWithZero K] (P : NormalPresentation M K)
variable (k : Type*) [CommRing k]

def sectionMap : Contracted.Algebra k K →ₗ[k] MonoidAlgebra k M :=
  (Contracted.monoidBasis (k:=k) (H:=K)).constr k
    (fun h => MonoidAlgebra.single (P.representative h.val) 1)

 theorem sectionMap_basis (h : K) (c : k) :
    P.sectionMap k (Contracted.basis k K h c) =
      if h = 0 then 0 else MonoidAlgebra.single (P.representative h) c := by
  by_cases hh : h = 0
  · simp [hh]
  · have he : Contracted.basis k K h c = c • Contracted.basis k K h 1 := by
      simp only [Contracted.basis, ← map_smul, MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
    rw [he, map_smul, ite_eq_right hh]
    have hb := (Contracted.monoidBasis (k:=k) (H:=K)).constr_basis
      k (fun h => MonoidAlgebra.single (P.representative h.val) (1:k)) ⟨h,hh⟩
    rw [Contracted.monoidBasis_apply] at hb
    change P.sectionMap k (Contracted.basis k K h 1) = _ at hb
    rw [hb]
    simp

 theorem algebraMap_section (x : Contracted.Algebra k K) :
    P.algebraMap k (P.sectionMap k x) = x := by
  have he : (P.algebraMap k).toLinearMap.comp (P.sectionMap k) = LinearMap.id := by
    apply (Contracted.monoidBasis (k:=k) (H:=K)).ext
    intro h
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply,
      Contracted.monoidBasis_apply, P.sectionMap_basis, ite_eq_right h.property,
      P.algebraMap_single, P.q_representative, LinearMap.id_apply]
  exact LinearMap.congr_fun he x

 theorem sectionMap_injective : Function.Injective (P.sectionMap k) :=
  Function.LeftInverse.injective (P.algebraMap_section k)

 theorem algebraMap_surjective : Function.Surjective (P.algebraMap k) :=
  Function.RightInverse.surjective (P.algebraMap_section k)

 theorem section_algebraMap_single (w : M) (c : k) :
    P.sectionMap k (P.algebraMap k (MonoidAlgebra.single w c)) =
      if P.normal w = P.omega then 0 else MonoidAlgebra.single (P.normal w) c := by
  rw [P.algebraMap_single, P.sectionMap_basis, P.representative_q, P.normal_eq_zero_iff]

 theorem section_algebraMap {m : ℕ} (C : BoundedEncoding.WordCalculus M m)
    (hn : C.normal = P.normal) (hz : C.omega = P.omega) (a : MonoidAlgebra k M) :
    P.sectionMap k (P.algebraMap k a) = C.collect k a := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add,ha,hb]
  | single w c => simp only [P.section_algebraMap_single, C.collect_single, hn, hz]

end NormalPresentation
end
end SimpleFInftyOvergroups.SemanticEncoding

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_RingAssemblyTools
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SimpleFInftyOvergroups.RingAssembly
open scoped Classical TensorProduct
open FiniteAlgebraicEnvelopes

variable {k B : Type*} [CommRing k] [Ring B] [Algebra k B]
open PartialAffine.Corner

def binaryS : Fin 2 → MonoidAlgebra k PartialAffine.monoid := ![s0 k,s1 k]
def binaryD : Fin 2 → MonoidAlgebra k PartialAffine.monoid := ![t0 k,t1 k]

lemma q_binaryS (i : Fin 2) : q k*binaryS i=binaryS i := by
  fin_cases i
  · exact q_s0 k
  · exact q_s1 k
lemma binaryS_q (i : Fin 2) : binaryS i*q k=binaryS i := by
  fin_cases i
  · exact s0_q k
  · exact s1_q k
lemma q_binaryD (i : Fin 2) : q k*binaryD i=binaryD i := by
  fin_cases i
  · exact q_t0 k
  · exact q_t1 k
lemma binaryD_q (i : Fin 2) : binaryD i*q k=binaryD i := by
  fin_cases i
  · exact t0_q k
  · exact t1_q k
lemma binaryDS (i j : Fin 2) : binaryD i*binaryS j=if i=j then q k else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [binaryS,binaryD,t0_s0,t0_s1,t1_s0,t1_s1]
lemma binary_partition : binaryS (k:=k) 0*binaryD 0+binaryS 1*binaryD 1=q k :=
  s0_t0_add_s1_t1 k

variable (ξ : B ⊗[k] MonoidAlgebra k PartialAffine.monoid →ₙₐ[k] B)

def binaryPhi : B →ₙₐ[k] B := ξ.comp (cornerTensor k B)

lemma binaryPhi_apply (a : B) : binaryPhi ξ a=ξ (a⊗ₜ[k] q k) := rfl

lemma binary_constant_commute (c : MonoidAlgebra k PartialAffine.monoid)
    (hqc : q k*c=c) (hcq : c*q k=c) (a : B) :
    Commute (ξ (1⊗ₜ[k] c)) (binaryPhi ξ a) := by
  change ξ (1⊗ₜ[k] c)*binaryPhi ξ a=binaryPhi ξ a*ξ (1⊗ₜ[k] c)
  rw [binaryPhi_apply,←map_mul,←map_mul]
  simp only [Algebra.TensorProduct.tmul_mul_tmul,one_mul,mul_one,hqc,hcq]

def binaryData : CompressedSplittings.BinaryData (binaryPhi ξ : B →ₙ+* B) where
  s i := ξ (1⊗ₜ[k] binaryS i)
  d i := ξ (1⊗ₜ[k] binaryD i)
  s_left i := by
    change ξ (1⊗ₜ[k] q k)*ξ (1⊗ₜ[k] binaryS i)=_
    rw [←map_mul,Algebra.TensorProduct.tmul_mul_tmul,one_mul,q_binaryS]
  s_right i := by
    change ξ (1⊗ₜ[k] binaryS i)*ξ (1⊗ₜ[k] q k)=_
    rw [←map_mul,Algebra.TensorProduct.tmul_mul_tmul,one_mul,binaryS_q]
  d_left i := by
    change ξ (1⊗ₜ[k] q k)*ξ (1⊗ₜ[k] binaryD i)=_
    rw [←map_mul,Algebra.TensorProduct.tmul_mul_tmul,one_mul,q_binaryD]
  d_right i := by
    change ξ (1⊗ₜ[k] binaryD i)*ξ (1⊗ₜ[k] q k)=_
    rw [←map_mul,Algebra.TensorProduct.tmul_mul_tmul,one_mul,binaryD_q]
  s_commute i := binary_constant_commute ξ (binaryS i) (q_binaryS i) (binaryS_q i)
  d_commute i := binary_constant_commute ξ (binaryD i) (q_binaryD i) (binaryD_q i)
  ds i j := by
    rw [←map_mul,Algebra.TensorProduct.tmul_mul_tmul,one_mul,binaryDS]
    split_ifs
    · rfl
    · rw [TensorProduct.tmul_zero,map_zero]
  partition := by
    rw [←map_mul,←map_mul,←map_add]
    simp only [Algebra.TensorProduct.tmul_mul_tmul,one_mul,←TensorProduct.tmul_add,binary_partition]
    rfl

 theorem binaryPhi_injective (hξ : Function.Injective ξ) : Function.Injective (binaryPhi ξ) :=
  hξ.comp (cornerTensor_injective k B)

end SimpleFInftyOvergroups.RingAssembly
end

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_TwoEnlargements
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SourceEnlargement

section OneLayer
variable (K : Type) [CommRing K]
variable (V Z : Type) [Group V] [MulAction V Z]

abbrev enlargedGroup := group (V := V) (BinaryPrefixOperators.idempotents K)
  (fun _ h => BinaryPrefixOperators.idempotents_are_idempotent K h)

instance enlargedAction : MulAction (enlargedGroup K V) (enlargedSet K Z) :=
  @MulAction.compHom _ _ _ _
    (unitsAction (D := BinaryPrefixOperators.algebra K) (V := V) (Z := Z))
    _ (enlargedGroup K V).subtype

variable {V Z}

def j (E : BinaryPrefixOperators.idempotents K) : V →* enlargedGroup K V :=
  map (BinaryPrefixOperators.idempotents K)
    (fun _ h => BinaryPrefixOperators.idempotents_are_idempotent K h) E

def groupEmbedding : V →* enlargedGroup K V :=
  j K ⟨1, BinaryPrefixOperators.identity_mem K⟩

lemma groupEmbedding_pointEmbedding (g : V) (z : Z) :
    groupEmbedding K g • pointEmbedding K z = pointEmbedding K (g • z) :=
  map_identity_basis (BinaryPrefixOperators.idempotents K)
    (fun _ h => BinaryPrefixOperators.idempotents_are_idempotent K h)
    (BinaryPrefixOperators.identity_mem K) g z

end OneLayer

namespace Double
variable (Q X : Type) [Group Q] [MulAction Q X]

abbrev W₁ := enlargedGroup (ZMod 2) Q
abbrev W := enlargedGroup (ZMod 3) (W₁ Q)

instance action₁ : MulAction (W₁ Q) (Y₁ X) :=
  enlargedAction (ZMod 2) Q X

instance action₂ : MulAction (W Q) (AmbientY X) :=
  enlargedAction (ZMod 3) (W₁ Q) (Y₁ X)

instance smul₁ : SMul (W₁ Q) (Y₁ X) := (action₁ Q X).toSMul
instance smul₂ : SMul (W Q) (AmbientY X) := (action₂ Q X).toSMul

variable {Q X}

def orbitSet : Set (AmbientY X) :=
  Saturation.carrier (W := W Q) (ambientPoint (X := X))

abbrev Y := orbitSet (Q := Q) (X := X)

instance orbitAction : MulAction (W Q) (Y (Q := Q) (X := X)) :=
  Saturation.action (W := W Q) (ambientPoint (X := X))

end Double
end SourceEnlargement
end

end OAI
end


