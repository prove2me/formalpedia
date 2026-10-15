-- Prove2me | Definitions.Def_OAI_Combinatorics_ParityLifts_TestAlgebra
-- name    : OAI_Combinatorics_ParityLifts_TestAlgebra
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T04:23:41.090304+00:00
-- url     : https://prove2.me/theorems/7b966260-a6e4-428d-a6fc-e1b0e5af962c
-- title:
--   Equality and edge tests, and the algebra spanned by rooted homomorphism counts on tuples of two graphs
-- statement:
--   Throughout, $G$ and $H$ are simple graphs on finite sets $V$ and $W$. A rooted test $F$ with $k$ roots and width parameter $t$ has a finite vertex set with a symmetric relation, root labels $\rho_F(0),\dots,\rho_F(k-1)$, and a rooted tree decomposition with bags of size at most $t$, child–parent intersections of size less than $t$, and root bag equal to the set of roots; $\hom_x(F,G)$ is the number of relation-preserving maps into $G$ sending $\rho_F(j)$ to $x_j$ for all $j$.
--
--   1. **Equality test.** For $k\le t$ and $i,j<k$, the equality test $E_{ij}$ has vertex set $\{0,\dots,k-1\}$ with $i$ and $j$ identified, the quotient map as root labelling, the empty relation, and a single bag. A map of $E_{ij}$ over $x$ exists, and is then unique, exactly when $x_i=x_j$.
--
--   2. **Edge test.** For $k\le t$ and $i,j<k$, the edge test $A_{ij}$ has vertex set $\{0,\dots,k-1\}$, the identity as root labelling, the relation $\{(i,j),(j,i)\}$ (a loop when $i=j$), and a single bag. A map of $A_{ij}$ over $x$ exists, and is then unique, exactly when $x_ix_j\in E(G)$.
--
--   3. **Test evaluations.** Let $\mathcal T_k=V^k\sqcup W^k$ be the set of $k$-tuples of either graph. For a rooted test $F$ with $k$ roots, its evaluation $\operatorname{ev}_F:\mathcal T_k\to\mathbb{Q}$ is $x\mapsto\hom_x(F,G)$ on $V^k$ and $x\mapsto\hom_x(F,H)$ on $W^k$.
--
--   4. **Test span and test algebra.** The test span is the $\mathbb{Q}$-linear subspace
--   $$
--   \mathcal S_{k,t}=\operatorname{span}_{\mathbb{Q}}\bigl\{\operatorname{ev}_F : F\text{ a rooted test with }k\text{ roots and width parameter }t\bigr\}\subseteq\mathbb{Q}^{\mathcal T_k}.
--   $$
--   When $k\le t$ it contains the constant function $1$ (the evaluation of the test consisting of $k$ isolated roots) and is closed under pointwise multiplication (the product $\operatorname{ev}_F\operatorname{ev}_{F'}$ is the evaluation of the test obtained by gluing $F$ and $F'$ along all roots), so it is a $\mathbb{Q}$-subalgebra of $\mathbb{Q}^{\mathcal T_k}$, the test algebra.
--
--   5. **Reindexing and summing out.** For $\psi:\{0,\dots,k-1\}\to\{0,\dots,m-1\}$, the linear map $\psi^{*}:\mathbb{Q}^{\mathcal T_k}\to\mathbb{Q}^{\mathcal T_m}$ is $(\psi^{*}f)(x)=f(x\circ\psi)$. For $i\in\{0,\dots,k\}$, the linear map $\Sigma_i:\mathbb{Q}^{\mathcal T_{k+1}}\to\mathbb{Q}^{\mathcal T_k}$ inserts a new entry at position $i$ and sums it out:
--   $$
--   (\Sigma_i f)(x)=\sum_{y\in V}f\bigl(x^{(i\leftarrow y)}\bigr)\ \ (x\in V^k),\qquad(\Sigma_i f)(x)=\sum_{y\in W}f\bigl(x^{(i\leftarrow y)}\bigr)\ \ (x\in W^k),
--   $$
--   where $x^{(i\leftarrow y)}=(x_0,\dots,x_{i-1},y,x_i,\dots,x_{k-1})$.
--
--   The test algebra is where the parity reduction converts equal homomorphism counts into equal Weisfeiler–Leman colour histograms: atomic types of tuples are expressed through equality and edge tests, and colour refinement is expressed through products, reindexing and summing out, operations that keep functions inside the test span under suitable bounds on $k$ relative to $t$.
--
--   **Formalization Note** The objects are `equalityTest hkt i j` and `edgeTest hkt i j` (both built with `singleBagTest`; the identification of $i$ with $j$ is the quotient `EqRoot i j` of `Fin k`), `TuplePair V W k = (Fin k → V) ⊕ (Fin k → W)`, `testEval`, `testSpan`, `testAlgebra k t hkt`, `tupleReindex`, `reindexLinear` and `sumInsertLinear`. The span ranges over all rooted tests whose vertex and node types lie in `Type`. The count identities for the equality and edge tests are proved as separate results.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/ParityLifts/TestAlgebra.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ParityLifts/TestAlgebra.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ParityLifts mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ParityLifts
import Definitions.Def_OAI_Combinatorics_ParityLifts_LiftCounts
import Definitions.Def_OAI_Combinatorics_ParityLifts_WeightedDual
import Definitions.Def_OAI_Combinatorics_ParityLifts_Masses
import Definitions.Def_OAI_Combinatorics_ParityLifts_BaseLabels
import Definitions.Def_OAI_Combinatorics_ParityLifts_BalancedBags
import Definitions.Def_OAI_Combinatorics_ParityLifts_DecompositionCuts
import Definitions.Def_OAI_Combinatorics_ParityLifts_Witnesses
import Definitions.Def_OAI_Combinatorics_ParityLifts_BagTrees
import Definitions.Def_OAI_Combinatorics_ParityLifts_TagSizes
import Definitions.Def_OAI_Combinatorics_ParityLifts_Detection
import Definitions.Def_OAI_Combinatorics_ParityLifts_RankedTrees
import Definitions.Def_OAI_Combinatorics_ParityLifts_RootedTests
import Definitions.Def_OAI_Combinatorics_ParityLifts_GlueTrees
import Definitions.Def_OAI_Combinatorics_ParityLifts_GlueVertices
import Definitions.Def_OAI_Combinatorics_ParityLifts_Rerooting

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace ParityWL

open scoped BigOperators

section AtomicTests

open scoped Classical

variable {k t : ℕ}

def EqRootRel (i j a b : Fin k) : Prop := a = i ∧ b = j

def EqRoot (i j : Fin k) := Quot (EqRootRel i j)

noncomputable instance eqRootFintype (i j : Fin k) : Fintype (EqRoot i j) :=
  Fintype.ofSurjective (Quot.mk (EqRootRel i j))
    (fun q => Quot.inductionOn q (fun a => ⟨a, rfl⟩))

noncomputable def equalityTest (hkt : k ≤ t) (i j : Fin k) : RootedTest k t := by
  letI : Fintype (Quot (EqRootRel i j)) := eqRootFintype i j
  exact singleBagTest (A := EqRoot i j) (fun _ _ : EqRoot i j => False) ⟨fun _ _ h => h⟩
    (Quot.mk (EqRootRel i j)) (fun q => Quot.inductionOn q (fun a => ⟨a, rfl⟩))
    ((Fintype.card_le_of_surjective (fun a : Fin k => (Quot.mk (EqRootRel i j) a : EqRoot i j))
      (fun q => Quot.inductionOn q (fun a => ⟨a, rfl⟩))).trans (by simpa using hkt))

noncomputable def edgeTest (hkt : k ≤ t) (i j : Fin k) : RootedTest k t :=
  singleBagTest (fun a b : Fin k => (a = i ∧ b = j) ∨ (a = j ∧ b = i))
    ⟨by rintro a b (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
        <;> simp only [true_and, true_or, or_true]⟩
    id Function.surjective_id (by simpa using hkt)

end AtomicTests

section TestAlgebra

open scoped Classical

abbrev TuplePair (V W : Type) (k : ℕ) := (Fin k → V) ⊕ (Fin k → W)

variable {V W : Type} [Fintype V] [Fintype W] (G : SimpleGraph V) (H : SimpleGraph W)

noncomputable def testEval {k t : ℕ} (F : RootedTest k t) : TuplePair V W k → ℚ :=
  Sum.elim (F.count G) (F.count H)

noncomputable def testSpan (k t : ℕ) : Submodule ℚ (TuplePair V W k → ℚ) :=
  Submodule.span ℚ (Set.range (fun F : RootedTest k t => testEval G H F))

lemma testEval_mem {k t : ℕ} (F : RootedTest k t) : testEval G H F ∈ testSpan G H k t :=
  Submodule.subset_span ⟨F, rfl⟩

lemma testSpan_one {k t : ℕ} (hkt : k ≤ t) : (1 : TuplePair V W k → ℚ) ∈ testSpan G H k t := by
  have he : testEval G H (isolatedTest k t hkt) = 1 := by
    funext a
    cases a with
    | inl x => exact isolatedTest_count k t hkt G x
    | inr x => exact isolatedTest_count k t hkt H x
  rw [← he]
  exact testEval_mem _ _ _

lemma testEval_mul_mem {k t : ℕ} (hkt : k ≤ t) (F L : RootedTest k t) :
    testEval G H F * testEval G H L ∈ testSpan G H k t := by
  let Fs : Fin 2 → RootedTest k t := ![F, L]
  let P := glueTest Fs (fun _ => id) hkt
  have he : testEval G H P = testEval G H F * testEval G H L := by
    funext a
    cases a with
    | inl x =>
      change P.count G x = F.count G x * L.count G x
      simp only [P, glueTest_count, Fin.prod_univ_two, Fs, Matrix.cons_val_zero,
        Matrix.cons_val_one, Function.comp_id]
    | inr x =>
      change P.count H x = F.count H x * L.count H x
      simp only [P, glueTest_count, Fin.prod_univ_two, Fs, Matrix.cons_val_zero,
        Matrix.cons_val_one, Function.comp_id]
  rw [← he]
  exact testEval_mem _ _ _

lemma testSpan_mul {k t : ℕ} (hkt : k ≤ t) {f g : TuplePair V W k → ℚ}
    (hf : f ∈ testSpan G H k t) (hg : g ∈ testSpan G H k t) : f * g ∈ testSpan G H k t := by
  refine Submodule.span_induction₂ (p := fun f g _ _ => f * g ∈ testSpan G H k t)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ hf hg
  · rintro _ _ ⟨F, rfl⟩ ⟨L, rfl⟩
    exact testEval_mul_mem G H hkt F L
  · intro _ _
    simpa only [zero_mul] using (testSpan G H k t).zero_mem
  · intro _ _
    simpa only [mul_zero] using (testSpan G H k t).zero_mem
  · intro f g h _ _ _ hf hg
    simpa only [add_mul] using (testSpan G H k t).add_mem hf hg
  · intro f g h _ _ _ hf hg
    simpa only [mul_add] using (testSpan G H k t).add_mem hf hg
  · intro a f g _ _ hf
    simpa only [smul_mul_assoc] using (testSpan G H k t).smul_mem a hf
  · intro a f g _ _ hf
    simpa only [mul_smul_comm] using (testSpan G H k t).smul_mem a hf

noncomputable def testAlgebra (k t : ℕ) (hkt : k ≤ t) : Subalgebra ℚ (TuplePair V W k → ℚ) where
  carrier := testSpan G H k t
  mul_mem' := testSpan_mul G H hkt
  one_mem' := testSpan_one G H hkt
  add_mem' := (testSpan G H k t).add_mem
  zero_mem' := (testSpan G H k t).zero_mem
  algebraMap_mem' a := by
    rw [Algebra.algebraMap_eq_smul_one]
    exact (testSpan G H k t).smul_mem a (testSpan_one G H hkt)

end TestAlgebra

section TestOperations

open scoped Classical

variable {V W : Type} [Fintype V] [Fintype W]
variable (G : SimpleGraph V) (H : SimpleGraph W)

def tupleReindex {k m : ℕ} (φ : Fin k → Fin m) : TuplePair V W m → TuplePair V W k :=
  Sum.map (fun x => x ∘ φ) (fun x => x ∘ φ)

noncomputable def reindexLinear {k m : ℕ} (φ : Fin k → Fin m) :
    (TuplePair V W k → ℚ) →ₗ[ℚ] (TuplePair V W m → ℚ) where
  toFun f := f ∘ tupleReindex φ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def sumInsertLinear {k : ℕ} (i : Fin (k + 1)) :
    (TuplePair V W (k + 1) → ℚ) →ₗ[ℚ] (TuplePair V W k → ℚ) where
  toFun f := Sum.elim (fun x => ∑ y : V, f (.inl (i.insertNth y x)))
    (fun x => ∑ y : W, f (.inr (i.insertNth y x)))
  map_add' f g := by
    funext a
    cases a <;> simp only [Sum.elim_inl, Sum.elim_inr, Pi.add_apply, Finset.sum_add_distrib]
  map_smul' a f := by
    funext x
    cases x <;> simp only [Sum.elim_inl, Sum.elim_inr, Pi.smul_apply, Finset.smul_sum,
      RingHom.id_apply]

end TestOperations

end ParityWL

end OAI


