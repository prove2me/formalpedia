-- Prove2me | Definitions.Def_OAIQ115N007
-- name    : OAIQ115N007
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T00:32:55.280991+00:00
-- url     : https://prove2.me/theorems/07fb9329-3aad-4cd6-8387-237dccfdab57
-- title:
--   Definitions bundle OAIQ115N007 of the split of OpenAI, A counterexample to Naimark's problem in ZFC
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.NaimarkZFC.main`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to Naimark's problem in ZFC*, OpenAI Math Release, September 24, 2026, result family 297, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 54 declarations of OpenAI's Lean: 6 definitions and 48 theorems. The definitions and types are `OAI.NaimarkZFC.FockAway`, `OAI.NaimarkZFC.FockStarts`, `OAI.NaimarkZFC.atomicFiniteAlgebra`, `OAI.NaimarkZFC.finiteFactorCorner`, `OAI.NaimarkZFC.normalSpan`, `OAI.NaimarkZFC.projectionCorner`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Naimark_Amalgamation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/Amalgamation.lean).
--
--   **Imports.** It imports the bundles `OAIQ115N004` and `OAIQ115N005` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ115N010` and `OAIQ115N011`.
-- source:
--   OpenAI, A counterexample to Naimark's problem in ZFC, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 297; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-counterexample-to-Naimarks-problem-in-ZFC-September-24-2026/naimark-counterexample-zfc.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ115N004
import Definitions.Def_OAIQ115N005

section
-- module Solutions.OAIQ115_Naimark.Naimark_Amalgamation
attribute [-instance] _root_.OAI.NaimarkZFC.CStarCompletion.instCStarAlgebraCompletionOfCStarRingOfStarModuleComplex_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instNormedAlgebraComplexCompletion_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instStarCompletion_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instStarRingCompletion_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace NaimarkZFC

attribute [local instance] Classical.propDecidable

open scoped ComplexOrder InnerProductSpace
open UniformSpace

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open Filter
open scoped Topology

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open Filter
open scoped Topology
variable {A V : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open scoped InnerProductSpace
variable {V : Type*} {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

open scoped InnerProductSpace
variable {V A H : Type*} [CStarAlgebra A] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

open scoped InnerProductSpace lp

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {A V : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem indexedColumnRepresentation_apply (τ : A →ₚ[ℂ] ℂ) (hτ : IsTracialPositive τ)
    (e : V → {a : A // IsStarProjection a})
    (horth : ∀ l k, l ≠ k → (e l).1 * (e k).1 = 0)
    (hmass : HasSum (fun l => (τ (e l).1).re) (τ 1).re)
    (hpos : ∀ l, 0 < (τ (e l).1).re) (r : V) (a : A)
    (x : ℓ²(Option (Σ l, CenteredColumnIndex τ hτ e l r), ℂ)) :
    indexedColumnRepresentation τ hτ e horth hmass hpos r a x =
      (tracialColumnBasis τ hτ e horth hmass hpos r).repr
        (traceColumnRepresentation τ hτ (e r) a
          ((tracialColumnBasis τ hτ e horth hmass hpos r).repr.symm x)) := rfl

open scoped InnerProductSpace lp
variable {A V : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

section
open scoped InnerProductSpace lp
variable {A V : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (τ : A →ₚ[ℂ] ℂ) (hτ : IsTracialPositive τ)
  (e : V → {a : A // IsStarProjection a})
  (horth : ∀ l k, l ≠ k → (e l).1 * (e k).1 = 0)
  (hmass : HasSum (fun l => (τ (e l).1).re) (τ 1).re)
  (hpos : ∀ l, 0 < (τ (e l).1).re)

theorem indexedColumnRepresentation_vacuum_vector (r : V)
    [DecidableEq (Option (Σ l, CenteredColumnIndex τ hτ e l r))] (a : A) :
    indexedColumnRepresentation τ hτ e horth hmass hpos r a (lp.single 2 none 1) =
      (tracialColumnBasis τ hτ e horth hmass hpos r).repr
        (traceColumnRepresentation τ hτ (e r) a (columnUnit τ hτ (e r))) := by
  let basis := tracialColumnBasis τ hτ e horth hmass hpos r
  exact (indexedColumnRepresentation_apply τ hτ e horth hmass hpos r a _).trans
    (congrArg (fun vector => basis.repr (traceColumnRepresentation τ hτ (e r) a vector))
      ((basis.repr_symm_single none).trans
        (tracialColumnBasis_none τ hτ e horth hmass hpos r)))

theorem indexedColumnRepresentation_vacuum (r : V)
    [DecidableEq (Option (Σ l, CenteredColumnIndex τ hτ e l r))] (a : A) :
    indexedColumnRepresentation τ hτ e horth hmass hpos r a (lp.single 2 none 1) none =
      (((Real.sqrt (τ (e r).1).re)⁻¹ : ℂ) ^ 2) * τ ((e r).1 * a * (e r).1) := by
  let b := tracialColumnBasis τ hτ e horth hmass hpos r
  calc
    _ = b.repr (traceColumnRepresentation τ hτ (e r) a (columnUnit τ hτ (e r))) none :=
      congrArg (fun vector => vector none)
        (indexedColumnRepresentation_vacuum_vector τ hτ e horth hmass hpos r a)
    _ = inner ℂ (b none)
        (traceColumnRepresentation τ hτ (e r) a (columnUnit τ hτ (e r))) :=
      b.repr_apply_apply _ none
    _ = inner ℂ (columnUnit τ hτ (e r))
        (traceColumnRepresentation τ hτ (e r) a (columnUnit τ hτ (e r))) :=
      congrArg (fun vector => inner ℂ vector
        (traceColumnRepresentation τ hτ (e r) a (columnUnit τ hτ (e r))))
        (tracialColumnBasis_none τ hτ e horth hmass hpos r)
    _ = _ := columnUnit_inner_action τ hτ (e r) a

end

open Filter Topology
variable {A V : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open Filter Topology
open scoped InnerProductSpace lp
variable {A V : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

attribute [local instance] Classical.propDecidable

open scoped InnerProductSpace ENNReal lp

variable {ι κ : Type*} {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

variable {ι : Type*} {J : ι → Type*} {H : ι → Type*}
  [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)]
  [∀ i, CompleteSpace (H i)]

open scoped InnerProductSpace ENNReal lp

variable {ι : Type*} {H K : ι → Type*}
  [∀ i, NormedAddCommGroup (H i)] [∀ i, NormedAddCommGroup (K i)]
  [∀ i, InnerProductSpace ℂ (H i)] [∀ i, InnerProductSpace ℂ (K i)]

variable [∀ i, CompleteSpace (H i)] [∀ i, CompleteSpace (K i)]

variable {A : Type*} [CStarAlgebra A]

open scoped InnerProductSpace ENNReal lp
variable {I V : Type*} (L : I → V → V → Type*) [DecidableEq I]

variable {A : I → Type*} [∀ i, CStarAlgebra (A i)]

open scoped InnerProductSpace lp
variable {I V : Type*} (L : I → V → V → Type*) [DecidableEq I]

variable {A : I → Type*} [∀ i, CStarAlgebra (A i)]

section
open scoped InnerProductSpace lp
variable {I V : Type*} (L : I → V → V → Type*) [DecidableEq I]

def FockAway (i : I) (x : AtomicFockSpace L) : Prop :=
  ∀ j, j.1 = some i → x j = 0

def FockStarts (i : I) (x : AtomicFockSpace L) : Prop :=
  ∀ j, j.1 ≠ some i → x j = 0

theorem fockBlockUnitary_symm_away (i : I) (x : AtomicFockSpace L)
    (hx : FockAway L i x) (t : FockTail L i) :
    (fockBlockUnitary L i).symm x t = lp.single 2 none (x t.1) := by
  classical
  ext c
  rw [fockBlockUnitary_symm_apply]
  cases c with
  | none => simp [fockJoin]
  | some c =>
    simp only [lp.single_apply, Pi.single_eq_of_ne (Option.some_ne_none c)]
    exact hx _ rfl

variable {A : I → Type*} [∀ i, CStarAlgebra (A i)]
variable (π : ∀ i r, A i →⋆ₐ[ℂ]
  (ℓ²(ColumnIndex L i r, ℂ) →L[ℂ] ℓ²(ColumnIndex L i r, ℂ)))

theorem atomicFock_creation (i : I) (a : A i) (x : AtomicFockSpace L)
    (hx : FockAway L i x) (t : FockTail L i) (c : ColumnIndex L i t.1.2.1) :
    atomicFockRepresentation L π i a x (fockJoin L i ⟨t,c⟩) =
      x t.1 * π i t.1.2.1 a (lp.single 2 none 1) c := by
  classical
  rw [atomicFockRepresentation_block, fockBlockUnitary_symm_away L i x hx]
  have h : lp.single 2 none (x t.1) = x t.1 •
      (lp.single 2 none 1 : ℓ²(ColumnIndex L i t.1.2.1, ℂ)) := by
    rw [← lp.single_smul]; simp
  rw [h, map_smul]
  rfl

theorem atomicFock_creation_starts (i : I) (a : A i)
    (ha : ∀ r, π i r a (lp.single 2 none 1) none = 0)
    (x : AtomicFockSpace L) (hx : FockAway L i x) :
    FockStarts L i (atomicFockRepresentation L π i a x) := by
  intro j hj
  have h := atomicFock_creation L π i a x hx ⟨j,hj⟩ none
  simpa [fockJoin, ha] using h

end

section
open scoped InnerProductSpace lp
variable {I V : Type*} (L : I → V → V → Type*) [DecidableEq I]

omit [DecidableEq I] in

theorem fockStarts_away {i k : I} (hik : i ≠ k) (x : AtomicFockSpace L)
    (hx : FockStarts L i x) : FockAway L k x := by
  intro j hj
  apply hx j
  rw [hj]
  exact fun h => hik (Option.some.inj h).symm

end

open scoped InnerProductSpace lp
variable {V J : Type*}

theorem l2Embed_apply_of_not_mem (e : V ↪ J) (z : ℓ²(V, ℂ)) (j : J)
    (hj : j ∉ Set.range e) : l2Embed e z j = 0 := by
  classical
  have h := (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) z).mapL
    ((lp.evalCLM ℂ (fun _ : J => ℂ) 2 j).comp (l2Embed e).toContinuousLinearMap)
  have hne : ∀ r, j ≠ e r := fun r he => hj ⟨r, he.symm⟩
  simpa [lp.evalCLM, l2Embed_single, lp.single_apply, Pi.single_eq_of_ne, hne] using h.tsum_eq.symm

section
open scoped InnerProductSpace lp
variable {I V : Type*} (L : I → V → V → Type*)

theorem fockVacuum_away (z : ℓ²(V, ℂ)) (i : I) : FockAway L i (fockVacuum L z) := by
  intro j hj
  apply l2Embed_apply_of_not_mem
  rintro ⟨r,hr⟩
  have he := congrArg (fun j : FockIndex L => j.1) hr
  change none = j.1 at he
  rw [hj] at he
  cases he

theorem fockVacuum_inner_starts (z : ℓ²(V, ℂ)) (i : I) (x : AtomicFockSpace L)
    (hx : FockStarts L i x) : inner ℂ (fockVacuum L z) x = 0 := by
  rw [lp.inner_eq_tsum]
  suffices h : ∀ j, inner ℂ (fockVacuum L z j) (x j) = 0 by simp only [h, tsum_zero]
  rintro ⟨j,r,p⟩
  cases p with
  | nil r => rw [hx _ (by simp), inner_zero_right]
  | cons k l r a j p hn =>
    rw [fockVacuum_away L z k _ rfl, inner_zero_left]

end

section
open scoped InnerProductSpace lp
variable {I V : Type*} (L : I → V → V → Type*)

theorem fockVacuum_inner (z : ℓ²(V, ℂ)) (x : AtomicFockSpace L) :
    inner ℂ (fockVacuum L z) x =
      ∑' r, inner ℂ (z r) (x (fockVacuumIndex L r)) := by
  rw [lp.inner_eq_tsum]
  have hs : Function.support (fun j => inner ℂ (fockVacuum L z j) (x j)) ⊆
      Set.range (fockVacuumIndex L) := by
    intro j hj
    by_contra hn
    exact hj (by
      change inner ℂ (l2Embed (fockVacuumIndex L) z j) (x j) = 0
      rw [l2Embed_apply_of_not_mem _ _ _ hn, inner_zero_left])
  rw [← (fockVacuumIndex L).injective.tsum_eq hs]
  congr 1
  funext r
  rw [show fockVacuum L z (fockVacuumIndex L r) = z r from l2Embed_apply _ _ _]

variable [DecidableEq I] {A : I → Type*} [∀ i, CStarAlgebra (A i)]
variable (π : ∀ i r, A i →⋆ₐ[ℂ]
  (ℓ²(ColumnIndex L i r, ℂ) →L[ℂ] ℓ²(ColumnIndex L i r, ℂ)))

theorem atomicFock_vacuum_coeff (i : I) (a : A i) (z : ℓ²(V, ℂ)) (r : V) :
    atomicFockRepresentation L π i a (fockVacuum L z) (fockVacuumIndex L r) =
      z r * π i r a (lp.single 2 none 1) none := by
  have h := atomicFock_creation L π i a (fockVacuum L z) (fockVacuum_away L z i)
    ⟨⟨none, r, .nil r⟩, by simp⟩ none
  simp only [fockJoin, fockVacuum_apply_nil] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  rfl

theorem atomicFock_vacuum_inner (i : I) (a : A i) (z : ℓ²(V, ℂ)) :
    inner ℂ (fockVacuum L z) (atomicFockRepresentation L π i a (fockVacuum L z)) =
      ∑' r, star (z r) * (z r * π i r a (lp.single 2 none 1) none) := by
  rw [fockVacuum_inner]
  congr 1
  funext r
  rw [atomicFock_vacuum_coeff, RCLike.inner_apply']
  rfl

end

open scoped InnerProductSpace ComplexOrder
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

section
open scoped InnerProductSpace lp

variable {I V : Type*} {A : I → Type*} [∀ i, CStarAlgebra (A i)]
  [∀ i, PartialOrder (A i)] [∀ i, StarOrderedRing (A i)]
variable (d : ∀ i, AtomicTraceData (A i) V)

variable [DecidableEq I]

theorem atomicLeft_centered (i : I) (a : A i)
    (ha : ∀ r, (d i).trace (((d i).atom r).1 * a * ((d i).atom r).1) = 0)
    (x : AtomicHilbertSpace d) (hx : FockAway (AtomicLetters d) i x) :
    FockStarts (AtomicLetters d) i (atomicLeft d i a x) := by
  apply atomicFock_creation_starts (AtomicLetters d) (atomicColumnReps d) i a _ x hx
  intro r
  rw [atomicColumnReps, indexedColumnRepresentation_vacuum, ha r, mul_zero]

end

section
open scoped InnerProductSpace lp
variable {I V : Type*} {A : I → Type*} [∀ i, CStarAlgebra (A i)]
  [∀ i, PartialOrder (A i)] [∀ i, StarOrderedRing (A i)]
variable (d : ∀ i, AtomicTraceData (A i) V)

variable [DecidableEq I]

theorem atomicLeft_vacuum_trace (k i : I)
    (hw : ∀ r, ((d k).trace ((d k).atom r).1).re =
      ((d i).trace ((d i).atom r).1).re) (a : A i) :
    inner ℂ (atomicVacuum d k) (atomicLeft d i a (atomicVacuum d k)) = (d i).trace a := by
  rw [atomicVacuum, atomicLeft, atomicFock_vacuum_inner]
  rw [← (trace_hasSum_atom_corners (d i).trace (d i).tracial (d i).atom
    (d i).orthogonal (d i).mass a).tsum_eq]
  apply tsum_congr
  intro r
  rw [atomicColumnReps, indexedColumnRepresentation_vacuum,
    atomicWeightVector_apply, hw r]
  have hne : (Real.sqrt (((d i).trace ((d i).atom r).1).re) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr ((d i).positive r)).ne'
  simp only [Complex.star_def, Complex.conj_ofReal]
  field_simp

end

section

variable {I B : Type*} [Ring B] [Algebra ℂ B]

theorem IsCenteredWord.head {K : I → Submodule ℂ B} {x : I × B} {w : List (I × B)}
    (h : IsCenteredWord K (x :: w)) : x.2 ∈ K x.1 := h.centered x (by simp)

variable (D : NonUnitalSubalgebra ℂ B) (F : I → NonUnitalSubalgebra ℂ B) (K : I → Submodule ℂ B)

def normalSpan : Submodule ℂ B :=
  Submodule.span ℂ {b | b ∈ D ∨ ∃ w, IsCenteredWord K w ∧ b = wordValue w}

theorem normalSpan_diagonal {d : B} (hd : d ∈ D) : d ∈ normalSpan D K :=
  Submodule.subset_span (Or.inl hd)

theorem normalSpan_word {w : List (I × B)} (hw : IsCenteredWord K w) :
    wordValue w ∈ normalSpan D K := Submodule.subset_span (Or.inr ⟨w, hw, rfl⟩)

variable {D F K}

theorem CenteredDecomposition.diagonal_word_mem (h : CenteredDecomposition D F K)
    {d : B} (hd : d ∈ D) {w : List (I × B)} (hw : IsCenteredWord K w) :
    d * wordValue w ∈ normalSpan D K := by
  cases w with
  | nil => simpa using normalSpan_diagonal D K hd
  | cons x w =>
    have hh := hw.modify_head (h.diagonal_mul x.1 d x.2 hd hw.head)
    simpa only [wordValue_cons, mul_assoc] using normalSpan_word D K hh

theorem CenteredDecomposition.factor_word_mem (h : CenteredDecomposition D F K)
    {i : I} {a : B} (ha : a ∈ F i) {w : List (I × B)} (hw : IsCenteredWord K w) :
    a * wordValue w ∈ normalSpan D K := by
  classical
  cases w with
  | nil =>
    rcases h.decompose i a ha with ⟨d, hd, c, hc, rfl⟩
    have hcw : IsCenteredWord K [(i,c)] :=
      ⟨by simpa, List.isChain_singleton _⟩
    have hh := (normalSpan D K).add_mem (normalSpan_diagonal D K hd)
      (normalSpan_word D K hcw)
    simpa using hh
  | cons x w =>
    by_cases hi : i = x.1
    · have hap : a * x.2 ∈ F x.1 := (F x.1).mul_mem (hi ▸ ha)
        (h.centered_le x.1 hw.head)
      rcases h.decompose x.1 (a * x.2) hap with ⟨d, hd, c, hc, he⟩
      rw [wordValue_cons, ← mul_assoc, he, add_mul]
      exact (normalSpan D K).add_mem (h.diagonal_word_mem hd hw.tail)
        (normalSpan_word D K (hw.modify_head hc))
    · rcases h.decompose i a ha with ⟨d, hd, c, hc, rfl⟩
      rw [add_mul]
      exact (normalSpan D K).add_mem (h.diagonal_word_mem hd hw)
        (normalSpan_word D K (hw.prepend hc hi))

theorem CenteredDecomposition.factor_stabilizes (h : CenteredDecomposition D F K)
    {i : I} {a : B} (ha : a ∈ F i) : a ∈ leftStabilizer (normalSpan D K) := by
  intro b hb
  induction hb using Submodule.span_induction with
  | mem b hb =>
    rcases hb with hb | ⟨w, hw, rfl⟩
    · have hab := (F i).mul_mem ha (h.diagonal_le i hb)
      simpa using h.factor_word_mem hab
        (show IsCenteredWord K [] from ⟨by simp, List.isChain_nil⟩)
    · exact h.factor_word_mem ha hw
  | zero => simp
  | add b c _ _ hb hc => simpa only [mul_add] using (normalSpan D K).add_mem hb hc
  | smul c b _ hb => simpa only [mul_smul_comm] using (normalSpan D K).smul_mem c hb

theorem CenteredDecomposition.adjoin_le_normalSpan (h : CenteredDecomposition D F K) :
    (Algebra.adjoin ℂ (⋃ i, (F i : Set B))).toSubmodule ≤ normalSpan D K := by
  have hs : Algebra.adjoin ℂ (⋃ i, (F i : Set B)) ≤ leftStabilizer (normalSpan D K) := by
    apply Algebra.adjoin_le
    intro a ha
    rcases Set.mem_iUnion.mp ha with ⟨i, hi⟩
    exact h.factor_stabilizes hi
  intro a ha
  have h1 := normalSpan_word D K
    (show IsCenteredWord K [] from ⟨by simp, List.isChain_nil⟩)
  simpa only [mul_one] using hs ha 1 h1

variable (φ : B →ₗ[ℂ] ℂ)
variable (hfree : ∀ w, IsCenteredWord K w → w ≠ [] → φ (wordValue w) = 0)

include hfree

theorem CenteredDecomposition.diagonal_word_zero (h : CenteredDecomposition D F K)
    {d : B} (hd : d ∈ D) {w : List (I × B)} (hw : IsCenteredWord K w) (hne : w ≠ []) :
    φ (d * wordValue w) = 0 := by
  cases w with
  | nil => exact (hne rfl).elim
  | cons x w =>
    have hh := hw.modify_head (h.diagonal_mul x.1 d x.2 hd hw.head)
    simpa only [wordValue_cons, mul_assoc] using hfree _ hh (by simp)

theorem CenteredDecomposition.factor_different_zero (h : CenteredDecomposition D F K)
    {i : I} {a : B} (ha : a ∈ F i) {x : I × B} {w : List (I × B)}
    (hw : IsCenteredWord K (x :: w)) (hi : i ≠ x.1) :
    φ (a * wordValue (x :: w)) = 0 := by
  rcases h.decompose i a ha with ⟨d, hd, c, hc, rfl⟩
  rw [add_mul, map_add, h.diagonal_word_zero φ hfree hd hw (by simp)]
  simpa only [zero_add, wordValue_cons] using hfree _ (hw.prepend hc hi) (by simp)

theorem CenteredDecomposition.factor_long_zero (h : CenteredDecomposition D F K)
    {i : I} {a : B} (ha : a ∈ F i) {w : List (I × B)}
    (hw : IsCenteredWord K w) (hlen : 2 ≤ w.length) : φ (a * wordValue w) = 0 := by
  classical
  cases w with
  | nil => simp at hlen
  | cons x w =>
    have hwne : w ≠ [] := by intro he; simp [he] at hlen
    by_cases hi : i = x.1
    · have hap : a * x.2 ∈ F x.1 := (F x.1).mul_mem (hi ▸ ha)
        (h.centered_le x.1 hw.head)
      rcases h.decompose x.1 (a * x.2) hap with ⟨d, hd, c, hc, he⟩
      rw [wordValue_cons, ← mul_assoc, he, add_mul, map_add,
        h.diagonal_word_zero φ hfree hd hw.tail hwne]
      simpa only [zero_add, wordValue_cons] using hfree _ (hw.modify_head hc) (by simp)
    · exact h.factor_different_zero φ hfree ha hw hi

omit hfree

variable [StarRing B]

omit [Algebra ℂ B] in
@[simp] theorem wordValue_starWord (w : List (I × B)) :
    wordValue (starWord w) = star (wordValue w) := by
  induction w with
  | nil => simp [starWord, wordValue]
  | cons x w ih =>
    simp only [starWord, List.reverse_cons, List.map_append,
      wordValue, List.map_append, List.prod_append,
      List.map_cons, List.prod_cons, List.map_nil, List.prod_nil, mul_one, star_mul] at *
    rw [ih]

omit [Algebra ℂ B] in
@[simp] theorem starWord_length (w : List (I × B)) : (starWord w).length = w.length := by
  simp [starWord]

variable (hKstar : ∀ i c, c ∈ K i → star c ∈ K i)

include hKstar in
theorem IsCenteredWord.starWord {w : List (I × B)} (hw : IsCenteredWord K w) :
    IsCenteredWord K (starWord w) := by
  constructor
  · intro x hx
    rcases List.mem_map.mp hx with ⟨y, hy, rfl⟩
    exact hKstar y.1 y.2 (hw.centered y (List.mem_reverse.mp hy))
  · apply (List.isChain_map _).mpr
    apply List.isChain_reverse.mpr
    exact hw.alternating.imp (fun _ _ hh => Ne.symm hh)

variable (hφstar : ∀ b, φ (star b) = star (φ b))
variable (hFstar : ∀ i a, a ∈ F i → star a ∈ F i)
variable (htr : ∀ i a b, a ∈ F i → b ∈ F i → φ (a * b) = φ (b * a))

include hfree hKstar hφstar hFstar

theorem CenteredDecomposition.factor_long_zero_right (h : CenteredDecomposition D F K)
    {i : I} {a : B} (ha : a ∈ F i) {w : List (I × B)}
    (hw : IsCenteredWord K w) (hlen : 2 ≤ w.length) : φ (wordValue w * a) = 0 := by
  have hh := h.factor_long_zero φ hfree (hFstar i a ha) (hw.starWord hKstar)
    (by simpa using hlen)
  rw [wordValue_starWord, ← star_mul, hφstar, star_eq_zero] at hh
  exact hh

include htr

theorem CenteredDecomposition.factor_word_trace (h : CenteredDecomposition D F K)
    {i : I} {a : B} (ha : a ∈ F i) {w : List (I × B)} (hw : IsCenteredWord K w) :
    φ (a * wordValue w) = φ (wordValue w * a) := by
  classical
  cases w with
  | nil => simp
  | cons x w =>
    cases w with
    | nil =>
      by_cases hi : i = x.1
      · simpa using htr i a x.2 ha (hi.symm ▸ h.centered_le x.1 hw.head)
      · have hl := h.factor_different_zero φ hfree ha hw hi
        have hs : IsCenteredWord K [(x.1, star x.2)] := hw.starWord hKstar
        have hr := h.factor_different_zero φ hfree (hFstar i a ha) hs hi
        simp only [wordValue_cons, wordValue_nil, mul_one] at hl hr ⊢
        rw [← star_mul, hφstar, star_eq_zero] at hr
        exact hl.trans hr.symm
    | cons y w =>
      have hl := h.factor_long_zero φ hfree ha hw (by simp)
      have hr := h.factor_long_zero_right φ hfree hKstar hφstar hFstar ha hw (by simp)
      exact hl.trans hr.symm

theorem CenteredDecomposition.factor_span_trace (h : CenteredDecomposition D F K)
    {i : I} {a : B} (ha : a ∈ F i) {b : B} (hb : b ∈ normalSpan D K) :
    φ (a * b) = φ (b * a) := by
  induction hb using Submodule.span_induction with
  | mem b hb =>
    rcases hb with hb | ⟨w, hw, rfl⟩
    · exact htr i a b ha (h.diagonal_le i hb)
    · exact h.factor_word_trace φ hfree hKstar hφstar hFstar htr ha hw
  | zero => simp
  | add b c _ _ hb hc => simp only [mul_add, add_mul, map_add, hb, hc]
  | smul c b _ hb => simp only [mul_smul_comm, smul_mul_assoc, map_smul, hb]

end

section

variable {V B : Type*} [Ring B] [Algebra ℂ B]

def projectionCorner (p : B) : NonUnitalSubalgebra ℂ B where
  carrier := {a | p * a = a ∧ a * p = a}
  zero_mem' := by simp
  add_mem' ha hb := ⟨by rw [mul_add, ha.1, hb.1], by rw [add_mul, ha.2, hb.2]⟩
  smul_mem' c a ha := ⟨by rw [mul_smul_comm, ha.1], by rw [smul_mul_assoc, ha.2]⟩
  mul_mem' ha hb := by
    constructor
    · rw [← mul_assoc, ha.1]
    · rw [mul_assoc, hb.2]

@[simp] theorem mem_projectionCorner {p a : B} :
    a ∈ projectionCorner p ↔ p * a = a ∧ a * p = a := Iff.rfl

variable (q : V → B)
variable (hq : ∀ r, q r * q r = q r)
variable (ho : ∀ r t, r ≠ t → q r * q t = 0)

include hq ho in
lemma atom_mem_finiteCorner [DecidableEq V] {s : Finset V} {r : V} (hr : r ∈ s) :
    q r ∈ projectionCorner (∑ t ∈ s, q t) := by
  constructor
  · rw [sum_mul_atom q hq ho, ite_eq_left hr]
  · rw [atom_mul_sum q hq ho, ite_eq_left hr]

variable (φ : B →ₗ[ℂ] ℂ)

def finiteFactorCorner (F : NonUnitalSubalgebra ℂ B) (s : Finset V) :
    NonUnitalSubalgebra ℂ B := F ⊓ projectionCorner (∑ r ∈ s, q r)

@[simp] theorem mem_atomicCenteredSubmodule (F : NonUnitalSubalgebra ℂ B) (a : B) :
    a ∈ atomicCenteredSubmodule q φ F ↔ a ∈ F ∧ ∀ r, φ (q r * a * q r) = 0 := by
  simp [atomicCenteredSubmodule]

end

variable {B : Type*} [NormedRing B] [NormedAlgebra ℂ B]

open Filter Topology
open scoped lp
variable {J V : Type*} [DecidableEq V]

theorem l2RootTruncation_norm (root : J → V) (s : Finset V) :
    ‖l2RootTruncation root s‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  rw [one_mul]
  apply lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0)
  intro j
  rw [l2RootTruncation_apply]
  split_ifs <;> simp

theorem l2RootTruncation_complement_norm (root : J → V) (s : Finset V) :
    ‖(1 : ℓ²(J, ℂ) →L[ℂ] ℓ²(J, ℂ)) - l2RootTruncation root s‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  rw [one_mul]
  apply lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0)
  intro j
  change ‖x j - l2RootTruncation root s x j‖ ≤ ‖x j‖
  rw [l2RootTruncation_apply]
  split_ifs <;> simp

variable [DecidableEq J]

theorem l2RootTruncation_single (root : J → V) (s : Finset V) (j : J) (z : ℂ) :
    l2RootTruncation root s (lp.single 2 j z) =
      if root j ∈ s then lp.single 2 j z else 0 := by
  ext k
  by_cases hk : j = k
  · subst k
    by_cases hs : root j ∈ s <;> simp [hs]
  · by_cases hs : root j ∈ s <;> simp [hs, lp.single_apply, Ne.symm hk]

theorem l2RootTruncation_strong (root : J → V) (x : ℓ²(J, ℂ)) :
    Tendsto (fun s : Finset V => l2RootTruncation root s x) atTop (𝓝 x) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hlim := lp.hasSum_single (by norm_num : (2 : ENNReal) ≠ ⊤) x
  have hlim' : Tendsto (fun t : Finset J => ∑ j ∈ t, lp.single 2 j (x j)) atTop (𝓝 x) := hlim
  obtain ⟨t, ht⟩ := Metric.tendsto_atTop.mp hlim' ε hε
  refine ⟨t.image root, ?_⟩
  intro s hs
  let y : ℓ²(J, ℂ) := ∑ j ∈ t, lp.single 2 j (x j)
  have hsy : l2RootTruncation root s y = y := by
    dsimp [y]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [l2RootTruncation_single, ite_eq_left (hs (Finset.mem_image_of_mem root hj))]
  have hid : (l2RootTruncation root s x - x) =
      -(((1 : ℓ²(J, ℂ) →L[ℂ] ℓ²(J, ℂ)) - l2RootTruncation root s) (x-y)) := by
    simp only [sub_apply, one_apply_eq_self, map_sub, hsy]
    abel
  rw [dist_eq_norm, hid, norm_neg]
  have hb := ((1 : ℓ²(J, ℂ) →L[ℂ] ℓ²(J, ℂ)) - l2RootTruncation root s).le_opNorm (x-y)
  have hh := l2RootTruncation_complement_norm root s
  calc
    _ ≤ ‖(1 : ℓ²(J, ℂ) →L[ℂ] ℓ²(J, ℂ)) - l2RootTruncation root s‖ * ‖x-y‖ := hb
    _ ≤ 1 * ‖x-y‖ := mul_le_mul_of_nonneg_right hh (norm_nonneg _)
    _ < ε := by simpa only [one_mul, ← dist_eq_norm, dist_comm] using ht t le_rfl

section
open scoped InnerProductSpace lp
variable {I V : Type*} {A : I → Type*} [∀ i, CStarAlgebra (A i)]
  [∀ i, PartialOrder (A i)] [∀ i, StarOrderedRing (A i)]
variable (d : ∀ i, AtomicTraceData (A i) V) [DecidableEq I]

theorem atomicCommonAtom_star (k : I) (r : V) :
    star (atomicCommonAtom d k r) = atomicCommonAtom d k r := by
  rw [atomicCommonAtom, ← map_star, ((d k).atom r).property.isSelfAdjoint.star_eq]

theorem atomicCommonAtom_state_ne (k : I) (r : V) :
    atomicState d k (atomicCommonAtom d k r) ≠ 0 := by
  rw [atomicState_apply, atomicCommonAtom, atomicLeft_vacuum_trace d k k (fun _ => rfl)]
  intro h
  have hh := (d k).positive r
  rw [h, Complex.zero_re] at hh
  exact (lt_irrefl 0) hh

variable (k : I) (hw : ∀ i r, ((d k).trace ((d k).atom r).1).re =
    ((d i).trace ((d i).atom r).1).re)
include hw

theorem atomicFactor_trace (i : I) (a b : AtomicOperators d)
    (ha : a ∈ atomicFactor d i) (hb : b ∈ atomicFactor d i) :
    atomicState d k (a*b) = atomicState d k (b*a) := by
  change ∃ a', atomicLeft d i a' = a at ha
  change ∃ b', atomicLeft d i b' = b at hb
  rcases ha with ⟨a,rfl⟩
  rcases hb with ⟨b,rfl⟩
  simp only [← map_mul, atomicState_apply, atomicLeft_vacuum_trace d k i (hw i)]
  exact (d i).tracial a b

variable [DecidableEq V]

theorem atomicCentered_starts (i : I) (T : AtomicOperators d)
    (hT : T ∈ atomicCenteredSubmodule (atomicCommonAtom d k) (atomicState d k)
      (atomicFactor d i)) (x : AtomicHilbertSpace d)
    (hx : FockAway (AtomicLetters d) i x) :
    FockStarts (AtomicLetters d) i (T x) := by
  rw [mem_atomicCenteredSubmodule] at hT
  rcases hT with ⟨hT, ha⟩
  change ∃ a, atomicLeft d i a = T at hT
  rcases hT with ⟨a, rfl⟩
  apply atomicLeft_centered d i a _ x hx
  intro r
  have hh := ha r
  simp only [atomicCommonAtom, ← atomicLeft_atoms d i k r, ← map_mul,
    atomicState_apply, atomicLeft_vacuum_trace d k i (hw i)] at hh
  exact hh

theorem atomicCenteredWord_starts (x : I × AtomicOperators d)
    (w : List (I × AtomicOperators d))
    (h : IsCenteredWord (fun i => atomicCenteredSubmodule (atomicCommonAtom d k)
      (atomicState d k) (atomicFactor d i)) (x :: w)) :
    FockStarts (AtomicLetters d) x.1 (wordValue (x :: w) (atomicVacuum d k)) := by
  induction w generalizing x with
  | nil =>
    simp only [wordValue_cons, wordValue_nil, mul_one]
    exact atomicCentered_starts d k hw x.1 x.2 h.head _
      (fockVacuum_away (AtomicLetters d) _ x.1)
  | cons y w ih =>
    rw [wordValue_cons, mul_apply_eq_comp]
    apply atomicCentered_starts d k hw x.1 x.2 h.head
    apply fockStarts_away (AtomicLetters d) _ _ (ih y h.tail)
    exact (List.isChain_cons_cons.mp h.alternating).1.symm

theorem atomicCenteredWord_zero (w : List (I × AtomicOperators d))
    (h : IsCenteredWord (fun i => atomicCenteredSubmodule (atomicCommonAtom d k)
      (atomicState d k) (atomicFactor d i)) w) (hn : w ≠ []) :
    atomicState d k (wordValue w) = 0 := by
  cases w with
  | nil => exact (hn rfl).elim
  | cons x w =>
    exact fockVacuum_inner_starts (AtomicLetters d) _ x.1 _
      (atomicCenteredWord_starts d k hw x w h)

end

section
open Filter Topology
open scoped InnerProductSpace lp
variable {I V : Type*} {A : I → Type*} [∀ i, CStarAlgebra (A i)]
  [∀ i, PartialOrder (A i)] [∀ i, StarOrderedRing (A i)]
variable (d : ∀ i, AtomicTraceData (A i) V) [DecidableEq I] [DecidableEq V]

theorem atomicCommonAtom_sum (k : I) (s : Finset V) :
    (∑ r ∈ s, atomicCommonAtom d k r) =
      l2RootTruncation (fun j : FockIndex (AtomicLetters d) => j.2.1) s := by
  ext x j
  simp only [sum_apply, lp.coeFn_sum, Finset.sum_apply, atomicCommonAtom_apply,
    l2RootTruncation_apply]
  exact Finset.sum_ite_eq' s j.2.1 (fun _ => x j)

def atomicFiniteAlgebra (k : I) (s : Finset V) : Subalgebra ℂ (AtomicOperators d) :=
  Algebra.adjoin ℂ (⋃ i, (finiteFactorCorner (atomicCommonAtom d k)
    (atomicFactor d i) s : Set (AtomicOperators d)))

theorem atomicFactor_stronglyApproximable (k i : I) (T : AtomicOperators d)
    (hT : T ∈ atomicFactor d i) :
    StronglyApproximable (atomicFiniteAlgebra d k) atTop T := by
  let P : Finset V → AtomicOperators d := fun s => ∑ r ∈ s, atomicCommonAtom d k r
  have hPF (s : Finset V) : P s ∈ atomicFactor d i :=
    (atomicFactor d i).sum_mem (fun r _ => atomicCommonAtom_mem d k i r)
  have hPP (s : Finset V) : P s * P s = P s := by
    change (∑ r ∈ s, atomicCommonAtom d k r) * _ = _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro r hr
    exact (atom_mul_sum (atomicCommonAtom d k) (atomicCommonAtom_idempotent d k)
      (atomicCommonAtom_orthogonal d k) s r).trans (ite_eq_left hr)
  have hPn (s : Finset V) : ‖P s‖ ≤ 1 := by
    dsimp [P]
    rw [atomicCommonAtom_sum]
    exact l2RootTruncation_norm _ s
  have hPlim (x : AtomicHilbertSpace d) :
      Tendsto (fun s => P s x) atTop (𝓝 x) := by
    simpa only [P, atomicCommonAtom_sum] using
      l2RootTruncation_strong (fun j : FockIndex (AtomicLetters d) => j.2.1) x
  refine ⟨fun s => P s * T * P s, ‖T‖, norm_nonneg _, ?_, ?_, ?_⟩
  · intro s
    apply Algebra.subset_adjoin
    apply Set.mem_iUnion.mpr
    refine ⟨i, (atomicFactor d i).mul_mem ((atomicFactor d i).mul_mem (hPF s) hT) (hPF s), ?_⟩
    constructor
    · change P s * (P s * T * P s) = _
      rw [← mul_assoc, ← mul_assoc, hPP]
    · change (P s * T * P s) * P s = _
      rw [mul_assoc (P s * T), hPP]
  · intro s
    calc
      ‖P s * T * P s‖ ≤ (‖P s‖ * ‖T‖) * ‖P s‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ (1 * ‖T‖) * 1 := mul_le_mul
        (mul_le_mul_of_nonneg_right (hPn s) (norm_nonneg _)) (hPn s)
        (norm_nonneg _) (by positivity)
      _ = ‖T‖ := by simp
  · intro x
    have hh := strong_apply_tendsto P (1 : AtomicOperators d) 1 hPn hPlim
      ((T.continuous.tendsto x).comp (hPlim x))
    exact hh

theorem atomicAlgebra_stronglyApproximable (k : I) {T : AtomicOperators d}
    (hT : T ∈ atomicAlgebra d) :
    StronglyApproximable (atomicFiniteAlgebra d k) atTop T := by
  have hh : atomicAlgebra d ≤ stronglyApproximableAlgebra (atomicFiniteAlgebra d k) atTop := by
    apply Algebra.adjoin_le
    rintro T hT
    rcases Set.mem_iUnion.mp hT with ⟨i,hi⟩
    exact atomicFactor_stronglyApproximable d k i T hi
  exact hh hT

end

section
open Filter Topology
open scoped InnerProductSpace lp
variable {I V : Type*} {A : I → Type*} [∀ i, CStarAlgebra (A i)]
  [∀ i, PartialOrder (A i)] [∀ i, StarOrderedRing (A i)]
variable (d : ∀ i, AtomicTraceData (A i) V) [DecidableEq I]

theorem atomicLeft_mem_algebra (i : I) (a : A i) : atomicLeft d i a ∈ atomicAlgebra d :=
  Algebra.subset_adjoin (Set.mem_iUnion.mpr ⟨i, a, rfl⟩)

end

open scoped InnerProductSpace

open scoped InnerProductSpace

open scoped InnerProductSpace

open scoped CStarAlgebra

open scoped ComplexOrder CStarAlgebra

open scoped CStarAlgebra

open scoped ComplexOrder CStarAlgebra

open scoped ComplexOrder CStarAlgebra

open scoped ComplexOrder CStarAlgebra

end NaimarkZFC

end

end OAI
end


