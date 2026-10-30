-- Prove2me | Definitions.Def_OAIQ115N010
-- name    : OAIQ115N010
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T00:49:21.51298+00:00
-- url     : https://prove2.me/theorems/6318f651-1917-4242-8966-960ff4ed5403
-- title:
--   Definitions bundle OAIQ115N010 of the split of OpenAI, A counterexample to Naimark's problem in ZFC
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.NaimarkZFC.main`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to Naimark's problem in ZFC*, OpenAI Math Release, September 24, 2026, result family 297, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 51 declarations of OpenAI's Lean: 13 definitions and 38 theorems. The definitions and types are `OAI.NaimarkZFC.AtomicTraceData.pullback`, `OAI.NaimarkZFC.MatrixHNNCorner`, `OAI.NaimarkZFC.atomicDiagonal`, `OAI.NaimarkZFC.atomicEmbedding`, `OAI.NaimarkZFC.atomicExpectation`, `OAI.NaimarkZFC.atomicKernel`, `OAI.NaimarkZFC.atomicTrace`, `OAI.NaimarkZFC.compressionIntoFactor`, `OAI.NaimarkZFC.factorExpectation`, `OAI.NaimarkZFC.matrixAtomicTraceData`, `OAI.NaimarkZFC.matrixCornerBase`, `OAI.NaimarkZFC.matrixCornerProjection`, `OAI.NaimarkZFC.matrixSingleHom`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Naimark_Amalgamation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/Amalgamation.lean), [`Naimark_Peaking`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/Peaking.lean).
--
--   **Imports.** It imports the bundles `OAIQ115N007` and `OAIQ115N008` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ115N012` and `OAIQ115N013`.
-- source:
--   OpenAI, A counterexample to Naimark's problem in ZFC, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 297; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-counterexample-to-Naimarks-problem-in-ZFC-September-24-2026/naimark-counterexample-zfc.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ115N007
import Definitions.Def_OAIQ115N008

section
-- module Solutions.OAIQ115_Naimark.Naimark_Amalgamation
attribute [-instance] _root_.OAI.NaimarkZFC.CStarCompletion.instCStarAlgebraCompletionOfCStarRingOfStarModuleComplex_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instNormedAlgebraComplexCompletion_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instStarCompletion_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instStarRingCompletion_solutions _root_.OAI.NaimarkZFC.constructionIndex_nonempty _root_.OAI.NaimarkZFC.retainedOrdinalAlgebra_cstar _root_.OAI.NaimarkZFC.hnnGeneratedCStar _root_.OAI.NaimarkZFC.omittedAlgebra_cstar
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

open scoped InnerProductSpace lp
variable {A V : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

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

open scoped InnerProductSpace lp
variable {V J : Type*}

open scoped InnerProductSpace ComplexOrder
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

section

variable {I B : Type*} [Ring B] [Algebra ℂ B]

variable (D : NonUnitalSubalgebra ℂ B) (F : I → NonUnitalSubalgebra ℂ B) (K : I → Submodule ℂ B)

variable {D F K}

variable (φ : B →ₗ[ℂ] ℂ)
variable (hfree : ∀ w, IsCenteredWord K w → w ≠ [] → φ (wordValue w) = 0)

include hfree

omit hfree

variable [StarRing B]

variable (hKstar : ∀ i c, c ∈ K i → star c ∈ K i)

variable (hφstar : ∀ b, φ (star b) = star (φ b))
variable (hFstar : ∀ i a, a ∈ F i → star a ∈ F i)
variable (htr : ∀ i a b, a ∈ F i → b ∈ F i → φ (a * b) = φ (b * a))

include hfree hKstar hφstar hFstar

include htr

theorem CenteredDecomposition.adjoin_trace (h : CenteredDecomposition D F K)
    {a b : B} (ha : a ∈ Algebra.adjoin ℂ (⋃ i, (F i : Set B)))
    (hb : b ∈ Algebra.adjoin ℂ (⋃ i, (F i : Set B))) : φ (a * b) = φ (b * a) := by
  induction ha using Algebra.adjoin_induction generalizing b with
  | mem a ha =>
    rcases Set.mem_iUnion.mp ha with ⟨i, hi⟩
    exact h.factor_span_trace φ hfree hKstar hφstar hFstar htr hi
      (h.adjoin_le_normalSpan hb)
  | algebraMap c => rw [Algebra.commutes]
  | add a c _ _ ha hc => simp only [add_mul, mul_add, map_add, ha hb, hc hb]
  | mul a c ha hc hia hic =>
    calc
      φ ((a * c) * b) = φ (a * (c * b)) := by rw [mul_assoc]
      _ = φ ((c * b) * a) := hia ((Algebra.adjoin ℂ _).mul_mem hc hb)
      _ = φ (c * (b * a)) := by rw [mul_assoc]
      _ = φ ((b * a) * c) := hic ((Algebra.adjoin ℂ _).mul_mem hb ha)
      _ = φ (b * (a * c)) := by rw [mul_assoc]

end

section

variable {V B : Type*} [Ring B] [Algebra ℂ B]

variable (q : V → B)
variable (hq : ∀ r, q r * q r = q r)
variable (ho : ∀ r t, r ≠ t → q r * q t = 0)

include hq ho in
theorem finiteAtomicDiagonal_le_corner [DecidableEq V] (s : Finset V) :
    finiteAtomicDiagonal q hq ho s ≤ projectionCorner (∑ t ∈ s, q t) := by
  change finiteAtomicSpan q s ≤ (projectionCorner (∑ t ∈ s, q t)).toSubmodule
  apply Submodule.span_le.mpr
  rintro a ⟨r, hr, rfl⟩
  exact atom_mem_finiteCorner q hq ho hr

variable (φ : B →ₗ[ℂ] ℂ)

include hq ho in
theorem finiteCorner_outside [DecidableEq V] {s : Finset V} {a : B}
    (ha : a ∈ projectionCorner (∑ t ∈ s, q t)) {r : V} (hr : r ∉ s) :
    q r * a = 0 := by
  rw [← ha.1, ← mul_assoc, atom_mul_sum q hq ho, ite_eq_right hr, zero_mul]

include hq ho in
theorem finiteAtomExpectation_centered [DecidableEq V]
    (hφq : ∀ r, φ (q r) ≠ 0) {s : Finset V} {a : B}
    (ha : a ∈ projectionCorner (∑ t ∈ s, q t)) (r : V) :
    φ (q r * (a - finiteAtomExpectation q φ s a) * q r) = 0 := by
  rw [mul_sub, sub_mul, map_sub, finiteAtomExpectation_atom q hq ho]
  by_cases hr : r ∈ s
  · rw [ite_eq_left hr, map_smul, smul_eq_mul, div_mul_cancel₀ _ (hφq r), sub_self]
  · rw [ite_eq_right hr, map_zero, finiteCorner_outside q hq ho ha hr, zero_mul, map_zero,
      sub_self]

include hq ho in
theorem finiteDiagonal_le_factorCorner [DecidableEq V]
    (F : NonUnitalSubalgebra ℂ B) (hF : ∀ r, q r ∈ F) (s : Finset V) :
    finiteAtomicDiagonal q hq ho s ≤ finiteFactorCorner q F s := by
  intro a ha
  constructor
  · have hh : finiteAtomicSpan q s ≤ F.toSubmodule := by
      apply Submodule.span_le.mpr
      rintro b ⟨r, _, rfl⟩
      exact hF r
    exact hh ha
  · exact finiteAtomicDiagonal_le_corner q hq ho s ha

include hq ho in
theorem finiteFactorCorner_decompose [DecidableEq V]
    (F : NonUnitalSubalgebra ℂ B) (hF : ∀ r, q r ∈ F)
    (hφq : ∀ r, φ (q r) ≠ 0) {s : Finset V} {a : B}
    (ha : a ∈ finiteFactorCorner q F s) :
    ∃ d ∈ finiteAtomicDiagonal q hq ho s,
      ∃ c ∈ atomicCenteredSubmodule q φ (finiteFactorCorner q F s), a = d + c := by
  let b := finiteAtomExpectation q φ s a
  have hb : b ∈ finiteAtomicDiagonal q hq ho s := finiteAtomExpectation_mem q hq ho φ s a
  have hbF := finiteDiagonal_le_factorCorner q hq ho F hF s hb
  refine ⟨b, hb, a-b, ?_, by simp⟩
  rw [mem_atomicCenteredSubmodule]
  exact ⟨(finiteFactorCorner q F s).sub_mem ha hbF,
    finiteAtomExpectation_centered q hq ho φ hφq ha.2⟩

include hq ho in
theorem finiteDiagonal_mul_centered [DecidableEq V]
    (F : NonUnitalSubalgebra ℂ B) (hF : ∀ r, q r ∈ F)
    {s : Finset V} {d c : B} (hd : d ∈ finiteAtomicDiagonal q hq ho s)
    (hc : c ∈ atomicCenteredSubmodule q φ (finiteFactorCorner q F s)) :
    d * c ∈ atomicCenteredSubmodule q φ (finiteFactorCorner q F s) := by
  rw [mem_atomicCenteredSubmodule] at hc ⊢
  refine ⟨(finiteFactorCorner q F s).mul_mem
    (finiteDiagonal_le_factorCorner q hq ho F hF s hd) hc.1, ?_⟩
  intro r
  obtain ⟨z, hz, _⟩ := finiteAtomicDiagonal_eigen q hq ho hd r
  rw [← mul_assoc (q r) d c, hz, smul_mul_assoc, smul_mul_assoc, map_smul, hc.2 r, smul_zero]

variable [StarRing B]
variable (hqstar : ∀ r, star (q r) = q r)
variable (hφstar : ∀ a, φ (star a) = star (φ a))

include hqstar in
theorem finiteFactorCorner_star (F : NonUnitalSubalgebra ℂ B)
    (hFs : ∀ a, a ∈ F → star a ∈ F) {s : Finset V} {a : B}
    (ha : a ∈ finiteFactorCorner q F s) : star a ∈ finiteFactorCorner q F s := by
  refine ⟨hFs a ha.1, ?_, ?_⟩
  · have hh := congrArg star ha.2.2
    simpa only [star_mul, star_sum, hqstar] using hh
  · have hh := congrArg star ha.2.1
    simpa only [star_mul, star_sum, hqstar] using hh

include hqstar hφstar in
theorem atomicCenteredSubmodule_star (F : NonUnitalSubalgebra ℂ B)
    (hFs : ∀ a, a ∈ F → star a ∈ F) {a : B}
    (ha : a ∈ atomicCenteredSubmodule q φ F) :
    star a ∈ atomicCenteredSubmodule q φ F := by
  rw [mem_atomicCenteredSubmodule] at ha ⊢
  refine ⟨hFs a ha.1, ?_⟩
  intro r
  have hh := congrArg star (ha.2 r)
  rw [star_zero, ← hφstar, star_mul, star_mul, hqstar] at hh
  simpa only [mul_assoc] using hh

end

section
variable {V I B : Type*} [Ring B] [Algebra ℂ B] [DecidableEq V]
variable (q : V → B) (hq : ∀ r, q r * q r = q r)
  (ho : ∀ r t, r ≠ t → q r * q t = 0)
  (φ : B →ₗ[ℂ] ℂ) (hφq : ∀ r, φ (q r) ≠ 0)
  (F : I → NonUnitalSubalgebra ℂ B) (hF : ∀ i r, q r ∈ F i)

include hφq hF

theorem finiteCornerCenteredDecomposition (s : Finset V) :
    CenteredDecomposition (finiteAtomicDiagonal q hq ho s)
      (fun i => finiteFactorCorner q (F i) s)
      (fun i => atomicCenteredSubmodule q φ (finiteFactorCorner q (F i) s)) where
  diagonal_le i := finiteDiagonal_le_factorCorner q hq ho (F i) (hF i) s
  centered_le _ _ ha := ha.1
  decompose i _ ha := finiteFactorCorner_decompose q hq ho φ (F i) (hF i) hφq ha
  diagonal_mul i _ _ hd hc := finiteDiagonal_mul_centered q hq ho φ (F i) (hF i) hd hc

include hq ho hφq hF

theorem finiteCorner_adjoin_trace [StarRing B]
    (hqstar : ∀ r, star (q r) = q r)
    (hφstar : ∀ a, φ (star a) = star (φ a))
    (hFstar : ∀ i a, a ∈ F i → star a ∈ F i)
    (htr : ∀ i a b, a ∈ F i → b ∈ F i → φ (a*b) = φ (b*a))
    (hfree : ∀ w, IsCenteredWord (fun i => atomicCenteredSubmodule q φ (F i)) w →
      w ≠ [] → φ (wordValue w) = 0)
    (s : Finset V) {a b : B}
    (ha : a ∈ Algebra.adjoin ℂ (⋃ i, (finiteFactorCorner q (F i) s : Set B)))
    (hb : b ∈ Algebra.adjoin ℂ (⋃ i, (finiteFactorCorner q (F i) s : Set B))) :
    φ (a*b) = φ (b*a) := by
  let h := finiteCornerCenteredDecomposition q hq ho φ hφq F hF s
  apply h.adjoin_trace φ _ _ hφstar _ _ ha hb
  · intro w hw hn
    apply hfree w ⟨?_, hw.alternating⟩ hn
    intro x hx
    have hh := hw.centered x hx
    rw [mem_atomicCenteredSubmodule] at hh ⊢
    exact ⟨hh.1.1, hh.2⟩
  · intro i c hc
    exact atomicCenteredSubmodule_star q φ hqstar hφstar _
      (fun a ha => finiteFactorCorner_star q hqstar (F i) (hFstar i) ha) hc
  · intro i a ha
    exact finiteFactorCorner_star q hqstar (F i) (hFstar i) ha
  · intro i a b ha hb
    exact htr i a b ha.1 hb.1

end

variable {B : Type*} [NormedRing B] [NormedAlgebra ℂ B]

open Filter Topology
open scoped lp
variable {J V : Type*} [DecidableEq V]

variable [DecidableEq J]

section
open scoped InnerProductSpace lp
variable {I V : Type*} {A : I → Type*} [∀ i, CStarAlgebra (A i)]
  [∀ i, PartialOrder (A i)] [∀ i, StarOrderedRing (A i)]
variable (d : ∀ i, AtomicTraceData (A i) V) [DecidableEq I]

variable (k : I) (hw : ∀ i r, ((d k).trace ((d k).atom r).1).re =
    ((d i).trace ((d i).atom r).1).re)
include hw

variable [DecidableEq V]

theorem atomicFiniteCorner_trace (s : Finset V) {a b : AtomicOperators d}
    (ha : a ∈ Algebra.adjoin ℂ (⋃ i, (finiteFactorCorner (atomicCommonAtom d k)
      (atomicFactor d i) s : Set (AtomicOperators d))))
    (hb : b ∈ Algebra.adjoin ℂ (⋃ i, (finiteFactorCorner (atomicCommonAtom d k)
      (atomicFactor d i) s : Set (AtomicOperators d)))) :
    atomicState d k (a*b) = atomicState d k (b*a) := by
  exact finiteCorner_adjoin_trace (atomicCommonAtom d k)
    (atomicCommonAtom_idempotent d k) (atomicCommonAtom_orthogonal d k)
    (atomicState d k) (atomicCommonAtom_state_ne d k)
    (atomicFactor d) (atomicCommonAtom_mem d k) (atomicCommonAtom_star d k)
    (operatorVectorFunctional_star (atomicVacuum d k)) (atomicFactor_star d)
    (atomicFactor_trace d k hw) (atomicCenteredWord_zero d k hw) s ha hb

end

section
open Filter Topology
open scoped InnerProductSpace lp
variable {I V : Type*} {A : I → Type*} [∀ i, CStarAlgebra (A i)]
  [∀ i, PartialOrder (A i)] [∀ i, StarOrderedRing (A i)]
variable (d : ∀ i, AtomicTraceData (A i) V) [DecidableEq I] [DecidableEq V]

theorem atomicAlgebra_trace (k : I)
    (hw : ∀ i r, ((d k).trace ((d k).atom r).1).re = ((d i).trace ((d i).atom r).1).re)
    {a b : AtomicOperators d} (ha : a ∈ atomicAlgebra d) (hb : b ∈ atomicAlgebra d) :
    atomicState d k (a*b) = atomicState d k (b*a) := by
  exact StronglyApproximable.vector_trace (atomicFiniteAlgebra d k) atTop (atomicVacuum d k)
    (fun s a b ha hb => atomicFiniteCorner_trace d k hw s ha hb)
    (atomicAlgebra_stronglyApproximable d k ha) (atomicAlgebra_stronglyApproximable d k hb)

end

section
open Filter Topology
open scoped InnerProductSpace lp
variable {I V : Type*} {A : I → Type*} [∀ i, CStarAlgebra (A i)]
  [∀ i, PartialOrder (A i)] [∀ i, StarOrderedRing (A i)]
variable (d : ∀ i, AtomicTraceData (A i) V) [DecidableEq I]

def atomicEmbedding (i : I) : A i →⋆ₐ[ℂ] AtomicCStar d :=
  (atomicLeft d i).codRestrict (atomicCStarAlgebra d) fun a =>
    subset_closure (atomicLeft_mem_algebra d i a)

theorem atomicCStar_trace (k : I)
    (hw : ∀ i r, ((d k).trace ((d k).atom r).1).re = ((d i).trace ((d i).atom r).1).re)
    (a b : AtomicCStar d) :
    operatorVectorFunctional (atomicVacuum d k) ((a : AtomicOperators d)*b) =
      operatorVectorFunctional (atomicVacuum d k) ((b : AtomicOperators d)*a) := by
  exact continuous_trace_closure (operatorVectorFunctional (atomicVacuum d k)) (atomicAlgebra d)
    (fun a ha b hb => atomicAlgebra_trace d k hw ha hb) a.2 b.2

end

open scoped InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable [CompleteSpace H]

variable {A : Type*} [CStarAlgebra A]

open scoped InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {A : Type*} [CStarAlgebra A]

open scoped InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

section
open scoped InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (B : StarSubalgebra ℂ (H →L[ℂ] H))
variable {I : Type*} {A : I → Type*} [∀ i, CStarAlgebra (A i)]
variable (ι : ∀ i, A i →⋆ₐ[ℂ] B) (ξ : H)

variable (D : NonUnitalSubalgebra ℂ B) (K : I → Submodule ℂ B)
variable (h : CenteredDecomposition D (factorAlgebra B ι) K)
variable (hfree : ∀ w, IsCenteredWord K w → w ≠ [] →
  restrictedVectorFunctional B ξ (wordValue w) = 0)
variable (htr : ∀ a b : B, restrictedVectorFunctional B ξ (a*b) =
  restrictedVectorFunctional B ξ (b*a))
include h hfree htr

theorem factorCompression_long_zero (i : I) {w : List (I × B)}
    (hw : IsCenteredWord K w) (hlen : 2 ≤ w.length) :
    factorCompression B ι ξ i (wordValue w) = 0 := by
  apply operatorCompression_zero_of_dense _ (cyclicOrbit (ambientFactor B ι i) ξ)
    (cyclicOrbit_dense (ambientFactor B ι i) ξ)
  intro a b
  change inner ℂ ((ambientFactor B ι i a) ξ)
    (((wordValue w : B) : H →L[ℂ] H) ((ambientFactor B ι i b) ξ)) = 0
  rw [factor_word_coefficient]
  rw [htr (star (ι i a) * wordValue w) (ι i b), ← mul_assoc]
  have hab : ι i b * star (ι i a) ∈ factorAlgebra B ι i := ⟨b * star a, by
    change ι i (b * star a) = _
    rw [map_mul, map_star]⟩
  exact h.factor_long_zero (restrictedVectorFunctional B ξ).toLinearMap hfree hab hw hlen

theorem factorCompression_different_zero (i j : I) (hij : i ≠ j) (x : B) (hx : x ∈ K j) :
    factorCompression B ι ξ i x = 0 := by
  apply operatorCompression_zero_of_dense _ (cyclicOrbit (ambientFactor B ι i) ξ)
    (cyclicOrbit_dense (ambientFactor B ι i) ξ)
  intro a b
  change inner ℂ ((ambientFactor B ι i a) ξ)
    ((x : H →L[ℂ] H) ((ambientFactor B ι i b) ξ)) = 0
  rw [factor_word_coefficient]
  rw [htr (star (ι i a) * x) (ι i b), ← mul_assoc]
  have hw : IsCenteredWord K [(j,x)] := by
    refine ⟨?_, List.isChain_singleton _⟩
    intro y hy
    cases List.mem_singleton.mp hy
    exact hx
  have hz := h.factor_different_zero (restrictedVectorFunctional B ξ).toLinearMap hfree
    (i := i) (show ι i b * star (ι i a) ∈ factorAlgebra B ι i from ⟨b * star a, by
      change ι i (b * star a) = _
      rw [map_mul, map_star]⟩) hw hij
  simpa using hz

theorem factorCompression_normal_mem (i : I) (z : B) (hz : z ∈ normalSpan D K) :
    factorCompression B ι ξ i z ∈
      (cyclicRepresentation (ambientFactor B ι i) ξ).range := by
  let W : Submodule ℂ B :=
    ((cyclicRepresentation (ambientFactor B ι i) ξ).range).toSubalgebra.toSubmodule.comap
      (factorCompression B ι ξ i).toLinearMap
  have hs : normalSpan D K ≤ W := by
    apply Submodule.span_le.mpr
    intro z hz
    rcases hz with hd | ⟨w, hw, rfl⟩
    · have hm : ∃ a : A i, ι i a = z := h.diagonal_le i hd
      obtain ⟨a,rfl⟩ := hm
      exact ⟨a, (factorCompression_factor B ι ξ i a).symm⟩
    · cases w with
      | nil =>
        refine ⟨1, ?_⟩
        change cyclicRepresentation (ambientFactor B ι i) ξ 1 =
          operatorCompression (cyclicSpan (ambientFactor B ι i) ξ) 1
        rw [map_one, operatorCompression_one]
      | cons x w =>
        cases w with
        | nil =>
          by_cases hi : i = x.1
          · have hm : ∃ a : A x.1, ι x.1 a = x.2 := h.centered_le x.1 hw.head
            obtain ⟨a,ha⟩ := hm
            subst i
            refine ⟨a, ?_⟩
            change cyclicRepresentation (ambientFactor B ι x.1) ξ a = _
            rw [wordValue_cons, wordValue_nil, mul_one, ← ha]
            exact (factorCompression_factor B ι ξ x.1 a).symm
          · refine ⟨0, ?_⟩
            simp only [map_zero, wordValue_cons, wordValue_nil, mul_one]
            exact (factorCompression_different_zero B ι ξ D K h hfree htr i x.1 hi x.2 hw.head).symm
        | cons y w =>
          refine ⟨0, ?_⟩
          rw [map_zero]
          exact (factorCompression_long_zero B ι ξ D K h hfree htr i hw (by simp)).symm
  exact hs hz

end

section
open scoped InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (B : StarSubalgebra ℂ (H →L[ℂ] H))
variable {I : Type*} {A : I → Type*} [∀ i, CStarAlgebra (A i)]
variable (ι : ∀ i, A i →⋆ₐ[ℂ] B) (ξ : H)

variable (D : NonUnitalSubalgebra ℂ B) (K : I → Submodule ℂ B)
variable (h : CenteredDecomposition D (factorAlgebra B ι) K)
variable (hfree : ∀ w, IsCenteredWord K w → w ≠ [] →
  restrictedVectorFunctional B ξ (wordValue w) = 0)
variable (htr : ∀ a b : B, restrictedVectorFunctional B ξ (a*b) =
  restrictedVectorFunctional B ξ (b*a))
variable (hdense : Dense (normalSpan D K : Set B))
variable (hsep : ∀ (i : I) (a : A i), (ambientFactor B ι i a) ξ = 0 → a = 0)
include h hfree htr hdense hsep

theorem factorCompression_mem (i : I) (b : B) :
    factorCompression B ι ξ i b ∈ (cyclicRepresentation (ambientFactor B ι i) ξ).range := by
  have hc : IsClosed {b : B | factorCompression B ι ξ i b ∈
      (cyclicRepresentation (ambientFactor B ι i) ξ).range} :=
    (faithfulRepresentation_range_closed _
      (cyclicRepresentation_injective _ ξ (hsep i))).preimage (factorCompression B ι ξ i).continuous
  exact closure_minimal
    (fun z hz => factorCompression_normal_mem B ι ξ D K h hfree htr i z hz) hc (hdense b)

def compressionIntoFactor (i : I) :
    B →L[ℂ] cyclicFactorAlgebra B ι ξ i where
  toFun b := ⟨factorCompression B ι ξ i b,
    factorCompression_mem B ι ξ D K h hfree htr hdense hsep i b⟩
  map_add' b c := Subtype.ext ((factorCompression B ι ξ i).map_add b c)
  map_smul' c b := Subtype.ext ((factorCompression B ι ξ i).map_smul c b)
  cont := (factorCompression B ι ξ i).continuous.subtype_mk _

def factorExpectation (i : I) : B →L[ℂ] A i :=
  (representationInverse (cyclicRepresentation (ambientFactor B ι i) ξ)
    (cyclicRepresentation_injective _ ξ (hsep i))).comp
      (compressionIntoFactor B ι ξ D K h hfree htr hdense hsep i)

@[simp] theorem factorExpectation_rep (i : I) (b : B) :
    cyclicRepresentation (ambientFactor B ι i) ξ
      (factorExpectation B ι ξ D K h hfree htr hdense hsep i b) =
      factorCompression B ι ξ i b :=
  representation_map_inverse (cyclicRepresentation (ambientFactor B ι i) ξ)
    (cyclicRepresentation_injective _ ξ (hsep i))
    (compressionIntoFactor B ι ξ D K h hfree htr hdense hsep i b)

@[simp] theorem factorExpectation_factor (i : I) (a : A i) :
    factorExpectation B ι ξ D K h hfree htr hdense hsep i (ι i a) = a := by
  apply cyclicRepresentation_injective _ ξ (hsep i)
  rw [factorExpectation_rep, factorCompression_factor]

@[simp] theorem factorExpectation_star (i : I) (b : B) :
    factorExpectation B ι ξ D K h hfree htr hdense hsep i (star b) =
      star (factorExpectation B ι ξ D K h hfree htr hdense hsep i b) := by
  apply cyclicRepresentation_injective _ ξ (hsep i)
  rw [map_star (cyclicRepresentation (ambientFactor B ι i) ξ), factorExpectation_rep, factorExpectation_rep, factorCompression_star]

end

open scoped CStarAlgebra

section
open scoped InnerProductSpace lp
variable {I V : Type*} {A : I → Type*} [∀ i, CStarAlgebra (A i)]
  [∀ i, PartialOrder (A i)] [∀ i, StarOrderedRing (A i)]
variable (d : ∀ i, AtomicTraceData (A i) V) [DecidableEq I] [DecidableEq V]

variable {Δ : Type*} [CStarAlgebra Δ]
variable (δ : ∀ i, Δ →⋆ₐ[ℂ] A i) (χ : Δ → V → ℂ)
variable (hatom : ∀ i x r, ((d i).atom r).1 * δ i x = χ x r • ((d i).atom r).1)
include hatom

theorem atomicEmbedding_diagonal_agree (i k : I) (x : Δ) :
    atomicEmbedding d i (δ i x) = atomicEmbedding d k (δ k x) :=
  Subtype.ext (atomicLeft_diagonal_agree d δ χ hatom i k x)

def atomicDiagonal (k : I) : NonUnitalSubalgebra ℂ (AtomicCStar d) :=
  ((atomicEmbedding d k).comp (δ k)).range.toSubalgebra.toNonUnitalSubalgebra

def atomicKernel (E : ∀ i, A i →L[ℂ] Δ) (i : I) : Submodule ℂ (AtomicCStar d) :=
  (LinearMap.ker (E i).toLinearMap).map (atomicEmbedding d i).toAlgHom.toLinearMap

variable (E : ∀ i, A i →L[ℂ] Δ)
variable (hfix : ∀ i x, E i (δ i x) = x)
variable (hleft : ∀ i x a, E i (δ i x * a) = x * E i a)

include hfix hleft

theorem atomicDiagonal_decomposition (k : I) :
    CenteredDecomposition (atomicDiagonal d δ k)
      (factorAlgebra (atomicCStarAlgebra d) (atomicEmbedding d)) (atomicKernel d E) where
  diagonal_le := by
    intro i x hx
    rcases hx with ⟨y,rfl⟩
    exact ⟨δ i y, atomicEmbedding_diagonal_agree d δ χ hatom i k y⟩
  centered_le := by
    intro i x hx
    rcases hx with ⟨a,_,rfl⟩
    exact ⟨a,rfl⟩
  decompose := by
    intro i x hx
    rcases hx with ⟨a,rfl⟩
    refine ⟨atomicEmbedding d i (δ i (E i a)), ?_,
      atomicEmbedding d i (a - δ i (E i a)), ?_, ?_⟩
    · exact ⟨E i a, (atomicEmbedding_diagonal_agree d δ χ hatom k i (E i a))⟩
    · refine ⟨a - δ i (E i a), ?_, rfl⟩
      change E i (a - δ i (E i a)) = 0
      rw [map_sub, hfix i, sub_self]
    · change atomicEmbedding d i a = atomicEmbedding d i (δ i (E i a)) +
        atomicEmbedding d i (a - δ i (E i a))
      rw [map_sub, add_sub_cancel]
  diagonal_mul := by
    intro i x c hx hc
    rcases hx with ⟨y,rfl⟩
    rcases hc with ⟨a,ha,rfl⟩
    refine ⟨δ i y * a, ?_, ?_⟩
    · change E i (δ i y * a) = 0
      change E i a = 0 at ha
      rw [hleft i, ha, mul_zero]
    · change atomicEmbedding d i (δ i y * a) =
        atomicEmbedding d k (δ k y) * atomicEmbedding d i a
      rw [map_mul, atomicEmbedding_diagonal_agree d δ χ hatom i k y]

end

section
open scoped InnerProductSpace lp
variable {I V : Type*} {A : I → Type*} [∀ i, CStarAlgebra (A i)]
  [∀ i, PartialOrder (A i)] [∀ i, StarOrderedRing (A i)]
variable (d : ∀ i, AtomicTraceData (A i) V) [DecidableEq I] [DecidableEq V]
variable {Δ : Type*} [CStarAlgebra Δ]
variable (δ : ∀ i, Δ →⋆ₐ[ℂ] A i) (χ : Δ → V → ℂ)
variable (hatom : ∀ i x r, ((d i).atom r).1 * δ i x = χ x r • ((d i).atom r).1)
variable (E : ∀ i, A i →L[ℂ] Δ)
variable (hfix : ∀ i x, E i (δ i x) = x)
variable (hleft : ∀ i x a, E i (δ i x * a) = x * E i a)

include hatom hfix hleft

theorem atomicNormalSpan_dense (k : I) :
    Dense (normalSpan (atomicDiagonal d δ k) (atomicKernel d E) : Set (AtomicCStar d)) := by
  let S : Subalgebra ℂ (AtomicCStar d) := Algebra.adjoin ℂ
    (⋃ i, (factorAlgebra (atomicCStarAlgebra d) (atomicEmbedding d) i : Set (AtomicCStar d)))
  have hlift (a : AtomicOperators d) (ha : a ∈ atomicAlgebra d) :
      (⟨a,subset_closure ha⟩ : AtomicCStar d) ∈ S := by
    induction ha using Algebra.adjoin_induction with
    | mem a ha =>
      rcases Set.mem_iUnion.mp ha with ⟨i,hi⟩
      rcases hi with ⟨b,rfl⟩
      exact Algebra.subset_adjoin (Set.mem_iUnion.mpr ⟨i,⟨b,rfl⟩⟩)
    | algebraMap c => exact S.algebraMap_mem c
    | add a b _ _ ha hb => exact S.add_mem ha hb
    | mul a b _ _ ha hb => exact S.mul_mem ha hb
  have hd : DenseRange (fun a : atomicAlgebra d =>
      (⟨a.1,subset_closure a.2⟩ : AtomicCStar d)) :=
    (denseRange_inclusion_iff subset_closure).mpr Set.Subset.rfl
  apply hd.mono
  rintro a ⟨a,rfl⟩
  exact (atomicDiagonal_decomposition d δ χ hatom E hfix hleft k).adjoin_le_normalSpan
    (hlift a.1 a.2)

omit hatom hfix hleft [DecidableEq V]

variable (hcenter : ∀ i a, E i a = 0 → ∀ r,
  (d i).trace (((d i).atom r).1 * a * ((d i).atom r).1) = 0)
include hcenter

theorem atomicKernel_starts (i : I) (T : AtomicCStar d) (hT : T ∈ atomicKernel d E i)
    (x : AtomicHilbertSpace d) (hx : FockAway (AtomicLetters d) i x) :
    FockStarts (AtomicLetters d) i ((T : AtomicOperators d) x) := by
  rcases hT with ⟨a,ha,rfl⟩
  exact atomicLeft_centered d i a (hcenter i a ha) x hx

theorem atomicKernelWord_starts (k : I) (x : I × AtomicCStar d)
    (w : List (I × AtomicCStar d)) (h : IsCenteredWord (atomicKernel d E) (x :: w)) :
    FockStarts (AtomicLetters d) x.1
      (((wordValue (x :: w) : AtomicCStar d) : AtomicOperators d) (atomicVacuum d k)) := by
  induction w generalizing x with
  | nil =>
    simp only [wordValue_cons, wordValue_nil, mul_one]
    exact atomicKernel_starts d E hcenter x.1 x.2 h.head _
      (fockVacuum_away (AtomicLetters d) _ x.1)
  | cons y w ih =>
    rw [wordValue_cons]
    change FockStarts (AtomicLetters d) x.1
      ((x.2 : AtomicOperators d) (((wordValue (y::w) : AtomicCStar d) : AtomicOperators d) _))
    apply atomicKernel_starts d E hcenter x.1 x.2 h.head
    apply fockStarts_away (AtomicLetters d) _ _ (ih y h.tail)
    exact (List.isChain_cons_cons.mp h.alternating).1.symm

theorem atomicKernelWord_zero (k : I) (w : List (I × AtomicCStar d))
    (h : IsCenteredWord (atomicKernel d E) w) (hne : w ≠ []) :
    restrictedVectorFunctional (atomicCStarAlgebra d) (atomicVacuum d k) (wordValue w) = 0 := by
  cases w with
  | nil => exact (hne rfl).elim
  | cons x w =>
    exact fockVacuum_inner_starts (AtomicLetters d) _ x.1 _
      (atomicKernelWord_starts d E hcenter k x w h)

omit hcenter in

theorem atomicFactor_separating (k : I)
    (hw : ∀ i r, ((d k).trace ((d k).atom r).1).re = ((d i).trace ((d i).atom r).1).re)
    (i : I) (a : A i) (ha : (atomicLeft d i a) (atomicVacuum d k) = 0) : a = 0 := by
  apply (d i).faithful a
  rw [← atomicLeft_vacuum_trace d k i (hw i)]
  change operatorVectorFunctional (atomicVacuum d k) (atomicLeft d i (star a*a)) = 0
  rw [map_mul, map_star, operatorVectorFunctional_star_mul, ha]
  simp

end

section
open scoped InnerProductSpace ComplexOrder CStarAlgebra lp
variable {I V : Type*} {A : I → Type*} [∀ i, CStarAlgebra (A i)]
  [∀ i, PartialOrder (A i)] [∀ i, StarOrderedRing (A i)]
variable (d : ∀ i, AtomicTraceData (A i) V) [DecidableEq I] [DecidableEq V]
variable {Δ : Type*} [CStarAlgebra Δ]

variable (c : AtomicAmalgamData (Δ := Δ) d)

def atomicExpectation (i : I) : AtomicCStar d →L[ℂ] A i :=
  factorExpectation (atomicCStarAlgebra d) (atomicEmbedding d) (atomicVacuum d c.base)
    (atomicDiagonal d c.diagonal c.base) (atomicKernel d c.expectation)
    (atomicDiagonal_decomposition d c.diagonal c.coordinate c.atom_mul c.expectation
      c.fix c.left c.base)
    (atomicKernelWord_zero d c.expectation c.centered c.base)
    (atomicCStar_trace d c.base c.weights)
    (atomicNormalSpan_dense d c.diagonal c.coordinate c.atom_mul c.expectation c.fix c.left c.base)
    (atomicFactor_separating d c.base c.weights) i

@[simp] theorem atomicExpectation_factor (i : I) (a : A i) :
    atomicExpectation d c i (atomicEmbedding d i a) = a :=
  factorExpectation_factor _ _ _ _ _ _ _ _ _ _ i a

@[simp] theorem atomicExpectation_one (i : I) : atomicExpectation d c i 1 = 1 := by
  rw [← map_one (atomicEmbedding d i), atomicExpectation_factor]

@[simp] theorem atomicExpectation_star (i : I) (b : AtomicCStar d) :
    atomicExpectation d c i (star b) = star (atomicExpectation d c i b) :=
  factorExpectation_star _ _ _ _ _ _ _ _ _ _ i b

def atomicTrace : AtomicCStar d →L[ℂ] ℂ :=
  restrictedVectorFunctional (atomicCStarAlgebra d) (atomicVacuum d c.base)

omit [DecidableEq V] in
@[simp] theorem atomicTrace_norm : ‖atomicTrace d c‖ = 1 :=
  restrictedVectorFunctional_norm _ _ (atomicVacuum_norm d c.base)

end

open scoped ComplexOrder CStarAlgebra
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {n : Type*} [Fintype n] [DecidableEq n]

open scoped CStarAlgebra
variable {A B n : Type*} [CStarAlgebra A] [CStarAlgebra B] [Fintype n] [DecidableEq n]

variable [PartialOrder A] [StarOrderedRing A]

open scoped ComplexOrder CStarAlgebra
variable {A V n : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Fintype n] [DecidableEq n]

variable [Nonempty n]

def matrixAtomicTraceData (τ : A →ₚ[ℂ] ℂ) (htr : IsTracialPositive τ)
    (hn : τ 1 = 1) (hf : ∀ a, τ (star a*a) = 0 → a = 0)
    (d : n → AtomicTraceData A V) (hd : ∀ i, (d i).trace = τ) :
    AtomicTraceData (CStarMatrix n n A) (n × V) where
  trace := normalizedMatrixTrace τ
  tracial := normalizedMatrixTrace_tracial τ htr
  normalized := normalizedMatrixTrace_one τ hn
  faithful := normalizedMatrixTrace_faithful τ hf
  atom v := ⟨matrixSingle v.1 v.1 ((d v.1).atom v.2).1,
    matrixSingle_projection _ _ ((d v.1).atom v.2).2⟩
  orthogonal v w h := by
    by_cases hvw : v.1 = w.1
    · rcases v with ⟨i,v⟩; rcases w with ⟨j,w⟩
      dsimp only at hvw
      subst j
      rw [matrixSingle_mul, (d i).orthogonal v w (by intro he; exact h (congrArg (Prod.mk i) he)),
        matrixSingle_zero]
    · exact matrixSingle_mul_of_ne _ _ _ _ _ _ hvw
  positive v := by
    rw [normalizedMatrixTrace_single, Complex.smul_re, smul_eq_mul]
    rw [← hd v.1]
    exact mul_pos (inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)) ((d v.1).positive _)
  mass := by
    let c : ℝ := (Fintype.card n : ℝ)⁻¹
    have hc : 0 < c := inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)
    let w : n × V → ℝ := fun v => c * ((d v.1).trace ((d v.1).atom v.2).1).re
    have hw (i : n) : HasSum (fun v : V => w (i,v)) c := by
      simpa only [w, (d i).normalized, Complex.one_re, mul_one] using (d i).mass.mul_left c
    have hsum : Summable w := (summable_prod_of_nonneg (fun v =>
      mul_nonneg hc.le ((d v.1).positive v.2).le)).mpr
      ⟨fun i => (hw i).summable, (hasSum_fintype _).summable⟩
    have hval : ∑' v, w v = 1 := by
      rw [hsum.tsum_prod' (fun i => (hw i).summable)]
      simp_rw [(hw _).tsum_eq]
      rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      dsimp only [c]
      exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
    convert hval ▸ hsum.hasSum using 1
    · funext v
      rw [normalizedMatrixTrace_single, ← hd v.1, Complex.smul_re, smul_eq_mul]
    · rw [normalizedMatrixTrace_one τ hn]
      rfl

@[simp] theorem matrixAtomicTraceData_atom (τ : A →ₚ[ℂ] ℂ) (htr : IsTracialPositive τ)
    (hn : τ 1 = 1) (hf : ∀ a, τ (star a*a) = 0 → a = 0)
    (d : n → AtomicTraceData A V) (hd : ∀ i, (d i).trace = τ) (v : n × V) :
    ((matrixAtomicTraceData τ htr hn hf d hd).atom v).1 =
      matrixSingle v.1 v.1 ((d v.1).atom v.2).1 := rfl

open scoped ComplexOrder CStarAlgebra
variable {B n V : Type*} [CStarAlgebra B] [Fintype n] [DecidableEq n] [Nonempty n]

variable {I : Type*}
  {A : I → Type*}
  [∀ i, CStarAlgebra (A i)]
  [∀ i, PartialOrder (A i)]
  [∀ i, StarOrderedRing (A i)]
  (χ : B → V → ℂ)

open scoped ComplexOrder CStarAlgebra
variable {A B V : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

@[simp] theorem positivePullback_apply (τ : A →ₚ[ℂ] ℂ) (φ : B →⋆ₐ[ℂ] A) (b : B) :
    positivePullback τ φ b = τ (φ b) := rfl

def AtomicTraceData.pullback (d : AtomicTraceData A V) (φ : B →⋆ₐ[ℂ] A)
    (hinj : Function.Injective φ) (p : V → B) (hp : ∀ v, φ (p v) = (d.atom v).1) :
    AtomicTraceData B V where
  trace := positivePullback d.trace φ
  tracial a b := by simp only [positivePullback_apply, map_mul]; exact d.tracial _ _
  normalized := by simpa only [positivePullback_apply, map_one] using d.normalized
  faithful b hb := by
    apply hinj
    rw [map_zero]
    apply d.faithful
    simpa only [positivePullback_apply, map_mul, map_star] using hb
  atom v := ⟨p v, by
    refine ⟨?_, ?_⟩
    · apply hinj
      simpa only [map_mul, hp] using (d.atom v).2.isIdempotentElem.eq
    · apply hinj
      simpa only [map_star, hp] using (d.atom v).2.isSelfAdjoint.star_eq⟩
  orthogonal v w h := by
    apply hinj
    simpa only [map_mul, hp, map_zero] using d.orthogonal v w h
  positive v := by simpa only [positivePullback_apply, hp] using d.positive v
  mass := by simpa only [positivePullback_apply, hp, map_one] using d.mass

@[simp] theorem AtomicTraceData.pullback_atom (d : AtomicTraceData A V) (φ : B →⋆ₐ[ℂ] A)
    (hinj : Function.Injective φ) (p : V → B) (hp : ∀ v, φ (p v) = (d.atom v).1) (v : V) :
    ((d.pullback φ hinj p hp).atom v).1 = p v := rfl

end NaimarkZFC

end

end OAI
end

section
-- module Solutions.OAIQ115_Naimark.Naimark_Peaking
attribute [-instance] _root_.OAI.NaimarkZFC.CStarCompletion.instCStarAlgebraCompletionOfCStarRingOfStarModuleComplex_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instNormedAlgebraComplexCompletion_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instStarCompletion_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instStarRingCompletion_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace NaimarkZFC

section
open scoped CStarAlgebra
variable {A B Z : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra Z]

@[simp] theorem matrixSingle_add {n : Type*} [Fintype n] [DecidableEq n]
    (i j : n) (a b : A) : matrixSingle i j (a+b) = matrixSingle i j a + matrixSingle i j b := by
  ext k l
  by_cases h : i = k ∧ j = l <;> simp [h]

variable (φ : CStarMatrix Bool Bool A →⋆ₐ[ℂ] Z)

def matrixCornerProjection : Z := φ (matrixSingle false false (1 : A))

theorem matrixCornerProjection_isProjection : IsStarProjection (matrixCornerProjection φ) :=
  (matrixSingle_projection false (1 : A) (IsStarProjection.one A)).map φ

abbrev MatrixHNNCorner := CStarCorner (matrixCornerProjection φ)
  (matrixCornerProjection_isProjection φ)

def matrixCornerBase : A →⋆ₐ[ℂ] MatrixHNNCorner φ where
  toFun a := ⟨φ (matrixSingle false false a), by
    constructor
    · change φ (matrixSingle false false (1 : A)) * φ (matrixSingle false false a) = _
      rw [← map_mul, matrixSingle_mul, one_mul]
    · change φ (matrixSingle false false a) * φ (matrixSingle false false (1 : A)) = _
      rw [← map_mul, matrixSingle_mul, mul_one]⟩
  map_zero' := Subtype.ext (by
    change φ (matrixSingle false false (0 : A)) = 0
    simp)
  map_one' := rfl
  map_add' a b := Subtype.ext (by
    change φ (matrixSingle false false (a+b)) = φ (matrixSingle false false a) + φ (matrixSingle false false b)
    simp)
  map_mul' a b := Subtype.ext (by
    change φ (matrixSingle false false (a*b)) = φ (matrixSingle false false a) * φ (matrixSingle false false b)
    rw [← map_mul, matrixSingle_mul])
  commutes' z := Subtype.ext (by
    change φ (matrixSingle false false (algebraMap ℂ A z)) = z • matrixCornerProjection φ
    rw [Algebra.algebraMap_eq_smul_one, matrixSingle_smul, map_smul]
    rfl)
  map_star' a := Subtype.ext (by
    change φ (matrixSingle false false (star a)) = star (φ (matrixSingle false false a))
    rw [← map_star, matrixSingle_star])

@[simp] theorem matrixCornerBase_coe (a : A) :
    (matrixCornerBase φ a : Z) = φ (matrixSingle false false a) := rfl

end

open scoped ComplexOrder CStarAlgebra
section
variable {A n : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Fintype n] [DecidableEq n]

def matrixSingleHom (i : n) : A →⋆ₙₐ[ℂ] CStarMatrix n n A where
  toFun := matrixSingle i i
  map_zero' := matrixSingle_zero i i
  map_add' a b := by ext k l; simp only [matrixSingle_apply, CStarMatrix.add_apply]; split_ifs <;> simp
  map_mul' a b := (matrixSingle_mul i i i a b).symm
  map_smul' z a := matrixSingle_smul i i a z
  map_star' a := (matrixSingle_star i i a).symm

end

open Filter Topology
open scoped ComplexOrder CStarAlgebra OnePoint

open Filter Topology
open scoped ComplexOrder

open Filter Topology

open Filter Topology
open scoped CStarAlgebra ComplexOrder OnePoint

open Filter Topology

open Filter Topology

open Filter Topology
open scoped OnePoint ComplexOrder CStarAlgebra

open Filter Topology
open scoped CStarAlgebra ComplexOrder OnePoint

open Filter Topology
open scoped CStarAlgebra ComplexOrder

open scoped InnerProductSpace ComplexStarModule CStarAlgebra ComplexOrder

open Filter Topology
open scoped InnerProductSpace ComplexStarModule CStarAlgebra ComplexOrder

open Filter Topology

open Filter Topology
open scoped CStarAlgebra ComplexOrder

open Filter Topology
open scoped CStarAlgebra ComplexOrder

open Filter Topology
open scoped InnerProductSpace ComplexOrder ComplexStarModule

open Filter Topology
open scoped CStarAlgebra ComplexOrder

open Filter Topology
open scoped CStarAlgebra ComplexOrder InnerProductSpace

open Filter Topology
open scoped CStarAlgebra ComplexOrder InnerProductSpace

open Filter Topology
open scoped CStarAlgebra ComplexOrder InnerProductSpace

open scoped CStarAlgebra ComplexOrder InnerProductSpace

open Filter Topology
open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder

end NaimarkZFC

end

end OAI
end


