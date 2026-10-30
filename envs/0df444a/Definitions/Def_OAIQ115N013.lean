-- Prove2me | Definitions.Def_OAIQ115N013
-- name    : OAIQ115N013
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T00:58:49.791853+00:00
-- url     : https://prove2.me/theorems/bda8cf48-d01b-476c-80d4-86d7ce4c55b7
-- title:
--   Definitions bundle OAIQ115N013 of the split of OpenAI, A counterexample to Naimark's problem in ZFC
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.NaimarkZFC.main`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to Naimark's problem in ZFC*, OpenAI Math Release, September 24, 2026, result family 297, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 30 declarations of OpenAI's Lean: 1 definition and 29 theorems. The definitions and types are `OAI.NaimarkZFC.jointFreeEquiv`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Naimark_Amalgamation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/Amalgamation.lean), [`Naimark_Extension`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/Extension.lean), [`Naimark_Peaking`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/Peaking.lean).
--
--   **Imports.** It imports the bundles `OAIQ115N010` and `OAIQ115N011` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ115N014` and `OAIQ115N015`.
-- source:
--   OpenAI, A counterexample to Naimark's problem in ZFC, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 297; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-counterexample-to-Naimarks-problem-in-ZFC-September-24-2026/naimark-counterexample-zfc.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ115N010
import Definitions.Def_OAIQ115N011

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

variable {B : Type*} [NormedRing B] [NormedAlgebra ℂ B]

open Filter Topology
open scoped lp
variable {J V : Type*} [DecidableEq V]

variable [DecidableEq J]

section
open Filter Topology
open scoped InnerProductSpace lp
variable {I V : Type*} {A : I → Type*} [∀ i, CStarAlgebra (A i)]
  [∀ i, PartialOrder (A i)] [∀ i, StarOrderedRing (A i)]
variable (d : ∀ i, AtomicTraceData (A i) V) [DecidableEq I]

theorem atomicEmbedding_injective (i : I) : Function.Injective (atomicEmbedding d i) := by
  intro a b h
  exact atomicLeft_injective d i (congrArg Subtype.val h)

theorem atomicCStar_faithful (k : I)
    (hw : ∀ i r, ((d k).trace ((d k).atom r).1).re = ((d i).trace ((d i).atom r).1).re)
    (a : AtomicCStar d)
    (ha : operatorVectorFunctional (atomicVacuum d k) (star (a : AtomicOperators d)*a) = 0) : a = 0 :=
  operatorVectorFunctional_faithful (atomicCStarAlgebra d) (atomicVacuum d k)
    (atomicCStar_cyclic d k) (atomicCStar_trace d k hw) a ha

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
variable (hdense : Dense (normalSpan D K : Set B))
variable (hsep : ∀ (i : I) (a : A i), (ambientFactor B ι i a) ξ = 0 → a = 0)
include h hfree htr hdense hsep

theorem factorExpectation_norm_le (i : I) (b : B) :
    ‖factorExpectation B ι ξ D K h hfree htr hdense hsep i b‖ ≤ ‖b‖ := by
  rw [← NonUnitalStarAlgHom.norm_map (cyclicRepresentation (ambientFactor B ι i) ξ)
    (cyclicRepresentation_injective _ ξ (hsep i)), factorExpectation_rep]
  exact factorCompression_norm_le B ι ξ i b

theorem factorExpectation_mul_factor (i : I) (b : B) (a : A i) :
    factorExpectation B ι ξ D K h hfree htr hdense hsep i (b * ι i a) =
      factorExpectation B ι ξ D K h hfree htr hdense hsep i b * a := by
  apply cyclicRepresentation_injective _ ξ (hsep i)
  rw [map_mul (cyclicRepresentation (ambientFactor B ι i) ξ), factorExpectation_rep, factorExpectation_rep, factorCompression_mul_factor]

theorem factorExpectation_factor_mul (i : I) (a : A i) (b : B) :
    factorExpectation B ι ξ D K h hfree htr hdense hsep i (ι i a * b) =
      a * factorExpectation B ι ξ D K h hfree htr hdense hsep i b := by
  apply cyclicRepresentation_injective _ ξ (hsep i)
  rw [map_mul (cyclicRepresentation (ambientFactor B ι i) ξ), factorExpectation_rep, factorExpectation_rep, factorCompression_factor_mul]

theorem factorExpectation_trace (i : I) (b : B) :
    restrictedVectorFunctional B ξ
      (ι i (factorExpectation B ι ξ D K h hfree htr hdense hsep i b)) =
      restrictedVectorFunctional B ξ b := by
  rw [← factorCompression_vector B ι ξ i, factorCompression_factor, factorExpectation_rep]
  exact factorCompression_vector B ι ξ i b

end

open scoped CStarAlgebra

section
open scoped InnerProductSpace ComplexOrder CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (B : StarSubalgebra ℂ (H →L[ℂ] H))
variable {I : Type*} {A : I → Type*} [∀ i, CStarAlgebra (A i)]
  [∀ i, PartialOrder (A i)] [∀ i, StarOrderedRing (A i)]
variable (ι : ∀ i, A i →⋆ₐ[ℂ] B) (ξ : H)
variable (D : NonUnitalSubalgebra ℂ B) (K : I → Submodule ℂ B)
variable (h : CenteredDecomposition D (factorAlgebra B ι) K)
variable (hfree : ∀ w, IsCenteredWord K w → w ≠ [] →
  restrictedVectorFunctional B ξ (wordValue w) = 0)
variable (htr : ∀ a b : B, restrictedVectorFunctional B ξ (a*b) =
  restrictedVectorFunctional B ξ (b*a))
variable (hdense : Dense (normalSpan D K : Set B))
variable (hsep : ∀ (i : I) (a : A i), (ambientFactor B ι i a) ξ = 0 → a = 0)

theorem factorExpectation_nonneg (i : I) (b : B) (hb : 0 ≤ b) :
    0 ≤ factorExpectation B ι ξ D K h hfree htr hdense hsep i b := by
  let π : A i →⋆ₐ[ℂ] ((cyclicSpan (ambientFactor B ι i) ξ) →L[ℂ]
    (cyclicSpan (ambientFactor B ι i) ξ)) := cyclicRepresentation (ambientFactor B ι i) ξ
  have hπ : Function.Injective π := cyclicRepresentation_injective _ ξ (hsep i)
  apply (faithfulStarHom_nonneg_iff (A := A i) (C := (cyclicSpan (ambientFactor B ι i) ξ →L[ℂ]
    cyclicSpan (ambientFactor B ι i) ξ)) π hπ _).mp
  rw [factorExpectation_rep]
  exact operatorCompression_nonneg _ _ hb

end

section
open scoped InnerProductSpace ComplexOrder CStarAlgebra lp
variable {I V : Type*} {A : I → Type*} [∀ i, CStarAlgebra (A i)]
  [∀ i, PartialOrder (A i)] [∀ i, StarOrderedRing (A i)]
variable (d : ∀ i, AtomicTraceData (A i) V) [DecidableEq I] [DecidableEq V]
variable {Δ : Type*} [CStarAlgebra Δ]

variable (c : AtomicAmalgamData (Δ := Δ) d)

theorem atomicExpectation_norm_le (i : I) (b : AtomicCStar d) :
    ‖atomicExpectation d c i b‖ ≤ ‖b‖ :=
  factorExpectation_norm_le _ _ _ _ _ _ _ _ _ _ i b

theorem atomicExpectation_nonneg (i : I) (b : AtomicCStar d) (hb : 0 ≤ b) :
    0 ≤ atomicExpectation d c i b :=
  factorExpectation_nonneg _ _ _ _ _ _ _ _ _ _ i b hb

theorem atomicExpectation_mul_factor (i : I) (b : AtomicCStar d) (a : A i) :
    atomicExpectation d c i (b * atomicEmbedding d i a) = atomicExpectation d c i b * a :=
  factorExpectation_mul_factor _ _ _ _ _ _ _ _ _ _ i b a

theorem atomicExpectation_factor_mul (i : I) (a : A i) (b : AtomicCStar d) :
    atomicExpectation d c i (atomicEmbedding d i a * b) = a * atomicExpectation d c i b :=
  factorExpectation_factor_mul _ _ _ _ _ _ _ _ _ _ i a b

omit [DecidableEq V] in
theorem atomicTrace_factor (i : I) (a : A i) :
    atomicTrace d c (atomicEmbedding d i a) = (d i).trace a :=
  atomicLeft_vacuum_trace d c.base i (c.weights i) a

omit [DecidableEq V] in
theorem atomicTrace_mul (a b : AtomicCStar d) :
    atomicTrace d c (a*b) = atomicTrace d c (b*a) := atomicCStar_trace d c.base c.weights a b

omit [DecidableEq V] in
theorem atomicTrace_faithful (a : AtomicCStar d)
    (ha : atomicTrace d c (star a*a) = 0) : a = 0 :=
  atomicCStar_faithful d c.base c.weights a ha

omit [DecidableEq V] in
theorem atomicTrace_square (a : AtomicCStar d) :
    (atomicTrace d c (star a*a)).im = 0 ∧ 0 ≤ (atomicTrace d c (star a*a)).re := by
  have hv : atomicTrace d c (star a*a) =
      (‖(a : AtomicOperators d) (atomicVacuum d c.base)‖ ^ 2 : ℝ) :=
    by
      change operatorVectorFunctional (atomicVacuum d c.base) (star (a : AtomicOperators d)*a) = _
      exact operatorVectorFunctional_star_mul (atomicVacuum d c.base) (a : AtomicOperators d)
  rw [hv]
  exact ⟨rfl, sq_nonneg _⟩

theorem atomicExpectation_trace (i : I) (b : AtomicCStar d) :
    (d i).trace (atomicExpectation d c i b) = atomicTrace d c b := by
  rw [← atomicTrace_factor d c i]
  exact factorExpectation_trace _ _ _ _ _ _ _ _ _ _ i b

theorem atomicExpectation_faithful (i : I) (b : AtomicCStar d)
    (hb : atomicExpectation d c i (star b*b) = 0) : b = 0 := by
  apply atomicTrace_faithful d c
  rw [← atomicExpectation_trace d c i, hb, map_zero]

end

open scoped ComplexOrder CStarAlgebra

open scoped CStarAlgebra

open scoped ComplexOrder CStarAlgebra

open scoped ComplexOrder CStarAlgebra

open scoped ComplexOrder CStarAlgebra

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

variable (φ : CStarMatrix Bool Bool A →⋆ₐ[ℂ] Z)

theorem matrixCornerBase_injective (hφ : Function.Injective φ) :
    Function.Injective (matrixCornerBase φ) := by
  intro a b hab
  have h := hφ (congrArg Subtype.val hab)
  have h' := congrArg (fun M : CStarMatrix Bool Bool A => M false false) h
  simpa only [matrixSingle_apply, and_self, ite_true, if_true] using h'

end

open scoped ComplexOrder CStarAlgebra

open Filter Topology
open scoped ComplexOrder CStarAlgebra OnePoint

section
variable {C : Type*} [CStarAlgebra C]

variable {I V : Type*} (L : I → V → V → Type*) [DecidableEq I]

theorem fockStartProjection_isProjection (i : I) : IsStarProjection (fockStartProjection L i) := by
  constructor
  · apply ContinuousLinearMap.ext
    intro x
    ext j
    simp only [mul_apply_eq_comp, fockStartProjection_apply]
    split_ifs <;> rfl
  · exact fockStartProjection_star L i

end

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
section
variable {A C : Type*} [CStarAlgebra A] [CStarAlgebra C]
  [PartialOrder A] [StarOrderedRing A]

variable (e : A) (he : IsStarProjection e)

omit [PartialOrder A] [StarOrderedRing A] in

theorem cornerCompression_norm (a : A) : ‖cornerCompression e he a‖ ≤ ‖a‖ := by
  change ‖e*a*e‖ ≤ ‖a‖
  calc
    _ ≤ (‖e‖*‖a‖)*‖e‖ := (norm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (1*‖a‖)*1 := mul_le_mul
      (mul_le_mul_of_nonneg_right (he.norm_le e) (norm_nonneg _)) (he.norm_le e)
      (norm_nonneg _) (by positivity)
    _ = ‖a‖ := by ring

end

end NaimarkZFC

end

end OAI
end

section
-- module Solutions.OAIQ115_Naimark.Naimark_Extension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace NaimarkZFC

open scoped CStarAlgebra ComplexOrder OnePoint

open Topology

open Topology

open Topology

open Topology
open scoped CStarAlgebra ComplexOrder

section
variable {I R : Type*} [Ring R] [Algebra ℂ R]

theorem CenteredDecomposition.moments_agree
    {D : NonUnitalSubalgebra ℂ R} {X : I → NonUnitalSubalgebra ℂ R}
    {K : I → Submodule ℂ R} (h : CenteredDecomposition D X K)
    (f g : R →ₗ[ℂ] ℂ) (hD : ∀ d ∈ D, f d = g d)
    (hf : ∀ w, IsCenteredWord K w → w ≠ [] → f (wordValue w) = 0)
    (hg : ∀ w, IsCenteredWord K w → w ≠ [] → g (wordValue w) = 0)
    (h1 : f 1 = g 1) {r : R}
    (hr : r ∈ Algebra.adjoin ℂ (⋃ i, (X i : Set R))) : f r = g r := by
  have hn := h.adjoin_le_normalSpan hr
  clear hr
  induction hn using Submodule.span_induction with
  | mem r hr =>
    rcases hr with hr | ⟨w,hw,rfl⟩
    · exact hD r hr
    · by_cases he : w = []
      · simpa [he] using h1
      · rw [hf w hw he,hg w hw he]
  | zero => simp
  | add a b _ _ ha hb => simp only [map_add,ha,hb]
  | smul c a _ ha => simp only [map_smul,ha]

variable {A B C : Type*} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B]
  [Ring C] [Algebra ℂ C] (V : I → Type*) [∀ i, Ring (V i)] [∀ i, Algebra ℂ (V i)]
  (inc : ∀ i, A →ₐ[ℂ] V i) (E : ∀ i, V i →ₗ[ℂ] A)
  (φ : ∀ i, V i →ₐ[ℂ] B) (ψ : ∀ i, V i →ₐ[ℂ] C)
  (b : A →ₐ[ℂ] B) (c : A →ₐ[ℂ] C)

theorem paired_centered_decomposition
    (hb : ∀ i, (φ i).comp (inc i) = b) (hc : ∀ i, (ψ i).comp (inc i) = c)
    (hfix : ∀ i a, E i (inc i a) = a)
    (hmod : ∀ i a x, E i (inc i a*x) = a*E i x) :
    CenteredDecomposition (pairedDiagonal b c) (pairedFactors V φ ψ)
      (pairedCenters V E φ ψ) := by
  have hp (i : I) (a : A) : ((φ i).prod (ψ i)) (inc i a) = (b.prod c) a := by
    apply Prod.ext
    · exact congrArg (fun h : A →ₐ[ℂ] B => h a) (hb i)
    · exact congrArg (fun h : A →ₐ[ℂ] C => h a) (hc i)
  constructor
  · intro i d hd
    obtain ⟨a,rfl⟩ := hd
    exact ⟨inc i a,hp i a⟩
  · intro i x hx
    obtain ⟨a,_,ha⟩ := hx
    exact ⟨a,ha⟩
  · intro i x hx
    obtain ⟨a,rfl⟩ := hx
    refine ⟨(b.prod c) (E i a),⟨E i a,rfl⟩,
      ((φ i).prod (ψ i)) (a-inc i (E i a)),?_,?_⟩
    · exact ⟨a-inc i (E i a),by
        change E i (a-inc i (E i a)) = 0
        rw [map_sub,hfix,sub_self],rfl⟩
    · rw [map_sub,hp,add_sub_cancel]
      rfl
  · intro i d x hd hx
    obtain ⟨a,rfl⟩ := hd
    obtain ⟨t,ht,rfl⟩ := hx
    refine ⟨inc i a*t,?_,?_⟩
    · change E i (inc i a*t) = 0
      rw [hmod,show E i t = 0 from ht,mul_zero]
    · change ((φ i).prod (ψ i)) (inc i a*t) = _
      rw [map_mul,hp]
      rfl

end

section
variable {I R S : Type*} [Ring R] [Algebra ℂ R] [Ring S] [Algebra ℂ S]

theorem IsCenteredWord.map_algHom {K : I → Submodule ℂ R}
    {L : I → Submodule ℂ S} (φ : R →ₐ[ℂ] S)
    (hKL : ∀ i a, a ∈ K i → φ a ∈ L i)
    {w : List (I × R)} (hw : IsCenteredWord K w) :
    IsCenteredWord L (w.map (fun p => (p.1,φ p.2))) := by
  refine ⟨?_,(List.isChain_map _).mpr hw.alternating⟩
  intro p hp
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
  exact hKL q.1 q.2 (hw.centered q hq)

@[simp] theorem wordValue_map_algHom (φ : R →ₐ[ℂ] S) (w : List (I × R)) :
    wordValue (w.map (fun p => (p.1,φ p.2))) = φ (wordValue w) := by
  induction w with
  | nil => simp
  | cons p w ih => simp only [List.map_cons,wordValue_cons,map_mul,ih]

variable {A B C : Type*} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B]
  [Ring C] [Algebra ℂ C] (V : I → Type*) [∀ i, Ring (V i)] [∀ i, Algebra ℂ (V i)]
  (inc : ∀ i, A →ₐ[ℂ] V i) (E : ∀ i, V i →ₗ[ℂ] A)
  (φ : ∀ i, V i →ₐ[ℂ] B) (ψ : ∀ i, V i →ₐ[ℂ] C)
  (b : A →ₐ[ℂ] B) (c : A →ₐ[ℂ] C)

theorem paired_free_moments_equal
    (hb : ∀ i, (φ i).comp (inc i) = b) (hc : ∀ i, (ψ i).comp (inc i) = c)
    (hfix : ∀ i a, E i (inc i a) = a)
    (hmod : ∀ i a x, E i (inc i a*x) = a*E i x)
    (f : B →ₗ[ℂ] ℂ) (g : C →ₗ[ℂ] ℂ)
    (hbase : ∀ a, f (b a) = g (c a))
    (hf : ∀ w, IsCenteredWord (factorCenters V E φ) w → w ≠ [] →
      f (wordValue w) = 0)
    (hg : ∀ w, IsCenteredWord (factorCenters V E ψ) w → w ≠ [] →
      g (wordValue w) = 0)
    {z : B × C} (hz : z ∈ Algebra.adjoin ℂ (⋃ i, (pairedFactors V φ ψ i : Set (B × C)))) :
    f z.1 = g z.2 := by
  let p : B × C →ₐ[ℂ] B := AlgHom.fst ℂ B C
  let q : B × C →ₐ[ℂ] C := AlgHom.snd ℂ B C
  have hp : ∀ i x, x ∈ pairedCenters V E φ ψ i → p x ∈ factorCenters V E φ i := by
    intro i x hx
    obtain ⟨a,ha,rfl⟩ := hx
    exact ⟨a,ha,rfl⟩
  have hq : ∀ i x, x ∈ pairedCenters V E φ ψ i → q x ∈ factorCenters V E ψ i := by
    intro i x hx
    obtain ⟨a,ha,rfl⟩ := hx
    exact ⟨a,ha,rfl⟩
  apply (paired_centered_decomposition V inc E φ ψ b c hb hc hfix hmod).moments_agree
    (f.comp p.toLinearMap) (g.comp q.toLinearMap) ?_ ?_ ?_ ?_ hz
  · intro d hd
    obtain ⟨a,rfl⟩ := hd
    exact hbase a
  · intro w hw hne
    have h := hf _ (hw.map_algHom p hp) (by simpa using hne)
    simpa only [wordValue_map_algHom,LinearMap.comp_apply,AlgHom.toLinearMap_apply] using h
  · intro w hw hne
    have h := hg _ (hw.map_algHom q hq) (by simpa using hne)
    simpa only [wordValue_map_algHom,LinearMap.comp_apply,AlgHom.toLinearMap_apply] using h
  · simpa using hbase 1
end

open Topology
open scoped ComplexOrder
section
variable {I A B C : Type*} [Ring A] [Algebra ℂ A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  (V : I → Type*) [∀ i, Ring (V i)] [∀ i, StarRing (V i)] [∀ i, Algebra ℂ (V i)]
  (φ : ∀ i, V i →⋆ₐ[ℂ] B) (ψ : ∀ i, V i →⋆ₐ[ℂ] C)

variable (inc : ∀ i, A →ₐ[ℂ] V i) (E : ∀ i, V i →ₗ[ℂ] A)
  (b : A →ₐ[ℂ] B) (c : A →ₐ[ℂ] C)
  (hb : ∀ i, (φ i).toAlgHom.comp (inc i) = b)
  (hc : ∀ i, (ψ i).toAlgHom.comp (inc i) = c)
  (hfix : ∀ i a, E i (inc i a) = a)
  (hmod : ∀ i a x, E i (inc i a*x) = a*E i x)
  (f : B →ₚ[ℂ] ℂ) (g : C →ₚ[ℂ] ℂ)
  (hbase : ∀ a, f (b a) = g (c a))
  (hfreeB : ∀ w, IsCenteredWord (factorCenters V E (fun i => (φ i).toAlgHom)) w →
    w ≠ [] → f (wordValue w) = 0)
  (hfreeC : ∀ w, IsCenteredWord (factorCenters V E (fun i => (ψ i).toAlgHom)) w →
    w ≠ [] → g (wordValue w) = 0)
include hb hc hfix hmod hbase hfreeB hfreeC

omit [StarOrderedRing B] [StarOrderedRing C] in
theorem jointStarModel_moments (z : jointStarModel V φ ψ) :
    f (jointFirst V φ ψ z) = g (jointSecond V φ ψ z) := by
  apply paired_free_moments_equal V inc E (fun i => (φ i).toAlgHom)
    (fun i => (ψ i).toAlgHom) b c hb hc hfix hmod f.toLinearMap g.toLinearMap
    hbase hfreeB hfreeC
  have hs : star (⋃ i, Set.range ((φ i).prod (ψ i))) ⊆
      ⋃ i, Set.range ((φ i).prod (ψ i)) := by
    intro x hx
    obtain ⟨i,a,ha⟩ := Set.mem_iUnion.mp (Set.mem_star.mp hx)
    exact Set.mem_iUnion.mpr ⟨i,star a,by rw [map_star,ha,star_star]⟩
  have hz := z.property
  change (z : B × C) ∈ (StarAlgebra.adjoin ℂ
    (⋃ i, Set.range ((φ i).prod (ψ i)))).toSubalgebra at hz
  rw [StarAlgebra.adjoin_toSubalgebra,Set.union_eq_self_of_subset_right hs] at hz
  exact hz

def jointFreeEquiv
    (hdB : Dense (StarAlgebra.adjoin ℂ (⋃ i, Set.range (φ i)) : Set B))
    (hdC : Dense (StarAlgebra.adjoin ℂ (⋃ i, Set.range (ψ i)) : Set C))
    (hf : ∀ x : B, f (star x*x) = 0 → x = 0)
    (hg : ∀ x : C, g (star x*x) = 0 → x = 0) : B ≃⋆ₐ[ℂ] C :=
  starAlgEquivOfFaithfulMoments (jointFirst V φ ψ) (jointSecond V φ ψ)
    (jointFirst_dense V φ ψ hdB) (jointSecond_dense V φ ψ hdC) f g
    (jointStarModel_moments V φ ψ inc E b c hb hc hfix hmod f g hbase hfreeB hfreeC) hf hg

variable (hdB : Dense (StarAlgebra.adjoin ℂ (⋃ i, Set.range (φ i)) : Set B))
    (hdC : Dense (StarAlgebra.adjoin ℂ (⋃ i, Set.range (ψ i)) : Set C))
    (hf : ∀ x : B, f (star x*x) = 0 → x = 0)
    (hg : ∀ x : C, g (star x*x) = 0 → x = 0)

@[simp] theorem jointFreeEquiv_factor (i : I) (a : V i) :
    jointFreeEquiv V φ ψ inc E b c hb hc hfix hmod f g hbase hfreeB hfreeC hdB hdC hf hg
      (φ i a) = ψ i a := by
  let z : jointStarModel V φ ψ := ⟨((φ i).prod (ψ i)) a,
    StarAlgebra.subset_adjoin ℂ _ (Set.mem_iUnion.mpr ⟨i,a,rfl⟩)⟩
  exact starAlgEquivOfFaithfulMoments_apply (jointFirst V φ ψ) (jointSecond V φ ψ)
    (jointFirst_dense V φ ψ hdB) (jointSecond_dense V φ ψ hdC) f g
    (jointStarModel_moments V φ ψ inc E b c hb hc hfix hmod f g hbase hfreeB hfreeC) hf hg z

theorem jointFreeEquiv_preserves (a : B) :
    g (jointFreeEquiv V φ ψ inc E b c hb hc hfix hmod f g hbase hfreeB hfreeC hdB hdC hf hg a) = f a :=
  starAlgEquivOfFaithfulMoments_preserves (jointFirst V φ ψ) (jointSecond V φ ψ)
    (jointFirst_dense V φ ψ hdB) (jointSecond_dense V φ ψ hdC) f g
    (jointStarModel_moments V φ ψ inc E b c hb hc hfix hmod f g hbase hfreeB hfreeC) hf hg a

end

open Topology
open scoped CStarAlgebra ComplexOrder

theorem wordValue_reindex {I J R : Type*} [Ring R] (s : I → J) (w : List (I × R)) :
    wordValue (w.map (fun p => (s p.1,p.2))) = wordValue w := by
  induction w with
  | nil => rfl
  | cons p w ih => simpa only [List.map_cons,wordValue_cons] using congrArg (p.2 * ·) ih

open Topology
open scoped CStarAlgebra ComplexOrder

open Topology
open scoped CStarAlgebra ComplexOrder

open Topology

open scoped InnerProductSpace ComplexStarModule CStarAlgebra

open UniformSpace
open scoped ComplexOrder

open scoped CStarAlgebra ComplexOrder

open Topology

open Filter Topology
open scoped CStarAlgebra ComplexOrder

open Topology

end NaimarkZFC

end

end OAI
end


