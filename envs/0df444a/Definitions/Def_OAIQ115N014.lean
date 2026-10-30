-- Prove2me | Definitions.Def_OAIQ115N014
-- name    : OAIQ115N014
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T01:19:51.375068+00:00
-- url     : https://prove2.me/theorems/c78ffdbc-122f-4644-b01b-cbfd7489e5be
-- title:
--   Definitions bundle OAIQ115N014 of the split of OpenAI, A counterexample to Naimark's problem in ZFC
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.NaimarkZFC.main`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to Naimark's problem in ZFC*, OpenAI Math Release, September 24, 2026, result family 297, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 41 declarations of OpenAI's Lean: 14 definitions, 2 inductive types or structures, 3 instances and 22 theorems. The definitions and types are `OAI.NaimarkZFC.BridgeSuccessor`, `OAI.NaimarkZFC.PeakingPairData.Endpoint`, `OAI.NaimarkZFC.PeakingPairData.HNNAlgebra`, `OAI.NaimarkZFC.PeakingPairData.cornerLetter`, `OAI.NaimarkZFC.PeakingPairData.hnnBase`, `OAI.NaimarkZFC.PeakingPairData.matrixTrace`, `OAI.NaimarkZFC.PeakingPairData.start`, `OAI.NaimarkZFC.PeakingPairData.support`, `OAI.NaimarkZFC.bridgeSupport`, `OAI.NaimarkZFC.cornerRestrictState`, `OAI.NaimarkZFC.cornerTrace`, `OAI.NaimarkZFC.cornerUnitary`, `OAI.NaimarkZFC.matrixCornerExpectation`, `OAI.NaimarkZFC.matrixCornerLetter`, `OAI.NaimarkZFC.matrixEntrySubalgebra`, `OAI.NaimarkZFC.matrixPeakingExpectation`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Naimark_HNN`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/HNN.lean), [`Naimark_Peaking`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/Peaking.lean).
--
--   **Imports.** It imports the published bundle `Def_Naimark`; the bundles `OAIQ115N012` and `OAIQ115N013` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ115N017`, `OAIQ115N018`, `OAIQ115N019` and `OAIQ115N020`.
-- source:
--   OpenAI, A counterexample to Naimark's problem in ZFC, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 297; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-counterexample-to-Naimarks-problem-in-ZFC-September-24-2026/naimark-counterexample-zfc.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_Naimark
import Definitions.Def_OAIQ115N012
import Definitions.Def_OAIQ115N013

section
-- module Solutions.OAIQ115_Naimark.Naimark_Peaking
attribute [-instance] _root_.OAI.NaimarkZFC.CStarCompletion.instCStarAlgebraCompletionOfCStarRingOfStarModuleComplex_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instNormedAlgebraComplexCompletion_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instStarCompletion_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instStarRingCompletion_solutions _root_.OAI.NaimarkZFC.retainedOrdinalAlgebra_cstar _root_.OAI.NaimarkZFC.hnnGeneratedCStar _root_.OAI.NaimarkZFC.omittedAlgebra_cstar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace NaimarkZFC

open scoped ComplexOrder CStarAlgebra

open Filter Topology
open scoped ComplexOrder CStarAlgebra OnePoint
section
variable {A n : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Fintype n] [DecidableEq n] [Nonempty n]

theorem matrixTraceState_isState (τ : A →L[ℂ] ℂ) (hτ : IsState τ) :
    IsState (matrixTraceState (n := n) τ hτ) := by
  apply (isState_iff _).mpr
  refine ⟨normalizedMatrixTrace_one _ ((isState_iff τ).mp hτ).1, ?_⟩
  intro M
  have h := (normalizedMatrixTrace (n := n) (positiveOfSquares τ hτ.2)).map_nonneg
    (star_mul_self_nonneg M)
  exact ⟨h.2.symm,h.1⟩

end

section
variable {C : Type*} [CStarAlgebra C]

variable {I V : Type*} (L : I → V → V → Type*) [DecidableEq I]

variable {A : I → Type*} [∀ i, CStarAlgebra (A i)]
  [∀ i, PartialOrder (A i)] [∀ i, StarOrderedRing (A i)]
  (d : ∀ i, AtomicTraceData (A i) V)

theorem atomicLeft_start_bound {i j : I} (hij : i ≠ j) (a : A i) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ r, ((d i).trace (((d i).atom r).1 * (star a*a) * ((d i).atom r).1)).re ≤
      C^2*((d i).trace ((d i).atom r).1).re) :
    ‖atomicLeft d i a * fockStartProjection (AtomicLetters d) j‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro x
  change ‖atomicLeft d i a (fockStartProjection (AtomicLetters d) j x)‖ ≤ C*‖x‖
  calc
    _ ≤ C * ‖fockStartProjection (AtomicLetters d) j x‖ :=
      atomicLeft_away_norm d i a C hC ha _
        (fockStarts_away _ hij.symm _ (fockStartProjection_starts _ _ _))
    _ ≤ C * (1*‖x‖) := mul_le_mul_of_nonneg_left
      (ContinuousLinearMap.le_of_opNorm_le _ (fockStartProjection_norm_le _ _) _) hC
    _ = C*‖x‖ := by rw [one_mul]

end

open Filter Topology
open scoped ComplexOrder
section
variable {I V : Type*} {A : I → Type*} [∀ i, CStarAlgebra (A i)]
  [∀ i, PartialOrder (A i)] [∀ i, StarOrderedRing (A i)]
  (d : ∀ i, AtomicTraceData (A i) V) [DecidableEq I] [DecidableEq V]
  {Δ : Type*} [CStarAlgebra Δ] (c : AtomicAmalgamData (Δ := Δ) d)

omit [DecidableEq I] [DecidableEq V] in

theorem atomicCoordinate_norm_le (x : Δ) (r : V) : ‖c.coordinate x r‖ ≤ ‖x‖ := by
  let i := c.base
  let q : A i := ((d i).atom r).1
  have hq : 0 < ‖q‖ := by
    apply norm_pos_iff.mpr
    intro hz
    have hp := (d i).positive r
    change 0 < ((d i).trace q).re at hp
    rw [hz, map_zero, Complex.zero_re] at hp
    exact (lt_irrefl 0) hp
  apply (mul_le_mul_iff_right₀ hq).mp
  calc
    ‖q‖ * ‖c.coordinate x r‖ = ‖c.coordinate x r • q‖ := by rw [norm_smul,mul_comm]
    _ = ‖q * c.diagonal i x‖ := congrArg norm (c.atom_mul i x r).symm
    _ ≤ ‖q‖ * ‖c.diagonal i x‖ := norm_mul_le _ _
    _ ≤ ‖q‖ * ‖x‖ := mul_le_mul_of_nonneg_left (NonUnitalStarAlgHom.norm_apply_le _ _) hq.le

omit [DecidableEq I] [DecidableEq V] in

theorem atomicExpectation_corner_formula (i : I) (a : A i) (r : V) :
    (d i).trace (((d i).atom r).1*a*((d i).atom r).1) =
      c.coordinate (c.expectation i a) r * (d i).trace ((d i).atom r).1 := by
  have hz := c.centered i (a-c.diagonal i (c.expectation i a)) (by rw [map_sub,c.fix,sub_self]) r
  rw [mul_sub,sub_mul,map_sub,c.atom_mul,smul_mul_assoc,
    ((d i).atom r).2.isIdempotentElem.eq,map_smul] at hz
  exact sub_eq_zero.mp hz

end

open Filter Topology

open Filter Topology
open scoped CStarAlgebra ComplexOrder OnePoint
section
variable {A n ι : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Fintype n] [DecidableEq n] [Nonempty n] [Preorder ι]
  {p : n → ℕ → A} {f : n → A →L[ℂ] ℂ}
  (hp : ∀ j, Peaks (p j) (f j)) (hp0 : ∀ j, p j 0 = 1)
  (τ : A →L[ℂ] ℂ) (hτ : IsState τ) (hpos : ∀ j k, 0 < (τ (peakAtom (p j) k)).re)

def matrixPeakingExpectation : CStarMatrix n n A →L[ℂ] (n → SequenceDiagonal) :=
  matrixDiagonalExpectation (fun j => peakingCoefficients (hp j) τ hτ (hpos j))
    (fun j a => peakingCoefficientsFun_norm_le (hp j) τ hτ (hpos j) a)

end

open Filter Topology

open Filter Topology

section
open scoped CStarAlgebra
variable {A D Z : Type*} [CStarAlgebra A] [CStarAlgebra D] [CStarAlgebra Z]
  [PartialOrder A] [StarOrderedRing A]
  [PartialOrder D] [StarOrderedRing D]
  (φ : CStarMatrix Bool Bool A →⋆ₐ[ℂ] Z)
  (ψ : CStarMatrix Bool Bool D →⋆ₐ[ℂ] Z)
  (δ : Bool → D →⋆ₐ[ℂ] A)
  (hd : ∀ x, φ (matrixDiagonalHom δ x) =
    ψ (matrixDiagonalHom (fun _ => StarAlgHom.id ℂ D) x))

def bridgeSupport (i : Bool) : Z := φ (matrixSingle i i (1:A))

end

open Filter Topology
open scoped OnePoint ComplexOrder CStarAlgebra

open Filter Topology
open scoped CStarAlgebra ComplexOrder OnePoint

namespace PeakingPairData
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (B : PeakingPairData A)

attribute [local instance] OAI.NaimarkZFC.PeakingPairData.matrixFamilyStarOrder
instance modelAddZeroClass : AddZeroClass B.Model :=
  B.modelCStarAlgebra.toAddZeroClass

theorem expectation_eq : B.expectation =
    matrixPeakingExpectation B.peaks (positiveCLM B.trace)
      (positiveCLM_isState B.trace B.normalized) B.atom_positive := rfl

abbrev support := bridgeSupport B.base
abbrev start := fockStartProjection (AtomicLetters B.atoms) true

end PeakingPairData

open Filter Topology
open scoped CStarAlgebra ComplexOrder

open scoped InnerProductSpace ComplexStarModule CStarAlgebra ComplexOrder

open Filter Topology
open scoped InnerProductSpace ComplexStarModule CStarAlgebra ComplexOrder

open Filter Topology

open Filter Topology
open scoped CStarAlgebra ComplexOrder
namespace PeakingPairData
attribute [local instance] matrixFamilyStarOrder
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (B : PeakingPairData A)

abbrev matrixTrace := matrixTraceState (n := Bool) (positiveCLM B.trace)
  (positiveCLM_isState B.trace B.normalized)

structure Endpoint (ι : Type*) [Preorder ι] where
  state : CStarMatrix Bool Bool A →L[ℂ] ℂ
  pure : IsPureState state
  net : ι → CStarMatrix Bool Bool A
  positive : ∀ k, 0 ≤ net k
  contractive : ∀ k, ‖net k‖ ≤ 1
  antitone : Antitone net
  excision : ∀ a, Tendsto (fun k => net k*(a-state a • 1)*net k) atTop (𝓝 0)
  trace_null : Tendsto (fun k => B.matrixTrace (net k)) atTop (𝓝 0)
  peakIndex : ι → ℕ
  peak_tendsto : Tendsto peakIndex atTop atTop
  tag : Option Bool
  matchedState : ∀ i, tag = some i → state = B.matrixState i
  matchedNet : ∀ i, tag = some i → ∀ k, net k = B.matrixPeak i (peakIndex k)
  unmatched : ∀ i, tag ≠ some i →
    ¬ UnitarilyEquivalent (pureGNS state pure) (pureGNS (B.matrixState i) (B.matrixPure i))

end PeakingPairData

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

section
-- module Solutions.OAIQ115_Naimark.Naimark_HNN
attribute [-instance] _root_.OAI.NaimarkZFC.CStarCompletion.instCStarAlgebraCompletionOfCStarRingOfStarModuleComplex_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instNormedAlgebraComplexCompletion_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instStarCompletion_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instStarRingCompletion_solutions _root_.OAI.NaimarkZFC.constructionIndex_nonempty _root_.OAI.NaimarkZFC.constructionIndex_orderBot _root_.OAI.NaimarkZFC.retainedOrdinalAlgebra_cstar _root_.OAI.NaimarkZFC.hnnGeneratedCStar _root_.OAI.NaimarkZFC.omittedAlgebra_cstar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace NaimarkZFC

open scoped CStarAlgebra ComplexOrder
namespace PeakingPairData
attribute [local instance] matrixFamilyStarOrder modelPartialOrder modelStarOrderedRing
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (B : PeakingPairData A)

instance modelCornerCStarAlgebra : CStarAlgebra B.Corner := inferInstance

theorem cornerBase_injective : Function.Injective B.cornerBase :=
  matrixCornerBase_injective B.embedBase (atomicEmbedding_injective B.atoms false)

end PeakingPairData

open scoped CStarAlgebra Matrix
section
variable {A Z : Type*} [CStarAlgebra A] [CStarAlgebra Z]
    (φ : CStarMatrix Bool Bool A →⋆ₐ[ℂ] Z)

theorem matrixCornerEntry_mul (i j : Bool) (x y : Z) :
    matrixCornerEntry φ i j (x*y) =
      matrixCornerEntry φ i false x * matrixCornerEntry φ false j y +
      matrixCornerEntry φ i true x * matrixCornerEntry φ true j y := by
  apply Subtype.ext
  change φ (matrixSingle false i 1) * (x*y) * φ (matrixSingle j false 1) =
    (φ (matrixSingle false i 1) * x * φ (matrixSingle false false 1)) *
      (φ (matrixSingle false false 1) * y * φ (matrixSingle j false 1)) +
    (φ (matrixSingle false i 1) * x * φ (matrixSingle true false 1)) *
      (φ (matrixSingle false true 1) * y * φ (matrixSingle j false 1))
  symm
  calc
    _ = φ (matrixSingle false i 1) * x *
        (φ (matrixSingle false false 1) * φ (matrixSingle false false 1) +
         φ (matrixSingle true false 1) * φ (matrixSingle false true 1)) *
        y * φ (matrixSingle j false 1) := by noncomm_ring
    _ = _ := by
      rw [← map_mul, ← map_mul, matrixSingle_mul, matrixSingle_mul, one_mul,
        ← map_add, matrix_diag_sum_one, map_one]
      simp only [mul_one, mul_assoc]

end

open scoped CStarAlgebra
section
variable {A D Z : Type*} [CStarAlgebra A] [CStarAlgebra D] [CStarAlgebra Z]
    (φ : CStarMatrix Bool Bool A →⋆ₐ[ℂ] Z)

def matrixEntrySubalgebra (S : StarSubalgebra ℂ (MatrixHNNCorner φ)) : StarSubalgebra ℂ Z where
  carrier := {z | ∀ i j, matrixCornerEntry φ i j z ∈ S}
  zero_mem' := by intro i j; rw [map_zero]; exact zero_mem S
  add_mem' := by intro x y hx hy i j; rw [map_add]; exact add_mem (hx i j) (hy i j)
  mul_mem' := by
    intro x y hx hy i j
    rw [matrixCornerEntry_mul]
    exact S.add_mem (S.mul_mem (hx i false) (hy false j)) (S.mul_mem (hx i true) (hy true j))
  algebraMap_mem' c := by
    intro i j
    rw [Algebra.algebraMap_eq_smul_one, map_smul, matrixCornerEntry_one]
    apply S.smul_mem
    cases i <;> cases j <;> simp
  star_mem' := by
    intro x hx i j
    rw [matrixCornerEntry_star]
    exact star_mem (hx j i)

@[simp] theorem mem_matrixEntrySubalgebra (S : StarSubalgebra ℂ (MatrixHNNCorner φ)) (z : Z) :
    z ∈ matrixEntrySubalgebra φ S ↔ ∀ i j, matrixCornerEntry φ i j z ∈ S := Iff.rfl

variable (ψ : CStarMatrix Bool Bool D →⋆ₐ[ℂ] Z)
    (diag : ∀ i : Bool, φ (matrixSingle i i (1 : A)) = ψ (matrixSingle i i (1 : D)))

def matrixCornerLetter (i : Bool) : MatrixHNNCorner φ :=
  if i then matrixStable φ ψ diag else star (matrixStable φ ψ diag)

@[simp] theorem matrixCornerLetter_star (i : Bool) :
    star (matrixCornerLetter φ ψ diag i) = matrixCornerLetter φ ψ diag (!i) := by
  cases i <;> simp [matrixCornerLetter]

end

open scoped CStarAlgebra ComplexOrder
namespace PeakingPairData
attribute [local instance] matrixFamilyStarOrder modelPartialOrder modelStarOrderedRing
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (B : PeakingPairData A)

abbrev cornerLetter : Bool → B.Corner :=
  matrixCornerLetter B.embedBase B.embedAux
    (matrixDiagonal_units B.embedBase B.embedAux B.diagonal B.model_diagonal_agree)

@[simp] theorem cornerLetter_true : B.cornerLetter true = (B.stableUnitary : B.Corner) := rfl
@[simp] theorem cornerLetter_false : B.cornerLetter false = star (B.stableUnitary : B.Corner) := rfl
@[simp] theorem cornerLetter_star (i : Bool) : star (B.cornerLetter i) = B.cornerLetter (!i) :=
  matrixCornerLetter_star _ _ _ i

end PeakingPairData

open scoped CStarAlgebra ComplexOrder
section
variable {A C : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra C]
  (φ : CStarMatrix Bool Bool A →⋆ₐ[ℂ] C)
  (E : C →L[ℂ] CStarMatrix Bool Bool A)

def matrixCornerExpectation : MatrixHNNCorner φ →L[ℂ] A :=
  (matrixEntryCLM false).comp (E.comp (cornerSubalgebra (matrixCornerProjection φ)
    (matrixCornerProjection_isProjection φ)).subtypeL)

@[simp] theorem matrixCornerExpectation_apply (x : MatrixHNNCorner φ) :
    matrixCornerExpectation φ E x = E (x:C) false false := rfl

end

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra

open scoped InnerProductSpace lp

open scoped CStarAlgebra ComplexOrder

section
open scoped ComplexOrder
variable {A : Type*} [CStarAlgebra A]
variable (e : A) (he : IsStarProjection e)

def cornerTrace (t : A →L[ℂ] ℂ) (c : ℝ) : CStarCorner e he →L[ℂ] ℂ :=
  c • t.comp (cornerSubalgebra e he).subtypeL

@[simp] theorem cornerTrace_apply (t : A →L[ℂ] ℂ) (c : ℝ) (a : CStarCorner e he) :
    cornerTrace e he t c a = c • t (a : A) := rfl

end

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra

open scoped CStarAlgebra ComplexOrder

open Topology
open scoped CStarAlgebra ComplexOrder

open Topology
open scoped CStarAlgebra ComplexOrder
namespace PeakingPairData
attribute [local instance] matrixFamilyStarOrder modelPartialOrder modelStarOrderedRing
variable {A : Type} [instA : CStarAlgebra A] [orderA : PartialOrder A]
  [starOrderA : StarOrderedRing A] (B : PeakingPairData A)

def HNNAlgebra : Type := B.Corner
instance hnnCStar : CStarAlgebra B.HNNAlgebra :=
  cornerCStarAlgebra (A := B.Model) (matrixCornerProjection B.embedBase)
    (matrixCornerProjection_isProjection B.embedBase)

def hnnBase : A →⋆ₐ[ℂ] B.HNNAlgebra := B.cornerBase

theorem hnnBase_injective : Function.Injective B.hnnBase := B.cornerBase_injective

end PeakingPairData

open scoped CStarAlgebra ComplexOrder InnerProductSpace ComplexStarModule
section
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (e : A) (he : IsStarProjection e)

def cornerRestrictState (f : A →L[ℂ] ℂ) : CStarCorner e he →L[ℂ] ℂ :=
  f.comp (cornerSubalgebra e he).subtypeL

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] theorem cornerRestrictState_apply (f : A →L[ℂ] ℂ) (a : CStarCorner e he) :
    cornerRestrictState e he f a = f (a : A) := rfl

end

open scoped CStarAlgebra ComplexOrder

open Filter Topology
open scoped CStarAlgebra ComplexOrder InnerProductSpace

open Filter Topology
open scoped CStarAlgebra ComplexOrder

open Filter Topology
open scoped CStarAlgebra ComplexOrder InnerProductSpace

open Filter Topology
open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder InnerProductSpace ComplexStarModule

open Filter Topology
open scoped CStarAlgebra ComplexOrder InnerProductSpace

open scoped CStarAlgebra ComplexOrder
section
variable {A : Type*} [CStarAlgebra A] (e : A) (he : IsStarProjection e)

def cornerUnitary (u : unitary (CStarCorner e he)) : unitary A := by
  let x : CStarCorner e he := u
  have hx : star (x:A)*(x:A)=e := congrArg (fun c : CStarCorner e he => (c:A)) u.property.1
  have hy : (x:A)*star (x:A)=e := congrArg (fun c : CStarCorner e he => (c:A)) u.property.2
  have hs : e*star (x:A)=star (x:A) ∧ star (x:A)*e=star (x:A) := (star x).property
  refine ⟨(x:A)+(1-e),?_,?_⟩
  · simp only [star_add,star_sub,star_one,he.isSelfAdjoint.star_eq,
      add_mul,mul_add,sub_mul,mul_sub,one_mul,mul_one,hx,x.property.1,hs.2,he.isIdempotentElem.eq]
    abel
  · simp only [star_add,star_sub,star_one,he.isSelfAdjoint.star_eq,
      add_mul,mul_add,sub_mul,mul_sub,one_mul,mul_one,hy,x.property.2,hs.1,he.isIdempotentElem.eq]
    abel

@[simp] theorem cornerUnitary_apply (u : unitary (CStarCorner e he)) :
    (cornerUnitary e he u : A) = ((u : CStarCorner e he):A)+(1-e) := rfl

end

open scoped CStarAlgebra ComplexOrder InnerProductSpace

open scoped CStarAlgebra ComplexOrder InnerProductSpace

open scoped CStarAlgebra ComplexOrder

open scoped ComplexOrder

open scoped CStarAlgebra ComplexOrder
section
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in

theorem exists_contracting_real_dual {E : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] (x : E) (hn : ‖x‖ = 1) :
    ∃ g : E →L[ℝ] ℝ, (∀ y, ‖g y‖ ≤ ‖y‖) ∧ g x = 1 := by
  obtain ⟨g,hg,hx⟩ := exists_dual_vector ℝ x (hn.trans_ne one_ne_zero)
  refine ⟨g,fun y => ?_,?_⟩
  · simpa only [hg,one_mul] using g.le_opNorm y
  · simpa [hn] using hx

omit [PartialOrder A] [StarOrderedRing A] in

theorem properIdeal_one_sub_norm (J : TwoSidedIdeal A) (hJ : J ≠ ⊤)
    (a : A) (ha : a ∈ J) : 1 ≤ ‖1-a‖ := by
  by_contra hn
  have hu : IsUnit a := by
    simpa only [sub_sub_cancel] using isUnit_one_sub_of_norm_lt_one (lt_of_not_ge hn)
  obtain ⟨u,rfl⟩ := hu
  apply hJ
  apply J.eq_top
  simpa using J.mul_mem_left (↑u⁻¹) (↑u) ha

theorem exists_state_killing_ideal (J : TwoSidedIdeal A) (hc : IsClosed (J : Set A))
    (hJ : J ≠ ⊤) :
    ∃ f : A →L[ℂ] ℂ, IsState f ∧ ∀ a ∈ J, f (star a*a) = 0 := by
  let S := idealSelfAdjointSubspace J
  let : IsClosed (S : Set (selfAdjoint A)) := hc.preimage continuous_subtype_val
  let q : selfAdjoint A →L[ℝ] (selfAdjoint A ⧸ S) := S.mkQL
  have hnorm : ‖q (1 : selfAdjoint A)‖ = 1 := by
    apply le_antisymm
    · exact (Submodule.Quotient.norm_mk_le (S := S) (1 : selfAdjoint A)).trans (by exact (IsStarProjection.one A).norm_le 1)
    · apply le_of_forall_pos_le_add
      intro ε hε
      obtain ⟨a,ha,hn⟩ := Submodule.Quotient.norm_mk_lt (q (1 : selfAdjoint A)) hε
      have hj : ((1 : selfAdjoint A)-a : selfAdjoint A) ∈ S :=
        (Submodule.Quotient.eq S).mp ha.symm
      have hb := properIdeal_one_sub_norm J hJ ((1 : selfAdjoint A)-a : selfAdjoint A) hj
      have hb' : 1 ≤ ‖a‖ := by
        change 1 ≤ ‖(a:A)‖
        change 1 ≤ ‖1-(1-(a:A))‖ at hb
        simpa only [sub_sub_cancel] using hb
      exact hb'.trans hn.le
  obtain ⟨g,hg,hgv⟩ := @exists_contracting_real_dual (selfAdjoint A ⧸ S)
    (Submodule.Quotient.seminormedAddCommGroup S) (Submodule.Quotient.normedSpace S ℝ)
    (q (1 : selfAdjoint A)) hnorm
  let G := g.comp q
  have hGn : ‖G‖ ≤ 1 := by
    apply G.opNorm_le_bound zero_le_one
    intro a
    calc
      ‖G a‖ ≤ ‖q a‖ := hg _
      _ ≤ 1*‖a‖ := by
        change ‖(Submodule.Quotient.mk a : selfAdjoint A ⧸ S)‖ ≤ 1*‖a‖
        simpa only [one_mul] using Submodule.Quotient.norm_mk_le (S := S) a
  have hG1 : G 1 = 1 := by
    change g (q 1) = 1
    exact hgv
  let F := selfAdjointPositive G hGn hG1
  have hF : IsState (positiveCLM F) := by
    apply (isState_iff _).mpr
    refine ⟨selfAdjointPositive_one G hGn hG1,fun a => ?_⟩
    have hh := F.map_nonneg (star_mul_self_nonneg a)
    exact ⟨hh.2.symm,hh.1⟩
  refine ⟨positiveCLM F,hF,?_⟩
  intro a ha
  let b : selfAdjoint A := ⟨star a*a,IsSelfAdjoint.of_nonneg (star_mul_self_nonneg a)⟩
  have hb : b ∈ S := J.mul_mem_left (star a) a ha
  have hq : q b = 0 := (Submodule.Quotient.mk_eq_zero S).mpr hb
  change F (b:A) = 0
  rw [selfAdjointPositive_coe]
  change ((g (q b):ℝ):ℂ) = 0
  rw [hq,map_zero,Complex.ofReal_zero]

end

open scoped CStarAlgebra ComplexOrder InnerProductSpace
open UniformSpace

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder

open Topology

open scoped CStarAlgebra ComplexOrder
section
universe u v w
variable {I : Type u} [Nonempty I] (A : I → Type v) [∀ i, CStarAlgebra (A i)]
  {C : Type w} [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]

theorem simple_of_dense_stage_ranges (hA : ∀ i, IsSimpleCStar (A i))
    (φ : ∀ i, A i →⋆ₐ[ℂ] C) (hi : ∀ i, Isometry (φ i))
    (hd : Dense (⋃ i, Set.range (φ i))) : IsSimpleCStar C := by
  let i₀ : I := Classical.choice inferInstance
  let : Nontrivial (A i₀) := (hA i₀).1
  let : Nontrivial C := (hi i₀).injective.nontrivial
  refine ⟨inferInstance,fun J hc => ?_⟩
  by_cases hJ : J = ⊤
  · exact Or.inr hJ
  left
  obtain ⟨g,hg,hkill⟩ := exists_state_killing_ideal J hc hJ
  let G : C →ₚ[ℂ] ℂ := positiveOfSquares g hg.2
  let π := G.gnsStarAlgHom
  have hn : ‖gnsVector G‖ = 1 := gnsVector_norm_eq_one G ((isState_iff g).mp hg).1
  have hstage (i : I) : Function.Injective (π.comp (φ i)) := by
    apply simple_nonzeroStarHom_injective (hA i) (π.comp (φ i)).toNonUnitalStarAlgHom
    intro hz
    have hh := congrArg (fun ψ : A i →⋆ₙₐ[ℂ] (G.GNS →L[ℂ] G.GNS) =>
      ψ 1 (gnsVector G)) hz
    have hh' : gnsVector G = 0 := by
      change π (φ i 1) (gnsVector G) = 0 at hh
      simpa only [map_one,one_apply_eq_self] using hh
    rw [hh',norm_zero] at hn
    exact zero_ne_one hn
  have hnorm (c : C) : ‖π c‖ = ‖c‖ := by
    apply (closure_minimal ?_ (isClosed_eq ((map_continuous π).norm) continuous_norm)) (hd c)
    intro c hc'
    obtain ⟨i,a,rfl⟩ := Set.mem_iUnion.mp hc'
    exact (NonUnitalStarAlgHom.norm_map (π.comp (φ i)) (hstage i) a).trans
      ((hi i).norm_map_of_map_zero (map_zero _) a).symm
  apply le_antisymm _ bot_le
  intro a ha
  have hz : π a = 0 := gns_kills_ideal G J hkill a ha
  have hna := hnorm a
  rw [hz,norm_zero] at hna
  rw [norm_eq_zero.mp hna.symm]
  exact TwoSidedIdeal.zero_mem _

end

open Topology
section
variable {A B C : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]

theorem IsSimpleCStar.of_equiv (hA : IsSimpleCStar A) (e : A ≃⋆ₐ[ℂ] B) :
    IsSimpleCStar B := by
  let : PartialOrder B := CStarAlgebra.spectralOrder B
  let : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
  apply simple_of_dense_stage_ranges (fun _ : Unit => A) (fun _ => hA)
    (fun _ => e.toStarAlgHom) (fun _ => StarAlgEquiv.isometry e)
  have he : (⋃ _ : Unit, Set.range e.toStarAlgHom) = Set.univ := by
    ext b
    simp only [Set.mem_iUnion,Set.mem_range,Set.mem_univ,iff_true]
    obtain ⟨a,ha⟩ := e.surjective b
    exact ⟨(),a,ha⟩
  rw [he]
  exact dense_univ

end

open Topology

open Topology
section

inductive BridgeSuccessor {A C : Type} [CStarAlgebra A] [CStarAlgebra C]
    [PartialOrder A] [StarOrderedRing A] (φ : A →⋆ₐ[ℂ] C) : Prop
  | identity (e : A ≃⋆ₐ[ℂ] C) (he : ∀ a, e a = φ a)
  | hnn (B : PeakingPairData A) (hs : B.Separated)
      (e : B.HNNAlgebra ≃⋆ₐ[ℂ] C) (he : ∀ a, e (B.hnnBase a) = φ a)

universe u

end

open Filter Topology
open scoped InnerProductSpace ComplexOrder ComplexStarModule CStarAlgebra

open Topology

open scoped CStarAlgebra ComplexOrder

open Filter Topology
open scoped CStarAlgebra ComplexOrder

open Topology
open scoped CStarAlgebra ComplexOrder

open Topology
open scoped CStarAlgebra ComplexOrder

open Filter Topology
open scoped CStarAlgebra ComplexOrder OnePoint

open Topology

end NaimarkZFC

end

end OAI
end


