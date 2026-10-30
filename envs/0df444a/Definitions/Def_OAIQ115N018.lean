-- Prove2me | Definitions.Def_OAIQ115N018
-- name    : OAIQ115N018
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T01:26:27.913431+00:00
-- url     : https://prove2.me/theorems/69b58f22-5708-4bb0-b923-2ba82659a85d
-- title:
--   Definitions bundle OAIQ115N018 of the split of OpenAI, A counterexample to Naimark's problem in ZFC
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.NaimarkZFC.main`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to Naimark's problem in ZFC*, OpenAI Math Release, September 24, 2026, result family 297, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 60 declarations of OpenAI's Lean: 15 definitions, 2 inductive types or structures, 1 instance and 42 theorems. The definitions and types are `OAI.NaimarkZFC.HNNWord.AllCoefficients`, `OAI.NaimarkZFC.HNNWord.join`, `OAI.NaimarkZFC.HNNWord.lastCoefficient`, `OAI.NaimarkZFC.HNNWord.mapCoefficients`, `OAI.NaimarkZFC.HNNWord.matrixCore`, `OAI.NaimarkZFC.HNNWord.matrixFinal`, `OAI.NaimarkZFC.PeakingPairData.turnCenter`, `OAI.NaimarkZFC.PeakingPairData.turnCentered`, `OAI.NaimarkZFC.PeakingPairData.turnRemainder`, `OAI.NaimarkZFC.TracialStage`, `OAI.NaimarkZFC.TracialStage.Hom`, `OAI.NaimarkZFC.carPeak`, `OAI.NaimarkZFC.carStagePeak`, `OAI.NaimarkZFC.carStageTrace`, `OAI.NaimarkZFC.carStageVector`, `OAI.NaimarkZFC.carTrace`, `OAI.NaimarkZFC.carVector`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Naimark_CAR`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/CAR.lean), [`Naimark_Dependencies`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/Dependencies.lean), [`Naimark_Extension`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/Extension.lean), [`Naimark_HNN`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/HNN.lean), [`Naimark_Omission`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/Omission.lean), [`Naimark_Stages`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/Stages.lean).
--
--   **Imports.** It imports the published bundle `Def_Naimark`; the bundles `OAIQ115N014` and `OAIQ115N015` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ115N021`, `OAIQ115N022`, `OAIQ115N023` and `OAIQ115N024`.
-- source:
--   OpenAI, A counterexample to Naimark's problem in ZFC, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 297; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-counterexample-to-Naimarks-problem-in-ZFC-September-24-2026/naimark-counterexample-zfc.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_Naimark
import Definitions.Def_OAIQ115N014
import Definitions.Def_OAIQ115N015

section
-- module Solutions.OAIQ115_Naimark.Naimark_HNN
attribute [-instance] _root_.OAI.NaimarkZFC.CStarCompletion.instCStarAlgebraCompletionOfCStarRingOfStarModuleComplex_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instNormedAlgebraComplexCompletion_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instStarCompletion_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instStarRingCompletion_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace NaimarkZFC

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra Matrix

open scoped CStarAlgebra

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra
section
variable {A D Z : Type*} [CStarAlgebra A] [CStarAlgebra D] [CStarAlgebra Z]
  (φ : CStarMatrix Bool Bool A →⋆ₐ[ℂ] Z) (ψ : CStarMatrix Bool Bool D →⋆ₐ[ℂ] Z)
  (diag : ∀ i : Bool, φ (matrixSingle i i (1:A)) = ψ (matrixSingle i i (1:D)))

theorem matrixCornerLetter_coe (i : Bool) :
    (matrixCornerLetter φ ψ diag i : Z) =
      φ (matrixSingle false i 1) * bridgeLetter ψ i *
        φ (matrixSingle (!i) false 1) := by
  cases i
  · change star (φ (matrixSingle false true 1)*ψ (matrixSingle true false 1)) =
      φ (matrixSingle false false 1) * ψ (matrixSingle false true 1) *
        φ (matrixSingle true false 1)
    simp only [star_mul,← map_star,matrixSingle_star,star_one]
    rw [diag false,← map_mul,matrixSingle_mul,one_mul]
  · change φ (matrixSingle false true 1)*ψ (matrixSingle true false 1) =
      φ (matrixSingle false true 1)*ψ (matrixSingle true false 1)*φ (matrixSingle false false 1)
    rw [mul_assoc,diag false,← map_mul,matrixSingle_mul,mul_one]

namespace HNNWord
variable {φ ψ diag}

def matrixCore : HNNWord A → BridgeCore (CStarMatrix Bool Bool A)
  | .single i _ => .single i
  | .cons i a w => w.matrixCore.cons i (matrixSingle (!i) w.first a)

def matrixFinal : HNNWord A → CStarMatrix Bool Bool A
  | .single i a => matrixSingle (!i) false a
  | .cons _ _ w => w.matrixFinal

theorem eval_matrix_core (w : HNNWord A) :
    ((w.eval (matrixCornerBase φ) (matrixCornerLetter φ ψ diag) : MatrixHNNCorner φ) : Z) =
      φ (matrixSingle false w.first 1) * w.matrixCore.eval φ (bridgeLetter ψ) * φ w.matrixFinal := by
  induction w with
  | single i a =>
    change (matrixCornerLetter φ ψ diag i : Z) * φ (matrixSingle false false a) = _
    rw [matrixCornerLetter_coe]
    change (φ (matrixSingle false i 1) * bridgeLetter ψ i * φ (matrixSingle (!i) false 1)) *
      φ (matrixSingle false false a) =
      φ (matrixSingle false i 1) * bridgeLetter ψ i * φ (matrixSingle (!i) false a)
    rw [mul_assoc,← map_mul,matrixSingle_mul,one_mul]
  | cons i a w ih =>
    change ((matrixCornerLetter φ ψ diag i : Z) * φ (matrixSingle false false a)) *
      (↑(w.eval (matrixCornerBase φ) (matrixCornerLetter φ ψ diag)) : Z) = _
    rw [matrixCornerLetter_coe,ih]
    change _ = φ (matrixSingle false i 1) *
      (w.matrixCore.cons i (matrixSingle (!i) w.first a)).eval φ (bridgeLetter ψ) * φ w.matrixFinal
    calc
      _ = φ (matrixSingle false i 1) * bridgeLetter ψ i *
          (φ (matrixSingle (!i) false 1) * φ (matrixSingle false false a) *
            φ (matrixSingle false w.first 1)) *
          w.matrixCore.eval φ (bridgeLetter ψ) * φ w.matrixFinal := by simp only [mul_assoc]
      _ = _ := by
        rw [← map_mul,← map_mul,matrixSingle_mul,matrixSingle_mul,one_mul,mul_one,
          BridgeCore.eval_cons]
        simp only [mul_assoc]

theorem matrixCore_centered (Q : Bool → A → Prop) (K : CStarMatrix Bool Bool A → Prop)
    (hK : ∀ i j a, i = j ∨ Q i a → K (matrixSingle (!i) j a))
    (w : HNNWord A) (hw : w.Reduced Q) : w.matrixCore.Centered K := by
  induction w with
  | single i a => trivial
  | cons i a w ih => exact w.matrixCore.centered_cons K i _ (hK i w.first a hw.1) (ih hw.2)
end HNNWord

end

open scoped InnerProductSpace lp
section
section Fock
variable {I V : Type*} (L : I → V → V → Type*) [DecidableEq I]
  {A : I → Type*} [∀ i, CStarAlgebra (A i)]
  (π : ∀ i r, A i →⋆ₐ[ℂ]
    (ℓ²(ColumnIndex L i r, ℂ) →L[ℂ] ℓ²(ColumnIndex L i r, ℂ)))

theorem atomicFock_vacuum_away_ne {i j : I} (hij : i ≠ j) (a : A i) (z : ℓ²(V,ℂ)) :
    FockAway L j (atomicFockRepresentation L π i a (fockVacuum L z)) := by
  intro p hp
  have hpi : p.1 ≠ some i := by
    rw [hp]
    exact fun h => hij (Option.some.inj h).symm
  have h := atomicFock_creation L π i a (fockVacuum L z)
    (fockVacuum_away L z i) ⟨p,hpi⟩ none
  change atomicFockRepresentation L π i a (fockVacuum L z) p = _ at h
  rw [h,fockVacuum_away L z j p hp,zero_mul]

theorem fockAway_inner_starts (i : I) (x y : AtomicFockSpace L)
    (hx : FockAway L i x) (hy : FockStarts L i y) : inner ℂ x y = 0 := by
  rw [lp.inner_eq_tsum]
  suffices h : ∀ p, inner ℂ (x p) (y p) = 0 by simp only [h,tsum_zero]
  intro p
  by_cases hp : p.1 = some i
  · rw [hx p hp,inner_zero_left]
  · rw [hy p hp,inner_zero_right]
end Fock

variable {I V : Type*} {A : I → Type*} [∀ i, CStarAlgebra (A i)]
  [∀ i, PartialOrder (A i)] [∀ i, StarOrderedRing (A i)]
  (d : ∀ i, AtomicTraceData (A i) V) [DecidableEq I] [DecidableEq V]
  {i j : I} (hij : i ≠ j) (b : Bool → A j)
  (hb : ∀ v r, (d j).trace (((d j).atom r).1*b v*((d j).atom r).1) = 0)
  (K : A i → Prop)
  (hK : ∀ a, K a → ∀ r, (d i).trace (((d i).atom r).1*a*((d i).atom r).1) = 0)

omit [DecidableEq V] in
include hij hb hK in

theorem atomicCore_coefficient_zero (k : I) (w : BridgeCore (A i)) (hw : w.Centered K)
    (a c : A i) :
    inner ℂ (atomicLeft d i a (atomicVacuum d k))
      (w.eval (atomicLeft d i) (fun v => atomicLeft d j (b v))
        (atomicLeft d i c (atomicVacuum d k))) = 0 := by
  exact fockAway_inner_starts (AtomicLetters d) j _ _
    (atomicFock_vacuum_away_ne (AtomicLetters d) (atomicColumnReps d) hij a _)
    (w.creation d hij b hb K hK hw _
      (atomicFock_vacuum_away_ne (AtomicLetters d) (atomicColumnReps d) hij c _))

omit [DecidableEq V] in
theorem atomicCore_coe (w : BridgeCore (A i)) :
    ((w.eval (atomicEmbedding d i) (fun v => atomicEmbedding d j (b v)) : AtomicCStar d) :
      AtomicOperators d) = w.eval (atomicLeft d i) (fun v => atomicLeft d j (b v)) := by
  induction w with
  | single v => rfl
  | double v a u => rfl
  | flank v a w c u ih =>
    change atomicLeft d j (b v) * atomicLeft d i a *
      (↑(w.eval (atomicEmbedding d i) (fun v => atomicEmbedding d j (b v))) : AtomicOperators d) *
      atomicLeft d i c * atomicLeft d j (b u) = _
    rw [ih]
    rfl

variable {Δ : Type*} [CStarAlgebra Δ] (c : AtomicAmalgamData (Δ := Δ) d)
include hij hb hK in

theorem atomicExpectation_core_zero (w : BridgeCore (A i)) (hw : w.Centered K) :
    atomicExpectation d c i
      (w.eval (atomicEmbedding d i) (fun v => atomicEmbedding d j (b v))) = 0 := by
  apply cyclicRepresentation_injective
    (ambientFactor (atomicCStarAlgebra d) (atomicEmbedding d) i)
    (atomicVacuum d c.base) (atomicFactor_separating d c.base c.weights i)
  rw [map_zero]
  change cyclicRepresentation _ _ (factorExpectation _ _ _ _ _ _ _ _ _ _ i _) = 0
  refine (factorExpectation_rep _ _ _ _ _ _ _ _ _ _ i _).trans ?_
  apply operatorCompression_zero_of_dense _
    (cyclicOrbit (ambientFactor (atomicCStarAlgebra d) (atomicEmbedding d) i)
      (atomicVacuum d c.base))
    (cyclicOrbit_dense _ _)
  intro a z
  change inner ℂ (atomicLeft d i a (atomicVacuum d c.base))
    ((↑(w.eval (atomicEmbedding d i) (fun v => atomicEmbedding d j (b v))) : AtomicOperators d)
      (atomicLeft d i z (atomicVacuum d c.base))) = 0
  rw [atomicCore_coe]
  exact atomicCore_coefficient_zero d hij b hb K hK c.base w hw a z

include hij hb hK in
theorem atomicExpectation_sandwich_core_zero (w : BridgeCore (A i))
    (hw : w.Centered K) (a z : A i) :
    atomicExpectation d c i (atomicEmbedding d i a *
      w.eval (atomicEmbedding d i) (fun v => atomicEmbedding d j (b v)) *
      atomicEmbedding d i z) = 0 := by
  rw [atomicExpectation_mul_factor,atomicExpectation_factor_mul,
    atomicExpectation_core_zero d hij b hb K hK c w hw,mul_zero,zero_mul]

end

open scoped CStarAlgebra ComplexOrder
namespace PeakingPairData
attribute [local instance] matrixFamilyStarOrder modelPartialOrder modelStarOrderedRing
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (B : PeakingPairData A)

def turnCentered (i : Bool) (a : A) : Prop := (B.input false).expectation (!i) a = 0

theorem turn_matrix_centered (i j : Bool) (a : A)
    (h : i = j ∨ B.turnCentered i a) :
    B.expectation (matrixSingle (!i) j a) = 0 := by
  ext k x
  change (matrixDiagonalExpectation (B.input false).expectation (B.input false).bound
    (matrixSingle (!i) j a)) k x = 0
  rw [matrixDiagonalExpectation_apply,matrixSingle_apply]
  by_cases he : (!i) = k ∧ j = k
  · rw [ite_eq_left he]
    have hj : i ≠ j := by
      rw [he.2,← he.1]
      cases i <;> decide
    have hc := h.resolve_left hj
    change (B.input false).expectation (!i) a = 0 at hc
    rw [← he.1,hc]
    rfl
  · rw [ite_eq_right he,map_zero]
    rfl

end PeakingPairData

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra
section
variable {A D Z : Type*} [CStarAlgebra A] [CStarAlgebra D] [CStarAlgebra Z]
  [PartialOrder A] [StarOrderedRing A] [PartialOrder D] [StarOrderedRing D]
  (φ : CStarMatrix Bool Bool A →⋆ₐ[ℂ] Z) (ψ : CStarMatrix Bool Bool D →⋆ₐ[ℂ] Z)
  (δ : Bool → D →⋆ₐ[ℂ] A)
  (hd : ∀ x, φ (matrixDiagonalHom δ x) =
    ψ (matrixDiagonalHom (fun _ => StarAlgHom.id ℂ D) x))

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder D] [StarOrderedRing D] in

theorem matrixCornerLetter_diagonal (i : Bool) (d : D) :
    matrixCornerLetter φ ψ (matrixDiagonal_units φ ψ δ hd) i *
      matrixCornerBase φ (δ (!i) d) *
      matrixCornerLetter φ ψ (matrixDiagonal_units φ ψ δ hd) (!i) =
        matrixCornerBase φ (δ i d) :=
  hnn_reverse_conjugacy (matrixCornerBase φ).toRingHom (fun i => (δ i).toRingHom)
    (matrixCornerLetter φ ψ (matrixDiagonal_units φ ψ δ hd))
    (matrixStable_star_mul φ ψ (matrixDiagonal_units φ ψ δ hd))
    (matrixStable_conjugates φ ψ δ hd) i d

end

open scoped CStarAlgebra ComplexOrder
namespace PeakingPairData
attribute [local instance] matrixFamilyStarOrder modelPartialOrder modelStarOrderedRing
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (B : PeakingPairData A)

def turnCenter (i : Bool) (a : A) : A :=
  a-B.diagonal (!i) ((B.input false).expectation (!i) a)

def turnRemainder (i : Bool) (a : A) : A :=
  B.diagonal i ((B.input false).expectation (!i) a)

end PeakingPairData

open Topology
open scoped CStarAlgebra ComplexOrder

open Topology
open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder InnerProductSpace ComplexStarModule

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

open scoped CStarAlgebra ComplexOrder InnerProductSpace

open scoped CStarAlgebra ComplexOrder InnerProductSpace

open scoped CStarAlgebra ComplexOrder

open scoped ComplexOrder

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder InnerProductSpace
open UniformSpace

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder

open Topology

open scoped CStarAlgebra ComplexOrder

open Topology

open Topology

open Topology

open Filter Topology
open scoped InnerProductSpace ComplexOrder ComplexStarModule CStarAlgebra

open Topology

open scoped CStarAlgebra ComplexOrder

open Filter Topology
open scoped CStarAlgebra ComplexOrder

open Topology
open scoped CStarAlgebra ComplexOrder

section
namespace HNNWord
variable {A B C : Type*}

def lastCoefficient : HNNWord A → A
  | .single _ a => a
  | .cons _ _ w => w.lastCoefficient

def mapCoefficients (φ : A → B) : HNNWord A → HNNWord B
  | .single i a => .single i (φ a)
  | .cons i a w => .cons i (φ a) (w.mapCoefficients φ)

@[simp] theorem first_mapCoefficients (φ : A → B) (w : HNNWord A) :
    (w.mapCoefficients φ).first = w.first := by cases w <;> rfl

@[simp] theorem last_mapCoefficients (φ : A → B) (w : HNNWord A) :
    (w.mapCoefficients φ).lastCoefficient = φ w.lastCoefficient := by
  induction w with
  | single i a => rfl
  | cons i a w ih => exact ih

theorem mapCoefficients_reduced (φ : A → B) (K : Bool → A → Prop) (L : Bool → B → Prop)
    (h : ∀ i a, K i a → L i (φ a)) (w : HNNWord A) (hw : w.Reduced K) :
    (w.mapCoefficients φ).Reduced L := by
  induction w with
  | single i a => trivial
  | cons i a w ih =>
    exact ⟨hw.1.imp (fun hh => by simpa only [first_mapCoefficients] using hh) (h i a),ih hw.2⟩

theorem eval_mapCoefficients [Mul C] (φ : A → B) (ψ : B → C) (v : Bool → C)
    (w : HNNWord A) : (w.mapCoefficients φ).eval ψ v = w.eval (ψ ∘ φ) v := by
  induction w with
  | single i a => rfl
  | cons i a w ih => simp only [mapCoefficients,eval,ih]; rfl

def join [Mul B] : HNNWord B → B → HNNWord B → HNNWord B
  | .single i a, b, z => .cons i (a*b) z
  | .cons i a w, b, z => .cons i a (w.join b z)

@[simp] theorem first_join [Mul B] (w z : HNNWord B) (b : B) :
    (w.join b z).first = w.first := by cases w <;> rfl

@[simp] theorem last_join [Mul B] (w z : HNNWord B) (b : B) :
    (w.join b z).lastCoefficient = z.lastCoefficient := by
  induction w with
  | single i a => rfl
  | cons i a w ih => exact ih

end HNNWord

end

open Topology
open scoped CStarAlgebra ComplexOrder

open Filter Topology
open scoped CStarAlgebra ComplexOrder OnePoint
namespace PeakingPairData
variable {A C : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  (B : PeakingPairData A) (D : PeakingPairData C)

theorem peakAtom_separates (i : Bool) (a b : A)
    (h : ∀ n, peakAtom (B.peak i) n*a = peakAtom (B.peak i) n*b) : a = b :=
  ((B.input false).data i).separating a b h

theorem diagonal_atom (i : Bool) (g : SequenceDiagonal) (n : ℕ) :
    peakAtom (B.peak i) n*B.diagonal i g = g n • peakAtom (B.peak i) n :=
  (B.input false).atom_mul i g n

theorem expectation_nat (i : Bool) (a : A) (n : ℕ) :
    (B.input false).expectation i a n =
      (B.trace (peakAtom (B.peak i) n)).re⁻¹ •
        B.trace (peakAtom (B.peak i) n*a*peakAtom (B.peak i) n) := rfl

theorem expectation_infty (i : Bool) (a : A) :
    (B.input false).expectation i a ∞ = B.state i a := rfl

variable (ι : A →⋆ₐ[ℂ] C) (hp : ∀ i n, ι (B.peak i n) = D.peak i n)

include hp in
theorem atom_natural (i : Bool) (n : ℕ) :
    ι (peakAtom (B.peak i) n) = peakAtom (D.peak i) n := by
  simp only [peakAtom,map_sub,hp]

include hp in
theorem diagonal_natural (i : Bool) (g : SequenceDiagonal) :
    ι (B.diagonal i g) = D.diagonal i g := by
  apply D.peakAtom_separates i
  intro n
  rw [← B.atom_natural D ι hp i n,← map_mul,B.diagonal_atom,map_smul,
    B.atom_natural D ι hp,D.diagonal_atom]

end PeakingPairData

open Topology

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

open Topology
open scoped ComplexOrder

open Topology
open scoped CStarAlgebra ComplexOrder

open Topology
open scoped CStarAlgebra ComplexOrder

open Topology
open scoped CStarAlgebra ComplexOrder

open Topology
namespace PeakingPairData
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (B Q : PeakingPairData A)

theorem separated_of_inequivalent
    (hn : ¬ PureStateEquivalent (B.state false) (B.peaks false).isPureState
      (B.state true) (B.peaks true).isPureState) : B.Separated := by
  intro i j hij h
  cases i <;> cases j
  · exact hij rfl
  · exact hn (matrix_pure_equivalence_reflects _ _ (B.peaks false).isPureState
      (B.peaks true).isPureState false true h)
  · exact hn (matrix_pure_equivalence_reflects _ _ (B.peaks false).isPureState
      (B.peaks true).isPureState false true h.symm)
  · exact hij rfl

end PeakingPairData

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

section
-- module Solutions.OAIQ115_Naimark.Naimark_CAR
attribute [-instance] _root_.OAI.NaimarkZFC.constructionIndex_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace NaimarkZFC

open scoped CStarAlgebra

open scoped ComplexOrder CStarAlgebra

open scoped ComplexOrder CStarAlgebra

def carStageTrace : ∀ n, {τ : CARStage n →L[ℂ] ℂ // IsState τ} :=
  Nat.rec ⟨ContinuousLinearMap.id ℂ ℂ,complex_identity_isState⟩ (fun _ T =>
    ⟨matrixTraceState T.1 T.2,matrixTraceState_isState T.1 T.2⟩)

@[simp] theorem carStageTrace_zero (z : ℂ) : (carStageTrace 0).1 z = z := rfl

@[simp] theorem carStageTrace_succ (n : ℕ) (M : CARStage (n+1)) :
    (carStageTrace (n+1)).1 M = matrixTraceState (carStageTrace n).1 (carStageTrace n).2 M := rfl

theorem carStageTrace_step (n : ℕ) (a : CARStage n) :
    (carStageTrace (n+1)).1 (carStep n a) = (carStageTrace n).1 a := by
  change (2:ℝ)⁻¹ • (∑ i : Bool, (carStageTrace n).1 (matrixScalarHom _ a i i)) = _
  simp only [matrixScalarHom_entry,Fintype.sum_bool,← two_smul ℝ]
  rw [smul_smul,inv_mul_cancel₀ (by norm_num : (2:ℝ) ≠ 0),one_smul]

theorem carStageTrace_compatible (n m : ℕ) (hnm : n ≤ m) (a : CARStage n) :
    (carStageTrace m).1 (carBond n m hnm a) = (carStageTrace n).1 a := by
  induction hnm with
  | refl => rw [carBond_self]; rfl
  | @step m h ih => rw [carBond_succ n m h,StarAlgHom.comp_apply,carStageTrace_step,ih]

def carTrace : CAR →L[ℂ] ℂ := cstarDirectLimitState CARStage carBond
  (fun n => (carStageTrace n).1) (fun n => (carStageTrace n).2) carStageTrace_compatible

@[simp] theorem carTrace_stage (n : ℕ) (a : CARStage n) :
    carTrace (carInclude n a) = (carStageTrace n).1 a := cstarDirectLimitState_stage _ _ _ _ _ n a

def carStageVector : ∀ n, {f : CARStage n →L[ℂ] ℂ // IsState f} :=
  Nat.rec ⟨ContinuousLinearMap.id ℂ ℂ,complex_identity_isState⟩ (fun _ f =>
    ⟨matrixState f.1 false,matrixState_isState f.1 f.2 false⟩)

theorem carStageVector_step (n : ℕ) (a : CARStage n) :
    (carStageVector (n+1)).1 (carStep n a) = (carStageVector n).1 a := by
  exact congrArg (carStageVector n).1 (matrixScalarHom_entry _ a false)

theorem carStageVector_compatible (n m : ℕ) (hnm : n ≤ m) (a : CARStage n) :
    (carStageVector m).1 (carBond n m hnm a) = (carStageVector n).1 a := by
  induction hnm with
  | refl => rw [carBond_self]; rfl
  | @step m h ih => rw [carBond_succ n m h,StarAlgHom.comp_apply,carStageVector_step,ih]

def carVector : CAR →L[ℂ] ℂ := cstarDirectLimitState CARStage carBond
  (fun n => (carStageVector n).1) (fun n => (carStageVector n).2) carStageVector_compatible

@[simp] theorem carVector_stage (n : ℕ) (a : CARStage n) :
    carVector (carInclude n a) = (carStageVector n).1 a := cstarDirectLimitState_stage _ _ _ _ _ n a

open scoped ComplexOrder CStarAlgebra

def carStagePeak : ∀ n, CARStage n
  | 0 => 1
  | n+1 => matrixSingle false false (carStagePeak n)

@[simp] theorem carStageVector_peak (n : ℕ) : (carStageVector n).1 (carStagePeak n) = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (carStageVector n).1 (matrixSingle false false (carStagePeak n) false false) = 1
    simpa only [matrixSingle_apply, and_self, eq_self_iff_true, ite_true, if_true] using ih

@[simp] theorem carStageTrace_peak (n : ℕ) : (carStageTrace n).1 (carStagePeak n) = (2:ℂ)⁻¹^n := by
  induction n with
  | zero => change (1:ℂ) = (2:ℂ)⁻¹^0; simp
  | succ n ih =>
    rw [carStageTrace_succ]
    change matrixTraceState (carStageTrace n).1 (carStageTrace n).2
      (matrixSingle false false (carStagePeak n)) = _
    rw [matrixTraceState_single,ih]
    norm_num [pow_succ,Complex.real_smul]
    ring

def carPeak (n : ℕ) : CAR := carInclude n (carStagePeak n)

@[simp] theorem carPeak_zero : carPeak 0 = 1 := map_one _

@[simp] theorem carVector_peak (n : ℕ) : carVector (carPeak n) = 1 := by
  rw [carPeak,carVector_stage,carStageVector_peak]

@[simp] theorem carTrace_peak (n : ℕ) : carTrace (carPeak n) = (2:ℂ)⁻¹^n := by
  rw [carPeak,carTrace_stage,carStageTrace_peak]

open scoped ComplexOrder CStarAlgebra

open scoped ComplexOrder CStarAlgebra

open Filter Topology
open scoped ComplexOrder CStarAlgebra

end NaimarkZFC

end

end OAI
end

section
-- module Solutions.OAIQ115_Naimark.Naimark_Dependencies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace NaimarkZFC

open Topology

open Filter Topology
open scoped CStarAlgebra ComplexOrder InnerProductSpace

open Topology

open Topology
open scoped CStarAlgebra ComplexOrder

open scoped ComplexOrder CStarAlgebra

open scoped ComplexOrder CStarAlgebra InnerProductSpace

open Filter Topology
open scoped CStarAlgebra
section
namespace HNNWord
variable {A C : Type*} [CStarAlgebra A] [CStarAlgebra C]

def AllCoefficients (S : Set A) : HNNWord A → Prop
  | .single _ a => a ∈ S
  | .cons _ a w => a ∈ S ∧ w.AllCoefficients S

end HNNWord

end

open Topology
open scoped CStarAlgebra ComplexOrder

open Filter Topology

open Filter Topology

open Filter Topology
open scoped InnerProductSpace ComplexStarModule CStarAlgebra

open Filter Topology
open scoped InnerProductSpace

open Topology

open Topology

section
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {f g h : A →L[ℂ] ℂ} {hf : IsPureState f} {hg : IsPureState g} {hh : IsPureState h}

theorem PureStateEquivalent.symm (e : PureStateEquivalent f hf g hg) :
    PureStateEquivalent g hg f hf := UnitarilyEquivalent.symm e

theorem PureStateEquivalent.trans (e : PureStateEquivalent f hf g hg)
    (e' : PureStateEquivalent g hg h hh) : PureStateEquivalent f hf h hh :=
  UnitarilyEquivalent.trans e e'

end

open scoped InnerProductSpace ComplexStarModule CStarAlgebra

end NaimarkZFC

end

end OAI
end

section
-- module Solutions.OAIQ115_Naimark.Naimark_Stages
attribute [-instance] _root_.OAI.NaimarkZFC.constructionIndex_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace NaimarkZFC

open Topology
section

structure TracialStage where
  carrier : Type
  [cstar : CStarAlgebra carrier]
  [order : PartialOrder carrier]
  [starOrder : StarOrderedRing carrier]
  simple : IsSimpleCStar carrier
  trace : carrier →L[ℂ] ℂ
  traceState : IsState trace
  tracial : ∀ a b, trace (a*b) = trace (b*a)
  base : CAR →⋆ₐ[ℂ] carrier
  base_injective : Function.Injective base
  baseUEP : PureUEP base

attribute [instance] TracialStage.cstar TracialStage.order TracialStage.starOrder
instance instCoeSortTracialStageType : CoeSort TracialStage Type := ⟨TracialStage.carrier⟩

namespace TracialStage

variable (X : TracialStage)

theorem traceFaithful (a : X) (ha : a ≠ 0) : 0 < (X.trace (star a*a)).re :=
  tracialState_strictPos_of_simple X.simple X.trace X.traceState X.tracial a ha

@[ext] structure Hom (X Y : TracialStage) where
  map : X →⋆ₐ[ℂ] Y
  injective : Function.Injective map
  trace_map : ∀ a, Y.trace (map a) = X.trace a
  base_map : ∀ a, map (X.base a) = Y.base a
  uep : PureUEP map

end TracialStage
end

open scoped CStarAlgebra ComplexOrder

open scoped InnerProductSpace

open scoped InnerProductSpace

open scoped InnerProductSpace

open scoped InnerProductSpace ComplexStarModule CStarAlgebra

open scoped InnerProductSpace

open scoped InnerProductSpace

open scoped InnerProductSpace

open scoped InnerProductSpace ComplexStarModule

open scoped InnerProductSpace

open scoped InnerProductSpace

open scoped InnerProductSpace

open scoped InnerProductSpace CStarAlgebra

open scoped InnerProductSpace

open scoped InnerProductSpace

open scoped InnerProductSpace

end NaimarkZFC

end

end OAI
end

section
-- module Solutions.OAIQ115_Naimark.Naimark_Omission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace NaimarkZFC

open Topology
open scoped CStarAlgebra ComplexOrder

namespace HNNWord
variable {A D I : Type*}

theorem AllCoefficients.mono {S T : Set A} (hst : S ⊆ T)
    (w : HNNWord A) (hw : w.AllCoefficients S) : w.AllCoefficients T := by
  induction w with
  | single i a => exact hst hw
  | cons i a w ih => exact ⟨hst hw.1,ih hw.2⟩

end HNNWord

open Topology
open scoped CStarAlgebra ComplexOrder

open Topology

open Topology
open scoped CStarAlgebra ComplexOrder

open Topology

open Topology

open Topology

open Topology

open Topology

open Topology
namespace PeakingPairData

section
universe u
attribute [local instance] ambientSubalgebraOrder ambientSubalgebraStarOrder
variable {A : Type} [CStarAlgebra A] [partialOrderA : PartialOrder A] [starOrderedRingA : StarOrderedRing A]

omit partialOrderA starOrderedRingA in
lemma subalgebra_simple_congr [PartialOrder A] [StarOrderedRing A] (S T : StarSubalgebra ℂ A)
    [IsClosed (S : Set A)] [IsClosed (T : Set A)] (h : S = T) :
    IsSimpleCStar S ↔ IsSimpleCStar T := by subst T; rfl

end

end PeakingPairData

open Topology

open Topology

open Topology

open Topology

open Topology

open Topology

open Cardinal Topology TopologicalSpace

open Cardinal Topology TopologicalSpace

end NaimarkZFC

end

end OAI
end


