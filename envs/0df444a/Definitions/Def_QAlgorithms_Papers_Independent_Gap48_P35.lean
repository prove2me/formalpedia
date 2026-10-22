-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P35
-- name    : QAlgorithms_Papers_Independent_Gap48_P35
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-22T04:48:58.336784+00:00
-- url     : https://prove2.me/theorems/37bcb7ed-9eed-49ab-81d8-47dd946e72e5
-- title:
--   Definitions for Monogamy of entanglement and other correlations
-- statement:
--   The objects the formalized statements of *Monogamy of entanglement and other correlations* (arXiv:quant-ph/0310037) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `finiteBasis`: PDF pp.1--2: identify each finite local basis with Fin(card), using the same equivalences for rows and columns. This changes no tensor ownership.
--   - `finiteSystemPreparationCost`: PDF pp.1--2: the accepted operational two-way singlet preparation cost. The fixed-basis adapter allows arbitrary finite local basis types.
--   - `commonLeft`: PDF pp.2,4: net common randomness with communication B to A. The accepted total optimizes C-R over finite nonnegative communication rates R. It uses entropy of the generated key and vanishing agreement error, with a uniform exponential key-alphabet bound. No initially shared randomness is supplied.
--   - `distillLeft`: PDF p.4: one-way EPR distillation with communication B to A, obtained by swapping the inputs of the accepted forward operational capacity.
--   - `distillTwoWay`: PDF p.6: two-way EPR distillation, with the accepted actual finite LOCC protocols, normalized EPR targets and vanishing fidelity error.
--   - `keyLeft`: PDF pp.4--5: one-way secret key B to A, secret against E and the public transcript. Reindex only the two legitimate parties of the accepted operational capacity. This is not the measurement-only expression printed on p.5.
--   - `BComplement`: PDF p.2: sigma is B-complement to rho precisely when both are marginals of one normalized pure state on A,B,C. C is the source's Bprime.
--   - `classicalCorrelationDeficit`: PDF p.3: the specified loss of net common randomness when B is discarded. Both rates are real-valued accepted operational rates; no EReal.toReal occurs.
--   - `forwardOutput`: PDF p.3: a sender instrument and a receiver channel controlled only by its public outcome. Hidden Kraus indices remain private and are summed out.
--   - `ForwardFormationRate`: PDF pp.1,3: actual one-way singlet formation feasibility. This is the accepted unrestricted finite-block definition with its LOCC map restricted to one sender instrument and a transcript-dependent receiver channel. Positive block lengths, unconditional output, local ancillas and disposal are retained.
--   - `forwardCost`: PDF p.3: A-to-B singlet formation cost, defined by the restricted operational protocols, independently of the unrestricted cost. For finite physical states the feasible set is nonempty (teleportation) and bounded below by zero. B-to-A cost is this definition applied to the swapped state.
--   - `dropC`: PDF p.5, Eq.(12): trace C out, retaining A,B,E in that order.
--   - `groupACBE`: PDF p.5: A,C,(B,E), giving B as well as E to the eavesdropper. This is a permutation of all four systems; none is traced out.
--   - `groupABCE`: PDF p.5: A,(B,C),E, grouping B,C into one legitimate party.
--   - `threeQutritAlternatingVector`: PDF p.4: the displayed three-qutrit alternating vector, with printed indices 1,2,3 represented by Lean indices 0,1,2.
-- source:
--   Monogamy of entanglement and other correlations, arXiv:quant-ph/0310037v1, https://arxiv.org/abs/quant-ph/0310037v1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P08
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P07
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P19
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P42
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P12
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P12

/-!
Koashi--Winter, arXiv:quant-ph/0310037v1, PDF pp.1--6.
Finite nonzero complex systems, entropy in bits, operational iid vanishing-error
rates, and no initial shared resource beyond the supplied state.
The two-way public-discussion key sandwich is deferred in HARD.md.
Compilation is pending the batch handoff.
-/

namespace QAlgorithms.Papers.Independent.Gap48.P35

open scoped Matrix ComplexConjugate ComplexOrder
open Filter Topology
open Information100.P21 (Op)
open Information100.P08 (IsPure formation measuredCorrelation)
open Dependency50.P19 (marginalRA marginalRB)

noncomputable section

/-- PDF pp.1--2: identify each finite local basis with Fin(card), using the
same equivalences for rows and columns. This changes no tensor ownership. -/
def finiteBasis {A B : Type} [Fintype A] [Fintype B] (rho : Op (A × B)) :
    Op (Fin (Fintype.card A) × Fin (Fintype.card B)) :=
  fun x y => rho ((Fintype.equivFin A).symm x.1, (Fintype.equivFin B).symm x.2)
    ((Fintype.equivFin A).symm y.1, (Fintype.equivFin B).symm y.2)

/-- PDF pp.1--2: the accepted operational two-way singlet preparation cost.
The fixed-basis adapter allows arbitrary finite local basis types. -/
def finiteSystemPreparationCost {A B : Type} [Fintype A] [Fintype B] (rho : Op (A × B)) : ℝ :=
  Dependency50.P42.entanglementCost Dependency50.P42.halfTraceDistance (finiteBasis rho)

/-- PDF pp.2,4: net common randomness with communication B to A. The accepted
total optimizes C-R over finite nonnegative communication rates R. It uses
entropy of the generated key and vanishing agreement error, with a uniform
exponential key-alphabet bound. No initially shared randomness is supplied. -/
def commonLeft {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (rho : Op (A × B)) : ℝ :=
  Dependency50.P07.total (Dependency50.P19.flip rho)

/-- PDF p.4: one-way EPR distillation with communication B to A, obtained
by swapping the inputs of the accepted forward operational capacity. -/
def distillLeft {A B : Type} [Fintype A] [Fintype B] (rho : Op (A × B)) : ℝ :=
  Frontier30.P12.entCapacity (Dependency50.P19.flip rho)

/-- PDF p.6: two-way EPR distillation, with the accepted actual finite LOCC
protocols, normalized EPR targets and vanishing fidelity error. -/
def distillTwoWay {A B : Type} [Fintype A] [Fintype B] (rho : Op (A × B)) : ℝ :=
  Frontier30.P12.twoWayCapacity (finiteBasis rho)

/-- PDF pp.4--5: one-way secret key B to A, secret against E and the public
transcript. Reindex only the two legitimate parties of the accepted operational
capacity. This is not the measurement-only expression printed on p.5. -/
def keyLeft {A B E : Type} [Fintype A] [Fintype B] [Fintype E]
    (rho : Op (A × (B × E))) : ℝ :=
  Frontier30.P12.quantumKeyCapacity
    (fun x y => rho (x.2.1, (x.1, x.2.2)) (y.2.1, (y.1, y.2.2)))

/-- PDF p.2: sigma is B-complement to rho precisely when both are marginals
of one normalized pure state on A,B,C. C is the source's Bprime. -/
def BComplement {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
    (rho : Op (A × B)) (sigma : Op (A × C)) : Prop :=
  ∃ omega : Op (A × (B × C)), IsPure omega ∧
    marginalRA omega = rho ∧ marginalRB omega = sigma

/-- PDF p.3: the specified loss of net common randomness when B is discarded.
Both rates are real-valued accepted operational rates; no EReal.toReal occurs. -/
def classicalCorrelationDeficit {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (rho : Op (A × (B × C))) : ℝ :=
  commonLeft rho - commonLeft (marginalRB rho)

/-- PDF p.3: a sender instrument and a receiver channel controlled only by
its public outcome. Hidden Kraus indices remain private and are summed out. -/
def forwardOutput {A B C D : Type} [Fintype A] [Fintype B]
    (T : Frontier30.P12.RectangularKrausData A C)
    (R : Fin T.l → Frontier30.P12.BobChannel B D) (rho : Op (A × B)) : Op (C × D) :=
  ∑ i, ∑ j, ∑ k,
    let K := Matrix.kronecker (T.kraus i j) ((R i).kraus k)
    K * rho * Kᴴ

/-- PDF pp.1,3: actual one-way singlet formation feasibility. This is the
accepted unrestricted finite-block definition with its LOCC map restricted to
one sender instrument and a transcript-dependent receiver channel. Positive
block lengths, unconditional output, local ancillas and disposal are retained. -/
def ForwardFormationRate {a b : ℕ} (rho : Op (Fin a × Fin b)) (e : ℝ) : Prop :=
  ∀ epsilon > (0 : ℝ), ∀ delta > (0 : ℝ),
    ∃ m n : ℕ, 0 < n ∧
      ∃ T : Frontier30.P12.RectangularKrausData (Fin (2 ^ m)) (Fin (a ^ n)),
      ∃ R : Fin T.l → Frontier30.P12.BobChannel (Fin (2 ^ m)) (Fin (b ^ n)),
        T.Valid ∧ (∀ i, (R i).Valid) ∧
        |e - (m : ℝ) / (n : ℝ)| ≤ delta ∧
        traceDistance (forwardOutput T R (Dependency50.P42.singlets m))
          (Dependency50.P42.dimensionedPower rho n) ≤ epsilon

/-- PDF p.3: A-to-B singlet formation cost, defined by the restricted
operational protocols, independently of the unrestricted cost. For finite
physical states the feasible set is nonempty (teleportation) and bounded below
by zero. B-to-A cost is this definition applied to the swapped state. -/
def forwardCost {A B : Type} [Fintype A] [Fintype B] (rho : Op (A × B)) : ℝ :=
  sInf {e : ℝ | ForwardFormationRate (finiteBasis rho) e}

/-- PDF p.5, Eq.(12): trace C out, retaining A,B,E in that order. -/
def dropC {A B C E : Type} [Fintype C]
    (rho : Op (A × (B × (C × E)))) : Op (A × (B × E)) :=
  fun x y => ∑ c, rho (x.1, (x.2.1, (c, x.2.2))) (y.1, (y.2.1, (c, y.2.2)))

/-- PDF p.5: A,C,(B,E), giving B as well as E to the eavesdropper.
This is a permutation of all four systems; none is traced out. -/
def groupACBE {A B C E : Type} (rho : Op (A × (B × (C × E)))) :
    Op (A × (C × (B × E))) :=
  fun x y => rho (x.1, (x.2.2.1, (x.2.1, x.2.2.2)))
    (y.1, (y.2.2.1, (y.2.1, y.2.2.2)))

/-- PDF p.5: A,(B,C),E, grouping B,C into one legitimate party. -/
def groupABCE {A B C E : Type} (rho : Op (A × (B × (C × E)))) :
    Op (A × ((B × C) × E)) :=
  fun x y => rho (x.1, (x.2.1.1, (x.2.1.2, x.2.2)))
    (y.1, (y.2.1.1, (y.2.1.2, y.2.2)))

/-- PDF p.4: the displayed three-qutrit alternating vector, with printed
indices 1,2,3 represented by Lean indices 0,1,2. -/
def threeQutritAlternatingVector : EuclideanSpace ℂ (Fin 3 × (Fin 3 × Fin 3)) :=
  WithLp.toLp 2 fun x =>
    (Real.sqrt 6 : ℂ)⁻¹ *
      (if x = (0, (1, 2)) ∨ x = (1, (2, 0)) ∨ x = (2, (0, 1)) then 1
       else if x = (0, (2, 1)) ∨ x = (1, (0, 2)) ∨ x = (2, (1, 0)) then -1
       else 0)

/-- Sanity: swapping twice restores every matrix entry. -/
example {A B : Type} (rho : Op (A × B)) : Dependency50.P19.flip (Dependency50.P19.flip rho) = rho := rfl

/-- Sanity: relabeling uses the same chosen basis map on both matrix indices. -/
example {A B : Type} [Fintype A] [Fintype B] (rho : Op (A × B))
    (x y : A × B) : finiteBasis rho
      ((Fintype.equivFin A) x.1, (Fintype.equivFin B) x.2)
      ((Fintype.equivFin A) y.1, (Fintype.equivFin B) y.2) = rho x y := by
  simp [finiteBasis]

/-- Sanity: left common randomness is exactly the accepted forward net rate on BA. -/
example {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (rho : Op (A × B)) : commonLeft rho = Dependency50.P07.total (Dependency50.P19.flip rho) := rfl

/-- Sanity: an explicit common pure witness produces complementary marginals. -/
example {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
    (v : EuclideanSpace ℂ (A × (B × C))) (hv : ‖v‖ = 1) :
    BComplement (marginalRA (pureDensity v)) (marginalRB (pureDensity v)) :=
  ⟨pureDensity v, ⟨v, hv, rfl⟩, rfl, rfl⟩

/-- Sanity: the deficit has exactly the two source-specified terms. -/
example {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C] (rho : Op (A × (B × C))) :
    classicalCorrelationDeficit rho + commonLeft (marginalRB rho) = commonLeft rho := by
  simp [classicalCorrelationDeficit]

/-- Sanity: a one-point identity local instrument and receiver channel have
no communication cost or shared ancilla and preserve the one-point input. -/
example (rho : Op (Fin 1 × Fin 1)) :
    forwardOutput
      (⟨1, 1, fun _ _ => (1 : Op (Fin 1))⟩ : Frontier30.P12.RectangularKrausData _ _)
      (fun _ => (⟨1, fun _ => (1 : Op (Fin 1))⟩ : Frontier30.P12.BobChannel _ _)) rho = rho := by
  simp [forwardOutput, Matrix.one_kronecker_one]

/-- Sanity: at E one-dimensional the grouped input retains both B and C. -/
example {A B C E : Type} (rho : Op (A × (B × (C × E))))
    (a a2 : A) (b b2 : B) (c c2 : C) (e e2 : E) :
    groupABCE rho (a, ((b, c), e)) (a2, ((b2, c2), e2)) =
      rho (a, (b, (c, e))) (a2, (b2, (c2, e2))) := rfl

/-- Sanity: giving B to Eve retains B's off-diagonal coherences. -/
example {A B C E : Type} (rho : Op (A × (B × (C × E))))
    (a a2 : A) (b b2 : B) (c c2 : C) (e e2 : E) :
    groupACBE rho (a, (c, (b, e))) (a2, (c2, (b2, e2))) =
      rho (a, (b, (c, e))) (a2, (b2, (c2, e2))) := rfl

/-- Sanity: discarding a one-dimensional C sums its single diagonal block. -/
example {A B E : Type} (rho : Op (A × (B × (Fin 1 × E))))
    (x y : A × (B × E)) :
    dropC rho x y = rho (x.1, (x.2.1, (0, x.2.2)))
      (y.1, (y.2.1, (0, y.2.2))) := by simp [dropC]

/-- Sanity: the printed |123> amplitude is positive. -/
example : threeQutritAlternatingVector (0, (1, 2)) = (Real.sqrt 6 : ℂ)⁻¹ := by
  norm_num [threeQutritAlternatingVector]

/-- Sanity: the printed |213> amplitude is negative. -/
example : threeQutritAlternatingVector (1, (0, 2)) = -(Real.sqrt 6 : ℂ)⁻¹ := by
  have hpositive : ¬ (((1 : Fin 3), ((0 : Fin 3), (2 : Fin 3))) = (0, (1, 2)) ∨
      ((1 : Fin 3), ((0 : Fin 3), (2 : Fin 3))) = (1, (2, 0)) ∨
      ((1 : Fin 3), ((0 : Fin 3), (2 : Fin 3))) = (2, (0, 1))) := by decide
  have hnegative : (((1 : Fin 3), ((0 : Fin 3), (2 : Fin 3))) = (0, (2, 1)) ∨
      ((1 : Fin 3), ((0 : Fin 3), (2 : Fin 3))) = (1, (0, 2)) ∨
      ((1 : Fin 3), ((0 : Fin 3), (2 : Fin 3))) = (2, (1, 0))) := by decide
  change (Real.sqrt 6 : ℂ)⁻¹ *
    (if ((1 : Fin 3), ((0 : Fin 3), (2 : Fin 3))) = (0, (1, 2)) ∨
        ((1 : Fin 3), ((0 : Fin 3), (2 : Fin 3))) = (1, (2, 0)) ∨
        ((1 : Fin 3), ((0 : Fin 3), (2 : Fin 3))) = (2, (0, 1)) then 1
     else if ((1 : Fin 3), ((0 : Fin 3), (2 : Fin 3))) = (0, (2, 1)) ∨
        ((1 : Fin 3), ((0 : Fin 3), (2 : Fin 3))) = (1, (0, 2)) ∨
        ((1 : Fin 3), ((0 : Fin 3), (2 : Fin 3))) = (2, (1, 0)) then -1
     else 0) = -(Real.sqrt 6 : ℂ)⁻¹
  rw [if_neg hpositive, if_pos hnegative, mul_neg_one]

/-- Sanity: the one-point identity sender instrument is complete. -/
example : (⟨1, 1, fun _ _ => (1 : Op (Fin 1))⟩ :
    Frontier30.P12.RectangularKrausData (Fin 1) (Fin 1)).Valid := by
  simp [Frontier30.P12.RectangularKrausData.Valid] <;>
    ext i j <;> simp [Matrix.one_apply, Subsingleton.elim i j]

/-- Sanity: the one-point identity receiver channel is trace preserving. -/
example : (⟨1, fun _ => (1 : Op (Fin 1))⟩ :
    Frontier30.P12.BobChannel (Fin 1) (Fin 1)).Valid := by
  simp [Frontier30.P12.BobChannel.Valid, IsKrausFamily] <;>
    ext i j <;> simp [Matrix.one_apply, Subsingleton.elim i j]

end

end QAlgorithms.Papers.Independent.Gap48.P35


