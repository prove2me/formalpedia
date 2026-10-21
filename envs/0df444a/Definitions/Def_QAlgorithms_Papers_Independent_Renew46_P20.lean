-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P20
-- name    : QAlgorithms_Papers_Independent_Renew46_P20
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T20:22:37.735157+00:00
-- url     : https://prove2.me/theorems/2fc984a7-b9fd-4664-815b-5275e0650b4f
-- title:
--   Definitions for Realization schemes for quantum instruments in finite dimensions
-- statement:
--   The objects the formalized statements of *Realization schemes for quantum instruments in finite dimensions* (arXiv:0810.3211) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `frameOperator`: PDF p.17, Eq.(84): the genuine Bochner integral of the frame projectors. Use only with the explicit integrability hypothesis carried by the statements.
--   - `aliceLift`: PDF p.18, Eq.(89): lift Alice's joint effect to Bob ⊗ Alice ⊗ input. The grouping is ((Bob, Alice), input), with no implicit wire permutation.
--   - `traceAlice`: PDF p.18, Eq.(89): partial trace discarding both Alice registers.
--   - `teleportRaw`: PDF pp.18,20, Eqs.(89),(98): the physical unnormalized output before Bob's conditional channel, with shared resource R and Alice effect E.
--   - `idealResource`: PDF p.20, Eq.(98): shared maximally entangled density, divided by d once.
--   - `bellEffectDensity`: PDF pp.19–20, Eqs.(93),(98): Bell POVM density d |U^T⟩⟩⟨⟨U^T|. The vector being vectorized is not normalized. This is distinct from the frozen two-qubit state Information100.P48.bellDensity.
-- source:
--   Realization schemes for quantum instruments in finite dimensions, arXiv:0810.3211v4, https://arxiv.org/abs/0810.3211v4

import Mathlib
import Definitions.Def_QAlgorithms_Defs_ContinuousPOVMDensities
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P40

/-!
Statements from Chiribella, D'Ariano and Perinotti, arXiv:0810.3211v4.
The tensor basis is output first, input second; vectorization is unnormalized.
Only the two nodes recorded in items.json are stated. Other nodes are explicitly
accounted for in HARD.md and GAPS.json. Compilation is pending the batch handoff.
-/

noncomputable section

open MeasureTheory
open scoped ComplexConjugate ComplexOrder Matrix Matrix.Norms.L2Operator

open QAlgorithms.Papers.Independent.Dependency50.P40 (operatorKet)

namespace QAlgorithms.Papers.Independent.Renew46.P20

/-- PDF p.17, Eq.(84): the genuine Bochner integral of the frame projectors.
Use only with the explicit integrability hypothesis carried by the statements. -/
def frameOperator {I W : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace W]
    (mu : Measure W) (A : W → Matrix I I ℂ) : Matrix (I × I) (I × I) ℂ :=
  ∫ w, pureDensity (operatorKet (A w)) ∂mu

/-- PDF p.18, Eq.(89): lift Alice's joint effect to Bob ⊗ Alice ⊗ input.
The grouping is ((Bob, Alice), input), with no implicit wire permutation. -/
def aliceLift {O A I : Type*} [DecidableEq O]
    (E : Matrix (A × I) (A × I) ℂ) :
    Matrix ((O × A) × I) ((O × A) × I) ℂ :=
  fun p q => if p.1.1 = q.1.1 then E (p.1.2, p.2) (q.1.2, q.2) else 0

/-- PDF p.18, Eq.(89): partial trace discarding both Alice registers. -/
def traceAlice {O A I : Type*} [Fintype A] [Fintype I]
    (X : Matrix ((O × A) × I) ((O × A) × I) ℂ) : Matrix O O ℂ :=
  fun b c => ∑ a, ∑ i, X ((b, a), i) ((c, a), i)

/-- PDF pp.18,20, Eqs.(89),(98): the physical unnormalized output before Bob's
conditional channel, with shared resource R and Alice effect E. -/
def teleportRaw {O A I : Type*} [Fintype O] [Fintype A] [Fintype I]
    [DecidableEq O] (R : Matrix (O × A) (O × A) ℂ)
    (E : Matrix (A × I) (A × I) ℂ) (rho : Matrix I I ℂ) : Matrix O O ℂ :=
  traceAlice (Matrix.kronecker R rho * aliceLift E)

/-- PDF p.20, Eq.(98): shared maximally entangled density, divided by d once. -/
def idealResource (I : Type*) [Fintype I] [DecidableEq I] :
    Matrix (I × I) (I × I) ℂ :=
  (Fintype.card I : ℂ)⁻¹ • pureDensity (operatorKet (1 : Matrix I I ℂ))

/-- PDF pp.19–20, Eqs.(93),(98): Bell POVM density d |U^T⟩⟩⟨⟨U^T|.
The vector being vectorized is not normalized. This is distinct from the frozen
two-qubit state Information100.P48.bellDensity. -/
def bellEffectDensity {I : Type*} [Fintype I] (U : Matrix I I ℂ) :
    Matrix (I × I) (I × I) ℂ :=
  (Fintype.card I : ℂ) • pureDensity (operatorKet U.transpose)

/-- Coordinate sanity: vectorization preserves the output-input matrix entry. -/
example {I O : Type*} (A : Matrix O I ℂ) (o : O) (i : I) :
    operatorKet A (o, i) = A o i := by
  rfl

/-- One-dimensional sanity: the unnormalized identity ket has coefficient one. -/
example : operatorKet (1 : Matrix Unit Unit ℂ) ((), ()) = 1 := by
  simp [operatorKet]

/-- Wire-order sanity: the lifted effect is the identity on Bob. -/
example {O A I : Type*} [DecidableEq O] (E : Matrix (A × I) (A × I) ℂ)
    (b : O) (a c : A) (i j : I) :
    aliceLift E ((b, a), i) ((b, c), j) = E (a, i) (c, j) := by
  simp [aliceLift]

/-- Partial-trace sanity: a zero joint operator produces a zero output. -/
example {O A I : Type*} [Fintype A] [Fintype I] :
    traceAlice (0 : Matrix ((O × A) × I) ((O × A) × I) ℂ) = 0 := by
  ext b c
  simp [traceAlice]

/-- Frame-integral sanity: the zero operator family has zero frame operator. -/
example {I W : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace W]
    (mu : Measure W) :
    frameOperator mu (fun _ => (0 : Matrix I I ℂ)) = 0 := by
  have hzero : pureDensity (operatorKet (0 : Matrix I I ℂ)) = 0 := by
    ext p q
    simp [pureDensity, operatorKet]
  simp [frameOperator, hzero]

/-- Bell-density sanity: a zero coefficient vector contributes the zero effect. -/
example {I : Type*} [Fintype I] : bellEffectDensity (0 : Matrix I I ℂ) = 0 := by
  ext p q
  simp [bellEffectDensity, operatorKet, pureDensity]

/-- Physical-contraction sanity: a zero resource gives a zero output. -/
example {O A I : Type*} [Fintype O] [Fintype A] [Fintype I]
    [DecidableEq O] (E : Matrix (A × I) (A × I) ℂ) (rho : Matrix I I ℂ) :
    teleportRaw (0 : Matrix (O × A) (O × A) ℂ) E rho = 0 := by
  ext b c
  simp [teleportRaw, traceAlice]

/-- One-dimensional resource sanity: its only matrix entry is one. -/
example : idealResource Unit ((), ()) ((), ()) = 1 := by
  simp [idealResource, pureDensity, operatorKet]

end QAlgorithms.Papers.Independent.Renew46.P20


