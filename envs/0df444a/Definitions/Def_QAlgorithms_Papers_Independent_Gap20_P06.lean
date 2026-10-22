-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P06
-- name    : QAlgorithms_Papers_Independent_Gap20_P06
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-21T20:15:31.60033+00:00
-- url     : https://prove2.me/theorems/73d677e5-94ee-4b75-aed9-88ff9b524edc
-- title:
--   Definitions for Quantum data processing and error correction
-- statement:
--   The objects the formalized statements of *Quantum data processing and error correction* (arXiv:quant-ph/9604022) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `inputEntanglementFidelity`: PDF p.6, Eq.(1): squared pure-state overlap with the original purification.
--   - `dilationChannel`: PDF pp.3--5: the Q channel computed from a fixed unitary and pure ancillary vector. Theorems require norm eta = 1; U is unitary by its type.
--   - `environmentOutput`: PDF pp.5,9--10: environment output computed from the same unitary dilation.
--   - `dilatedVector`: PDF p.5: actual final pure vector, coordinates ordered R,(Q,E).
--   - `referenceEnvironment`: PDF pp.9--10: trace out Q from the actual RQE output, keeping all RE coherences.
--   - `ketBra`: PDF p.15: the rank-one operator |u><v|; conjugation is on the bra.
--   - `recoveryOperators`: PDF pp.15--16: None is the extra complement branch, and Some j is the jth Schmidt branch. This avoids the printed collision between A_0 and an l index.
--   - `middleSuperop`: PDF pp.16--17: id_R tensor f tensor id_E, on every matrix block.
--   - `appendEnvironment`: PDF p.17: X_RQ tensor Y_E in the same R,(Q,E) coordinates as dilatedVector.
-- source:
--   Quantum data processing and error correction, arXiv:quant-ph/9604022v1, https://arxiv.org/abs/quant-ph/9604022v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_Measurement

/-!
Schumacher--Nielsen, Quantum data processing and error correction,
arXiv:quant-ph/9604022v1. Finite nonzero complex coordinate spaces; entropy in bits.
The main reversal iff is recorded as reuse of the pinned Renew46.P35 theorem.
All new helpers are confined to this paper. Source entropy, coherent information,
support and complement formulas use imported primitives directly: no same-named
wrappers of frozen declarations are introduced. Compilation awaits the batch handoff.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap20.P06

open QAlgorithms
open scoped Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.6, Eq.(1): squared pure-state overlap with the original purification. -/
def inputEntanglementFidelity {R Q : Type*} [Fintype R] [Fintype Q]
    (psi : EuclideanSpace ℂ (R × Q)) (f : Superop Q Q) : ℝ :=
  effectProb (pureDensity psi) (idTensorSuperop (R := R) f (pureDensity psi))

/-- PDF pp.3--5: the Q channel computed from a fixed unitary and pure ancillary vector.
Theorems require norm eta = 1; U is unitary by its type. -/
def dilationChannel {Q E : Type*} [Fintype Q] [Fintype E]
    (U : Matrix.unitaryGroup (Q × E) ℂ) (eta : EuclideanSpace ℂ E) : Superop Q Q :=
  fun X => traceRight (conjSuperop (U : Matrix (Q × E) (Q × E) ℂ)
    (Matrix.kronecker X (pureDensity eta)))

/-- PDF pp.5,9--10: environment output computed from the same unitary dilation. -/
def environmentOutput {Q E : Type*} [Fintype Q] [Fintype E]
    (U : Matrix.unitaryGroup (Q × E) ℂ) (eta : EuclideanSpace ℂ E)
    (rho : Matrix Q Q ℂ) : Matrix E E ℂ :=
  traceLeft (conjSuperop (U : Matrix (Q × E) (Q × E) ℂ)
    (Matrix.kronecker rho (pureDensity eta)))

/-- PDF p.5: actual final pure vector, coordinates ordered R,(Q,E). -/
def dilatedVector {R Q E : Type*} [Fintype R] [Fintype Q] [Fintype E]
    (U : Matrix.unitaryGroup (Q × E) ℂ) (eta : EuclideanSpace ℂ E)
    (psi : EuclideanSpace ℂ (R × Q)) : EuclideanSpace ℂ (R × (Q × E)) :=
  act (Matrix.kronecker (1 : Matrix R R ℂ) (U : Matrix (Q × E) (Q × E) ℂ))
    (WithLp.toLp 2 fun z => psi (z.1, z.2.1) * eta z.2.2)

/-- PDF pp.9--10: trace out Q from the actual RQE output, keeping all RE coherences. -/
def referenceEnvironment {R Q E : Type*} [Fintype R] [Fintype Q] [Fintype E]
    (U : Matrix.unitaryGroup (Q × E) ℂ) (eta : EuclideanSpace ℂ E)
    (psi : EuclideanSpace ℂ (R × Q)) : Matrix (R × E) (R × E) ℂ :=
  fun a b => ∑ q, pureDensity (dilatedVector U eta psi) (a.1, (q, a.2)) (b.1, (q, b.2))

/-- PDF p.15: the rank-one operator |u><v|; conjugation is on the bra. -/
def ketBra {Q : Type*} (u v : EuclideanSpace ℂ Q) : Matrix Q Q ℂ :=
  fun a b => u a * conj (v b)

/-- PDF pp.15--16: None is the extra complement branch, and Some j is the jth
Schmidt branch. This avoids the printed collision between A_0 and an l index. -/
def recoveryOperators {Q : Type*} [Fintype Q] {k l : ℕ}
    (beta : Fin k → EuclideanSpace ℂ Q)
    (phi : Fin k × Fin l → EuclideanSpace ℂ Q) : Option (Fin l) → Matrix Q Q ℂ
  | none => (1 - ∑ a, pureDensity (phi a))
  | some j => ∑ i, ketBra (beta i) (phi (i, j))

/-- PDF pp.16--17: id_R tensor f tensor id_E, on every matrix block. -/
def middleSuperop {R Q E : Type*} (f : Superop Q Q) :
    Superop (R × (Q × E)) (R × (Q × E)) :=
  fun X a b => f (fun q t => X (a.1, (q, a.2.2)) (b.1, (t, b.2.2))) a.2.1 b.2.1

/-- PDF p.17: X_RQ tensor Y_E in the same R,(Q,E) coordinates as dilatedVector. -/
def appendEnvironment {R Q E : Type*} (X : Matrix (R × Q) (R × Q) ℂ)
    (Y : Matrix E E ℂ) : Matrix (R × (Q × E)) (R × (Q × E)) ℂ :=
  fun a b => X (a.1, a.2.1) (b.1, b.2.1) * Y a.2.2 b.2.2

/-! Definitional sanity tests, independent of the target theorems below. -/

example {R Q : Type*} [Fintype R] [Fintype Q]
    (psi : EuclideanSpace ℂ (R × Q)) (f : Superop Q Q) :
    inputEntanglementFidelity psi f =
      effectProb (pureDensity psi) (idTensorSuperop f (pureDensity psi)) := rfl

example {Q : Type*} [Fintype Q] :
    LinearMap.range (Matrix.toEuclideanLin (0 : Matrix Q Q ℂ)) = ⊥ := by
  simp

example {Q : Type*} [Fintype Q] (v : EuclideanSpace ℂ Q) :
    ketBra v v = pureDensity v := rfl

example {Q : Type*} [Fintype Q] {k l : ℕ}
    (beta : Fin k → EuclideanSpace ℂ Q) (phi : Fin k × Fin l → EuclideanSpace ℂ Q) :
    recoveryOperators beta phi none = (1 - ∑ a, pureDensity (phi a)) ∧
    (∀ j, recoveryOperators beta phi (some j) = ∑ i, ketBra (beta i) (phi (i, j))) :=
  ⟨rfl, fun _ => rfl⟩

example {Q : Type*} [Fintype Q]
    (phi : Fin 0 × Fin 0 → EuclideanSpace ℂ Q) : (1 - ∑ a, pureDensity (phi a)) = 1 := by
  simp

example {R Q E : Type*} (X : Matrix (R × (Q × E)) (R × (Q × E)) ℂ) :
    middleSuperop (fun Y : Matrix Q Q ℂ => Y) X = X := rfl

example {R Q E : Type*} (X : Matrix (R × Q) (R × Q) ℂ) (Y : Matrix E E ℂ)
    (a b : R × (Q × E)) :
    appendEnvironment X Y a b = X (a.1, a.2.1) (b.1, b.2.1) * Y a.2.2 b.2.2 := rfl

example {Q E : Type*} [Fintype Q] [Fintype E]
    (eta : EuclideanSpace ℂ E) (rho : Matrix Q Q ℂ) :
    environmentOutput (1 : Matrix.unitaryGroup (Q × E) ℂ) eta rho =
      rho.trace • pureDensity eta := by
  ext a b
  simp [environmentOutput, conjSuperop, traceLeft, Matrix.kronecker,
    Matrix.trace, Finset.sum_mul]

example {Q E : Type*} [Fintype Q] [Fintype E]
    (eta : EuclideanSpace ℂ E) (rho : Matrix Q Q ℂ) :
    dilationChannel (1 : Matrix.unitaryGroup (Q × E) ℂ) eta rho =
      (pureDensity eta).trace • rho := by
  ext a b
  simp [dilationChannel, conjSuperop, traceRight, Matrix.kronecker,
    Matrix.trace, Finset.mul_sum, mul_comm]

example {R Q E : Type*} [Fintype R] [Fintype Q] [Fintype E]
    (eta : EuclideanSpace ℂ E) (psi : EuclideanSpace ℂ (R × Q))
    (z : R × (Q × E)) :
    dilatedVector (1 : Matrix.unitaryGroup (Q × E) ℂ) eta psi z =
      psi (z.1, z.2.1) * eta z.2.2 := by
  simp [dilatedVector, act]

example {R Q E : Type*} [Fintype R] [Fintype Q] [Fintype E]
    (U : Matrix.unitaryGroup (Q × E) ℂ) (eta : EuclideanSpace ℂ E)
    (psi : EuclideanSpace ℂ (R × Q)) (a b : R × E) :
    referenceEnvironment U eta psi a b =
      ∑ q, dilatedVector U eta psi (a.1, (q, a.2)) *
        conj (dilatedVector U eta psi (b.1, (q, b.2))) := rfl

end QAlgorithms.Papers.Independent.Gap20.P06


