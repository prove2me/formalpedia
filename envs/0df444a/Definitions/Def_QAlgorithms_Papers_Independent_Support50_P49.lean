-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Support50_P49
-- name    : QAlgorithms_Papers_Independent_Support50_P49
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-24T00:03:42.644055+00:00
-- url     : https://prove2.me/theorems/0f2cf45e-126f-49ae-b34c-4781bb5978d5
-- title:
--   Definitions for General bounds for sender-receiver capacities in multipoint quantum communications
-- statement:
--   The objects the formalized statements of *General bounds for sender-receiver capacities in multipoint quantum communications* (arXiv:1603.07262) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `BellOutcome`: PDF pp.6,9–10, Figs.3,6,8: one pair of Weyl labels per sender.
--   - `inputCorrection`: PDF pp.9–10, Eqs.(53),(63): tensor product of input Weyl unitaries; it acts on entangled inputs as well as product inputs.
--   - `outputCorrection`: PDF pp.6,9–10, Eqs.(27),(53),(63): independent output laboratories. Every local correction may depend on the entire public Bell outcome tuple.
--   - `CorrectionCovariance`: PDF pp.6,9–10: a fixed correction table, valid for all normalized inputs. No correction is chosen after seeing the unknown input state.
--   - `ProductTeleportationCovariant`: PDF pp.6,9–10, Eqs.(27),(53),(63): product-output teleportation covariance. The existential table is just a simultaneous choice of the source's corrections, not a simulator, output state, capacity, or stretching assumption.
--   - `bellBra`: PDF pp.6,9–10, Figs.3,6,8: sender's destructive Bell measurement bra. For outcome (a,b), this is the bra of (U(a,b)^dagger tensor I)|Phi_d>. With this convention the uncorrected receiver branch contains E(U rho U^dagger), so the receiver must apply the inverse V, as in the source figures.
--   - `simulationKraus`: PDF pp.6,9–10: physical Kraus branch of the teleportation LOCC. Each sender applies its own Bell bra and communicates its outcome to all receivers. Each receiver applies its local inverse correction. All measured sender registers are discarded; each receiver retains its original resource share. The input order is ((unknown inputs, sender resource halves), receiver shares).
--   - `teleportationLOCC`: PDF pp.6,9–10: average over all physical Bell outcomes of the explicit local-measurement, public-communication, local-correction protocol above. Completeness is a conclusion of the simulation theorems, not a field.
--   - `attachResource`: PDF pp.6,9–10: attach the resource independently of the input and reference, then regroup by the parties who hold each register. Off-diagonal reference blocks are retained. This formula is meaningful for arbitrary reference bases; there is no finite-rank, finite-energy, or product-input restriction.
-- source:
--   General bounds for sender-receiver capacities in multipoint quantum communications, arXiv:1603.07262v2, https://arxiv.org/abs/1603.07262v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P75
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P56
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P43

/-!
Laurenza and Pirandola, arXiv:1603.07262v2, finite-dimensional channel
simulations. PDF page numbers are used throughout. Deferred operational and
bosonic results are recorded individually in HARD.md and GAPS.json.

The simulator below is an explicit LOCC recipe: each sender destructively
measures its input and its own resource half with a complete Bell instrument,
broadcasts the outcome, and each receiver applies its own inverse correction.
It is not an arbitrary channel on the aggregate receiver laboratory.
The referenced identity is stated on all matrix kernels, the linear extension
of channel equality; it therefore includes every normal state with an arbitrary
reference basis, without bounding reference dimension. Only transmitted and
resource shares have finite dimensions. Compilation is pending batch handoff.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P49

open scoped Matrix ComplexConjugate

open QAlgorithms.Papers.Independent.Information100.P75 (Register)
open QAlgorithms.Papers.Independent.Information100.P56 (normalizedChoi)
open QAlgorithms.Papers.Independent.Claimed50.P43 (finiteWeyl)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.6,9–10, Figs.3,6,8: one pair of Weyl labels per sender. -/
abbrev BellOutcome {m : ℕ} (d : Fin m → ℕ) :=
  (i : Fin m) → Fin (d i) × Fin (d i)

/-- PDF pp.9–10, Eqs.(53),(63): tensor product of input Weyl unitaries;
it acts on entangled inputs as well as product inputs. -/
def inputCorrection {m : ℕ} {d : Fin m → ℕ}
    (hd : ∀ i, 0 < d i) (o : BellOutcome d) :
    Matrix (Register d) (Register d) ℂ :=
  fun x y => ∏ i, finiteWeyl (d i) (hd i) (o i).1 (o i).2 (x i) (y i)

/-- PDF pp.6,9–10, Eqs.(27),(53),(63): independent output laboratories.
Every local correction may depend on the entire public Bell outcome tuple. -/
def outputCorrection {k : ℕ} {e : Fin k → ℕ}
    (V : (j : Fin k) → Matrix.unitaryGroup (Fin (e j)) ℂ) :
    Matrix (Register e) (Register e) ℂ :=
  fun x y => ∏ j, (V j : Matrix (Fin (e j)) (Fin (e j)) ℂ) (x j) (y j)

/-- PDF pp.6,9–10: a fixed correction table, valid for all normalized inputs.
No correction is chosen after seeing the unknown input state. -/
def CorrectionCovariance {m k : ℕ} {d : Fin m → ℕ} {e : Fin k → ℕ}
    (hd : ∀ i, 0 < d i)
    (E : Superop (Register d) (Register e))
    (V : BellOutcome d → (j : Fin k) → Matrix.unitaryGroup (Fin (e j)) ℂ) : Prop :=
  ∀ o rho, IsDensityMatrix rho →
    E (inputCorrection hd o * rho * (inputCorrection hd o)ᴴ) =
      outputCorrection (V o) * E rho * (outputCorrection (V o))ᴴ

/-- PDF pp.6,9–10, Eqs.(27),(53),(63): product-output teleportation covariance.
The existential table is just a simultaneous choice of the source's corrections,
not a simulator, output state, capacity, or stretching assumption. -/
def ProductTeleportationCovariant {m k : ℕ} {d : Fin m → ℕ} {e : Fin k → ℕ}
    (hd : ∀ i, 0 < d i)
    (E : Superop (Register d) (Register e)) : Prop :=
  ∃ V : BellOutcome d → (j : Fin k) → Matrix.unitaryGroup (Fin (e j)) ℂ,
    CorrectionCovariance hd E V

/-- PDF pp.6,9–10, Figs.3,6,8: sender's destructive Bell measurement bra.
For outcome (a,b), this is the bra of (U(a,b)^dagger tensor I)|Phi_d>.
With this convention the uncorrected receiver branch contains E(U rho U^dagger),
so the receiver must apply the inverse V, as in the source figures. -/
def bellBra (d : ℕ) (hd : 0 < d) (o : Fin d × Fin d) :
    Matrix (Fin 1) (Fin d × Fin d) ℂ :=
  fun _ p => finiteWeyl d hd o.1 o.2 p.2 p.1 / (Real.sqrt (d : ℝ) : ℂ)

/-- PDF pp.6,9–10: physical Kraus branch of the teleportation LOCC.
Each sender applies its own Bell bra and communicates its outcome to all
receivers. Each receiver applies its local inverse correction. All measured
sender registers are discarded; each receiver retains its original resource share.
The input order is ((unknown inputs, sender resource halves), receiver shares). -/
def simulationKraus {m k : ℕ} {d : Fin m → ℕ} {e : Fin k → ℕ}
    (hd : ∀ i, 0 < d i)
    (V : BellOutcome d → (j : Fin k) → Matrix.unitaryGroup (Fin (e j)) ℂ)
    (o : BellOutcome d) :
    Matrix (Register e) ((Register d × Register d) × Register e) ℂ :=
  fun b p => (∏ i, bellBra (d i) (hd i) (o i) 0 (p.1.1 i, p.1.2 i)) *
    star (outputCorrection (V o) p.2 b)

/-- PDF pp.6,9–10: average over all physical Bell outcomes of the explicit
local-measurement, public-communication, local-correction protocol above.
Completeness is a conclusion of the simulation theorems, not a field. -/
def teleportationLOCC {m k : ℕ} {d : Fin m → ℕ} {e : Fin k → ℕ}
    (hd : ∀ i, 0 < d i)
    (V : BellOutcome d → (j : Fin k) → Matrix.unitaryGroup (Fin (e j)) ℂ) :
    Superop ((Register d × Register d) × Register e) (Register e) :=
  krausApply (simulationKraus hd V)

/-- PDF pp.6,9–10: attach the resource independently of the input and reference,
then regroup by the parties who hold each register. Off-diagonal reference
blocks are retained. This formula is meaningful for arbitrary reference bases;
there is no finite-rank, finite-energy, or product-input restriction. -/
def attachResource {R : Type*} {m k : ℕ} {d : Fin m → ℕ} {e : Fin k → ℕ}
    (X : Matrix (R × Register d) (R × Register d) ℂ)
    (omega : Matrix (Register d × Register e) (Register d × Register e) ℂ) :
    Matrix (R × ((Register d × Register d) × Register e))
      (R × ((Register d × Register d) × Register e)) ℂ :=
  fun p q => X (p.1, p.2.1.1) (q.1, q.2.1.1) *
    omega (p.2.1.2, p.2.2) (q.2.1.2, q.2.2)

/-- The one-dimensional Weyl operator is the identity, including its phase. -/
example : finiteWeyl 1 (by decide) 0 0 0 0 = 1 := by
  change ((1 : Matrix (Fin 1) (Fin 1) ℂ) * 1 : Matrix (Fin 1) (Fin 1) ℂ) 0 0 = 1
  simp

/-- The positive qubit shift sends |0> to |1>. -/
example : finiteWeyl 2 (by decide) 1 0 1 0 = 1 := by
  change ((Matrix.of (fun a b : Fin 2 => if a = b + 1 then (1 : ℂ) else 0)) ^ 1 *
    1 : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 1
  norm_num [Matrix.of_apply]

/-- A one-dimensional Bell instrument has one branch with amplitude one. -/
example : bellBra 1 (by decide) (0, 0) 0 (0, 0) = 1 := by
  have hweyl : finiteWeyl 1 (by decide) 0 0 0 0 = 1 := by
    change ((1 : Matrix (Fin 1) (Fin 1) ℂ) * 1 : Matrix (Fin 1) (Fin 1) ℂ) 0 0 = 1
    simp
  simpa [bellBra] using hweyl

/-- The Choi reference and output indices retain their order. -/
example {m k : ℕ} {d : Fin m → ℕ} {e : Fin k → ℕ}
    (E : Superop (Register d) (Register e))
    (x y : Register d) (b c : Register e) :
    normalizedChoi E (x,b) (y,c) = E (Matrix.single x y 1) b c /
      (Fintype.card (Register d) : ℂ) := rfl

/-- Reference coherences survive attachment of the independent resource. -/
example {R : Type*} {m k : ℕ} {d : Fin m → ℕ} {e : Fin k → ℕ}
    (X : Matrix (R × Register d) (R × Register d) ℂ)
    (omega : Matrix (Register d × Register e) (Register d × Register e) ℂ)
    (r s : R) (x y a t : Register d) (b c : Register e) :
    attachResource X omega (r,((x,a),b)) (s,((y,t),c)) =
      X (r,x) (s,y) * omega (a,b) (t,c) := rfl

/-- Averaged physical evolution is linear at the zero operator; zero is not a state. -/
example {m k : ℕ} {d : Fin m → ℕ} {e : Fin k → ℕ}
    (hd : ∀ i, 0 < d i)
    (V : BellOutcome d → (j : Fin k) → Matrix.unitaryGroup (Fin (e j)) ℂ) :
    teleportationLOCC hd V 0 = 0 := by
  simp [teleportationLOCC, krausApply]

end QAlgorithms.Papers.Independent.Support50.P49


