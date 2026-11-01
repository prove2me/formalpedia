-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P75
-- name    : QAlgorithms_Papers_Independent_Intakenext100_P75
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-31T07:46:27.499727+00:00
-- url     : https://prove2.me/theorems/4d42617d-926c-4d40-a2b0-2e75995a0994
-- title:
--   Definitions for The Fidelity of Recovery is Multiplicative
-- statement:
--   The objects the formalized statements of *The Fidelity of Recovery is Multiplicative* (arXiv:1502.07973) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `generalizedRecoveryFidelity`: PDF p.1, (6): optimization over every CPTP C → B map. On density inputs the objective set is nonempty (replacement channels) and bounded in [0,1].
--   - `marginalAD`: The AD marginal of a state on (AC)D, PDF p.2, Lemma 1.
--   - `choiOutput`: PDF p.3, (14): lift sqrt(sigma_AD) by I_B, sandwich, then trace D.
--   - `recovered`: PDF p.1, (4): recover A from C, with B passive; output is ordered B,A,C.
--   - `ordinaryRecovery`: PDF p.1, (4): ordinary fidelity of recovery.
--   - `ordinaryTensor`: PDF p.2, (7): the product state grouped as BB', (AA',CC').
--   - `channelTensor`: Tensor product of linear channels, using all matrix units (PDF p.4, (27)).
--   - `productRecovery`: PDF p.2 after (7): a product recovery channel, canonically regrouped.
--   - `conditionedLastCMIBits`: PDF p.1, (1): use the accepted CMI in bits after reordering B,A,C to A,C,B. The accepted CMI conditions on its middle register, so this is I(A:B|C).
--   - `halfRenyi`: PDF p.7, (49): order-one-half divergence in bits; zero fidelity gives +infinity. There is no support-containment requirement at order one-half.
--   - `halfRecovery`: PDF p.7, (49): optimization over all local CPTP recoveries, including channels whose individual fidelity is zero.
--   - `ordinaryCopies`: PDF pp.6–7, tensor powers regrouped into B^n,A^n,C^n.
--   - `Redistribution`: PDF p.5, Definition 3: a finite protocol with sender AR, receiver C and independent arbitrary shared assistance. Scratch and discarding are included in CPTP maps. Positive dimensions are encoded as successor cardinalities.
--   - `Redistribution.cost`: PDF p.5, Definition 3: communication cost log_2 dim Q, a real number.
--   - `Redistribution.output`: PDF p.5, (31): the full reconstructed state, with B passive and R returned. First order the input for the encoder, then reorder for the decoder.
--   - `fullTarget`: PDF p.5: target including the sender's reference, under A ≅ A'.
--   - `discardReference`: Trace R, leaving the tripartite density matrix for the rate formula.
--   - `fullCopies`: PDF p.6, (34): n copies, regrouping each register across the copies.
-- source:
--   The Fidelity of Recovery is Multiplicative, arXiv:1502.07973v2, https://arxiv.org/abs/1502.07973v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P63
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P53
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P08
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P18
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P12

/-!
Statements from Berta and Tomamichel, arXiv:1502.07973v2.
All registers have finite nonempty complex orthonormal bases. Ordinary tripartite
states are ordered B × (A × C), to keep the passive register first.
Pinned accepted definitions supply matrices, squared fidelity, purity, partial traces,
tensor regrouping and CMI. Local definitions implement the remaining paper-specific
optimization and protocol interfaces.
-/

namespace QAlgorithms.Papers.Independent.Intakenext100.P75

open scoped Matrix ComplexOrder

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)
open QAlgorithms.Papers.Independent.Information100.P53 (fidelity)
open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)
open QAlgorithms.Papers.Independent.Dependency50.P18 (bipartiteTensor)

variable {A B C D Ap Bp Cp R I J K L : Type}
variable [Fintype A] [DecidableEq A] [Nonempty A]
variable [Fintype B] [DecidableEq B] [Nonempty B]
variable [Fintype C] [DecidableEq C] [Nonempty C]
variable [Fintype D] [DecidableEq D] [Nonempty D]
variable [Fintype Ap] [DecidableEq Ap] [Nonempty Ap]
variable [Fintype Bp] [DecidableEq Bp] [Nonempty Bp]
variable [Fintype Cp] [DecidableEq Cp] [Nonempty Cp]
variable [Fintype R] [DecidableEq R] [Nonempty R]

/-- PDF p.1, (6): optimization over every CPTP C → B map. On density
inputs the objective set is nonempty (replacement channels) and bounded in [0,1]. -/
noncomputable def generalizedRecoveryFidelity (rho : Mat (A × B)) (sigma : Mat (A × C)) : ℝ :=
  sSup {v | ∃ f : Superop C B, IsChannel f ∧
    v = fidelity rho (idTensorSuperop (R := A) f sigma)}

/-- The AD marginal of a state on (AC)D, PDF p.2, Lemma 1. -/
def marginalAD (sigma : Mat ((A × C) × D)) : Mat (A × D) :=
  fun x y => ∑ c, sigma ((x.1, c), x.2) ((y.1, c), y.2)

/-- PDF p.3, (14): lift sqrt(sigma_AD) by I_B, sandwich, then trace D. -/
noncomputable def choiOutput (sigma : Mat (A × D)) (t : Mat ((A × B) × D)) :
    Mat (A × B) :=
  let s := cfc Real.sqrt sigma
  let lift : Mat ((A × B) × D) := fun x y =>
    s (x.1.1, x.2) (y.1.1, y.2) * (1 : Mat B) x.1.2 y.1.2
  traceRight (lift * t * lift)

/-- PDF p.1, (4): recover A from C, with B passive; output is ordered B,A,C. -/
def recovered (rho : Mat (B × (A × C))) (f : Superop C (A × C)) : Mat (B × (A × C)) :=
  idTensorSuperop (R := B) f
    (fun b b2 => ∑ a, rho (b.1, (a, b.2)) (b2.1, (a, b2.2)))

/-- PDF p.1, (4): ordinary fidelity of recovery. -/
noncomputable def ordinaryRecovery (rho : Mat (B × (A × C))) : ℝ :=
  generalizedRecoveryFidelity rho (fun x y : B × C => ∑ a, rho (x.1, (a, x.2)) (y.1, (a, y.2)))

/-- PDF p.2, (7): the product state grouped as BB', (AA',CC'). -/
def ordinaryTensor (rho : Mat (B × (A × C))) (tau : Mat (Bp × (Ap × Cp))) :
    Mat ((B × Bp) × ((A × Ap) × (C × Cp))) :=
  fun x y => rho (x.1.1, (x.2.1.1, x.2.2.1)) (y.1.1, (y.2.1.1, y.2.2.1)) *
    tau (x.1.2, (x.2.1.2, x.2.2.2)) (y.1.2, (y.2.1.2, y.2.2.2))

/-- Tensor product of linear channels, using all matrix units (PDF p.4, (27)). -/
noncomputable def channelTensor [Fintype I] [DecidableEq I]
    [Fintype K] [DecidableEq K] (f : Superop I J) (g : Superop K L) :
    Superop (I × K) (J × L) :=
  fun x => fun o p => ∑ i, ∑ j, ∑ k, ∑ l,
    x (i, k) (j, l) * f (Matrix.single i j 1) o.1 p.1 *
      g (Matrix.single k l 1) o.2 p.2

/-- PDF p.2 after (7): a product recovery channel, canonically regrouped. -/
noncomputable def productRecovery (f : Superop C (A × C)) (g : Superop Cp (Ap × Cp)) :
    Superop (C × Cp) ((A × Ap) × (C × Cp)) :=
  fun x => (channelTensor f g x).submatrix
    (fun o => ((o.1.1, o.2.1), (o.1.2, o.2.2)))
    (fun o => ((o.1.1, o.2.1), (o.1.2, o.2.2)))

/-- PDF p.1, (1): use the accepted CMI in bits after reordering B,A,C to A,C,B.
The accepted CMI conditions on its middle register, so this is I(A:B|C). -/
noncomputable def conditionedLastCMIBits (rho : Mat (B × (A × C))) : ℝ :=
  QAlgorithms.Papers.Independent.Claimed50.P12.cmi
    (rho.submatrix (fun x : A × (C × B) => (x.2.2, (x.1, x.2.1)))
      (fun x : A × (C × B) => (x.2.2, (x.1, x.2.1))))

/-- PDF p.7, (49): order-one-half divergence in bits; zero fidelity gives +infinity.
There is no support-containment requirement at order one-half. -/
noncomputable def halfRenyi [Fintype I] [DecidableEq I] (rho sigma : Mat I) : EReal :=
  if fidelity rho sigma = 0 then ⊤ else ((-Real.logb 2 (fidelity rho sigma) : ℝ) : EReal)

/-- PDF p.7, (49): optimization over all local CPTP recoveries, including
channels whose individual fidelity is zero. -/
noncomputable def halfRecovery (rho : Mat (B × (A × C))) : EReal :=
  sInf {v | ∃ f : Superop C (A × C), IsChannel f ∧ v = halfRenyi rho (recovered rho f)}

/-- PDF pp.6–7, tensor powers regrouped into B^n,A^n,C^n. -/
def ordinaryCopies (rho : Mat (B × (A × C))) (n : ℕ) :
    Mat ((Fin n → B) × ((Fin n → A) × (Fin n → C))) :=
  fun x y => ∏ i, rho (x.1 i, (x.2.1 i, x.2.2 i)) (y.1 i, (y.2.1 i, y.2.2 i))

/-- PDF p.5, Definition 3: a finite protocol with sender AR, receiver C and
independent arbitrary shared assistance. Scratch and discarding are included in CPTP maps.
Positive dimensions are encoded as successor cardinalities. -/
structure Redistribution (A C R : Type*) [Fintype A] [DecidableEq A]
    [Fintype C] [DecidableEq C] [Fintype R] [DecidableEq R] where
  messagePred : ℕ
  alicePred : ℕ
  bobPred : ℕ
  assistance : Mat (Fin (alicePred + 1) × Fin (bobPred + 1))
  assistance_density : IsDensityMatrix assistance
  encoder : Superop ((A × R) × Fin (alicePred + 1)) (Fin (messagePred + 1) × R)
  encoder_channel : IsChannel encoder
  decoder : Superop ((C × Fin (messagePred + 1)) × Fin (bobPred + 1)) (A × C)
  decoder_channel : IsChannel decoder

/-- PDF p.5, Definition 3: communication cost log_2 dim Q, a real number. -/
noncomputable def Redistribution.cost (p : Redistribution A C R) : ℝ :=
  Real.logb 2 (p.messagePred + 1)

/-- PDF p.5, (31): the full reconstructed state, with B passive and R returned.
First order the input for the encoder, then reorder for the decoder. -/
noncomputable def Redistribution.output (p : Redistribution A C R)
    (psi : Mat (B × (R × (A × C)))) : Mat ((B × R) × (A × C)) :=
  let initial : Mat ((B × (C × Fin (p.bobPred + 1))) ×
      ((A × R) × Fin (p.alicePred + 1))) := fun x y =>
    psi (x.1.1, (x.2.1.2, (x.2.1.1, x.1.2.1)))
      (y.1.1, (y.2.1.2, (y.2.1.1, y.1.2.1))) *
    p.assistance (x.2.2, x.1.2.2) (y.2.2, y.1.2.2)
  let encoded := idTensorSuperop p.encoder initial
  let ordered : Mat ((B × R) × ((C × Fin (p.messagePred + 1)) × Fin (p.bobPred + 1))) :=
    encoded.submatrix
      (fun x => ((x.1.1, (x.2.1.1, x.2.2)), (x.2.1.2, x.1.2)))
      (fun x => ((x.1.1, (x.2.1.1, x.2.2)), (x.2.1.2, x.1.2)))
  idTensorSuperop p.decoder ordered

/-- PDF p.5: target including the sender's reference, under A ≅ A'. -/
def fullTarget (psi : Mat (B × (R × (A × C)))) : Mat ((B × R) × (A × C)) :=
  psi.submatrix (fun x => (x.1.1, (x.1.2, x.2))) (fun x => (x.1.1, (x.1.2, x.2)))

/-- Trace R, leaving the tripartite density matrix for the rate formula. -/
def discardReference (psi : Mat (B × (R × (A × C)))) : Mat (B × (A × C)) :=
  fun x y => ∑ r, psi (x.1, (r, x.2)) (y.1, (r, y.2))

/-- PDF p.6, (34): n copies, regrouping each register across the copies. -/
def fullCopies (psi : Mat (B × (R × (A × C)))) (n : ℕ) :
    Mat ((Fin n → B) × ((Fin n → R) × ((Fin n → A) × (Fin n → C)))) :=
  fun x y => ∏ i, psi (x.1 i, (x.2.1 i, (x.2.2.1 i, x.2.2.2 i)))
    (y.1 i, (y.2.1 i, (y.2.2.1 i, y.2.2.2 i)))

/-! Sanity checks pin coordinate order, full spectator blocks, zero copies and log zero. -/

example (rho : Mat (A × B)) (sigma : Mat (A × C)) :
    generalizedRecoveryFidelity rho sigma =
      sSup {v | ∃ f : Superop C B, IsChannel f ∧
        v = fidelity rho (idTensorSuperop (R := A) f sigma)} := rfl

example (rho : Mat (B × (A × C))) :
    conditionedLastCMIBits rho = QAlgorithms.Papers.Independent.Claimed50.P12.cmi
      (rho.submatrix (fun x : A × (C × B) => (x.2.2, (x.1, x.2.1)))
        (fun x : A × (C × B) => (x.2.2, (x.1, x.2.1)))) := rfl

example [Fintype I] [DecidableEq I] (x y : Mat I) :
    fidelity x y = rootFidelity x y ^ 2 := rfl

example (f : Superop C B) (x : Mat (A × C)) (a a2 : A) (b b2 : B) :
    idTensorSuperop f x (a, b) (a2, b2) =
      f (fun c c2 => x (a, c) (a2, c2)) b b2 := rfl

example (rho : Mat (A × B)) (tau : Mat (Ap × Bp)) (a : A) (b : B)
    (ap : Ap) (bp : Bp) :
    bipartiteTensor rho tau ((a, ap), (b, bp)) ((a, ap), (b, bp)) =
      rho (a, b) (a, b) * tau (ap, bp) (ap, bp) := rfl

example (rho : Mat (B × (A × C))) (x y) : ordinaryCopies rho 0 x y = 1 := by
  simp [ordinaryCopies]

example [Fintype I] [DecidableEq I] (rho sigma : Mat I)
    (h : fidelity rho sigma = 0) : halfRenyi rho sigma = ⊤ := by
  simp [halfRenyi, h]

example (psi : Mat (B × (R × (A × C)))) (b : B) (r : R) (a : A) (c : C) :
    fullTarget psi ((b, r), (a, c)) ((b, r), (a, c)) =
      psi (b, (r, (a, c))) (b, (r, (a, c))) := rfl

end QAlgorithms.Papers.Independent.Intakenext100.P75


