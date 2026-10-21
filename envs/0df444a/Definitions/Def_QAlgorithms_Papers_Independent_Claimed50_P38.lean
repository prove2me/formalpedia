-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P38
-- name    : QAlgorithms_Papers_Independent_Claimed50_P38
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T10:40:35.423694+00:00
-- url     : https://prove2.me/theorems/2635d4cd-a33c-4bb2-86c3-fc7856062ee0
-- title:
--   Definitions for Inequalities for quantum channels assisted by limited resources
-- statement:
--   The objects the formalized statements of *Inequalities for quantum channels assisted by limited resources* (arXiv:quant-ph/0406111) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `completeDephasing`: PDF p.4, (15): complete dephasing in the fixed computational basis.
--   - `tensorSuperop`: PDF p.4, before (16): independent tensor product of two linear channels, constructed by matrix-unit expansion on arbitrary correlated inputs.
--   - `dephasedPower`: PDF p.4, (17): n actual uses of M tensor T, with the n original registers grouped before the n flag registers. Both regroupings are explicit; the action is not defined by its conditional-state decomposition.
--   - `conditionalBlock`: PDF p.4, (18): the subnormalized conditional input, computed from R.
--   - `branchWeight`: PDF p.4, (18): the probability of the flag measurement, the real trace of its positive conditional block.
--   - `conditionalState`: PDF p.4, (18): normalize a positive-weight conditional block. On a zero-weight branch use the fixed pure state at a0; its weighted contribution is zero. In the theorems R is a density matrix, so negative weights do not arise.
--   - `entropyD`: PDF p.4, (14),(19): entropy in dits of base d, converting the accepted base-two von Neumann entropy. Theorems require d >= 2, so the conversion factor is positive. This base stays d for the larger product channel.
--   - `flagEntropy`: PDF p.4, (20): Shannon entropy of the computed flag probabilities, in base d. The zero summand is zero (Real.logb is total).
--   - `conditionalPurification`: PDF p.4, (21): conditional purification obtained by projecting the SAME purification psi of R. Its registers are A and the unchanged reference C. The fallback is a unit basis vector on zero-probability branches.
--   - `withReference`: PDF p.4, (22),(23): M tensor id_C, acting on every reference block; reference coherences are preserved, rather than being measured or traced out.
--   - `purifiedOutput`: PDF p.4, (22): apply (M tensor T)^n tensor id_C, and move C before the flag for comparison with (M^n tensor id_C)(Phi_rho) tensor |b><b|.
--   - `UnassistedCode`: PDF pp.1-2,4: an unassisted block code for unknown logical base-d qudits. Encoding and decoding are CPTP maps fixed before the unknown input. The physical register type A is independent of d; this prevents changing units when adjoining a dephasing side channel. Arbitrary local ancillas are absorbed into the two CPTP maps. No side communication or shared state occurs.
--   - `UnassistedCode.output`: PDF p.4: decoded density from exactly n physical channel applications.
--   - `AchievableUnassisted`: PDF pp.1-2,4: operational achievable rate in base-d qudits per actual use. This generalizes the accepted qubit-only IsAchievableQRate to a fixed logical base independent of A, using uniform unknown-pure-state fidelity. For every accuracy and rate slack all sufficiently large positive block lengths have a single physical code which works for EVERY unit input.
--   - `unassistedQuantumCapacityD`: PDF p.4, (16): the nonnegative extended supremum of operationally achievable rates. It is NOT the coherent-information formula (13). ENNReal retains an unbounded supremum rather than replacing it with a junk real zero. This is quantum transmission in base-d units, distinct from the accepted Frontier30.P06.unassistedCapacity for classical messages in bits.
-- source:
--   Inequalities for quantum channels assisted by limited resources, arXiv:quant-ph/0406111v3, https://arxiv.org/abs/quant-ph/0406111v3

import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P58

/-!
# Inequalities for quantum channels assisted by limited resources

Giovannetti, arXiv:quant-ph/0406111v3, PDF p.4, Section II B.
This draft states (16), (17), (19), (22), (23), and (24). Other assigned
nodes are individually deferred in HARD.md and GAPS.json. No assisted capacity
is represented by an arbitrary function or defined by a claimed entropy formula.
The operational unassisted capacity keeps the logical base independent of the
physical channel dimension, as required when comparing M with M tensor T.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P38

open scoped ComplexConjugate Matrix
open Filter
open QAlgorithms.Papers.Independent.Information100.P58 (Word)

/-- The empty word has exactly one possible basis label, independent of d. -/
example (d : ℕ) : Subsingleton (Word 0 d) := by
  infer_instance

/-- PDF p.4, (15): complete dephasing in the fixed computational basis. -/
def completeDephasing {A : Type*} [DecidableEq A] : Superop A A :=
  fun X a b => if a = b then X a b else 0

/-- Dephasing preserves every diagonal entry, including in dimension one. -/
example {A : Type*} [DecidableEq A] (X : Matrix A A ℂ) (a : A) :
    completeDephasing X a a = X a a := by
  simp [completeDephasing]

/-- PDF p.4, before (16): independent tensor product of two linear channels,
constructed by matrix-unit expansion on arbitrary correlated inputs. -/
def tensorSuperop {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (M : Superop A A) (T : Superop B B) :
    Superop (A × B) (A × B) :=
  fun X a b => ∑ i : A × B, ∑ j : A × B,
    X i j * M (Matrix.single i.1 j.1 1) a.1 b.1 *
      T (Matrix.single i.2 j.2 1) a.2 b.2

/-- A zero first operation gives zero joint output: the expansion has no
implicit normalization or postselection. -/
example {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (T : Superop B B) (X : Matrix (A × B) (A × B) ℂ) :
    tensorSuperop (fun _ => 0) T X = 0 := by
  ext a b
  simp [tensorSuperop]

/-- PDF p.4, (17): n actual uses of M tensor T, with the n original
registers grouped before the n flag registers. Both regroupings are explicit;
the action is not defined by its conditional-state decomposition. -/
def dephasedPower {d delta : ℕ} (M : Superop (Fin d) (Fin d)) (n : ℕ) :
    Superop (Word n d × Word n delta) (Word n d × Word n delta) :=
  fun X a b =>
    piSuperop (fun _ : Fin n => tensorSuperop M (completeDephasing (A := Fin delta)))
      (fun i j => X (fun k => (i k).1, fun k => (i k).2)
        (fun k => (j k).1, fun k => (j k).2))
      (fun k => (a.1 k, a.2 k)) (fun k => (b.1 k, b.2 k))

/-- At one use, regrouping gives precisely the single channel M tensor T. -/
example {d delta : ℕ} (M : Superop (Fin d) (Fin d))
    (X : Matrix (Word 1 d × Word 1 delta) (Word 1 d × Word 1 delta) ℂ)
    (a b : Word 1 d × Word 1 delta) :
    dephasedPower M 1 X a b =
      piSuperop (fun _ : Fin 1 => tensorSuperop M (completeDephasing (A := Fin delta)))
        (fun i j => X (fun k => (i k).1, fun k => (i k).2)
          (fun k => (j k).1, fun k => (j k).2))
        (fun k => (a.1 k, a.2 k)) (fun k => (b.1 k, b.2 k)) := by
  rfl

/-- PDF p.4, (18): the subnormalized conditional input, computed from R. -/
def conditionalBlock {A B : Type*}
    (R : Matrix (A × B) (A × B) ℂ) (b : B) : Matrix A A ℂ :=
  fun i j => R (i, b) (j, b)

/-- A flag-diagonal block reads the actual matrix entries of R. -/
example {A B : Type*} (R : Matrix (A × B) (A × B) ℂ) (b : B) (i j : A) :
    conditionalBlock R b i j = R (i, b) (j, b) := by
  rfl

/-- PDF p.4, (18): the probability of the flag measurement, the real trace
of its positive conditional block. -/
def branchWeight {A B : Type*} [Fintype A]
    (R : Matrix (A × B) (A × B) ℂ) (b : B) : ℝ :=
  (conditionalBlock R b).trace.re

/-- The zero input has zero branch weights, rather than arbitrary supplied weights. -/
example {A B : Type*} [Fintype A] (b : B) :
    branchWeight (0 : Matrix (A × B) (A × B) ℂ) b = 0 := by
  simp [branchWeight, conditionalBlock, Matrix.trace]

/-- PDF p.4, (18): normalize a positive-weight conditional block. On a
zero-weight branch use the fixed pure state at a0; its weighted contribution
is zero. In the theorems R is a density matrix, so negative weights do not arise. -/
def conditionalState {A B : Type*} [Fintype A] [DecidableEq A]
    (a0 : A) (R : Matrix (A × B) (A × B) ℂ) (b : B) : Matrix A A ℂ :=
  if 0 < branchWeight R b then
    ((branchWeight R b : ℂ)⁻¹) • conditionalBlock R b
  else pureDensity (ket a0)

/-- Impossible branches retain a normalized fallback, not the zero vector. -/
example {A B : Type*} [Fintype A] [DecidableEq A]
    (a0 : A) (R : Matrix (A × B) (A × B) ℂ) (b : B) (h : branchWeight R b = 0) :
    conditionalState a0 R b = pureDensity (ket a0) := by
  simp [conditionalState, h]

/-- PDF p.4, (14),(19): entropy in dits of base d, converting the accepted
base-two von Neumann entropy. Theorems require d >= 2, so the conversion
factor is positive. This base stays d for the larger product channel. -/
def entropyD {A : Type*} [Fintype A] [DecidableEq A]
    (d : ℕ) (R : Matrix A A ℂ) : ℝ :=
  vnEntropy R / Real.logb 2 d

/-- At base two this is exactly the accepted entropy in bits. -/
example {A : Type*} [Fintype A] [DecidableEq A] (R : Matrix A A ℂ) :
    entropyD 2 R = vnEntropy R := by
  simp only [entropyD, Nat.cast_ofNat]
  rw [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), div_one]

/-- PDF p.4, (20): Shannon entropy of the computed flag probabilities,
in base d. The zero summand is zero (Real.logb is total). -/
def flagEntropy {A B : Type*} [Fintype A] [Fintype B]
    (d : ℕ) (R : Matrix (A × B) (A × B) ℂ) : ℝ :=
  -∑ b, branchWeight R b * Real.logb d (branchWeight R b)

/-- A zero-weight family contributes zero entropy. -/
example {A B : Type*} [Fintype A] [Fintype B] (d : ℕ) :
    flagEntropy d (0 : Matrix (A × B) (A × B) ℂ) = 0 := by
  simp [flagEntropy, branchWeight, conditionalBlock, Matrix.trace]

/-- PDF p.4, (21): conditional purification obtained by projecting the SAME
purification psi of R. Its registers are A and the unchanged reference C.
The fallback is a unit basis vector on zero-probability branches. -/
def conditionalPurification {A B C : Type*} [Fintype A]
    [DecidableEq A] [DecidableEq C] (a0 : A) (c0 : C)
    (R : Matrix (A × B) (A × B) ℂ)
    (psi : EuclideanSpace ℂ ((A × B) × C)) (b : B) : EuclideanSpace ℂ (A × C) :=
  if 0 < branchWeight R b then
    WithLp.toLp 2 fun z => psi ((z.1, b), z.2) / (Real.sqrt (branchWeight R b) : ℂ)
  else ket (a0, c0)

/-- The conditional vector at an impossible outcome is explicitly a unit ket. -/
example {A B C : Type*} [Fintype A] [DecidableEq A] [DecidableEq C]
    (a0 : A) (c0 : C) (R : Matrix (A × B) (A × B) ℂ)
    (psi : EuclideanSpace ℂ ((A × B) × C)) (b : B) (h : branchWeight R b = 0) :
    conditionalPurification a0 c0 R psi b = ket (a0, c0) := by
  simp [conditionalPurification, h]

/-- PDF p.4, (22),(23): M tensor id_C, acting on every reference block;
reference coherences are preserved, rather than being measured or traced out. -/
def withReference {A C : Type*} (M : Superop A A) : Superop (A × C) (A × C) :=
  fun X a b => idTensorSuperop (R := C) M
    (fun i j => X (i.2, i.1) (j.2, j.1)) (a.2, a.1) (b.2, b.1)

/-- The reference extension of the identity preserves even off-diagonal entries. -/
example {A C : Type*} (X : Matrix (A × C) (A × C) ℂ) :
    withReference (fun R : Matrix A A ℂ => R) X = X := by
  ext a b
  rfl

/-- PDF p.4, (22): apply (M tensor T)^n tensor id_C, and move C before the
flag for comparison with (M^n tensor id_C)(Phi_rho) tensor |b><b|. -/
def purifiedOutput {d delta : ℕ} {C : Type*}
    (M : Superop (Fin d) (Fin d)) (n : ℕ)
    (psi : EuclideanSpace ℂ ((Word n d × Word n delta) × C)) :
    Matrix ((Word n d × C) × Word n delta) ((Word n d × C) × Word n delta) ℂ :=
  fun a b => withReference (dephasedPower M n) (pureDensity psi)
    ((a.1.1, a.2), a.1.2) ((b.1.1, b.2), b.1.2)

/-- The reference is kept in the output, with the flag moved past it. -/
example {d delta : ℕ} {C : Type*} (M : Superop (Fin d) (Fin d)) (n : ℕ)
    (psi : EuclideanSpace ℂ ((Word n d × Word n delta) × C))
    (a b : (Word n d × C) × Word n delta) :
    purifiedOutput M n psi a b = withReference (dephasedPower M n) (pureDensity psi)
      ((a.1.1, a.2), a.1.2) ((b.1.1, b.2), b.1.2) := by
  rfl

/-- PDF pp.1-2,4: an unassisted block code for unknown logical base-d qudits.
Encoding and decoding are CPTP maps fixed before the unknown input. The
physical register type A is independent of d; this prevents changing units
when adjoining a dephasing side channel. Arbitrary local ancillas are
absorbed into the two CPTP maps. No side communication or shared state occurs. -/
structure UnassistedCode (d : ℕ) (A : Type*) [Fintype A] [DecidableEq A] (n k : ℕ) where
  encode : Superop (Word k d) (Fin n → A)
  decode : Superop (Fin n → A) (Word k d)
  encode_channel : IsChannel encode
  decode_channel : IsChannel decode

/-- Physical identity maps form an unassisted identity code, with n logical
registers and n actual uses. -/
example (d n : ℕ) : Nonempty (UnassistedCode d (Fin d) n n) := by
  have hid : IsChannel (fun X : Matrix (Word n d) (Word n d) ℂ => X) :=
    ⟨1, fun _ => 1, by simp [IsKrausFamily], fun X => by simp [krausApply]⟩
  exact ⟨⟨(fun X => X), (fun X => X), hid, hid⟩⟩

/-- PDF p.4: decoded density from exactly n physical channel applications. -/
def UnassistedCode.output {d n k : ℕ} {A : Type*} [Fintype A] [DecidableEq A]
    (code : UnassistedCode d A n k) (M : Superop A A)
    (rho : Matrix (Word k d) (Word k d) ℂ) : Matrix (Word k d) (Word k d) ℂ :=
  code.decode (piSuperop (fun _ : Fin n => M) (code.encode rho))

/-- The physical uses come from the tensor-channel list, not a free cost field. -/
example {d n k : ℕ} {A : Type*} [Fintype A] [DecidableEq A]
    (code : UnassistedCode d A n k) (M : Superop A A)
    (rho : Matrix (Word k d) (Word k d) ℂ) :
    code.output M rho = code.decode (piSuperop (fun _ : Fin n => M) (code.encode rho)) := by
  rfl

/-- The accepted measurement probability tests the transmitted pure state.
A zero output has zero overlap, so missing normalization cannot create success. -/
example {A : Type*} [Fintype A] (psi : EuclideanSpace ℂ A) :
    effectProb (pureDensity psi) 0 = 0 := by
  simp [effectProb]

/-- PDF pp.1-2,4: operational achievable rate in base-d qudits per actual use.
This generalizes the accepted qubit-only IsAchievableQRate to a fixed logical
base independent of A, using uniform unknown-pure-state fidelity. For every
accuracy and rate slack all sufficiently large positive block lengths have a
single physical code which works for EVERY unit input. -/
def AchievableUnassisted (d : ℕ) {A : Type*} [Fintype A] [DecidableEq A]
    (M : Superop A A) (rate : ℝ) : Prop :=
  0 ≤ rate ∧ ∀ eps : ℝ, 0 < eps → ∀ slack : ℝ, 0 < slack →
    ∃ n0 : ℕ, ∀ n ≥ n0, 0 < n → ∃ k : ℕ,
      (rate - slack) * (n : ℝ) ≤ (k : ℝ) ∧
      ∃ code : UnassistedCode d A n k, ∀ psi : EuclideanSpace ℂ (Word k d),
        IsState psi → 1 - eps ≤ effectProb (pureDensity psi) (code.output M (pureDensity psi))

/-- Achievability never admits a negative rate through a total-function default. -/
example (d : ℕ) {A : Type*} [Fintype A] [DecidableEq A]
    (M : Superop A A) (rate : ℝ) (h : AchievableUnassisted d M rate) : 0 ≤ rate := by
  exact h.1

/-- PDF p.4, (16): the nonnegative extended supremum of operationally
achievable rates. It is NOT the coherent-information formula (13). ENNReal
retains an unbounded supremum rather than replacing it with a junk real zero.
This is quantum transmission in base-d units, distinct from the accepted
Frontier30.P06.unassistedCapacity for classical messages in bits. -/
def unassistedQuantumCapacityD (d : ℕ) {A : Type*} [Fintype A] [DecidableEq A]
    (M : Superop A A) : ENNReal :=
  sSup {r | ∃ rate : ℝ, AchievableUnassisted d M rate ∧ r = ENNReal.ofReal rate}

/-- The capacity definition uses exactly the independently defined code-achievable rates. -/
example (d : ℕ) {A : Type*} [Fintype A] [DecidableEq A] (M : Superop A A) :
    unassistedQuantumCapacityD d M =
      sSup {r | ∃ rate : ℝ, AchievableUnassisted d M rate ∧ r = ENNReal.ofReal rate} := by
  rfl

end QAlgorithms.Papers.Independent.Claimed50.P38


