-- Prove2me | Definitions.Def_QAlgorithms_Defs_PauliNoiseFourier
-- name    : QAlgorithms_Defs_PauliNoiseFourier
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:20:29.734982+00:00
-- url     : https://prove2.me/theorems/956b0845-0ba4-462d-bd1f-ef931cda9f44
-- title:
--   PauliNoiseFourier
-- statement:
--   PauliNoiseFourier
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\PauliNoiseFourier.lean

import Definitions.Def_QAlgorithms_Defs_CommutingPauli
noncomputable section

namespace QAlgorithms.SparsePauliNoise

/-- Source Pauli labels (x,z), in that order (2007.07901 p.2, Eq.(1)). -/
abbrev Label (n : ℕ) := (Fin n → ZMod 2) × (Fin n → ZMod 2)

/-- Swap source X/Z order into the frozen canonical Z/X convention
(2007.07901 p.2, Eq.(1)). -/
def labelOperator {n : ℕ} (a : Label n) : Matrix (Qubits n) (Qubits n) ℂ :=
  (canonicalPauli (a.2,a.1)).toMatrix

/-- Commutation pairing x·z'+z·x' over F2 (2007.07901 p.2, Eq.(2)). -/
def symplecticPairing {n : ℕ} (a b : Label n) : ZMod 2 :=
  a.1 ⬝ᵥ b.2+a.2 ⬝ᵥ b.1

/-- Forward Pauli-commutation WHT without normalization (2007.07901 p.3, Eq.(5)). -/
def eigenvalueWHT {n : ℕ} (p : Label n → ℝ) : Label n → ℝ :=
  fun a => ∑ b, (-1 : ℝ)^(symplecticPairing a b).val*p b

/-- Inverse WHT with 1/4^n normalization (2007.07901 p.3, Eq.(6)). -/
def inverseWHT {n : ℕ} (lam : Label n → ℝ) : Label n → ℝ :=
  fun b => ((4 : ℝ)^n)⁻¹*∑ a, (-1 : ℝ)^(symplecticPairing b a).val*lam a

/-- The channel induced by nonnegative normalized error rates, not an unrelated
superoperator (2007.07901 p.2, Eq.(3)). -/
def channelFromRates {n : ℕ} (p : Label n → ℝ) (_distribution : Learning.IsDistribution p) :
    Superop (Qubits n) (Qubits n) :=
  fun X => ∑ a, (p a : ℂ) • conjSuperop (labelOperator a) X

example : symplecticPairing ((![1],![0]) : Label 1) (![0],![1]) = 1 := by
  simp [symplecticPairing, dotProduct, Fin.sum_univ_one]

example (n : ℕ) : eigenvalueWHT (Pi.single (0 : Label n) 1) = fun _ => 1 := by
  funext a
  classical
  rw [eigenvalueWHT, Finset.sum_eq_single 0]
  · simp [Pi.single_apply,symplecticPairing]
  · intro b _ hb
    simp [Pi.single_apply,hb]
  · simp

example (p : Label 0 → ℝ) : inverseWHT p = p := by
  letI : Unique (Label 0) := ⟨⟨0⟩,fun a => Subsingleton.elim _ _⟩
  funext a
  have ha : a = 0 := Subsingleton.elim _ _
  subst a
  simp [inverseWHT, symplecticPairing]
  rfl

end QAlgorithms.SparsePauliNoise


