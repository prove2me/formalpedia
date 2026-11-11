-- Prove2me | Definitions.Def_EFI1PRS_Uniform_Extraction
-- name    : EFI1PRS_Uniform_Extraction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:55:53.807396+00:00
-- url     : https://prove2.me/theorems/6028a047-1298-42f4-a82d-c01b91a6a69d
-- title:
--   Quantum extraction with ideal and public-seed states
-- statement:
--   Extraction applies the actual $m$-qubit unitary to the source register, keeps its first $\ell$ qubits, and traces the rest while preserving arbitrary quantum side information. The ideal output is the maximally mixed retained register tensored with the actual past marginal. Public raw-seed states use exactly uniform binary seeds and the concrete sampler's circuit matrices.
--
--   For the first $i$ columns, the analysis channel is written as an explicit finite Kraus sum. Every seed is available, all shift registers pass through unchanged, and no classical or product assumption is imposed on the quantum input. These discards describe analysis only; the generator retains their environments. The transition error is exactly $e_\lambda=2^{-\lambda}+2^{-\lambda^2}$.
-- source:
--   Rishabh Batra, STOC 2027 submission #273 (October 2026), EFI ⇔ 1PRS, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/273.pdf, Fact 2.16, p.10; §5.1, pp.13–14

import Definitions.Def_EFI1PRS_Uniform_CliffordSampler

/-! Batra, §§2.3 and 5.1, pp.10,13–14. Analysis-only partial traces. -/
noncomputable section
namespace EFI1PRS.Uniform
open QAlgorithms
open scoped BigOperators Matrix ComplexConjugate
attribute [local instance] Classical.propDecidable Classical.decEq

def classicalUniform {K A : Type*} [Fintype K]
    (states : K → Matrix A A ℂ) : Matrix (K × A) (K × A) ℂ :=
  fun x y => if x.1 = y.1 then (Fintype.card K : ℂ)⁻¹ * states x.1 x.2 y.2 else 0

def extractColumn {B : Type*} [Fintype B] (m ell : ℕ)
    (U : Matrix (Qubits m) (Qubits m) ℂ)
    (ζ : Matrix (Qubits m × B) (Qubits m × B) ℂ) :
    Matrix (Qubits ell × B) (Qubits ell × B) ℂ :=
  let V := Matrix.kronecker U (1 : Matrix B B ℂ)
  let state := V * ζ * Vᴴ
  fun x y => ∑ d : Qubits (m-ell),
    state (fun j => if j.val < ell then bitAt x.1 j.val else bitAt d (j.val-ell), x.2)
      (fun j => if j.val < ell then bitAt y.1 j.val else bitAt d (j.val-ell), y.2)

def idealExtracted {B : Type*} [Fintype B] (m ell : ℕ)
    (ζ : Matrix (Qubits m × B) (Qubits m × B) ℂ) :=
  Matrix.kronecker (maximallyMixed ell) (traceLeft ζ)

def cliffordMatrix {m : ℕ} (U : QAlgorithms.Clifford.ProjectiveGroup m) :
    Matrix (Qubits m) (Qubits m) ℂ := (QAlgorithms.Clifford.representative U).val

def seededExtraction {B : Type*} [Fintype B] (m ell sec : ℕ)
    (ζ : Matrix (Qubits m × B) (Qubits m × B) ℂ) :=
  classicalUniform (fun s : Qubits (seedLength m sec) =>
    extractColumn m ell (sampledCircuit m sec s).unitary ζ)

def seededIdeal {B : Type*} [Fintype B] (m ell sec : ℕ)
    (ζ : Matrix (Qubits m × B) (Qubits m × B) ℂ) :=
  classicalUniform (fun _ : Qubits (seedLength m sec) => idealExtracted m ell ζ)

def columnError (sec : ℕ) : ℝ := (2 : ℝ)^(-(sec : ℤ)) + (2 : ℝ)^(-((sec^2 : ℕ) : ℤ))

/-- One Kraus operator of all first-i analysis extractions. The actual generator
retains these d bits instead of summing over them. -/
def prefixKraus (g : PairPreparation) (sec i : ℕ)
    (S : Qubits (windowLength (sourceWidth g sec) *
      seedLength (rows (sourceWidth g sec) sec) sec))
    (d : Qubits (i*(rows (sourceWidth g sec) sec-retained (sourceWidth g sec) sec))) :
    Matrix (Qubits (rows (sourceWidth g sec) sec * shiftBits (sourceWidth g sec) +
      i*retained (sourceWidth g sec) sec))
      (Qubits (rows (sourceWidth g sec) sec * shiftBits (sourceWidth g sec) +
      i*rows (sourceWidth g sec) sec)) ℂ :=
  let M := sourceWidth g sec
  let t := rows M sec
  let ell := retained M sec
  let pastShifts := t*shiftBits M
  fun x y => if ∀ j : Fin pastShifts, bitAt x j.val = bitAt y j.val then
    ∏ c : Fin i,
      let s : Qubits (seedLength t sec) := fun j => bitAt S (c.val*seedLength t sec+j.val)
      (sampledCircuit t sec s).unitary
        (fun j => if j.val < ell then bitAt x (pastShifts+c.val*ell+j.val)
          else bitAt d (c.val*(t-ell)+j.val-ell))
        (fun j => bitAt y (pastShifts+c.val*t+j.val))
  else 0

def extractedPrefix (g : PairPreparation) (sec i : ℕ)
    (S : Qubits (windowLength (sourceWidth g sec) *
      seedLength (rows (sourceWidth g sec) sec) sec))
    (X : Matrix (Qubits (rows (sourceWidth g sec) sec * shiftBits (sourceWidth g sec) +
      i*rows (sourceWidth g sec) sec))
      (Qubits (rows (sourceWidth g sec) sec * shiftBits (sourceWidth g sec) +
      i*rows (sourceWidth g sec) sec)) ℂ) :=
  ∑ d : Qubits (i*(rows (sourceWidth g sec) sec-retained (sourceWidth g sec) sec)),
    prefixKraus g sec i S d * X * (prefixKraus g sec i S d)ᴴ

end EFI1PRS.Uniform


