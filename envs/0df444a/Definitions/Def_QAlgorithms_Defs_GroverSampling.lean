-- Prove2me | Definitions.Def_QAlgorithms_Defs_GroverSampling
-- name    : QAlgorithms_Defs_GroverSampling
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:20:41.519105+00:00
-- url     : https://prove2.me/theorems/3f74ef4a-0282-42a4-a006-d1c2a4dd1975
-- title:
--   GroverSampling
-- statement:
--   GroverSampling
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\GroverSampling.lean

import Definitions.Def_QAlgorithms_Defs_SingleQubitCert
import Definitions.Def_QAlgorithms_Defs_GroverPolynomial
noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

namespace QAlgorithms

/-- Operational helper GroverInstrumentStep for the source construction. Source: arxiv-2207.08628v3 PDF p.9; arxiv-2207.08628v3 PDF p.10; arxiv-2207.08628v3 PDF p.12; arxiv-2207.08628v3 PDF p.13; arxiv-2207.08628v3 PDF p.14. -/
inductive GroverInstrumentStep (n : ℕ) where
  | ancilla (U : Matrix.unitaryGroup (Qubits n) ℂ)
  | rotation (piBasis : Bool) (phi : ℝ) (control : Option (Fin n))
  | opposite (piBasis : Bool) (phi : ℝ) (flag : Fin n)

/-- A quantum sampling template over the above two oracle kinds and selectable real angles: finite ancillas in |0⟩, known ancilla gates, actual oracle applications (with the measurement controls explicitly allowed and counted), ancilla measurement records and deterministic classical maps to a bit and one of the four signal-state labels. Source: arxiv-2207.08628v3 PDF p.9; arxiv-2207.08628v3 PDF p.10; arxiv-2207.08628v3 PDF p.12; arxiv-2207.08628v3 PDF p.13; arxiv-2207.08628v3 PDF p.14. -/
structure GroverSamplingInstrument (n : ℕ) where
  steps : GroverLabel → List (GroverInstrumentStep n)
  decode : GroverLabel → Qubits n → Bool × GroverLabel

/-- Operational helper GroverInstrumentStep.mat for the source construction. Source: arxiv-2207.08628v3 PDF p.9; arxiv-2207.08628v3 PDF p.10; arxiv-2207.08628v3 PDF p.12; arxiv-2207.08628v3 PDF p.13; arxiv-2207.08628v3 PDF p.14. -/
def GroverInstrumentStep.mat {n : ℕ} (F : GroverFrame) :
    GroverInstrumentStep n → Matrix (Qubits n × Bool) (Qubits n × Bool) ℂ
  | .ancilla U => Matrix.kronecker (U : Matrix _ _ ℂ) 1
  | .rotation p phi none => Matrix.kronecker 1 (groverRotationOracle F p phi)
  | .rotation p phi (some c) => Matrix.of fun y z =>
      if y.1 = z.1 then
        (if z.1 c then groverRotationOracle F p phi y.2 z.2 else (1 : Matrix Bool Bool ℂ) y.2 z.2)
      else 0
  | .opposite p phi c => Matrix.of fun y z =>
      if y.1 = z.1 then groverRotationOracle F p (if z.1 c then -phi else phi) y.2 z.2 else 0

/-- Compute subnormalized retained signal density for each ancilla record by actual unitary action, Born/Luders projection and partial trace; sum records with the same decoded bit/label. Source: arxiv-2207.08628v3 PDF p.9; arxiv-2207.08628v3 PDF p.13; arxiv-2207.08628v3 PDF p.14. -/
def groverInstrumentBranch {n : ℕ} (I : GroverSamplingInstrument n) (F : GroverFrame)
    (input : GroverLabel) (rho : Matrix Bool Bool ℂ) (b : Bool) (label : GroverLabel) :
    Matrix Bool Bool ℂ :=
  let U := ((I.steps input).map (GroverInstrumentStep.mat F)).reverse.prod
  let X := conjSuperop U (Matrix.kronecker (pureDensity (zeroKet n)) rho)
  ∑ z : Qubits n, if I.decode input z = (b, label) then
    Matrix.of (fun i j => X (z, i) (z, j)) else 0

/-- Count actual ordinary/opposite-angle oracle applications, including controlled final Hadamard-test measurement calls. Source: arxiv-2207.08628v3 PDF p.10; arxiv-2207.08628v3 PDF p.14. -/
def groverInstrumentQueryCount {n : ℕ} (I : GroverSamplingInstrument n)
    (input : GroverLabel) (piBasis opposite : Bool) : ℕ :=
  (I.steps input).countP fun s => match s with
    | .ancilla _ => false
    | .rotation p _ _ => !opposite && decide (p = piBasis)
    | .opposite p _ _ => opposite && decide (p = piBasis)

/-- Sanity test. Source: arxiv-2207.08628v3 PDF p.9; arxiv-2207.08628v3 PDF p.10; arxiv-2207.08628v3 PDF p.12; arxiv-2207.08628v3 PDF p.13; arxiv-2207.08628v3 PDF p.14. -/
example (F : GroverFrame) (rho : Matrix Bool Bool ℂ) (input : GroverLabel) :
    groverInstrumentBranch (⟨fun _ => [], fun l _ => (false, l)⟩ : GroverSamplingInstrument 0)
      F input rho false input = rho := by
  have hd : ∀ z : Qubits 0, z = fun _ => false := fun _ => Subsingleton.elim _ _
  ext i j
  simp [groverInstrumentBranch, conjSuperop, zeroKet, pureDensity, ket, hd]

/-- Sanity test. Source: arxiv-2207.08628v3 PDF p.9; arxiv-2207.08628v3 PDF p.10; arxiv-2207.08628v3 PDF p.12; arxiv-2207.08628v3 PDF p.13; arxiv-2207.08628v3 PDF p.14. -/
example {n : ℕ} (c : Fin n) (input : GroverLabel) :
    groverInstrumentQueryCount
      (⟨fun _ => [.rotation true (Real.pi / 2) (some c)], fun l _ => (false, l)⟩ :
        GroverSamplingInstrument n) input true false = 1 := by
  simp [groverInstrumentQueryCount]

end QAlgorithms


