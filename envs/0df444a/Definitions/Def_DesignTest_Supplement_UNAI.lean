-- Prove2me | Definitions.Def_DesignTest_Supplement_UNAI
-- name    : DesignTest_Supplement_UNAI
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:05:13.133771+00:00
-- url     : https://prove2.me/theorems/5256af27-f0d6-4845-b7fb-e635ea7ed907
-- title:
--   Non-adaptive incoherent procedures in the uncontrolled unitary access model
-- statement:
--   Given $m$ sampled unitaries, a **non-adaptive incoherent procedure** performs $n$ single-query experiments fixed in advance. Experiment $j$ prepares a new input $\rho_j$ on a query register $\mathbb C^d$ and a new reference $\mathbb C^w$, applies $U_{i_j}$ or $U_{i_j}^\dagger$ to the query register, measures both registers with a POVM $\{E_{j,o}\}$ and discards them; the transcript probability is $\prod_j\mathrm{Tr}[E_{j,o_j}W_j\rho_jW_j^\dagger]$. The total query count is $q_{\mathrm{total}}=n$; $w=1$ means ancilla-free (no reference).
--
--   This is the class of the testers of Theorems 5.4 (incoherent), 5.5, 5.12 and 5.22–5.24.
--
--   **Formalization Note.** Seeds and finite-outcome measurements: the randomized wrapper `RandProc` draws an internal seed from an arbitrary probability space before any sample, and every measurement has finitely many outcomes; by Chiribella–D'Ariano–Schlingemann (PRL 98, 190403, 2007) a measurement with a continuum of outcomes on a finite-dimensional system is a randomization of finite-outcome ones followed by classical post-processing.
-- source:
--   Kawachi–Nakata–Takeuchi, Testing State and Unitary Designs, STOC 2027 submission (sha256 e2f0a429…), Definitions 3.1, 3.3, 3.7, pp.14–16

import Mathlib
import Definitions.Def_DesignTest_Supplement_twirlDist
import Definitions.Def_DesignTest_Supplement_RandProc

set_option autoImplicit false

namespace DesignTest.Supplement

open MeasureTheory RandomGateDesign.MasterBound
open scoped Kronecker Matrix ComplexOrder

/-- **A deterministic non-adaptive incoherent procedure in the uncontrolled unitary access model** with
`m` samples and `n` single-query experiments (A. Kawachi, Y. Nakata, Y. Takeuchi, *Testing State and
Unitary Designs*, STOC 2027 submission (sha256 e2f0a429…), Definitions 3.1, 3.3, 3.7, pp.14–16).
Experiment `j` prepares a new input `ρ_j` on a query register `ℂ^d` and a new reference `ℂ^w`, makes the
one call `U_{idx j}^{±1}` (forward if `σ j = true`, inverse otherwise) on the query register, measures
both registers with the POVM `{E j o}_{o ∈ Fin K}` and discards them. All choices are fixed in advance.

**Formalization Note.** `w = 1` is "a new `d`-dimensional input without a reference register"
(ancilla-free). `n` is the total query count `q_total`. Initial randomness and classical
post-processing of the outcomes are supplied by `RandProc`. -/
structure UNAI (d m n w K : ℕ) where
  /-- the sample queried by experiment `j` -/
  idx : Fin n → Fin m
  /-- the direction of experiment `j` (`true` = forward) -/
  σ : Fin n → Bool
  /-- the input state of experiment `j` -/
  ρ : Fin n → Matrix (Fin d × Fin w) (Fin d × Fin w) ℂ
  /-- inputs are positive semidefinite -/
  ρ_psd : ∀ j, (ρ j).PosSemidef
  /-- inputs have unit trace -/
  ρ_tr : ∀ j, (ρ j).trace = 1
  /-- the POVM of experiment `j` -/
  E : Fin n → Fin K → Matrix (Fin d × Fin w) (Fin d × Fin w) ℂ
  /-- effects are positive semidefinite -/
  E_psd : ∀ j o, (E j o).PosSemidef
  /-- effects sum to the identity -/
  E_sum : ∀ j, ∑ o, E j o = 1

/-- The single-query operator `U_{idx j}^{±1} ⊗ I_w` of experiment `j`. -/
def UNAI.callOp {d m n w K : ℕ} (A : UNAI d m n w K) (u : Fin m → U d) (j : Fin n) :
    Matrix (Fin d × Fin w) (Fin d × Fin w) ℂ :=
  uPow (u (A.idx j) : Matrix (Fin d) (Fin d) ℂ) (some (A.σ j)) ⊗ₖ (1 : Matrix (Fin w) (Fin w) ℂ)

/-- Transcript probability `∏_j Tr[E_{j,o_j} W_j ρ_j W_j†]`. -/
noncomputable def UNAI.prob {d m n w K : ℕ} (A : UNAI d m n w K) (u : Fin m → U d)
    (o : Fin n → Fin K) : ℝ :=
  ∏ j, (Matrix.trace (A.E j (o j) * (A.callOp u j * A.ρ j * (A.callOp u j)ᴴ))).re

/-- The number of experiments querying sample `i` (queries per sampled oracle). -/
def UNAI.queriesTo {d m n w K : ℕ} (A : UNAI d m n w K) (i : Fin m) : ℕ :=
  (Finset.univ.filter fun j => A.idx j = i).card

/-- Randomized non-adaptive incoherent procedures, uncontrolled unitary access. -/
abbrev UNAIProc (d m n w K : ℕ) := RandProc (U d) m (UNAI d m n w K) (Fin n → Fin K) UNAI.prob

end DesignTest.Supplement


