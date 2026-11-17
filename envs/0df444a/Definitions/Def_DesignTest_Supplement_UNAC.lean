-- Prove2me | Definitions.Def_DesignTest_Supplement_UNAC
-- name    : DesignTest_Supplement_UNAC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:04:31.531175+00:00
-- url     : https://prove2.me/theorems/413ef0b0-d21b-4d07-9052-69eea76821dc
-- title:
--   Non-adaptive coherent procedures in the uncontrolled unitary access model
-- statement:
--   Given $m$ sampled unitaries $U_1,\dots,U_m$, a **non-adaptive coherent (parallel) procedure** with at most $q$ queries per sample fixes in advance a joint input state $\rho$ on $q$ query registers $\mathbb C^d$ per sample and a reference system, the direction $\sigma_{ik}\in\{+1,-1\}$ (or no call) of each query slot, and a joint POVM $\{E_o\}$. It applies $V=\bigotimes_{i,k}U_i^{\sigma_{ik}}$ in parallel and measures: outcome $o$ has probability $\mathrm{Tr}[E_o(V\otimes I)\rho(V\otimes I)^\dagger]$.
--
--   This is the class of the coherent tester of Theorem 5.4 and of the estimator of Theorem 6.3.
--
--   **Formalization Note.** Seeds and finite-outcome measurements: the randomized wrapper `RandProc` draws an internal seed from an arbitrary probability space before any sample, and every measurement has finitely many outcomes; by Chiribella–D'Ariano–Schlingemann (PRL 98, 190403, 2007) a measurement with a continuum of outcomes on a finite-dimensional system is a randomization of finite-outcome ones followed by classical post-processing.
-- source:
--   Kawachi–Nakata–Takeuchi, Testing State and Unitary Designs, STOC 2027 submission (sha256 e2f0a429…), Definitions 3.2, 3.3, 3.7, pp.14–16

import Mathlib
import Definitions.Def_DesignTest_Supplement_twirlDist
import Definitions.Def_DesignTest_Supplement_RandProc

set_option autoImplicit false

namespace DesignTest.Supplement

open MeasureTheory RandomGateDesign.MasterBound
open scoped Kronecker Matrix ComplexOrder

/-- **A deterministic non-adaptive coherent procedure in the uncontrolled unitary access model** with
`m` samples and at most `q` queries per sample (A. Kawachi, Y. Nakata, Y. Takeuchi, *Testing State and
Unitary Designs*, STOC 2027 submission (sha256 e2f0a429…), Definitions 3.2, 3.3, 3.7, pp.14–16): a joint
input state `ρ` on the query registers `(ℂ^d)^{⊗(m q)}` (slot `(i, k)` belongs to sample `i`) and a
reference system `ℂ^w`, fixed in advance; the parallel calls `U_i^{σ_{ik}}` on slot `(i, k)`
(`σ_{ik} ∈ {+1, −1}`, or no call); a joint POVM `{E o}_{o ∈ Fin K}`.

**Formalization Note.** A slot with `σ = none` is not queried, so the class is "at most `q` queries to
each sampled unitary". Initial randomness (in particular a random choice of the directions `σ`) and
post-processing are supplied by `RandProc`. -/
structure UNAC (d m q w K : ℕ) where
  /-- the query direction of slot `(i, k)` -/
  σ : Fin m → Fin q → Option Bool
  /-- the joint input state on the query slots and the reference -/
  ρ : Matrix ((Fin m → Fin q → Fin d) × Fin w) ((Fin m → Fin q → Fin d) × Fin w) ℂ
  /-- `ρ ≥ 0` -/
  ρ_psd : ρ.PosSemidef
  /-- `Tr ρ = 1` -/
  ρ_tr : ρ.trace = 1
  /-- the final joint POVM -/
  E : Fin K → Matrix ((Fin m → Fin q → Fin d) × Fin w) ((Fin m → Fin q → Fin d) × Fin w) ℂ
  /-- effects are positive semidefinite -/
  E_psd : ∀ o, (E o).PosSemidef
  /-- effects sum to the identity -/
  E_sum : ∑ o, E o = 1

/-- The parallel query operator `⊗_{i,k} U_i^{σ_{ik}}` on the query slots. -/
def UNAC.queryOp {d m q : ℕ} (σ : Fin m → Fin q → Option Bool) (u : Fin m → U d) :
    Matrix (Fin m → Fin q → Fin d) (Fin m → Fin q → Fin d) ℂ :=
  Matrix.of fun x y => ∏ i, ∏ k, uPow (u i : Matrix (Fin d) (Fin d) ℂ) (σ i k) (x i k) (y i k)

/-- Outcome probability `Tr[E_o (V ⊗ I) ρ (V ⊗ I)†]`, `V = ⊗_{i,k} U_i^{σ_{ik}}`. -/
noncomputable def UNAC.prob {d m q w K : ℕ} (A : UNAC d m q w K) (u : Fin m → U d) (o : Fin K) : ℝ :=
  (Matrix.trace (A.E o * ((UNAC.queryOp A.σ u ⊗ₖ (1 : Matrix (Fin w) (Fin w) ℂ)) * A.ρ *
    (UNAC.queryOp A.σ u ⊗ₖ (1 : Matrix (Fin w) (Fin w) ℂ))ᴴ))).re

/-- Randomized non-adaptive coherent procedures, uncontrolled unitary access. -/
abbrev UNACProc (d m q w K : ℕ) := RandProc (U d) m (UNAC d m q w K) (Fin K) UNAC.prob

end DesignTest.Supplement


