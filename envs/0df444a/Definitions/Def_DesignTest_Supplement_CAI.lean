-- Prove2me | Definitions.Def_DesignTest_Supplement_CAI
-- name    : DesignTest_Supplement_CAI
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:06:42.112136+00:00
-- url     : https://prove2.me/theorems/5729baf4-0ac0-45b2-9596-bf8c334e3ef3
-- title:
--   Adaptive and non-adaptive incoherent algorithms in the controlled unitary access model
-- statement:
--   Given $m$ sampled unitaries, an **incoherent algorithm with controlled access** and at most $q$ queries is a classical decision tree of $q$ single-query experiments. Experiment $k$, chosen from the earlier outcomes, prepares new index, query and reference registers (the index register may be in superposition), applies $C_U$, $C_U^\dagger$ or nothing, and measures all its registers with a POVM; only the outcome is kept. It is **non-adaptive** if every experiment is fixed in advance, and uses **no inverse query** if no experiment applies $C_U^\dagger$.
--
--   These are the estimators of Theorems 6.8 and 6.15.
--
--   **Formalization Note.** Seeds and finite-outcome measurements: the randomized wrapper `RandProc` draws an internal seed from an arbitrary probability space before any sample, and every measurement has finitely many outcomes; by Chiribella–D'Ariano–Schlingemann (PRL 98, 190403, 2007) a measurement with a continuum of outcomes on a finite-dimensional system is a randomization of finite-outcome ones followed by classical post-processing.
-- source:
--   Kawachi–Nakata–Takeuchi, Testing State and Unitary Designs, STOC 2027 submission (sha256 e2f0a429…), Definitions 3.1, 3.3, 3.4, 3.8, pp.14–16

import Mathlib
import Definitions.Def_DesignTest_Supplement_CAC

set_option autoImplicit false

namespace DesignTest.Supplement

open MeasureTheory RandomGateDesign.MasterBound
open scoped Kronecker Matrix ComplexOrder

/-- **A deterministic adaptive incoherent algorithm in the controlled unitary access model** with at
most `q` queries (A. Kawachi, Y. Nakata, Y. Takeuchi, *Testing State and Unitary Designs*, STOC 2027
submission (sha256 e2f0a429…), Definitions 3.1, 3.4, 3.8, pp.14–16): a classical decision tree of
`q` single-query experiments. Experiment `k`, chosen from the outcomes `h` of experiments `0, …, k − 1`,
prepares new index, query and reference registers in the state `ρ k h` (the index register may be in
superposition), makes one call `C_U^{(σ)}` (`C_U` or `C_U†`, or none) and measures all its registers with
the POVM `{E k h o}_{o ∈ Fin K}`; only the outcome is kept.

**Formalization Note.** `σ = none` makes no call, so every execution uses at most `q` queries. Seeds
and the output come from `RandProc`. -/
structure CAI (d m q w K : ℕ) where
  /-- the call of experiment `k` -/
  σ : (k : ℕ) → (Fin k → Fin K) → Option Bool
  /-- the input of experiment `k` -/
  ρ : (k : ℕ) → (Fin k → Fin K) → Matrix (CSys d m w) (CSys d m w) ℂ
  /-- inputs are positive semidefinite -/
  ρ_psd : ∀ k h, (ρ k h).PosSemidef
  /-- inputs have unit trace -/
  ρ_tr : ∀ k h, (ρ k h).trace = 1
  /-- the POVM of experiment `k` -/
  E : (k : ℕ) → (Fin k → Fin K) → Fin K → Matrix (CSys d m w) (CSys d m w) ℂ
  /-- effects are positive semidefinite -/
  E_psd : ∀ k h o, (E k h o).PosSemidef
  /-- effects sum to the identity -/
  E_sum : ∀ k h, ∑ o, E k h o = 1

/-- The outcomes of the experiments before experiment `k`. -/
def CAI.past {K q : ℕ} (h : Fin q → Fin K) (k : Fin q) : Fin k → Fin K :=
  fun j => h ⟨j.val, lt_trans j.isLt k.isLt⟩

/-- Transcript probability `∏_k Tr[E_{k,o_k} C^{(σ_k)} ρ_k C^{(σ_k)†}]`. -/
noncomputable def CAI.prob {d m q w K : ℕ} (A : CAI d m q w K) (u : Fin m → U d)
    (h : Fin q → Fin K) : ℝ :=
  ∏ k : Fin q,
    (Matrix.trace (A.E k (CAI.past h k) (h k) *
      ((uPow (ctrlU u) (A.σ k (CAI.past h k)) ⊗ₖ (1 : Matrix (Fin w) (Fin w) ℂ)) *
        A.ρ k (CAI.past h k) *
        (uPow (ctrlU u) (A.σ k (CAI.past h k)) ⊗ₖ (1 : Matrix (Fin w) (Fin w) ℂ))ᴴ))).re

/-- **Non-adaptive**: every experiment's call, input and POVM is fixed in advance, independent of the
earlier outcomes (STOC 2027 submission (sha256 e2f0a429…), Definition 3.3, p.15). -/
def CAI.IsNonAdaptive {d m q w K : ℕ} (A : CAI d m q w K) : Prop :=
  ∀ k (h h' : Fin k → Fin K), A.σ k h = A.σ k h' ∧ A.ρ k h = A.ρ k h' ∧ A.E k h = A.E k h'

/-- **No inverse query**: no experiment calls `C_U†`. -/
def CAI.NoInverse {d m q w K : ℕ} (A : CAI d m q w K) : Prop :=
  ∀ k (h : Fin k → Fin K), A.σ k h ≠ some false

/-- Randomized adaptive incoherent algorithms, controlled unitary access, at most `q` queries. -/
abbrev CAIProc (d m q w K : ℕ) := RandProc (U d) m (CAI d m q w K) (Fin q → Fin K) CAI.prob

end DesignTest.Supplement


