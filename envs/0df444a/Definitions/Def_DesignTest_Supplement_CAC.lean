-- Prove2me | Definitions.Def_DesignTest_Supplement_CAC
-- name    : DesignTest_Supplement_CAC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:05:53.778062+00:00
-- url     : https://prove2.me/theorems/6094914f-c645-41dd-a87f-3e4000dbaffc
-- title:
--   Adaptive coherent algorithms in the controlled unitary access model
-- statement:
--   Given $m$ sampled unitaries, an **adaptive coherent algorithm with controlled access** and at most $q$ queries is a causally ordered quantum strategy on an index register $\mathbb C^{m+1}$, a query register $\mathbb C^d$ and a workspace. Starting from a state $\rho_0$, it alternates $q+1$ intermediate instruments (finitely many outcomes, chosen from earlier outcomes) with $q$ query slots; each slot applies $C_U$, $C_U^\dagger$ or nothing, the choice made classically from the outcomes so far. The last instrument is the final measurement, and the transcript is the list of all outcomes.
--
--   This is the most general class (it subsumes all eight access/processing settings, p.16): the testers of Theorem 5.9 and the estimators of Theorems 6.6 and 6.9.
--
--   **Formalization Note.** Seeds and finite-outcome measurements: the randomized wrapper `RandProc` draws an internal seed from an arbitrary probability space before any sample, and every measurement has finitely many outcomes; by Chiribella–D'Ariano–Schlingemann (PRL 98, 190403, 2007) a measurement with a continuum of outcomes on a finite-dimensional system is a randomization of finite-outcome ones followed by classical post-processing.
-- source:
--   Kawachi–Nakata–Takeuchi, Testing State and Unitary Designs, STOC 2027 submission (sha256 e2f0a429…), Definitions 3.2, 3.4, 3.8, pp.14–16

import Mathlib
import Definitions.Def_DesignTest_Supplement_twirlDist
import Definitions.Def_DesignTest_Supplement_RandProc

set_option autoImplicit false

namespace DesignTest.Supplement

open MeasureTheory RandomGateDesign.MasterBound
open scoped Kronecker Matrix ComplexOrder

/-- The system of a controlled-access algorithm: index register `ℂ^{m+1}`, query register `ℂ^d`, and a
workspace `ℂ^w`. -/
abbrev CSys (d m w : ℕ) : Type := (Fin (m + 1) × Fin d) × Fin w

/-- **A deterministic adaptive coherent algorithm in the controlled unitary access model** with at most
`q` queries (A. Kawachi, Y. Nakata, Y. Takeuchi, *Testing State and Unitary Designs*, STOC 2027
submission (sha256 e2f0a429…), Definitions 3.2, 3.4, 3.8, pp.14–16): a causally ordered quantum strategy
with quantum memory. From the initial state `ρ₀`, rounds `k = 0, 1, …, q` alternate an intermediate
instrument with `K` outcomes (Kraus operators `kraus k h o j`, chosen from the outcome history `h` of
the earlier instruments) and, for `k < q`, one oracle call `C_U^{(σ)}` (`C_U` or `C_U†`, or none), its
direction chosen classically from the outcomes so far. The instrument of round `q` is the final
measurement. The index register may be in superposition.

**Formalization Note.** `σ = none` makes no call, so every execution uses at most `q` queries, and
stopping early is the special case of no further calls. Instruments and the oracle act on the fixed
registers `CSys d m w`; register permutations are part of the instruments. Seeds and the output come
from `RandProc`. -/
structure CAC (d m q w K J : ℕ) where
  /-- initial state -/
  ρ0 : Matrix (CSys d m w) (CSys d m w) ℂ
  /-- `ρ₀ ≥ 0` -/
  ρ0_psd : ρ0.PosSemidef
  /-- `Tr ρ₀ = 1` -/
  ρ0_tr : ρ0.trace = 1
  /-- Kraus operator `j` of outcome `o` of the instrument of round `k` after history `h` -/
  kraus : (k : ℕ) → (Fin k → Fin K) → Fin K → Fin J → Matrix (CSys d m w) (CSys d m w) ℂ
  /-- each instrument is trace preserving -/
  kraus_complete : ∀ k h, ∑ o, ∑ j, (kraus k h o j)ᴴ * kraus k h o j = 1
  /-- the query after the instrument of round `k`, given its outcome history of length `k + 1` -/
  query : (k : ℕ) → (Fin (k + 1) → Fin K) → Option Bool

/-- The unnormalized state after the instruments of rounds `0, …, k − 1` with outcomes `h` and the
calls between them. -/
noncomputable def CAC.state {d m q w K J : ℕ} (A : CAC d m q w K J) (u : Fin m → U d) :
    (k : ℕ) → (Fin k → Fin K) → Matrix (CSys d m w) (CSys d m w) ℂ
  | 0, _ => A.ρ0
  | k + 1, h =>
    if k < q then
      (uPow (ctrlU u) (A.query k h) ⊗ₖ (1 : Matrix (Fin w) (Fin w) ℂ)) *
        (∑ j, A.kraus k (Fin.init h) (h (Fin.last k)) j * A.state u k (Fin.init h) *
          (A.kraus k (Fin.init h) (h (Fin.last k)) j)ᴴ) *
        (uPow (ctrlU u) (A.query k h) ⊗ₖ (1 : Matrix (Fin w) (Fin w) ℂ))ᴴ
    else
      ∑ j, A.kraus k (Fin.init h) (h (Fin.last k)) j * A.state u k (Fin.init h) *
        (A.kraus k (Fin.init h) (h (Fin.last k)) j)ᴴ

/-- Probability of the outcome history `h` of all `q + 1` instruments. -/
noncomputable def CAC.prob {d m q w K J : ℕ} (A : CAC d m q w K J) (u : Fin m → U d)
    (h : Fin (q + 1) → Fin K) : ℝ :=
  (Matrix.trace (A.state u (q + 1) h)).re

/-- Randomized adaptive coherent algorithms, controlled unitary access, at most `q` queries. -/
abbrev CACProc (d m q w K J : ℕ) :=
  RandProc (U d) m (CAC d m q w K J) (Fin (q + 1) → Fin K) CAC.prob

end DesignTest.Supplement


