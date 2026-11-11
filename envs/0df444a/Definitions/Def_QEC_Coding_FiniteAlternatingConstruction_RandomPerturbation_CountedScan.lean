-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedScan
-- name    : QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedScan
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T22:40:29.973581+00:00
-- url     : https://prove2.me/theorems/1c0e50b4-8286-4584-8048-b4bde83d663c
-- title:
--   Counted Scan
-- statement:
--   Definitions and structural lemmas for Counted Scan, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedScan.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Execution
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Cost
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_fullEventQuery_correct

set_option autoImplicit false
namespace QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
def scanQuery {I Ω : Type*} (q : I → Ω → Bool × ℕ) : List I → Ω → Option I × ℕ
  | [], _ => (none,0)
  | i::L, ω => let qi := q i ω
               if qi.1 then (some i,qi.2+1) else
                 let tail := scanQuery q L ω
                 (tail.1,qi.2+tail.2+1)
noncomputable def geometricGlobalQuery (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r lambda : ℝ) (K : ℕ) (e : Event P J r) (p : Vertex P → Space) : Bool × ℕ :=
  fullEventQuery P J r lambda K e (fun v => p v.val)
theorem geometricGlobalQuery_correct (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r lambda : ℝ) (K : ℕ) (e : Event P J r) (p : Vertex P → Space) :
    (geometricGlobalQuery P J r lambda K e p).1 = true ↔
      p ∈ localEvent (X := fun _ : Vertex P => Space) (eventSupport P J r) (eventBad P J r lambda K) e :=
  fullEventQuery_correct P J r lambda K e _
noncomputable instance geometricGlobalBadDecidable (P : TannerSquarePresentation)
    (J : Vertex P → Space) (r lambda : ℝ) (K : ℕ) :
    ∀ e : Event P J r, DecidablePred (· ∈ localEvent (X := fun _ : Vertex P => Space) (eventSupport P J r) (eventBad P J r lambda K) e) :=
  fun e p => if h : (geometricGlobalQuery P J r lambda K e p).1 = true then
    isTrue ((geometricGlobalQuery_correct P J r lambda K e p).mp h)
  else isFalse (fun hp => h ((geometricGlobalQuery_correct P J r lambda K e p).mpr hp))
end QEC.Coding.BDL26RandomPerturbation


