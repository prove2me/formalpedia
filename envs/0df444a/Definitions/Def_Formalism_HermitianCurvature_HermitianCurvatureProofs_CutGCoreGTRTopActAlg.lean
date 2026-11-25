-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTRTopActAlg
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTRTopActAlg
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T05:03:39.520127+00:00
-- url     : https://prove2.me/theorems/0164d6e8-a86f-4eb1-8460-c992b031cbda
-- title:
--   Cut GCore GTRTop Act Alg
-- statement:
--   Definitions and structural lemmas for Cut GCore GTRTop Act Alg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutGCoreGTRTopActAlg.lean

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementE
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.GroupTheory.Perm.Support
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Finset
noncomputable section
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
open Formalism.REAL
def QTopAlg : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (E : Fin n → Fin n → A) (h : ℂ),
    ∃ d : ℕ → A, (∀ Y : ℂ, qminor E id id (Y + h) = ∑ j ∈ Finset.range (n + 1), Y ^ j • d j) ∧
      (1 ≤ n → d (n - 1) = ∑ a, E a a + algebraMap ℂ A ((n : ℂ) * h - (n : ℂ) * ((n : ℂ) - 1) / 2))
namespace TopAlg
variable {A : Type*} [Ring A] [Algebra ℂ A]
def fac (lin : Prop) [Decidable lin] (B : A) : A[X] := (if lin then X else 0) + C B
def prodP {m : ℕ} (lin : Fin m → Prop) [DecidablePred lin] (B : Fin m → A) : A[X] :=
  (List.ofFn fun l => fac (lin l) (B l)).prod
end TopAlg
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC


