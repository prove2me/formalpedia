-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJABddSSnChainPf
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJABddSSnChainPf
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T05:57:39.622821+00:00
-- url     : https://prove2.me/theorems/4e64a5a4-6181-4ab7-bdf0-7c295d4ddddd
-- title:
--   Cut JABdd SSn Chain Pf
-- statement:
--   Definitions and structural lemmas for Cut JABdd SSn Chain Pf, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutJABddSSnChainPf.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJABddSSnChain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.ChainPf
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
structure Tm (k r : ℕ) where
  j : ℕ
  ws : Fin j → List (Bool × Mat k r)
variable {k r : ℕ} {V E' : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup E'] [NormedSpace ℂ E']
def tval (Ψ : V → E') (F : Mat k r → V) (t : Tm k r) (g : Mat k r) : E' :=
  iteratedFDeriv ℝ t.j Ψ (F g) (fun i => Dw (t.ws i) F g)
def tnext (x : Bool × Mat k r) (t : Tm k r) : List (Tm k r) :=
  ⟨t.j + 1, Fin.cons [x] t.ws⟩ :: List.ofFn fun i : Fin t.j => (⟨t.j, Function.update t.ws i (x :: t.ws i)⟩ : Tm k r)
end
end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.ChainPf


