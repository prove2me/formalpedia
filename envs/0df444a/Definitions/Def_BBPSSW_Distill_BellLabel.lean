-- Prove2me | Definitions.Def_BBPSSW_Distill_BellLabel
-- name    : BBPSSW_Distill_BellLabel
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:14:39.533622+00:00
-- url     : https://prove2.me/theorems/d664add6-bd3e-47f0-be3b-a7649ca584cc
-- title:
--   Labels of the four Bell states $\Psi^-,\Psi^+,\Phi^+,\Phi^-$
-- statement:
--   The four labels $\Psi^-$, $\Psi^+$, $\Phi^+$, $\Phi^-$ of the Bell states of two spin-$\tfrac12$ particles. The vectors themselves are `bellVec`.
-- source:
--   Bennett, Brassard, Popescu, Schumacher, Smolin, Wootters, Purification of Noisy Entanglement and Faithful Teleportation via Noisy Channels, arXiv:quant-ph/9511027v2, p. 2, unnumbered ("the four states Ψ± and Φ±—known as the four Bell states")

import Mathlib

namespace BBPSSW.Distill

/-- **Labels of the four Bell states `Ψ⁻, Ψ⁺, Φ⁺, Φ⁻`.**
Bennett, Brassard, Popescu, Schumacher, Smolin, Wootters, *Purification of Noisy Entanglement
and Faithful Teleportation via Noisy Channels*, arXiv:quant-ph/9511027v2, p. 2 (unnumbered: "Mixtures of the four states Ψ± and Φ±—known as the four Bell states").

The vectors themselves are `bellVec`. -/
inductive BellLabel
  | psiMinus
  | psiPlus
  | phiPlus
  | phiMinus
  deriving DecidableEq

instance : Fintype BellLabel where
  elems := {.psiMinus, .psiPlus, .phiPlus, .phiMinus}
  complete := fun a => by cases a <;> decide

end BBPSSW.Distill


