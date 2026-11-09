-- Prove2me | Definitions.Def_GevreyGibbsSep_QReg
-- name    : GevreyGibbsSep_QReg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:34:50.665914+00:00
-- url     : https://prove2.me/theorems/f9e08ea9-53b7-47cc-bc36-9e65ce4bd040
-- title:
--   Basis labels $(x,b,w)$ of the quantum register
-- statement:
--   The computational basis of the quantum register is labelled by triples $(x,b,w)$: a query point $x\in\mathbb R^d$, an answer register $b\in\mathbb R^d$ and a workspace label $w$ from a set $W$ chosen by the algorithm. This is the register $|x\rangle|b\rangle$ of the gradient oracle (7), with a workspace.
-- source:
--   Olivucci, Sobchuk, Hoque, Hnybida, Kim, Shayeghi, Ronagh, Provable Quantum–Classical Separation for Continuous Gibbs Sampling, arXiv:2608.24527 (held version, sha256 d4fd40eb…), Eq. (7), p.6

import Mathlib

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace GevreyGibbsSep

/-- Computational-basis labels `(x, b, w)` of the quantum register: a query point `x ∈ ℝ^d`, an
answer register `b ∈ ℝ^d` and a workspace label `w ∈ W` (arXiv:2608.24527 (sha256 d4fd40eb…),
Eq. (7), p.6: `|x⟩|b⟩`). -/
abbrev QReg (d : ℕ) (W : Type) : Type := (Fin d → ℝ) × (Fin d → ℝ) × W

end GevreyGibbsSep


