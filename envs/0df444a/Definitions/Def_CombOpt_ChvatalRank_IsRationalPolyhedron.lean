-- Prove2me | Definitions.Def_CombOpt_ChvatalRank_IsRationalPolyhedron
-- name    : CombOpt_ChvatalRank_IsRationalPolyhedron
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:05:47.922043+00:00
-- url     : https://prove2.me/theorems/d64bd7cb-f30e-4af7-9cab-bcc99f21906c
-- title:
--   Rational polyhedron
-- statement:
--   A polyhedron $P\subseteq\mathbb R^n$ is **rational** if it can be defined by a rational linear system: $P=\{x\in\mathbb R^n : Ax\le b\}$ for some rational matrix $A$ and rational vector $b$.
--
--   All of §6.4–§6.7 of the book is restricted to rational polyhedra.
--
--   **Formalization Note** The points of $P$ are real vectors; only some defining system is required to be rational.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §6.4, pp. 218–219 (PDF 226–227)

import Mathlib
import Definitions.Def_RobustToDynamics_polyhedron

open Matrix

namespace CombOpt.ChvatalRank

/-- **Rational polyhedron.** Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §6.4, pp. 218–219 (PDF 226–227):
"rational polyhedra, that is, polyhedra that can be defined by rational linear systems."

**Formalization Note.** The set lives in `ℝⁿ`; only some defining system has rational entries. -/
def IsRationalPolyhedron {n : ℕ} (P : Set (Fin n → ℝ)) : Prop :=
  ∃ (m : ℕ) (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ),
    P = RobustToDynamics.polyhedron (A.map (Rat.cast : ℚ → ℝ)) (fun i => (b i : ℝ))

end CombOpt.ChvatalRank


