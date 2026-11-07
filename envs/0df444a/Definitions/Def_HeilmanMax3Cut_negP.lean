-- Prove2me | Definitions.Def_HeilmanMax3Cut_negP
-- name    : HeilmanMax3Cut_negP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:27:10.59023+00:00
-- url     : https://prove2.me/theorems/8d4f240f-ccc6-4888-8ac2-e9a831253392
-- title:
--   The reflected triple $-A$
-- statement:
--   For $E\subseteq\mathbb R^n$ write $-E=\{-x:x\in E\}$, and for a triple $A=(A_1,A_2,A_3)$ write $-A=(-A_1,-A_2,-A_3)$.
--
--   The reflection converts negative-correlation noise stability into bilinear form: $T_{-\sigma}1_E=T_\sigma 1_{-E}$.
-- source:
--   Heilman, Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT, arXiv:2608.00333 (held version, sha256 2b4f1d11…), p.21

import Mathlib
import Definitions.Def_GaussianPropeller
open OAI.GaussianPropeller

namespace HeilmanMax3Cut

/-- **The reflected partition `−A`.** Heilman, *Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT*, arXiv:2608.00333 (held version,
sha256 2b4f1d11…), p.21: "For measurable `E ⊆ ℝⁿ`, write
`−E = {−x : x ∈ E}`, and `−A := (−Aᵢ)_{i=1}^3`."

**Formalization Note.** `{−x : x ∈ E}` is written as `{y | −y ∈ E}`, the same set. -/
def negP {n : ℕ} (A : Fin 3 → Set (Space n)) : Fin 3 → Set (Space n) :=
  fun i => {y | -y ∈ A i}

end HeilmanMax3Cut


