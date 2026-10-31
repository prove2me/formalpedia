-- Prove2me | Definitions.Def_SweepingDesing_orientedTalweg
-- name    : SweepingDesing_orientedTalweg
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:16:09.282064+00:00
-- url     : https://prove2.me/theorems/dcf5af0a-fd88-40dd-90fa-43ecd8f5090d
-- title:
--   Definition 6 — oriented talweg $\varphi^\uparrow$
-- statement:
--   For a set-valued map $S:\mathbb R\rightrightarrows\mathbb R^n$, the **oriented talweg** is the worst oriented modulus on each slice:
--
--   $$
--   \varphi^\uparrow(t)=\sup_{x\in S(t)}\|D^*S(t,x)|^+,\qquad t\in\operatorname{dom}(S).
--   $$
--
--   Its integrability near a time $a$ is one of the four equivalent conditions of Theorem A.
--
--   **Formalization Note** Values in `ℝ≥0∞`. Off $\operatorname{dom}(S)$, where the paper leaves $\varphi^\uparrow$ undefined, the empty supremum gives $0$.
-- source:
--   Daniilidis, Tapia-García, Desingularization of the Sweeping Process Mapping, arXiv:2110.08686v1, Definition 6, p.6

import Mathlib
import Definitions.Def_SweepingDesing_orientedModulus
open Filter Topology MeasureTheory Set
open scoped ENNReal

namespace SweepingDesing

/-- Daniilidis, Tapia-García, Desingularization of the Sweeping Process Mapping, arXiv:2110.08686v1, Definition 6, p.6: the *oriented talweg* `φ↑(t) = sup_{x ∈ S(t)} ‖D*S(t, x)|⁺`.

**Formalization Note** Values in `[0, +∞]`. The paper defines `φ↑` on `dom(S)` only; for
`t ∉ dom(S)` the supremum is empty and Lean returns `0`. -/
noncomputable def orientedTalweg {n : ℕ} (S : ℝ → Set (EuclideanSpace ℝ (Fin n))) (t : ℝ) :
    ℝ≥0∞ :=
  ⨆ x ∈ S t, orientedModulus S t x

end SweepingDesing


