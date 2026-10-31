-- Prove2me | Definitions.Def_SweepingDesing_talweg
-- name    : SweepingDesing_talweg
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:16:14.152396+00:00
-- url     : https://prove2.me/theorems/66e3c044-a810-461f-b326-f38f96774d52
-- title:
--   Remark 7 — talweg $\varphi$
-- statement:
--   For a set-valued map $S:\mathbb R\rightrightarrows\mathbb R^n$, the (symmetric) **talweg** is
--
--   $$
--   \varphi(t)=\sup_{x\in S(t)}\|D^*S(t,x)\|^+,\qquad t\in\operatorname{dom}(S).
--   $$
--
--   It is the function used in earlier work on desingularization of the coderivative, and it dominates the oriented talweg $\varphi^\uparrow$.
--
--   **Formalization Note** Values in `ℝ≥0∞`; $0$ off $\operatorname{dom}(S)$.
-- source:
--   Daniilidis, Tapia-García, Desingularization of the Sweeping Process Mapping, arXiv:2110.08686v1, Remark 7, p.6

import Mathlib
import Definitions.Def_SweepingDesing_modulus
open Filter Topology MeasureTheory Set
open scoped ENNReal

namespace SweepingDesing

/-- Daniilidis, Tapia-García, Desingularization of the Sweeping Process Mapping, arXiv:2110.08686v1, Remark 7, p.6: the (symmetric) *talweg* `φ(t) = sup_{x ∈ S(t)} ‖D*S(t, x)‖⁺`.

**Formalization Note** Values in `[0, +∞]`; `0` off `dom(S)` (empty supremum). -/
noncomputable def talweg {n : ℕ} (S : ℝ → Set (EuclideanSpace ℝ (Fin n))) (t : ℝ) : ℝ≥0∞ :=
  ⨆ x ∈ S t, modulus S t x

end SweepingDesing


