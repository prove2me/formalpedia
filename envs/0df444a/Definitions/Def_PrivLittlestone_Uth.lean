-- Prove2me | Definitions.Def_PrivLittlestone_Uth
-- name    : PrivLittlestone_Uth
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:27:28.377242+00:00
-- url     : https://prove2.me/theorems/24e584d9-f890-4015-b0ac-e8f8ed43f3c5
-- title:
--   Stopping threshold $U = \lceil 96/\varepsilon_s + 16L_T/\varepsilon_a\rceil$
-- statement:
--   The stopping threshold of the continual learner,
--   $$
--   U = \left\lceil \frac{96}{\varepsilon_s} + \frac{16 L_T}{\varepsilon_a} \right\rceil
--   $$
--   of (7).
--
--   **Formalization Note** Named `Uth` to avoid a clash with the candidate universe $U$.
-- source:
--   He–He, Private Online Learning of Littlestone Classes and Matroid Flats, STOC 2027 submission (manuscript sha256 21480556…c562), (7), p.8

import Mathlib
import Definitions.Def_PrivLittlestone_epsS
import Definitions.Def_PrivLittlestone_epsA
import Definitions.Def_PrivLittlestone_LT

namespace PrivLittlestone

/-- The stopping threshold `U = ⌈96/ε_s + 16 L_T/ε_a⌉` (He–He, *Private Online Learning of
Littlestone Classes and Matroid Flats*, STOC 2027 submission manuscript (sha256 21480556…c562),
(7), p.8).

**Formalization Note** Named `Uth` (the paper's `U`) to avoid a clash with the candidate universe
`U`. `⌈·⌉₊` (`Nat.ceil`) equals the ceiling for the positive argument of every use. -/
noncomputable def Uth (K m T : ℕ) (ε δ β : ℝ) : ℝ :=
  (⌈96 / epsS K m ε δ + 16 * LT K T β / epsA ε⌉₊ : ℝ)

end PrivLittlestone


