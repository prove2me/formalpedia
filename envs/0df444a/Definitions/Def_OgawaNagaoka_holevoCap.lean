-- Prove2me | Definitions.Def_OgawaNagaoka_holevoCap
-- name    : OgawaNagaoka_holevoCap
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:23:20.425558+00:00
-- url     : https://prove2.me/theorems/f02b3be9-f2c6-4cef-8d27-d5afe1b85d47
-- title:
--   Capacity $C=\max_\pi I(\pi)$
-- statement:
--   The maximum of the quantum mutual information over the input distributions,
--
--   $$
--   C=\max_{\pi\in P_{\mathcal X}} I(\pi).
--   $$
--
--   The paper defines the operational capacity on p.2 and quotes the quantum coding theorem, which identifies it with $\max_\pi I(\pi)$; its proof of the strong converse uses this expression.
--
--   **Formalization Note** A real supremum over the image of the simplex. For a nonempty alphabet and density matrices the set is nonempty, bounded above by $\log|D|$, and the supremum is attained (continuity on a compact set). For an empty alphabet the value is the junk value $0$.
-- source:
--   Ogawa–Nagaoka, Strong Converse to the Quantum Channel Coding Theorem, arXiv:quant-ph/9808063v2, p.2

import Mathlib
import Definitions.Def_OgawaNagaoka_holevoInfo

namespace OgawaNagaoka

/-- Ogawa–Nagaoka, *Strong Converse to the Quantum Channel Coding Theorem*,
arXiv:quant-ph/9808063v2, p.2: `max_π I(π)`, the maximum of the quantum mutual information over
the probability distributions `π` on the input alphabet. The paper identifies it with the
capacity `C` through the quantum coding theorem ("The quantum coding theorem states that
`max_π I(π)` is equal to the operational capacity `C`").

**Formalization Note.** A real `sSup` over the image of the simplex `stdSimplex ℝ A`. For a
nonempty alphabet and density matrices `ρ_i` the set is nonempty, bounded above by `log |D|`,
and the supremum is attained (continuity on a compact set), so `sSup` is the maximum. For an
empty alphabet the value is the junk `sSup ∅ = 0`. -/
noncomputable def holevoCap {A D : Type} [Fintype A] [Fintype D] [DecidableEq D]
    (ρ : A → Matrix D D ℂ) : ℝ :=
  sSup (holevoInfo ρ '' stdSimplex ℝ A)

end OgawaNagaoka


