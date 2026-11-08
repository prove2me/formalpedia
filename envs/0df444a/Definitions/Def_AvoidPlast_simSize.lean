-- Prove2me | Definitions.Def_AvoidPlast_simSize
-- name    : AvoidPlast_simSize
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:43:24.828228+00:00
-- url     : https://prove2.me/theorems/da1eede1-0bcb-4859-abd4-f2fe6e81d060
-- title:
--   Simulation size
-- statement:
--   The simulation size after $t$ steps: the bits $\lceil\log_2(q+1)\rceil$ of the state, plus, over every work tape, the span visited so far, the bits of the head position and one. It is the budget $U_\varepsilon$ gives to a simulated machine.
--
--   **Formalization Note** The budget counts bits, so a universal machine can meet it in space $O(m_\varepsilon(n))$ even for a description with many tapes and states (reading R4). For a fixed machine it is its work space up to constant factors.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Definition 5.13, p.29

import Mathlib
import Definitions.Def_AvoidPlast_Machine
import Definitions.Def_AvoidPlast_run

namespace AvoidPlast

/-- The simulation size after `t` steps (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), Definition 5.13, p.29, "using at most `n^{ε²}` work
space", reading R4): the bits of the state, plus, over every work tape, the visited span, the bits of
the head position and one more.

**Formalization Note** This budget counts bits, so a universal machine can meet it in space
`O(m_ε(n))` even for a description with many tapes and states (the last sentence of Definition 5.13).
For a fixed machine it is the work space up to an additive constant and a factor. -/
noncomputable def simSize {r : ℕ} (M : Machine r) (xs : Fin r → List Bool) (t : ℕ) : ℕ :=
  Nat.clog 2 (M.q + 1) + ∑ j : Fin (M.w + r),
    ((Finset.range (t + 1)).sup (fun t' => (run M xs t').workPos j) + 1 +
      Nat.size ((run M xs t).workPos j) + 1)

end AvoidPlast


