-- Prove2me | Definitions.Def_TimeSpaceMA_Supplement_InTIME1
-- name    : TimeSpaceMA_Supplement_InTIME1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T01:44:24.97738+00:00
-- url     : https://prove2.me/theorems/8b862773-4fae-4547-af68-8f3154bc0d8d
-- title:
--   The class $\mathrm{TIME}_1[t]$
-- statement:
--   A language $L$ is in $\mathrm{TIME}_1[t]$ if one deterministic Turing machine with random read-only access to its input and one sequential work tape decides every input $x$ within $t(|x|)$ steps.
--
--   The single work-tape head moves by at most one cell in a step; no work-space bound is imposed. This is the one-tape class to which the paper applies its crossing-sequence simulation.
--
--   **Formalization Note** The machine is the published `TimeSpaceMA.RATM` specialized to exactly one work tape. Accepting and rejecting states stutter, so inspecting the configuration at the time cap expresses halting within the cap.
-- source:
--   Williams, Xi, Short Non-Interactive Proofs for Time-Space Computations, STOC 2027 submission (manuscript sha256 184c2f95…), Theorem 1.3, p.5; §4.2 and Theorem 4.1, pp.23–24

import Definitions.Def_TimeSpaceMA_RATM

set_option autoImplicit false

namespace TimeSpaceMA
namespace Supplement

/-- `L ∈ TIME₁[t]` (Williams–Xi, *Short Non-Interactive Proofs for Time-Space Computations*,
STOC 2027 submission, manuscript sha256 184c2f95…, Theorem 1.3, p.5, and Theorem 4.1,
p.23): one deterministic machine with random read-only access to its input and one sequential
work tape decides `L` within `t(|x|)` steps.

**Formalization Note** The machine is the published `TimeSpaceMA.RATM` specialized by `M.k = 1`.
Its input address register gives random read-only input access, while the unique work-tape head
moves only left, right, or stays. Since accepting and rejecting configurations stutter, being in a
halting state after `t(|x|)` steps means halting within that bound. No work-space bound is imposed. -/
def InTIME1 (L : Set (List Bool)) (t : ℕ → ℕ) : Prop :=
  ∃ M : RATM, M.k = 1 ∧ ∀ x : List Bool,
    let c := M.run x (t x.length)
    (c.state = M.qaccept ∨ c.state = M.qreject) ∧
      (c.state = M.qaccept ↔ x ∈ L)

end Supplement
end TimeSpaceMA


