-- Prove2me | Definitions.Def_DetDLP_W3C_FpCosetLoop
-- name    : DetDLP_W3C_FpCosetLoop
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-25T02:34:49.792328+00:00
-- url     : https://prove2.me/theorems/d590ded0-96f9-4c20-a653-65b0510f910e
-- title:
--   Finite-field Stage II coset shrinkage certificate
-- statement:
--   Applies the Stage2Trace bounded descent theorem to a fixed-width injective query and certified HNF operations, producing a consistent terminal coset within the logarithmic cut bound.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_W3C_FpRowTrace
import Definitions.Def_DetDLP_W3C_Stage2Trace

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace DetDLP.W3C.FpCosetLoop
open DetDLP Stage2Trace

/-- A consistent label keeps every exact row intersection nonempty. The
    Stage-II descent therefore stops within the logarithmic initial coset size. -/
theorem boundedCuts {q : w3_Query} (ops : w3_hnfOps) (hM : 2 ≤ q.M)
    {L : ℕ} (width : ∀ X Y, (q.code X Y).length = L)
    (inj : Function.Injective (Function.uncurry q.code))
    (z : w3_Label q.M q.FB.totalCoords) (pass : w3_pass q.FB q.M q.P z)
    (s : w3_Rep q.M q.FB.totalCoords) (hs : Invariant z s)
    (cap : Nat.card (w3_coset s) ≤ 2^L) :
    ∃ n t, n ≤ L ∧ w3_Cuts q.FB q.M q.P n s t ∧ Invariant z t ∧
      w3_mass (Stage2Trace.root q t) = 0 := by
  exact Stage2Trace.bounded q ops hM width inj z pass L s hs cap

end DetDLP.W3C.FpCosetLoop


