-- Prove2me | Definitions.Def_DetDLP_S8M_StepFits
-- name    : DetDLP_S8M_StepFits
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-25T03:01:55.836827+00:00
-- url     : https://prove2.me/theorems/4e3fde96-9719-56fc-9abd-33efc2c710c0
-- title:
--   Routed natural address encoding fits each EC addition step
-- statement:
--   A route-aligned canonical natural-number name code fits the EC addition block for arbitrary abstract register-bank dimensions, allowing stagewise use in the accumulator fold.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_S8M_StepBaseDefs
import Definitions.Def_DetDLP_S8M_AtomMapNatFits

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace DetDLP.S8M.StepFits

open S8H0.RegisterMap S8H0.NamedBlocks S8H0.GateRoutes S8H0.HashRows
open DetDLP.S8M.Routes DetDLP.S8M.MakePacket
open DetDLP.S8N.ECAddRoutes

variable {m d e : ℕ}

/-- Route-aligned natural code for one short-Weierstrass addition tile.
The dimensions `(m,d,e)` are abstract, so the graph edge count is not unfolded. -/
def stepN_v2 (hd : 1 ≤ d) (p neg1 three c4 : ℕ)
    (flag0 : Ref (Routes.bank m d e))
    (x0 y0 : Word (Routes.bank m d e))
    (flag1 : Ref (Routes.bank m d e))
    (x1 y1 : Word (Routes.bank m d e))
    (path : Path (addShape d e) (Routes.bank m d e)) : NC :=
  codeOf (addBlock hd p neg1 three c4 flag0 x0 y0 flag1 x1 y1 path)

/-- For every addition-stage block, the natural code is exactly the canonical
name model of that `ECAddRoutes.addBlock`. Keeping this lemma fully polymorphic
lets the accumulator fold instantiate it at each stage without specializing or
unfolding the edge-count parameter. -/
theorem step_fits (hd : 1 ≤ d) (p neg1 three c4 : ℕ)
    (flag0 : Ref (Routes.bank m d e))
    (x0 y0 : Word (Routes.bank m d e))
    (flag1 : Ref (Routes.bank m d e))
    (x1 y1 : Word (Routes.bank m d e))
    (path : Path (addShape d e) (Routes.bank m d e)) :
    Fits (stepN_v2 hd p neg1 three c4 flag0 x0 y0 flag1 x1 y1 path)
      (addBlock hd p neg1 three c4 flag0 x0 y0 flag1 x1 y1 path) := by
  exact codeOf_spec _

/-- The canonical natural encoding for a fold stage, with caller-supplied
accumulator input and mapped point input, inherits the tile fitting theorem. -/
theorem fold_stage_fits (hd : 1 ≤ d) (p neg1 three c4 : ℕ)
    (flag0 : Ref (Routes.bank m d e))
    (x0 y0 : Word (Routes.bank m d e))
    (flag1 : Ref (Routes.bank m d e))
    (x1 y1 : Word (Routes.bank m d e))
    (path : Path (addShape d e) (Routes.bank m d e)) :
    Fits (stepN_v2 hd p neg1 three c4 flag0 x0 y0 flag1 x1 y1 path)
      (addBlock hd p neg1 three c4 flag0 x0 y0 flag1 x1 y1 path) :=
  step_fits hd p neg1 three c4 flag0 x0 y0 flag1 x1 y1 path

end DetDLP.S8M.StepFits


