-- Prove2me | Definitions.Def_StableMSR_WindowPortPacking
-- name    : StableMSR_WindowPortPacking
-- status  : Definition
-- author  : @lreyzin
-- created : 2026-11-22T23:18:29.560827+00:00
-- url     : https://prove2.me/theorems/56f656a8-7d16-4807-ad31-a08e562a21f7
-- title:
--   Physical expansion of individual separator ports into exact-count records
-- statement:
--   The native table transducer reads the uncounted port rows and emits the five evaluator bands. Its bounded base-n digit extraction addresses the original port and both child counts. One distinguished zero ticket provides empty operands and the last row retains the original scenario dimension.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, Appendix A.6, https://arxiv.org/abs/2611.03547. This contribution gives explicit counted join records for the mission's real-distance RAM.

import Definitions.Def_StableMSR_WindowPorts
open scoped Classical
set_option autoImplicit false
open StableMSR.Recovery StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowJoins
open StableMSR.Recovery.WindowProfiles (subR divN remN)
namespace StableMSR.Recovery.WindowPorts
def reader (x : World) (z : ℕ) := divN x (divN x (z-1))
def leftDigit (x : World) (z : ℕ) := remN x (divN x (z-1))
def rightDigit (x : World) (z : ℕ) := remN x (z-1)
noncomputable def contents (x : World) (b z j : ℕ) (s : Bool) : ℤ :=
  let B:=board x;let q:=reader x z;let a:=leftDigit x z;let d:=rightDigit x z
  if b=1 then (if z=0 then 0 else B.value q j s)
  else if b=2 then (if s then (finish x.n (B.root (divN x z)) (remN x z):ℤ) else (rightDigit x z:ℤ))
  else if b=3 then (if s then (if z≠0 ∧ B.tag q≠0 then 1 else 0) else (if z=0 then 0 else activeTicket B x.n x.k q a d))
  else if s then (if B.tag q=1 then 0 else (finish x.n (B.child q) d:ℤ))
  else (if B.tag q=1 then (finish x.n (B.child q) a:ℤ) else (stage x.n (B.dest q) a:ℤ))
noncomputable def packed (x : World) (r j : ℕ) (s : Bool) : ℤ :=
  let V:=capacity x
  if r=0 then (V:ℤ) else if r=x.rows-1 then x.mem 1 else
  if r≤ V then 0 else if r≤2*V then contents x 1 (subR x r (1+V)) j s
  else if r≤3*V then contents x 2 (subR x r (1+2*V)) j s
  else if r≤4*V then contents x 3 (subR x r (1+3*V)) j s
  else contents x 4 (subR x r (1+4*V)) j s
end StableMSR.Recovery.WindowPorts


