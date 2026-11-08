-- Prove2me | Definitions.Def_AvoidPlast_step
-- name    : AvoidPlast_step
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:41:24.152423+00:00
-- url     : https://prove2.me/theorems/4f0b91a5-5ee6-4027-bcc7-bb00a5e4f8a7
-- title:
--   One machine step
-- statement:
--   One step of a machine on read-only inputs $(x_j)_j$. A halting configuration is a fixed point. A read-only head past the end of its string reads a blank. Each work tape writes a symbol and moves; each read-only head moves or jumps to the number on its index tape (as it stood before this step's writes); an optional output bit is appended.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Section 3, machine model, p.13

import Mathlib
import Definitions.Def_AvoidPlast_HeadAct
import Definitions.Def_AvoidPlast_Machine
import Definitions.Def_AvoidPlast_moveApply
import Definitions.Def_AvoidPlast_indexValue
import Definitions.Def_AvoidPlast_Config

namespace AvoidPlast

/-- One step of a machine on read-only inputs `xs` (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), §3, p.13, the machine model). A
configuration in a halting state is a fixed point. A read-only head past the end of its string reads
`none`. A jump puts the head at the number written on its index tape before this step's writes. -/
noncomputable def step {r : ℕ} (M : Machine r) (xs : Fin r → List Bool) (c : Config M) : Config M :=
  if M.halting c.state then c else
    let o := M.δ c.state (fun j => c.work j (c.workPos j)) (fun j => (xs j)[c.inPos j]?)
    { state := o.1
      work := fun j => Function.update (c.work j) (c.workPos j) (o.2.1 j).1
      workPos := fun j => moveApply (o.2.1 j).2 (c.workPos j)
      inPos := fun j =>
        match o.2.2.1 j with
        | HeadAct.move m => moveApply m (c.inPos j)
        | HeadAct.jump => indexValue (c.work (Fin.natAdd M.w j))
      out := c.out ++ o.2.2.2.toList }

end AvoidPlast


