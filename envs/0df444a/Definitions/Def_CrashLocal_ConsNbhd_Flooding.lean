-- Prove2me | Definitions.Def_CrashLocal_ConsNbhd_Flooding
-- name    : CrashLocal_ConsNbhd_Flooding
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T19:59:06.686577+00:00
-- url     : https://prove2.me/theorems/3af7a9ac-723b-41f9-a403-2cb477e370c0
-- title:
--   Algorithm 3 (flooding a message) and informed nodes
-- statement:
--   §5.2. flood is Algorithm 3 run with the fixed graph H as the communication graph: a node's input label is true iff it initially holds the message m (it is in X), its state is true iff it is informed; in every round every informed node that has not crashed sends m to all its neighbors in H (the message true; false carries nothing), and a node that receives at least one copy of m becomes informed. Flooding continues indefinitely. informed H id X adv r w: in this execution w has not crashed and is informed at the end of round r.
-- source:
--   Ghinea, Kuhn, Liu-Zhang, Parsaeian 2026, arXiv:2611.04898, §5.2 and Algorithm 3, pp. 24–25

import Mathlib
import Definitions.Def_CrashLocal_ConsNbhd_Model

noncomputable section
open Classical

namespace CrashLocal.ConsNbhd

/-- Algorithm 3 (flooding a message `m` on a fixed graph `H`), run with `H` as the communication
graph. A node's input label is `true` iff it initially holds `m` (`v ∈ X`); its state is `true`
iff it is informed (`m_v = m`). In every round an informed node sends `m` to all its neighbors in
`H` (the message `true`; `false` carries no information and stands for "no message"), and a node
receiving at least one copy of `m` becomes informed. Flooding continues indefinitely. -/
def flood : NodeProgram Bool Bool where
  State := Bool
  Msg := Bool
  init _ b _ := b
  send s _ := s
  update s inb := s || decide (∃ a, inb a = some true)
  output s := some s

variable {W : Type}

/-- In flooding on `H` from the initial holders `X`, node `w` is informed (and has not crashed)
at the end of round `r`. -/
def informed (H : SimpleGraph W) (id : W → ℕ) (X : Set W) (adv : Adversary W) (r : ℕ) (w : W) :
    Prop :=
  config H id (fun w => decide (w ∈ X)) flood adv r w = some true

end CrashLocal.ConsNbhd


