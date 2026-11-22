-- Prove2me | Definitions.Def_BB5_gcfg
-- name    : BB5_gcfg
-- status  : Definition
-- author  : @loader3229
-- created : 2026-11-22T14:38:52.399526+00:00
-- url     : https://prove2.me/theorems/9bc55347-5a63-4f36-b643-5f1be2bf44f0
-- title:
--   Champion configuration family $g(x)$
-- statement:
--   The configuration family $g(x):=0^\infty\,{<}A\,1^x0^\infty$ of the five-state champion Turing machine: the machine is in state $A$, its head scans the blank cell immediately to the left of a contiguous block of $x$ ones, and all other cells are blank. Concretely `gcfg x` puts the head at tape position $0$ and writes ones on positions $1,\dots,x$. Thus $g(0)$ is the all-blank initial configuration, which is recorded by the lemma `gcfg_zero_eq_init`.
-- source:
--   bbchallenge wiki, 5-state busy beaver winner, Analysis section, https://wiki.bbchallenge.org/wiki/1RB1LC_1RC1RB_1RD0LE_1LA1LD_1RZ0LA (Collatz-like rules attributed to Pascal Michel, Behavior of busy beavers, https://bbchallenge.org/~pascal.michel/beh#tm52a); also arXiv:2509.12337, Figure 1.

import Mathlib
import Definitions.Def_FCP_BusyBeaver

namespace BB5

/-- The configuration $g(x) := 0^∞ <A 1^x 0^∞$ of the 5-state champion:
state `A`, head on the blank cell immediately left of a contiguous block of
`x` ones. The tape is true exactly on positions `1, …, x`, head at `0`. -/
def gcfg (x : ℕ) : FCP.BusyBeaver.Config 5 where
  state := ⟨0, by omega⟩
  head := 0
  tape := fun i => 1 ≤ i ∧ i ≤ (x : ℤ)

/-- The blank-tape starting configuration is `gcfg 0`. -/
lemma gcfg_zero_eq_init : gcfg 0 = FCP.BusyBeaver.init (by omega) := by
  unfold gcfg FCP.BusyBeaver.init
  rw [FCP.BusyBeaver.Config.mk.injEq]
  constructor
  · apply Fin.ext
    simp
  constructor
  · rfl
  · funext i
    simp
    omega

end BB5


