-- Prove2me | Definitions.Def_CatalyticSorting494_Sorting_Supplement_Transducer
-- name    : CatalyticSorting494_Sorting_Supplement_Transducer
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:18:38.834276+00:00
-- url     : https://prove2.me/theorems/69b00d42-9f34-4137-b319-024a4b79ec77
-- title:
--   Definitions 2.1/2.3 ($k=1$) — catalytic transducers (catalytic 1-output-pass machines)
-- statement:
--   A **catalytic transducer** is a machine of the base mission's model — read-only random-access input, a clean work tape, and a catalytic tape of fixed length with arbitrary initial content, all accessed through index tapes whose cells are charged as clean space — extended by an **output tape** that starts all zero and has a write-only one-way head. In each step, besides its ordinary action, the machine may write a bit into the current output cell and may move the output head right by one cell; it never moves it left and never reads the output tape. When the machine halts, its **output** is the content of the cells to the left of the output head.
--
--   The transducer runs on $(x,z)$ within time $T$ and clean space $S$ with output $\mathrm{out}$ when, started on input $x$ with catalytic content $z$, it halts after at most $T$ steps with charged clean space at most $S$, with output $\mathrm{out}$, and with the catalytic tape restored exactly:
--
--   $$\text{final catalytic content}=z .$$
--
--   The output tape is not charged. This is the model of Theorem 5.4 (and Theorem 1.8), in contrast to the dirty-XOR-output model of the rest of the paper.
--
--   **Formalization Note** The output head is controlled by the same state and visible bits as the underlying transition; the halting step performs no output. "The output is all the bits up to the head's position" is read as the cells strictly to the left of the head; a machine wanting the inclusive reading moves once more. The published `Machine` and `cleanSpace` are reused unchanged. The parenthetical bound $2^{O(S)}$ on the output tape's length in Definition 2.1 is not imposed.
-- source:
--   Adelmo Morrison Orozco, Nathan S. Sheffield, Ryan Williams, STOC 2027 submission #494 (October 2026), Definition 2.1, printed p.7 (PDF p.8); Definition 2.3 and the k = 1 remark, printed pp.8–9 (PDF pp.9–10); catalytic transducer, §5.2, printed p.22 (PDF p.23)

import Mathlib
import Definitions.Def_CatalyticSorting494_Sorting_Machine

namespace CatalyticSorting494.Sorting.Supplement

open CatalyticSorting494.Sorting

/-- A catalytic transducer: a machine of the published model (random-access read-only input, clean
tape and catalytic tape through charged index tapes) together with an output tape that starts all
zero and has a write-only one-way head (Definition 2.1). In every non-halting step, `out` gives, from
the same state and visible bits as the transition, an optional bit to write into the current output
cell and whether the output head then moves right by one cell. The output tape is never read. -/
structure Transducer where
  machine : Machine
  out : Fin machine.numStates → View → Option Bool × Bool

namespace Transducer

/-- A configuration: a configuration of the underlying machine, the output tape, and the output
head's position. -/
structure Config (M : Transducer) where
  base : M.machine.Config
  outTape : ℕ → Bool
  outPos : ℕ

/-- The initial configuration on catalytic content `z`; the output tape is all zero and its head is
on the leftmost cell. -/
def init (M : Transducer) (z : List Bool) : M.Config :=
  ⟨M.machine.init z, fun _ => false, 0⟩

/-- One step: the underlying machine's step, together with the output action. `none` means the
machine has halted. -/
def step (M : Transducer) (x : List Bool) (cfg : M.Config) : Option M.Config :=
  match M.machine.step x cfg.base with
  | none => none
  | some base' =>
    let o := M.out cfg.base.state (M.machine.view x cfg.base)
    some
      { base := base'
        outTape := match o.1 with
          | none => cfg.outTape
          | some b => Function.update cfg.outTape cfg.outPos b
        outPos := if o.2 then cfg.outPos + 1 else cfg.outPos }

/-- The configuration after `t` steps, if the machine has not halted before then. -/
def configAt (M : Transducer) (x z : List Bool) : ℕ → Option M.Config
  | 0 => some (M.init z)
  | t + 1 => (M.configAt x z t).bind (M.step x)

/-- The output: every bit of the output tape to the left of the head. -/
def output {M : Transducer} (cfg : M.Config) : List Bool :=
  (List.range cfg.outPos).map cfg.outTape

/-- The catalytic transducer `M`, started on input `x` with catalytic content `z`, halts within `T`
steps, charged at most `S` clean bits (the published `cleanSpace`, index tapes included; the output
tape is not charged), with the catalytic tape restored exactly to `z` and output `out`. -/
def RunsWithin (M : Transducer) (x z out : List Bool) (T S : ℕ) : Prop :=
  ∃ (t : ℕ) (cfg : M.Config),
    M.configAt x z t = some cfg ∧ M.step x cfg = none ∧ t ≤ T ∧
      Machine.cleanSpace cfg.base ≤ S ∧ cfg.base.dirty = z ∧ output cfg = out

end Transducer

end CatalyticSorting494.Sorting.Supplement


