-- Prove2me | Definitions.Def_SparsestCutOracle_Main_Machine
-- name    : SparsestCutOracle_Main_Machine
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:36:02.810062+00:00
-- url     : https://prove2.me/theorems/a59d58e4-2c96-48f1-94f2-0d89e16d3630
-- title:
--   Charged randomized real RAM with square roots and Gaussian samples
-- statement:
--   A program is a finite list of instructions extending the published randomized exact real RAM. The extension adds the square root of a real register and one independent standard Gaussian sample. All real literals are rational. Every executed scalar instruction, including halting and random sampling, costs one unit; the program cannot access its work counter or either random-tape cursor.
--
--   If $P$ halts on tape $\omega$, write $w_P(\omega)$ for its work at the first halting state. Its expected work is
--
--   $$\mathbb E[w_P]=\int w_P(\omega)\,d\mu(\omega),$$
--
--   where $\mu$ is the product law of independent fair coins and standard Gaussians. Almost-sure halting and integrability are required separately wherever this integral bounds running time. This prevents a default integral value or uncharged mathematical function from implementing an algorithm.
-- source:
--   Robin Münk, Monika Henzinger, Harald Räcke, STOC 2027 submission #1170 (October 2026), p. 4, Theorem 1; paper.md R1–R2 (the paper names no machine)

import Mathlib
import Definitions.Def_ClusterDecomp_Machine

namespace SparsestCutOracle.Main

/-- The published charged machine extended only by square root and Gaussian sampling. -/
inductive Instr where
  | base (op : ClusterDecomp.Instr)
  | sqrt (dst src : ℕ)
  | gauss (dst : ℕ)

abbrev Program := List Instr
abbrev Tape := (ℕ → Bool) × (ℕ → ℝ)

/-- The placeholder is used only at extension instructions, dispatched separately below. -/
def baseProgram (P : Program) : ClusterDecomp.Program :=
  P.map fun op => match op with
  | .base i => i
  | _ => .core (.const 0 0)

def Admissible (P : Program) : Prop := ClusterDecomp.Admissible (baseProgram P)

structure State where
  base : ClusterDecomp.State
  gaussianCursor : ℕ

/-- Neither the work counter nor either tape cursor is addressable by the program. -/
noncomputable def step (P : Program) (ω : Tape) (s : State) : State :=
  if s.base.halted then s else
  match P[s.base.core.pc]? with
  | some (.sqrt d a) =>
    { s with base := { s.base with
        work := s.base.work + 1
        core := { s.base.core with
          pc := s.base.core.pc + 1
          regs := Function.update s.base.core.regs d (Real.sqrt (s.base.core.regs a)) } } }
  | some (.gauss d) =>
    { base := { s.base with
        work := s.base.work + 1
        core := { s.base.core with
          pc := s.base.core.pc + 1
          regs := Function.update s.base.core.regs d (ω.2 s.gaussianCursor) } }
      gaussianCursor := s.gaussianCursor + 1 }
  | _ => { s with base := ClusterDecomp.step (baseProgram P) ω.1 s.base }

noncomputable def init (ints : List ℤ) (reals : List ℝ) : State :=
  ⟨ClusterDecomp.initState ints reals, 0⟩

noncomputable def run (P : Program) (s : State) (ω : Tape) (t : ℕ) : State :=
  (step P ω)^[t] s

noncomputable def tapeLaw : MeasureTheory.Measure Tape :=
  ClusterDecomp.coinTape.prod
    (MeasureTheory.Measure.infinitePi (fun _ : ℕ => ProbabilityTheory.gaussianReal 0 1))

/-- This is a mathematical observation of a run, not a machine operation. -/
def Halts (P : Program) (s : State) (ω : Tape) : Prop :=
  ∃ t : ℕ, (run P s ω t).base.halted = true

noncomputable def haltTime (P : Program) (s : State) (ω : Tape) : ℕ :=
  by
  classical
  exact if h : Halts P s ω then Nat.find h else 0

noncomputable def final (P : Program) (s : State) (ω : Tape) : State :=
  run P s ω (haltTime P s ω)

/-- Nonhalting tapes have work 0 here; all complexity guarantees separately require a.s. halting. -/
noncomputable def work (P : Program) (s : State) (ω : Tape) : ℝ :=
  by
  classical
  exact if Halts P s ω then ((final P s ω).base.work : ℝ) else 0

noncomputable def outputCut (n : ℕ) (s : State) : Finset (Fin n) :=
  Finset.univ.filter fun v => ClusterDecomp.label s.base v.val ≠ 0

end SparsestCutOracle.Main


