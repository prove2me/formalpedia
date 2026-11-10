-- Prove2me | Definitions.Def_GeoRobustLearn_OracleMachine
-- name    : GeoRobustLearn_OracleMachine
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:07:26.339575+00:00
-- url     : https://prove2.me/theorems/e41c3eb1-be8b-4aa3-a653-d3d8fd68030a
-- title:
--   The arithmetic real RAM with an evaluation oracle for $P$
-- statement:
--   Lemmas 6.2 and 6.5 bound running time in units of $T_{\mathrm{eval}}(P)$, the time to evaluate $P$ at one point. The model is the published real RAM of the companion mission (same states, memory layout, labelled-example instruction of cost $d+1$, output block) restricted to its arithmetic instructions, plus one instruction `evalP dst addr`: it reads the $d+1$ memory cells starting at the address in pointer `addr` as a point $z\in\mathbb R^{d+1}$, stores $P(z)$ in a register, and costs $T$ units of work. Literals are rational.
--
--   This lets a statement quantify over every function $P$ and every evaluation cost $T$ while the program stays fixed.
--
--   **Formalization Note** $P$ is a parameter of the step function and is used only by `evalP`. The machine has no $\sqrt{\cdot}$, $\exp$, $\log$ or Gaussian draws.
-- source:
--   Lange, Marcussen, Vasilyan, Geometrically Constrained Learning I: Agnostically Learning Adversarially Robust Classifiers, manuscript (Nov. 3, 2026; sha256 8cbf3f52…), Lemma 6.2, pp.31–33; Lemma 6.5, pp.35–37

import Definitions.Def_GeoLipLearn_Agnostic_Machine

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace GeoRobustLearn

open GeoLipLearn.Agnostic

/-!
# The arithmetic real RAM with an evaluation oracle for `P`

Lange, Marcussen, Vasilyan, *Geometrically Constrained Learning I*, manuscript of November 3, 2026
(sha256 8cbf3f52…): Lemma 6.2 (pp.31–33) and Lemma 6.5 (pp.35–37) bound running time in units of
`T_eval(P)`, "the time to evaluate P at one point".

**Formalization Note.** A copy of the published `GeoLipLearn.Agnostic.Machine` (same `State`,
`Streams`, `initial`, `representation`, same costs, same `sample` instruction of cost `d + 1`)
restricted to its arithmetic instructions, plus one instruction `evalP dst addr`: it reads the
`d + 1` memory cells starting at the address held in pointer `addr` as a point `z ∈ ℝ^{d+1}`, sets
`r[dst] := P z`, and costs `T`. The function `P` is a parameter of `ostep` and is used only in that
branch. Literals are rational (`OAdmissible`).
-/

/-- An instruction: the arithmetic real-RAM core, pointer-to-real cast, `sample`, `evalP`, `halt`. -/
inductive OInstr where
  | core (i : SmaleNinth.RAMInstr)
  | pointerReal (dst src : ℕ)
  | sample (addr : ℕ)
  | evalP (dst addr : ℕ)
  | halt (src : ℕ)

/-- A program of the oracle machine. -/
abbrev OProgram := List OInstr

/-- Rational literals only, and no `accept`/`reject` (the published `Admissible`). -/
def OAdmissible (A : OProgram) : Prop :=
  ∀ i ∈ A, (∀ dst c, i = .core (.const dst c) → ∃ q : ℚ, c = (q : ℝ)) ∧
    i ≠ .core .accept ∧ i ≠ .core .reject

/-- The core part of an instruction (non-core instructions become a halted core step). -/
def OInstr.coreOf : OInstr → SmaleNinth.RAMInstr
  | .core i => i
  | _ => .accept

/-- The query point: the `d + 1` cells from the address in pointer `addr`. -/
noncomputable def queryPoint {d : ℕ} (S : State) (addr : ℕ) : Space (d+1) :=
  WithLp.toLp 2 (fun j : Fin (d+1) => S.cfg.mem (S.cfg.ptrs addr + (j.val : ℤ)))

/-- One step of the oracle machine; `evalP` costs `T`, everything else as in the published step. -/
noncomputable def ostep (d : ℕ) (P : Space (d+1) → ℝ) (T : ℕ) (A : OProgram) (ω : Streams d)
    (S : State) : State :=
  if S.halted then S else
  let r := S.cfg.regs
  match A[S.cfg.pc]? with
  | none => { S with work := S.work+1 }
  | some (.core _) =>
      { S with cfg := SmaleNinth.RAMStep (A.map OInstr.coreOf) S.cfg, work := S.work+1 }
  | some (.pointerReal dst src) => S.next (Function.update r dst (S.cfg.ptrs src : ℝ))
  | some (.sample addr) =>
      let b := S.cfg.ptrs addr
      let e := ω.1 S.examples
      let mem := fun j =>
        if h : b ≤ j ∧ j < b+(d : ℤ) then e.1 ⟨(j-b).toNat, by omega⟩
        else if j = b+(d : ℤ) then e.2 else S.cfg.mem j
      { S with
        cfg := { S.cfg with pc := S.cfg.pc+1, mem := mem }
        examples := S.examples+1
        work := S.work+d+1 }
  | some (.evalP dst addr) =>
      { S.next (Function.update r dst (P (queryPoint (d := d) S addr))) with work := S.work + T }
  | some (.halt src) => { S with halted := true, output := r src, work := S.work+1 }

/-- `t` steps of the oracle machine. -/
noncomputable def orun (d : ℕ) (P : Space (d+1) → ℝ) (T : ℕ) (A : OProgram) (ω : Streams d)
    (S : State) (t : ℕ) : State :=
  (ostep d P T A ω)^[t] S

end GeoRobustLearn


