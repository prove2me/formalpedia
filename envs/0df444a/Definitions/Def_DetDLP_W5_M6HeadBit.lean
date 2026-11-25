-- Prove2me | Definitions.Def_DetDLP_W5_M6HeadBit
-- name    : DetDLP_W5_M6HeadBit
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T01:24:17.729793+00:00
-- url     : https://prove2.me/theorems/fc703dd2-01b4-4284-933c-49c942da5261
-- title:
--   M6 Head Bit
-- statement:
--   Either initial bit of a nonempty primitive-machine input can be compiled into the tape simulator, with the same constant-factor step bound and additive scratch-space bound.

import Definitions.Def_DetDLP_W5_M6TapeSimulator

namespace DetDLP.w5_M6HeadBit
open w5_EntryTapeCode
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation
open BitProgram w5_EntryTapeModel
def headBits (E : PrimitiveMachine) (b₀ : Bool) : Heads E := fun i => if i=E.inputTape then some b₀ else none
theorem initial_headBits (E : PrimitiveMachine) (b₀ : Bool) (w : List Bool) :
    machineHeads E (w5_EntryTapeModel.init E (b₀::w))=headBits E b₀ := by
  funext i; by_cases h : i=E.inputTape <;> simp [machineHeads,w5_EntryTapeModel.init,Cells.init,h,headBits] <;> rfl

theorem initial_body (E : PrimitiveMachine) (b₀ : Bool) (w : List Bool) :
    store E (w5_EntryTapeModel.init E (b₀::w)) =
      fun j => if j=lane E E.inputTape false true then List.replicate w.length true else
        if j=lane E E.inputTape false false then w else [] := by
  funext j
  obtain ⟨⟨i,d,b⟩,rfl⟩ := (slot E).surjective j
  change store E _ (lane E i d b)=if lane E i d b=_ then _ else if lane E i d b=_ then _ else _
  rw [store_at]
  by_cases H : i=E.inputTape
  · subst i; cases d <;> cases b <;>
      simp [w5_EntryTapeModel.init,Cells.init,bit,half,List.map_map,Function.comp_def]
  · cases d <;> cases b <;> simp [w5_EntryTapeModel.init,H,Cells.init,half]

theorem callbackBit (E : PrimitiveMachine) (b₀ : Bool) (out : Fin E.tapeCount) :
    ∃ (s l : ℕ) (Q : Program 3 s l) (it iv ot ov : Fin s), it≠iv ∧ ot≠ov ∧
    ∀ (input output : List Bool) (T M : ℝ),RunsWithin E out (b₀::input) output T M →
      ∀ r : Fin 3→Bool,
      let initial : Cfg 3 s l := ⟨some Q.entry,r,fun j =>
        if j=it then List.replicate input.length true else if j=iv then input else []⟩
      ∃ (n : ℕ) (final : Cfg 3 s l), (n:ℝ)≤8*T ∧ BitProgram.Trace Q n initial final ∧
        final.pc=none ∧ ((((final.stacks ot).zip (final.stacks ov)).takeWhile Prod.fst).map Prod.snd)=output ∧
        ∀ k c,k≤n→ BitProgram.Trace Q k initial c→∀ j,(c.stacks j).length≤⌊M⌋₊+8 := by
  let Q := program E out (headBits E b₀)
  refine ⟨S E,L E,Q,lane E E.inputTape false true,lane E E.inputTape false false,
    lane E out false true,lane E out false false,by simp,by simp,?_⟩
  intro input output T M run r initial
  obtain ⟨k,c,ht,hc,hw,hs⟩ := call E out (b₀::input) output T M run r (headBits E b₀)
  rw [initial_headBits,initial_body] at hs
  exact ⟨k,c,ht,hs.trace,hc,(extract_eq _ _).symm.trans hw,fun k c hk tr => hs.prefix hk tr⟩

end DetDLP.w5_M6HeadBit


