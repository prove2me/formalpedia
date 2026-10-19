-- Prove2me | Definitions.Def_QAlgorithms_Defs_ClassicalEntryPrograms
-- name    : QAlgorithms_Defs_ClassicalEntryPrograms
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:20:48.601523+00:00
-- url     : https://prove2.me/theorems/0a02c4ea-7d24-47c0-a210-88fe96eb825a
-- title:
--   ClassicalEntryPrograms
-- statement:
--   ClassicalEntryPrograms
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\ClassicalEntryPrograms.lean

import Definitions.Def_QAlgorithms_Defs_ZeroSumGeometry
noncomputable section

open scoped ENNReal

namespace QAlgorithms.ZeroSum

variable {n m d k b w M K N c out : ℕ}

/-- Ideal numerical memory and actual entry-read trace, 1904.03180 pp.5–6. -/
structure EntryState (n m : ℕ) where
  memory : ℕ → ℝ
  trace : List (Fin n × Fin m)
  work : ℕ
  failed : Bool

/-- Numerical instructions for the proof's unit-work model (1904.03180 p.6).
The finite array primitives expand to linear scans, whose work is charged. -/
inductive EntryInstruction where
  | constant (dst : ℕ) (value : ℝ)
  | add (dst a b : ℕ)
  | mul (dst a b : ℕ)
  | div (dst a b : ℕ)
  | exp (dst a : ℕ)
  | entry (dst row col : ℕ)
  | load (dst base index : ℕ)
  | store (base index src : ℕ)
  | sum (dst base length : ℕ)
  | sample (dst base length : ℕ)
  | compare (a b : ℕ)

/-- Cost of expanded numerical instructions (1904.03180 p.6).
Sampling includes weight reads, normalization, cumulative sums and a search. -/
def EntryInstruction.work : EntryInstruction → ℕ
  | .sum _ _ k => 2 * k + 1
  | .sample _ _ k => 5 * k + 1
  | _ => 1

/-- The ideal finite array-sampling PMF, 1904.03180 p.6; division is guarded. -/
def arrayDistribution (v : Fin k → ℝ) (h0 : ∀ i, 0 ≤ v i) (hs : 0 < ∑ i, v i) : PMF (Fin k) :=
  PMF.ofFintype (fun i => ENNReal.ofReal (v i / ∑ j, v j)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => div_nonneg (h0 i) hs.le)]
    rw [← Finset.sum_div, div_self hs.ne']
    simp)

/-- Execute one instruction; only entry reads can inspect A
(1904.03180 pp.5–6). Invalid divisions/indices fail and preserve traces. -/
def entryInstructionLaw {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ)
    (op : EntryInstruction) (s : EntryState n m) : PMF (Bool × EntryState n m) := by
  classical
  let st := { s with work := s.work + op.work }
  let set (dst : ℕ) (v : ℝ) := (false, { st with memory := Function.update st.memory dst v })
  let fail := (false, { st with failed := true })
  exact if s.failed then PMF.pure (false, s) else match op with
    | .constant dst v => PMF.pure (set dst v)
    | .add dst a b => PMF.pure (set dst (s.memory a + s.memory b))
    | .mul dst a b => PMF.pure (set dst (s.memory a * s.memory b))
    | .div dst a b => if s.memory b = 0 then PMF.pure fail
        else PMF.pure (set dst (s.memory a / s.memory b))
    | .exp dst a => PMF.pure (set dst (Real.exp (s.memory a)))
    | .entry dst row col =>
        let i := ⌊s.memory row⌋₊
        let j := ⌊s.memory col⌋₊
        if h : i < n ∧ j < m then
          PMF.pure (false, { st with
            memory := Function.update st.memory dst (A ⟨i,h.1⟩ ⟨j,h.2⟩)
            trace := st.trace ++ [(⟨i,h.1⟩, ⟨j,h.2⟩)] })
        else PMF.pure fail
    | .load dst base idx => PMF.pure (set dst (s.memory (base + ⌊s.memory idx⌋₊)))
    | .store base idx src => PMF.pure (set (base + ⌊s.memory idx⌋₊) (s.memory src))
    | .sum dst base k => PMF.pure (set dst (∑ i : Fin k, s.memory (base + i.val)))
    | .sample dst base k =>
        if h : (∀ i : Fin k, 0 ≤ s.memory (base + i.val)) ∧
            0 < ∑ i : Fin k, s.memory (base + i.val) then
          (arrayDistribution (fun i : Fin k => s.memory (base + i.val)) h.1 h.2).map
            (fun i => set dst i.val)
        else PMF.pure fail
    | .compare a b => PMF.pure (decide (s.memory a ≤ s.memory b), st)

/-- Classical randomized entry program with branching and counted loops,
1904.03180 pp.5–6. Program data precede A. -/
inductive ClassicalEntryProgram where
  | done
  | step (op : EntryInstruction) (next : Bool → ClassicalEntryProgram)
  | loop (count : ℕ) (body rest : ClassicalEntryProgram)

/-- Actual operational law, including oracle trace and numerical work,
1904.03180 p.6. Independent draws are obtained by PMF composition. -/
def entryProgramLaw {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) :
    ClassicalEntryProgram → EntryState n m → PMF (EntryState n m)
  | .done, s => PMF.pure s
  | .step op next, s => (entryInstructionLaw A op s).bind fun p => entryProgramLaw A (next p.1) p.2
  | .loop k body rest, s =>
      ((List.range k).foldl (fun law _ => law.bind (entryProgramLaw A body)) (PMF.pure s)).bind
        (entryProgramLaw A rest)

/-- Straight-line compilation from numerical operations, 1904.03180 p.6. -/
def entrySteps (ops : List EntryInstruction) : ClassicalEntryProgram :=
  ops.foldr (fun op rest => .step op fun _ => rest) .done

/-- Sequential composition of source programs, 1904.03180 p.6. -/
def entryThen : ClassicalEntryProgram → ClassicalEntryProgram → ClassicalEntryProgram
  | .done, Q => Q
  | .step op next, Q => .step op fun b => entryThen (next b) Q
  | .loop k body rest, Q => .loop k body (entryThen rest Q)

/-- Sanity check for the modeled source objects (arxiv-1904.03180v1, PDF pp.5,6). -/
example {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (s : EntryState n m) :
    entryProgramLaw A .done s = PMF.pure s := rfl

/-- Sanity check for the modeled source objects (arxiv-1904.03180v1, PDF pp.5,6). -/
example (a b : Matrix (Fin 1) (Fin 1) ℝ) (s : EntryState 1 1) :
    entryProgramLaw a (entrySteps [.constant 0 7]) s =
      entryProgramLaw b (entrySteps [.constant 0 7]) s := rfl

end QAlgorithms.ZeroSum


