-- Prove2me | Definitions.Def_SubspaceEvasion312_GMC_exec
-- name    : SubspaceEvasion312_GMC_exec
-- status  : Definition
-- author  : @Mr Robbins
-- created : 2026-11-23T03:27:28.628803+00:00
-- url     : https://prove2.me/theorems/b6836a9d-980a-4607-a9a0-8c2356ad7b56
-- title:
--   Successful-run traces and indexed relocation for the matrix compiler
-- statement:
--   This reusable execution module converts a successful bounded `runFrom` evaluation into a non-halt `reach` trace ending at an explicit halt, and proves initial/final register bounds and monotonicity of the two output lists. It also defines indexed relocation `reloc2`, implemented by `List.flatMap` over `zipIdx`, the post-exit register invariant `ExitB`, and a per-block size estimate. Each four-instruction relocated block costs at most $4+\log_2(\mathrm{fieldBase})$ extra size beyond its source instruction.
--
--   **Formalization Note.** The source instruction's register bound is required at every transition by `runFrom`; the trace conversion retains the final bound and halt instruction explicitly.
-- source:
--   Supporting generic operational infrastructure for STOC 2027 submission #312, Theorem 17's explicit linear-code programs, printed p.10 (PDF p.11); complexity conventions in Theorem 8's proof, printed pp.7–8 (PDF pp.8–9).

import Definitions.Def_SubspaceEvasion312_GMC_memory

set_option maxHeartbeats 800000
namespace SubspaceEvasion312.Explicit.Dev.GMC
open SubspaceEvasion312.Explicit
variable {F : Type} [Field F]

/-- Indexed four-instruction relocation, with the exit address available in halt blocks. -/
def reloc2From (natBase fieldBase na : ℕ) (nm : ℕ → ℕ) (fo no base exit start : ℕ)
    (P : Program F) : Program F :=
  (P.zipIdx start).flatMap fun x => blk2 natBase fieldBase na nm fo no base exit x.2 x.1

def reloc2 (natBase fieldBase na : ℕ) (nm : ℕ → ℕ) (fo no base exit : ℕ)
    (P : Program F) : Program F :=
  reloc2From natBase fieldBase na nm fo no base exit 0 P

/-- The register part of the relocated-call invariant after the translated halt jump. -/
structure ExitB (natBase fieldBase fo no B exit : ℕ)
    (z w₀ w : MachineState F) : Prop where
  pc : w.pc = exit
  subN : ∀ j, w.natReg (N natBase j) = z.natReg j
  mainN : ∀ a < natBase, w.natReg a = if a = no then z.natOut.reverse.getD 0 0 else w₀.natReg a
  subF : ∀ j, w.fieldReg (A fieldBase j) = z.fieldReg j
  mainF : ∀ a < fieldBase, w.fieldReg a = if a = fo then z.out.reverse.getD 0 0 else w₀.fieldReg a
  bnd : ∀ j, w.natReg j ≤ B
  out : w.out = w₀.out
  nout : w.natOut = w₀.natOut

lemma runFrom_left_bnd {P : Program F} {ns : List ℕ} {xs : List F} {B t : ℕ}
    {z z' : MachineState F} (h : runFrom P ns xs B t z = some z') :
    ∀ i, z.natReg i ≤ B := by
  cases t with
  | zero => simp [runFrom] at h
  | succ t =>
    simp only [runFrom] at h
    split at h
    · assumption
    · simp at h

lemma runFrom_nonhalt {P : Program F} {ns : List ℕ} {xs : List F} {B t : ℕ}
    {z : MachineState F} {ins : Instruction F} (hb : ∀ i, z.natReg i ≤ B)
    (hc : P[z.pc]? = some ins) (hh : ins ≠ .halt) :
    runFrom P ns xs B (t+1) z = runFrom P ns xs B t (eff ns xs z ins) := by
  cases ins <;> simp_all [runFrom, step_eq]

lemma runFrom_final_bnd {P : Program F} {ns : List ℕ} {xs : List F} {B t : ℕ}
    {z z' : MachineState F} (h : runFrom P ns xs B t z = some z') :
    ∀ i, z'.natReg i ≤ B := by
  induction t generalizing z with
  | zero => simp [runFrom] at h
  | succ t ih =>
    have hb := runFrom_left_bnd h
    cases hc : P[z.pc]? with
    | none => simp [runFrom, hb, hc, step] at h
    | some ins =>
      by_cases hh : ins = .halt
      · subst ins
        have hz : z' = z := by simpa [runFrom, hb, hc] using h.symm
        simpa [hz] using hb
      · rw [runFrom_nonhalt hb hc hh] at h
        exact ih h

lemma step_output_lengths {P : Program F} {ns : List ℕ} {xs : List F}
    {z z₁ : MachineState F} {ins : Instruction F}
    (hc : P[z.pc]? = some ins) (hs : step P ns xs z = some z₁) :
    z.out.length ≤ z₁.out.length ∧ z.natOut.length ≤ z₁.natOut.length := by
  cases ins <;> simp_all [step] <;> cases hs <;> simp

lemma runFrom_output_lengths {P : Program F} {ns : List ℕ} {xs : List F} {B t : ℕ}
    {z z' : MachineState F} (h : runFrom P ns xs B t z = some z') :
    z.out.length ≤ z'.out.length ∧ z.natOut.length ≤ z'.natOut.length := by
  induction t generalizing z with
  | zero => simp [runFrom] at h
  | succ t ih =>
    have hb := runFrom_left_bnd h
    cases hc : P[z.pc]? with
    | none => simp [runFrom, hb, hc, step] at h
    | some ins =>
      by_cases hh : ins = .halt
      · subst ins
        have hz : z' = z := by simpa [runFrom, hb, hc] using h.symm
        subst z'; exact ⟨Nat.le_refl _, Nat.le_refl _⟩
      · rw [runFrom_nonhalt hb hc hh] at h
        have hs : step P ns xs z = some (eff ns xs z ins) := step_eq hc hh
        have h₁ := step_output_lengths hc hs
        have h₂ := ih h
        exact ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩

/-- A successful timed run is precisely a bounded non-halt trace followed by a halt. -/
lemma runFrom_reach {P : Program F} {ns : List ℕ} {xs : List F} {B t : ℕ}
    {z z' : MachineState F} (h : runFrom P ns xs B t z = some z') :
    ∃ n, n < t ∧ reach P ns xs B n z z' ∧ P[z'.pc]? = some .halt ∧
      (∀ i, z'.natReg i ≤ B) := by
  induction t generalizing z with
  | zero => simp [runFrom] at h
  | succ t ih =>
    have hb := runFrom_left_bnd h
    cases hc : P[z.pc]? with
    | none => simp [runFrom, hb, hc, step] at h
    | some ins =>
      by_cases hh : ins = .halt
      · subst ins
        have hz : z' = z := by simpa [runFrom, hb, hc] using h.symm
        subst z'
        exact ⟨0, by omega, reach.zero _, hc, hb⟩
      · rw [runFrom_nonhalt hb hc hh] at h
        obtain ⟨n, hn, hr', hhalt, hb'⟩ := ih h
        exact ⟨n+1, by omega, reach.succ ins hb hc hh hr', hhalt, hb'⟩

/-- Every relocated block charges a bounded number of instructions beyond its source. -/
lemma blk2_programSize (natBase fieldBase na : ℕ) (nm : ℕ → ℕ)
    (fo no base exit p : ℕ) (ins : Instruction F) :
    programSize (blk2 natBase fieldBase na nm fo no base exit p ins) ≤
      instructionSize ins + (4 + fieldBase.log2) := by
  cases ins <;> simp [programSize, blk2, pad, tr2, instructionSize]
  all_goals try split_ifs
  all_goals try simp [programSize, instructionSize]
  all_goals omega

end SubspaceEvasion312.Explicit.Dev.GMC


