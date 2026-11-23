-- Prove2me | Definitions.Def_DetANN_RunComposition
-- name    : DetANN_RunComposition
-- status  : Definition
-- author  : @Mr Robbins
-- created : 2026-11-23T03:20:15.186376+00:00
-- url     : https://prove2.me/theorems/89a8c0da-4f65-4b76-b9db-529391ae11c8
-- title:
--   Sequential run and written-cell composition for the real RAM
-- statement:
--   This utility module exposes the two sequential-composition equations for the PNormReg real RAM. For any program, initial state, tape, and natural numbers $a,b$,
--   $$
--   \operatorname{run}(P,s,\omega,a+b)=\operatorname{run}(P,\operatorname{run}(P,s,\omega,a),\omega,b).
--   $$
--   On the deterministic tape, written-cell accounting splits in the same way:
--   $$
--   \operatorname{cellsWritten}(P,s,a+b)=\operatorname{cellsWritten}(P,s,a)\cup
--   \operatorname{cellsWritten}(P,\operatorname{run}(P,s,\mathrm{detTape},a),b).
--   $$
--   These identities allow preprocessing and query drivers to combine work and space estimates one program block at a time.
-- source:
--   Original structural utility lemmas for the PNormReg machine (Definitions Def_PNormReg_Machine and Def_DetANN_DataStructure), written for the machine composition in Feng--Indyk, STOC 2027 submission, §7.4, p.19. They formalize iteration addition and the defining biUnion of cellsWritten.

import Mathlib
import Definitions.Def_PNormReg_Machine
import Definitions.Def_DetANN_DataStructure

namespace PNormReg

/-- Running for `a + b` steps is running for `a` steps and then for `b` steps. -/
theorem run_add (P : Program) (s : State) (ω : ℕ → Bool) (a b : ℕ) :
    run P s ω (a + b) = run P (run P s ω a) ω b := by
  rw [Nat.add_comm a b]
  simp only [run, Function.iterate_add_apply]

end PNormReg

namespace DetANN

open PNormReg

/-- Cells written in two consecutive run segments form the union of the two segment accounts. -/
theorem cellsWritten_add (P : Program) (s : State) (a b : ℕ) :
    cellsWritten P s (a + b) = cellsWritten P s a ∪
      cellsWritten P (run P s detTape a) b := by
  ext c
  simp only [cellsWritten, Finset.mem_biUnion, Finset.mem_range, Finset.mem_union]
  constructor
  · rintro ⟨i, hi, hc⟩
    by_cases hia : i < a
    · exact Or.inl ⟨i, hia, hc⟩
    · refine Or.inr ⟨i - a, by omega, ?_⟩
      have hsum : a + (i - a) = i := by omega
      rw [← hsum, PNormReg.run_add] at hc
      exact hc
  · rintro (⟨i, hi, hc⟩ | ⟨j, hj, hc⟩)
    · exact ⟨i, by omega, hc⟩
    · refine ⟨a + j, by omega, ?_⟩
      rwa [PNormReg.run_add]

end DetANN


