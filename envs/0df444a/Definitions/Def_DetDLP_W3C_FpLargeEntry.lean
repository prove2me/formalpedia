-- Prove2me | Definitions.Def_DetDLP_W3C_FpLargeEntry
-- name    : DetDLP_W3C_FpLargeEntry
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-25T01:18:54.244752+00:00
-- url     : https://prove2.me/theorems/8b38bee3-690f-40de-93df-5141d827289a
-- title:
--   Finite-field large-entry trace
-- statement:
--   Certified large-prime preprocessing prefix for the Stage-II trace
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_W3C_FpLoopSound

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace DetDLP.W3C.FpLargeEntry
open FpStep FpLoopSound FpOracles NineOracleLoop FpTraceStep DetDLP_W1_Queries
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open MachineComposition

variable {en de : Port} (kit : Kit en de)

noncomputable abbrev prepAnswer {p : ℕ} (L : Plan p) := Encoding.encodeList id [countWord p,m89_fp_plan_word L]
abbrev saved (p g a : ℕ) := packState (start 2 (encodeFpDLPInput p g a))
noncomputable abbrev next {p : ℕ} (g a : ℕ) (L : Plan p) := prepared (saved p g a, prepAnswer L)
abbrev stepFn := FpStep.step resume
abbrev calls (t s : ℝ) := NineCall (family kit) (outputs kit) t s

theorem first_call (p g a : ℕ) (hg : w3_large p (p-1)) :
    stepFn (pairWord (encodeFpDLPInput p g a) []) = false :: pairWord (saved p g a) (tag9 1 (countWord p)) := by
  have hc := NewtonPoly.largeCheck_correct p (p-1)
  unfold stepFn; rw [FpStep.step_entry]; unfold entry
  simp only [encodeFpDLPInput,w5_M6Sort.decode_encode,List.getD_cons_zero]
  change (if NewtonPoly.largeCheck p (p-1) then _ else _) = _
  rw [hc.mpr hg,if_pos rfl]
  simp [saved,call,queryInput,start,encodeFpDLPInput]

theorem second_call {p : ℕ} (g a : ℕ) (L : Plan p) :
    stepFn (pairWord (saved p g a) (prepAnswer L)) =
      false :: pairWord (packState (next g a L)) (tag9 2 (prepAnswer L)) := by
  unfold stepFn saved; rw [FpStep.step_saved]; change call 2 _ _ = _
  simp [call,queryInput,next,prepared,saved,start,encodeFpDLPInput,prepAnswer,second]

/-- The first two calls use the same certified plan; extend any phase-3 continuation
    by exactly those two rounds. The prefix cap accounts also for the answer words. -/
theorem enter {p : ℕ} [Fact p.Prime] (g a : ℕ) (hg : w3_large p (p-1))
    (t s : ℝ) (ht₁ : mainSpaceBound kit.prepC (bitLen p) ≤ t)
    (hs₁ : polyBound kit.prepC (bitLen p) ≤ s)
    (ht₂ : mainSpaceBound kit.enumC (bitLen p) ≤ t)
    (hs₂ : mainSpaceBound kit.enumC (bitLen p) ≤ s) :
    ∃ (L : Plan p) (B : Blocks p), m89_fp_plan_ok L ∧
      (∀ i, (B i).Nodup ∧ (B i).toFinset = m89_fp_plan_block L i) ∧
      ∀ n r y, let w := encodeFpDLPInput p g a; let v := saved p g a
               let v' := packState (next g a L); let z := prepAnswer L
               (pairWord w []).length ≤ n → (pairWord v (tag9 1 (countWord p))).length ≤ n →
               z.length ≤ n → (pairWord v z).length ≤ n → (pairWord v' (tag9 2 z)).length ≤ n →
               (encodeFpFactorBlocks B).length ≤ n →
               LoopRuns stepFn (calls kit t s) r v' (encodeFpFactorBlocks B) y n →
               LoopRuns stepFn (calls kit t s) (r+2) w [] y n := by
  obtain ⟨L,ok,r₁⟩ := kit.prep p
  obtain ⟨B,hB,r₂⟩ := kit.enumerate p L ok
  refine ⟨L,B,ok,hB,?_⟩
  intro n r y w v v' z h₀ h₁ hz hv h₂ hB' tail
  exact Or.inr ⟨v,_,z,first_call p g a hg,h₀,h₁,hz,
    ⟨1,_,rfl,runsWithin_mono r₁ ht₁ hs₁⟩,Or.inr ⟨v',_,_,second_call g a L,hv,h₂,hB',
      ⟨2,_,rfl,runsWithin_mono r₂ ht₂ hs₂⟩,tail⟩⟩

end DetDLP.W3C.FpLargeEntry


