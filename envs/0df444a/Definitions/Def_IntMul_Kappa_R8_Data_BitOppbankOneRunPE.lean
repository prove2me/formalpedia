-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRunPE
-- name    : IntMul_Kappa_R8_Data_BitOppbankOneRunPE
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T17:20:17.25193+00:00
-- url     : https://prove2.me/theorems/9699770d-3835-4f4f-8631-fe4e38569171
-- title:
--   oneRun 1 PE inhabitance via edge_of_pivs
-- statement:
--   If $q$ is an idempotent $529\times529$ matrix of rank $1$ with an origin pivot $\mathrm{IsPiv}\,q\,0\,0$, then there exists an edge $e$ realising $\mathrm{PE}\,q\,(\mathrm{oneRun}\,1)\,e$.
--
--   Constructed from the proved R6 lemma `edge_of_pivs`. This is the rank-$1$ base case toward inhabiting one-run PE for `ec` (and hence toward `net0O` moment expansion).
-- source:
--   R6 edge_of_pivs; OneRun oneRun/PE; Jain PR #104

import Mathlib
import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun
import Theorems.Thm_IntMul_Kappa_R6_Bit_NB_edge_of_pivs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

/-!
# OneRun PE inhabitance from `edge_of_pivs`

Rank-1 case: a single pivot at the origin realises `oneRun 1`.
-/

namespace IntMul.Kappa.R8.Bit.Oppbank.OneRunPE

open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R6.Bit.NB
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet
open Matrix

private theorem one_lt_529 : 1 < 529 := by decide

def rs1 : List (ℕ × ℕ × ℕ) := [(0, 0, 1)]

theorem runOK_001 : RunOK 529 (0, 0, 1) := by
  refine ⟨by decide, by decide, ?_, ?_⟩ <;> decide

theorem runPairs_001 : NB.runPairs rs1 = [(0, 0)] := by
  simp [rs1, NB.runPairs]

theorem nodup_001 : (NB.runPairs rs1).Nodup := by
  simp [runPairs_001]

/-- Rank-1 idempotent with origin pivot ⇒ `PE q (oneRun 1)`. -/
theorem oneRun1_of_piv (q : Matrix (Fin 529) (Fin 529) ℚ)
    (hq : q * q = q) (hr : q.rank = 1) (hp : IsPiv q 0 0) :
    ∃ e, PE q (oneRun 1) e := by
  have hok : ∀ ρ ∈ rs1, RunOK 529 ρ := by
    intro ρ hρ; simp [rs1] at hρ; subst hρ; exact runOK_001
  have hpiv : ∀ x ∈ NB.runPairs rs1, IsPiv q x.1 x.2 := by
    intro x hx; simp [runPairs_001] at hx; subst hx; exact hp
  obtain ⟨e, ⟨rs', hrs, h1, hlen⟩, hRun, hE1u, hE1d, hE2u, hE2d, hpsw⟩ :=
    edge_of_pivs (m := 529) one_lt_529 q hq rs1 hok nodup_001 hpiv
  have hlen' : rs'.length = 0 := by
    have : (NB.runPairs rs1).length = 1 := by simp [runPairs_001]
    omega
  have hrs' : rs' = [] := List.eq_nil_of_length_eq_zero hlen'
  have hruns : e.runs = [(0, 0, 1)] := by simp [hrs, hrs', rs1]
  refine ⟨e, ⟨hRun, hE1u, hE1d, hE2u, hE2d, hpsw⟩, ?_⟩
  refine ⟨[], hruns, ?_, by decide⟩
  intro ρ hρ
  cases hρ

end IntMul.Kappa.R8.Bit.Oppbank.OneRunPE


