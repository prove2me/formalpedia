-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRunPE2
-- name    : IntMul_Kappa_R8_Data_BitOppbankOneRunPE2
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T17:36:06.887331+00:00
-- url     : https://prove2.me/theorems/b8f301c1-b86f-4b8e-a9bf-5695a835a4a3
-- title:
--   oneRun r PE inhabitance via edge_of_pivs (no pad)
-- statement:
--   # OneRunPE2 — PE inhabitance for corrected one-run
--
--   If $q$ is an idempotent $529\times529$ matrix of rank $r$ ($0<r<529$) with diagonal origin pivots $\mathrm{IsPiv}\,q\,k\,k$ for all $k<r$, then there exists an edge realising $\mathrm{PE}\,q\,(\mathrm{oneRun}\,r)$.
--
--   Constructed from the proved R6 lemma `edge_of_pivs` with seed run $[(0,0,r)]$; the pad is empty precisely when $\mathrm{rank}=r$, matching Jain's one-child-of-width-$r$ compile.
--
--   **Formalization Note.** Includes rank-$1$ specialization `oneRun1_of_piv`.
-- source:
--   OneRun2 e0d447f6; R6 edge_of_pivs

import Mathlib
import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Theorems.Thm_IntMul_Kappa_R6_Bit_NB_edge_of_pivs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

/-!
# OneRun2 PE inhabitance from `edge_of_pivs`

General rank-`r` case: a contiguous origin run of width `r` with `q.rank = r`
realises `oneRun r` (no singleton pad).
-/

namespace IntMul.Kappa.R8.Bit.Oppbank.OneRunPE2

open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R6.Bit.NB
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open Matrix

private theorem one_lt_529 : 1 < 529 := by decide

def rsR (r : ℕ) : List (ℕ × ℕ × ℕ) := [(0, 0, r)]

theorem runPairs_rsR (r : ℕ) : NB.runPairs (rsR r) = (List.range r).map fun k => (k, k) := by
  simp [rsR, NB.runPairs]

theorem nodup_diag (r : ℕ) : ((List.range r).map fun k => (k, k)).Nodup := by
  have hnd : (List.range r).Nodup := List.nodup_range
  refine (List.nodup_map_iff_inj_on hnd).2 ?_
  intro a ha b hb h
  exact (Prod.ext_iff.1 h).1

theorem nodup_rsR (r : ℕ) : (NB.runPairs (rsR r)).Nodup := by
  simpa [runPairs_rsR] using nodup_diag r

/-- Rank-`r` idempotent with origin diagonal pivots ⇒ `PE q (oneRun r)`. -/
theorem oneRun_of_pivs (r : ℕ) (hr : 0 < r) (hrm : r < 529)
    (q : Matrix (Fin 529) (Fin 529) ℚ)
    (hq : q * q = q) (hrank : q.rank = r)
    (hp : ∀ k, k < r → IsPiv q k k) :
    ∃ e, PE q (oneRun r) e := by
  have hok : ∀ ρ ∈ rsR r, RunOK 529 ρ := by
    intro ρ hρ; simp [rsR] at hρ; subst hρ; exact runOK_origin hr hrm
  have hpiv : ∀ x ∈ NB.runPairs (rsR r), IsPiv q x.1 x.2 := by
    intro x hx
    rw [runPairs_rsR] at hx
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
    exact hp k (List.mem_range.1 hk)
  obtain ⟨e, ⟨rs', hrs, h1, hlen⟩, hRun, hE1u, hE1d, hE2u, hE2d, hpsw⟩ :=
    edge_of_pivs (m := 529) one_lt_529 q hq (rsR r) hok (nodup_rsR r) hpiv
  have hlen_rp : (NB.runPairs (rsR r)).length = r := by
    simp [runPairs_rsR]
  have hrs' : rs' = [] := by
    have : rs'.length = 0 := by omega
    exact List.eq_nil_of_length_eq_zero this
  have hruns : e.runs = [(0, 0, r)] := by simp [hrs, hrs', rsR]
  refine ⟨e, ⟨hRun, hE1u, hE1d, hE2u, hE2d, hpsw⟩, ?_⟩
  exact ⟨hr, hrm, hruns⟩

theorem oneRun1_of_piv (q : Matrix (Fin 529) (Fin 529) ℚ)
    (hq : q * q = q) (hr : q.rank = 1) (hp : IsPiv q 0 0) :
    ∃ e, PE q (oneRun 1) e :=
  oneRun_of_pivs 1 (by decide) (by decide) q hq hr (fun k hk => by
    have : k = 0 := by omega
    simpa [this] using hp)

end IntMul.Kappa.R8.Bit.Oppbank.OneRunPE2


