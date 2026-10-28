-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankNetMom2
-- name    : IntMul_Kappa_R8_Data_BitOppbankNetMom2
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T16:32:19.733065+00:00
-- url     : https://prove2.me/theorems/daa25ede-b9d1-4ea5-a75d-dc27d88ddf7b
-- title:
--   R8 NetMom2: hist_mom + EM algebra + MomPack bitR8
-- statement:
--   Opp-bank moment wiring through `Net0P` toward exact `histMoment = Jain.bitR8`.
--
--   Adds
--   $$\mathrm{histMoment}(C.\mathrm{hist},529,\tau)=\sum_e \mathrm{EM}_\tau(e)$$
--   together with `EM_side`/`EM_aux`/`EM_data` and MomPack `oppbankHist=bitR8`. `MomEqStmt` reduces to matching `net0P.hist` with `oppbankHist` via the edge-moment expansion.
-- source:
--   Pnd 1351eb81; Net0P 373d80bb; MomPack cddcbe7a; GoodPrimes fac3e30f; NetMom 84ad4683

import Mathlib
import Definitions.Def_IntMul_KappaFramework
import Definitions.Def_IntMul_KappaJainData
import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNet
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankProjB
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankNet0P
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankMomPack
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankGenCN
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSideRanks
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankHist
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankWireLayout

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false

/-!
# R8 `net_mom` wiring through `Net0P` (MomPack + GenCN + SideRanks)

Edge-moment algebra (`fw`/`EM`/`sideV`/`auxV`/`dataV`) retargeted to opp-bank
wire constants (`wEnt = 3542`, `wAuxEnd = 31336`, `NR = 27794`, `v = 1771`).

`EM_side` / `EM_aux` / `EM_data` discharge on Defs52 run predicates from ProjB.
Histogram packaging: `oppbankHist = Jain.bitR8` (MomPack) so the open
`mom_eq` leaf is exact equality of `histMoment` once `net_mom` matches
`oppbankHist`.
-/

namespace IntMul.Kappa.R8.Bit.Oppbank.NetMom

open IntMul.Kappa
open IntMul.Kappa.Jain
open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R6.Bit.NB
open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.ProjB
open IntMul.Kappa.R8.Bit.Oppbank.Net0P
open IntMul.Kappa.R8.Bit.Oppbank.MomPack
open IntMul.Kappa.R8.Bit.Oppbank.GenCN

/-! ## Edge moments (Defs52, τ-parametric) -/

section Mom

variable (τ : ℝ)

noncomputable def fw (w : ℕ) : ℝ := ((w : ℝ) / 529) ^ τ

noncomputable def EM (e : Edge 529) : ℝ := (e.runs.map fun ρ => fw τ ρ.2.2).sum

noncomputable def sideV (r : ℕ) : ℝ :=
  if 23 < 2 * r then fw τ (2 * r - 23) + ((23 - r : ℕ) : ℝ) * fw τ 1
  else (r : ℝ) * fw τ 1

/-- Aux runs `[(0,506,23),(23,23,483)]` → widths 23 and 483. -/
noncomputable def auxV : ℝ := fw τ 23 + fw τ 483

/-- Data runs + 24 singletons (Defs52 `DataR`). -/
noncomputable def dataV : ℝ := fw τ 439 + fw τ 21 + 24 * fw τ 1

theorem sum_ones (rs : List (ℕ × ℕ × ℕ)) (h : ∀ ρ ∈ rs, ρ.2.2 = 1) :
    (rs.map fun ρ => fw τ ρ.2.2).sum = rs.length * fw τ 1 := by
  induction rs with
  | nil => simp
  | cons ρ rs ih =>
    have hρ : ρ.2.2 = 1 := h ρ (by simp)
    have hrs : ∀ ρ' ∈ rs, ρ'.2.2 = 1 := fun ρ' h' => h ρ' (by simp [h'])
    simp [hρ, ih hrs, add_mul, add_comm]

theorem EM_side {r : ℕ} {e : Edge 529} (h : SideR r e.runs) : EM τ e = sideV τ r := by
  obtain ⟨rs', hr, h1, hlen⟩ := h
  simp only [EM, hr, List.map_append, List.sum_append, sum_ones τ rs' h1, sideV]
  unfold sideRuns at hlen ⊢
  by_cases hc : 23 < 2 * r
  · simp only [if_pos hc] at hlen ⊢
    have hl : (runPairs [(23 - r, 529 - r, 2 * r - 23)]).length = 2 * r - 23 := by
      simp [runPairs]
    rw [hl] at hlen
    have hrs' : rs'.length = 23 - r := by omega
    simp [hrs']
  · simp only [if_neg hc] at hlen ⊢
    have hl : (runPairs ([] : List (ℕ × ℕ × ℕ))).length = 0 := rfl
    rw [hl, zero_add] at hlen
    simp [hlen]

theorem EM_aux {e : Edge 529} (h : AuxR e.runs) : EM τ e = auxV τ := by
  have hrs : e.runs = auxRuns 19 := h
  simp only [EM, hrs, auxRuns, auxV, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero, fw]

theorem EM_data {e : Edge 529} (h : DataR e.runs) : EM τ e = dataV τ := by
  obtain ⟨rs', hr, h1, hlen⟩ := h
  simp only [EM, hr, List.map_append, List.sum_append, sum_ones τ rs' h1, hlen, dataV]
  simp only [dataRuns, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, fw]
  norm_num

end Mom

/-! ## R8 entrance / aux widths (vs R6 `3542` / `40077`) -/

theorem wEnt_eq : wEnt = 3542 := rfl
theorem wAuxEnd_eq : wAuxEnd = 31336 := rfl
theorem NR_eq : NR = 27794 := rfl
theorem aux_len : wAuxEnd - wEnt = 27794 := by decide
theorem v_eq : v = 1771 := rfl

/-! ## GenCN / SideRanks / MomPack hooks -/

theorem hist_target (τ : ℝ) :
    histMoment oppbankHist 529 τ = histMoment bitR8 529 τ :=
  histMoment_oppbank_bitR8_529 τ

theorem sideRanks_total : sideChainRankHist_count = 162155 := sideRanks_count

theorem DC_pack_0 : DC 0 = 34016 := DC_0


/-! ## hist_mom: network histogram moment = edge EM sum -/

theorem hist_mom (τ : ℝ) (C : QHNet (ZMod 2) 104719230 3217907 529) :
    histMoment C.hist 529 τ = (C.edges.map (EM τ)).sum := by
  unfold histMoment QHNet.hist QHNet.widths
  generalize C.edges = l
  induction l with
  | nil => rfl
  | cons e l ih =>
    rw [List.flatMap_cons, List.map_append, List.map_append, List.sum_append, ih, List.map_cons,
      List.sum_cons]
    congr 1
    rw [EM, List.map_map, List.map_map]
    refine congrArg List.sum (List.map_congr_left fun ρ _ => ?_)
    simp [fw]

theorem hist_mom_net0P (τ : ℝ) :
    histMoment net0P.hist 529 τ = (net0P.edges.map (EM τ)).sum :=
  hist_mom τ net0P

/-- Open `mom_eq` packaging: network histMoment equals Jain once `net_mom` hits `oppbankHist`. -/
def MomEqStmt : Prop :=
  ∀ τ : ℝ, histMoment net0P.hist 529 τ = histMoment bitR8 529 τ

/-- Partial discharge: target histogram identity (independent of edge expansion). -/
theorem momEq_of_hist_eq
    (h : ∀ τ : ℝ, histMoment net0P.hist 529 τ = histMoment oppbankHist 529 τ) :
    MomEqStmt := fun τ => (h τ).trans (hist_target τ)

/-- Named network for packaging `⟨Tmp, net0P, …⟩`. -/
theorem net0P_Tmp : Tmp = 3217907 := net0P_T

end IntMul.Kappa.R8.Bit.Oppbank.NetMom


