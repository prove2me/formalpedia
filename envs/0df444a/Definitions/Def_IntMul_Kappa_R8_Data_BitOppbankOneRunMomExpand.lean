-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRunMomExpand
-- name    : IntMul_Kappa_R8_Data_BitOppbankOneRunMomExpand
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T18:10:33.724999+00:00
-- url     : https://prove2.me/theorems/7fe078b1-4150-4d05-a70d-3f39f5df9ecd
-- title:
--   OneRun2 moment packaging: AllOneRun + WidthsEqOppbank ⇒ net_mom
-- statement:
--   # OneRunMomExpand
--
--   Packages the edge-moment identity for the corrected one-run network:
--   $$\mathrm{AllOneRun}\wedge\mathrm{WidthsEqOppbank}\implies
--   \sum_e\mathrm{EM}_\tau(e)=\mathrm{histMoment}(\mathrm{oppbankHist},529,\tau).$$
--
--   Proved ingredients include $\mathrm{EM}(\mathrm{dfltE})=0$, $\mathrm{EM}=\mathrm{oneRunV}$ on `oneRun` edges, `pickE` witness extraction, and the reduction `net_mom_of_packs`.
--
--   **Formalization Note.** Depends on OneRun2 / OneRunMom2 / OneRunPE2.
-- source:
--   OneRun2 e0d447f6; OneRunMom2 a4deb37c; OneRunPE2 b8f301c1

import Mathlib
import Definitions.Def_IntMul_KappaFramework
import Definitions.Def_IntMul_KappaJainData
import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRunMom2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRunPE2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankHist
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankMomPack

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.dupNamespace false

/-!
# OneRunMomExpand — PE collapse + hist packaging toward `net0O2_net_mom`

Proved: `EM_dflt`, `EM_of_oneRun`, `pickE_of_exists`, `EM_eq_edgeMom_of_AllOneRun`,
`net_mom_of_packs`.
-/

namespace IntMul.Kappa.R8.Bit.Oppbank.OneRunMomExpand

open IntMul.Kappa
open IntMul.Kappa.Jain
open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R6.Bit.NB
open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.OneRunMom2
open IntMul.Kappa.R8.Bit.Oppbank.OneRunPE2
open IntMul.Kappa.R8.Bit.Oppbank.MomPack

section Mom
variable (τ : ℝ)

theorem EM_dflt : EM τ dfltE = 0 := by
  simp [EM, dfltE]

theorem EM_of_oneRun {r : ℕ} {e : Edge 529} (h : oneRun r e.runs) :
    EM τ e = oneRunV τ r :=
  EM_oneRun τ h

theorem oneRunV_eq_fw (r : ℕ) : oneRunV τ r = fw τ r := rfl

theorem EM_eq_fw_of_oneRun {r : ℕ} {e : Edge 529} (h : oneRun r e.runs) :
    EM τ e = fw τ r := by
  rw [EM_of_oneRun τ h, oneRunV_eq_fw]

theorem runs_of_oneRun {r : ℕ} {e : Edge 529} (h : oneRun r e.runs) :
    e.runs = [(0, 0, r)] := h.2.2

theorem pickE_of_exists {P : Edge 529 → Prop} (h : ∃ e, P e) :
    P (pickE P) := by
  classical
  unfold pickE
  simp [dif_pos h]
  exact Classical.choose_spec h

theorem pickE_eq_dflt_of_empty {P : Edge 529 → Prop} (h : ¬ ∃ e, P e) :
    pickE P = dfltE := by
  classical
  unfold pickE
  simp [dif_neg h]

def headW (e : Edge 529) : ℕ := e.runs.head?.map (·.2.2) |>.getD 0

theorem headW_of_oneRun {r : ℕ} {e : Edge 529} (h : oneRun r e.runs) :
    headW e = r := by
  simp [headW, runs_of_oneRun h]

theorem headW_dflt : headW dfltE = 0 := by
  simp [headW, dfltE]

theorem EM_of_oneRun_headW {r : ℕ} {e : Edge 529} (h : oneRun r e.runs) :
    EM τ e = oneRunV τ (headW e) := by
  rw [headW_of_oneRun h, EM_of_oneRun τ h]

/-- Every network edge is default or a true one-run. -/
def AllOneRun : Prop :=
  ∀ e ∈ net0O.edges, e = dfltE ∨ ∃ r, oneRun r e.runs

/-- Edge moment: `0` on empty runs, else `oneRunV` of head width. -/
noncomputable def edgeMom (τ : ℝ) (e : Edge 529) : ℝ :=
  match e.runs with
  | [] => 0
  | _ => oneRunV τ (headW e)

theorem EM_eq_edgeMom_of_AllOneRun (h : AllOneRun) (τ : ℝ) (e : Edge 529)
    (he : e ∈ net0O.edges) : EM τ e = edgeMom τ e := by
  rcases h e he with hd | ⟨r, hr⟩
  · rw [hd, EM_dflt]
    simp [edgeMom, dfltE]
  · have hrs : e.runs = [(0, 0, r)] := runs_of_oneRun hr
    simp only [edgeMom, hrs]
    exact EM_of_oneRun_headW τ hr

def WidthsEqOppbank : Prop :=
  ∀ τ : ℝ, (net0O.edges.map (edgeMom τ)).sum = histMoment oppbankHist 529 τ

theorem net_mom_of_packs (hA : AllOneRun) (hW : WidthsEqOppbank) (τ : ℝ) :
    (net0O.edges.map (EM τ)).sum = histMoment oppbankHist 529 τ := by
  have h1 : net0O.edges.map (EM τ) = net0O.edges.map (edgeMom τ) :=
    List.map_congr_left fun e he => EM_eq_edgeMom_of_AllOneRun hA τ e he
  rw [h1, hW τ]

end Mom

def Nsq : ℕ := 1771 * 1771
theorem Nsq_eq : Nsq = 3136441 := by decide
theorem width_ei_ex : 22 = 23 - 1 := by decide
theorem width_en : 484 = 529 - 2 * 23 + 1 := by decide

end IntMul.Kappa.R8.Bit.Oppbank.OneRunMomExpand


