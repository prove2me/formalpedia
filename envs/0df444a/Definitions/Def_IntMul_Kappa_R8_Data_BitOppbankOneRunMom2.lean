-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRunMom2
-- name    : IntMul_Kappa_R8_Data_BitOppbankOneRunMom2
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T17:35:00.495922+00:00
-- url     : https://prove2.me/theorems/a4deb37c-6800-40fb-af60-1b9fdadb7796
-- title:
--   Corrected one-run edge moments (EM = fw r)
-- statement:
--   # OneRunMom2 — corrected edge-moment algebra
--
--   With `OneRun2.oneRun` (single run of width $r$), the edge moment collapses to
--   $$\mathrm{EM}_\tau(e)=\Bigl(\frac{r}{529}\Bigr)^\tau.$$
--   Package lemmas: `EM_oneRun`, `hist_mom_net0O`, and `momEqO_of_hist_eq` reducing the moment identity to matching `net0O.hist` against `oppbankHist` (MomPack identifies the latter with `Jain.bitR8`).
--
--   **Formalization Note.** Namespace `OneRunMom2`; carrier `OneRunNet2.net0O`.
-- source:
--   OneRun2 e0d447f6; MomPack cddcbe7a; Hist cb4b257b

import Mathlib
import Definitions.Def_IntMul_KappaFramework
import Definitions.Def_IntMul_KappaJainData
import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankMomPack
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankHist

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
set_option linter.dupNamespace false

/-!
# OneRunMom2 — corrected edge-moment algebra

`oneRun r rs` (single run of width `r`) ⇒ `EM = fw τ r`.
-/

namespace IntMul.Kappa.R8.Bit.Oppbank.OneRunMom2

open IntMul.Kappa
open IntMul.Kappa.Jain
open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.MomPack

section Mom
variable (τ : ℝ)

noncomputable def fw (w : ℕ) : ℝ := ((w : ℝ) / 529) ^ τ

noncomputable def EM (e : Edge 529) : ℝ := (e.runs.map fun ρ => fw τ ρ.2.2).sum

noncomputable def oneRunV (r : ℕ) : ℝ := fw τ r

theorem EM_oneRun {r : ℕ} {e : Edge 529} (h : oneRun r e.runs) :
    EM τ e = oneRunV τ r := by
  obtain ⟨hr, hrm, hrs⟩ := h
  simp [EM, hrs, oneRunV, fw]

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

theorem hist_mom_net0O (τ : ℝ) :
    histMoment net0O.hist 529 τ = (net0O.edges.map (EM τ)).sum :=
  hist_mom τ net0O

theorem hist_target (τ : ℝ) :
    histMoment oppbankHist 529 τ = histMoment bitR8 529 τ :=
  histMoment_oppbank_bitR8_529 τ

def MomEqStmtO : Prop :=
  ∀ τ : ℝ, histMoment net0O.hist 529 τ = histMoment bitR8 529 τ

theorem momEqO_of_hist_eq
    (h : ∀ τ : ℝ, histMoment net0O.hist 529 τ = histMoment oppbankHist 529 τ) :
    MomEqStmtO := fun τ => (h τ).trans (hist_target τ)

end Mom

end IntMul.Kappa.R8.Bit.Oppbank.OneRunMom2


