-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRunMom
-- name    : IntMul_Kappa_R8_Data_BitOppbankOneRunMom
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T17:05:21.435795+00:00
-- url     : https://prove2.me/theorems/3b1af3e6-f0e9-4ea7-b8d0-86096072fb18
-- title:
--   One-run edge-moment algebra toward net0O_mom_eq
-- statement:
--   # One-run edge moments
--
--   For the densified one-run opposite-bank network $\mathrm{net0O}$, an edge whose Bruhat runs satisfy the one-run predicate of width $r$ contributes
--   $$\mathrm{fw}(\tau,r)+(r-1)\cdot\mathrm{fw}(\tau,1)$$
--   to the $\tau$-moment (proved as `EM_oneRun`).
--
--   Also records `hist_mom` (network histogram moment equals the sum of edge moments) and the packaging implication
--   $$\mathrm{histMoment}(\mathrm{net0O.hist})=\mathrm{histMoment}(\mathrm{oppbankHist})
--   \;\Longrightarrow\;
--   \mathrm{histMoment}(\mathrm{net0O.hist})=\mathrm{histMoment}(\mathrm{Jain.bitR8}).$$
--
--   **Formalization Note.** Namespace `IntMul.Kappa.R8.Bit.Oppbank.OneRunMom`.
-- source:
--   Jain round8-oppbank OneRun moment algebra

import Mathlib
import Definitions.Def_IntMul_KappaFramework
import Definitions.Def_IntMul_KappaJainData
import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankMomPack
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankHist

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
set_option linter.dupNamespace false

/-!
# OneRunMom — edge-moment algebra for one-run Bruhat runs

`oneRun r rs` ⇒ histogram contribution `fw τ r + (r-1) * fw τ 1`.
MomEq packaging reduces `net0O_mom_eq` to matching the GenCN/SideRanks expansion
against MomPack `bitR8`.
-/

namespace IntMul.Kappa.R8.Bit.Oppbank.OneRunMom

open IntMul.Kappa
open IntMul.Kappa.Jain
open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet
open IntMul.Kappa.R8.Bit.Oppbank.MomPack

section Mom
variable (τ : ℝ)

noncomputable def fw (w : ℕ) : ℝ := ((w : ℝ) / 529) ^ τ

noncomputable def EM (e : Edge 529) : ℝ := (e.runs.map fun ρ => fw τ ρ.2.2).sum

noncomputable def oneRunV (r : ℕ) : ℝ := fw τ r + ((r - 1 : ℕ) : ℝ) * fw τ 1

theorem sum_ones (rs : List (ℕ × ℕ × ℕ)) (h : ∀ ρ ∈ rs, ρ.2.2 = 1) :
    (rs.map fun ρ => fw τ ρ.2.2).sum = rs.length * fw τ 1 := by
  induction rs with
  | nil => simp
  | cons ρ rs ih =>
    have hρ : ρ.2.2 = 1 := h ρ (by simp)
    have hrs : ∀ ρ' ∈ rs, ρ'.2.2 = 1 := fun ρ' h' => h ρ' (by simp [h'])
    simp [hρ, ih hrs, add_mul, add_comm]

theorem EM_oneRun {r : ℕ} {e : Edge 529} (h : oneRun r e.runs) :
    EM τ e = oneRunV τ r := by
  obtain ⟨rs', hr, h1, hlen⟩ := h
  have hlen' : rs'.length = r - 1 := by
    have : rs'.length + 1 = r := hlen
    omega
  simp only [EM, hr, List.map_cons, List.sum_cons, sum_ones τ rs' h1, oneRunV, hlen']

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

end IntMul.Kappa.R8.Bit.Oppbank.OneRunMom


