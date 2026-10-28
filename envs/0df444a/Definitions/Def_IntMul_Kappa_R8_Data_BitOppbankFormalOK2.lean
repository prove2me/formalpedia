-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankFormalOK2
-- name    : IntMul_Kappa_R8_Data_BitOppbankFormalOK2
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T16:40:36.356711+00:00
-- url     : https://prove2.me/theorems/d78bc747-6623-40e8-a544-015a3214845d
-- title:
--   R8 EdgesOK via good_edges + mom packaging on Net0Pnd
-- statement:
--   Expands FormalOKFeed with the proved R6 lemmas `good_edges`/`good_mats`.
--
--   Discharges
--
--   $$\exists q_0,\;\forall q>q_0\ \mathrm{prime},\;\forall f,\;\mathrm{EdgesOK}(\mathrm{net0Pnd},q^f)$$
--
--   (`edges_good`, `EdgesOK_large`, `net0_runs_edges`). Also packages `MomEqStmtPnd` (network hist vs MomPack `bitR8`) and `EM0_good`.
--
--   Open for full `net0_ok`: `FormalOK` via full `FB0_ex`/`e*_spec`, and `mom_eq` once flag-basis edges realise SideR/AuxR/DataR matching `bitR8`.
-- source:
--   Jain R8 opp-bank; FormalOKFeed 112701fa; R6 good_edges 3935173d; good_mats ff209901; MomPack cddcbe7a

import Mathlib
import Definitions.Def_IntMul_KappaFramework
import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_KappaJainData
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankFormalOK
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankNetMom
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankMomPack
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankNet0Pnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Theorems.Thm_IntMul_Kappa_R6_Bit_NB_good_edges
import Theorems.Thm_IntMul_Kappa_R6_Bit_NB_good_mats

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

/-!
# FormalOK2 — EdgesOK via good_edges + mom_eq packaging on Net0Pnd

Uses proved R6 `good_edges` / `good_mats` on FormalOKFeed.`E0`/`E0_Q`.
Discharges the EdgesOK half of `net0_ok` for `net0Pnd`. FormalOK still needs
full `FB0_ex` / `e*_spec`. MomEq reduces to hist identity vs MomPack `bitR8`.
-/

namespace IntMul.Kappa.R8.Bit.Oppbank.FormalOK2

open IntMul.Kappa
open IntMul.Kappa.Jain
open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R6.Bit.NB
open IntMul.Kappa.R6.Bit.QHNet (RunsOK EdgesOK FormalOK)
open IntMul.Kappa.R8.Bit.Oppbank.FormalOKFeed
open IntMul.Kappa.R8.Bit.Oppbank.Net0Pnd
open IntMul.Kappa.R8.Bit.Oppbank.NetMom
open IntMul.Kappa.R8.Bit.Oppbank.MomPack
open AModel AModelFac Matrix Finset

/-- Every family edge in `E0` is `EdgeOK` at large prime powers (`good_edges`). -/
theorem edges_good :
    ∃ q₀ : ℕ, ∀ q, q.Prime → q₀ < q → ∀ f : ℕ, ∀ e ∈ E0, EdgeOK (q ^ f) e :=
  good_edges E0 E0_Q

/-- **EdgesOK half of `net0_ok`** on `net0Pnd`. -/
theorem EdgesOK_large :
    ∃ q₀ : ℕ, ∀ q, q.Prime → q₀ < q → ∀ f, EdgesOK (m := 529) net0Pnd (q ^ f) := by
  obtain ⟨q₀, h⟩ := edges_good
  exact ⟨q₀, fun q hq hlt f => EdgesOK_of_good_primes q₀ h hq hlt f⟩

/-- RunsOK ∧ EdgesOK packaging (FormalOK still open). -/
theorem net0_runs_edges :
    ∃ q₀ : ℕ,
      RunsOK (m := 529) net0Pnd ∧
        (∀ q, q.Prime → q₀ < q → ∀ f, EdgesOK (m := 529) net0Pnd (q ^ f)) := by
  obtain ⟨q₀, hE⟩ := EdgesOK_large
  exact ⟨q₀, net0Pnd_RunsOK, hE⟩

/-! ## Mom packaging on net0Pnd -/

def MomEqStmtPnd : Prop :=
  ∀ τ : ℝ, histMoment net0Pnd.hist 529 τ = histMoment bitR8 529 τ

theorem momEqPnd_of_hist_eq
    (h : ∀ τ : ℝ, histMoment net0Pnd.hist 529 τ = histMoment oppbankHist 529 τ) :
    MomEqStmtPnd := fun τ => (h τ).trans (histMoment_oppbank_bitR8_529 τ)

theorem hist_mom_net0Pnd' (τ : ℝ) :
    histMoment net0Pnd.hist 529 τ = (net0Pnd.edges.map (EM τ)).sum :=
  hist_mom_net0Pnd τ

/-- Finite Bruhat-factor pack for `good_mats` (same shape as GoodPrimes `EM0`). -/
noncomputable def EM0 : Finset (QMat2 529) :=
  E0.image Edge.E₁ ∪ E0.image Edge.E₂

theorem EM0_good :
    ∃ q₀ : ℕ, ∀ q, q.Prime → q₀ < q → ∀ f : ℕ, ∀ A ∈ EM0, ∀ i j,
      Nat.Coprime (A i j).den (q ^ f) ∧ (A i j ≠ 0 → IsUnit (redQ (q ^ f) (A i j))) :=
  good_mats EM0

end IntMul.Kappa.R8.Bit.Oppbank.FormalOK2


