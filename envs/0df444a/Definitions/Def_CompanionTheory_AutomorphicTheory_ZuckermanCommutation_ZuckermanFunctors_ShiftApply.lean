-- Prove2me | Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_ShiftApply
-- name    : CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_ShiftApply
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T05:02:05.52707+00:00
-- url     : https://prove2.me/theorems/5e054b8f-c984-445a-b7b6-f22bcf2d9be1
-- title:
--   Shift Apply
-- statement:
--   Definitions and structural lemmas for Shift Apply, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ZuckermanCommutation/ZuckermanFunctors/ShiftApply.lean

import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_MultOne
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_SchurH
import Theorems.Thm_CompanionTheory_LimBd_SchurHpk_isURepOn_of_ds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped Kronecker
noncomputable section
namespace CompanionTheory.Zuck
open BranchingSupport Formalism.FourierDecayAlt.ThreeDimData
open PI.UpqRep (IsHCParam)
open PI.ZuckTensor (GapAtLeast)
structure Lib (t : ∀ n : ℕ, (Fin n → Bool) → ℝ) : Prop where
  zg : ZG t
  dec : ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (μ : Fin (2 * r + k + 1) → ℝ) (U : URep k r) (h : ℝ) (m : ℕ),
    U.R.IsDS ε μ → GapAtLeast ε μ h → t _ ε + m < h → Decay U m
  uniq : ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (μ : Fin (2 * r + k + 1) → ℝ) (R R' : Rep k r) (h : ℝ),
    R.IsDS ε μ → R'.IsDS ε μ → GapAtLeast ε μ h → t _ ε < h →
    ∃ e : R.H ≃ₗᵢ[ℂ] R'.H, ∀ g ∈ GG k r, ∀ x, e (R.σ g x) = R'.σ g (e x)
  exist : ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (μ μ' : Fin (2 * r + k + 1) → ℝ) (R : Rep k r) (h : ℝ),
    R.IsDS ε μ → IsHCParam μ' → GapAtLeast ε μ' h → t _ ε < h → ∃ R' : Rep k r, R'.IsDS ε μ'
structure Steps : Prop where
  infChar : PI.DSInfCharCap.DSInfCharCap
  decOfInj : DecOfInj
  decOfTrace : DecOfTrace
  homCat : HomCat
  okTriv : OKTriv
  okVr : OKVr
  okWedge : OKWedge
  okTens : OKTens
  matHom : MatHom
  uIso : UIso
  homLie : HomLie
  casSplit : CasSplit
  casDS : CasDS
  wedgeInt : WedgeInt
  wedgeQ : WedgeQ
  schur : Schur
  adj : Adj
  multOne : MultOne
  inj : InjStep
  occ : OccStep
  zuckH : ZuckH
  decTens : DecTens
  toRaw : ToRaw
  count : Count
section lin
variable {O : Type 1} {N : O → Type} [∀ o, AddCommGroup (N o)] [∀ o, Module ℂ (N o)]
  {Hom : ∀ a b, (N a →ₗ[ℂ] N b) → Prop}
end lin
section num
variable {n : ℕ}
end num
variable {t : ∀ n : ℕ, (Fin n → Bool) → ℝ} {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool}
def mkU {μ : Fin (2 * r + k + 1) → ℝ} (R : Rep k r) (h : R.IsDS ε μ) : URep k r :=
  ⟨R, CompanionTheory.LimBd.SchurHpk.isURepOn_of_ds h.2⟩
def ZuckSm (t : ∀ n : ℕ, (Fin n → Bool) → ℝ) : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r) (h : ℝ), 1 ≤ k →
    R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h →
    (∀ (l : ℕ) (RI : Sub (2 * r + k + 1) l → Rep k r), t _ ε + ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + 3 + l < h →
      (∀ a c, a < c → (l : ℝ) + 1 ≤ mu a - mu c) → (∀ I, (RI I).IsDS ε (addSet mu I.1)) →
      ∃ io pr, TensRaw (cmp l) R RI io pr) ∧
    ∀ RI : Fin (2 * r + k + 1) → Rep k r, t _ ε + ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + 3 < h →
      (∀ s, (RI s).IsDS ε (mu - Pi.single s 1)) → ∃ io pr, TensRaw dualM R RI io pr
end CompanionTheory.Zuck
end


