-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_HeightSurvey_ImaginaryRootConj
-- name    : Development_AbelianVarietyTheory_Counterexamples_HeightSurvey_ImaginaryRootConj
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T00:12:35.553268+00:00
-- url     : https://prove2.me/theorems/d3dc76ed-1de8-4144-a962-c4a28b1af120
-- title:
--   Imaginary Root Conj
-- statement:
--   Definitions and structural lemmas for Imaginary Root Conj, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/HeightSurvey/ImaginaryRootConj.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_HostTraceIdentity
import Theorems.Thm_Formalism_L2_Pj_min_le_vV_add
import Theorems.Thm_Formalism_L2_Pj_vV_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.RowChartCounterexample
open Formalism.L2.FormalSeriesBounds Formalism.L2.Pj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {C : Type} [Field C]
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {l : Level H} {c : Coeff l} {T : CDVR} {io : c.F →+* T.Fr} {ι : T.Fr →+* C} {V : VF C}
variable {Orb : Type} {d : ℕ}
open Classical in

def selfVF (T : CDVR) (p : ℕ) (hp : p.Prime) (h : 0 < vV T.V ((p : ℕ) : T.Fr)) : VF T.Fr where
  v := AddValuation.of
    (fun x => if x = 0 then ⊤ else (((vV T.V x : ℝ) / (vV T.V ((p : ℕ) : T.Fr) : ℝ) : ℝ) : WithTop ℝ))
    (by simp) (by simp [vV])
    (fun x y => by
      by_cases hxy : x + y = 0
      · simp [hxy]
      by_cases hx : x = 0
      · simp [hx]
      by_cases hy : y = 0
      · simp [hy]
      simp only [hx, hy, hxy, if_false]
      have hp0 : (0 : ℝ) ≤ (vV T.V ((p : ℕ) : T.Fr) : ℝ) := by exact_mod_cast h.le
      rcases min_le_iff.1 (min_le_vV_add (V := T.V) hx hy hxy) with h' | h'
      · exact min_le_iff.2 (Or.inl (WithTop.coe_le_coe.2 (div_le_div_of_nonneg_right (by exact_mod_cast h') hp0)))
      · exact min_le_iff.2 (Or.inr (WithTop.coe_le_coe.2 (div_le_div_of_nonneg_right (by exact_mod_cast h') hp0))))
    (fun x y => by
      by_cases hx : x = 0
      · simp [hx]
      by_cases hy : y = 0
      · simp [hy]
      simp only [hx, hy, mul_ne_zero hx hy, if_false]
      rw [vV_mul hx hy, Int.cast_add, add_div, WithTop.coe_add])
  l := p
  l_prime := hp
  v_l := by
    have h1 : ((p : ℕ) : T.Fr) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
    have h2 : (vV T.V ((p : ℕ) : T.Fr) : ℝ) ≠ 0 := by exact_mod_cast h.ne'
    rw [AddValuation.of_apply, if_neg h1, div_self h2]
    rfl
def padicT (p : ℕ) [Fact p.Prime] : CDVR where
  V := ℤ_[p]
end GlobalTheory.RowChartCounterexample


