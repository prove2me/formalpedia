-- Prove2me | Definitions.Def_Formalism_LocalRingCardinality_DataJet
-- name    : Formalism_LocalRingCardinality_DataJet
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T18:12:25.111668+00:00
-- url     : https://prove2.me/theorems/b112f65a-c632-48b8-98dc-9411f6d62680
-- title:
--   Data Jet
-- statement:
--   Definitions and structural lemmas for Data Jet, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/DataJet.lean

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_Params
import Definitions.Def_Formalism_LocalRingCardinality_DataHost
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
namespace Formalism.BasicNotions
def JetTdeg {σ : Type*} (m : σ →₀ ℕ) : ℕ := m.sum (fun _ k => k)
def jetLogG (l d : ℕ) [Fact l.Prime] {β : Type*} (v : ZMod d × β) : MvPowerSeries (ZMod d × β) ℂ_[l] :=
  fun m => ∑ e ∈ Finset.range (JetTdeg m + 1),
    if m = Finsupp.single (v.1 - 2 * (e : ZMod d), v.2) ((l ^ 2) ^ e) then (((l : ℂ_[l]) ^ e)⁻¹) else 0
structure JetLoc where

  l : ℕ
  [hl : Fact l.Prime]

  five_le_l : 5 ≤ l

  d : ℕ
  [hd : NeZero d]
  d_even : Even d
  two_le_d : 2 ≤ d

  N0 : ℕ
  N1 : ℕ

  Th : MvPowerSeries (ZMod d × Fin N0 × Fin N1) ℂ_[l]
attribute [instance] JetLoc.hl JetLoc.hd
structure JetLoc1 where
  l : ℕ
  [hl : Fact l.Prime]

  five_le_l : 5 ≤ l
  N0 : ℕ
  N1 : ℕ

  Th : MvPowerSeries (ZMod 1 × Fin N0 × Fin N1) ℂ_[l]
attribute [instance] JetLoc1.hl
structure ThetaJet (R : Ranks) (host : Host R) : Type 1 where
  Sit : Type
  loc : Sit → JetLoc

  l_inert : ∀ i, host.cls (loc i).l = .signal ∨ host.cls (loc i).l = .inertClass
  jOf : Sit → ℕ
  j_mem : ∀ i, 1 ≤ jOf i ∧ jOf i ≤ R.m
  N0_eq : ∀ i, (loc i).N0 = R.N (jOf i - 1)
  N1_eq_exponentN1 : ∀ i, (loc i).N1 = R.N (jOf i)
  Sit1 : Type
  loc1 : Sit1 → JetLoc1
  l_inert1 : ∀ i, host.cls (loc1 i).l = .inertClass ∧ ¬ HNeZero host (loc1 i).l
  j1Of : Sit1 → ℕ
  firstJetIndex_mem_range : ∀ i, 1 ≤ j1Of i ∧ j1Of i ≤ R.m
  firstJet_lowerRank_eq : ∀ i, (loc1 i).N0 = R.N (j1Of i - 1)
  firstJet_upperRank_eq : ∀ i, (loc1 i).N1 = R.N (j1Of i)
end Formalism.BasicNotions
end


