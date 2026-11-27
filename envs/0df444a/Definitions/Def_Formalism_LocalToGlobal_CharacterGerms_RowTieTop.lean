-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieTop
-- name    : Formalism_LocalToGlobal_CharacterGerms_RowTieTop
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-27T04:39:37.167106+00:00
-- url     : https://prove2.me/theorems/003cfafa-37d2-51a8-bd85-ca3c45f40966
-- title:
--   Row Tie Top
-- statement:
--   Definitions and structural lemmas for Row Tie Top, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieTop.lean

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_HostTraceIdentity
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_PlugUP
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_FBChart_hyps
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_zero_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_zero_alt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_zero_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_zero_alt


set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
namespace Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds Formalism.L2.Pj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
theorem card_sigma_fst {d : ℕ} [NeZero d] (m : ZMod d → ℕ) (a : ZMod d) :
    (Finset.univ.filter fun x : (Σ a : ZMod d, Fin (m a)) => x.1 = a).card = m a := by
  rw [show (Finset.univ.filter fun x : (Σ a : ZMod d, Fin (m a)) => x.1 = a) =
      (Finset.univ : Finset (Fin (m a))).map ⟨Sigma.mk a, sigma_mk_injective⟩ from ?_]
  · simp
  · ext x
    obtain ⟨b, i⟩ := x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Function.Embedding.coeFn_mk]
    constructor
    · rintro rfl
      exact ⟨i, rfl⟩
    · rintro ⟨j, hj⟩
      exact (congrArg Sigma.fst hj).symm
section CH
open ReciprocityTheory.PGsh.Up CharacteristicFromRanks ValuationFitting
variable {C : Type} [Field C]
end CH
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {C : Type} [Field C] [CharZero C] {V : VF C}
section Rank
variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} {Orb : Type} {d : ℕ} [NeZero d]
theorem rankHyp_ofLab {C3 : IntChart T io y} {ι : T.Fr →+* C} {Y : FBChart C V (𝓞 E) (chD C3.ch)} {lab : Lab E Orb d}
    (ha : LabArith V io ι lab) (hg : LabGeo C3 ι Y lab) (hr : lab.RankOK Dw) (o : Orb) :
    (Y.raw (pairOfLab ha hg o)).RankHyp where
  big_compl := (hr o).1
  rk_big := fun g a hb => (card_sigma_fst (fun a => Dw.mult (lab.tau o g a)) a).trans ((hr o).2.1 g a hb)
  rk_small := fun g a hb => (card_sigma_fst (fun a => Dw.mult (lab.tau o g a)) a).trans ((hr o).2.2 g a hb)
end Rank
section Named
variable (Xo c)
def AllCharts (Φ : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) (I : Fin 2 → Type) [∀ g, Fintype (I g)] (dd : ℕ),
    RawChart C d I (Fin dd) → Prop) : Prop :=
  (∀ a : 𝓞 E, star a = H.bar a) →
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y)
    (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι →
    ∀ (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ι k Y →
    ∀ (Orb : Type) (d : ℕ) [NeZero d] (lab : Lab E Orb d) (ha : LabArith V io ι lab) (hg : LabGeo C3 ι Y lab),
    lab.RankOK Dw → ∀ o, Φ C V d (lab.II Dw o) (chD C3.ch) (Y.raw (pairOfLab ha hg o))
def RankMaximalCharts : Prop := AllCharts Xo c fun _ _ V _ _ _ _ X => ∀ Hc : ∀ g, X.CartHyp V g, RawChart.RankMaximalCondition Hc
def CharacterHypothesisAllCharts : Prop := AllCharts Xo c fun _ _ V _ _ _ _ X => ∀ Hc : ∀ g, X.CartHyp V g, RawChart.CHSt Hc
end Named
section Top
variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} {Orb : Type} {d : ℕ} [NeZero d]
theorem hypotheses_of_labelling (hCart : CartFBSt) (hAx : AxesFBSt) (hG0 : IntegralGermIndependentAllCharts) (hC : CEqFBSt) (hR1 : IndependenceBoundAllCharts)
    (hR2 : RankMaximalCharts Xo c) (hCH : CharacterHypothesisAllCharts Xo c) (hstar : ∀ a : 𝓞 E, star a = H.bar a)
    {C3 : IntChart T io y} {ι : T.Fr →+* C} (hι : EmbOK T V ι) {k : ℕ}
    {Y : FBChart C V (𝓞 E) (chD C3.ch)} (hY : IsBC C3 ι k Y) {lab : Lab E Orb d}
    (ha : LabArith V io ι lab) (hg : LabGeo C3 ι Y lab) (hr : lab.RankOK Dw) (o : Orb) :
    (Y.raw (pairOfLab ha hg o)).Hyps V :=
  FBChart.hyps hCart hAx hG0 hC hR1 Y (pairOfLab ha hg o) (rankHyp_ofLab ha hg hr o)
    (hR2 hstar _ _ _ C3 C V ι hι k Y hY Orb d lab ha hg hr o _)
    (hCH hstar _ _ _ C3 C V ι hι k Y hY Orb d lab ha hg hr o _)
def pairRowData (hCart : CartFBSt) (hAx : AxesFBSt) (hG0 : IntegralGermIndependentAllCharts) (hC : CEqFBSt) (hR1 : IndependenceBoundAllCharts)
    (hR2 : RankMaximalCharts Xo c) (hCH : CharacterHypothesisAllCharts Xo c) (hstar : ∀ a : 𝓞 E, star a = H.bar a)
    {C3 : IntChart T io y} {ι : T.Fr →+* C} (hι : EmbOK T V ι) {k : ℕ}
    {Y : FBChart C V (𝓞 E) (chD C3.ch)} (hY : IsBC C3 ι k Y) {lab : Lab E Orb d}
    (ha : LabArith V io ι lab) (hg : LabGeo C3 ι Y lab) (hr : lab.RankOK Dw) (o : Orb) :
    RowData C V d (lab.II Dw o) (JJ (lab.II Dw o)) :=
  (Y.raw (pairOfLab ha hg o)).rowData (hypotheses_of_labelling hCart hAx hG0 hC hR1 hR2 hCH hstar hι hY ha hg hr o)
end Top
end Formalism.L2.FormalSeriesBounds


