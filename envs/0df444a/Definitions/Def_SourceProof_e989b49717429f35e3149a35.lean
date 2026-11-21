-- Prove2me | Definitions.Def_SourceProof_e989b49717429f35e3149a35
-- name    : SourceProof_e989b49717429f35e3149a35
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T22:37:28.255857+00:00
-- url     : https://prove2.me/theorems/3eb6c161-1450-4ceb-a824-d7ca46bddded
-- title:
--   LevyStochCalc source module: SourceProof_e989b49717429f35e3149a35
-- statement:
--   The original source theorem `LevyStochCalc.Driver.pairing_char_joint_eq_zero` comes from the `LevyStochCalc.Driver.JointComplement` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_JointComplement_F000
import Definitions.Def_SourceProof_7ea79b056610f3e15dd559e8
import Definitions.Def_SourceProof_adfa01854b07ed0ea603550e
import Definitions.Def_SourceProof_cc04f7a83f7e31f30eccd6e0

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The orthogonal complement of the joint ranges

The times of a finite family of Brownian coordinate values, together with the horizon, sort into
an increasing grid whose last point is the horizon, and a finite family of window sets sits
inside a single window of finite mark intensity. A product of a Brownian cylinder character and a
window character is therefore a value character along the grid, and the joint grid induction
applies. The clamping horizon of that induction is strictly beyond the last grid point, so the
orthogonality hypothesis is carried up by the marked perp bridge.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace LevyStochCalc.Driver

open LevyStochCalc.Poisson LevyStochCalc.Poisson.Compensated
open LevyStochCalc.Brownian LevyStochCalc.Brownian.Ito LevyStochCalc.Brownian.Multidim

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ} {ν : Measure E} [SigmaFinite ν] {T : ℝ}

section MarkSet

end MarkSet

section Complement

variable (W : MultidimBrownianMotion P d) (N : PoissonRandomMeasure P ν)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)


theorem _root_.Prove2MeSourceProof.h_e989b49717429f35e3149a35 [Nonempty E] (hd : 0 < d)
    (hℱi : ∀ i, IsBrownianFiltration (W.W i) ℱ)
    (hℱB : ∀ {c : Fin d → ℝ} (hc : ∑ i, c i ^ 2 = 1),
      IsBrownianFiltration (MultidimBrownianMotion.combineBM W hc) ℱ)
    (hℱN : IsPoissonFiltration N ℱ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    (hT : 0 < T) {Z : Ω → ℝ} (hZ2 : MemLp Z 2 P) (hZm : AEStronglyMeasurable[ℱ T] Z P)
    (hperp : ∀ i, PerpItoIntegrals (W.W i) ℱ (hℱi i) fun ω => (Z ω : ℂ))
    (hZcomp : ∀ G' : MarkedHorizonIntegrand P ν ℱ T, ∫ ω, Z ω * G'.integral N hℱN ω ∂P = 0)
    (hZ0 : ∫ ω, Z ω ∂P = 0) (F : Finset (Fin d × Set.Iic T))
    (G : Finset (Poisson.WindowSet E ν T)) (w : F → ℝ) (v : G → ℝ) :
    ∫ ω, Complex.exp (((∑ p : F, (W.W p.1.1).W (p.1.2 : ℝ) ω * w p : ℝ) : ℂ) * Complex.I)
      * Complex.exp (((∑ B : G,
          (N.N ω ((B : Poisson.WindowSet E ν T) : Set (ℝ × E))).toReal * v B : ℝ) : ℂ)
        * Complex.I) * ((Z ω : ℝ) : ℂ) ∂P = 0 := by
  classical
  obtain ⟨n₀, hn₀⟩ : ∃ n : ℕ, (Classical.arbitrary E) ∈ spanningSets ν n := by
    have : (Classical.arbitrary E) ∈ ⋃ n, spanningSets ν n := by
      rw [iUnion_spanningSets ν]; trivial
    exact Set.mem_iUnion.mp this
  set S : Finset ℝ := insert T (LevyStochCalc.Analysis.posTimes F) with hSdef
  set τ : ℕ → ℝ := LevyStochCalc.Analysis.sortedGrid S with hτdef
  have hSpos : ∀ x ∈ S, 0 < x := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hT
    · exact LevyStochCalc.Analysis.pos_of_mem_posTimes hx
  have hSle : ∀ x ∈ S, x ≤ T := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact le_rfl
    · exact LevyStochCalc.Analysis.le_of_mem_posTimes hx
  have hlt : ∀ k, k < S.card → τ k < τ (k + 1) := fun k hk =>
    LevyStochCalc.Analysis.sortedGrid_lt_succ S hSpos hk
  have hTle : T ≤ τ S.card := _root_.Prove2MeSourceProof.h_7ea79b056610f3e15dd559e8 (Finset.mem_insert_self T _)
  have hleT : τ S.card ≤ T :=
    hSle _ (LevyStochCalc.Analysis.sortedGrid_card_mem ⟨T, Finset.mem_insert_self T _⟩)
  have hTn : τ S.card < T + 1 := lt_of_le_of_lt hleT (by linarith)
  have hR : (0 : ℝ) < T + 1 := by linarith
  have hTR : T ≤ T + 1 := by linarith
  have hBm : ∀ B : G, MeasurableSet ((B : LevyStochCalc.Poisson.WindowSet E ν T) : Set (ℝ × E)) :=
    fun B => (B : LevyStochCalc.Poisson.WindowSet E ν T).measurableSet
  have hBsub : ∀ B : G, ((B : LevyStochCalc.Poisson.WindowSet E ν T) : Set (ℝ × E))
      ⊆ Set.Ioc (0 : ℝ) (T + 1) ×ˢ LevyStochCalc.Driver.markUnion G n₀ := by
    intro B
    refine (LevyStochCalc.Driver.subset_markSet (B : LevyStochCalc.Poisson.WindowSet E ν T)).trans ?_
    exact Set.prod_mono (Set.Ioc_subset_Ioc le_rfl hTR)
      (LevyStochCalc.Driver.markSet_subset_markUnion B.2 n₀)
  have hZcompR : ∀ G' : LevyStochCalc.Poisson.Compensated.MarkedHorizonIntegrand P ν ℱ (T + 1),
      ∫ ω, Z ω * G'.integral N hℱN ω ∂P = 0 := fun G' =>
    _root_.Prove2MeSourceProof.h_cc04f7a83f7e31f30eccd6e0 N hℱN hT hZ2 hZm hZcomp hTR G'
  have hkey := _root_.Prove2MeSourceProof.h_adfa01854b07ed0ea603550e W N ℱ hd hℱi hℱB hℱN hℱ0 hnull
    (τ := τ) (LevyStochCalc.Analysis.sortedGrid_zero S) hR (LevyStochCalc.Driver.measurableSet_markUnion G n₀)
    (LevyStochCalc.Driver.markUnion_ne_top G n₀) v hBm hBsub (LevyStochCalc.Driver.mem_markUnion G hn₀) hZ2 hperp hZcompR hZ0
    (fun k i => LevyStochCalc.Analysis.weightAt F w (τ k) i) S.card hlt hTn
  refine Eq.trans (integral_congr_ae ?_) hkey
  filter_upwards [LevyStochCalc.Brownian.Ito.ae_forall_eq_zero_of_nonpos W F] with ω hω
  have hBrown : (∑ p : F, (W.W p.1.1).W (p.1.2 : ℝ) ω * w p)
      = ∑ i, ∑ k ∈ Finset.Ico 1 (S.card + 1),
          LevyStochCalc.Analysis.weightAt F w (τ k) i * (W.W i).W (τ k) ω :=
    _root_.Prove2MeSourceProof.h_527e9e3b2fcbd8b1a9548140 F w (fun i t => (W.W i).W t ω)
      (fun p hp => hω p.1 p.2 hp) (Finset.subset_insert _ _) hSpos
  have hwin : (∑ B : G,
        (N.N ω ((B : LevyStochCalc.Poisson.WindowSet E ν T) : Set (ℝ × E))).toReal * v B)
      = ∑ B : G, v B * (N.N ω (((B : LevyStochCalc.Poisson.WindowSet E ν T) : Set (ℝ × E))
          ∩ Set.Ioc (0 : ℝ) (τ S.card) ×ˢ Set.univ)).toReal := by
    refine Finset.sum_congr rfl fun B _ => ?_
    have hsub : ((B : LevyStochCalc.Poisson.WindowSet E ν T) : Set (ℝ × E))
        ⊆ Set.Ioc (0 : ℝ) (τ S.card) ×ˢ Set.univ := by
      refine (LevyStochCalc.Driver.subset_markSet (B : LevyStochCalc.Poisson.WindowSet E ν T)).trans ?_
      exact Set.prod_mono (Set.Ioc_subset_Ioc le_rfl hTle) (Set.subset_univ _)
    rw [Set.inter_eq_self_of_subset_left hsub, mul_comm]
  have hE : ∀ x : ℝ, Complex.exp ((x : ℂ) * Complex.I)
      = Complex.exp (Complex.I * (x : ℂ)) := fun x => by rw [mul_comm]
  rw [hE, hE, hBrown, hwin, LevyStochCalc.Poisson.charAt]
  ring
end Complement

end LevyStochCalc.Driver


