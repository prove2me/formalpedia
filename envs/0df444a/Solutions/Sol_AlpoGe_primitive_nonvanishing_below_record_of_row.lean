-- Prove2me | solution 1 for AlpoGe.primitive_nonvanishing_below_record_of_row
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @RSoulat
-- created : 2026-11-22T17:27:43.653072+00:00
-- url     : https://prove2.me/submissions/73302fd7-3cea-4054-9b58-b34ca6a1838c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AlpoGeB008
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Theorems.Thm_AlpoGe_cyclic_character_logDeriv_locally_bounded_below_record_of_row

open Filter Set
open scoped Topology
set_option autoImplicit false

theorem solution
    (H : UpperTheory.GalStar.Row0b fun h rc => UpperTheory.Zero.LLC.IsRecT h rc) :
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
      ∀ s : ℂ, 1 / 2 < s.re → s.re ≤ (0.8749570698 : ℝ) →
        DirichletCharacter.LFunction χ s ≠ 0 := by
  classical
  intro N _ χ hχ s hs hcap
  let X : Finset (DirichletCharacter ℂ N) :=
    Finset.univ.filter (· ∈ Subgroup.zpowers χ)
  let F (z : ℂ) := ∏ η ∈ X, DirichletCharacter.LFunction η z
  have hχX : χ ∈ X := Finset.mem_filter.mpr ⟨Finset.mem_univ _, Subgroup.mem_zpowers χ⟩
  have hLt : s.re < 1 := hcap.trans_lt (by norm_num)
  have hs1 : s ≠ 1 := by
    rintro rfl
    simp at hLt
  have hFactors (η : DirichletCharacter ℂ N) :
      AnalyticOnNhd ℂ (DirichletCharacter.LFunction η) ({1}ᶜ : Set ℂ) :=
    DifferentiableOn.analyticOnNhd
      (fun z hz => (η.differentiableAt_LFunction z (.inl hz)).differentiableWithinAt)
      isOpen_compl_singleton
  have hProduct (A : Finset (DirichletCharacter ℂ N)) (z : ℂ)
      (hz : z ∈ ({1}ᶜ : Set ℂ)) :
      AnalyticAt ℂ (fun w => ∏ η ∈ A, DirichletCharacter.LFunction η w) z := by
    induction A using Finset.induction_on with
    | empty => simpa only [Finset.prod_empty] using (analyticAt_const :
        AnalyticAt ℂ (fun _ : ℂ => (1 : ℂ)) z)
    | @insert η A hη ih =>
      simpa only [Finset.prod_insert hη, Pi.mul_def] using (hFactors η z hz).mul ih
  have hAnalytic : AnalyticOnNhd ℂ F ({1}ᶜ : Set ℂ) := hProduct X
  have h2 : F 2 ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun η _ =>
      η.LFunction_ne_zero_of_one_le_re (.inr (by norm_num)) (by norm_num)
  have hConnected : IsConnected ({1}ᶜ : Set ℂ) :=
    isConnected_compl_singleton_of_one_lt_rank (by simp) 1
  have h2mem : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) := by norm_num
  have hAt2 : analyticOrderAt F 2 = 0 :=
    (hAnalytic 2 h2mem).analyticOrderAt_eq_zero.mpr h2
  have hFinite : analyticOrderAt F s ≠ ⊤ :=
    hAnalytic.analyticOrderAt_ne_top_of_isPreconnected hConnected.isPreconnected h2mem hs1
      (by rw [hAt2]; exact ENat.zero_ne_top)
  have hAtS : AnalyticAt ℂ F s := hAnalytic s hs1
  intro hZero
  have hFZero : F s = 0 :=
    Finset.prod_eq_zero hχX hZero
  have hOrder : meromorphicOrderAt F s ≠ 0 :=
    fun h => hAtS.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mp h hFZero
  have hOrderFinite : meromorphicOrderAt F s ≠ ⊤ := by
    rw [hAtS.meromorphicOrderAt_eq]
    simpa using hFinite
  have hPole : meromorphicOrderAt (logDeriv F) s = -1 :=
    meromorphicOrderAt_logDeriv_eq_neg_one hAtS.meromorphicAt hOrder hOrderFinite
  have hDivergence : Tendsto (fun z => ‖logDeriv F z‖) (𝓝[≠] s) atTop :=
    tendsto_norm_atTop_iff_cobounded.mpr <|
      tendsto_cobounded_of_meromorphicOrderAt_neg (by
        rw [hPole]
        exact WithTop.coe_lt_coe.mpr (by decide : (-1 : ℤ) < 0))
  obtain ⟨C, hBound⟩ :=
    AlpoGe.cyclic_character_logDeriv_locally_bounded_below_record_of_row H N χ hχ s hs hcap
  have hFalse : ∀ᶠ z in 𝓝[≠] s, False := by
    filter_upwards [hDivergence.eventually_gt_atTop C, hBound] with z hLarge hSmall
    exact (not_lt_of_ge hSmall) hLarge
  obtain ⟨_, contradiction⟩ := hFalse.exists
  exact contradiction
