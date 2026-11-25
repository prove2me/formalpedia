-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetB
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetB
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T14:10:04.982455+00:00
-- url     : https://prove2.me/theorems/108fcde2-11e8-4817-9d3c-9ce1ef26ddd6
-- title:
--   Hol Jet B
-- statement:
--   Definitions and structural lemmas for Hol Jet B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/HolJetB.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_TaylorMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ValAtLem
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdJet_mk_trunc_coe
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdJet_psJet_mul
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdJet_psTrunc_eq
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_ValAt_valAt__res_9bf5469fe96a
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_ValAt_valAt__sub_69b16cdcbcca
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_TM_taylor_multiplication
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_ValAt_analyticAt_val

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
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
open AlgebraicGeometry CategoryTheory Opposite Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt
open scoped ContDiff
section JetOf
variable {g : ℕ}
def jetOf (m : ℕ) (θ : (Fin g → ℂ) → ℂ) : Jet ℂ (Fin 1 × Fin g) m := psJet m (tay θ 0)
theorem psJet_add' {ι : Type} [Fintype ι] [DecidableEq ι] (m : ℕ) (f h : MvPowerSeries ι ℂ) :
    psJet m (f + h) = psJet m f + psJet m h := by
  simp only [psJet, psTrunc, map_add, Finset.sum_add_distrib]
theorem jetOf_mul (m : ℕ) {f h : (Fin g → ℂ) → ℂ} (hf : ContDiffAt ℂ ω f 0) (hh : ContDiffAt ℂ ω h 0) :
    jetOf m (f * h) = jetOf m f * jetOf m h := by
  rw [jetOf, (TM.taylor_multiplication.1 g f h hf hh).1, Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet.psJet_mul]
  rfl
theorem jetOf_add (m : ℕ) {f h : (Fin g → ℂ) → ℂ} (hf : ContDiffAt ℂ ω f 0) (hh : ContDiffAt ℂ ω h 0) :
    jetOf m (f + h) = jetOf m f + jetOf m h := by
  rw [jetOf, (TM.taylor_multiplication.1 g f h hf hh).2, psJet_add']
  rfl
theorem jetOf_const (m : ℕ) (c : ℂ) :
    jetOf m (fun _ : Fin g → ℂ => c) = algebraMap ℂ (Jet ℂ (Fin 1 × Fin g) m) c := by
  rw [jetOf, TM.taylor_multiplication.2.1 g c]
  have h : (MvPowerSeries.C c : MvPowerSeries (Fin 1 × Fin g) ℂ) =
      ((MvPolynomial.C c : MvPolynomial (Fin 1 × Fin g) ℂ) : MvPowerSeries (Fin 1 × Fin g) ℂ) := by simp
  rw [h, psJet, Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet.psTrunc_eq, Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet.mk_trunc_coe, ← MvPolynomial.algebraMap_eq]
  rfl
theorem jetOf_congr (m : ℕ) {f h : (Fin g → ℂ) → ℂ} (hfh : f =ᶠ[nhds 0] h) : jetOf m f = jetOf m h := by
  rw [jetOf, jetOf, TM.taylor_multiplication.2.2 g f h hfh]
end JetOf
section HolJet
variable {g : ℕ} {Y : Scheme.{0}}
abbrev cpt : Sp ℂ := IsLocalRing.closedPoint (CommRingCat.of ℂ)
def IsHolFam (e : (Fin g → ℂ) → (Sp ℂ ⟶ Y)) : Prop :=
  ∀ (U : Y.Opens) (f : Γ(Y, U)), IsOpen {z | ⊤ ≤ e z ⁻¹ᵁ U} ∧
    DifferentiableOn ℂ (fun z => valAt' (e z) U f) {z | ⊤ ≤ e z ⁻¹ᵁ U}
variable (e : (Fin g → ℂ) → (Sp ℂ ⟶ Y)) (hol : IsHolFam e)
set_option backward.isDefEq.respectTransparency false in
theorem top_le_of_mem {x : Sp ℂ ⟶ Y} {U : Y.Opens} (h : x cpt ∈ U) : ⊤ ≤ x ⁻¹ᵁ U :=
  (Scheme.preimage_eq_top_of_closedPoint_mem x h).ge
include hol in
theorem eventually_mem {U : Y.Opens} (hU : e 0 cpt ∈ U) : ∀ᶠ z in nhds 0, ⊤ ≤ e z ⁻¹ᵁ U :=
  (hol U 0).1.mem_nhds (top_le_of_mem hU)
include hol in
theorem contDiffAt_val {U : Y.Opens} (hU : e 0 cpt ∈ U) (f : Γ(Y, U)) :
    ContDiffAt ℂ ω (fun z => valAt' (e z) U f) 0 :=
  (analyticAt_val e hol U f 0 (top_le_of_mem hU)).contDiffAt
def jetRingHom (m : ℕ) (U : Y.Opens) (hU : e 0 cpt ∈ U) : Γ(Y, U) →+* Jet ℂ (Fin 1 × Fin g) m where
  toFun f := jetOf m (fun z => valAt' (e z) U f)
  map_one' := by
    rw [← map_one (algebraMap ℂ (Jet ℂ (Fin 1 × Fin g) m)), ← jetOf_const]
    refine jetOf_congr m ((eventually_mem e hol hU).mono fun z hz => ?_)
    exact valAt'_one _ _ hz
  map_mul' f h := by
    rw [← jetOf_mul m (contDiffAt_val e hol hU f) (contDiffAt_val e hol hU h)]
    congr 1
    funext z
    exact valAt'_mul _ _ f h
  map_zero' := by
    rw [← map_zero (algebraMap ℂ (Jet ℂ (Fin 1 × Fin g) m)), ← jetOf_const]
    congr 1
    funext z
    have := valAt'_sub (e z) U 0 0
    rw [sub_self, sub_self] at this
    exact this
  map_add' f h := by
    rw [← jetOf_add m (contDiffAt_val e hol hU f) (contDiffAt_val e hol hU h)]
    congr 1
    funext z
    exact valAt'_add _ _ f h
def jetψ (m : ℕ) (U : Y.Opens) (hU : e 0 cpt ∈ U) :
    Γ(Y, U) ⟶ CommRingCat.of (Jet ℂ (Fin 1 × Fin g) m) :=
  CommRingCat.ofHom (jetRingHom e hol m U hU)
theorem jetψ_apply (m : ℕ) (U : Y.Opens) (hU : e 0 cpt ∈ U) (f : Γ(Y, U)) :
    jetψ e hol m U hU f = jetOf m (fun z => valAt' (e z) U f) := rfl
theorem jetψ_res (m : ℕ) (U V : Y.Opens) (hU : e 0 cpt ∈ U) (hV : e 0 cpt ∈ V) (h : V ≤ U) :
    Y.presheaf.map (homOfLE h).op ≫ jetψ e hol m V hV = jetψ e hol m U hU := by
  ext f
  rw [CommRingCat.comp_apply, jetψ_apply, jetψ_apply]
  refine jetOf_congr m ((eventually_mem e hol hV).mono fun z hz => ?_)
  exact valAt'_res _ h hz f
def jetPt (m : ℕ) : Sp (Jet ℂ (Fin 1 × Fin g) m) ⟶ Y :=
  nbhdPt (y₀ := e 0 cpt) (jetψ e hol m) (jetψ_res e hol m)
end HolJet
end ReciprocityTheory.ChartRestriction.G.PullbackSections


