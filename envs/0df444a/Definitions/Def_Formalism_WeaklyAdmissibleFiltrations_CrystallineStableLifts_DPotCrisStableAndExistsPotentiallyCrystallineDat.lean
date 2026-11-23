-- Prove2me | Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CrystallineStableLifts_DPotCrisStableAndExistsPotentiallyCrystallineDat
-- name    : Formalism_WeaklyAdmissibleFiltrations_CrystallineStableLifts_DPotCrisStableAndExistsPotentiallyCrystallineDat
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:27:38.981375+00:00
-- url     : https://prove2.me/theorems/6d4bf2ad-dfdd-44ca-987f-bed1e34bf06a
-- title:
--   DPot Cris Stable And Exists Potentially Crystalline Dat
-- statement:
--   Definitions and structural lemmas for DPot Cris Stable And Exists Potentially Crystalline Dat, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WeaklyAdmissibleFiltrations/CrystallineStableLifts/DPotCrisStableAndExistsPotentiallyCrystallineDat.lean

import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_DpcrisStable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.WeaklyAdmissibleFiltrations
open Module TensorProduct
section Top
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
def PeriodData.pcResTop (PD : PeriodData G Qp K₀ K B BdR) :
    PeriodData (⊤ : Subgroup G) Qp K₀ K B BdR where
  p := PD.p
  hp := PD.hp
  finK₀ := PD.finK₀
  finK := PD.finK
  σ := PD.σ
  σ_bij := PD.σ_bij
  actB := PD.actB.comp (⊤ : Subgroup G).subtype
  invB b hb := PD.invB b (fun g => hb ⟨g, Subgroup.mem_top g⟩)
  φ := PD.φ
  φ_inj := PD.φ_inj
  φ_K₀ := PD.φ_K₀
  φ_comm g b := PD.φ_comm g b
  actdR := PD.actdR.comp (⊤ : Subgroup G).subtype
  invdR b hb := PD.invdR b (fun g => hb ⟨g, Subgroup.mem_top g⟩)
  ι := PD.ι
  ι_inj := PD.ι_inj
  ι_comm g b := PD.ι_comm g b
  Fil := PD.Fil
  Fil_anti := PD.Fil_anti
  one_mem := PD.one_mem
  Fil_mul := PD.Fil_mul
  Fil_exh := PD.Fil_exh
  Fil_sep := PD.Fil_sep
  Fil_G g := PD.Fil_G g
  χ := PD.χ.comp (⊤ : Subgroup G).subtype
  t := PD.t
  t_unit := PD.t_unit
  t_act g := PD.t_act g
  t_φ := PD.t_φ
  mem_filtration_one := PD.mem_filtration_one
  not_mem_filtration_two := PD.not_mem_filtration_two
  fund := PD.fund
def PotCrysData.pcOfTop (PD : PeriodData G Qp K₀ K B BdR) : PotCrysData G Qp K₀ K K₀ K B BdR where
  H := ⊤
  normal := inferInstance
  finiteIndex := inferInstance
  PD := PD
  PD' := PD.pcResTop
  actB_eq _ _ := rfl
  actdR_eq _ _ := rfl
  φ_eq _ := rfl
  ι_eq _ := rfl
  Fil_eq _ := rfl
  p_eq := rfl
  t_eq := rfl
  χ_eq _ := rfl
  stableK₀' g c := ⟨c, AlgEquiv.commutes (PD.actB g) c⟩
end Top
section Stable
variable {G : Type} [Group G] {Qp K₀ K K₀' K' : Type} [Field Qp] [Field K₀] [Field K]
    [Field K₀'] [Field K']
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    [Algebra Qp K₀'] [Algebra Qp K'] [Algebra K₀' K'] [IsScalarTower Qp K₀' K']
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra K₀' B] [IsScalarTower Qp K₀' B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    [Algebra K₀' BdR] [Algebra K' BdR] [IsScalarTower Qp K' BdR]
    [IsScalarTower K₀' K' BdR] [IsScalarTower Qp K₀' BdR]
    (PC : PotCrysData G Qp K₀ K K₀' K' B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)
end Stable
end Formalism.WeaklyAdmissibleFiltrations


