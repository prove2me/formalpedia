-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_UnitaryInverseIdentity
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_UnitaryInverseIdentity
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T01:10:18.537907+00:00
-- url     : https://prove2.me/theorems/2bee71a9-3adf-4a2d-bd8e-34b4b85c5d33
-- title:
--   Unitary Inverse Identity
-- statement:
--   Definitions and structural lemmas for Unitary Inverse Identity, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/UnitaryInverseIdentity.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_IsotropicVanish
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_SecondCoeffConsistency
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_ArithmeticFrobeniusAction
import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_HyperbolicPlaneSplit
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_FourFoldOrthogonalSum
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_FinsuppZmodOneEqSingle
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_BimultiplicativeDivisibleTorsion
import Definitions.Def_Formalism_GL3MeanSquares_FinalB
import Theorems.Thm_Formalism_L2_Th1_C_Pts_constantCoeff_subst_l
import Theorems.Thm_Formalism_L2_Th1_C_Pts_constantCoeff_subst_linv
import Theorems.Thm_Formalism_L2_Th1_C_Pts_isPt_fadd
import Theorems.Thm_Formalism_L2_Th1_C_Pts_isPt_fmul
import Theorems.Thm_Formalism_L2_Th1_C_Pts_subst_l_linv
import Theorems.Thm_Formalism_L2_Th1_C_Pts_subst_linv_l
import Theorems.Thm_Formalism_L2_Th1_C_lGBinom
import Theorems.Thm_Formalism_L2_Th1_C_mvExp_add
import Theorems.Thm_Formalism_L2_Th1_C_mvExp_zero
import Theorems.Thm_Formalism_LT_TorsProof_one_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Formalism.L2.Th1.C
namespace Calc
open Pts
section CongCalc
variable {K : Type} [Field K] [CharZero K] {R : Subring K} {σ : Type}
theorem lg_zero : LG R (0 : MvPowerSeries σ K) := by
  classical
  unfold LG
  refine ⟨map_zero _, ?_⟩
  rw [mvExp_zero]
  intro n
  rw [MvPowerSeries.coeff_one]
  split_ifs
  · exact R.one_mem
  · exact R.zero_mem
theorem lg_add {f g : MvPowerSeries σ K} (hf : LG R f) (hg : LG R g) : LG R (f + g) := by
  classical
  unfold LG at *
  refine ⟨by rw [map_add, hf.1, hg.1, add_zero], ?_⟩
  rw [mvExp_add hf.1 hg.1]
  intro n
  rw [MvPowerSeries.coeff_mul]
  exact sum_mem fun p _ => mul_mem (hf.2 p.1) (hg.2 p.2)
end CongCalc
end Calc
namespace Calc
open Pts Formalism.HermitianLattices.IntegralLatticeDensity
section Construct
def Ser {K : Type} [Field K] {O : Type} [CommRing O] (_τ : O →+* K) (σ : Type) : Type :=
  MvPowerSeries σ K
instance {K : Type} [Field K] {O : Type} [CommRing O] (τ : O →+* K) (σ : Type) :
    AddCommGroup (Ser τ σ) := inferInstanceAs (AddCommGroup (MvPowerSeries σ K))
instance {K : Type} [Field K] {O : Type} [CommRing O] (τ : O →+* K) (σ : Type) :
    Module O (Ser τ σ) := Module.compHom (MvPowerSeries σ K) τ
abbrev ofS {K : Type} [Field K] {O : Type} [CommRing O] {τ : O →+* K} {σ : Type} (g : Ser τ σ) :
    MvPowerSeries σ K := g
abbrev toS {K : Type} [Field K] {O : Type} [CommRing O] (τ : O →+* K) {σ : Type}
    (g : MvPowerSeries σ K) : Ser τ σ := g
def saRing (O : Type) [CommRing O] [StarRing O] : Subring O where
  carrier := {z | star z = z}
  mul_mem' := fun {a b} (ha : star a = a) (hb : star b = b) => by
    show star (a * b) = a * b
    rw [star_mul', ha, hb]
  one_mem' := star_one O
  add_mem' := fun {a b} (ha : star a = a) (hb : star b = b) => by
    show star (a + b) = a + b
    rw [star_add, ha, hb]
  zero_mem' := star_zero O
  neg_mem' := fun {a} (ha : star a = a) => by
    show star (-a) = -a
    rw [star_neg, ha]
def nm {O : Type} [CommRing O] [StarRing O] (α : O) : saRing O :=
  ⟨star α * α, by
    show star (star α * α) = star α * α
    rw [star_mul', star_star, mul_comm]⟩
def tr {O : Type} [CommRing O] [StarRing O] (α : O) : saRing O :=
  ⟨star α + α, by
    show star (star α + α) = star α + α
    rw [star_add, star_star, add_comm]⟩
variable {K : Type} [Field K] [CharZero K] {O : Type} [CommRing O] [StarRing O]
structure Data (R : Subring K) (l linv : PowerSeries K) (τ : O →+* K) : Prop where
  log : IsLogPair l linv
  fg : FGInt R l linv
  endo : ∀ α, EndInt R l linv (τ α)
  binom : ∀ z : O, star z = z → IsBinomScalar R (τ z)
variable {R : Subring K} {l linv : PowerSeries K} {τ : O →+* K}
theorem smul_ser (σ : Type) (α : O) (g : Ser τ σ) :
    ofS (α • g) = MvPowerSeries.C (τ α) * ofS g := by
  show τ α • ofS g = MvPowerSeries.C (τ α) * ofS g
  first
    | exact MvPowerSeries.smul_eq_C_mul _ _
    | (ext n; simp [MvPowerSeries.coeff_C_mul])
theorem linv_add (h : IsLogPair l linv) {σ : Type} {g g' : MvPowerSeries σ K}
    (hg : MvPowerSeries.constantCoeff g = 0) (hg' : MvPowerSeries.constantCoeff g' = 0) :
    PowerSeries.subst (g + g') linv =
      fadd l linv (PowerSeries.subst g linv) (PowerSeries.subst g' linv) := by
  unfold fadd
  rw [Pts.subst_l_linv h hg, Pts.subst_l_linv h hg']
theorem linv_C_mul (h : IsLogPair l linv) {σ : Type} (a : K) {g : MvPowerSeries σ K}
    (hg : MvPowerSeries.constantCoeff g = 0) :
    PowerSeries.subst (MvPowerSeries.C a * g) linv = fmul l linv a (PowerSeries.subst g linv) := by
  unfold fmul
  rw [Pts.subst_l_linv h hg]
def ptsSub (D : Data R l linv τ) (σ : Type) : Submodule O (Ser τ σ) where
  carrier := {g | MvPowerSeries.constantCoeff (ofS g) = 0 ∧
    IntMv R (PowerSeries.subst (ofS g) linv)}
  add_mem' := by
    rintro g g' ⟨hg, hi⟩ ⟨hg', hi'⟩
    refine ⟨(map_add _ _ _).trans (by rw [hg, hg', add_zero]), ?_⟩
    have := isPt_fadd D.log D.fg ⟨constantCoeff_subst_linv D.log hg, hi⟩
      ⟨constantCoeff_subst_linv D.log hg', hi'⟩
    rw [← linv_add D.log hg hg'] at this
    exact this.2
  zero_mem' := by
    refine ⟨map_zero _, ?_⟩
    have e : PowerSeries.subst (0 : MvPowerSeries σ K) linv = 0 :=
      PowerSeries.subst_zero_of_constantCoeff_zero D.log.2.2.1
    intro n
    show MvPowerSeries.coeff n (PowerSeries.subst (0 : MvPowerSeries σ K) linv) ∈ R
    rw [e, map_zero]
    exact R.zero_mem
  smul_mem' := by
    rintro α g ⟨hg, hi⟩
    show MvPowerSeries.constantCoeff (ofS (α • g)) = 0 ∧
      IntMv R (PowerSeries.subst (ofS (α • g)) linv)
    rw [smul_ser]
    refine ⟨by rw [map_mul, hg, mul_zero], ?_⟩
    rw [linv_C_mul D.log _ hg]
    exact (isPt_fmul D.log (D.endo α) ⟨constantCoeff_subst_linv D.log hg, hi⟩).2
def lgSub (D : Data R l linv τ) (σ : Type) : Submodule (saRing O) (Ser τ σ) where
  carrier := {f | LG R (ofS f)}
  add_mem' := fun hf hg => lg_add hf hg
  zero_mem' := lg_zero
  smul_mem' := fun z f hf => lGBinom K R σ (τ z) (D.binom z z.2) f hf
def pt (D : Data R l linv τ) {σ : Type} (g : ptsSub D σ) : MvPowerSeries σ K :=
  PowerSeries.subst (ofS g.1) linv
def toM (D : Data R l linv τ) {σ : Type} (x : MvPowerSeries σ K) (hx : IsPt R x) : ptsSub D σ :=
  ⟨toS τ (PowerSeries.subst x l), constantCoeff_subst_l D.log hx.1, by
    show IntMv R (PowerSeries.subst (PowerSeries.subst x l) linv)
    rw [subst_linv_l D.log hx.1]
    exact hx.2⟩
def cls (D : Data R l linv τ) {σ : Type} (f : MvPowerSeries σ K) : Ser τ σ ⧸ lgSub D σ :=
  (lgSub D σ).mkQ (toS τ f)
def phi (D : Data R l linv τ) (ph : PowerSeries K) {σ : Type} (g : ptsSub D σ) :
    Ser τ σ ⧸ lgSub D σ := cls D (PowerSeries.subst (pt D g) ph)
end Construct
end Calc
end Formalism.L2.Th1.C


