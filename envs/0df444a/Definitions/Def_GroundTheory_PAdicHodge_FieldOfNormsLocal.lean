-- Prove2me | Definitions.Def_GroundTheory_PAdicHodge_FieldOfNormsLocal
-- name    : GroundTheory_PAdicHodge_FieldOfNormsLocal
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T11:17:14.425598+00:00
-- url     : https://prove2.me/theorems/616fa315-8da5-4157-845a-d7b89dcfee90
-- title:
--   Field Of Norms Local
-- statement:
--   Definitions and structural lemmas for Field Of Norms Local, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FieldOfNormsLocal.lean

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_FieldOfNormsField
import Definitions.Def_GroundTheory_LocalFields_Examples
import Theorems.Thm_GroundTheory_LocalField_coe_homeomorphOfIsAlgebraic
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_PAdicHodge_NormTower_D_pos
import Theorems.Thm_GroundTheory_PAdicHodge_NormTower_Fam_eq_zero_iff
import Theorems.Thm_GroundTheory_PAdicHodge_NormTower_Fam_inv_val
import Theorems.Thm_GroundTheory_PAdicHodge_NormTower_Fam_mul_val
import Theorems.Thm_GroundTheory_PAdicHodge_NormTower_Fam_one_val
import Theorems.Thm_GroundTheory_PAdicHodge_NormTower_Fam_toFam_add
import Theorems.Thm_GroundTheory_PAdicHodge_NormTower_Fam_toFam_mul
import Theorems.Thm_GroundTheory_PAdicHodge_NormTower_Fam_zero_val
import Theorems.Thm_GroundTheory_PAdicHodge_NormTower_N_one
import Theorems.Thm_GroundTheory_PAdicHodge_NormTower_N_zero
import Theorems.Thm_GroundTheory_PAdicHodge_NormTower_Plus_charP
import Theorems.Thm_GroundTheory_PAdicHodge_NormTower_Plus_natCast_p
import Theorems.Thm_GroundTheory_PAdicHodge_NormTower_Plus_nrm_add_val_zero_le
import Theorems.Thm_GroundTheory_PAdicHodge_continuous_nrm
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_add_le_of_le
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_eq_zero
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_inv
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_mul
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_neg
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_nonneg
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_one
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_pow
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_zero
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_NormTower___lt_one_de857b87b125
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.coe_homeomorphOfIsAlgebraic
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.PAdicHodge.NormTower.Fam.one_val
attribute [local simp] GroundTheory.PAdicHodge.NormTower.Fam.zero_val
attribute [local simp] GroundTheory.PAdicHodge.NormTower.N_one
attribute [local simp] GroundTheory.PAdicHodge.NormTower.N_zero
attribute [local simp] GroundTheory.PAdicHodge.nrm_eq_zero
attribute [local simp] GroundTheory.PAdicHodge.nrm_neg
attribute [local simp] GroundTheory.PAdicHodge.nrm_one
attribute [local simp] GroundTheory.PAdicHodge.nrm_zero


set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.style.haveILetI false
namespace GroundTheory.PAdicHodge
open GroundTheory.LocalField ValuativeRel Filter Topology
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] {p : ℕ}
namespace NormTower
variable (t : NormTower K Ω p)
namespace Plus
variable {t}
theorem sub_cong (x y : t.Plus) (n : ℕ) : nrm K ((x - y).1 n - (x.1 n - y.1 n)) ≤ t.ρ := by
  rw [show x - y = x + -y from sub_eq_add_neg x y]
  have h1 := add_cong x (-y) n
  have h2 := neg_cong y n
  have e : (x + -y).1 n - (x.1 n - y.1 n) =
      ((x + -y).1 n - (x.1 n + (-y).1 n)) + ((-y).1 n - -y.1 n) := by ring
  rw [e]
  exact nrm_add_le_of_le h1 h2
theorem exists_le_D (M : ℕ) : ∃ j, M ≤ t.D 0 j := by
  obtain ⟨j, hj⟩ := t.exists_le_cnt 0 M
  refine ⟨j, hj.trans ?_⟩
  clear hj
  induction j with
  | zero => simp [cnt, D]
  | succ j ih =>
    rw [cnt_succ, D_succ]
    split_ifs with hk
    · have h2 : 2 ≤ p ^ t.k (0 + j) := (t.prime.two_le).trans (Nat.le_self_pow hk _)
      have := t.D_pos 0 j
      nlinarith
    · have := Nat.one_le_pow (t.k (0 + j)) p t.prime.pos
      nlinarith
end Plus
namespace Fam
variable {t}
theorem eq_scalePlus_mul_inv (x : t.Fam) (m : ℕ) (h : t.value 0 ^ m * nrm K (x.1 0) ≤ 1) :
    x = (scalePlus x m h).toFam * ((Plus.unif t ^ m).toFam)⁻¹ := by
  refine Subtype.ext (funext fun n ↦ ?_)
  rw [mul_val, inv_val]
  change x.1 n = (Plus.unif t).1 n ^ m * x.1 n * ((Plus.unif t ^ m).1 n)⁻¹
  rw [Plus.pow_val]
  have := Plus.unif_val_ne_zero (t := t) n
  field_simp
theorem nrm_add_val_zero_le (x y : t.Fam) :
    nrm K ((x + y).1 0) ≤ max (nrm K (x.1 0)) (nrm K (y.1 0)) := by
  obtain ⟨mx, hmx⟩ := exists_scale x
  obtain ⟨my, hmy⟩ := exists_scale y
  set m := max mx my
  have hv0 := t.value_pos 0
  have hv1 := (t.value_lt_one 0).le
  have hm : ∀ {z : t.Fam} {mz : ℕ}, mz ≤ m → t.value 0 ^ mz * nrm K (z.1 0) ≤ 1 →
      t.value 0 ^ m * nrm K (z.1 0) ≤ 1 := fun hle hz ↦
    (mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hv0.le hv1 hle) (nrm_nonneg _)).trans hz
  have hx := hm (le_max_left _ _) hmx
  have hy := hm (le_max_right _ _) hmy
  set a := scalePlus x m hx
  set b := scalePlus y m hy
  set w := (Plus.unif t ^ m).toFam
  have hxy : x + y = (a + b).toFam * w⁻¹ := by
    conv_lhs => rw [eq_scalePlus_mul_inv x m hx, eq_scalePlus_mul_inv y m hy]
    rw [toFam_add]; ring
  have hw : nrm K (w⁻¹.1 0) = (t.value 0 ^ m)⁻¹ := by
    rw [inv_val, nrm_inv]
    change (nrm K ((Plus.unif t ^ m).1 0))⁻¹ = _
    rw [Plus.pow_val, nrm_pow, Plus.nrm_unif]
  have ha : nrm K (x.1 0) = nrm K (a.1 0) * (t.value 0 ^ m)⁻¹ := by
    conv_lhs => rw [eq_scalePlus_mul_inv x m hx]
    rw [mul_val, nrm_mul, hw]; rfl
  have hb : nrm K (y.1 0) = nrm K (b.1 0) * (t.value 0 ^ m)⁻¹ := by
    conv_lhs => rw [eq_scalePlus_mul_inv y m hy]
    rw [mul_val, nrm_mul, hw]; rfl
  rw [hxy, mul_val, nrm_mul, hw, ha, hb, ← max_mul_of_nonneg _ _ (inv_nonneg.mpr (pow_nonneg hv0.le _))]
  exact mul_le_mul_of_nonneg_right (Plus.nrm_add_val_zero_le a b) (inv_nonneg.mpr (pow_nonneg hv0.le _))
variable (t) in

def abv : AbsoluteValue t.Fam ℝ where
  toFun x := nrm K (x.1 0)
  map_mul' x y := by simp only [mul_val, nrm_mul]
  nonneg' x := nrm_nonneg _
  eq_zero' x := by rw [nrm_eq_zero, ← eq_zero_iff]
  add_le' x y := (nrm_add_val_zero_le x y).trans (max_le_add_of_nonneg (nrm_nonneg _) (nrm_nonneg _))
theorem abv_add_le_max (x y : t.Fam) : abv t (x + y) ≤ max (abv t x) (abv t y) :=
  nrm_add_val_zero_le x y
theorem abv_unif : abv t (Plus.unif t).toFam = t.value 0 :=
  Plus.nrm_unif 0
end Fam
namespace Fam
variable {t}
theorem toFam_zero : (0 : t.Plus).toFam = 0 := Subtype.ext (funext fun n ↦ by rw [zero_val]; rfl)
theorem toFam_one : (1 : t.Plus).toFam = 1 := Subtype.ext (funext fun n ↦ by rw [one_val]; rfl)
variable (t) in

def toFamHom : t.Plus →+* t.Fam where
  toFun := Plus.toFam
  map_one' := toFam_one
  map_mul' := toFam_mul
  map_zero' := toFam_zero
  map_add' := toFam_add
theorem toFam_sub (a b : t.Plus) : (a - b).toFam = a.toFam - b.toFam :=
  map_sub (toFamHom t) a b
theorem natCast_p : ((p : ℕ) : t.Fam) = 0 := by
  rw [← map_natCast (toFamHom t), Plus.natCast_p, map_zero]
instance charP : CharP t.Fam p :=
  (CharP.charP_iff_prime_eq_zero t.prime).mpr natCast_p
instance instNormedField : NormedField t.Fam :=
  (abv t).toNormedField
theorem norm_def (x : t.Fam) : ‖x‖ = nrm K (x.1 0) := rfl
instance instIsUltrametricDist : IsUltrametricDist t.Fam :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm abv_add_le_max
theorem norm_unif : ‖(Plus.unif t).toFam‖ = t.value 0 := abv_unif
instance instNontriviallyNormedField : NontriviallyNormedField t.Fam where
  non_trivial := ⟨((Plus.unif t).toFam)⁻¹, by
    rw [norm_inv, norm_unif]; exact one_lt_inv_iff₀.mpr ⟨t.value_pos 0, t.value_lt_one 0⟩⟩
def intFamSet : Set (ℕ → Ω) := {z | t.IsIntFam z}
variable (t) in
theorem isCompact_intFamSet : IsCompact (intFamSet (t := t)) := by
  have hP : IsCompact {z : ℕ → Ω | ∀ n, z n ∈ t.intSet n} :=
    isCompact_pi_infinite t.isCompact_intSet
  have hC : IsClosed {z : ℕ → Ω | ∀ n, nrm K (t.N n (z (n + 1)) - z n) ≤ 0} := by
    have e : {z : ℕ → Ω | ∀ n, nrm K (t.N n (z (n + 1)) - z n) ≤ 0} =
        ⋂ n, {z : ℕ → Ω | nrm K (t.N n (z (n + 1)) - z n) ≤ 0} := by ext; simp
    rw [e]
    exact isClosed_iInter fun n ↦ isClosed_le ((continuous_nrm K Ω).comp
      (((t.continuous_N n).comp (continuous_apply _)).sub (continuous_apply _))) continuous_const
  convert hP.inter_right hC using 1
  ext z
  simp only [intFamSet, Set.mem_ofPred_eq, Set.mem_inter_iff, IsIntFam, IsFam, intSet]
  constructor
  · rintro ⟨h, h1⟩
    exact ⟨fun n ↦ ⟨(h n).1, h1 n⟩, fun n ↦ by rw [(h n).2, sub_self, nrm_zero]⟩
  · rintro ⟨h, h1⟩
    refine ⟨fun n ↦ ⟨(h n).1, ?_⟩, fun n ↦ (h n).2⟩
    rw [← sub_eq_zero, ← nrm_eq_zero (K := K)]
    exact le_antisymm (h1 n) (nrm_nonneg _)
open Classical in

def ofSeq (z : ℕ → Ω) : t.Fam :=
  if h : t.IsFam z then ⟨z, h⟩ else 0
theorem ofSeq_of_isFam {z : ℕ → Ω} (h : t.IsFam z) : ofSeq z = ⟨z, h⟩ := by
  unfold ofSeq; exact dif_pos h
variable (t) in

theorem isCompact_closedBall : IsCompact (Metric.closedBall (0 : t.Fam) 1) := by
  have himage : Metric.closedBall (0 : t.Fam) 1 = ofSeq '' intFamSet (t := t) := by
    ext x
    simp only [Metric.mem_closedBall, dist_zero_right, Set.mem_image]
    constructor
    · intro hx
      exact ⟨x.1, isIntFam_of_nrm_le hx, ofSeq_of_isFam x.2⟩
    · rintro ⟨z, hz, rfl⟩
      rw [ofSeq_of_isFam hz.1]
      exact hz.2 0
  rw [himage]
  refine (isCompact_intFamSet t).image_of_continuousOn fun z₀ hz₀ ↦ ?_
  rw [ContinuousWithinAt, Metric.tendsto_nhds]
  intro ε hε
  set ρ' := max t.ρ (1 / 2)
  have hρ'1 : ρ' < 1 := max_lt t.ρ_lt_one (by norm_num)
  have hρ'0 : 0 < ρ' := lt_max_of_lt_right (by norm_num)
  obtain ⟨M, hM⟩ := exists_pow_lt_of_lt_one hε hρ'1
  obtain ⟨j, hj⟩ := Plus.exists_le_D (t := t) M
  have hU : {z : ℕ → Ω | nrm K (z j - z₀ j) < ρ'} ∈ 𝓝[intFamSet (t := t)] z₀ := by
    refine mem_nhdsWithin_of_mem_nhds (IsOpen.mem_nhds ?_ ?_)
    · exact isOpen_lt ((continuous_nrm K Ω).comp ((continuous_apply j).sub continuous_const))
        continuous_const
    · show nrm K (z₀ j - z₀ j) < ρ'
      rw [sub_self, nrm_zero]; exact hρ'0
  filter_upwards [hU, self_mem_nhdsWithin] with z hz hzI
  let a : t.Plus := ⟨z, hzI⟩
  let b : t.Plus := ⟨z₀, hz₀⟩
  have ha : ofSeq z = a.toFam := ofSeq_of_isFam hzI.1
  have hb : ofSeq z₀ = b.toFam := ofSeq_of_isFam hz₀.1
  rw [dist_eq_norm, ha, hb, ← toFam_sub, norm_def]

  have h1 : nrm K ((a - b).1 j) ≤ ρ' := by
    have e : (a - b).1 j = ((a - b).1 j - (a.1 j - b.1 j)) + (a.1 j - b.1 j) := by ring
    rw [e]
    exact nrm_add_le_of_le ((Plus.sub_cong a b j).trans (le_max_left _ _)) hz.le
  calc nrm K ((a - b).toFam.1 0) = nrm K ((a - b).1 j) ^ t.D 0 j := Plus.nrm_val_zero (a - b) j
    _ ≤ ρ' ^ t.D 0 j := pow_le_pow_left₀ (nrm_nonneg _) h1 _
    _ ≤ ρ' ^ M := pow_le_pow_of_le_one hρ'0.le hρ'1.le hj
    _ < ε := hM
instance instProperSpace : ProperSpace t.Fam := by
  haveI : WeaklyLocallyCompactSpace t.Fam := ⟨fun x ↦ ⟨Metric.closedBall x 1, by
    have : Metric.closedBall x 1 = (fun y ↦ x + y) '' Metric.closedBall 0 1 := by
      ext y
      simp only [Set.mem_image, Metric.mem_closedBall, dist_eq_norm]
      constructor
      · intro h; exact ⟨y - x, by simpa using h, by ring⟩
      · rintro ⟨z, hz, rfl⟩; simpa using hz
    rw [this]
    exact (isCompact_closedBall t).image (continuous_const.add continuous_id),
    Metric.closedBall_mem_nhds x one_pos⟩⟩
  exact .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace t.Fam
instance instValuativeRel : ValuativeRel t.Fam :=
  ValuativeRel.ofValuation (NormedField.valuation (K := t.Fam))
theorem vle_iff_norm_le (x y : t.Fam) : x ≤ᵥ y ↔ ‖x‖ ≤ ‖y‖ := by
  change NormedField.valuation x ≤ NormedField.valuation y ↔ _
  exact NNReal.coe_le_coe
instance instCompatible : (NormedField.valuation (K := t.Fam)).Compatible :=
  Valuation.Compatible.ofValuation _
instance instIsValuativeTopology : IsValuativeTopology t.Fam := by
  let : Valued t.Fam NNReal := NormedField.toValued
  have : (Valued.v : Valuation t.Fam NNReal).Compatible := instCompatible
  exact GroundTheory.LocalField.isValuativeTopology_of_valued
instance instIsNontrivial : IsNontrivial t.Fam := by
  refine ⟨⟨valuation t.Fam (Plus.unif t).toFam, ?_, ?_⟩⟩
  · rw [ne_eq, Valuation.zero_iff, ← norm_eq_zero, norm_unif]
    exact (t.value_pos 0).ne'
  · intro h
    have h2 : (1 : t.Fam) ≤ᵥ (Plus.unif t).toFam := by
      rw [Valuation.vle_iff_le (valuation t.Fam), h, map_one]
    rw [vle_iff_norm_le, norm_unif, norm_one] at h2
    exact absurd h2 (not_le.2 (t.value_lt_one 0))
instance instIsNonarchimedeanLocalField : IsNonarchimedeanLocalField t.Fam where
  toIsValuativeTopology := inferInstance
  toLocallyCompactSpace := inferInstance
  toIsNontrivial := inferInstance
end Fam
end NormTower
end GroundTheory.PAdicHodge


