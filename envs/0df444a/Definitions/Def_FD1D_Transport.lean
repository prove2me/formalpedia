-- Prove2me | Definitions.Def_FD1D_Transport
-- name    : FD1D_Transport
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T10:07:22.599512+00:00
-- url     : https://prove2.me/theorems/45b93648-74b9-52cd-81a3-d1585c1808ac
-- title:
--   Transport
-- statement:
--   Definitions and structural lemmas for Transport, from Yash Kanoria (ykanoria/FD1d-Lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Tight upper bound for fully dynamic matching on the line development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Transport.lean

import Definitions.Def_FD1D_Basic
import Theorems.Thm_FD1D_FiniteLaw_expect_const
attribute [local simp] FD1D.FiniteLaw.expect_const


set_option autoImplicit true
namespace FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral
inductive DyadicMass : ℕ → Type
  | leaf (mass : ℝ) : DyadicMass 0
  | branch {L : ℕ} (left right : DyadicMass L) : DyadicMass (L + 1)
namespace DyadicMass
def total : {L : ℕ} → DyadicMass L → ℝ
  | 0, leaf m => m
  | _ + 1, branch l r => total l + total r
def leaves : {L : ℕ} → DyadicMass L → List ℝ
  | 0, leaf m => [m]
  | _ + 1, branch l r => leaves l ++ leaves r
@[simp] theorem length_leaves {L : ℕ} (q : DyadicMass L) :
    q.leaves.length = 2 ^ L := by
  induction q with
  | leaf => simp [leaves]
  | @branch L l r ihl ihr =>
      simp [leaves, ihl, ihr, pow_succ]
      omega
def ofLeafVector : (L : ℕ) → (Fin (2 ^ L) → ℝ) → DyadicMass L
  | 0, f => .leaf (f 0)
  | L + 1, f =>
      let e : Fin (2 ^ L + 2 ^ L) ≃ Fin (2 ^ (L + 1)) :=
        finCongr (by rw [pow_succ]; omega)
      .branch
        (ofLeafVector L (fun i => f (e (Fin.castAdd _ i))))
        (ofLeafVector L (fun i => f (e (Fin.natAdd _ i))))
@[simp] theorem total_ofLeafVector (L : ℕ) (f : Fin (2 ^ L) → ℝ) :
    (ofLeafVector L f).total = ∑ i, f i := by
  induction L with
  | zero =>
      simp [ofLeafVector, total]
  | succ L ih =>
      simp only [ofLeafVector, total]
      rw [ih, ih]
      let e : Fin (2 ^ L + 2 ^ L) ≃ Fin (2 ^ (L + 1)) :=
        finCongr (by rw [pow_succ]; omega)
      rw [← e.sum_comp f]
      exact (Fin.sum_univ_add (fun i => f (e i))).symm
def allNonneg : {L : ℕ} → DyadicMass L → Prop
  | 0, leaf m => 0 ≤ m
  | _ + 1, branch l r => allNonneg l ∧ allNonneg r
theorem total_nonneg {L : ℕ} (q : DyadicMass L) (hq : q.allNonneg) :
    0 ≤ q.total := by
  induction q with
  | leaf => exact hq
  | branch l r ihl ihr =>
      exact add_nonneg (ihl hq.1) (ihr hq.2)
structure IsProbability {L : ℕ} (q : DyadicMass L) : Prop where
  nonneg : q.allNonneg
  total_eq_one : q.total = 1
def piecewiseCDF : {L : ℕ} → DyadicMass L → ℝ → ℝ
  | 0, leaf m => fun z => m * z
  | _ + 1, branch l r => fun z =>
      if z ≤ 1 / 2 then piecewiseCDF l (2 * z)
      else total l + piecewiseCDF r (2 * z - 1)
@[simp] theorem piecewiseCDF_zero {L : ℕ} (q : DyadicMass L) :
    q.piecewiseCDF 0 = 0 := by
  induction q with
  | leaf => simp [piecewiseCDF]
  | branch l r ihl ihr => simp [piecewiseCDF, ihl]
@[simp] theorem piecewiseCDF_one {L : ℕ} (q : DyadicMass L) :
    q.piecewiseCDF 1 = q.total := by
  induction q with
  | leaf => simp [piecewiseCDF, total]
  | branch l r ihl ihr => norm_num [piecewiseCDF, total, ihr]
theorem piecewiseCDF_nonneg {L : ℕ} (q : DyadicMass L) (hq : q.allNonneg)
    {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    0 ≤ q.piecewiseCDF z := by
  induction q generalizing z with
  | leaf m =>
      simp only [piecewiseCDF]
      exact mul_nonneg hq hz0
  | @branch L l r ihl ihr =>
      simp only [piecewiseCDF]
      by_cases hz : z ≤ 1 / 2
      · rw [if_pos hz]
        exact ihl hq.1 (by linarith) (by linarith)
      · rw [if_neg hz]
        exact add_nonneg (total_nonneg l hq.1)
          (ihr hq.2 (by linarith) (by linarith))
theorem piecewiseCDF_le_total {L : ℕ} (q : DyadicMass L) (hq : q.allNonneg)
    {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    q.piecewiseCDF z ≤ q.total := by
  induction q generalizing z with
  | leaf m =>
      simp only [piecewiseCDF, total]
      have := mul_nonneg hq (sub_nonneg.mpr hz1)
      nlinarith
  | @branch L l r ihl ihr =>
      simp only [piecewiseCDF]
      by_cases hz : z ≤ 1 / 2
      · rw [if_pos hz]
        have hle := ihl hq.1 (z := 2 * z) (by linarith) (by linarith)
        have hr := total_nonneg r hq.2
        simp only [total]
        linarith
      · rw [if_neg hz]
        have hle := ihr hq.2 (z := 2 * z - 1) (by linarith) (by linarith)
        simp only [total]
        linarith
theorem piecewiseCDF_monotoneOn {L : ℕ} (q : DyadicMass L) (hq : q.allNonneg) :
    MonotoneOn q.piecewiseCDF (Icc 0 1) := by
  induction q with
  | leaf m =>
      intro x hx y hy hxy
      simp only [piecewiseCDF]
      exact mul_le_mul_of_nonneg_left hxy hq
  | @branch L l r ihl ihr =>
      intro x hx y hy hxy
      simp only [piecewiseCDF]
      by_cases hxhalf : x ≤ 1 / 2
      · rw [if_pos hxhalf]
        by_cases hyhalf : y ≤ 1 / 2
        · rw [if_pos hyhalf]
          exact ihl hq.1 (a := 2 * x) (b := 2 * y)
            ⟨by linarith [hx.1], by linarith⟩
            ⟨by linarith [hy.1], by linarith⟩ (by linarith)
        · rw [if_neg hyhalf]
          have hleft := piecewiseCDF_le_total l hq.1
            (z := 2 * x) (by linarith [hx.1]) (by linarith)
          have hright := piecewiseCDF_nonneg r hq.2
            (z := 2 * y - 1) (by linarith) (by linarith [hy.2])
          linarith
      · have hyhalf : ¬y ≤ 1 / 2 := by linarith
        rw [if_neg hxhalf, if_neg hyhalf]
        simpa [add_comm] using add_le_add_left (ihr hq.2
          (a := 2 * x - 1) (b := 2 * y - 1)
          ⟨by linarith, by linarith [hx.2]⟩
          ⟨by linarith, by linarith [hy.2]⟩ (by linarith)) l.total
def quantile : {L : ℕ} → DyadicMass L → ℝ → ℝ
  | 0, leaf m => fun u => u / m
  | _ + 1, branch l r => fun u =>
      if u ≤ l.total then l.quantile u / 2
      else (1 + r.quantile (u - l.total)) / 2
def selectedLeaf : {L : ℕ} → DyadicMass L → ℝ → ℝ
  | 0, leaf _ => fun _ => 0
  | _ + 1, branch l r => fun u =>
      if u ≤ l.total then l.selectedLeaf u / 2
      else (1 + r.selectedLeaf (u - l.total)) / 2
theorem piecewiseCDF_measurable {L : ℕ} (q : DyadicMass L) :
    Measurable q.piecewiseCDF := by
  induction q with
  | leaf =>
      exact measurable_const.mul measurable_id
  | @branch L l r ihl ihr =>
      apply Measurable.ite (measurableSet_le measurable_id measurable_const)
      · exact ihl.comp (measurable_const.mul measurable_id)
      · exact measurable_const.add
          (ihr.comp ((measurable_const.mul measurable_id).sub measurable_const))
theorem quantile_measurable {L : ℕ} (q : DyadicMass L) :
    Measurable q.quantile := by
  induction q with
  | leaf =>
      exact measurable_id.div_const _
  | @branch L l r ihl ihr =>
      apply Measurable.ite (measurableSet_le measurable_id measurable_const)
      · exact ihl.div_const _
      · exact (measurable_const.add
          (ihr.comp (measurable_id.sub measurable_const))).div_const _
theorem selectedLeaf_measurable {L : ℕ} (q : DyadicMass L) :
    Measurable q.selectedLeaf := by
  induction q with
  | leaf =>
      exact measurable_const
  | @branch L l r ihl ihr =>
      apply Measurable.ite (measurableSet_le measurable_id measurable_const)
      · exact ihl.div_const _
      · exact (measurable_const.add
          (ihr.comp (measurable_id.sub measurable_const))).div_const _
theorem quantile_mem_unit {L : ℕ} (q : DyadicMass L) (hq : q.allNonneg)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ q.total) :
    q.quantile u ∈ Icc (0 : ℝ) 1 := by
  induction q generalizing u with
  | leaf m =>
      simp only [quantile]
      by_cases hm : m = 0
      · subst m
        have hu : u = 0 := by simpa [total] using le_antisymm hu1 hu0
        simp [hu]
      · have hmpos : 0 < m := lt_of_le_of_ne hq (Ne.symm hm)
        constructor
        · exact div_nonneg hu0 hmpos.le
        · exact (div_le_one hmpos).2 (by simpa [total] using hu1)
  | @branch L l r ihl ihr =>
      simp only [quantile]
      by_cases hu : u ≤ l.total
      · rw [if_pos hu]
        have hlocal := ihl hq.1 hu0 hu
        constructor <;> linarith [hlocal.1, hlocal.2]
      · rw [if_neg hu]
        have hulocal : 0 ≤ u - l.total := by linarith
        have hurlocal : u - l.total ≤ r.total := by
          rw [total] at hu1
          linarith
        have hlocal := ihr hq.2 hulocal hurlocal
        constructor <;> linarith [hlocal.1, hlocal.2]
theorem selectedLeaf_mem_unit {L : ℕ} (q : DyadicMass L) (hq : q.allNonneg)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ q.total) :
    q.selectedLeaf u ∈ Icc (0 : ℝ) 1 := by
  induction q generalizing u with
  | leaf =>
      simp [selectedLeaf]
  | @branch L l r ihl ihr =>
      simp only [selectedLeaf]
      by_cases hu : u ≤ l.total
      · rw [if_pos hu]
        have hlocal := ihl hq.1 hu0 hu
        constructor <;> linarith [hlocal.1, hlocal.2]
      · rw [if_neg hu]
        have hulocal : 0 ≤ u - l.total := by linarith
        have hurlocal : u - l.total ≤ r.total := by
          rw [total] at hu1
          linarith
        have hlocal := ihr hq.2 hulocal hurlocal
        constructor <;> linarith [hlocal.1, hlocal.2]
theorem quantile_pos {L : ℕ} (q : DyadicMass L) (hq : q.allNonneg)
    {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ q.total) :
    0 < q.quantile u := by
  induction q generalizing u with
  | leaf m =>
      simp only [quantile]
      have hm : 0 < m := lt_of_lt_of_le hu0 (by simpa [total] using hu1)
      exact div_pos hu0 hm
  | @branch L l r ihl ihr =>
      simp only [quantile]
      by_cases hu : u ≤ l.total
      · rw [if_pos hu]
        exact div_pos (ihl hq.1 hu0 hu) (by norm_num)
      · rw [if_neg hu]
        have hlocal : 0 ≤ r.quantile (u - l.total) :=
          (r.quantile_mem_unit hq.2 (by linarith)
            (by
              rw [total] at hu1
              linarith)).1
        linarith
theorem quantile_le_iff {L : ℕ} (q : DyadicMass L) (hq : q.allNonneg)
    {u z : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ q.total)
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    q.quantile u ≤ z ↔ u ≤ q.piecewiseCDF z := by
  induction q generalizing u z with
  | leaf m =>
      simp only [quantile, piecewiseCDF]
      by_cases hm : m = 0
      · subst m
        have hu : u = 0 := by simpa [total] using le_antisymm hu1 hu0
        simp [hu, hz0]
      · have hmpos : 0 < m := lt_of_le_of_ne hq (Ne.symm hm)
        rw [div_le_iff₀ hmpos]
        ring_nf
  | @branch L l r ihl ihr =>
      simp only [quantile, piecewiseCDF]
      by_cases hz : z ≤ 1 / 2
      · rw [if_pos hz]
        have h2z0 : 0 ≤ 2 * z := by linarith
        have h2z1 : 2 * z ≤ 1 := by linarith
        by_cases hu : u ≤ l.total
        · rw [if_pos hu]
          rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
          simpa [mul_comm] using ihl hq.1 hu0 hu h2z0 h2z1
        · rw [if_neg hu]
          have hqr := quantile_mem_unit r hq.2
            (u := u - l.total) (by linarith)
            (by
              rw [total] at hu1
              linarith)
          have hqrpos := quantile_pos r hq.2 (u := u - l.total)
            (by linarith) (by
              rw [total] at hu1
              linarith)
          have hleft := piecewiseCDF_le_total l hq.1 h2z0 h2z1
          constructor
          · intro h
            exfalso
            linarith
          · intro h
            exfalso
            exact hu (h.trans hleft)
      · rw [if_neg hz]
        have h2z0 : 0 ≤ 2 * z - 1 := by linarith
        have h2z1 : 2 * z - 1 ≤ 1 := by linarith
        by_cases hu : u ≤ l.total
        · rw [if_pos hu]
          have hql := quantile_mem_unit l hq.1 hu0 hu
          have hright := piecewiseCDF_nonneg r hq.2 h2z0 h2z1
          constructor
          · intro _
            linarith
          · intro _
            linarith [hql.2]
        · rw [if_neg hu]
          have hulocal : 0 ≤ u - l.total := by linarith
          have hurlocal : u - l.total ≤ r.total := by
            rw [total] at hu1
            linarith
          have hiff := ihr hq.2 hulocal hurlocal h2z0 h2z1
          constructor
          · intro h
            have hqle : r.quantile (u - l.total) ≤ 2 * z - 1 := by
              linarith
            have := hiff.mp hqle
            linarith
          · intro h
            have hlocal : u - l.total ≤ r.piecewiseCDF (2 * z - 1) := by
              linarith
            have := hiff.mpr hlocal
            linarith
theorem selectedLeaf_sub_quantile_le {L : ℕ} (q : DyadicMass L)
    (hq : q.allNonneg) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ q.total) :
    |q.selectedLeaf u - q.quantile u| ≤ 1 / ((2 ^ L : ℕ) : ℝ) := by
  induction q generalizing u with
  | leaf m =>
      have hqu := (leaf m).quantile_mem_unit hq hu0 hu1
      simp only [selectedLeaf]
      rw [abs_of_nonpos (by simpa using hqu.1)]
      norm_num
      linarith [hqu.2]
  | @branch L l r ihl ihr =>
      simp only [selectedLeaf, quantile]
      by_cases hu : u ≤ l.total
      · rw [if_pos hu, if_pos hu]
        have h := ihl hq.1 hu0 hu
        rw [show l.selectedLeaf u / 2 - l.quantile u / 2 =
          (l.selectedLeaf u - l.quantile u) / 2 by ring]
        rw [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        simp only [pow_succ]
        norm_num at h ⊢
        nlinarith
      · rw [if_neg hu, if_neg hu]
        have hulocal : 0 ≤ u - l.total := by linarith
        have hurlocal : u - l.total ≤ r.total := by
          rw [total] at hu1
          linarith
        have h := ihr hq.2 hulocal hurlocal
        rw [show (1 + r.selectedLeaf (u - l.total)) / 2 -
            (1 + r.quantile (u - l.total)) / 2 =
          (r.selectedLeaf (u - l.total) -
            r.quantile (u - l.total)) / 2 by ring]
        rw [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        simp only [pow_succ]
        norm_num at h ⊢
        nlinarith
def unitTent (z : ℝ) : ℝ :=
  if z ≤ 1 / 2 then z else 1 - z
def haarSeries : {L : ℕ} → DyadicMass L → ℝ → ℝ
  | 0, leaf _ => fun _ => 0
  | _ + 1, branch l r => fun z =>
      (total l - total r) * unitTent z +
        if z ≤ 1 / 2 then haarSeries l (2 * z)
        else haarSeries r (2 * z - 1)
end DyadicMass
def dyadicTent (l p z : ℝ) : ℝ :=
  (Icc l (l + p / 2)).indicator (fun x => (x - l) / p) z +
    (Ioc (l + p / 2) (l + p)).indicator (fun x => (l + p - x) / p) z
structure HaarTerm where
  left : ℝ
  width : ℝ
  coeff : ℝ
namespace HaarTerm
def value (t : HaarTerm) (z : ℝ) : ℝ :=
  t.coeff * dyadicTent t.left t.width z
end HaarTerm
def haarTermSum (ts : List HaarTerm) (z : ℝ) : ℝ :=
  (ts.map (fun t => t.value z)).sum
@[simp] theorem haarTermSum_nil (z : ℝ) :
    haarTermSum [] z = 0 := rfl
@[simp] theorem haarTermSum_cons (t : HaarTerm) (ts : List HaarTerm) (z : ℝ) :
    haarTermSum (t :: ts) z = t.value z + haarTermSum ts z := by
  simp [haarTermSum]
@[simp] theorem haarTermSum_append (s t : List HaarTerm) (z : ℝ) :
    haarTermSum (s ++ t) z = haarTermSum s z + haarTermSum t z := by
  simp [haarTermSum]
def DyadicMass.haarTermsAt :
    {L : ℕ} → ℝ → ℝ → DyadicMass L → List HaarTerm
  | 0, _, _, .leaf _ => []
  | _ + 1, a, p, .branch l r =>
      ⟨a, p, l.total - r.total⟩ ::
        (haarTermsAt a (p / 2) l ++
          haarTermsAt (a + p / 2) (p / 2) r)
def DyadicMass.haarTerms {L : ℕ} (q : DyadicMass L) : List HaarTerm :=
  q.haarTermsAt 0 1
@[simp] theorem DyadicMass.length_haarTermsAt
    {L : ℕ} (q : DyadicMass L) (a p : ℝ) :
    (q.haarTermsAt a p).length = 2 ^ L - 1 := by
  induction q generalizing a p with
  | leaf => simp [haarTermsAt]
  | @branch L l r ihl ihr =>
      have hpow : 0 < 2 ^ L := Nat.two_pow_pos L
      simp [haarTermsAt, ihl, ihr, pow_succ]
      omega
@[simp] theorem DyadicMass.length_haarTerms
    {L : ℕ} (q : DyadicMass L) :
    q.haarTerms.length = 2 ^ L - 1 := by
  simp [haarTerms]
abbrev CompleteHaarNode (L : ℕ) := Σ d : Fin L, Fin (2 ^ d.val)
def haarNodeLeft {L : ℕ} (v : CompleteHaarNode L) : ℝ :=
  (v.2.val : ℝ) / (2 ^ v.1.val : ℕ)
def haarNodeWidth {L : ℕ} (v : CompleteHaarNode L) : ℝ :=
  1 / (2 ^ v.1.val : ℕ)
def haarNodeTent {L : ℕ} (v : CompleteHaarNode L) : ℝ → ℝ :=
  dyadicTent (haarNodeLeft v) (haarNodeWidth v)
def HaarSupportNested {L : ℕ} (v w : CompleteHaarNode L) : Prop :=
  Icc (haarNodeLeft v) (haarNodeLeft v + haarNodeWidth v) ⊆
    Icc (haarNodeLeft w) (haarNodeLeft w + haarNodeWidth w)
namespace DyadicMass
def nodeChildMasses : {L : ℕ} → DyadicMass L → CompleteHaarNode L → ℝ × ℝ
  | 0, .leaf _, v => Fin.elim0 v.1
  | _ + 1, .branch l r, ⟨⟨0, _⟩, _⟩ => (l.total, r.total)
  | L + 1, .branch l r, ⟨⟨d + 1, hd⟩, v⟩ =>
      let d' : Fin L := ⟨d, Nat.lt_of_succ_lt_succ hd⟩
      let w : Fin (2 ^ d + 2 ^ d) :=
        Fin.cast (by rw [pow_succ]; omega) v
      Fin.addCases
        (fun vl => nodeChildMasses l ⟨d', vl⟩)
        (fun vr => nodeChildMasses r ⟨d', vr⟩) w
def nodeCoefficient {L : ℕ} (q : DyadicMass L) (v : CompleteHaarNode L) : ℝ :=
  (q.nodeChildMasses v).1 - (q.nodeChildMasses v).2
@[simp] theorem nodeChildMasses_root {L : ℕ} (l r : DyadicMass L) :
    (branch l r).nodeChildMasses
      ⟨⟨0, Nat.zero_lt_succ L⟩, (0 : Fin 1)⟩ = (l.total, r.total) :=
  rfl
@[simp] theorem nodeCoefficient_root {L : ℕ} (l r : DyadicMass L) :
    (branch l r).nodeCoefficient
      ⟨⟨0, Nat.zero_lt_succ L⟩, (0 : Fin 1)⟩ = l.total - r.total :=
  rfl
def leftNode {L : ℕ} (v : CompleteHaarNode L) : CompleteHaarNode (L + 1) :=
  ⟨v.1.succ, ⟨v.2.val, by
    change v.2.val < 2 ^ (v.1.val + 1)
    rw [pow_succ]
    omega⟩⟩
def rightNode {L : ℕ} (v : CompleteHaarNode L) : CompleteHaarNode (L + 1) :=
  ⟨v.1.succ, ⟨2 ^ v.1.val + v.2.val, by
    change 2 ^ v.1.val + v.2.val < 2 ^ (v.1.val + 1)
    rw [pow_succ]
    omega⟩⟩
def childFinEquiv (d : ℕ) : Fin (2 ^ d + 2 ^ d) ≃ Fin (2 ^ (d + 1)) :=
  finCongr (by rw [pow_succ]; omega)
@[simp] theorem haarNodeLeft_leftNode {L : ℕ} (v : CompleteHaarNode L) :
    haarNodeLeft (leftNode v) = haarNodeLeft v / 2 := by
  simp [haarNodeLeft, leftNode, pow_succ]
  ring
@[simp] theorem haarNodeWidth_leftNode {L : ℕ} (v : CompleteHaarNode L) :
    haarNodeWidth (leftNode v) = haarNodeWidth v / 2 := by
  simp [haarNodeWidth, leftNode, pow_succ]
  ring
@[simp] theorem haarNodeLeft_rightNode {L : ℕ} (v : CompleteHaarNode L) :
    haarNodeLeft (rightNode v) = 1 / 2 + haarNodeLeft v / 2 := by
  simp [haarNodeLeft, rightNode, pow_succ]
  field_simp
@[simp] theorem haarNodeWidth_rightNode {L : ℕ} (v : CompleteHaarNode L) :
    haarNodeWidth (rightNode v) = haarNodeWidth v / 2 := by
  simp [haarNodeWidth, rightNode, pow_succ]
  ring
@[simp] theorem nodeChildMasses_leftNode {L : ℕ} (l r : DyadicMass L)
    (v : CompleteHaarNode L) :
    (branch l r).nodeChildMasses (leftNode v) = l.nodeChildMasses v := by
  rcases v with ⟨⟨d, hd⟩, v⟩
  simp [leftNode, nodeChildMasses, Fin.addCases]
@[simp] theorem nodeChildMasses_rightNode {L : ℕ} (l r : DyadicMass L)
    (v : CompleteHaarNode L) :
    (branch l r).nodeChildMasses (rightNode v) = r.nodeChildMasses v := by
  rcases v with ⟨⟨d, hd⟩, v⟩
  simp [rightNode, nodeChildMasses, Fin.addCases]
@[simp] theorem nodeCoefficient_leftNode {L : ℕ} (l r : DyadicMass L)
    (v : CompleteHaarNode L) :
    (branch l r).nodeCoefficient (leftNode v) = l.nodeCoefficient v := by
  simp [nodeCoefficient]
@[simp] theorem nodeCoefficient_rightNode {L : ℕ} (l r : DyadicMass L)
    (v : CompleteHaarNode L) :
    (branch l r).nodeCoefficient (rightNode v) = r.nodeCoefficient v := by
  simp [nodeCoefficient]
end DyadicMass
namespace FiniteLaw
variable {Ω : Type*} [Fintype Ω]
def InvariantUnder (μ : FiniteLaw Ω) (e : Ω ≃ Ω) : Prop :=
  ∀ ω, μ.mass (e ω) = μ.mass ω
def OddSymmetry (μ : FiniteLaw Ω) (f : Ω → ℝ) : Prop :=
  ∃ e : Ω ≃ Ω, InvariantUnder μ e ∧ ∀ ω, f (e ω) = -f ω
end FiniteLaw
def IntervalsSeparated {ι : Type*} (l p : ι → ℝ) (i j : ι) : Prop :=
  l i + p i ≤ l j ∨ l j + p j ≤ l i
variable {ι Ω : Type*} [Fintype ι] [Fintype Ω]
def haarCombination (l p : ι → ℝ) (b : ι → ℝ) (z : ℝ) : ℝ :=
  ∑ i, b i * dyadicTent (l i) (p i) z
namespace DyadicMass
end DyadicMass
def haarL2 (l p : ι → ℝ) (b : ι → ℝ) : ℝ :=
  ∫ z, haarCombination l p b z ^ 2
def cdfTransportArea (f : ℝ → ℝ) : ℝ :=
  ∫ z in Icc (0 : ℝ) 1, |f z|
def leStep (a b : ℝ) : ℝ :=
  if a ≤ b then 1 else 0
structure MonotoneQuantilePolicy (F : ℝ → ℝ) where
  monotoneCDF : MonotoneOn F (Icc 0 1)
  cdf_measurable : Measurable F
  cdf_mapsTo : MapsTo F (Icc 0 1) (Icc 0 1)
  quantileMap : ℝ → ℝ
  quantile_measurable : Measurable quantileMap
  quantile_mapsTo : MapsTo quantileMap (Icc 0 1) (Icc 0 1)
  generalizedInverse : ∀ u ∈ Icc (0 : ℝ) 1, ∀ z ∈ Icc (0 : ℝ) 1,
    quantileMap u ≤ z ↔ u ≤ F z
  selectedPoint : ℝ → ℝ
  selected_measurable : Measurable selectedPoint
  selected_mapsTo : MapsTo selectedPoint (Icc 0 1) (Icc 0 1)
  withinError : ℝ
  withinError_nonneg : 0 ≤ withinError
  selected_close : ∀ u ∈ Icc (0 : ℝ) 1,
    |selectedPoint u - quantileMap u| ≤ withinError
namespace MonotoneQuantilePolicy
def expectedDistance {F : ℝ → ℝ} (P : MonotoneQuantilePolicy F) : ℝ :=
  ∫ u in Icc (0 : ℝ) 1, |P.selectedPoint u - u|
def quantileDistance {F : ℝ → ℝ} (P : MonotoneQuantilePolicy F) : ℝ :=
  ∫ u in Icc (0 : ℝ) 1, |P.quantileMap u - u|
end MonotoneQuantilePolicy
def DyadicMass.quantilePolicy {L : ℕ} (q : DyadicMass L)
    (hq : q.IsProbability) :
    MonotoneQuantilePolicy q.piecewiseCDF where
  monotoneCDF := q.piecewiseCDF_monotoneOn hq.nonneg
  cdf_measurable := q.piecewiseCDF_measurable
  cdf_mapsTo := fun z hz => ⟨q.piecewiseCDF_nonneg hq.nonneg hz.1 hz.2,
    by simpa [hq.total_eq_one] using q.piecewiseCDF_le_total hq.nonneg hz.1 hz.2⟩
  quantileMap := q.quantile
  quantile_measurable := q.quantile_measurable
  quantile_mapsTo := fun u hu => q.quantile_mem_unit hq.nonneg hu.1
    (by simpa [hq.total_eq_one] using hu.2)
  generalizedInverse := fun u hu z hz => q.quantile_le_iff hq.nonneg hu.1
    (by simpa [hq.total_eq_one] using hu.2) hz.1 hz.2
  selectedPoint := q.selectedLeaf
  selected_measurable := q.selectedLeaf_measurable
  selected_mapsTo := fun u hu => q.selectedLeaf_mem_unit hq.nonneg hu.1
    (by simpa [hq.total_eq_one] using hu.2)
  withinError := 1 / ((2 ^ L : ℕ) : ℝ)
  withinError_nonneg := by positivity
  selected_close := fun u hu => q.selectedLeaf_sub_quantile_le hq.nonneg hu.1
    (by simpa [hq.total_eq_one] using hu.2)
namespace FiniteLaw
end FiniteLaw
end
end FD1D


