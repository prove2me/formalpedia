-- Prove2me | Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_FmZeroHLatEmpty
-- name    : Formalism_LocalRingCardinality_SpanPowerMembership_FmZeroHLatEmpty
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T18:34:46.130348+00:00
-- url     : https://prove2.me/theorems/964b43b4-ec71-499c-9167-0cd203ba0dac
-- title:
--   Fm Zero HLat Empty
-- statement:
--   Definitions and structural lemmas for Fm Zero HLat Empty, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/FmZeroHLatEmpty.lean

import Definitions.Def_Formalism_LocalRingCardinality_DataForms
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


set_option autoImplicit false
noncomputable section
namespace Formalism.BasicNotions.Examples₂
open NumberField Formalism.BasicNotions
section Weights
variable {R : Ranks} (P : HCParam R)
def blkN (R : Ranks) (n : ℕ) : ℕ := (n - R.k) / (R.t + 1)
def wtN (n : ℕ) : ℚ :=
  if h : n < R.k then hcToWeightQ P.u ⟨n, h⟩
  else if hb : blkN R n < R.m then -wG R (P.e ⟨blkN R n, hb⟩) (blkN R n + 1) else 0
def wtQ (j : ℕ) (hj : j ≤ R.m) (i : Fin (R.N j)) : ℚ :=
  if h : i.1 < R.k then hcToWeightQ P.u ⟨i.1, h⟩
  else -wG R (P.e ⟨(i.1 - R.k) / (R.t + 1), R.blk_lt hj i h⟩) ((i.1 - R.k) / (R.t + 1) + 1)
theorem wtQ_eq_wtN (j : ℕ) (hj : j ≤ R.m) (i : Fin (R.N j)) : wtQ P j hj i = wtN P i.1 := by
  by_cases h : i.1 < R.k
  · simp only [wtQ, wtN, dif_pos h]
  · have hb : blkN R i.1 < R.m := R.blk_lt hj i h
    rw [wtQ, wtN, dif_neg h, dif_neg h, dif_pos hb]
    rfl
theorem u_step (i : ℕ) (hi : i + 1 < R.k) : P.u ⟨i + 1, hi⟩ + 1 ≤ P.u ⟨i, by omega⟩ := by
  have hi' : i < R.k - 1 := by omega
  have h1 : P.v ⟨i, hi'⟩ < P.u ⟨i, by omega⟩ := P.u_gt_v ⟨i, hi'⟩
  have h2 : P.u ⟨i + 1, hi⟩ < P.v ⟨i, hi'⟩ := P.v_gt_u ⟨i, hi'⟩
  obtain ⟨a, ha⟩ := P.u_half ⟨i + 1, hi⟩
  obtain ⟨c, hc⟩ := P.u_half ⟨i, by omega⟩
  obtain ⟨b, hb⟩ := P.v_int ⟨i, hi'⟩
  rw [hb, hc] at h1
  rw [hb, ha] at h2
  rw [ha, hc]
  have e1 : (a : ℚ) < b := by linarith
  have e2 : (b : ℚ) < c + 1 := by linarith
  have f1 : a < b := by exact_mod_cast e1
  have f2 : b < c + 1 := by exact_mod_cast e2
  have f3 : ((a : ℚ) + 1) ≤ c := by exact_mod_cast (show a + 1 ≤ c by omega)
  linarith
theorem wtN_eq_neg_wG_blkN (n : ℕ) (hn : ¬ n < R.k) (hb : blkN R n < R.m) :
    wtN P n = -wG R (P.e ⟨blkN R n, hb⟩) (blkN R n + 1) := by
  unfold wtN
  rw [dif_neg hn, dif_pos hb]
theorem neg_wG_le_of_adjacent_blocks (c c' : ℕ) (hc : c < R.m) (hc' : c' < R.m) (h : c' = c ∨ c' = c + 1) :
    -wG R (P.e ⟨c', hc'⟩) (c' + 1) ≤ -wG R (P.e ⟨c, hc⟩) (c + 1) := by
  rcases h with rfl | rfl
  · exact le_rfl
  · have h1 : ((R.t : ℚ) + 3) / 2 ≤ P.e ⟨c + 1, hc'⟩ - P.b ⟨c + 1, hc'⟩ := P.gap_be ⟨c + 1, hc'⟩
    have h2 : ((R.t : ℚ) + 3) / 2 ≤ P.b ⟨c + 1, hc'⟩ - P.e ⟨c, hc⟩ := P.gap_eb ⟨c, hc⟩ hc'
    simp only [wG]
    push_cast
    linarith
theorem wtN_step (n : ℕ) (hn : n + 1 < R.N R.m) : wtN P (n + 1) ≤ wtN P n := by
  by_cases hn0 : n < R.k
  · by_cases hA : n + 1 < R.k
    · have hs := u_step P n hA
      unfold wtN
      rw [dif_pos hA, dif_pos hn0]
      simp only [hcToWeightQ, rhoVec, Fin.val_mk]
      push_cast
      linarith
    · have hk : n + 1 = R.k := by omega
      have hm0 : 0 < R.m := by have := R.two_le_m; omega
      have hb : blkN R (n + 1) < R.m := by
        unfold blkN
        rw [show n + 1 - R.k = 0 by omega, Nat.zero_div]
        exact hm0
      have hb0 : blkN R (n + 1) = 0 := by
        unfold blkN
        rw [show n + 1 - R.k = 0 by omega, Nat.zero_div]
      rw [wtN_eq_neg_wG_blkN P (n + 1) hA hb]
      have he : P.e ⟨blkN R (n + 1), hb⟩ = P.e ⟨0, hm0⟩ := by
        congr 1
        exact Fin.ext hb0
      rw [he, hb0]
      have hnk : (⟨R.k - 1, by omega⟩ : Fin R.k) = ⟨n, hn0⟩ := Fin.ext (by show R.k - 1 = n; omega)
      have h1 := P.u_last_gt (by omega) hm0
      rw [hnk] at h1
      have h2 : ((R.t : ℚ) + 3) / 2 ≤ P.e ⟨0, hm0⟩ - P.b ⟨0, hm0⟩ := P.gap_be ⟨0, hm0⟩
      have hnq : (n : ℚ) + 1 = R.k := by exact_mod_cast hk
      unfold wtN
      rw [dif_pos hn0]
      simp only [wG, hcToWeightQ, rhoVec, Fin.val_mk]
      push_cast
      linarith
  · have hmn : n + 1 - R.k < R.m * (R.t + 1) := by
      unfold Ranks.N at hn
      omega
    have hb1 : blkN R (n + 1) < R.m := by
      unfold blkN
      exact (Nat.div_lt_iff_lt_mul (Nat.succ_pos _)).mpr hmn
    have hle : blkN R n ≤ blkN R (n + 1) := Nat.div_le_div_right (by omega)
    have hb0 : blkN R n < R.m := lt_of_le_of_lt hle hb1
    have hor : blkN R (n + 1) = blkN R n ∨ blkN R (n + 1) = blkN R n + 1 := by
      unfold blkN
      rw [show n + 1 - R.k = (n - R.k) + 1 by omega, Nat.succ_div]
      split_ifs <;> simp
    rw [wtN_eq_neg_wG_blkN P (n + 1) (by omega) hb1, wtN_eq_neg_wG_blkN P n hn0 hb0]
    exact neg_wG_le_of_adjacent_blocks P _ _ hb0 hb1 hor
theorem wtN_anti {n n' : ℕ} (h : n ≤ n') (hn' : n' < R.N R.m) : wtN P n' ≤ wtN P n := by
  revert hn'
  induction n', h using Nat.le_induction with
  | base => intro _; exact le_rfl
  | succ q hq ih =>
    intro hq'
    exact le_trans (wtN_step P q hq') (ih (by omega))
theorem N_mono {j : ℕ} (hj : j ≤ R.m) : R.N j ≤ R.N R.m := by
  unfold Ranks.N
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hj) _
theorem wtQ_anti (j : ℕ) (hj : j ≤ R.m) : Antitone (wtQ P j hj) := by
  intro a b hab
  rw [wtQ_eq_wtN, wtQ_eq_wtN]
  exact wtN_anti P hab (lt_of_lt_of_le b.2 (N_mono hj))
theorem wtQ_int (j : ℕ) (hj : j ≤ R.m) (i : Fin (R.N j)) : ∃ z : ℤ, wtQ P j hj i = z := by
  obtain ⟨a, ha⟩ := R.k_even
  obtain ⟨c, hc⟩ := R.t_odd
  have hk : (R.k : ℚ) = a + a := by exact_mod_cast ha
  have ht : (R.t : ℚ) = 2 * c + 1 := by exact_mod_cast hc
  by_cases h : i.1 < R.k
  · obtain ⟨z, hz⟩ := P.u_half ⟨i.1, h⟩
    refine ⟨z + 1 - a + i.1, ?_⟩
    rw [wtQ, dif_pos h]
    simp only [hcToWeightQ, rhoVec, Fin.val_mk, hz]
    rw [hk]
    push_cast
    ring
  · obtain ⟨z, hz⟩ := P.e_int ⟨(i.1 - R.k) / (R.t + 1), R.blk_lt hj i h⟩
    refine ⟨-z + a + (2 * (((i.1 - R.k) / (R.t + 1) : ℕ) : ℤ) + 1) * (c + 1), ?_⟩
    rw [wtQ, dif_neg h]
    simp only [wG, hz]
    generalize (i.1 - R.k) / (R.t + 1) = B
    rw [hk, ht]
    push_cast
    ring
def lamOf (j : ℕ) : DomWeight (R.N j) :=
  if hj : j ≤ R.m then ⟨fun i => ⌊wtQ P j hj i⌋, fun _ _ hii => Int.floor_mono (wtQ_anti P j hj hii)⟩
  else ⟨fun _ => 0, fun _ _ _ => le_rfl⟩
theorem lamOf_eq (j : ℕ) (hj : j ≤ R.m) (i : Fin (R.N j)) : ((lamOf P j).w i : ℚ) = wtQ P j hj i := by
  obtain ⟨z, hz⟩ := wtQ_int P j hj i
  simp only [lamOf, dif_pos hj, hz, Int.floor_intCast]
end Weights
def fmZeroHLat (K : Type) [Field K] [NumberField K] [StarRing K] : HLat K where
  V := Fin 0 → K
  ι := Fin 0
  b := Pi.basisFun K (Fin 0)
  X := fun _ => 0
  L := ⊤
instance fmZeroHLat_sub (K : Type) [Field K] [NumberField K] [StarRing K] :
    Subsingleton (fmZeroHLat K).V := inferInstanceAs (Subsingleton (Fin 0 → K))
instance fmZeroHLat_empty (K : Type) [Field K] [NumberField K] [StarRing K] :
    IsEmpty (fmZeroHLat K).ι := inferInstanceAs (IsEmpty (Fin 0))
theorem fmZeroHLat_good (K : Type) [Field K] [NumberField K] [StarRing K] : (fmZeroHLat K).Good := by
  unfold HLat.Good
  refine ⟨fun v => ?_, ?_, Subsingleton.elim _ _⟩
  · rw [Matrix.det_isEmpty]
    exact isUnit_one
  · rw [Subsingleton.elim (fmZeroHLat K).L ⊥]
    exact Submodule.fg_bot
theorem fmZeroHLat_maj (K : Type) [Field K] [NumberField K] [StarRing K] (v : InfinitePlace K)
    (x y : (fmZeroHLat K).V) :
    Formalism.HermitianLatticesTheory.majAt (fmZeroHLat K).b (fmZeroHLat K).X v x y = 0 := by
  unfold Formalism.HermitianLatticesTheory.majAt
  exact Fintype.sum_empty _
section Forms
variable {R : Ranks} {LL : Type} [Field LL] [NumberField LL] [StarRing LL] (embLL : LL →+* ℂ)
  (Pl : Rows.Places LL) {Tau : Type} [Fintype Tau] (hTau : Fintype.card Tau = R.f)
  {hc : Tau → HCParam R} (C : ColumnChain R Tau hc) [hE : ∀ i, IsEmpty (C.cls i)]
  (A : ColumnsAtT R C) (P : PeriodMap R C)
def formsToy : MemberForms LL embLL Pl Tau hc C A P where
  lv := fun i v _ => Fin (R.N i) → A.Fv v
  lv_rank := fun i v _ => Module.finrank_fin_fun (A.Fv v)
  fv := fun i v _ => LinearMap.proj ⟨0, R.N_pos i⟩
  fv_ne := fun _ _ c => isEmptyElim c
  up := fun _ _ c _ => c
  upT := fun _ _ _ _ => LinearEquiv.refl ℂ _
  lk := fun i v _ => Fin (R.N i) → A.Fv v
  lk_rank := fun i v _ => Module.finrank_fin_fun (A.Fv v)
  te := fun i v _ => Pi.single ⟨0, R.N_pos i⟩ 1
  te_ne := fun _ _ c => isEmptyElim c
  dn := fun _ _ c _ => c
  dnT := fun _ _ _ _ => LinearEquiv.refl ℂ _
  dil := fun _ _ _ c => c
  dilT := fun _ _ _ _ => LinearEquiv.refl ℂ _
  dil_one := fun _ _ _ => rfl
  dil_mul := fun _ _ _ _ _ => rfl
  dil_fv := fun _ _ _ c => isEmptyElim c
  dil_stab := fun _ _ _ _ => rfl
  rhoT_dil := fun _ _ _ c => isEmptyElim c
  tauOf := fun _ => Fintype.equivOfCardEq (by rw [A.card_vT, hTau])
  seenP := fun _ => true
  lam := fun j τ => lamOf (hc τ) j
  lam_eq := fun j hj τ i => lamOf_eq (hc τ) j hj i
  sg := fun _ => ⟨fun _ => 0, fun _ _ _ => le_rfl⟩
  Fi := fun _ => ⊥
  Fi_zero := Subsingleton.elim _ _
  ipV := fun _ _ => 0
  lat := fun _ => fmZeroHLat LL
  lat_good := fun _ => fmZeroHLat_good LL
  emb := fun _ => 0
  emb_basis := fun _ => ⟨linearIndependent_empty_type, by
    rw [Set.range_eq_empty, Submodule.span_empty]⟩
  emb_norm := fun i x => by
    rw [fmZeroHLat_maj]
    simp
  rhoT_lat := fun _ _ _ _ => ⟨0, Submodule.zero_mem _, Subsingleton.elim _ _⟩
  Bw := fun _ _ _ => ⊤
  Bw_span := fun _ _ _ => Subsingleton.elim _ _
  clsP := Empty
  stabilizer₂ := fun _ => Unit
  til := fun c => c.elim
  stabMap := fun c => c.elim
  stabMap_inj := fun c => c.elim
  evz_til := fun φ ψ _ => by rw [Subsingleton.elim φ ψ]
  ptC := ⊥
  ipP := 0
  ptLat := fmZeroHLat LL
  ptLat_good := fmZeroHLat_good LL
  ptEmb := 0
  ptEmb_basis := ⟨linearIndependent_empty_type, by rw [Set.range_eq_empty, Submodule.span_empty]⟩
  ptEmb_norm := fun x => by
    rw [fmZeroHLat_maj]
    simp
  beOn := fun _ => 0
  beOn_nonneg := fun _ => le_rfl
  thFree := fun _ _ _ _ => 0
  thFree_nonneg := fun _ _ _ _ => le_rfl
end Forms
def gxExample (LL : Type) [Field LL] [NumberField LL] (Tau : Type) : GlobalExtra LL Tau :=
  ⟨fun _ _ => 1, fun _ _ => one_pos, fun _ => 1, fun _ => one_pos⟩
end Formalism.BasicNotions.Examples₂


