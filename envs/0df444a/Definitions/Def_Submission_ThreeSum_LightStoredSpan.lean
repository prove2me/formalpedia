-- Prove2me | Definitions.Def_Submission_ThreeSum_LightStoredSpan
-- name    : Submission_ThreeSum_LightStoredSpan
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T10:11:27.183094+00:00
-- url     : https://prove2.me/theorems/37d0bfcc-34b4-41bd-a519-ae2aefa16f85
-- title:
--   Light Stored Span
-- statement:
--   Definitions and structural lemmas for Light Stored Span, from the weighted-cache deterministic 3SUM development.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightStoredSpan.lean

import Definitions.Def_Submission_ThreeSum_TernaryStoredSpan
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Copy
import Theorems.Thm_Light_Ends_mono
import Theorems.Thm_Light_Ends_next
import Theorems.Thm_Light_Meets_mono
import Theorems.Thm_Light_SameOn_mono
import Theorems.Thm_Light_SameOutside_mono
import Theorems.Thm_Light_fill_meets
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab
import Theorems.Thm_ThreeSum_LightSpanAxpy_meets
import Theorems.Thm_ThreeSum_LightSpanCatalogBlock_meets
import Theorems.Thm_ThreeSum_LightSpanCatalogStep_meets
import Theorems.Thm_ThreeSum_LightSpanCatalogTest_meets
import Theorems.Thm_ThreeSum_LightSpanRowEqual_meets
import Theorems.Thm_ThreeSum_LightTernaryPass_meets
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryBank_mem_lowerWords
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
import Theorems.Thm_ThreeSum_TernaryStoredSpan_present_iff
import Theorems.Thm_ThreeSum_TernaryStoredSpan_read_next
import Theorems.Thm_ThreeSum_TernaryStoredSpan_represents_next
import Theorems.Thm_ThreeSum_TernaryStoredSpan_represents_zero
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
attribute [local simp] ThreeSum.TernaryBank.mem_bank
attribute [local simp] ThreeSum.TernaryBank.mem_lowerWords
attribute [local simp] ThreeSum.TernaryBank.mem_nearWords


set_option autoImplicit false
noncomputable section
namespace ThreeSum.LightStoredSpan
open Light ThreeSum.TernaryStoredSpan
set_option maxHeartbeats 5000000
set_option maxRecDepth 12000
attribute [local instance] Classical.propDecidable
variable {lim : Limits} {P : Program} {p J : ℕ} [Fact p.Prime]
def rowValues (row : Fin J → ZMod p) (i : ℕ) : ℕ := if hi : i<J then (row ⟨i,hi⟩).val else 0
def admissibleFlag (rows : List (Fin J → ZMod p)) (row : Fin J → ZMod p) : ℕ :=
  if row∈Submodule.span (ZMod p) {v | v∈rows} then 0 else 1
@[simp] theorem admissibleFlag_eq_one (rows : List (Fin J → ZMod p)) (row : Fin J → ZMod p) :
    admissibleFlag rows row=1 ↔ row∉Submodule.span (ZMod p) {v | v∈rows} := by
  by_cases h : row∈Submodule.span (ZMod p) {v | v∈rows} <;> simp [admissibleFlag,h]
theorem init_meets {pFill catalog d : ℕ} (hfill : P[pFill]?=some fillBody)
    (μ : ℕ → ℤ) (hw : (lim.space : ℤ)≤lim.word) (hspace : catalog+J≤lim.space) :
    Meets lim P pFill d [catalog,J,0] μ (fillTime J)
      (fun _ ν => (∀ i<J, ν (catalog+i)=0) ∧
        Represents (p := p) (J := J) (fun _ _ => 0) 1 [] ∧ SameOutside μ ν catalog J) := by
  have hc := fill_meets (d := d) (x := (0 : ℤ)) hfill (μ := μ) hw hspace
  exact hc.mono le_rfl (fun _ ν h => ⟨by intro i hi; exact (h.1 i (by simpa using hi)).trans (List.getElem_replicate _),represents_zero,h.2⟩)
theorem step_meets {pMain pBlock pAxpy pMulAdd pDivide src n rowBase dst d : ℕ}
    (hmain : P[pMain]?=some (LightSpanCatalogStep.body pBlock))
    (hblock : P[pBlock]?=some (LightSpanCatalogBlock.body pAxpy))
    (haxpy : P[pAxpy]?=some (LightSpanAxpy.body pMulAdd))
    (hmul : P[pMulAdd]?=some (LightPrimeCoefficient.mulAddBody pDivide))
    (hdivide : P[pDivide]?=some LightSmallDivide.body)
    (μ : ℕ → ℤ) (f : ℕ → ℕ → ℕ) (row : Fin J → ZMod p) (rows : List (Fin J → ZMod p))
    (H : Represents f n rows) (hn : 0<n)
    (hw : (lim.space : ℤ)≤lim.word) (hsrc : src+J*n≤dst) (hrow : rowBase+J≤dst)
    (hdst : dst+J*n*p≤lim.space)
    (hword : (LightPrimeCoefficient.word p : ℤ)≤lim.word)
    (hcontrols : ((n+J+16 : ℕ) : ℤ)≤lim.word)
    (hf : ∀ k<n, ∀ i<J, f k i<p)
    (hread : ∀ k<n, ∀ i<J, μ (src+J*k+i)=(f k i : ℤ))
    (hreadRow : ∀ i<J, μ (rowBase+i)=((rowValues row i : ℕ) : ℤ))
    (hd : d+4≤lim.depth) :
    Meets lim P pMain d [src,n,rowBase,dst,J,p] μ (LightSpanCatalogStep.time J p n)
      (fun _ ν => (∀ q<p*n, ∀ i<J, ν (dst+J*q+i)=(next f (rowValues row) p n q i : ℤ)) ∧
        Represents (next f (rowValues row) p n) (p*n) (row::rows) ∧
        (∀ q<p*n, ∀ i<J, next f (rowValues row) p n q i<p) ∧ SameOutside μ ν dst (J*n*p)) := by
  have hp : 0<p := (Fact.out : p.Prime).pos
  have hr : ∀ i<J, rowValues row i<p := by
    intro i hi
    simpa only [rowValues,dif_pos hi] using ZMod.val_lt (row ⟨i,hi⟩)
  have hc := LightSpanCatalogStep.meets hmain hblock haxpy hmul hdivide μ f (rowValues row)
    hw hsrc hrow hdst hp hword hcontrols hf hr hread hreadRow hd
  exact hc.mono le_rfl (fun _ ν h => ⟨read_next f (rowValues row) hn h.1,
    represents_next f row rows hn H,fun q _ i _ => Nat.mod_lt _ hp,h.2⟩)
theorem admissible_meets {pMain pEq catalog n candidate d : ℕ}
    (hmain : P[pMain]?=some (LightSpanCatalogTest.body pEq)) (heq : P[pEq]?=some LightSpanRowEqual.body)
    (μ : ℕ → ℤ) (f : ℕ → ℕ → ℕ) (row : Fin J → ZMod p) (rows : List (Fin J → ZMod p))
    (H : Represents f n rows)
    (hw : (lim.space : ℤ)≤lim.word) (hcat : catalog+J*n≤lim.space) (hrow : candidate+J≤lim.space)
    (hcontrols : ((n+J+16 : ℕ) : ℤ)≤lim.word) (hpp : (p : ℤ)≤lim.word)
    (hf : ∀ k<n, ∀ i<J, f k i<p)
    (hread : ∀ k<n, ∀ i<J, μ (catalog+J*k+i)=(f k i : ℤ))
    (hreadRow : ∀ i<J, μ (candidate+i)=(rowValues row i : ℤ)) (hd : d+1≤lim.depth) :
    Meets lim P pMain d [catalog,n,J,candidate] μ (LightSpanCatalogTest.time J n)
      (fun r ν => r=(admissibleFlag rows row : ℤ) ∧ ν=μ) := by
  have hp : 0<p := (Fact.out : p.Prime).pos
  have hone : (1 : ℤ)≤lim.word := (Int.ofNat_le.mpr (show 1≤p by omega)).trans hpp
  have hF : ∀ k<n, ∀ i<J, |(f k i : ℤ)|≤lim.word := by
    intro k hk i hi
    rw [abs_of_nonneg (by positivity)]
    exact (Int.ofNat_le.mpr (Nat.le_of_lt (hf k hk i hi))).trans hpp
  have hR : ∀ i<J, |(rowValues row i : ℤ)|≤lim.word := by
    intro i hi
    rw [abs_of_nonneg (by positivity)]
    have hh : rowValues row i<p := by simpa only [rowValues,dif_pos hi] using ZMod.val_lt (row ⟨i,hi⟩)
    exact (Int.ofNat_le.mpr (Nat.le_of_lt hh)).trans hpp
  have hc := LightSpanCatalogTest.meets hmain heq μ (fun k i => (f k i : ℤ)) (fun i => (rowValues row i : ℤ))
    hw hcat hrow hone hcontrols hF hR hread hreadRow hd
  have hFlag : LightSpanCatalogTest.flag (fun k i => (f k i : ℤ)) (fun i => (rowValues row i : ℤ)) J n=
      admissibleFlag rows row := by
    unfold LightSpanCatalogTest.flag admissibleFlag
    have hpresent := present_iff f n rows row H hf
    have hrowfn : (fun i => (rowValues row i : ℤ))=
        (fun i => if hi : i<J then ((row ⟨i,hi⟩).val : ℤ) else 0) := by
      funext i
      by_cases hi : i<J <;> simp [rowValues,hi]
    rw [hrowfn,hpresent]

  exact hc.mono le_rfl (fun r ν h => ⟨by simpa only [hFlag] using h.1,h.2⟩)
def program : Program := [fillBody,LightSpanCatalogStep.body 2,LightSpanCatalogBlock.body 3,
  LightSpanAxpy.body 4,LightPrimeCoefficient.mulAddBody 5,LightSmallDivide.body,
  LightSpanCatalogTest.body 7,LightSpanRowEqual.body]
def program_init_meets {catalog d : ℕ} :=
  init_meets (lim := lim) (P := program) (p := p) (J := J) (catalog := catalog) (d := d) (pFill := 0) rfl
def program_step_meets {src n rowBase dst d : ℕ} :=
  step_meets (lim := lim) (P := program) (p := p) (J := J) (src := src) (n := n)
    (rowBase := rowBase) (dst := dst) (d := d) (pMain := 1) (pBlock := 2) (pAxpy := 3)
    (pMulAdd := 4) (pDivide := 5) rfl rfl rfl rfl rfl
def program_admissible_meets {catalog n candidate d : ℕ} :=
  admissible_meets (lim := lim) (P := program) (p := p) (J := J) (catalog := catalog) (n := n)
    (candidate := candidate) (d := d) (pMain := 6) (pEq := 7) rfl rfl
end ThreeSum.LightStoredSpan


