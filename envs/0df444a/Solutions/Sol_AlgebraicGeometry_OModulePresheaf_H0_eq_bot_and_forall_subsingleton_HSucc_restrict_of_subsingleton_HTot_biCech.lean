-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.H0_eq_bot_and_forall_subsingleton_HSucc_restrict_of_subsingleton_HTot_biCech
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/6fa033b6-9a3c-5196-ad96-7325cf22512c

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_DoubleComplex
import Definitions.Def_AlgebraicGeometry_BiCech
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_d_comp_d
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_H0_eq_bot_and_forall_subsingleton_HSucc_restrict_of_subsingleton_HTot_biCech

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

namespace K3Sol

p2m_open "AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.OModulePresheaf"

variable {X : Scheme.{u}} {U V : X.Opens}
variable (𝔙 : (V : Scheme.{u}).OrderedAffineCover) (𝔘 : (U : Scheme.{u}).OrderedAffineCover)
variable (𝔛' : X.OrderedAffineCover) (eV : 𝔙.ι ↪o 𝔛'.ι) (eU : 𝔘.ι ↪o 𝔛'.ι)

def pureV {p : ℕ} (s : 𝔙.Idx p) : 𝔛'.Idx p := ⟨eV ∘ s.1, eV.strictMono.comp s.2⟩

def pureU {q : ℕ} (t : 𝔘.Idx q) : 𝔛'.Idx q := ⟨eU ∘ t.1, eU.strictMono.comp t.2⟩

theorem pureV_val {p : ℕ} (s : 𝔙.Idx p) (j : Fin (p + 1)) : (pureV 𝔙 𝔛' eV s).1 j = eV (s.1 j) := rfl
theorem pureU_val {q : ℕ} (t : 𝔘.Idx q) (j : Fin (q + 1)) : (pureU 𝔘 𝔛' eU t).1 j = eU (t.1 j) := rfl

theorem face_pureV {p : ℕ} (s : 𝔙.Idx (p + 1)) (j : Fin (p + 2)) :
    𝔛'.face (pureV 𝔙 𝔛' eV s) j = pureV 𝔙 𝔛' eV (𝔙.face s j) := rfl

theorem face_pureU {q : ℕ} (t : 𝔘.Idx (q + 1)) (j : Fin (q + 2)) :
    𝔛'.face (pureU 𝔘 𝔛' eU t) j = pureU 𝔘 𝔛' eU (𝔘.face t j) := rfl

theorem pureV_injective {p : ℕ} : Function.Injective (pureV 𝔙 𝔛' eV (p := p)) := by
  intro s s' h
  apply Subtype.ext
  funext j
  exact eV.injective (congrFun (congrArg Subtype.val h) j)

theorem pureU_injective {q : ℕ} : Function.Injective (pureU 𝔘 𝔛' eU (q := q)) := by
  intro t t' h
  apply Subtype.ext
  funext j
  exact eU.injective (congrFun (congrArg Subtype.val h) j)

def mixFun {p q n : ℕ} (h : p + q + 1 = n) (s : 𝔙.Idx p) (t : 𝔘.Idx q) (j : Fin (n + 1)) : 𝔛'.ι :=
  if hj : (j : ℕ) < p + 1 then eV (s.1 ⟨j, hj⟩) else eU (t.1 ⟨(j : ℕ) - (p + 1), by omega⟩)

variable (hlt : ∀ b a, eV b < eU a)
include hlt

theorem mixFun_strictMono {p q n : ℕ} (h : p + q + 1 = n) (s : 𝔙.Idx p) (t : 𝔘.Idx q) :
    StrictMono (mixFun 𝔙 𝔘 𝔛' eV eU h s t) := by
  intro a b hab
  have hab' : (a : ℕ) < (b : ℕ) := hab
  simp only [mixFun]
  split_ifs with ha hb hb
  · exact eV.strictMono (s.2 (Fin.mk_lt_mk.mpr hab'))
  · exact hlt _ _
  · omega
  · exact eU.strictMono (t.2 (Fin.mk_lt_mk.mpr (by omega)))

def mix {p q n : ℕ} (h : p + q + 1 = n) (s : 𝔙.Idx p) (t : 𝔘.Idx q) : 𝔛'.Idx n :=
  ⟨mixFun 𝔙 𝔘 𝔛' eV eU h s t, mixFun_strictMono 𝔙 𝔘 𝔛' eV eU hlt h s t⟩

theorem mix_val_left {p q n : ℕ} (h : p + q + 1 = n) (s : 𝔙.Idx p) (t : 𝔘.Idx q) (j : Fin (n + 1))
    (hj : (j : ℕ) < p + 1) : (mix 𝔙 𝔘 𝔛' eV eU hlt h s t).1 j = eV (s.1 ⟨j, hj⟩) := by
  simp [mix, mixFun, hj]

theorem mix_val_right {p q n : ℕ} (h : p + q + 1 = n) (s : 𝔙.Idx p) (t : 𝔘.Idx q) (j : Fin (n + 1))
    (hj : ¬ (j : ℕ) < p + 1) :
    (mix 𝔙 𝔘 𝔛' eV eU hlt h s t).1 j = eU (t.1 ⟨(j : ℕ) - (p + 1), by omega⟩) := by
  simp [mix, mixFun, hj]

omit hlt in
theorem val_succAbove {n : ℕ} (j : Fin (n + 1)) (k : Fin n) :
    ((j.succAbove k : Fin (n + 1)) : ℕ) = if (k : ℕ) < (j : ℕ) then (k : ℕ) else (k : ℕ) + 1 := by
  unfold Fin.succAbove
  split_ifs with h1 h2 h2 <;> simp_all [Fin.lt_def]

theorem mix_val {p q n : ℕ} (h : p + q + 1 = n) (s : 𝔙.Idx p) (t : 𝔘.Idx q) (j : Fin (n + 1)) :
    (mix 𝔙 𝔘 𝔛' eV eU hlt h s t).1 j =
      if hj : (j : ℕ) < p + 1 then eV (s.1 ⟨j, hj⟩) else eU (t.1 ⟨(j : ℕ) - (p + 1), by omega⟩) := rfl

omit hlt in

theorem mixFun_congr {p q : ℕ} (s : 𝔙.Idx p) (t : 𝔘.Idx q) {a b : ℕ} (hab : a = b)
    (ha : ¬ a < p + 1 → a - (p + 1) < q + 1) (hb : ¬ b < p + 1 → b - (p + 1) < q + 1) :
    (if h : a < p + 1 then eV (s.1 ⟨a, h⟩) else eU (t.1 ⟨a - (p + 1), ha h⟩)) =
      (if h : b < p + 1 then eV (s.1 ⟨b, h⟩) else eU (t.1 ⟨b - (p + 1), hb h⟩)) := by
  subst hab; rfl

theorem face_mix_left {p q n : ℕ} (hn : p + q + 1 = n) (s : 𝔙.Idx (p + 1)) (t : 𝔘.Idx q)
    (j : Fin (p + 2)) :
    𝔛'.face (mix 𝔙 𝔘 𝔛' eV eU hlt (p := p + 1) (q := q) (n := n + 1) (by omega) s t) ⟨j, by omega⟩
      = mix 𝔙 𝔘 𝔛' eV eU hlt hn (𝔙.face s j) t := by
  apply Subtype.ext
  funext k
  simp only [Scheme.OrderedAffineCover.face_val, Function.comp_apply, mix_val]
  have hv : ((Fin.succAbove (⟨j, by omega⟩ : Fin (n + 2)) k : Fin (n + 2)) : ℕ)
      = if (k : ℕ) < (j : ℕ) then (k : ℕ) else (k : ℕ) + 1 := val_succAbove _ _
  by_cases hk : (k : ℕ) < p + 1
  · have hk' : ((Fin.succAbove (⟨j, by omega⟩ : Fin (n + 2)) k : Fin (n + 2)) : ℕ) < p + 1 + 1 := by
      rw [hv]; split_ifs <;> omega
    rw [dif_pos hk', dif_pos hk]
    exact congrArg eV (congrArg s.1 (Fin.ext (by simp only [hv, val_succAbove])))
  · have hk' : ¬ ((Fin.succAbove (⟨j, by omega⟩ : Fin (n + 2)) k : Fin (n + 2)) : ℕ) < p + 1 + 1 := by
      rw [hv]; split_ifs <;> omega
    rw [dif_neg hk', dif_neg hk]
    exact congrArg eU (congrArg t.1 (Fin.ext (by simp only [hv]; split_ifs <;> omega)))

theorem face_mix_right {p q n : ℕ} (hn : p + q + 1 = n) (s : 𝔙.Idx p) (t : 𝔘.Idx (q + 1))
    (k : Fin (q + 2)) :
    𝔛'.face (mix 𝔙 𝔘 𝔛' eV eU hlt (p := p) (q := q + 1) (n := n + 1) (by omega) s t) ⟨p + 1 + k, by omega⟩
      = mix 𝔙 𝔘 𝔛' eV eU hlt hn s (𝔘.face t k) := by
  apply Subtype.ext
  funext l
  simp only [Scheme.OrderedAffineCover.face_val, Function.comp_apply, mix_val]
  have hv : ((Fin.succAbove (⟨p + 1 + k, by omega⟩ : Fin (n + 2)) l : Fin (n + 2)) : ℕ)
      = if (l : ℕ) < p + 1 + (k : ℕ) then (l : ℕ) else (l : ℕ) + 1 := val_succAbove _ _
  by_cases hl : (l : ℕ) < p + 1
  · have hl' : ((Fin.succAbove (⟨p + 1 + k, by omega⟩ : Fin (n + 2)) l : Fin (n + 2)) : ℕ) < p + 1 := by
      rw [hv]; split_ifs <;> omega
    rw [dif_pos hl', dif_pos hl]
    exact congrArg eV (congrArg s.1 (Fin.ext (by simp only [hv]; split_ifs <;> omega)))
  · have hl' : ¬ ((Fin.succAbove (⟨p + 1 + k, by omega⟩ : Fin (n + 2)) l : Fin (n + 2)) : ℕ) < p + 1 := by
      rw [hv]; split_ifs <;> omega
    rw [dif_neg hl', dif_neg hl]
    exact congrArg eU (congrArg t.1 (Fin.ext (by simp only [hv, val_succAbove]; split_ifs <;> omega)))

theorem face_mix_zero {q : ℕ} (s : 𝔙.Idx 0) (t : 𝔘.Idx q) :
    𝔛'.face (mix 𝔙 𝔘 𝔛' eV eU hlt (p := 0) (q := q) (n := q + 1) (by omega) s t) 0 = pureU 𝔘 𝔛' eU t := by
  apply Subtype.ext
  funext l
  simp only [Scheme.OrderedAffineCover.face_val, Function.comp_apply, mix_val, pureU_val, Fin.succAbove_zero]
  rw [dif_neg (by simp)]
  exact congrArg eU (congrArg t.1 (Fin.ext (by simp)))

theorem face_mix_last {p : ℕ} (s : 𝔙.Idx p) (t : 𝔘.Idx 0) :
    𝔛'.face (mix 𝔙 𝔘 𝔛' eV eU hlt (p := p) (q := 0) (n := p + 1) (by omega) s t) (Fin.last (p + 1))
      = pureV 𝔙 𝔛' eV s := by
  apply Subtype.ext
  funext l
  simp only [Scheme.OrderedAffineCover.face_val, Function.comp_apply, mix_val, pureV_val, Fin.succAbove_last]
  rw [dif_pos (by simp [l.isLt])]
  exact congrArg eV (congrArg s.1 (Fin.ext (by simp)))

theorem eV_ne_eU (b : 𝔙.ι) (a : 𝔘.ι) : eV b ≠ eU a := (hlt b a).ne

theorem pureV_ne_mix {p q n : ℕ} (h : p + q + 1 = n) (s₀ : 𝔙.Idx n) (s : 𝔙.Idx p) (t : 𝔘.Idx q) :
    pureV 𝔙 𝔛' eV s₀ ≠ mix 𝔙 𝔘 𝔛' eV eU hlt h s t := by
  intro e
  have := congrFun (congrArg Subtype.val e) ⟨p + 1, by omega⟩
  rw [pureV_val, mix_val, dif_neg (by simp)] at this
  exact eV_ne_eU 𝔙 𝔘 𝔛' eV eU hlt _ _ this

theorem pureU_ne_mix {p q n : ℕ} (h : p + q + 1 = n) (t₀ : 𝔘.Idx n) (s : 𝔙.Idx p) (t : 𝔘.Idx q) :
    pureU 𝔘 𝔛' eU t₀ ≠ mix 𝔙 𝔘 𝔛' eV eU hlt h s t := by
  intro e
  have := congrFun (congrArg Subtype.val e) ⟨0, by omega⟩
  rw [pureU_val, mix_val, dif_pos (by simp)] at this
  exact eV_ne_eU 𝔙 𝔘 𝔛' eV eU hlt _ _ this.symm

theorem pureV_ne_pureU {n : ℕ} (s : 𝔙.Idx n) (t : 𝔘.Idx n) : pureV 𝔙 𝔛' eV s ≠ pureU 𝔘 𝔛' eU t := by
  intro e
  exact eV_ne_eU 𝔙 𝔘 𝔛' eV eU hlt _ _ (congrFun (congrArg Subtype.val e) 0)

theorem mix_eq_mix_fst {p q p' q' n : ℕ} (h : p + q + 1 = n) (h' : p' + q' + 1 = n)
    (s : 𝔙.Idx p) (t : 𝔘.Idx q) (s' : 𝔙.Idx p') (t' : 𝔘.Idx q')
    (e : mix 𝔙 𝔘 𝔛' eV eU hlt h s t = mix 𝔙 𝔘 𝔛' eV eU hlt h' s' t') : p = p' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt' | hgt
  · have := congrFun (congrArg Subtype.val e) ⟨p + 1, by omega⟩
    rw [mix_val, mix_val, dif_neg (by simp), dif_pos (by simp; omega)] at this
    exact eV_ne_eU 𝔙 𝔘 𝔛' eV eU hlt _ _ this.symm
  · have := congrFun (congrArg Subtype.val e) ⟨p' + 1, by omega⟩
    rw [mix_val, mix_val, dif_pos (by simp; omega), dif_neg (by simp)] at this
    exact eV_ne_eU 𝔙 𝔘 𝔛' eV eU hlt _ _ this

theorem mix_injective {p q n : ℕ} (h : p + q + 1 = n)
    (s s' : 𝔙.Idx p) (t t' : 𝔘.Idx q)
    (e : mix 𝔙 𝔘 𝔛' eV eU hlt h s t = mix 𝔙 𝔘 𝔛' eV eU hlt h s' t') : s = s' ∧ t = t' := by
  have ev := fun j => congrFun (congrArg Subtype.val e) j
  refine ⟨Subtype.ext (funext fun j => ?_), Subtype.ext (funext fun j => ?_)⟩
  · have := ev ⟨j, by omega⟩
    rw [mix_val, mix_val, dif_pos (by simp <;> omega),
      dif_pos (by simp <;> omega)] at this
    have := eV.injective this
    rwa [show (⟨((⟨j, by omega⟩ : Fin (n + 1)) : ℕ), _⟩ : Fin (p + 1)) = j from Fin.ext rfl] at this
  · have := ev ⟨p + 1 + j, by omega⟩
    rw [mix_val, mix_val, dif_neg (by simp <;> omega),
      dif_neg (by simp <;> omega)] at this
    have := eU.injective this
    rwa [show (⟨((⟨p + 1 + j, by omega⟩ : Fin (n + 1)) : ℕ) - (p + 1), _⟩ : Fin (q + 1)) = j from
      Fin.ext (by simp)] at this

omit hlt in
theorem strictMono_snoc {m : ℕ} {ι : Type u} [Preorder ι] (f : Fin (m + 1) → ι) (hf : StrictMono f) (b : ι)
    (hb : f (Fin.last m) < b) : StrictMono (Fin.snoc f b : Fin (m + 2) → ι) := by
  intro i j hij
  by_cases hj : j = Fin.last (m + 1)
  · subst hj
    have hi : i ≠ Fin.last (m + 1) := hij.ne
    obtain ⟨i', rfl⟩ := Fin.exists_castSucc_eq.mpr hi
    rw [Fin.snoc_castSucc, Fin.snoc_last]
    exact (hf.monotone (Fin.le_last i')).trans_lt hb
  · obtain ⟨j', rfl⟩ := Fin.exists_castSucc_eq.mpr hj
    have hi : i ≠ Fin.last (m + 1) := (hij.trans (Fin.castSucc_lt_last j')).ne
    obtain ⟨i', rfl⟩ := Fin.exists_castSucc_eq.mpr hi
    rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
    exact hf (Fin.castSucc_lt_castSucc_iff.mp hij)

omit hlt in

def snocV {p : ℕ} (s : 𝔙.Idx p) (b : 𝔙.ι) (hb : s.1 (Fin.last p) < b) : 𝔙.Idx (p + 1) :=
  ⟨Fin.snoc s.1 b, strictMono_snoc s.1 s.2 b hb⟩

omit hlt in
theorem snocV_last {p : ℕ} (s : 𝔙.Idx p) (b : 𝔙.ι) (hb : s.1 (Fin.last p) < b) :
    (snocV 𝔙 s b hb).1 (Fin.last (p + 1)) = b := by
  simp [snocV]

omit hlt in
theorem snocV_castSucc {p : ℕ} (s : 𝔙.Idx p) (b : 𝔙.ι) (hb : s.1 (Fin.last p) < b) (k : Fin (p + 1)) :
    (snocV 𝔙 s b hb).1 k.castSucc = s.1 k := by
  simp [snocV]

omit hlt in

def snocU {q : ℕ} (t : 𝔘.Idx q) (a : 𝔘.ι) (ha : t.1 (Fin.last q) < a) : 𝔘.Idx (q + 1) :=
  ⟨Fin.snoc t.1 a, strictMono_snoc t.1 t.2 a ha⟩

omit hlt in
theorem snocU_last {q : ℕ} (t : 𝔘.Idx q) (a : 𝔘.ι) (ha : t.1 (Fin.last q) < a) :
    (snocU 𝔘 t a ha).1 (Fin.last (q + 1)) = a := by
  simp [snocU]

omit hlt in
theorem snocU_castSucc {q : ℕ} (t : 𝔘.Idx q) (a : 𝔘.ι) (ha : t.1 (Fin.last q) < a) (k : Fin (q + 1)) :
    (snocU 𝔘 t a ha).1 k.castSucc = t.1 k := by
  simp [snocU]

omit hlt in

def single {W : Scheme.{u}} (K : W.OrderedAffineCover) (i : K.ι) : K.Idx 0 :=
  ⟨fun _ => i, fun a b hab => absurd hab (by rw [Fin.lt_def]; omega)⟩

omit hlt in
theorem val_castSucc_eq {m : ℕ} (σ : 𝔛'.Idx (m + 1)) (k : Fin (m + 1)) :
    σ.1 k.castSucc = (𝔛'.face σ (Fin.last (m + 1))).1 k := by
  rw [Scheme.OrderedAffineCover.face_val, Function.comp_apply, Fin.succAbove_last]

theorem trichotomy (hcov : ∀ j, j ∈ Set.range eV ∨ j ∈ Set.range eU) :
    ∀ (n : ℕ) (σ : 𝔛'.Idx n),
      (∃ s, σ = pureV 𝔙 𝔛' eV s) ∨ (∃ t, σ = pureU 𝔘 𝔛' eU t) ∨
        ∃ (p q : ℕ) (h : p + q + 1 = n) (s : 𝔙.Idx p) (t : 𝔘.Idx q), σ = mix 𝔙 𝔘 𝔛' eV eU hlt h s t := by
  intro n
  induction n with
  | zero =>
    intro σ
    rcases hcov (σ.1 0) with ⟨b, hb⟩ | ⟨a, ha⟩
    · refine Or.inl ⟨single 𝔙 b, Subtype.ext (funext fun k => ?_)⟩
      rw [Fin.fin_one_eq_zero k, pureV_val]; exact hb.symm
    · refine Or.inr (Or.inl ⟨single 𝔘 a, Subtype.ext (funext fun k => ?_)⟩)
      rw [Fin.fin_one_eq_zero k, pureU_val]; exact ha.symm
  | succ m ih =>
    intro σ
    set σ' := 𝔛'.face σ (Fin.last (m + 1)) with hσ'
    have hlast : σ'.1 (Fin.last m) < σ.1 (Fin.last (m + 1)) := by
      rw [hσ', ← val_castSucc_eq]
      exact σ.2 (Fin.castSucc_lt_last _)

    have hbelow : ∀ k : Fin (m + 1), σ.1 k.castSucc = σ'.1 k := fun k => val_castSucc_eq 𝔛' σ k
    rcases ih σ' with ⟨s, hs⟩ | ⟨t, ht⟩ | ⟨p, q, h, s, t, hst⟩
    · rcases hcov (σ.1 (Fin.last (m + 1))) with ⟨b, hb⟩ | ⟨a, ha⟩
      ·
        have hb' : s.1 (Fin.last m) < b := by
          apply eV.lt_iff_lt.mp
          rw [hb, ← pureV_val 𝔙 𝔛' eV s, ← hs]; exact hlast
        refine Or.inl ⟨snocV 𝔙 s b hb', Subtype.ext (funext fun k => ?_)⟩
        rw [pureV_val]
        by_cases hk : k = Fin.last (m + 1)
        · subst hk; rw [snocV_last]; exact hb.symm
        · obtain ⟨k', rfl⟩ := Fin.exists_castSucc_eq.mpr hk
          rw [snocV_castSucc, hbelow, hs, pureV_val]
      ·
        refine Or.inr (Or.inr ⟨m, 0, by omega, s, single 𝔘 a, Subtype.ext (funext fun k => ?_)⟩)
        rw [mix_val]
        by_cases hk : (k : ℕ) < m + 1
        · rw [dif_pos hk]
          have e1 : σ.1 k = σ'.1 ⟨k, hk⟩ :=
            (congrArg σ.1 (Fin.ext rfl : k = (⟨k, hk⟩ : Fin (m + 1)).castSucc)).trans (hbelow ⟨k, hk⟩)
          rw [e1, hs, pureV_val]
        · rw [dif_neg hk]
          have : k = Fin.last (m + 1) := Fin.ext (by have := k.isLt; simp; omega)
          exact (congrArg σ.1 this).trans ha.symm
    · rcases hcov (σ.1 (Fin.last (m + 1))) with ⟨b, hb⟩ | ⟨a, ha⟩
      ·
        exfalso
        have h1 : σ'.1 (Fin.last m) = eU (t.1 (Fin.last m)) := by rw [ht, pureU_val]
        rw [h1, ← hb] at hlast
        exact (lt_asymm hlast (hlt _ _)).elim
      · have ha' : t.1 (Fin.last m) < a := by
          apply eU.lt_iff_lt.mp
          rw [ha, ← pureU_val 𝔘 𝔛' eU t, ← ht]; exact hlast
        refine Or.inr (Or.inl ⟨snocU 𝔘 t a ha', Subtype.ext (funext fun k => ?_)⟩)
        rw [pureU_val]
        by_cases hk : k = Fin.last (m + 1)
        · subst hk; rw [snocU_last]; exact ha.symm
        · obtain ⟨k', rfl⟩ := Fin.exists_castSucc_eq.mpr hk
          rw [snocU_castSucc, hbelow, ht, pureU_val]
    · rcases hcov (σ.1 (Fin.last (m + 1))) with ⟨b, hb⟩ | ⟨a, ha⟩
      · exfalso
        have h1 : σ'.1 (Fin.last m) = eU (t.1 ⟨m - (p + 1), by omega⟩) := by
          rw [hst, mix_val, dif_neg (by simp; omega)]
          exact congrArg eU (congrArg t.1 (Fin.ext (by simp)))
        rw [h1, ← hb] at hlast
        exact (lt_asymm hlast (hlt _ _)).elim
      · have ha' : t.1 (Fin.last q) < a := by
          apply eU.lt_iff_lt.mp
          rw [ha]
          have h1 : σ'.1 (Fin.last m) = eU (t.1 (Fin.last q)) := by
            rw [hst, mix_val, dif_neg (by simp; omega)]
            exact congrArg eU (congrArg t.1 (Fin.ext (by simp; omega)))
          rw [← h1]; exact hlast
        refine Or.inr (Or.inr ⟨p, q + 1, by omega, s, snocU 𝔘 t a ha', Subtype.ext (funext fun k => ?_)⟩)
        rw [mix_val]
        by_cases hk : k = Fin.last (m + 1)
        · subst hk
          rw [dif_neg (by simp; omega)]
          have : (⟨(Fin.last (m + 1) : ℕ) - (p + 1), by simp; omega⟩ : Fin (q + 2)) = Fin.last (q + 1) :=
            Fin.ext (by simp; omega)
          rw [this, snocU_last]; exact ha.symm
        · obtain ⟨k', rfl⟩ := Fin.exists_castSucc_eq.mpr hk
          rw [hbelow, hst, mix_val]
          simp only [Fin.val_castSucc]
          by_cases hk' : (k' : ℕ) < p + 1
          · rw [dif_pos hk', dif_pos hk']
          · rw [dif_neg hk', dif_neg hk']
            have : (⟨(k' : ℕ) - (p + 1), by omega⟩ : Fin (q + 2))
                = (⟨(k' : ℕ) - (p + 1), by omega⟩ : Fin (q + 1)).castSucc := Fin.ext rfl
            rw [this, snocU_castSucc]

section Opens

variable (hV : ∀ b, 𝔛'.U (eV b) = V.ι ''ᵁ 𝔙.U b) (hU : ∀ a, 𝔛'.U (eU a) = U.ι ''ᵁ 𝔘.U a)

omit hlt in
include hV in

theorem image_inter_le_inter_pureV {p : ℕ} (s : 𝔙.Idx p) :
    V.ι ''ᵁ 𝔙.inter s ≤ 𝔛'.inter (pureV 𝔙 𝔛' eV s) := by
  refine le_iInf fun j => ?_
  rw [pureV_val, hV]
  exact Scheme.Hom.image_mono _ (𝔙.inter_le s j)

omit hlt in
include hV in

theorem inter_pureV_le_image_inter {p : ℕ} (s : 𝔙.Idx p) :
    𝔛'.inter (pureV 𝔙 𝔛' eV s) ≤ V.ι ''ᵁ 𝔙.inter s := by
  have hle : ∀ j, 𝔛'.inter (pureV 𝔙 𝔛' eV s) ≤ V.ι ''ᵁ 𝔙.U (s.1 j) := fun j =>
    (iInf_le _ j).trans (by rw [pureV_val, hV])
  have hO : 𝔛'.inter (pureV 𝔙 𝔛' eV s) ≤ V.ι.opensRange := (hle 0).trans (V.ι.image_le_opensRange _)
  have h1 : V.ι ⁻¹ᵁ 𝔛'.inter (pureV 𝔙 𝔛' eV s) ≤ 𝔙.inter s := le_iInf fun j =>
    (V.ι.preimage_mono (hle j)).trans (by rw [Scheme.Hom.preimage_image_eq])
  calc 𝔛'.inter (pureV 𝔙 𝔛' eV s) = V.ι ''ᵁ V.ι ⁻¹ᵁ 𝔛'.inter (pureV 𝔙 𝔛' eV s) := by
        rw [Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right.mpr hO]
    _ ≤ V.ι ''ᵁ 𝔙.inter s := V.ι.image_mono h1

omit hlt in
include hV in

theorem inter_pureV_eq {p : ℕ} (s : 𝔙.Idx p) :
    𝔛'.inter (pureV 𝔙 𝔛' eV s) = (𝔙.imageFamily V.ι).inter (show (𝔙.imageFamily V.ι).Idx p from s) := by
  refine le_antisymm (le_iInf fun j => ?_) (le_iInf fun j => ?_)
  · refine (iInf_le _ j).trans ?_
    rw [pureV_val, hV]; exact le_rfl
  · refine (iInf_le _ j).trans ?_
    show V.ι ''ᵁ 𝔙.U (s.1 j) ≤ _
    rw [pureV_val, hV]

include hV hU in
theorem inter_mix_le {p q n : ℕ} (h : p + q + 1 = n) (s : 𝔙.Idx p) (t : 𝔘.Idx q) :
    𝔛'.inter (mix 𝔙 𝔘 𝔛' eV eU hlt h s t)
      ≤ (𝔙.imageFamily V.ι).inter (show (𝔙.imageFamily V.ι).Idx p from s)
        ⊓ (𝔘.imageFamily U.ι).inter (show (𝔘.imageFamily U.ι).Idx q from t) := by
  refine le_inf (le_iInf fun j => ?_) (le_iInf fun k => ?_)
  · refine (iInf_le _ ⟨j, by omega⟩).trans ?_
    show 𝔛'.U ((mix 𝔙 𝔘 𝔛' eV eU hlt h s t).1 ⟨j, _⟩) ≤ V.ι ''ᵁ 𝔙.U (s.1 j)
    rw [mix_val, dif_pos (by simp <;> omega), hV]
  · refine (iInf_le _ ⟨p + 1 + k, by omega⟩).trans ?_
    show 𝔛'.U ((mix 𝔙 𝔘 𝔛' eV eU hlt h s t).1 ⟨p + 1 + k, _⟩) ≤ U.ι ''ᵁ 𝔘.U (t.1 k)
    rw [mix_val, dif_neg (by simp <;> omega), hU]
    apply le_of_eq; congr 2; apply congrArg; exact Fin.ext (by simp)

include hV hU in
theorem le_inter_mix {p q n : ℕ} (h : p + q + 1 = n) (s : 𝔙.Idx p) (t : 𝔘.Idx q) :
    (𝔙.imageFamily V.ι).inter (show (𝔙.imageFamily V.ι).Idx p from s)
        ⊓ (𝔘.imageFamily U.ι).inter (show (𝔘.imageFamily U.ι).Idx q from t)
      ≤ 𝔛'.inter (mix 𝔙 𝔘 𝔛' eV eU hlt h s t) := by
  refine le_iInf fun l => ?_
  by_cases hl : (l : ℕ) < p + 1
  · refine inf_le_left.trans ((iInf_le _ ⟨l, hl⟩).trans ?_)
    show V.ι ''ᵁ 𝔙.U (s.1 ⟨l, hl⟩) ≤ 𝔛'.U ((mix 𝔙 𝔘 𝔛' eV eU hlt h s t).1 l)
    rw [mix_val, dif_pos hl, hV]
  · refine inf_le_right.trans ((iInf_le _ ⟨(l : ℕ) - (p + 1), by omega⟩).trans ?_)
    show U.ι ''ᵁ 𝔘.U (t.1 ⟨(l : ℕ) - (p + 1), _⟩) ≤ 𝔛'.U ((mix 𝔙 𝔘 𝔛' eV eU hlt h s t).1 l)
    rw [mix_val, dif_neg hl, hU]

end Opens

section Maps

variable {R : Type u} [CommRing R] (π : X ⟶ Spec (.of R)) (N : X.Modules)
variable (hV : ∀ b, 𝔛'.U (eV b) = V.ι ''ᵁ 𝔙.U b) (hU : ∀ a, 𝔛'.U (eU a) = U.ι ''ᵁ 𝔘.U a)

local notation "FX" => OModulePresheaf.ofModules π N
local notation "FV" => OModulePresheaf.ofModules (V.ι ≫ π) (N.restrict V.ι)
local notation "AV" => Scheme.OrderedAffineCover.imageFamily 𝔙 V.ι
local notation "BU" => Scheme.OrderedAffineCover.imageFamily 𝔘 U.ι
local notation "DD" => OModulePresheaf.biCech (OModulePresheaf.ofModules π N)
  (Scheme.OrderedAffineCover.imageFamily 𝔙 V.ι) (Scheme.OrderedAffineCover.imageFamily 𝔘 U.ι)

omit hlt in

theorem res_res_self {O O' : X.Opens} (h : O ≤ O') (h' : O' ≤ O) (y : (FX).obj O) :
    (FX).res h ((FX).res h' y) = y := by
  rw [OModulePresheaf.res_res]; exact OModulePresheaf.res_refl_apply _ _ _

omit hlt in

theorem resV_eq {W W' : (V : Scheme.{u}).Opens} (h : W ≤ W') (y : (FV).obj W') :
    (FV).res h y = (FX).res (V.ι.image_mono h) (show (FX).obj (V.ι ''ᵁ W') from y) := by
  show (N.restrict V.ι).presheaf.map (homOfLE h).op y = N.presheaf.map (homOfLE _).op y
  rw [Scheme.Modules.restrict_map]
  exact congrArg (fun g : (V.ι ''ᵁ W ⟶ V.ι ''ᵁ W') => N.presheaf.map g.op y) (Subsingleton.elim _ _)

omit hlt in

noncomputable def rx {m : ℕ} (x : (FX).cochain 𝔛' m) {O : X.Opens} (τ : 𝔛'.Idx m) (h : O ≤ 𝔛'.inter τ) : (FX).obj O :=
  (FX).res h (x τ)

omit hlt in
theorem rx_congr {m : ℕ} (x : (FX).cochain 𝔛' m) {O : X.Opens} {τ τ' : 𝔛'.Idx m} (e : τ = τ')
    (h : O ≤ 𝔛'.inter τ) : rx 𝔛' π N x τ h = rx 𝔛' π N x τ' ((congrArg 𝔛'.inter e).le.trans' h) := by
  subst e; rfl

omit hlt in
theorem res_rx {m : ℕ} (x : (FX).cochain 𝔛' m) {O O' : X.Opens} (τ : 𝔛'.Idx m) (h : O' ≤ 𝔛'.inter τ)
    (h' : O ≤ O') : (FX).res h' (rx 𝔛' π N x τ h) = rx 𝔛' π N x τ (h'.trans h) :=
  OModulePresheaf.res_res _ _ _ _

omit hlt in

theorem res_d_apply {m : ℕ} (x : (FX).cochain 𝔛' m) (σ : 𝔛'.Idx (m + 1)) {O : X.Opens} (h : O ≤ 𝔛'.inter σ) :
    (FX).res h ((FX).d 𝔛' m x σ)
      = ∑ l : Fin (m + 2), ((-1 : ℤ) ^ (l : ℕ)) • rx 𝔛' π N x (𝔛'.face σ l) (h.trans (𝔛'.inter_le_inter_face σ l)) := by
  rw [OModulePresheaf.d_apply, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_zsmul, OModulePresheaf.res_res]; rfl

omit hlt in
include hV in

noncomputable def resV {m : ℕ} (x : (FX).cochain 𝔛' m) : (FV).cochain 𝔙 m :=
  fun s => show (FX).obj (V.ι ''ᵁ 𝔙.inter s) from
    rx 𝔛' π N x (pureV 𝔙 𝔛' eV s) (image_inter_le_inter_pureV 𝔙 𝔛' eV hV s)

omit hlt in
include hV in
theorem resV_add {m : ℕ} (x y : (FX).cochain 𝔛' m) :
    resV 𝔙 𝔛' eV π N hV (x + y) = resV 𝔙 𝔛' eV π N hV x + resV 𝔙 𝔛' eV π N hV y := by
  funext s; exact map_add ((FX).res _) _ _

omit hlt in
include hV in
theorem resV_sub {m : ℕ} (x y : (FX).cochain 𝔛' m) :
    resV 𝔙 𝔛' eV π N hV (x - y) = resV 𝔙 𝔛' eV π N hV x - resV 𝔙 𝔛' eV π N hV y := by
  funext s; exact map_sub ((FX).res _) _ _

omit hlt in
include hV in
theorem resV_zero {m : ℕ} : resV 𝔙 𝔛' eV π N hV (0 : (FX).cochain 𝔛' m) = 0 := by
  funext s; exact map_zero ((FX).res _)

omit hlt in
include hV in

theorem resV_d {m : ℕ} (x : (FX).cochain 𝔛' m) :
    resV 𝔙 𝔛' eV π N hV ((FX).d 𝔛' m x) = (FV).d 𝔙 m (resV 𝔙 𝔛' eV π N hV x) := by
  funext s
  show (FX).res _ ((FX).d 𝔛' m x (pureV 𝔙 𝔛' eV s)) = _
  rw [res_d_apply, OModulePresheaf.d_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [resV_eq]
  show _ = ((-1 : ℤ) ^ (l : ℕ)) • (FX).res _ (rx 𝔛' π N x _ _)
  rw [res_rx]
  rfl

omit hlt in
include hV in

noncomputable def extVAux {m : ℕ} (z : (FV).cochain 𝔙 m) (σ : 𝔛'.Idx m) (s : 𝔙.Idx m)
    (e : pureV 𝔙 𝔛' eV s = σ) : (FX).obj (𝔛'.inter σ) :=
  (FX).res ((congrArg 𝔛'.inter e).symm.le.trans (inter_pureV_le_image_inter 𝔙 𝔛' eV hV s))
    (show (FX).obj (V.ι ''ᵁ 𝔙.inter s) from z s)

omit hlt in
include hV in
theorem extVAux_indep {m : ℕ} (z : (FV).cochain 𝔙 m) (σ : 𝔛'.Idx m) (s s' : 𝔙.Idx m)
    (e : pureV 𝔙 𝔛' eV s = σ) (e' : pureV 𝔙 𝔛' eV s' = σ) :
    extVAux 𝔙 𝔛' eV π N hV z σ s e = extVAux 𝔙 𝔛' eV π N hV z σ s' e' := by
  obtain rfl : s = s' := pureV_injective 𝔙 𝔛' eV (e.trans e'.symm)
  rfl

omit hlt in
include hV in

noncomputable def extV {m : ℕ} (z : (FV).cochain 𝔙 m) : (FX).cochain 𝔛' m :=
  fun σ => by
    classical
    exact if h : ∃ s, pureV 𝔙 𝔛' eV s = σ then extVAux 𝔙 𝔛' eV π N hV z σ h.choose h.choose_spec else 0

omit hlt in
include hV in
theorem extV_pureV {m : ℕ} (z : (FV).cochain 𝔙 m) (s : 𝔙.Idx m) :
    extV 𝔙 𝔛' eV π N hV z (pureV 𝔙 𝔛' eV s)
      = (FX).res (inter_pureV_le_image_inter 𝔙 𝔛' eV hV s) (show (FX).obj (V.ι ''ᵁ 𝔙.inter s) from z s) := by
  have h : ∃ s', pureV 𝔙 𝔛' eV s' = pureV 𝔙 𝔛' eV s := ⟨s, rfl⟩
  classical
  show dite _ _ _ = _
  rw [dif_pos h, extVAux_indep 𝔙 𝔛' eV π N hV z _ h.choose s h.choose_spec rfl]
  rfl

omit hlt in
include hV in
theorem extV_of_ne {m : ℕ} (z : (FV).cochain 𝔙 m) (σ : 𝔛'.Idx m) (hσ : ∀ s, pureV 𝔙 𝔛' eV s ≠ σ) :
    extV 𝔙 𝔛' eV π N hV z σ = 0 := by
  classical
  show dite _ _ _ = _
  rw [dif_neg (fun ⟨s, hs⟩ => hσ s hs)]

omit hlt in
include hV in
theorem resV_extV {m : ℕ} (z : (FV).cochain 𝔙 m) : resV 𝔙 𝔛' eV π N hV (extV 𝔙 𝔛' eV π N hV z) = z := by
  funext s
  show (FX).res _ (extV 𝔙 𝔛' eV π N hV z (pureV 𝔙 𝔛' eV s)) = _
  rw [extV_pureV, res_res_self]

include hV hU in

noncomputable def toTot {n : ℕ} (x : (FX).cochain 𝔛' (n + 1)) : DoubleComplex.Tot DD n :=
  fun pq st => ((-1 : ℤ) ^ pq.1.2) •
    rx 𝔛' π N x (mix 𝔙 𝔘 𝔛' eV eU hlt (n := n + 1) (by have := pq.2; omega) st.1 st.2)
      (le_inter_mix 𝔙 𝔘 𝔛' eV eU hlt hV hU _ st.1 st.2)

include hV hU in
theorem toTot_apply {n : ℕ} (x : (FX).cochain 𝔛' (n + 1)) (pq : DoubleComplex.Diag n)
    (st : (AV).Idx pq.1.1 × (BU).Idx pq.1.2) :
    toTot 𝔙 𝔘 𝔛' eV eU hlt π N hV hU x pq st = ((-1 : ℤ) ^ pq.1.2) •
      rx 𝔛' π N x (mix 𝔙 𝔘 𝔛' eV eU hlt (n := n + 1) (by have := pq.2; omega) st.1 st.2)
        (le_inter_mix 𝔙 𝔘 𝔛' eV eU hlt hV hU _ st.1 st.2) := rfl

include hV hU in
theorem toTot_add {n : ℕ} (x y : (FX).cochain 𝔛' (n + 1)) :
    toTot 𝔙 𝔘 𝔛' eV eU hlt π N hV hU (x + y)
      = toTot 𝔙 𝔘 𝔛' eV eU hlt π N hV hU x + toTot 𝔙 𝔘 𝔛' eV eU hlt π N hV hU y := by
  funext pq st
  show _ = toTot 𝔙 𝔘 𝔛' eV eU hlt π N hV hU x pq st + toTot 𝔙 𝔘 𝔛' eV eU hlt π N hV hU y pq st
  simp only [toTot_apply, rx, Pi.add_apply, map_add, smul_add]

include hV hU in
theorem toTot_sub {n : ℕ} (x y : (FX).cochain 𝔛' (n + 1)) :
    toTot 𝔙 𝔘 𝔛' eV eU hlt π N hV hU (x - y)
      = toTot 𝔙 𝔘 𝔛' eV eU hlt π N hV hU x - toTot 𝔙 𝔘 𝔛' eV eU hlt π N hV hU y := by
  funext pq st
  show _ = toTot 𝔙 𝔘 𝔛' eV eU hlt π N hV hU x pq st - toTot 𝔙 𝔘 𝔛' eV eU hlt π N hV hU y pq st
  simp only [toTot_apply, rx, Pi.sub_apply, map_sub, smul_sub]

include hV hU in

noncomputable def ofTotAux {n : ℕ} (mm : DoubleComplex.Tot DD n) (σ : 𝔛'.Idx (n + 1))
    (pq : DoubleComplex.Diag n) (st : (AV).Idx pq.1.1 × (BU).Idx pq.1.2)
    (e : mix 𝔙 𝔘 𝔛' eV eU hlt (n := n + 1) (by have := pq.2; omega) st.1 st.2 = σ) : (FX).obj (𝔛'.inter σ) :=
  ((-1 : ℤ) ^ pq.1.2) • (FX).res
    ((congrArg 𝔛'.inter e).symm.le.trans (inter_mix_le 𝔙 𝔘 𝔛' eV eU hlt hV hU _ st.1 st.2)) (mm pq st)

include hV hU in
theorem ofTotAux_indep {n : ℕ} (mm : DoubleComplex.Tot DD n) (σ : 𝔛'.Idx (n + 1))
    (pq pq' : DoubleComplex.Diag n) (st : (AV).Idx pq.1.1 × (BU).Idx pq.1.2)
    (st' : (AV).Idx pq'.1.1 × (BU).Idx pq'.1.2)
    (e : mix 𝔙 𝔘 𝔛' eV eU hlt (n := n + 1) (by have := pq.2; omega) st.1 st.2 = σ)
    (e' : mix 𝔙 𝔘 𝔛' eV eU hlt (n := n + 1) (by have := pq'.2; omega) st'.1 st'.2 = σ) :
    ofTotAux 𝔙 𝔘 𝔛' eV eU hlt π N hV hU mm σ pq st e = ofTotAux 𝔙 𝔘 𝔛' eV eU hlt π N hV hU mm σ pq' st' e' := by
  obtain ⟨⟨p, q⟩, hpq⟩ := pq
  obtain ⟨⟨p', q'⟩, hpq'⟩ := pq'
  obtain ⟨s, t⟩ := st
  obtain ⟨s', t'⟩ := st'
  obtain rfl : p = p' := mix_eq_mix_fst 𝔙 𝔘 𝔛' eV eU hlt _ _ s t s' t' (e.trans e'.symm)
  obtain rfl : q = q' := by simp only at hpq hpq'; omega
  obtain ⟨rfl, rfl⟩ := mix_injective 𝔙 𝔘 𝔛' eV eU hlt _ s s' t t' (e.trans e'.symm)
  rfl

include hV hU in

noncomputable def ofTot {n : ℕ} (mm : DoubleComplex.Tot DD n) : (FX).cochain 𝔛' (n + 1) :=
  fun σ => by
    classical
    exact if h : ∃ (pq : DoubleComplex.Diag n) (st : (AV).Idx pq.1.1 × (BU).Idx pq.1.2),
        mix 𝔙 𝔘 𝔛' eV eU hlt (n := n + 1) (by have := pq.2; omega) st.1 st.2 = σ
      then ofTotAux 𝔙 𝔘 𝔛' eV eU hlt π N hV hU mm σ h.choose h.choose_spec.choose h.choose_spec.choose_spec
      else 0

include hV hU in
theorem ofTot_mix {n : ℕ} (mm : DoubleComplex.Tot DD n) (pq : DoubleComplex.Diag n)
    (st : (AV).Idx pq.1.1 × (BU).Idx pq.1.2) :
    ofTot 𝔙 𝔘 𝔛' eV eU hlt π N hV hU mm (mix 𝔙 𝔘 𝔛' eV eU hlt (n := n + 1) (by have := pq.2; omega) st.1 st.2)
      = ((-1 : ℤ) ^ pq.1.2) •
        (FX).res (inter_mix_le 𝔙 𝔘 𝔛' eV eU hlt hV hU _ st.1 st.2) (mm pq st) := by
  have h : ∃ (pq' : DoubleComplex.Diag n) (st' : (AV).Idx pq'.1.1 × (BU).Idx pq'.1.2),
      mix 𝔙 𝔘 𝔛' eV eU hlt (n := n + 1) (by have := pq'.2; omega) st'.1 st'.2
        = mix 𝔙 𝔘 𝔛' eV eU hlt (n := n + 1) (by have := pq.2; omega) st.1 st.2 := ⟨pq, st, rfl⟩
  classical
  show dite _ _ _ = _
  rw [dif_pos h, ofTotAux_indep 𝔙 𝔘 𝔛' eV eU hlt π N hV hU mm _ h.choose pq h.choose_spec.choose st
    h.choose_spec.choose_spec rfl]
  rfl

include hV hU in
theorem ofTot_pureV {n : ℕ} (mm : DoubleComplex.Tot DD n) (s : 𝔙.Idx (n + 1)) :
    ofTot 𝔙 𝔘 𝔛' eV eU hlt π N hV hU mm (pureV 𝔙 𝔛' eV s) = 0 := by
  classical
  show dite _ _ _ = _
  rw [dif_neg]
  rintro ⟨pq, st, e⟩
  exact pureV_ne_mix 𝔙 𝔘 𝔛' eV eU hlt _ s st.1 st.2 e.symm

include hV hU in
theorem ofTot_pureU {n : ℕ} (mm : DoubleComplex.Tot DD n) (t : 𝔘.Idx (n + 1)) :
    ofTot 𝔙 𝔘 𝔛' eV eU hlt π N hV hU mm (pureU 𝔘 𝔛' eU t) = 0 := by
  classical
  show dite _ _ _ = _
  rw [dif_neg]
  rintro ⟨pq, st, e⟩
  exact pureU_ne_mix 𝔙 𝔘 𝔛' eV eU hlt _ t st.1 st.2 e.symm

omit hlt in
theorem neg_one_pow_smul_smul_self {M : Type u} [AddCommGroup M] (q : ℕ) (y : M) :
    ((-1 : ℤ) ^ q) • (((-1 : ℤ) ^ q) • y) = y := by
  rw [smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul]

include hV hU in
theorem toTot_ofTot {n : ℕ} (mm : DoubleComplex.Tot DD n) :
    toTot 𝔙 𝔘 𝔛' eV eU hlt π N hV hU (ofTot 𝔙 𝔘 𝔛' eV eU hlt π N hV hU mm) = mm := by
  funext pq st
  rw [toTot_apply, rx, ofTot_mix, map_zsmul, res_res_self, neg_one_pow_smul_smul_self]

include hV hU in
theorem resV_ofTot {n : ℕ} (mm : DoubleComplex.Tot DD n) :
    resV 𝔙 𝔛' eV π N hV (ofTot 𝔙 𝔘 𝔛' eV eU hlt π N hV hU mm) = 0 := by
  funext s
  show (FX).res _ (ofTot 𝔙 𝔘 𝔛' eV eU hlt π N hV hU mm (pureV 𝔙 𝔛' eV s)) = 0
  rw [ofTot_pureV, map_zero]

omit hlt in
theorem sum_fin_split {M : Type u} [AddCommMonoid M] {m a b : ℕ} (h : a + b = m) (f : Fin m → M) :
    ∑ l : Fin m, f l = ∑ j : Fin a, f ⟨j, by omega⟩ + ∑ k : Fin b, f ⟨a + k, by omega⟩ := by
  subst h
  rw [Fin.sum_univ_add]
  rfl

omit hlt in
theorem negOnePow_congr {a b : ℕ} (h : a % 2 = b % 2) : ((-1 : ℤ) ^ a) = (-1 : ℤ) ^ b := by
  rw [neg_one_pow_eq_pow_mod_two, h, ← neg_one_pow_eq_pow_mod_two]

include hV hU in

theorem toTot_d_apply {n p q : ℕ} (h : p + q = n + 1) (x : (FX).cochain 𝔛' (n + 1))
    (s : (AV).Idx p) (t : (BU).Idx q) :
    toTot 𝔙 𝔘 𝔛' eV eU hlt π N hV hU ((FX).d 𝔛' (n + 1) x) ⟨(p, q), h⟩ (s, t)
      = ((-1 : ℤ) ^ q) •
        ((∑ j : Fin (p + 1), ((-1 : ℤ) ^ (j : ℕ)) •
            rx 𝔛' π N x (𝔛'.face (mix 𝔙 𝔘 𝔛' eV eU hlt (n := n + 1 + 1) (by omega) s t) ⟨j, by omega⟩)
              ((le_inter_mix 𝔙 𝔘 𝔛' eV eU hlt hV hU _ s t).trans (𝔛'.inter_le_inter_face _ _))) +
          ∑ k : Fin (q + 1), ((-1 : ℤ) ^ (p + 1 + (k : ℕ))) •
            rx 𝔛' π N x (𝔛'.face (mix 𝔙 𝔘 𝔛' eV eU hlt (n := n + 1 + 1) (by omega) s t) ⟨p + 1 + k, by omega⟩)
              ((le_inter_mix 𝔙 𝔘 𝔛' eV eU hlt hV hU _ s t).trans (𝔛'.inter_le_inter_face _ _))) := by
  rw [toTot_apply]
  show ((-1 : ℤ) ^ q) • rx 𝔛' π N ((FX).d 𝔛' (n + 1) x) _ _ = _
  rw [rx, res_d_apply, sum_fin_split (a := p + 1) (b := q + 1) (by omega)]

include hV hU in

theorem toTot_d_eq {n : ℕ} (y : (FX).cochain 𝔛' (n + 1))
    (hyV : ∀ s, y (pureV 𝔙 𝔛' eV s) = 0) (hyU : ∀ t, y (pureU 𝔘 𝔛' eU t) = 0) :
    toTot 𝔙 𝔘 𝔛' eV eU hlt π N hV hU ((FX).d 𝔛' (n + 1) y)
      = DoubleComplex.dTot DD n (toTot 𝔙 𝔘 𝔛' eV eU hlt π N hV hU y) := by
  funext pq st
  obtain ⟨⟨p, q⟩, hpq⟩ := pq
  obtain ⟨s, t⟩ := st
  simp only at hpq
  rcases p with _ | p' <;> rcases q with _ | q'
  · exfalso; omega
  ·
    obtain rfl : q' = n := by omega
    rw [toTot_d_apply, DoubleComplex.dTot_apply_zero_succ, OModulePresheaf.biCech_dV,
      OModulePresheaf.BiCech.dV_apply]
    simp only [toTot_apply, map_zsmul, res_rx, smul_add, Finset.smul_sum, smul_smul]

    rw [Fin.sum_univ_one, rx_congr 𝔛' π N y
      (show 𝔛'.face _ ⟨((0 : Fin 1) : ℕ), _⟩ = pureU 𝔘 𝔛' eU t from by
        rw [show (⟨((0 : Fin 1) : ℕ), by omega⟩ : Fin (q' + 1 + 2)) = 0 from Fin.ext rfl]
        exact face_mix_zero 𝔙 𝔘 𝔛' eV eU hlt s t)]
    rw [rx, hyU, map_zero, smul_zero, zero_add]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [rx_congr 𝔛' π N y (face_mix_right 𝔙 𝔘 𝔛' eV eU hlt (p := 0) (q := q') (n := q' + 1) (by omega) s t k)]
    congr 1
    simp only [← pow_add]
    exact negOnePow_congr (by omega)
  ·
    obtain rfl : p' = n := by omega
    rw [toTot_d_apply, DoubleComplex.dTot_apply_succ_zero, OModulePresheaf.biCech_dH,
      OModulePresheaf.BiCech.dH_apply]
    simp only [toTot_apply, map_zsmul, res_rx, smul_add, Finset.smul_sum, smul_smul]
    rw [Fin.sum_univ_one, rx_congr 𝔛' π N y
      (show 𝔛'.face _ ⟨p' + 1 + 1 + ((0 : Fin 1) : ℕ), _⟩ = pureV 𝔙 𝔛' eV s from by
        rw [show (⟨p' + 1 + 1 + ((0 : Fin 1) : ℕ), by omega⟩ : Fin (p' + 1 + 2)) = Fin.last (p' + 1 + 1) from
          Fin.ext (by simp)]
        exact face_mix_last 𝔙 𝔘 𝔛' eV eU hlt s t)]
    rw [rx, hyV, map_zero, smul_zero, add_zero]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [rx_congr 𝔛' π N y (face_mix_left 𝔙 𝔘 𝔛' eV eU hlt (p := p') (q := 0) (n := p' + 1) (by omega) s t j)]
    congr 1
    simp only [← pow_add]
    exact negOnePow_congr (by omega)
  ·
    have hn3 : p' + (q' + 1) + 1 = n + 1 := by omega
    have hn4 : p' + 1 + q' + 1 = n + 1 := by omega
    rw [toTot_d_apply, DoubleComplex.dTot_apply_succ_succ, OModulePresheaf.biCech_dH, OModulePresheaf.biCech_dV,
      Pi.add_apply, Pi.smul_apply, OModulePresheaf.BiCech.dH_apply, OModulePresheaf.BiCech.dV_apply]
    simp only [toTot_apply, map_zsmul, res_rx, smul_add, Finset.smul_sum, smul_smul]
    congr 1
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [rx_congr 𝔛' π N y (face_mix_left 𝔙 𝔘 𝔛' eV eU hlt (p := p') (q := q' + 1) (n := n + 1) hn3 s t j)]
      congr 1
      simp only [← pow_add]
      exact negOnePow_congr (by omega)
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [rx_congr 𝔛' π N y (face_mix_right 𝔙 𝔘 𝔛' eV eU hlt (p := p' + 1) (q := q') (n := n + 1) hn4 s t k)]
      congr 1
      simp only [← pow_add]
      exact negOnePow_congr (by omega)

omit hlt in

theorem d_pureU_eq_zero {m : ℕ} (y : (FX).cochain 𝔛' m) (hyU : ∀ t, y (pureU 𝔘 𝔛' eU t) = 0)
    (t : 𝔘.Idx (m + 1)) : (FX).d 𝔛' m y (pureU 𝔘 𝔛' eU t) = 0 := by
  rw [OModulePresheaf.d_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  have h0 : y (𝔛'.face (pureU 𝔘 𝔛' eU t) j) = 0 := hyU (𝔘.face t j)
  rw [h0, map_zero, smul_zero]

omit hlt in

theorem d_pureV_eq_zero {m : ℕ} (y : (FX).cochain 𝔛' m) (hyV : ∀ s, y (pureV 𝔙 𝔛' eV s) = 0)
    (s : 𝔙.Idx (m + 1)) : (FX).d 𝔛' m y (pureV 𝔙 𝔛' eV s) = 0 := by
  rw [OModulePresheaf.d_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  have h0 : y (𝔛'.face (pureV 𝔙 𝔛' eV s) j) = 0 := hyV (𝔙.face s j)
  rw [h0, map_zero, smul_zero]

omit hlt in
include hV in

theorem pureV_eq_zero_of_resV {m : ℕ} (x : (FX).cochain 𝔛' m) (hx : resV 𝔙 𝔛' eV π N hV x = 0)
    (s : 𝔙.Idx m) : x (pureV 𝔙 𝔛' eV s) = 0 := by
  have h1 : (FX).res (image_inter_le_inter_pureV 𝔙 𝔛' eV hV s) (x (pureV 𝔙 𝔛' eV s)) = 0 := congrFun hx s
  rw [← res_res_self π N (inter_pureV_le_image_inter 𝔙 𝔛' eV hV s) (image_inter_le_inter_pureV 𝔙 𝔛' eV hV s)
    (x (pureV 𝔙 𝔛' eV s)), h1, map_zero]

include hV hU in

theorem mix_eq_zero_of_toTot {n : ℕ} (x : (FX).cochain 𝔛' (n + 1))
    (hx : toTot 𝔙 𝔘 𝔛' eV eU hlt π N hV hU x = 0) {p q : ℕ} (h : p + q + 1 = n + 1)
    (s : 𝔙.Idx p) (t : 𝔘.Idx q) : x (mix 𝔙 𝔘 𝔛' eV eU hlt h s t) = 0 := by
  have h1 := congrFun (congrFun hx ⟨(p, q), by omega⟩) (s, t)
  rw [toTot_apply] at h1
  have h2 : rx 𝔛' π N x (mix 𝔙 𝔘 𝔛' eV eU hlt h s t) (le_inter_mix 𝔙 𝔘 𝔛' eV eU hlt hV hU _ s t) = 0 := by
    rw [← neg_one_pow_smul_smul_self q (rx 𝔛' π N x _ _)]
    exact (congrArg _ h1).trans (smul_zero _)
  rw [← res_res_self π N (inter_mix_le 𝔙 𝔘 𝔛' eV eU hlt hV hU h s t)
    (le_inter_mix 𝔙 𝔘 𝔛' eV eU hlt hV hU h s t) (x _)]
  exact (congrArg _ h2).trans (map_zero _)

theorem eq_zero_of_forall (hcov : ∀ j, j ∈ Set.range eV ∨ j ∈ Set.range eU) {m : ℕ} (x : (FX).cochain 𝔛' m)
    (hV0 : ∀ s, x (pureV 𝔙 𝔛' eV s) = 0) (hU0 : ∀ t, x (pureU 𝔘 𝔛' eU t) = 0)
    (hM0 : ∀ (p q : ℕ) (h : p + q + 1 = m) (s : 𝔙.Idx p) (t : 𝔘.Idx q),
      x (mix 𝔙 𝔘 𝔛' eV eU hlt h s t) = 0) : x = 0 := by
  funext σ
  rcases trichotomy 𝔙 𝔘 𝔛' eV eU hlt hcov m σ with ⟨s, rfl⟩ | ⟨t, rfl⟩ | ⟨p, q, h, s, t, rfl⟩
  · exact hV0 s
  · exact hU0 t
  · exact hM0 p q h s t

end Maps

section Main

variable {R : Type u} [CommRing R] (π : X ⟶ Spec (.of R)) (N : X.Modules)
variable (hV : ∀ b, 𝔛'.U (eV b) = V.ι ''ᵁ 𝔙.U b) (hU : ∀ a, 𝔛'.U (eU a) = U.ι ''ᵁ 𝔘.U a)
variable (hcov : ∀ j, j ∈ Set.range eV ∨ j ∈ Set.range eU)

local notation "FX" => OModulePresheaf.ofModules π N
local notation "FV" => OModulePresheaf.ofModules (V.ι ≫ π) (N.restrict V.ι)
local notation "DD" => OModulePresheaf.biCech (OModulePresheaf.ofModules π N)
  (Scheme.OrderedAffineCover.imageFamily 𝔙 V.ι) (Scheme.OrderedAffineCover.imageFamily 𝔘 U.ι)

include hV hU in

theorem dTot_toTot_d_extV {m : ℕ} (z : (FV).cochain 𝔙 m) (hz : (FV).d 𝔙 m z = 0) :
    DoubleComplex.dTot DD m (toTot 𝔙 𝔘 𝔛' eV eU hlt π N hV hU ((FX).d 𝔛' m (extV 𝔙 𝔛' eV π N hV z))) = 0 := by
  set x0 := extV 𝔙 𝔛' eV π N hV z with hx0
  have hU0 : ∀ t, x0 (pureU 𝔘 𝔛' eU t) = 0 := fun t =>
    extV_of_ne 𝔙 𝔛' eV π N hV z _ fun s => pureV_ne_pureU 𝔙 𝔘 𝔛' eV eU hlt s t

  have hdV : ∀ s, (FX).d 𝔛' m x0 (pureV 𝔙 𝔛' eV s) = 0 := by
    refine pureV_eq_zero_of_resV 𝔙 𝔛' eV π N hV _ ?_
    rw [resV_d, hx0, resV_extV, hz]
  have hdU : ∀ t, (FX).d 𝔛' m x0 (pureU 𝔘 𝔛' eU t) = 0 := d_pureU_eq_zero 𝔘 𝔛' eU π N x0 hU0
  rw [← toTot_d_eq 𝔙 𝔘 𝔛' eV eU hlt π N hV hU _ hdV hdU]
  have : (FX).d 𝔛' (m + 1) ((FX).d 𝔛' m x0) = 0 := by
    rw [← LinearMap.comp_apply, OModulePresheaf.d_comp_d]; rfl
  rw [this]
  funext pq st
  simp only [toTot_apply, rx, Pi.zero_apply, map_zero, smul_zero]
  rfl

include hV hU hcov in

theorem eq_zero_of_d_zero
    (hX : (FX).H0 𝔛' = ⊥)
    (hD : Subsingleton (DoubleComplex.HTot DD 0))
    (z : (FV).cochain 𝔙 0) (hz : (FV).d 𝔙 0 z = 0) : z = 0 := by
  set x0 := extV 𝔙 𝔛' eV π N hV z with hx0

  set mm := toTot 𝔙 𝔘 𝔛' eV eU hlt π N hV hU ((FX).d 𝔛' 0 x0) with hmm
  have hm0 : DoubleComplex.dTot DD 0 mm = 0 := dTot_toTot_d_extV 𝔙 𝔘 𝔛' eV eU hlt π N hV hU z hz
  have hmm0 : mm = 0 := by
    have htop : (⊥ : Submodule R (LinearMap.ker (DoubleComplex.dTot DD 0))) = ⊤ :=
      Submodule.Quotient.subsingleton_iff.mp hD
    have : (⟨mm, hm0⟩ : LinearMap.ker (DoubleComplex.dTot DD 0)) ∈ (⊥ : Submodule R _) := htop ▸ Submodule.mem_top
    exact congrArg Subtype.val ((Submodule.mem_bot R).mp this)

  have hU0 : ∀ t, x0 (pureU 𝔘 𝔛' eU t) = 0 := fun t =>
    extV_of_ne 𝔙 𝔛' eV π N hV z _ fun s => pureV_ne_pureU 𝔙 𝔘 𝔛' eV eU hlt s t
  have hdx0 : (FX).d 𝔛' 0 x0 = 0 := by
    refine eq_zero_of_forall 𝔙 𝔘 𝔛' eV eU hlt π N hcov _ ?_ ?_ ?_
    · refine pureV_eq_zero_of_resV 𝔙 𝔛' eV π N hV _ ?_
      rw [resV_d, hx0, resV_extV, hz]
    · exact d_pureU_eq_zero 𝔘 𝔛' eU π N x0 hU0
    · intro p q h s t
      exact mix_eq_zero_of_toTot 𝔙 𝔘 𝔛' eV eU hlt π N hV hU _ (hmm ▸ hmm0) h s t

  have hx00 : x0 = 0 := by
    have : x0 ∈ (FX).H0 𝔛' := LinearMap.mem_ker.mpr hdx0
    rw [hX] at this
    exact (Submodule.mem_bot R).mp this
  rw [← resV_extV 𝔙 𝔛' eV π N hV z, ← hx0, hx00, resV_zero]

include hV hU hcov in

theorem mem_range_of_d_zero (i : ℕ)
    (hX : Subsingleton ((FX).HSucc 𝔛' i))
    (hD : Subsingleton (DoubleComplex.HTot DD (i + 1)))
    (z : (FV).cochain 𝔙 (i + 1)) (hz : (FV).d 𝔙 (i + 1) z = 0) :
    z ∈ LinearMap.range ((FV).d 𝔙 i) := by
  set x0 := extV 𝔙 𝔛' eV π N hV z with hx0
  set mm := toTot 𝔙 𝔘 𝔛' eV eU hlt π N hV hU ((FX).d 𝔛' (i + 1) x0) with hmm
  have hm0 : DoubleComplex.dTot DD (i + 1) mm = 0 := dTot_toTot_d_extV 𝔙 𝔘 𝔛' eV eU hlt π N hV hU z hz

  obtain ⟨mm', hmm'⟩ : mm ∈ LinearMap.range (DoubleComplex.dTot DD i) := by
    have htop : (LinearMap.range (DoubleComplex.dTot DD i)).comap
        (LinearMap.ker (DoubleComplex.dTot DD (i + 1))).subtype = ⊤ :=
      Submodule.Quotient.subsingleton_iff.mp hD
    have : (⟨mm, hm0⟩ : LinearMap.ker (DoubleComplex.dTot DD (i + 1))) ∈
        (LinearMap.range (DoubleComplex.dTot DD i)).comap (LinearMap.ker (DoubleComplex.dTot DD (i + 1))).subtype :=
      htop ▸ Submodule.mem_top
    exact this

  set x1 := x0 - ofTot 𝔙 𝔘 𝔛' eV eU hlt π N hV hU mm' with hx1
  have hU0 : ∀ t, x0 (pureU 𝔘 𝔛' eU t) = 0 := fun t =>
    extV_of_ne 𝔙 𝔛' eV π N hV z _ fun s => pureV_ne_pureU 𝔙 𝔘 𝔛' eV eU hlt s t
  have hoV := ofTot_pureV 𝔙 𝔘 𝔛' eV eU hlt π N hV hU mm'
  have hoU := ofTot_pureU 𝔙 𝔘 𝔛' eV eU hlt π N hV hU mm'
  have hdx1 : (FX).d 𝔛' (i + 1) x1 = 0 := by
    refine eq_zero_of_forall 𝔙 𝔘 𝔛' eV eU hlt π N hcov _ ?_ ?_ ?_
    · refine pureV_eq_zero_of_resV 𝔙 𝔛' eV π N hV _ ?_
      rw [resV_d, hx1, resV_sub, hx0, resV_extV, resV_ofTot, sub_zero, hz]
    · refine d_pureU_eq_zero 𝔘 𝔛' eU π N x1 fun t => ?_
      rw [hx1, Pi.sub_apply, hU0, hoU, sub_zero]
    · intro p q h s t
      refine mix_eq_zero_of_toTot 𝔙 𝔘 𝔛' eV eU hlt π N hV hU _ ?_ h s t
      rw [hx1, map_sub, toTot_sub, ← hmm, toTot_d_eq 𝔙 𝔘 𝔛' eV eU hlt π N hV hU _ hoV hoU, toTot_ofTot, hmm',
        sub_self]

  obtain ⟨w, hw⟩ : x1 ∈ LinearMap.range ((FX).d 𝔛' i) := by
    have htop : (LinearMap.range ((FX).d 𝔛' i)).comap (LinearMap.ker ((FX).d 𝔛' (i + 1))).subtype = ⊤ :=
      Submodule.Quotient.subsingleton_iff.mp hX
    have : (⟨x1, LinearMap.mem_ker.mpr hdx1⟩ : LinearMap.ker ((FX).d 𝔛' (i + 1))) ∈
        (LinearMap.range ((FX).d 𝔛' i)).comap (LinearMap.ker ((FX).d 𝔛' (i + 1))).subtype :=
      htop ▸ Submodule.mem_top
    exact this

  refine ⟨resV 𝔙 𝔛' eV π N hV w, ?_⟩
  rw [← resV_d, hw, hx1, resV_sub, hx0, resV_extV, resV_ofTot, sub_zero]

end Main

end K3Sol

open K3Sol in
theorem solution
    {R : Type u} [CommRing R] {X : Scheme.{u}} (π : X ⟶ Spec (CommRingCat.of R))
    (N : X.Modules) (U V : X.Opens)
    (𝔙 : (V : Scheme.{u}).OrderedAffineCover) (𝔘 : (U : Scheme.{u}).OrderedAffineCover)
    (𝔛' : X.OrderedAffineCover) (eV : 𝔙.ι ↪o 𝔛'.ι) (eU : 𝔘.ι ↪o 𝔛'.ι)
    (hV : ∀ b, 𝔛'.U (eV b) = V.ι ''ᵁ 𝔙.U b) (hU : ∀ a, 𝔛'.U (eU a) = U.ι ''ᵁ 𝔘.U a)
    (hlt : ∀ b a, eV b < eU a) (hcov : ∀ j, j ∈ Set.range eV ∨ j ∈ Set.range eU)
    (hX : (OModulePresheaf.ofModules π N).H0 𝔛' = ⊥ ∧
      ∀ i, Subsingleton ((OModulePresheaf.ofModules π N).HSucc 𝔛' i))
    (hD : ∀ n, Subsingleton (DoubleComplex.HTot
      ((OModulePresheaf.ofModules π N).biCech (𝔙.imageFamily V.ι) (𝔘.imageFamily U.ι)) n)) :
    (OModulePresheaf.ofModules (V.ι ≫ π) (N.restrict V.ι)).H0 𝔙 = ⊥ ∧
      ∀ i, Subsingleton ((OModulePresheaf.ofModules (V.ι ≫ π) (N.restrict V.ι)).HSucc 𝔙 i) := by
  refine ⟨(Submodule.eq_bot_iff _).mpr fun z hz => ?_, fun i => ?_⟩
  · exact eq_zero_of_d_zero 𝔙 𝔘 𝔛' eV eU hlt π N hV hU hcov hX.1 (hD 0) z (LinearMap.mem_ker.mp hz)
  · refine Submodule.Quotient.subsingleton_iff.mpr (eq_top_iff.mpr fun z _ => ?_)
    exact mem_range_of_d_zero 𝔙 𝔘 𝔛' eV eU hlt π N hV hU hcov i (hX.2 i) (hD (i + 1)) z.1
      (LinearMap.mem_ker.mp z.2)

end S_AlgebraicGeometry_OModulePresheaf_H0_eq_bot_and_forall_subsingleton_HSucc_restrict_of_subsingleton_HTot_biCech
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_H0_eq_bot_and_forall_subsingleton_HSucc_restrict_of_subsingleton_HTot_biCech (solution)
