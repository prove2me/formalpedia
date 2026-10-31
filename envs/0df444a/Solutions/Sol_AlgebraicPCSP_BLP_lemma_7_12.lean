-- Prove2me | solution 1 for AlgebraicPCSP.BLP.lemma_7_12
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T00:53:53.63465+00:00
-- url     : https://prove2.me/submissions/7ab8d23e-a6fd-4629-b91c-40ed18aa72b4

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_AlgebraicPCSP_BLP_PPConstruction
import Definitions.Def_AlgebraicPCSP_BLP_Qconv
import Definitions.Def_AlgebraicPCSP_BLP_LP

open PCSPBLPAff.Symmetric
open AlgebraicPCSP.BLP
open scoped Classical

variable {τ : Type} {ar : τ → ℕ} {A : Type} [Fintype A] [DecidableEq A] [Nonempty A]

abbrev FreeVar (ar : τ → ℕ) (n : ℕ) (R : τ) : Type := Fin (ar R) × Fin n
abbrev QuantVar (A : Type) (ar : τ → ℕ) (R : τ) : Type := Fin (ar R) → A
abbrev AtomIdx (A : Type) (ar : τ → ℕ) (n : ℕ) (R : τ) : Type :=
  QuantVar A ar R ⊕ QuantVar A ar R ⊕ Bool ⊕ (FreeVar ar n R × Bool)

noncomputable def varEquiv (ar : τ → ℕ) (n : ℕ) (R : τ) :
    Fin (Fintype.card (FreeVar ar n R ⊕ QuantVar A ar R)) ≃ (FreeVar ar n R ⊕ QuantVar A ar R) :=
  (Fintype.equivFin (FreeVar ar n R ⊕ QuantVar A ar R)).symm

lemma card_var_pos (ar : τ → ℕ) (n : ℕ) (R : τ) :
    0 < Fintype.card (FreeVar ar n R ⊕ QuantVar A ar R) :=
  @Fintype.card_pos _ _ ⟨Sum.inr (fun _ => Classical.arbitrary A)⟩

noncomputable def mkLinIneq (ar : τ → ℕ) (n : ℕ) (R : τ)
    (cX : FreeVar ar n R → ℚ) (cY : QuantVar A ar R → ℚ) (d : ℚ) : LinIneq where
  k := Fintype.card (FreeVar ar n R ⊕ QuantVar A ar R)
  k_pos := card_var_pos (A := A) ar n R
  c := fun j => Sum.elim cX cY (varEquiv (A := A) ar n R j)
  d := d

lemma mem_Qconv_mkLinIneq (ar : τ → ℕ) (n : ℕ) (R : τ)
    (cX : FreeVar ar n R → ℚ) (cY : QuantVar A ar R → ℚ) (d : ℚ)
    (a : FreeVar ar n R → ℚ) (b : QuantVar A ar R → ℚ) :
    (fun j => Sum.elim a b (varEquiv (A := A) ar n R j)) ∈
      Qconv.rel (mkLinIneq (A := A) ar n R cX cY d) ↔
    (∑ x, cX x * a x) + (∑ y, cY y * b y) ≤ d := by
  change (∑ j, Sum.elim cX cY (varEquiv (A := A) ar n R j) *
    Sum.elim a b (varEquiv (A := A) ar n R j) ≤ d) ↔ _
  rw [Equiv.sum_comp (varEquiv (A := A) ar n R)
    (fun v => Sum.elim cX cY v * Sum.elim a b v), Fintype.sum_sum_type]
  rfl

def atomCX {n : ℕ} {R : τ} : AtomIdx A ar n R → FreeVar ar n R → ℚ
  | Sum.inl _ => fun _ => 0
  | Sum.inr (Sum.inl _) => fun _ => 0
  | Sum.inr (Sum.inr (Sum.inl _)) => fun _ => 0
  | Sum.inr (Sum.inr (Sum.inr (p, true))) => fun p' => if p' = p then 1 else 0
  | Sum.inr (Sum.inr (Sum.inr (p, false))) => fun p' => if p' = p then -1 else 0

noncomputable def atomCY {n : ℕ} (𝔸 : RelStruct τ ar A) (e : Fin n ≃ A) (R : τ) :
    AtomIdx A ar n R → QuantVar A ar R → ℚ
  | Sum.inl r => fun r' => if r' = r then -1 else 0
  | Sum.inr (Sum.inl r) => fun r' => if r' = r then (if r ∈ 𝔸.rel R then 0 else 1) else 0
  | Sum.inr (Sum.inr (Sum.inl true)) => fun _ => 1
  | Sum.inr (Sum.inr (Sum.inl false)) => fun _ => -1
  | Sum.inr (Sum.inr (Sum.inr (p, true))) => fun r => if r p.1 = e p.2 then -1 else 0
  | Sum.inr (Sum.inr (Sum.inr (p, false))) => fun r => if r p.1 = e p.2 then 1 else 0

def atomD {n : ℕ} {R : τ} : AtomIdx A ar n R → ℚ
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl _) => 0
  | Sum.inr (Sum.inr (Sum.inl true)) => 1
  | Sum.inr (Sum.inr (Sum.inl false)) => -1
  | Sum.inr (Sum.inr (Sum.inr _)) => 0

noncomputable def relFormula {n : ℕ} (𝔸 : RelStruct τ ar A) (e : Fin n ≃ A) (R : τ) :
    AlgebraicPCSP.Theory.PPFormula LinIneq LinIneq.k (FreeVar ar n R) where
  Y := QuantVar A ar R
  Atom := AtomIdx A ar n R
  atomSym t := mkLinIneq (A := A) ar n R (atomCX t) (atomCY 𝔸 e R t) (atomD t)
  atomArgs _ := varEquiv (A := A) ar n R
  Eqn := Empty
  eqns := Empty.elim

lemma holds_relFormula_iff {n : ℕ} (𝔸 : RelStruct τ ar A) (e : Fin n ≃ A) (R : τ)
    (t : Fin (ar R) → Fin n → ℚ) :
    (relFormula 𝔸 e R).Holds Qconv (fun p => t p.1 p.2) ↔
      ∃ γ : (Fin (ar R) → A) → ℚ,
        (∀ r, 0 ≤ γ r) ∧
        (∀ r, r ∉ 𝔸.rel R → γ r = 0) ∧
        ∑ r, γ r = 1 ∧
        ∀ (i : Fin (ar R)) (j : Fin n),
          ∑ r ∈ Finset.univ.filter (fun r : Fin (ar R) → A => r i = e j), γ r = t i j := by
  refine exists_congr (fun (γ : (Fin (ar R) → A) → ℚ) => ?_)
  trans (∀ s : AtomIdx A ar n R,
      (fun j => Sum.elim (fun p : FreeVar ar n R => t p.1 p.2) γ (varEquiv (A := A) ar n R j)) ∈
        Qconv.rel (mkLinIneq (A := A) ar n R (atomCX s) (atomCY 𝔸 e R s) (atomD s)))
  · exact ⟨fun h => h.1, fun h => ⟨h, fun q => q.elim⟩⟩
  trans (∀ s : AtomIdx A ar n R,
      (∑ x, atomCX s x * (fun p : FreeVar ar n R => t p.1 p.2) x) +
        (∑ y, atomCY 𝔸 e R s y * γ y) ≤ atomD s)
  · exact forall_congr' (fun s =>
      mem_Qconv_mkLinIneq (A := A) ar n R (atomCX s) (atomCY 𝔸 e R s) (atomD s)
        (fun p : FreeVar ar n R => t p.1 p.2) γ)
  have h_inl : ∀ r, (∑ x, atomCX (Sum.inl r : AtomIdx A ar n R) x * t x.1 x.2) +
      (∑ y, atomCY 𝔸 e R (Sum.inl r) y * γ y) = -γ r := by
    intro r
    simp [atomCX, atomCY]
  have h_inr_inl : ∀ r, (∑ x, atomCX (Sum.inr (Sum.inl r) : AtomIdx A ar n R) x * t x.1 x.2) +
      (∑ y, atomCY 𝔸 e R (Sum.inr (Sum.inl r)) y * γ y) =
      if r ∈ 𝔸.rel R then 0 else γ r := by
    intro r
    by_cases hr : r ∈ 𝔸.rel R <;> simp [atomCX, atomCY, hr]
  have h_sum_pos : (∑ x, atomCX (Sum.inr (Sum.inr (Sum.inl true)) : AtomIdx A ar n R) x * t x.1 x.2) +
      (∑ y, atomCY 𝔸 e R (Sum.inr (Sum.inr (Sum.inl true))) y * γ y) = ∑ y, γ y := by
    simp [atomCX, atomCY]
  have h_sum_neg : (∑ x, atomCX (Sum.inr (Sum.inr (Sum.inl false)) : AtomIdx A ar n R) x * t x.1 x.2) +
      (∑ y, atomCY 𝔸 e R (Sum.inr (Sum.inr (Sum.inl false))) y * γ y) = -∑ y, γ y := by
    simp [atomCX, atomCY, Finset.sum_neg_distrib]
  have h_marg_true : ∀ i j,
      (∑ x, atomCX (Sum.inr (Sum.inr (Sum.inr ((i, j), true))) : AtomIdx A ar n R) x * t x.1 x.2) +
        (∑ y, atomCY 𝔸 e R (Sum.inr (Sum.inr (Sum.inr ((i, j), true)))) y * γ y) =
      t i j - ∑ r ∈ Finset.univ.filter (fun r : Fin (ar R) → A => r i = e j), γ r := by
    intro i j
    simp [atomCX, atomCY, ← Finset.sum_filter, Finset.sum_neg_distrib, sub_eq_add_neg]
  have h_marg_false : ∀ i j,
      (∑ x, atomCX (Sum.inr (Sum.inr (Sum.inr ((i, j), false))) : AtomIdx A ar n R) x * t x.1 x.2) +
        (∑ y, atomCY 𝔸 e R (Sum.inr (Sum.inr (Sum.inr ((i, j), false)))) y * γ y) =
      -t i j + ∑ r ∈ Finset.univ.filter (fun r : Fin (ar R) → A => r i = e j), γ r := by
    intro i j
    simp [atomCX, atomCY, ← Finset.sum_filter]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro r
      have hr := h (Sum.inl r)
      rw [h_inl r, atomD] at hr
      linarith
    · intro r hr_not
      have hr1 := h (Sum.inl r)
      have hr2 := h (Sum.inr (Sum.inl r))
      rw [h_inl r, atomD] at hr1
      rw [h_inr_inl r, if_neg hr_not, atomD] at hr2
      linarith
    · have h1 := h (Sum.inr (Sum.inr (Sum.inl true)))
      have h2 := h (Sum.inr (Sum.inr (Sum.inl false)))
      rw [h_sum_pos, atomD] at h1
      rw [h_sum_neg, atomD] at h2
      linarith
    · intro i j
      have hp1 := h (Sum.inr (Sum.inr (Sum.inr ((i, j), true))))
      have hp2 := h (Sum.inr (Sum.inr (Sum.inr ((i, j), false))))
      rw [h_marg_true i j, atomD] at hp1
      rw [h_marg_false i j, atomD] at hp2
      linarith
  · rintro ⟨hnonneg, hsupp, hsum1, hmarg⟩ s
    rcases s with r | r | b | ⟨⟨i, j⟩, b⟩
    · rw [h_inl r, atomD]
      linarith [hnonneg r]
    · rw [h_inr_inl r, atomD]
      by_cases hr : r ∈ 𝔸.rel R
      · simp [hr]
      · simp [hr, hsupp r hr]
    · cases b
      · rw [h_sum_neg, atomD, hsum1]
      · rw [h_sum_pos, atomD, hsum1]
    · cases b
      · rw [h_marg_false i j, atomD, hmarg i j]
        linarith
      · rw [h_marg_true i j, atomD, hmarg i j]
        linarith

def ppStruct {n : ℕ} (𝔸 : RelStruct τ ar A) (e : Fin n ≃ A) : RelStruct τ ar (Fin n → ℚ) where
  rel R := {t | (relFormula 𝔸 e R).Holds Qconv (fun p => t p.1 p.2)}

abbrev vecToDist {n : ℕ} (e : Fin n ≃ A) (v : Fin n → ℚ) : Prop :=
  (∀ a : A, 0 ≤ v (e.symm a)) ∧ ∑ a : A, v (e.symm a) = 1

noncomputable def defaultLPDist : LPDist A :=
  let a₀ : A := Classical.arbitrary A
  ⟨fun a => if a = a₀ then 1 else 0, by
    refine ⟨fun a => by dsimp only; split_ifs <;> norm_num, ?_⟩
    simp [Finset.sum_ite_eq', Finset.mem_univ]⟩

noncomputable def homB {n : ℕ} (e : Fin n ≃ A) (v : Fin n → ℚ) : LPDist A :=
  if hv : vecToDist e v then (⟨fun a => v (e.symm a), hv⟩ : LPDist A) else defaultLPDist

lemma homB_val_of_vecToDist {n : ℕ} (e : Fin n ≃ A) (v : Fin n → ℚ) (hv : vecToDist e v) :
    (homB e v).val = fun a => v (e.symm a) := by
  have h : homB e v = (⟨fun a => v (e.symm a), hv⟩ : LPDist A) := dif_pos hv
  exact congrArg Subtype.val h

def homA {n : ℕ} (e : Fin n ≃ A) (a : A) : Fin n → ℚ :=
  fun j => if e j = a then 1 else 0

theorem solution {τ : Type} {ar : τ → ℕ} {A : Type} [Fintype A] [DecidableEq A]
    [Nonempty A] (𝔸 : RelStruct τ ar A) :
    ∃ (n : ℕ) (𝔸' 𝔹' : RelStruct τ ar (Fin n → ℚ)),
      AlgebraicPCSP.Theory.IsPPPower n Qconv Qconv 𝔸' 𝔹' ∧
        AlgebraicPCSP.Theory.IsRelaxation 𝔸' 𝔹' 𝔸 (LP 𝔸) := by
  let n := Fintype.card A
  let e : Fin n ≃ A := (Fintype.equivFin A).symm
  refine ⟨n, ppStruct 𝔸 e, ppStruct 𝔸 e, ?_, ?_⟩
  · intro R
    exact ⟨relFormula 𝔸 e R, fun _ => Iff.rfl, fun _ => Iff.rfl⟩
  · refine ⟨⟨homA e, ?_⟩, ⟨homB e, ?_⟩⟩
    · intro R r₀ hr₀
      change (relFormula 𝔸 e R).Holds Qconv (fun p => (homA e ∘ r₀) p.1 p.2)
      rw [holds_relFormula_iff]
      refine ⟨fun r => if r = r₀ then 1 else 0, ?_, ?_, ?_, ?_⟩
      · intro r
        dsimp only
        split_ifs <;> norm_num
      · intro r hr
        have hne : r ≠ r₀ := fun h => hr (h ▸ hr₀)
        exact if_neg hne
      · simp [Finset.sum_ite_eq', Finset.mem_univ]
      · intro i j
        simp only [Function.comp_apply, homA, ← Finset.sum_filter, Finset.filter_filter]
        have hfilter : Finset.univ.filter (fun r : Fin (ar R) → A => r i = e j ∧ r = r₀) =
            if e j = r₀ i then {r₀} else ∅ := by
          ext r
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          split_ifs with h
          · simp only [Finset.mem_singleton]
            exact ⟨fun hr => hr.2, fun hr => ⟨by rw [hr, h], hr⟩⟩
          · simp only [Finset.notMem_empty, iff_false, not_and]
            intro h1 h2
            exact h (by rw [← h1, h2])
        rw [hfilter]
        split_ifs <;> simp
    · intro R t ht
      have ht' : (relFormula 𝔸 e R).Holds Qconv (fun p => t p.1 p.2) := ht
      rw [holds_relFormula_iff] at ht'
      rcases ht' with ⟨γ, hnonneg, hsupp, hsum1, hmarg⟩
      have hvec : ∀ i : Fin (ar R), vecToDist e (t i) := by
        intro i
        refine ⟨?_, ?_⟩
        · intro a
          have h := hmarg i (e.symm a)
          rw [Equiv.apply_symm_apply] at h
          rw [← h]
          exact Finset.sum_nonneg (fun r _ => hnonneg r)
        · have h1 : ∀ a : A, t i (e.symm a) =
              ∑ r ∈ Finset.univ.filter (fun r : Fin (ar R) → A => r i = a), γ r := by
            intro a
            have h := (hmarg i (e.symm a)).symm
            rwa [Equiv.apply_symm_apply] at h
          simp_rw [h1]
          rw [Finset.sum_fiberwise Finset.univ (fun r : Fin (ar R) → A => r i) γ, hsum1]
      refine ⟨γ, hnonneg, hsupp, hsum1, ?_⟩
      intro i a
      simp only [Function.comp_apply, homB_val_of_vecToDist e (t i) (hvec i)]
      have h := hmarg i (e.symm a)
      rwa [Equiv.apply_symm_apply] at h
