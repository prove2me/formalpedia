-- Prove2me | solution 1 for AlgebraicPCSP.BLP.theorem_7_9
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T02:35:59.132994+00:00
-- url     : https://prove2.me/submissions/f6395302-a911-4363-be3e-73c48ec1b5c3

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_AlgebraicPCSP_Theory_MinorCondition
import Definitions.Def_AlgebraicPCSP_BLP_PPConstruction
import Definitions.Def_AlgebraicPCSP_BLP_Qconv
import Definitions.Def_AlgebraicPCSP_BLP_LP
import Theorems.Thm_AlgebraicPCSP_BLP_blp_iff_hom_LP
import Theorems.Thm_AlgebraicPCSP_BLP_lemma_4_8_pp_power
import Theorems.Thm_AlgebraicPCSP_BLP_lemma_4_8_relaxation
import Theorems.Thm_AlgebraicPCSP_BLP_lemma_7_12
import Theorems.Thm_AlgebraicPCSP_BLP_remark_7_13
import Theorems.Thm_AlgebraicPCSP_BLP_h_ell_hom

namespace AlgebraicPCSP.BLP

open PCSPBLPAff.Symmetric

attribute [local instance] AlgebraicPCSP.Theory.PPFormula.finY
  AlgebraicPCSP.Theory.PPFormula.finAtom AlgebraicPCSP.Theory.PPFormula.finEqn

private lemma rat_in_LPell (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (ℓ : ℕ) (hℓ : 0 < ℓ)
    (hdvd : q.den ∣ ℓ) :
    ∃ k : ℕ, k ≤ ℓ ∧ q = (k : ℚ) / ℓ := by
  have hmul : q.den * (ℓ / q.den) = ℓ := Nat.mul_div_cancel' hdvd
  have hd_pos : 0 < ℓ / q.den := Nat.pos_of_ne_zero fun hd0 => by
    rw [hd0, mul_zero] at hmul
    omega
  have hqnum : 0 ≤ q.num := Rat.num_nonneg.mpr hq0
  have hcast_num : (q.num.toNat : ℚ) = (q.num : ℚ) := by
    exact_mod_cast Int.toNat_of_nonneg hqnum
  have hmul_q : (ℓ : ℚ) = (q.den : ℚ) * ((ℓ / q.den : ℕ) : ℚ) := by exact_mod_cast hmul.symm
  have hd_ne : ((ℓ / q.den : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hd_pos.ne'
  have hq_eq : ((q.num.toNat * (ℓ / q.den) : ℕ) : ℚ) / (ℓ : ℚ) = q := by
    rw [hmul_q]
    push_cast
    rw [hcast_num, mul_div_mul_right (q.num : ℚ) (q.den : ℚ) hd_ne, Rat.num_div_den]
  refine ⟨q.num.toNat * (ℓ / q.den), ?_, hq_eq.symm⟩
  have hle_rat : ((q.num.toNat * (ℓ / q.den) : ℕ) : ℚ) ≤ (ℓ : ℚ) := by
    have hℓ_pos : (0 : ℚ) < (ℓ : ℚ) := by positivity
    exact (div_le_one hℓ_pos).mp (hq_eq.trans_le hq1)
  exact_mod_cast hle_rat

private lemma imp_2_1 {τ : Type} {ar : τ → ℕ} {A B : Type} [Fintype A] [DecidableEq A]
    (𝔸 : RelStruct τ ar A) (𝔹 : RelStruct τ ar B)
    (h2 : ∀ n : ℕ, 0 < n → ∃ f : (Fin n → A) → B, IsPolymorphism 𝔸 𝔹 f ∧ IsSymmetric f) :
    BLPSolves 𝔸 𝔹 := by
  intro X ⟨w, p, hw0, hp0, hp_vanish, hw_sum, hp_sum, h_marg⟩
  let ℓ₁ : ℕ := ∏ ia : Fin X.n × A, (w ia.1 ia.2).den
  let ℓ₂ : ℕ := ∏ jy : (Σ j : Fin X.m, Fin (ar (X.sym j)) → A), (p jy.1 jy.2).den
  let ℓ : ℕ := ℓ₁ * ℓ₂
  have hℓ₁ : 0 < ℓ₁ := Finset.prod_pos (fun ia _ => Rat.den_pos _)
  have hℓ₂ : 0 < ℓ₂ := Finset.prod_pos (fun jy _ => Rat.den_pos _)
  have hℓ : 0 < ℓ := Nat.mul_pos hℓ₁ hℓ₂
  have hw_le1 : ∀ i a, w i a ≤ 1 := fun i a => by
    rw [← hw_sum i]
    exact Finset.single_le_sum (fun a' _ => hw0 i a') (Finset.mem_univ a)
  have hp_le1 : ∀ j y, p j y ≤ 1 := fun j y => by
    rw [← hp_sum j]
    exact Finset.single_le_sum (fun y' _ => hp0 j y') (Finset.mem_univ y)
  have hw_dvd : ∀ i a, (w i a).den ∣ ℓ := fun i a =>
    dvd_mul_of_dvd_left (Finset.dvd_prod_of_mem _ (Finset.mem_univ (i, a))) ℓ₂
  have hp_dvd : ∀ j y, (p j y).den ∣ ℓ := fun j y =>
    dvd_mul_of_dvd_right
      (Finset.dvd_prod_of_mem _
        (Finset.mem_univ (⟨j, y⟩ : Σ j' : Fin X.m, Fin (ar (X.sym j')) → A))) ℓ₁
  let ϕ : Fin X.n → LPellDist A ℓ := fun i =>
    ⟨w i, ⟨fun a => rat_in_LPell (w i a) (hw0 i a) (hw_le1 i a) ℓ hℓ (hw_dvd i a), hw_sum i⟩⟩
  obtain ⟨h, hh⟩ := h_ell_hom 𝔸 𝔹 ℓ hℓ (h2 ℓ hℓ)
  refine ⟨fun i => h (ϕ i), fun j => ?_⟩
  change (h ∘ (ϕ ∘ X.scope j)) ∈ 𝔹.rel (X.sym j)
  apply hh (X.sym j) (ϕ ∘ X.scope j)
  refine ⟨p j, fun r => rat_in_LPell (p j r) (hp0 j r) (hp_le1 j r) ℓ hℓ (hp_dvd j r),
    hp_vanish j, hp_sum j, fun k a => h_marg j k a⟩

private lemma imp_3_2 {τ : Type} {ar : τ → ℕ} {A B : Type}
    (𝔸 : RelStruct τ ar A) (𝔹 : RelStruct τ ar B) (h : IsPromiseTemplate 𝔸 𝔹)
    (h3 : ∃ ξ, AlgebraicPCSP.Theory.IsMinionHom convexMinion (AlgebraicPCSP.Theory.Pol 𝔸 𝔹 h) ξ) :
    ∀ n : ℕ, 0 < n → ∃ f : (Fin n → A) → B, IsPolymorphism 𝔸 𝔹 f ∧ IsSymmetric f := by
  obtain ⟨ξ, hξ⟩ := h3
  intro n hn
  let α : Fin n → ℚ := fun _ => (1 : ℚ) / (n : ℚ)
  let u : (Fin n → ℚ) → ℚ := fun x => ∑ i : Fin n, α i * x i
  have hu : u ∈ convexMinion.mem n := by
    refine ⟨α, fun _ => ⟨by positivity, ?_⟩, ?_, rfl⟩
    · have : (1 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
      exact div_le_one_of_le₀ this (by positivity)
    · dsimp [α]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        mul_one_div_cancel (by positivity : (n : ℚ) ≠ 0)]
  let f := (ξ n ⟨u, hu⟩).val
  have hf_pol : IsPolymorphism 𝔸 𝔹 f := ((ξ n ⟨u, hu⟩).property).2
  refine ⟨f, hf_pol, ?_⟩
  intro π x
  have hu_perm : (fun y : Fin n → ℚ => u (y ∘ π)) = u := by
    funext y
    simp only [u, α, Function.comp]
    exact Equiv.sum_comp π (fun i => (1 : ℚ) / (n : ℚ) * y i)
  have hminor := hξ π u hu
  have hsub : (⟨fun y => u (y ∘ π), convexMinion.minor_mem π u hu⟩ :
      {g // g ∈ convexMinion.mem n}) = ⟨u, hu⟩ := Subtype.ext hu_perm
  rw [hsub] at hminor
  exact (congrFun hminor x).symm

private lemma minionHom_comp {A₁ B₁ A₂ B₂ A₃ B₃ : Type}
    {M₁ : AlgebraicPCSP.Theory.Minion A₁ B₁}
    {M₂ : AlgebraicPCSP.Theory.Minion A₂ B₂}
    {M₃ : AlgebraicPCSP.Theory.Minion A₃ B₃}
    {ξ₁ : (n : ℕ) → {f // f ∈ M₁.mem n} → {f // f ∈ M₂.mem n}}
    {ξ₂ : (n : ℕ) → {f // f ∈ M₂.mem n} → {f // f ∈ M₃.mem n}}
    (h₁ : AlgebraicPCSP.Theory.IsMinionHom M₁ M₂ ξ₁)
    (h₂ : AlgebraicPCSP.Theory.IsMinionHom M₂ M₃ ξ₂) :
    AlgebraicPCSP.Theory.IsMinionHom M₁ M₃ (fun n f => ξ₂ n (ξ₁ n f)) := by
  intro m n π g hg
  dsimp only
  have h1 := h₁ π g hg
  have h2 := h₂ π (ξ₁ m ⟨g, hg⟩).val (ξ₁ m ⟨g, hg⟩).property
  have hsub : (⟨fun x => (ξ₁ m ⟨g, hg⟩).val (x ∘ π),
      M₂.minor_mem π (ξ₁ m ⟨g, hg⟩).val (ξ₁ m ⟨g, hg⟩).property⟩ : {f // f ∈ M₂.mem n}) =
      ξ₁ n ⟨fun x => g (x ∘ π), M₁.minor_mem π g hg⟩ :=
    Subtype.ext h1.symm
  rw [← hsub]
  exact h2

private lemma isPromiseTemplate_of_ppPower {τ₁ τ₂ : Type} {ar₁ : τ₁ → ℕ} {ar₂ : τ₂ → ℕ}
    {A₁ B₁ : Type} (n : ℕ)
    (𝔸₁ : RelStruct τ₁ ar₁ A₁) (𝔹₁ : RelStruct τ₁ ar₁ B₁)
    (𝔸₂ : RelStruct τ₂ ar₂ (Fin n → A₁)) (𝔹₂ : RelStruct τ₂ ar₂ (Fin n → B₁))
    (h₁ : IsPromiseTemplate 𝔸₁ 𝔹₁)
    (hpow : AlgebraicPCSP.Theory.IsPPPower n 𝔸₁ 𝔹₁ 𝔸₂ 𝔹₂) :
    IsPromiseTemplate 𝔸₂ 𝔹₂ := by
  obtain ⟨σ, hσ⟩ := h₁
  refine ⟨fun x i => σ (x i), fun R t ht => ?_⟩
  obtain ⟨Ψ, hΨA, hΨB⟩ := hpow R
  obtain ⟨b, hatom, heqn⟩ := (hΨA t).mp ht
  refine (hΨB (fun j i => σ (t j i))).mpr ⟨σ ∘ b, ?_, ?_⟩
  · intro a
    have h_elim : (fun j => Sum.elim (fun p : Fin (ar₂ R) × Fin n => σ (t p.1 p.2)) (σ ∘ b)
        (Ψ.atomArgs a j)) = σ ∘ (fun j => Sum.elim (fun p => t p.1 p.2) b (Ψ.atomArgs a j)) := by
      funext j
      change Sum.elim (fun p : Fin (ar₂ R) × Fin n => σ (t p.1 p.2)) (σ ∘ b) (Ψ.atomArgs a j) =
        σ (Sum.elim (fun p => t p.1 p.2) b (Ψ.atomArgs a j))
      cases Ψ.atomArgs a j <;> rfl
    rw [h_elim]
    exact hσ (Ψ.atomSym a) _ (hatom a)
  · intro q
    have h1 : Sum.elim (fun p : Fin (ar₂ R) × Fin n => σ (t p.1 p.2)) (σ ∘ b) (Ψ.eqns q).1 =
        σ (Sum.elim (fun p => t p.1 p.2) b (Ψ.eqns q).1) := by cases (Ψ.eqns q).1 <;> rfl
    have h2 : Sum.elim (fun p : Fin (ar₂ R) × Fin n => σ (t p.1 p.2)) (σ ∘ b) (Ψ.eqns q).2 =
        σ (Sum.elim (fun p => t p.1 p.2) b (Ψ.eqns q).2) := by cases (Ψ.eqns q).2 <;> rfl
    rw [h1, h2, heqn q]

private lemma ppConstructible_minionHom (T₀ : Template) (h₀ : IsPromiseTemplate T₀.𝔸 T₀.𝔹)
    {T' : Template} (hpp : PPConstructible T₀ T') :
    ∃ (hT' : IsPromiseTemplate T'.𝔸 T'.𝔹) (ξ : _),
      AlgebraicPCSP.Theory.IsMinionHom
        (AlgebraicPCSP.Theory.Pol T₀.𝔸 T₀.𝔹 h₀)
        (AlgebraicPCSP.Theory.Pol T'.𝔸 T'.𝔹 hT') ξ := by
  induction hpp with
  | refl =>
    exact ⟨h₀, fun _ f => f, fun _ _ _ => rfl⟩
  | @power T₁ hpp₁ n τ'' _ ar'' har'' 𝔸'' 𝔹'' hpow ih =>
    obtain ⟨hT₁, ξ₁, hξ₁⟩ := ih
    have hT₂ : IsPromiseTemplate 𝔸'' 𝔹'' :=
      isPromiseTemplate_of_ppPower n T₁.𝔸 T₁.𝔹 𝔸'' 𝔹'' hT₁ hpow
    obtain ⟨ξ₂, hξ₂⟩ := lemma_4_8_pp_power T₁.ar_pos har'' n T₁.𝔸 T₁.𝔹 𝔸'' 𝔹'' hT₁ hT₂ hpow
    exact ⟨hT₂, fun n f => ξ₂ n (ξ₁ n f), minionHom_comp hξ₁ hξ₂⟩
  | @relax T₁ hpp₁ A'' B'' 𝔸'' 𝔹'' htemp hrel ih =>
    obtain ⟨hT₁, ξ₁, hξ₁⟩ := ih
    obtain ⟨ξ₂, hξ₂⟩ := lemma_4_8_relaxation T₁.ar_pos T₁.𝔸 T₁.𝔹 𝔸'' 𝔹'' hT₁ htemp hrel
    exact ⟨htemp, fun n f => ξ₂ n (ξ₁ n f), minionHom_comp hξ₁ hξ₂⟩

private lemma imp_4_3 {τ : Type} [Fintype τ] {ar : τ → ℕ} (har : ∀ R, 0 < ar R)
    {A B : Type} (𝔸 : RelStruct τ ar A) (𝔹 : RelStruct τ ar B) (h : IsPromiseTemplate 𝔸 𝔹)
    (h4 : ∃ S : Finset LinIneq,
      PPConstructible (Template.of (QconvReduct S) (QconvReduct S) (fun ι => ι.val.k_pos))
        (Template.of 𝔸 𝔹 har)) :
    ∃ ξ, AlgebraicPCSP.Theory.IsMinionHom convexMinion (AlgebraicPCSP.Theory.Pol 𝔸 𝔹 h) ξ := by
  obtain ⟨S, hpp⟩ := h4
  let T₀ := Template.of (QconvReduct S) (QconvReduct S) (fun ι => ι.val.k_pos)
  have h₀ : IsPromiseTemplate (QconvReduct S) (QconvReduct S) := ⟨id, fun _ _ ht => ht⟩
  obtain ⟨hT', ξ, hξ⟩ := ppConstructible_minionHom T₀ h₀ hpp
  have hconv_pol : ∀ (m : ℕ) (f : (Fin m → ℚ) → ℚ),
      f ∈ convexMinion.mem m →
        f ∈ (AlgebraicPCSP.Theory.Pol (QconvReduct S) (QconvReduct S) h₀).mem m := by
    rintro m f ⟨α, hα01, hαsum, rfl⟩
    have hm : 0 < m := by
      by_contra hm0
      have hm_eq : m = 0 := by omega
      subst hm_eq
      simp at hαsum
    refine ⟨hm, fun ι M hM => ?_⟩
    change ∑ k : Fin ι.val.k, ι.val.c k * (∑ l : Fin m, α l * M l k) ≤ ι.val.d
    have hswap : ∑ k : Fin ι.val.k, ι.val.c k * (∑ l : Fin m, α l * M l k) =
        ∑ l : Fin m, α l * (∑ k : Fin ι.val.k, ι.val.c k * M l k) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun k _ => by ring))
    rw [hswap]
    calc ∑ l : Fin m, α l * (∑ k : Fin ι.val.k, ι.val.c k * M l k)
        ≤ ∑ l : Fin m, α l * ι.val.d :=
          Finset.sum_le_sum (fun l _ => mul_le_mul_of_nonneg_left (hM l) (hα01 l).1)
      _ = (∑ l : Fin m, α l) * ι.val.d := (Finset.sum_mul _ _ _).symm
      _ = ι.val.d := by rw [hαsum, one_mul]
  let ξ₀ : (m : ℕ) → {f // f ∈ convexMinion.mem m} →
      {f // f ∈ (AlgebraicPCSP.Theory.Pol (QconvReduct S) (QconvReduct S) h₀).mem m} :=
    fun m f => ⟨f.val, hconv_pol m f.val f.property⟩
  have hξ₀ : AlgebraicPCSP.Theory.IsMinionHom convexMinion
      (AlgebraicPCSP.Theory.Pol (QconvReduct S) (QconvReduct S) h₀) ξ₀ := fun _ _ _ => rfl
  exact ⟨fun n f => ξ n (ξ₀ n f), minionHom_comp hξ₀ hξ⟩

private lemma hom_LP_of_BLPSolves {τ : Type} [Fintype τ] {ar : τ → ℕ}
    {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [Nonempty B]
    (𝔸 : RelStruct τ ar A) (𝔹 : RelStruct τ ar B)
    (h1 : BLPSolves 𝔸 𝔹) :
    ∃ σ : LPDist A → B, IsHom (LP 𝔸) 𝔹 σ := by
  classical
  have : Countable (LPDist A) := Function.Injective.countable Subtype.val_injective
  apply remark_7_13 (LP 𝔸) 𝔹
  intro S
  let nS := S.card
  let eS : Fin nS ≃ S := S.equivFin.symm
  let CR : Finset (Σ R : τ, Fin (ar R) → S) :=
    Finset.univ.filter (fun p => (fun k => (p.2 k).val) ∈ (LP 𝔸).rel p.1)
  let mS := CR.card
  let eCR : Fin mS ≃ CR := CR.equivFin.symm
  let XS : Instance τ ar := {
    n := nS
    m := mS
    sym := fun j => (eCR j).val.1
    scope := fun j k => eS.symm ((eCR j).val.2 k)
  }
  have hsat_LP : SatIn XS (LP 𝔸) := by
    refine ⟨fun i => (eS i).val, fun j => ?_⟩
    have h_eq : ((fun i => (eS i).val) ∘ XS.scope j) = fun k => ((eCR j).val.2 k).val := by
      funext k
      simp [XS]
    rw [h_eq]
    exact (Finset.mem_filter.mp (eCR j).property).2
  have hsat_B : SatIn XS 𝔹 := h1 XS ((blp_iff_hom_LP 𝔸 XS).mpr hsat_LP)
  obtain ⟨σB, hσB⟩ := hsat_B
  let b₀ : B := Classical.arbitrary B
  refine ⟨fun ϕ => if hϕ : ϕ ∈ S then σB (eS.symm ⟨ϕ, hϕ⟩) else b₀, fun R t ht htS => ?_⟩
  let tS : Fin (ar R) → S := fun k => ⟨t k, htS k⟩
  have ht_CR : (⟨R, tS⟩ : Σ R' : τ, Fin (ar R') → S) ∈ CR := by
    simp [CR, tS, ht]
  let j : Fin mS := eCR.symm ⟨⟨R, tS⟩, ht_CR⟩
  have hj : (eCR j).val = ⟨R, tS⟩ := by simp [j]
  have h_comp : (fun k : Fin (ar R) =>
      (if hϕ : t k ∈ S then σB (eS.symm ⟨t k, hϕ⟩) else b₀)) =
      fun k : Fin (ar R) => σB (eS.symm (tS k)) := by
    funext k
    simp [htS k, tS]
  change (fun k => if hϕ : t k ∈ S then σB (eS.symm ⟨t k, hϕ⟩) else b₀) ∈ 𝔹.rel R
  rw [h_comp]
  have hj_rel : (fun k => σB (eS.symm ((eCR j).val.2 k))) ∈ 𝔹.rel (eCR j).val.1 := hσB j
  rw [hj] at hj_rel
  exact hj_rel

private lemma imp_1_4 {τ : Type} [Fintype τ] {ar : τ → ℕ} (har : ∀ R, 0 < ar R)
    {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [Nonempty B]
    (𝔸 : RelStruct τ ar A) (𝔹 : RelStruct τ ar B) (h : IsPromiseTemplate 𝔸 𝔹)
    (h1 : BLPSolves 𝔸 𝔹) :
    ∃ S : Finset LinIneq,
      PPConstructible (Template.of (QconvReduct S) (QconvReduct S) (fun ι => ι.val.k_pos))
        (Template.of 𝔸 𝔹 har) := by
  classical
  by_cases hA : Nonempty A
  · obtain ⟨σ_LP, hσ_LP⟩ := hom_LP_of_BLPSolves 𝔸 𝔹 h1
    obtain ⟨n, 𝔸', 𝔹', hpow, ⟨hrelA, hB_LP, hhB_LP⟩⟩ := lemma_7_12 𝔸
    have hrel : AlgebraicPCSP.Theory.IsRelaxation 𝔸' 𝔹' 𝔸 𝔹 :=
      ⟨hrelA, ⟨σ_LP ∘ hB_LP, fun R t ht => hσ_LP R (hB_LP ∘ t) (hhB_LP R t ht)⟩⟩
    choose Ψ hΨA hΨB using hpow
    let _ : ∀ R : τ, Fintype (Ψ R).Atom := fun R => Fintype.ofFinite (Ψ R).Atom
    let S : Finset LinIneq :=
      Finset.univ.biUnion (fun R : τ => Finset.univ.image (fun a : (Ψ R).Atom => (Ψ R).atomSym a))
    have hpow_S : AlgebraicPCSP.Theory.IsPPPower n (QconvReduct S) (QconvReduct S) 𝔸' 𝔹' := by
      intro R
      let ΨS : AlgebraicPCSP.Theory.PPFormula S (fun ι => ι.val.k) (Fin (ar R) × Fin n) := {
        Y := (Ψ R).Y
        finY := (Ψ R).finY
        Atom := (Ψ R).Atom
        finAtom := (Ψ R).finAtom
        atomSym := fun a => ⟨(Ψ R).atomSym a,
          Finset.mem_biUnion.mpr ⟨R, Finset.mem_univ R, Finset.mem_image_of_mem _ (Finset.mem_univ a)⟩⟩
        atomArgs := (Ψ R).atomArgs
        Eqn := (Ψ R).Eqn
        finEqn := (Ψ R).finEqn
        eqns := (Ψ R).eqns
      }
      refine ⟨ΨS, fun t => (hΨA R t).trans ⟨fun h => h, fun h => h⟩,
        fun t => (hΨB R t).trans ⟨fun h => h, fun h => h⟩⟩
    let T₀ := Template.of (QconvReduct S) (QconvReduct S) (fun ι => ι.val.k_pos)
    have hpp₁ : PPConstructible T₀ (Template.of 𝔸' 𝔹' har) :=
      PPConstructible.power (T' := T₀) PPConstructible.refl n τ ar har 𝔸' 𝔹' hpow_S
    exact ⟨S, PPConstructible.relax hpp₁ A B 𝔸 𝔹 h hrel⟩
  · have : IsEmpty A := not_nonempty_iff.mp hA
    let ι₀ : LinIneq := ⟨1, Nat.one_pos, fun _ => 0, -1⟩
    let S : Finset LinIneq := {ι₀}
    let 𝔸' : RelStruct τ ar (Fin 1 → ℚ) := { rel := fun _ => ∅ }
    let 𝔹' : RelStruct τ ar (Fin 1 → ℚ) := { rel := fun _ => ∅ }
    have hpow_S : AlgebraicPCSP.Theory.IsPPPower 1 (QconvReduct S) (QconvReduct S) 𝔸' 𝔹' := by
      intro R
      let ΨS : AlgebraicPCSP.Theory.PPFormula S (fun ι => ι.val.k) (Fin (ar R) × Fin 1) := {
        Y := PUnit
        Atom := PUnit
        atomSym := fun _ => ⟨ι₀, Finset.mem_singleton_self ι₀⟩
        atomArgs := fun _ _ => Sum.inr PUnit.unit
        Eqn := PEmpty
        eqns := PEmpty.elim
      }
      have hfalse : ∀ x : Fin (ar R) × Fin 1 → ℚ, ¬ ΨS.Holds (QconvReduct S) x := by
        rintro x ⟨b, hatom, -⟩
        have h0 := hatom PUnit.unit
        change ∑ i : Fin 1, (0 : ℚ) * b PUnit.unit ≤ (-1 : ℚ) at h0
        norm_num at h0
      refine ⟨ΨS, fun t => ⟨False.elim, fun h => (hfalse _ h).elim⟩,
        fun t => ⟨False.elim, fun h => (hfalse _ h).elim⟩⟩
    have hrel : AlgebraicPCSP.Theory.IsRelaxation 𝔸' 𝔹' 𝔸 𝔹 := by
      refine ⟨⟨isEmptyElim, fun R t _ => (IsEmpty.false (t ⟨0, har R⟩)).elim⟩,
        ⟨fun _ => Classical.arbitrary B, fun _ _ ht => False.elim ht⟩⟩
    let T₀ := Template.of (QconvReduct S) (QconvReduct S) (fun ι => ι.val.k_pos)
    have hpp₁ : PPConstructible T₀ (Template.of 𝔸' 𝔹' har) :=
      PPConstructible.power (T' := T₀) PPConstructible.refl 1 τ ar har 𝔸' 𝔹' hpow_S
    exact ⟨S, PPConstructible.relax hpp₁ A B 𝔸 𝔹 h hrel⟩

end AlgebraicPCSP.BLP

open AlgebraicPCSP.BLP PCSPBLPAff.Symmetric

theorem solution {τ : Type} [Fintype τ] {ar : τ → ℕ} (har : ∀ R, 0 < ar R)
    {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [Nonempty B]
    (𝔸 : RelStruct τ ar A) (𝔹 : RelStruct τ ar B) (h : IsPromiseTemplate 𝔸 𝔹) :
    List.TFAE
      [BLPSolves 𝔸 𝔹,
       ∀ n : ℕ, 0 < n → ∃ f : (Fin n → A) → B, IsPolymorphism 𝔸 𝔹 f ∧ IsSymmetric f,
       ∃ ξ, AlgebraicPCSP.Theory.IsMinionHom convexMinion (AlgebraicPCSP.Theory.Pol 𝔸 𝔹 h) ξ,
       ∃ S : Finset LinIneq,
         PPConstructible (Template.of (QconvReduct S) (QconvReduct S) (fun ι => ι.val.k_pos))
           (Template.of 𝔸 𝔹 har)] := by
  tfae_have 1 → 4 := imp_1_4 har 𝔸 𝔹 h
  tfae_have 4 → 3 := imp_4_3 har 𝔸 𝔹 h
  tfae_have 3 → 2 := imp_3_2 𝔸 𝔹 h
  tfae_have 2 → 1 := imp_2_1 𝔸 𝔹
  tfae_finish
