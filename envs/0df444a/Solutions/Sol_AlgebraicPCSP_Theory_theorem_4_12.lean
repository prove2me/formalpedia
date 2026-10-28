-- Prove2me | solution 1 for AlgebraicPCSP.Theory.theorem_4_12
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-28T04:27:34.499062+00:00
-- url     : https://prove2.me/submissions/7e2064fe-4469-44e1-81d6-30b5fdc05ba5

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_AlgebraicPCSP_Theory_Minion
import Definitions.Def_AlgebraicPCSP_Theory_MinorCondition
import Definitions.Def_AlgebraicPCSP_Theory_PPConstruction

set_option autoImplicit false

namespace P0082

open PCSPBLPAff.Symmetric AlgebraicPCSP.Theory

/-- A minion homomorphism between the polymorphism families of two templates. -/
def PolHom {τ τ' : Type} {ar : τ → ℕ} {ar' : τ' → ℕ} {A B A' B' : Type}
    (𝔸 : RelStruct τ ar A) (𝔹 : RelStruct τ ar B) (𝔸' : RelStruct τ' ar' A')
    (𝔹' : RelStruct τ' ar' B') : Prop :=
  ∃ ξ : (n : ℕ) → {f // f ∈ polFamily 𝔸 𝔹 n} → {f // f ∈ polFamily 𝔸' 𝔹' n},
    ∀ {m n : ℕ} (π : Fin m → Fin n) (g : (Fin m → A) → B) (hg : g ∈ polFamily 𝔸 𝔹 m)
      (hg' : (fun x : Fin n → A => g (x ∘ π)) ∈ polFamily 𝔸 𝔹 n),
      (ξ n ⟨fun x => g (x ∘ π), hg'⟩).val = fun x : Fin n → A' => (ξ m ⟨g, hg⟩).val (x ∘ π)

theorem polHom_refl {τ : Type} {ar : τ → ℕ} {A B : Type}
    (𝔸 : RelStruct τ ar A) (𝔹 : RelStruct τ ar B) : PolHom 𝔸 𝔹 𝔸 𝔹 :=
  ⟨fun _ f => f, fun _ _ _ _ => rfl⟩

theorem polHom_trans {τ τ' τ'' : Type} {ar : τ → ℕ} {ar' : τ' → ℕ} {ar'' : τ'' → ℕ}
    {A B A' B' A'' B'' : Type}
    {𝔸 : RelStruct τ ar A} {𝔹 : RelStruct τ ar B} {𝔸' : RelStruct τ' ar' A'}
    {𝔹' : RelStruct τ' ar' B'} {𝔸'' : RelStruct τ'' ar'' A''} {𝔹'' : RelStruct τ'' ar'' B''}
    (h1 : PolHom 𝔸 𝔹 𝔸' 𝔹') (h2 : PolHom 𝔸' 𝔹' 𝔸'' 𝔹'') : PolHom 𝔸 𝔹 𝔸'' 𝔹'' := by
  obtain ⟨ξ, hξ⟩ := h1
  obtain ⟨η, hη⟩ := h2
  refine ⟨fun n f => η n (ξ n f), ?_⟩
  intro m n π g hg hg'
  have h := hξ π g hg hg'
  have hmem : (fun x => (ξ m ⟨g, hg⟩).val (x ∘ π)) ∈ polFamily 𝔸' 𝔹' n :=
    h ▸ (ξ n ⟨fun x => g (x ∘ π), hg'⟩).property
  have h3 : ξ n ⟨fun x => g (x ∘ π), hg'⟩ = ⟨fun x => (ξ m ⟨g, hg⟩).val (x ∘ π), hmem⟩ :=
    Subtype.ext h
  show (η n (ξ n ⟨fun x => g (x ∘ π), hg'⟩)).val = _
  rw [h3]
  exact hη π _ (ξ m ⟨g, hg⟩).property hmem

theorem polHom_relax {τ : Type} {ar : τ → ℕ} {A B A' B' : Type}
    (𝔸 : RelStruct τ ar A) (𝔹 : RelStruct τ ar B) (𝔸' : RelStruct τ ar A')
    (𝔹' : RelStruct τ ar B') (h : IsRelaxation 𝔸 𝔹 𝔸' 𝔹') : PolHom 𝔸 𝔹 𝔸' 𝔹' := by
  obtain ⟨⟨hA, hhA⟩, ⟨hB, hhB⟩⟩ := h
  refine ⟨fun n f => ⟨fun x => hB (f.val (fun l => hA (x l))), f.property.1, ?_⟩, ?_⟩
  · intro R M hM
    exact hhB R _ (f.property.2 R (fun l c => hA (M l c)) (fun l => hhA R (M l) (hM l)))
  · intro m n π g hg hg'
    rfl

theorem sum_elim_col {X Y C D : Type} {L : ℕ} (f : (Fin L → C) → D) (a : Fin L → X → C)
    (b : Fin L → Y → C) (v : X ⊕ Y) :
    Sum.elim (fun p => f (fun l => a l p)) (fun y => f (fun l => b l y)) v =
      f (fun l => Sum.elim (a l) (b l) v) := by
  cases v <;> rfl

theorem polHom_power {τ τ' : Type} {ar : τ → ℕ} {ar' : τ' → ℕ} {A B : Type} (N : ℕ)
    (𝔸 : RelStruct τ ar A) (𝔹 : RelStruct τ ar B)
    (𝔸' : RelStruct τ' ar' (Fin N → A)) (𝔹' : RelStruct τ' ar' (Fin N → B))
    (h : IsPPPower N 𝔸 𝔹 𝔸' 𝔹') : PolHom 𝔸 𝔹 𝔸' 𝔹' := by
  refine ⟨fun L f => ⟨fun x k => f.val (fun l => x l k), f.property.1, ?_⟩, ?_⟩
  · intro R M hM
    obtain ⟨Ψ, hΨA, hΨB⟩ := h R
    rw [hΨB]
    have hrow : ∀ l, Ψ.Holds 𝔸 (fun p => M l p.1 p.2) := fun l => (hΨA _).1 (hM l)
    choose b hb using hrow
    have key := sum_elim_col f.val (fun l (p : Fin (ar' R) × Fin N) => M l p.1 p.2) b
    refine ⟨fun y => f.val (fun l => b l y), ?_, ?_⟩
    · intro t
      have hp := f.property.2 (Ψ.atomSym t)
        (fun l j => Sum.elim (fun p => M l p.1 p.2) (b l) (Ψ.atomArgs t j)) (fun l => (hb l).1 t)
      convert hp using 1
      funext j
      exact key _
    · intro q
      rw [key, key]
      exact congrArg f.val (funext fun l => (hb l).2 q)
  · intro m n π g hg hg'
    rfl

theorem polHom_of_ppc (T T' : Template) (h : PPConstructible T T') :
    PolHom T.𝔸 T.𝔹 T'.𝔸 T'.𝔹 := by
  induction h with
  | refl => exact polHom_refl _ _
  | power _ n τ'' ar'' _ 𝔸'' 𝔹'' hpow ih =>
      exact polHom_trans ih (polHom_power n _ _ 𝔸'' 𝔹'' hpow)
  | relax _ A'' B'' 𝔸'' 𝔹'' _ hrel ih =>
      exact polHom_trans ih (polHom_relax _ _ 𝔸'' 𝔹'' hrel)

/-- The pp-formula defining `R^F` inside the pp-power of `(𝔸₁, 𝔹₁)`. -/
def psi {τ₁ τ₂ : Type} [Fintype τ₁] {ar₁ : τ₁ → ℕ} {ar₂ : τ₂ → ℕ} {A₁ A₂ : Type}
    [Fintype A₁] (𝔸₁ : RelStruct τ₁ ar₁ A₁) (𝔸₂ : RelStruct τ₂ ar₂ A₂) {n : ℕ}
    (e : Fin n ≃ A₂) (m : τ₂ → ℕ) (eR : (R : τ₂) → Fin (m R) ≃ 𝔸₂.rel R) {N : ℕ}
    (eqv : Fin N ≃ (Fin n → A₁)) (R : τ₂) : PPFormula τ₁ ar₁ (Fin (ar₂ R) × Fin N) where
  Y := Fin (m R) → A₁
  Atom := (S : τ₁) × {M : Fin (m R) → Fin (ar₁ S) → A₁ // ∀ l, M l ∈ 𝔸₁.rel S}
  atomSym := fun a => a.1
  atomArgs := fun a c => Sum.inr (fun l => a.2.val l c)
  Eqn := Fin (ar₂ R) × Fin N
  eqns := fun q => (Sum.inl q, Sum.inr (fun j => eqv q.2 (e.symm ((eR R j).val q.1))))

theorem four_to_five {τ₁ τ₂ : Type} [Fintype τ₁]
    {ar₁ : τ₁ → ℕ} {ar₂ : τ₂ → ℕ}
    {A₁ B₁ A₂ B₂ : Type} [Fintype A₁] [Nonempty A₂] [Nonempty B₂]
    (𝔸₁ : RelStruct τ₁ ar₁ A₁) (𝔹₁ : RelStruct τ₁ ar₁ B₁)
    (𝔸₂ : RelStruct τ₂ ar₂ A₂) (𝔹₂ : RelStruct τ₂ ar₂ B₂) (hne : ∀ R, (𝔸₂.rel R).Nonempty)
    (h₁ : IsPromiseTemplate 𝔸₁ 𝔹₁)
    {n : ℕ} (e : Fin n ≃ A₂) (m : τ₂ → ℕ) (eR : (R : τ₂) → Fin (m R) ≃ 𝔸₂.rel R)
    (c : {f // f ∈ (Pol 𝔸₁ 𝔹₁ h₁).mem n} → B₂)
    (hc : IsHom (freeStructure (Pol 𝔸₁ 𝔹₁ h₁) 𝔸₂ e m eR) 𝔹₂ c) :
    ∃ (N : ℕ) (𝔸' : RelStruct τ₂ ar₂ (Fin N → A₁)) (𝔹' : RelStruct τ₂ ar₂ (Fin N → B₁)),
      IsPPPower N 𝔸₁ 𝔹₁ 𝔸' 𝔹' ∧ IsRelaxation 𝔸' 𝔹' 𝔸₂ 𝔹₂ := by
  classical
  let eqv : Fin (Fintype.card (Fin n → A₁)) ≃ (Fin n → A₁) := (Fintype.equivFin _).symm
  let Ψ := psi 𝔸₁ 𝔸₂ e m eR eqv
  refine ⟨_, ⟨fun R => {t | (Ψ R).Holds 𝔸₁ (fun p => t p.1 p.2)}⟩,
    ⟨fun R => {t | (Ψ R).Holds 𝔹₁ (fun p => t p.1 p.2)}⟩,
    fun R => ⟨Ψ R, fun t => Iff.rfl, fun t => Iff.rfl⟩, ?_, ?_⟩
  · refine ⟨fun a k => eqv k (e.symm a), ?_⟩
    intro R t ht
    refine ⟨fun y => y ((eR R).symm ⟨t, ht⟩), ?_, ?_⟩
    · rintro ⟨S, M, hM⟩
      exact hM _
    · rintro ⟨i, k⟩
      show eqv k (e.symm (t i)) = eqv k (e.symm ((eR R ((eR R).symm ⟨t, ht⟩)).val i))
      rw [Equiv.apply_symm_apply]
  · have hm : ∀ R, 0 < m R := fun R => by
      obtain ⟨t, ht⟩ := hne R
      exact Fin.pos ((eR R).symm ⟨t, ht⟩)
    refine ⟨fun φ => if hφ : (fun x => φ (eqv.symm x)) ∈ (Pol 𝔸₁ 𝔹₁ h₁).mem n then
      c ⟨_, hφ⟩ else Classical.arbitrary B₂, ?_⟩
    intro R t ht
    obtain ⟨g, hgA, hgE⟩ := ht
    have hg : g ∈ (Pol 𝔸₁ 𝔹₁ h₁).mem (m R) :=
      ⟨hm R, fun S M hM => hgA ⟨S, ⟨M, hM⟩⟩⟩
    have hφ : ∀ i, (fun x => t i (eqv.symm x)) =
        fun x : Fin n → A₁ => g (fun j => x (e.symm ((eR R j).val i))) := by
      intro i
      funext x
      refine (hgE (i, eqv.symm x)).trans ?_
      show g (fun j => eqv (eqv.symm x) (e.symm ((eR R j).val i))) = _
      rw [Equiv.apply_symm_apply]
    have hmem : ∀ i, (fun x => t i (eqv.symm x)) ∈ (Pol 𝔸₁ 𝔹₁ h₁).mem n := by
      intro i
      rw [hφ i]
      exact (Pol 𝔸₁ 𝔹₁ h₁).minor_mem (fun j => e.symm ((eR R j).val i)) g hg
    have hrel : (fun i => (⟨_, hmem i⟩ : {f // f ∈ (Pol 𝔸₁ 𝔹₁ h₁).mem n})) ∈
        (freeStructure (Pol 𝔸₁ 𝔹₁ h₁) 𝔸₂ e m eR).rel R := ⟨g, hg, fun i => hφ i⟩
    have := hc R _ hrel
    convert this using 1
    funext i
    simp only [Function.comp_apply]
    rw [dif_pos (hmem i)]

end P0082

open PCSPBLPAff.Symmetric AlgebraicPCSP.Theory in
theorem solution {τ₁ τ₂ : Type} [Fintype τ₁] [Fintype τ₂]
    {ar₁ : τ₁ → ℕ} {ar₂ : τ₂ → ℕ} (har₁ : ∀ R, 0 < ar₁ R) (har₂ : ∀ R, 0 < ar₂ R)
    {A₁ B₁ A₂ B₂ : Type} [Fintype A₁] [DecidableEq A₁] [Nonempty A₁] [Fintype B₁] [DecidableEq B₁] [Nonempty B₁]
    [Fintype A₂] [DecidableEq A₂] [Nonempty A₂] [Fintype B₂] [DecidableEq B₂] [Nonempty B₂]
    (𝔸₁ : RelStruct τ₁ ar₁ A₁) (𝔹₁ : RelStruct τ₁ ar₁ B₁)
    (𝔸₂ : RelStruct τ₂ ar₂ A₂) (𝔹₂ : RelStruct τ₂ ar₂ B₂) (hne : ∀ R, (𝔸₂.rel R).Nonempty)
    (h₁ : IsPromiseTemplate 𝔸₁ 𝔹₁) (h₂ : IsPromiseTemplate 𝔸₂ 𝔹₂)
    {n : ℕ} (e : Fin n ≃ A₂) (m : τ₂ → ℕ) (eR : (R : τ₂) → Fin (m R) ≃ 𝔸₂.rel R) :
    List.TFAE
      [ ∃ ξ, IsMinionHom (Pol 𝔸₁ 𝔹₁ h₁) (Pol 𝔸₂ 𝔹₂ h₂) ξ,
        ∀ S : BipartiteMinorCondition, (Pol 𝔸₁ 𝔹₁ h₁).Satisfies S → (Pol 𝔸₂ 𝔹₂ h₂).Satisfies S,
        (Pol 𝔸₂ 𝔹₂ h₂).Satisfies
          (sigmaCondition 𝔸₂ (freeStructure (Pol 𝔸₁ 𝔹₁ h₁) 𝔸₂ e m eR) e m eR),
        ∃ c, IsHom (freeStructure (Pol 𝔸₁ 𝔹₁ h₁) 𝔸₂ e m eR) 𝔹₂ c,
        ∃ (N : ℕ) (𝔸' : RelStruct τ₂ ar₂ (Fin N → A₁)) (𝔹' : RelStruct τ₂ ar₂ (Fin N → B₁)),
          IsPPPower N 𝔸₁ 𝔹₁ 𝔸' 𝔹' ∧ IsRelaxation 𝔸' 𝔹' 𝔸₂ 𝔹₂,
        PPConstructible (Template.of 𝔸₁ 𝔹₁ har₁) (Template.of 𝔸₂ 𝔹₂ har₂) ] := by
  tfae_have 1 → 2 := by
    rintro ⟨ξ, hξ⟩ S hS
    unfold Minion.Satisfies SatisfiedIn at hS ⊢
    obtain ⟨ζU, ζV, hU, hV, hE⟩ := hS
    refine ⟨fun u => (ξ _ ⟨ζU u, hU u⟩).val, fun v => (ξ _ ⟨ζV v, hV v⟩).val,
      fun u => (ξ _ _).property, fun v => (ξ _ _).property, ?_⟩
    intro i
    have h1 : (⟨ζU (S.lhs i), hU (S.lhs i)⟩ : {f // f ∈ (Pol 𝔸₁ 𝔹₁ h₁).mem (S.arU (S.lhs i))}) =
        ⟨fun x => ζV (S.rhs i) (x ∘ S.map i),
          (Pol 𝔸₁ 𝔹₁ h₁).minor_mem (S.map i) _ (hV (S.rhs i))⟩ := Subtype.ext (hE i)
    show (ξ _ ⟨ζU (S.lhs i), hU (S.lhs i)⟩).val = _
    rw [h1]
    exact hξ (S.map i) (ζV (S.rhs i)) (hV (S.rhs i))
  tfae_have 2 → 3 := by
    intro h
    apply h
    unfold Minion.Satisfies SatisfiedIn
    refine ⟨fun v => v.val, fun C => Classical.choose C.2.2, fun v => v.property,
      fun C => (Classical.choose_spec C.2.2).1, ?_⟩
    rintro ⟨C, i⟩
    exact (Classical.choose_spec C.2.2).2 i
  tfae_have 3 → 4 := by
    intro h
    unfold Minion.Satisfies SatisfiedIn at h
    obtain ⟨ζU, ζV, hU, hV, hE⟩ := h
    refine ⟨fun v => ζU v (fun i => e i), ?_⟩
    intro R t ht
    have key : ∀ i, ζU (t i) (fun i => e i) = ζV ⟨R, ⟨t, ht⟩⟩ (fun j => (eR R j).val i) := by
      intro i
      have h2 := congrFun (hE ⟨⟨R, ⟨t, ht⟩⟩, i⟩) (fun i => e i)
      refine h2.trans ?_
      show ζV ⟨R, ⟨t, ht⟩⟩ (fun j => e (e.symm ((eR R j).val i))) = _
      simp only [Equiv.apply_symm_apply]
    have hpol := (hV ⟨R, ⟨t, ht⟩⟩).2 R (fun j => (eR R j).val) (fun j => (eR R j).property)
    have h3 : (fun v => ζU v (fun i => e i)) ∘ t =
        fun c => ζV ⟨R, ⟨t, ht⟩⟩ (fun l => (eR R l).val c) := funext key
    exact cast (congrArg (fun s => s ∈ 𝔹₂.rel R) h3).symm hpol
  tfae_have 4 → 5 := by
    rintro ⟨c, hc⟩
    exact P0082.four_to_five 𝔸₁ 𝔹₁ 𝔸₂ 𝔹₂ hne h₁ e m eR c hc
  tfae_have 5 → 6 := by
    rintro ⟨N, 𝔸', 𝔹', hpow, hrel⟩
    have h1 := PPConstructible.power (PPConstructible.refl (T := Template.of 𝔸₁ 𝔹₁ har₁))
      N τ₂ ar₂ har₂ 𝔸' 𝔹' hpow
    exact PPConstructible.relax h1 A₂ B₂ 𝔸₂ 𝔹₂ h₂ hrel
  tfae_have 6 → 1 := by
    intro h
    obtain ⟨ξ, hξ⟩ := P0082.polHom_of_ppc _ _ h
    exact ⟨ξ, fun π g hg => hξ π g hg _⟩
  tfae_finish
