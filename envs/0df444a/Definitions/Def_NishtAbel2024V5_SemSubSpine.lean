-- Prove2me | Definitions.Def_NishtAbel2024V5_SemSubSpine
-- name    : NishtAbel2024V5_SemSubSpine
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-07T04:27:28.279782+00:00
-- url     : https://prove2.me/theorems/89428c89-21a1-4963-abc9-50ec6a57f074
-- title:
--   Chapter 5.3–5.4 (V5 Support): Soundness of Higher-Kinded Subtyping, Pattern Matching, and Semantic Copattern Spines
-- statement:
--   Proves semantic soundness of polarized higher-kinded subtyping (`subTy_sound`, Theorem 2 part 3, including $\beta$-conversion and mixed-variance fixpoints), semantic pattern matching (`SemPat`), semantic copattern elimination spines (`SemSpine`), and strong normalization of copattern lambda abstractions (`ClauseHead`).
-- source:
--   Nisht & Abel 2024, Kind Inference and Termination Checking in a Language with Co-Patterns and Size-Change Termination, https://urn.kb.se/resolve?urn=urn:nbn:se:chalmers:diva-542843, Chapter 5, Sections 5.3-5.4, pp. 35-37, Theorems 2-3

import Definitions.Def_NishtAbel2024V5_SemKinding
import Mathlib.Data.Fintype.Card

/-! ## Solutions/V5/SubSound.lean -/

/-! # V5: valuation updates, semantic opening, and soundness of subtyping -/

namespace NishtAbel2024V5

/-! ## Valuation updates -/

def SizeVal.update (ρ : SizeVal) (j : Nat) (β : Ordinal.{0}) : SizeVal :=
  fun i => if i = j then β else ρ i

def TEnv.update (θ : TEnv) (X : Nat) (P : PSem) : TEnv :=
  fun Y => if Y = X then P else θ Y

theorem SizeVal.update_agree {ρ : SizeVal} {j : Nat} {β : Ordinal.{0}} {Ψ : SizeCtx}
    (hj : j ∉ Ψ.dom) : ∀ i ∈ Ψ.dom, SizeVal.update ρ j β i = ρ i := by
  intro i hi
  have : i ≠ j := fun h => hj (h ▸ hi)
  simp [SizeVal.update, this]

theorem TEnv.update_agree {θ : TEnv} {X : Nat} {P : PSem} {Θ : List Nat} (hX : X ∉ Θ) :
    ∀ Y ∈ Θ, TEnv.update θ X P Y = θ Y := by
  intro Y hY
  have : Y ≠ X := fun h => hX (h ▸ hY)
  simp [TEnv.update, this]

@[simp] theorem TEnv.update_self (θ : TEnv) (X : Nat) (P : PSem) : TEnv.update θ X P X = P := by
  simp [TEnv.update]

@[simp] theorem SizeVal.update_self (ρ : SizeVal) (j : Nat) (β : Ordinal.{0}) :
    SizeVal.update ρ j β j = β := by
  simp [SizeVal.update]

/-- Every bound of the context is well-formed in the context. -/
def CtxBoundsWf (Ψ : SizeCtx) : Prop := ∀ p ∈ Ψ, SizeWf Ψ p.2

theorem ValidVal.agree {Ψ : SizeCtx} {ρ ρ' : SizeVal} (hv : ValidVal Ψ ρ) (hb : CtxBoundsWf Ψ)
    (hag : ∀ i ∈ Ψ.dom, ρ' i = ρ i) : ValidVal Ψ ρ' := by
  intro p hp
  have hi : p.1 ∈ Ψ.dom := SizeCtx.mem_dom (a := p.2) (by simpa using hp)
  rw [hag _ hi, sizeVal_agree (fun i h => hag i h) (fun _ h => absurd h (Nat.not_lt_zero _))
    (hb p hp)]
  exact hv p hp

theorem ValidVal.extend {Ψ : SizeCtx} {ρ : SizeVal} (hv : ValidVal Ψ ρ) (hb : CtxBoundsWf Ψ)
    {j : Nat} (hj : j ∉ Ψ.dom) {a : Size} (ha : SizeWf Ψ a) {β : Ordinal.{0}}
    (hβ : β < sizeVal ρ SzEnv.zero a) :
    ValidVal (Ψ ++ [(j, a)]) (SizeVal.update ρ j β) := by
  have hag := SizeVal.update_agree (ρ := ρ) (β := β) hj
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · exact (hv.agree hb hag) p hp
  · simp at hp; subst hp
    simp only [SizeVal.update_self]
    rw [sizeVal_agree hag (fun _ h => absurd h (Nat.not_lt_zero _)) ha]
    exact hβ

theorem CtxBoundsWf.extend {Ψ : SizeCtx} (hb : CtxBoundsWf Ψ) {j : Nat} {a : Size}
    (ha : SizeWf Ψ a) : CtxBoundsWf (Ψ ++ [(j, a)]) := by
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · exact (hb p hp).weaken dom_append_left le_rfl
  · simp at hp; subst hp; exact ha.weaken dom_append_left le_rfl

theorem sizeWf_fresh_var (Ψ : SizeCtx) (j : Nat) (a : Size) :
    SizeWf (Ψ ++ [(j, a)]) (.var j 0) := by
  simp [SizeWf, SizeWfAt, SizeCtx.dom]

/-! ## Lookups in extended kinding contexts -/

theorem KCtx.lookup_append (Δ Δ' : KCtx) (X : Nat) :
    (Δ ++ Δ').lookup X = match Δ.lookup X with
      | some e => some e
      | none => Δ'.lookup X := by
  induction Δ with
  | nil => rfl
  | cons p Δ ih =>
    obtain ⟨Y, e⟩ := p
    by_cases h : X = Y
    · subst h; simp [List.lookup]
    · have hb : (X == Y) = false := by simpa using h
      simp only [List.cons_append, List.lookup, hb]
      exact ih

theorem KCtx.lookup_none_of_not_dom {Δ : KCtx} {X : Nat} (h : X ∉ Δ.dom) : Δ.lookup X = none := by
  cases hl : Δ.lookup X with
  | none => rfl
  | some e => exact absurd (KCtx.lookup_some_dom hl) h

theorem KCtx.lookup_snoc_fresh {Δ : KCtx} {X : Nat} (hX : X ∉ Δ.dom) (e : Pol × Kind) :
    (Δ ++ [(X, e)]).lookup X = some e := by
  rw [KCtx.lookup_append, KCtx.lookup_none_of_not_dom hX]
  simp [List.lookup]

theorem TRel.extend {W : World} {Δ : KCtx} {θ : TEnv} (h : TRel W Δ θ θ) {X : Nat}
    (hX : X ∉ Δ.dom) {π : Pol} {κ : Kind} {Y : Sem κ.erase} (hY : Good W κ Y) :
    TRel W (Δ ++ [(X, π, κ)]) (TEnv.update θ X (PSem.ofSem κ.erase Y))
      (TEnv.update θ X (PSem.ofSem κ.erase Y)) := by
  intro Z π' κ' hZ
  rw [KCtx.lookup_append] at hZ
  cases hl : Δ.lookup Z with
  | some e =>
    rw [hl] at hZ
    simp only [Option.some.injEq] at hZ
    subst hZ
    have hZX : Z ≠ X := fun h => hX (h ▸ KCtx.lookup_some_dom hl)
    simp only [TEnv.update, hZX, if_false]
    exact h Z π' κ' hl
  | none =>
    rw [hl] at hZ
    by_cases hZX : Z = X
    · subst hZX
      simp [List.lookup] at hZ
      obtain ⟨rfl, rfl⟩ := hZ
      simp only [TEnv.update_self, PSem.ofSem_self]
      exact ⟨hY, hY, PolRel.refl _ hY⟩
    · have hb : (Z == X) = false := by simpa using hZX
      simp [List.lookup, hb] at hZ

theorem TRel.agree {W : World} {Δ : KCtx} {θ θ' : TEnv} (h : TRel W Δ θ θ)
    (hag : ∀ X ∈ Δ.dom, θ' X = θ X) : TRel W Δ θ' θ' := by
  intro X π κ hX
  rw [hag X (KCtx.lookup_some_dom hX)]
  exact h X π κ hX

/-! ## Opening at fresh variables -/

/-- Opening a type binder at a fresh free type variable. -/
theorem interp_open_fresh_ty {W : World} {Ψ : SizeCtx} {Θ : List Nat} {ρ : SizeVal} {θ : TEnv}
    {m : Nat} {B : Ty} (hB : TyWf Ψ Θ 1 m B) {X : Nat} (hX : X ∉ Θ) (P : PSem) (ι : SKind)
    (ζ : SzEnv) (η : Env) :
    interp W ρ (TEnv.update θ X P) (B.substTy 0 (.fvar X)) ι ζ η =
      interp W ρ θ B ι ζ (Env.cons P η) := by
  rw [interp_openTy (T := .fvar X) (fun _ _ _ _ _ => rfl)]
  have h1 : tyVal W ρ (TEnv.update θ X P) (.fvar X) ζ η = P := by
    funext ι'
    simp [tyVal, interp]
  rw [h1]
  exact interp_agree hB ρ ρ _ θ _ _ _ _ (fun _ _ => rfl) (TEnv.update_agree hX) (fun _ _ => rfl)
    (fun n hn => by cases n with | zero => rfl | succ n => omega) ι

/-- Opening a size binder at a fresh free size variable. -/
theorem interp_open_fresh_sz {W : World} {Ψ : SizeCtx} {Θ : List Nat} {ρ : SizeVal} {θ : TEnv}
    {k : Nat} {B : Ty} (hB : TyWf Ψ Θ k 1 B) {j : Nat} (hj : j ∉ Ψ.dom) (β : Ordinal.{0})
    (ι : SKind) (η : Env) :
    interp W (SizeVal.update ρ j β) θ (B.openSz 0 (.var j 0)) ι SzEnv.zero η =
      interp W ρ θ B ι (SzEnv.cons β SzEnv.zero) η := by
  rw [interp_openSz0 W _ θ (b := .var j 0) trivial]
  have h1 : sizeVal (SizeVal.update ρ j β) SzEnv.zero (.var j 0) = β := by
    simp [sizeVal, SizeVal.update]
  rw [h1]
  exact interp_agree hB _ ρ θ θ _ _ _ _ (SizeVal.update_agree hj) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) ι

/-! ## Casts between equal simple kinds -/

theorem PSem.ofSem_cast {ι ι' : SKind} (e : ι = ι') (X : Sem ι) :
    PSem.ofSem ι' (cast (congrArg Sem e) X) = PSem.ofSem ι X := by
  subst e; rfl

theorem good_cast {W : World} {κ : Kind} {ι ι' : SKind} (e : ι = ι') (X : Sem ι) :
    Good W κ (cast (congrArg Sem e) X) ↔ Good W κ X := by
  subst e; rfl

/-! ## β-conversion -/

theorem interp_beta {W : World} {Ψ : SizeCtx} {Δ : KCtx} {F G : Ty} {ι : SKind} {κ : Kind}
    (hk : KindingC Ψ Δ (.app (.lam ι F) G ι) κ) (ρ : SizeVal) (θ : TEnv) :
    interp W ρ θ (.app (.lam ι F) G ι) κ.erase SzEnv.zero Env.empty =
      interp W ρ θ (F.substTy 0 G) κ.erase SzEnv.zero Env.empty := by
  obtain ⟨π, κ₁, κ₂, hF, hG, hι, hs⟩ := Kinding.inv_app hk
  obtain ⟨π', κ₁', κ₂', hι', hF', hs'⟩ := Kinding.inv_lam hF
  have e₂ : κ₂'.erase = κ.erase := by
    cases hs' with
    | arr _ _ h2 => exact h2.erase_eq.trans hs.erase_eq
  have hGc : TyWf Ψ (Δ.inv π).dom 0 0 G := hG.tyWf
  rw [interp_app, interp_openTy (envFree_of_closed hGc ρ θ), ← e₂, interp_lam_arr]
  apply interp_agree_kinded hF' ρ θ θ SzEnv.zero
  · intros; rfl
  · intro k π'' κ'' hk
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hk
      obtain ⟨rfl, rfl⟩ := hk
      subst hι
      rw [hι']
      simp [tyVal]
    | succ k => simp at hk

/-! ## Functors of fixpoints -/

theorem functor_cand {W : World} (hW : WorldClosed W) {Ψ : SizeCtx} {Δ : KCtx} {R : List Ty}
    {ρ : SizeVal} {θ : TEnv} {π : Pol} (hθ : TRel W Δ θ θ)
    (hR : ∀ T ∈ R, Kinding Ψ (Δ.inv π) ((π, .star) :: BCtx.inv π []) 0 T .star) :
    ∀ d < R.length, ∀ 𝒳, Cand W 𝒳 →
      Cand W (interpAt W ρ θ R d SzEnv.zero (Env.cons (PSem.ofSem .star 𝒳) Env.empty)) := by
  intro d hd 𝒳 h𝒳
  rw [interpAt_eq W ρ θ R d _ _ hd]
  have hBnil : BRel W (BCtx.inv π []) Env.empty Env.empty := fun _ _ _ hk => by simp at hk
  exact (kinding_sound hW (hR _ (List.getElem_mem hd)) ρ θ θ SzEnv.zero _ _ (hθ.inv_refl π)
    (hBnil.cons (κ := .star) h𝒳 h𝒳 (PolRel.refl π (W := W) h𝒳))).1

theorem functor_mono_pos {W : World} (hW : WorldClosed W) {Ψ : SizeCtx} {Δ : KCtx}
    {S : List Ty} {ρ : SizeVal} {θ : TEnv} (hθ : TRel W Δ θ θ)
    (hpos : ∀ T ∈ S, Kinding Ψ Δ [(.pos, .star)] 0 T .star) :
    ∀ c 𝒳 𝒴, Cand W 𝒳 → Cand W 𝒴 → 𝒳 ⊆ 𝒴 →
      interpAt W ρ θ S c SzEnv.zero (Env.cons (PSem.ofSem .star 𝒳) Env.empty) ⊆
        interpAt W ρ θ S c SzEnv.zero (Env.cons (PSem.ofSem .star 𝒴) Env.empty) := by
  intro c 𝒳 𝒴 h𝒳 h𝒴 hsub
  by_cases hc : c < S.length
  · rw [interpAt_eq W ρ θ S c _ _ hc, interpAt_eq W ρ θ S c _ _ hc]
    have hBnil : BRel W [] Env.empty Env.empty := fun _ _ _ hk => by simp at hk
    exact (kinding_sound hW (hpos _ (List.getElem_mem hc)) ρ θ θ SzEnv.zero _ _ hθ
      (hBnil.cons (κ := .star) h𝒳 h𝒴 hsub)).2.2
  · rw [interpAt_out W ρ θ S c _ _ (by omega)]
    exact Set.empty_subset _

theorem functor_le {W : World} {Ψ : SizeCtx} {Δ : KCtx} {X : Nat} {S S' : List Ty}
    {ρ : SizeVal} {θ : TEnv} (hX : X ∉ Δ.dom) (hlen : S.length = S'.length)
    (hSw : ∀ T ∈ S, TyWf Ψ Δ.dom 1 0 T) (hSw' : ∀ T ∈ S', TyWf Ψ Δ.dom 1 0 T)
    (hv : ValidVal Ψ ρ) (hb : CtxBoundsWf Ψ) (hθ : TRel W Δ θ θ)
    (ih : ∀ (c : Nat) (T T' : Ty), S[c]? = some T → S'[c]? = some T' →
      ∀ (ρ : SizeVal) (θ : TEnv), ValidVal Ψ ρ → CtxBoundsWf Ψ →
        TRel W (Δ ++ [(X, .mix, .star)]) θ θ →
        KSound W .star (interp W ρ θ (T.substTy 0 (.fvar X)) Kind.star.erase SzEnv.zero Env.empty)
          (interp W ρ θ (T'.substTy 0 (.fvar X)) Kind.star.erase SzEnv.zero Env.empty)) :
    ∀ c 𝒳, Cand W 𝒳 →
      interpAt W ρ θ S c SzEnv.zero (Env.cons (PSem.ofSem .star 𝒳) Env.empty) ⊆
        interpAt W ρ θ S' c SzEnv.zero (Env.cons (PSem.ofSem .star 𝒳) Env.empty) := by
  intro c 𝒳 h𝒳
  by_cases hc : c < S.length
  · have hc' : c < S'.length := hlen ▸ hc
    rw [interpAt_eq W ρ θ S c _ _ hc, interpAt_eq W ρ θ S' c _ _ hc']
    have h := ih c _ _ (List.getElem?_eq_getElem hc) (List.getElem?_eq_getElem hc') ρ
      (TEnv.update θ X (PSem.ofSem Kind.star.erase 𝒳)) hv hb (hθ.extend hX (κ := .star) h𝒳)
    simp only [Kind.erase_star] at h
    rw [interp_open_fresh_ty (hSw _ (List.getElem_mem hc)) hX,
      interp_open_fresh_ty (hSw' _ (List.getElem_mem hc')) hX] at h
    exact h.2.2
  · rw [interpAt_out W ρ θ S c _ _ (by omega)]
    exact Set.empty_subset _

/-- Stages of `μ` are ordered along bound normalization. -/
theorem muSet_up_mono {W : World} {F : Nat → Set Tm → Set Tm} {ρ : SizeVal} {a b : Size}
    (h : sizeVal ρ SzEnv.zero a.up ≤ sizeVal ρ SzEnv.zero b.up ∨
      sizeVal ρ SzEnv.zero a ≤ sizeVal ρ SzEnv.zero b.up) :
    MuSet W F (sizeVal ρ SzEnv.zero a) ⊆ MuSet W F (sizeVal ρ SzEnv.zero b) := by
  have h' : sizeVal ρ SzEnv.zero a ≤ sizeVal ρ SzEnv.zero b ∨
      (Omega ≤ sizeVal ρ SzEnv.zero a ∧ Omega ≤ sizeVal ρ SzEnv.zero b) := by
    rcases h with h | h
    · exact le_of_up_le ρ SzEnv.zero a b h
    · exact le_of_le_up ρ SzEnv.zero a b h
  rcases h' with hab | ⟨ha, hb⟩
  · exact muSet_mono_ord hab
  · rw [muSet_ge_omega W F ha, muSet_ge_omega W F hb]

theorem nuSet_up_anti {W : World} {n : Nat} {G : Nat → Set Tm → Set Tm} {ρ : SizeVal}
    {a b : Size} (h : sizeVal ρ SzEnv.zero b.up ≤ sizeVal ρ SzEnv.zero a.up ∨
      sizeVal ρ SzEnv.zero b ≤ sizeVal ρ SzEnv.zero a.up) :
    NuSet W n G (sizeVal ρ SzEnv.zero a) ⊆ NuSet W n G (sizeVal ρ SzEnv.zero b) := by
  have h' : sizeVal ρ SzEnv.zero b ≤ sizeVal ρ SzEnv.zero a ∨
      (Omega ≤ sizeVal ρ SzEnv.zero b ∧ Omega ≤ sizeVal ρ SzEnv.zero a) := by
    rcases h with h | h
    · exact le_of_up_le ρ SzEnv.zero b a h
    · exact le_of_le_up ρ SzEnv.zero b a h
  rcases h' with hba | ⟨hb, ha⟩
  · exact nuSet_anti_ord hba
  · rw [nuSet_ge_omega W n G ha, nuSet_ge_omega W n G hb]

/-! ## Soundness of subtyping -/

theorem subTy_sound {W : World} (hW : WorldClosed W) {Ψ : SizeCtx} {Δ : KCtx} {A B : Ty}
    {κ : Kind} (h : SubTy Ψ Δ A B κ) :
    ∀ (ρ : SizeVal) (θ : TEnv), ValidVal Ψ ρ → CtxBoundsWf Ψ → TRel W Δ θ θ →
      KSound W κ (interp W ρ θ A κ.erase SzEnv.zero Env.empty)
        (interp W ρ θ B κ.erase SzEnv.zero Env.empty) := by
  have hBnil : ∀ η η' : Env, BRel W [] η η' := fun _ _ k _ _ hk => by simp at hk
  induction h with
  | refl hA =>
    intro ρ θ _ _ hθ
    exact kinding_sound hW hA ρ θ θ SzEnv.zero Env.empty Env.empty hθ (hBnil _ _)
  | trans _ _ ih₁ ih₂ =>
    intro ρ θ hv hb hθ
    have h₁ := ih₁ ρ θ hv hb hθ
    have h₂ := ih₂ ρ θ hv hb hθ
    exact ⟨h₁.1, h₂.2.1, SemLe.trans h₁.1 h₁.2.1 h₂.2.1 h₁.2.2 h₂.2.2⟩
  | beta_l hk _ ih =>
    intro ρ θ hv hb hθ
    rw [interp_beta hk ρ θ]
    exact ih ρ θ hv hb hθ
  | beta_r hk _ ih =>
    intro ρ θ hv hb hθ
    rw [interp_beta hk ρ θ]
    exact ih ρ θ hv hb hθ
  | prod _ _ ihA ihB =>
    intro ρ θ hv hb hθ
    have hA := ihA ρ θ hv hb hθ
    have hB := ihB ρ θ hv hb hθ
    simp only [Kind.erase_star, interp_prod_star] at hA hB ⊢
    exact ⟨introSet_cand hW _, introSet_cand hW _, prodSet_mono hA.2.2 hB.2.2⟩
  | arr _ _ ihA ihB =>
    intro ρ θ hv hb hθ
    have hA := ihA ρ θ hv hb hθ
    have hB := ihB ρ θ hv hb hθ
    simp only [Kind.erase_star, interp_arr_star] at hA hB ⊢
    exact ⟨arrSet_cand hW hA.2.1 hB.1, arrSet_cand hW hA.1 hB.2.1, arrSet_mono hA.2.2 hB.2.2⟩
  | @app Ψ Δ F F' G G' ι π κ₁ κ₂ _ _ _ hG hG' hι ihF ihGpos ihGneg =>
    intro ρ θ hv hb hθ
    subst hι
    have hF := ihF ρ θ hv hb hθ
    simp only [Kind.erase_arr] at hF
    have hGs := kinding_sound hW hG ρ θ θ SzEnv.zero Env.empty Env.empty (hθ.inv_refl π)
      (hBnil _ _)
    have hGs' := kinding_sound hW hG' ρ θ θ SzEnv.zero Env.empty Env.empty (hθ.inv_refl π)
      (hBnil _ _)
    have hrel : PolRel W π κ₁ (interp W ρ θ G κ₁.erase SzEnv.zero Env.empty)
        (interp W ρ θ G' κ₁.erase SzEnv.zero Env.empty) := by
      cases π with
      | pos => exact (ihGpos trivial ρ θ hv hb hθ).2.2
      | neg => exact (ihGneg trivial ρ θ hv hb hθ).2.2
      | mix => exact ⟨(ihGpos trivial ρ θ hv hb hθ).2.2, (ihGneg trivial ρ θ hv hb hθ).2.2⟩
      | top => trivial
    rw [interp_app, interp_app]
    exact ⟨hF.1.1 _ hGs.1, hF.2.1.1 _ hGs'.1, hF.2.2 _ _ hGs.1 hGs'.1 hrel⟩
  | @lam Ψ Δ F F' ι ι' π κ₁ κ₂ X hX _ hk hk' ih =>
    intro ρ θ hv hb hθ
    have hs := kinding_sound hW hk ρ θ θ SzEnv.zero Env.empty Env.empty hθ (hBnil _ _)
    have hs' := kinding_sound hW hk' ρ θ θ SzEnv.zero Env.empty Env.empty hθ (hBnil _ _)
    refine ⟨hs.1, hs'.1, ?_⟩
    obtain ⟨π₁, κ₁₁, κ₂₁, _, hFk, _⟩ := Kinding.inv_lam hk
    obtain ⟨π₂, κ₁₂, κ₂₂, _, hFk', _⟩ := Kinding.inv_lam hk'
    have hFw : TyWf Ψ Δ.dom 1 0 F := by simpa using hFk.tyWf
    have hFw' : TyWf Ψ Δ.dom 1 0 F' := by simpa using hFk'.tyWf
    have hgF : ∀ Y : Sem κ₁.erase, Good W κ₁ Y → Good W κ₂
        (interp W ρ θ F κ₂.erase SzEnv.zero (Env.cons (PSem.ofSem κ₁.erase Y) Env.empty)) :=
      fun Y hY => hs.1.1 Y hY
    have hgF' : ∀ Y : Sem κ₁.erase, Good W κ₁ Y → Good W κ₂
        (interp W ρ θ F' κ₂.erase SzEnv.zero (Env.cons (PSem.ofSem κ₁.erase Y) Env.empty)) :=
      fun Y hY => hs'.1.1 Y hY
    have hmF' : ∀ Y Z : Sem κ₁.erase, Good W κ₁ Y → Good W κ₁ Z → PolRel W π κ₁ Y Z →
        SemLe W κ₂
          (interp W ρ θ F' κ₂.erase SzEnv.zero (Env.cons (PSem.ofSem κ₁.erase Y) Env.empty))
          (interp W ρ θ F' κ₂.erase SzEnv.zero (Env.cons (PSem.ofSem κ₁.erase Z) Env.empty)) :=
      fun Y Z hY hZ hYZ => hs'.1.2 Y Z hY hZ hYZ
    intro Y Z hY hZ hYZ
    have hY' := ih ρ (TEnv.update θ X (PSem.ofSem κ₁.erase Y)) hv hb (hθ.extend hX hY)
    rw [interp_open_fresh_ty hFw hX, interp_open_fresh_ty hFw' hX] at hY'
    exact SemLe.trans (hgF Y hY) (hgF' Y hY) (hgF' Z hZ) hY'.2.2 (hmF' Y Z hY hZ hYZ)
  | @allT Ψ Δ κ κ' B B' X hsub hX _ hk hk' ih =>
    intro ρ θ hv hb hθ
    have hs := kinding_sound hW hk ρ θ θ SzEnv.zero Env.empty Env.empty hθ (hBnil _ _)
    have hs' := kinding_sound hW hk' ρ θ θ SzEnv.zero Env.empty Env.empty hθ (hBnil _ _)
    refine ⟨hs.1, hs'.1, ?_⟩
    simp only [Kind.erase_star, interp_allT_star]
    have hBw : TyWf Ψ Δ.dom 1 0 B := by simpa using (Kinding.inv_allT hk).2.tyWf
    have hBw' : TyWf Ψ Δ.dom 1 0 B' := by simpa using (Kinding.inv_allT hk').2.tyWf
    intro t ht
    refine ⟨ht.1, fun Y hY => ?_⟩
    have e := hsub.erase_eq
    have hY' : Good W κ' (cast (congrArg Sem e) Y) := (good_cast e Y).mpr (Good.sub hsub hY)
    have h1 : Tm.app t .inst ∈
        interpT W ρ θ B SzEnv.zero (Env.cons (PSem.ofSem κ.erase Y) Env.empty) := by
      have := ht.2 _ hY'
      rw [← PSem.ofSem_cast e Y]
      exact this
    have hih := ih ρ (TEnv.update θ X (PSem.ofSem κ.erase Y)) hv hb (hθ.extend hX hY)
    simp only [Kind.erase_star] at hih
    rw [interp_open_fresh_ty hBw hX, interp_open_fresh_ty hBw' hX] at hih
    exact hih.2.2 h1
  | @exT Ψ Δ κ κ' B B' X hsub hX _ hk hk' ih =>
    intro ρ θ hv hb hθ
    have hs := kinding_sound hW hk ρ θ θ SzEnv.zero Env.empty Env.empty hθ (hBnil _ _)
    have hs' := kinding_sound hW hk' ρ θ θ SzEnv.zero Env.empty Env.empty hθ (hBnil _ _)
    refine ⟨hs.1, hs'.1, ?_⟩
    simp only [Kind.erase_star, interp_exT_star]
    have hBw : TyWf Ψ Δ.dom 1 0 B := by simpa using (Kinding.inv_exT hk).2.tyWf
    have hBw' : TyWf Ψ Δ.dom 1 0 B' := by simpa using (Kinding.inv_exT hk').2.tyWf
    apply introSet_mono
    rintro v ⟨t, Y, rfl, hY, ht⟩
    have e := hsub.erase_eq
    refine ⟨t, cast (congrArg Sem e) Y, rfl, (good_cast e Y).mpr (Good.sub hsub hY), ?_⟩
    have hih := ih ρ (TEnv.update θ X (PSem.ofSem κ.erase Y)) hv hb (hθ.extend hX hY)
    simp only [Kind.erase_star] at hih
    rw [interp_open_fresh_ty hBw hX, interp_open_fresh_ty hBw' hX] at hih
    have h2 : t ∈ interpT W ρ θ B' SzEnv.zero (Env.cons (PSem.ofSem κ.erase Y) Env.empty) :=
      hih.2.2 ht
    rw [← PSem.ofSem_cast e Y] at h2
    exact h2
  | @allS Ψ Δ a b B B' j hle hj _ hk hk' ih =>
    intro ρ θ hv hb hθ
    have hs := kinding_sound hW hk ρ θ θ SzEnv.zero Env.empty Env.empty hθ (hBnil _ _)
    have hs' := kinding_sound hW hk' ρ θ θ SzEnv.zero Env.empty Env.empty hθ (hBnil _ _)
    refine ⟨hs.1, hs'.1, ?_⟩
    simp only [Kind.erase_star, interp_allS_star]
    obtain ⟨_, ha, hBk⟩ := Kinding.inv_allS hk
    obtain ⟨_, hbw, hBk'⟩ := Kinding.inv_allS hk'
    have hBw := hBk.tyWf
    have hBw' := hBk'.tyWf
    have hba := sizeLe_sound hv hle
    intro t ht
    refine ⟨ht.1, fun β hβ => ?_⟩
    have h1 := ht.2 β (lt_of_lt_of_le hβ hba)
    have hih := ih (SizeVal.update ρ j β) θ (hv.extend hb hj hbw hβ) (hb.extend hbw) hθ
    simp only [Kind.erase_star] at hih
    rw [interp_open_fresh_sz hBw hj, interp_open_fresh_sz hBw' hj] at hih
    exact hih.2.2 h1
  | @exS Ψ Δ a b B B' j hle hj _ hk hk' ih =>
    intro ρ θ hv hb hθ
    have hs := kinding_sound hW hk ρ θ θ SzEnv.zero Env.empty Env.empty hθ (hBnil _ _)
    have hs' := kinding_sound hW hk' ρ θ θ SzEnv.zero Env.empty Env.empty hθ (hBnil _ _)
    refine ⟨hs.1, hs'.1, ?_⟩
    simp only [Kind.erase_star, interp_exS_star]
    obtain ⟨_, ha, hBk⟩ := Kinding.inv_exS hk
    obtain ⟨_, hbw, hBk'⟩ := Kinding.inv_exS hk'
    have hBw := hBk.tyWf
    have hBw' := hBk'.tyWf
    have hab := sizeLe_sound hv hle
    apply introSet_mono
    rintro v ⟨t, β, rfl, hβ, ht⟩
    refine ⟨t, β, rfl, lt_of_lt_of_le hβ hab, ?_⟩
    have hih := ih (SizeVal.update ρ j β) θ (hv.extend hb hj ha hβ) (hb.extend ha) hθ
    simp only [Kind.erase_star] at hih
    rw [interp_open_fresh_sz hBw hj, interp_open_fresh_sz hBw' hj] at hih
    exact hih.2.2 ht
  | @mu_pos Ψ Δ a b S S' X hle hlen hX _ hpos hk hk' ih =>
    intro ρ θ hv hb hθ
    have hs := kinding_sound hW hk ρ θ θ SzEnv.zero Env.empty Env.empty hθ (hBnil _ _)
    have hs' := kinding_sound hW hk' ρ θ θ SzEnv.zero Env.empty Env.empty hθ (hBnil _ _)
    refine ⟨hs.1, hs'.1, ?_⟩
    simp only [Kind.erase_star, interp_mu_star]
    obtain ⟨_, π, _, _, hS⟩ := Kinding.inv_mu hk
    obtain ⟨_, π', _, _, hS'⟩ := Kinding.inv_mu hk'
    have hSw : ∀ T ∈ S, TyWf Ψ Δ.dom 1 0 T := fun T hT => by simpa using (hS T hT).tyWf
    have hSw' : ∀ T ∈ S', TyWf Ψ Δ.dom 1 0 T := fun T hT => by simpa using (hS' T hT).tyWf
    have hle' := hle.imp (sizeLe_sound hv) (sizeLe_sound hv)
    refine Set.Subset.trans (muSet_mono_cand hW ?_ _) (muSet_up_mono hle')
    intro c 𝒳 𝒴 h𝒳 h𝒴 hsub
    exact Set.Subset.trans (functor_le hX hlen hSw hSw' hv hb hθ ih c 𝒳 h𝒳)
      (functor_mono_pos hW hθ hpos c 𝒳 𝒴 h𝒳 h𝒴 hsub)
  | @mu_eqv Ψ Δ a b S S' X hle hlen hX _ _ hk hk' ih₁ ih₂ =>
    intro ρ θ hv hb hθ
    have hs := kinding_sound hW hk ρ θ θ SzEnv.zero Env.empty Env.empty hθ (hBnil _ _)
    have hs' := kinding_sound hW hk' ρ θ θ SzEnv.zero Env.empty Env.empty hθ (hBnil _ _)
    refine ⟨hs.1, hs'.1, ?_⟩
    simp only [Kind.erase_star, interp_mu_star]
    obtain ⟨_, π, _, _, hS⟩ := Kinding.inv_mu hk
    obtain ⟨_, π', _, _, hS'⟩ := Kinding.inv_mu hk'
    have hSw : ∀ T ∈ S, TyWf Ψ Δ.dom 1 0 T := fun T hT => by simpa using (hS T hT).tyWf
    have hSw' : ∀ T ∈ S', TyWf Ψ Δ.dom 1 0 T := fun T hT => by simpa using (hS' T hT).tyWf
    have hle' := hle.imp (sizeLe_sound hv) (sizeLe_sound hv)
    have ih₂' : ∀ (c : Nat) (T T' : Ty), S'[c]? = some T → S[c]? = some T' →
        ∀ (ρ : SizeVal) (θ : TEnv), ValidVal Ψ ρ → CtxBoundsWf Ψ →
          TRel W (Δ ++ [(X, .mix, .star)]) θ θ →
          KSound W .star
            (interp W ρ θ (T.substTy 0 (.fvar X)) Kind.star.erase SzEnv.zero Env.empty)
            (interp W ρ θ (T'.substTy 0 (.fvar X)) Kind.star.erase SzEnv.zero Env.empty) :=
      fun c T T' h1 h2 => ih₂ c T' T h2 h1
    refine Set.Subset.trans (subset_of_eq (muSet_congr_cand hW ?_ _)) (muSet_up_mono hle')
    intro c 𝒳 h𝒳
    exact Set.Subset.antisymm (functor_le hX hlen hSw hSw' hv hb hθ ih₁ c 𝒳 h𝒳)
      (functor_le hX hlen.symm hSw' hSw hv hb hθ ih₂' c 𝒳 h𝒳)
  | @nu_pos Ψ Δ a b R R' X hle hlen hX _ hpos hk hk' ih =>
    intro ρ θ hv hb hθ
    have hs := kinding_sound hW hk ρ θ θ SzEnv.zero Env.empty Env.empty hθ (hBnil _ _)
    have hs' := kinding_sound hW hk' ρ θ θ SzEnv.zero Env.empty Env.empty hθ (hBnil _ _)
    refine ⟨hs.1, hs'.1, ?_⟩
    simp only [Kind.erase_star, interp_nu_star]
    obtain ⟨_, π, _, _, hR⟩ := Kinding.inv_nu hk
    obtain ⟨_, π', _, _, hR'⟩ := Kinding.inv_nu hk'
    have hRw : ∀ T ∈ R, TyWf Ψ Δ.dom 1 0 T := fun T hT => by simpa using (hR T hT).tyWf
    have hRw' : ∀ T ∈ R', TyWf Ψ Δ.dom 1 0 T := fun T hT => by simpa using (hR' T hT).tyWf
    have hle' := hle.imp (sizeLe_sound hv) (sizeLe_sound hv)
    rw [← hlen]
    refine Set.Subset.trans (nuSet_mono_cand hW (functor_cand hW hθ hR)
      (hlen ▸ functor_cand hW hθ hR') ?_ _) (nuSet_up_anti hle')
    intro d _ 𝒳 𝒴 h𝒳 h𝒴 hsub
    exact Set.Subset.trans (functor_le hX hlen hRw hRw' hv hb hθ ih d 𝒳 h𝒳)
      (functor_mono_pos hW hθ hpos d 𝒳 𝒴 h𝒳 h𝒴 hsub)
  | @nu_eqv Ψ Δ a b R R' X hle hlen hX _ _ hk hk' ih₁ ih₂ =>
    intro ρ θ hv hb hθ
    have hs := kinding_sound hW hk ρ θ θ SzEnv.zero Env.empty Env.empty hθ (hBnil _ _)
    have hs' := kinding_sound hW hk' ρ θ θ SzEnv.zero Env.empty Env.empty hθ (hBnil _ _)
    refine ⟨hs.1, hs'.1, ?_⟩
    simp only [Kind.erase_star, interp_nu_star]
    obtain ⟨_, π, _, _, hR⟩ := Kinding.inv_nu hk
    obtain ⟨_, π', _, _, hR'⟩ := Kinding.inv_nu hk'
    have hRw : ∀ T ∈ R, TyWf Ψ Δ.dom 1 0 T := fun T hT => by simpa using (hR T hT).tyWf
    have hRw' : ∀ T ∈ R', TyWf Ψ Δ.dom 1 0 T := fun T hT => by simpa using (hR' T hT).tyWf
    have hle' := hle.imp (sizeLe_sound hv) (sizeLe_sound hv)
    have ih₂' : ∀ (c : Nat) (T T' : Ty), R'[c]? = some T → R[c]? = some T' →
        ∀ (ρ : SizeVal) (θ : TEnv), ValidVal Ψ ρ → CtxBoundsWf Ψ →
          TRel W (Δ ++ [(X, .mix, .star)]) θ θ →
          KSound W .star
            (interp W ρ θ (T.substTy 0 (.fvar X)) Kind.star.erase SzEnv.zero Env.empty)
            (interp W ρ θ (T'.substTy 0 (.fvar X)) Kind.star.erase SzEnv.zero Env.empty) :=
      fun c T T' h1 h2 => ih₂ c T' T h2 h1
    rw [← hlen]
    refine Set.Subset.trans (subset_of_eq (nuSet_congr_cand hW (functor_cand hW hθ hR) ?_ _))
      (nuSet_up_anti hle')
    intro d _ 𝒳 h𝒳
    exact Set.Subset.antisymm (functor_le hX hlen hRw hRw' hv hb hθ ih₁ d 𝒳 h𝒳)
      (functor_le hX hlen.symm hRw' hRw hv hb hθ ih₂' d 𝒳 h𝒳)

end NishtAbel2024V5

/-! ## Solutions/V5/Match.lean -/

/-! # V5: semantic contexts and pattern matching soundness -/

namespace NishtAbel2024V5

/-- Free type variables of a typing context denote good values of their kinds. -/
def TEnvOK (W : World) (Θ : TyCtx) (θ : TEnv) : Prop := TRel W Θ.toK θ θ

/-- `σ ∈ ⟦Γ⟧ρθ`: every variable of `Γ` is bound by `σ` to a member of its type, and all values of
`σ` are closed. -/
def SemCtx (W : World) (ρ : SizeVal) (θ : TEnv) (Γ : TermCtx) (σ : TmSubst) : Prop :=
  (∀ x A, Γ.lookup x = some A →
    ∃ v, σ.lookup x = some v ∧ v ∈ interpT W ρ θ A SzEnv.zero Env.empty) ∧
  (∀ x v, σ.lookup x = some v → v.Closed)

/-- Every type in the context is well-kinded. -/
def TermCtxWf (Ψ : SizeCtx) (Θ : TyCtx) (Γ : TermCtx) : Prop :=
  ∀ p ∈ Γ, KindingC Ψ Θ.toK p.2 .star

theorem interp_cand_closed {W : World} (hW : WorldClosed W) {Ψ : SizeCtx} {Θ : TyCtx} {A : Ty}
    (hA : KindingC Ψ Θ.toK A .star) (ρ : SizeVal) {θ : TEnv} (hθ : TEnvOK W Θ θ) :
    Cand W (interpT W ρ θ A SzEnv.zero Env.empty) :=
  (kinding_sound hW hA ρ θ θ SzEnv.zero Env.empty Env.empty hθ
    (fun _ _ _ hk => by simp at hk)).1

theorem interp_closed_mem {W : World} (hW : WorldClosed W) {Ψ : SizeCtx} {Θ : TyCtx} {A : Ty}
    (hA : KindingC Ψ Θ.toK A .star) (ρ : SizeVal) {θ : TEnv} (hθ : TEnvOK W Θ θ) {v : Tm}
    (hv : v ∈ interpT W ρ θ A SzEnv.zero Env.empty) : SNc W v :=
  (interp_cand_closed hW hA ρ hθ).sn v hv

/-! ## Kinding facts for typing contexts -/

theorem KindingC.mono_append {Ψ Ψ' : SizeCtx} {Δ Δ' : KCtx} {A : Ty} {κ : Kind}
    (h : KindingC Ψ Δ A κ) : KindingC (Ψ ++ Ψ') (Δ ++ Δ') A κ :=
  h.mono dom_append_left (fun _ _ h => lookup_append_left h)

theorem KindingC.mono_append_sz {Ψ Ψ' : SizeCtx} {Δ : KCtx} {A : Ty} {κ : Kind}
    (h : KindingC Ψ Δ A κ) : KindingC (Ψ ++ Ψ') Δ A κ :=
  h.mono dom_append_left (fun _ _ h => h)

theorem KindingC.mono_append_ty {Ψ : SizeCtx} {Δ Δ' : KCtx} {A : Ty} {κ : Kind}
    (h : KindingC Ψ Δ A κ) : KindingC Ψ (Δ ++ Δ') A κ :=
  h.mono (fun _ h => h) (fun _ _ h => lookup_append_left h)

theorem KindingC.unfold_mu {Ψ : SizeCtx} {Δ : KCtx} (hΔ : Δ.AllMix) {a b : Size} {S : List Ty}
    {c : Nat} {Sc : Ty} (hwf : KindingC Ψ Δ (.mu a S) .star) (hc : S[c]? = some Sc)
    (hb : SizeWf Ψ b) : KindingC Ψ Δ (Sc.substTy 0 (.mu b S)) .star := by
  obtain ⟨_, π, hπ, _, hS⟩ := Kinding.inv_mu hwf
  rw [hΔ.inv] at hS
  have hS' : ∀ T ∈ S, Kinding Ψ Δ [(π, .star)] 0 T .star := fun T hT => by simpa using hS T hT
  refine Kinding.open_ty (hS' Sc (List.mem_of_getElem? hc)) hΔ ?_
  exact .mu hπ hb (fun T hT => by rw [hΔ.inv]; simpa using hS' T hT)

theorem KindingC.unfold_nu {Ψ : SizeCtx} {Δ : KCtx} (hΔ : Δ.AllMix) {a b : Size} {R : List Ty}
    {d : Nat} {Rd : Ty} (hwf : KindingC Ψ Δ (.nu a R) .star) (hd : R[d]? = some Rd)
    (hb : SizeWf Ψ b) : KindingC Ψ Δ (Rd.substTy 0 (.nu b R)) .star := by
  obtain ⟨_, π, hπ, _, hR⟩ := Kinding.inv_nu hwf
  rw [hΔ.inv] at hR
  have hR' : ∀ T ∈ R, Kinding Ψ Δ [(π, .star)] 0 T .star := fun T hT => by simpa using hR T hT
  refine Kinding.open_ty (hR' Rd (List.mem_of_getElem? hd)) hΔ ?_
  exact .nu hπ hb (fun T hT => by rw [hΔ.inv]; simpa using hR' T hT)

/-- A fixpoint with its size replaced. -/
theorem KindingC.mu_size {Ψ : SizeCtx} {Δ : KCtx} {a b : Size} {S : List Ty}
    (hwf : KindingC Ψ Δ (.mu a S) .star) (hb : SizeWf Ψ b) : KindingC Ψ Δ (.mu b S) .star := by
  obtain ⟨_, π, hπ, _, hS⟩ := Kinding.inv_mu hwf
  exact .mu hπ hb hS

theorem KindingC.nu_size {Ψ : SizeCtx} {Δ : KCtx} {a b : Size} {R : List Ty}
    (hwf : KindingC Ψ Δ (.nu a R) .star) (hb : SizeWf Ψ b) : KindingC Ψ Δ (.nu b R) .star := by
  obtain ⟨_, π, hπ, _, hR⟩ := Kinding.inv_nu hwf
  exact .nu hπ hb hR

theorem TyCtx.not_mem_toK {Θ : TyCtx} {X : Nat} (hX : X ∉ Θ.map Prod.fst) : X ∉ Θ.toK.dom := by
  simpa using hX

theorem TyCtx.toK_snoc_lookup {Θ : TyCtx} {X : Nat} (hX : X ∉ Θ.map Prod.fst) (κ : Kind) :
    (Θ ++ [(X, κ)]).toK.lookup X = some (.mix, κ) := by
  rw [TyCtx.toK_append]
  exact KCtx.lookup_snoc_fresh (TyCtx.not_mem_toK hX) _

/-- Opening an existential/universal type binder at a fresh type variable. -/
theorem KindingC.open_fresh_ty {Ψ : SizeCtx} {Θ : TyCtx} {κ : Kind} {B : Ty}
    (hB : Kinding Ψ Θ.toK [(.mix, κ)] 0 B .star) {X : Nat} (hX : X ∉ Θ.map Prod.fst) :
    KindingC Ψ (Θ ++ [(X, κ)]).toK (B.substTy 0 (.fvar X)) .star := by
  have hB' : Kinding Ψ (Θ ++ [(X, κ)]).toK [(.mix, κ)] 0 B .star :=
    hB.weaken (fun _ h => h) (fun _ _ h => by rw [TyCtx.toK_append]; exact lookup_append_left h)
      (fun _ _ h => h) le_rfl
  exact Kinding.open_ty hB' (TyCtx.toK_allMix _) (.fvar (TyCtx.toK_snoc_lookup hX κ) trivial)

/-- Opening a size binder at a fresh size variable. -/
theorem KindingC.open_fresh_sz {Ψ : SizeCtx} {Δ : KCtx} {B : Ty} (hB : Kinding Ψ Δ [] 1 B .star)
    (j : Nat) (a : Size) : KindingC (Ψ ++ [(j, a)]) Δ (B.openSz 0 (.var j 0)) .star := by
  have hB' : Kinding (Ψ ++ [(j, a)]) Δ [] 1 B .star :=
    hB.weaken dom_append_left (fun _ _ h => h) (fun _ _ h => h) le_rfl
  exact Kinding.open_sz hB' (sizeWf_fresh_var _ _ _)

/-! ## Type environments -/

theorem TEnvOK.extend {W : World} {Θ : TyCtx} {θ : TEnv} (h : TEnvOK W Θ θ) {X : Nat}
    (hX : X ∉ Θ.map Prod.fst) {κ : Kind} {Y : Sem κ.erase} (hY : Good W κ Y) :
    TEnvOK W (Θ ++ [(X, κ)]) (TEnv.update θ X (PSem.ofSem κ.erase Y)) := by
  unfold TEnvOK
  rw [TyCtx.toK_append]
  exact TRel.extend h (TyCtx.not_mem_toK hX) hY

theorem TEnvOK.agree {W : World} {Θ : TyCtx} {θ θ' : TEnv} (h : TEnvOK W Θ θ)
    (hag : ∀ X ∈ Θ.map Prod.fst, θ' X = θ X) : TEnvOK W Θ θ' :=
  TRel.agree h (fun X hX => hag X (by simpa using hX))

/-! ## Unfolding at fresh variables -/

/-- The payload type of a constructor pattern, opened at a fresh size variable. -/
theorem interp_unfold_mu_fresh {W : World} {Ψ : SizeCtx} {Θ : List Nat} {ρ : SizeVal}
    {θ : TEnv} {a : Size} {S : List Ty} {c j : Nat} {Sc : Ty} (hwf : TyWf Ψ Θ 0 0 (.mu a S))
    (hj : j ∉ Ψ.dom) (hc : S[c]? = some Sc) (β : Ordinal.{0}) :
    interpT W (SizeVal.update ρ j β) θ (Sc.substTy 0 (.mu (.var j 0) S)) SzEnv.zero Env.empty =
      interpAt W ρ θ S c SzEnv.zero (Env.cons (PSem.ofSem .star (MuSet W
        (fun c 𝒳 => interpAt W ρ θ S c SzEnv.zero (Env.cons (PSem.ofSem .star 𝒳) Env.empty))
          β)) Env.empty) := by
  have hcl : c < S.length := (List.getElem?_eq_some_iff.mp hc).1
  have hScEq : S[c] = Sc := (List.getElem?_eq_some_iff.mp hc).2
  have hS : ∀ T ∈ S, TyWf Ψ Θ 1 0 T := by cases hwf with | mu _ h => exact h
  have hag : ∀ i ∈ Ψ.dom, SizeVal.update ρ j β i = ρ i := SizeVal.update_agree hj
  have hwfj : TyWf (Ψ ++ [(j, Size.inf 0)]) Θ 0 0 (.mu (.var j 0) S) :=
    .mu (sizeWf_fresh_var _ _ _)
      (fun T hT => (hS T hT).weaken _ _ _ _ dom_append_left (fun _ h => h) le_rfl le_rfl)
  rw [← hScEq]
  unfold interpT
  rw [interp_unfold_mu hcl hwfj]
  have hval : sizeVal (SizeVal.update ρ j β) SzEnv.zero (.var j 0) = β := by
    simp [sizeVal, SizeVal.update]
  rw [hval]
  have hF : (fun (c : Nat) (𝒳 : Set Tm) => interpAt W (SizeVal.update ρ j β) θ S c SzEnv.zero
        (Env.cons (PSem.ofSem .star 𝒳) Env.empty)) =
      (fun (c : Nat) (𝒳 : Set Tm) =>
        interpAt W ρ θ S c SzEnv.zero (Env.cons (PSem.ofSem .star 𝒳) Env.empty)) := by
    funext c' 𝒳
    exact interpAt_congr (fun c hc => interp_agree (hS _ (List.getElem_mem hc)) _ ρ θ θ _ _ _ _
      hag (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) _) c'
  rw [hF]
  exact interpAt_congr (fun c hc => interp_agree (hS _ (List.getElem_mem hc)) _ ρ θ θ _ _ _ _
    hag (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) _) c

theorem interp_unfold_nu_fresh {W : World} {Ψ : SizeCtx} {Θ : List Nat} {ρ : SizeVal}
    {θ : TEnv} {a : Size} {R : List Ty} {d j : Nat} {Rd : Ty} (hwf : TyWf Ψ Θ 0 0 (.nu a R))
    (hj : j ∉ Ψ.dom) (hd : R[d]? = some Rd) (β : Ordinal.{0}) :
    interpT W (SizeVal.update ρ j β) θ (Rd.substTy 0 (.nu (.var j 0) R)) SzEnv.zero Env.empty =
      interpAt W ρ θ R d SzEnv.zero (Env.cons (PSem.ofSem .star (NuSet W R.length
        (fun d 𝒳 => interpAt W ρ θ R d SzEnv.zero (Env.cons (PSem.ofSem .star 𝒳) Env.empty))
          β)) Env.empty) := by
  have hdl : d < R.length := (List.getElem?_eq_some_iff.mp hd).1
  have hRd : R[d] = Rd := (List.getElem?_eq_some_iff.mp hd).2
  have hR : ∀ T ∈ R, TyWf Ψ Θ 1 0 T := by cases hwf with | nu _ h => exact h
  have hag : ∀ i ∈ Ψ.dom, SizeVal.update ρ j β i = ρ i := SizeVal.update_agree hj
  have hwfj : TyWf (Ψ ++ [(j, Size.inf 0)]) Θ 0 0 (.nu (.var j 0) R) :=
    .nu (sizeWf_fresh_var _ _ _)
      (fun T hT => (hR T hT).weaken _ _ _ _ dom_append_left (fun _ h => h) le_rfl le_rfl)
  rw [← hRd]
  unfold interpT
  rw [interp_unfold_nu hdl hwfj]
  have hval : sizeVal (SizeVal.update ρ j β) SzEnv.zero (.var j 0) = β := by
    simp [sizeVal, SizeVal.update]
  rw [hval]
  have hG : (fun (d : Nat) (𝒳 : Set Tm) => interpAt W (SizeVal.update ρ j β) θ R d SzEnv.zero
        (Env.cons (PSem.ofSem .star 𝒳) Env.empty)) =
      (fun (d : Nat) (𝒳 : Set Tm) =>
        interpAt W ρ θ R d SzEnv.zero (Env.cons (PSem.ofSem .star 𝒳) Env.empty)) := by
    funext d' 𝒳
    exact interpAt_congr (fun c hc => interp_agree (hR _ (List.getElem_mem hc)) _ ρ θ θ _ _ _ _
      hag (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) _) d'
  rw [hG]
  exact interpAt_congr (fun c hc => interp_agree (hR _ (List.getElem_mem hc)) _ ρ θ θ _ _ _ _
    hag (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) _) d

/-! ## Facts about pattern typing -/

theorem patTy_dom {Ψ : SizeCtx} {Θ : TyCtx} {p : Pat} {A : Ty} {Γ : TermCtx} {Ψ' : SizeCtx}
    {Θ' : TyCtx} (h : PatTy Ψ Θ p A Γ Ψ' Θ') : Γ.map Prod.fst = p.vars := by
  induction h with
  | var => rfl
  | unit => rfl
  | pair _ _ ih₁ ih₂ => simp [Pat.vars, ih₁, ih₂]
  | cons _ _ _ ih => simpa [Pat.vars] using ih
  | packT _ _ ih => simpa [Pat.vars] using ih
  | packS _ _ ih => simpa [Pat.vars] using ih

theorem patTy_ctx {Ψ : SizeCtx} {Θ : TyCtx} {p : Pat} {A : Ty} {Γ : TermCtx} {Ψ' : SizeCtx}
    {Θ' : TyCtx} (h : PatTy Ψ Θ p A Γ Ψ' Θ') : KindingC Ψ Θ.toK A .star → CtxBoundsWf Ψ →
      TermCtxWf (Ψ ++ Ψ') (Θ ++ Θ') Γ ∧ CtxBoundsWf (Ψ ++ Ψ') := by
  induction h with
  | var Ψ Θ x A =>
    intro hA hb
    refine ⟨?_, by simpa using hb⟩
    intro q hq; simp at hq; subst hq; simpa using hA
  | unit Ψ Θ => intro _ hb; exact ⟨by simp [TermCtxWf], by simpa using hb⟩
  | @pair Ψ Ψ₁ Ψ₂ Θ Θ₁ Θ₂ p q A B Γ₁ Γ₂ _ _ ih₁ ih₂ =>
    intro hAB hb
    obtain ⟨_, hA, hB⟩ := Kinding.inv_prod hAB
    obtain ⟨hΓ₁, hb₁⟩ := ih₁ hA hb
    obtain ⟨hΓ₂, hb₂⟩ := ih₂ (by rw [TyCtx.toK_append]; exact KindingC.mono_append hB) hb₁
    refine ⟨?_, by simpa using hb₂⟩
    intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · have h' := hΓ₁ r hr
      rw [TyCtx.toK_append] at h'
      have h'' : KindingC (Ψ ++ Ψ₁ ++ Ψ₂) (Θ.toK ++ Θ₁.toK ++ Θ₂.toK) r.2 .star :=
        KindingC.mono_append h'
      simpa using h''
    · simpa using hΓ₂ r hr
  | @cons Ψ Ψ' Θ Θ' c j p a S Sc Γ hc hj _ ih =>
    intro hA hb
    obtain ⟨_, _, _, ha, _⟩ := Kinding.inv_mu hA
    have hA' : KindingC (Ψ ++ [(j, a)]) Θ.toK (.mu a S) .star := hA.mono_append_sz
    have hunf := hA'.unfold_mu (TyCtx.toK_allMix Θ) (b := .var j 0) hc (sizeWf_fresh_var _ _ _)
    obtain ⟨hΓ, hb'⟩ := ih hunf (hb.extend ha)
    exact ⟨by simpa using hΓ, by simpa using hb'⟩
  | @packT Ψ Ψ' Θ Θ' X κ p B Γ hX _ ih =>
    intro hA hb
    have hB := (Kinding.inv_exT hA).2
    obtain ⟨hΓ, hb'⟩ := ih (KindingC.open_fresh_ty hB hX) hb
    exact ⟨by simpa using hΓ, hb'⟩
  | @packS Ψ Ψ' Θ Θ' j p a B Γ hj _ ih =>
    intro hA hb
    obtain ⟨_, ha, hB⟩ := Kinding.inv_exS hA
    obtain ⟨hΓ, hb'⟩ := ih (KindingC.open_fresh_sz hB j a) (hb.extend ha)
    exact ⟨by simpa using hΓ, by simpa using hb'⟩

/-! ## Semantic contexts -/

theorem SemCtx.nil (W : World) (ρ : SizeVal) (θ : TEnv) : SemCtx W ρ θ [] [] :=
  ⟨by simp, by simp⟩

theorem lookup_none_of_not_mem {σ : TmSubst} {x : Nat} (h : x ∉ σ.map Prod.fst) :
    σ.lookup x = none := by
  cases hl : σ.lookup x with
  | none => rfl
  | some v => exact absurd (List.mem_map.mpr ⟨(x, v), lookup_mem hl, rfl⟩) h

theorem lookup_none_of_not_mem_ctx {Γ : TermCtx} {x : Nat} (h : Γ.lookup x = none) :
    x ∉ Γ.map Prod.fst := by
  intro hx
  obtain ⟨⟨y, A⟩, hm, rfl⟩ := List.mem_map.mp hx
  induction Γ with
  | nil => simp at hm
  | cons q Γ ih =>
    obtain ⟨z, B⟩ := q
    rw [List.lookup_cons] at h
    by_cases hyz : y = z
    · subst hyz; simp at h
    · have : (y == z) = false := beq_eq_false_iff_ne.mpr hyz
      simp only [this] at h
      rcases List.mem_cons.mp hm with hm | hm
      · simp at hm; exact hyz hm.1
      · exact ih hm h (List.mem_map.mpr ⟨(y, A), hm, rfl⟩)

theorem SemCtx.append {W : World} {ρ : SizeVal} {θ : TEnv} {Γ₁ Γ₂ : TermCtx} {σ₁ σ₂ : TmSubst}
    (h₁ : SemCtx W ρ θ Γ₁ σ₁) (h₂ : SemCtx W ρ θ Γ₂ σ₂)
    (hdom : σ₁.map Prod.fst = Γ₁.map Prod.fst) : SemCtx W ρ θ (Γ₁ ++ Γ₂) (σ₁ ++ σ₂) := by
  refine ⟨?_, ?_⟩
  · intro x A hx
    rw [List.lookup_append] at hx ⊢
    cases hΓ : Γ₁.lookup x with
    | some B =>
      rw [hΓ] at hx; simp at hx; subst hx
      obtain ⟨v, hv, hmem⟩ := h₁.1 x _ hΓ
      exact ⟨v, by simp [hv], hmem⟩
    | none =>
      rw [hΓ] at hx; simp at hx
      have : σ₁.lookup x = none := by
        apply lookup_none_of_not_mem
        rw [hdom]
        exact lookup_none_of_not_mem_ctx hΓ
      obtain ⟨v, hv, hmem⟩ := h₂.1 x _ hx
      exact ⟨v, by simp [this, hv], hmem⟩
  · intro x v hx
    rw [List.lookup_append] at hx
    cases h : σ₁.lookup x with
    | some w => rw [h] at hx; simp at hx; subst hx; exact h₁.2 x _ h
    | none => rw [h] at hx; simp at hx; exact h₂.2 x _ hx

theorem lookup_mem_ctx {Γ : TermCtx} {x : Nat} {A : Ty} (h : Γ.lookup x = some A) :
    (x, A) ∈ Γ := by
  induction Γ with
  | nil => simp at h
  | cons q Γ ih =>
    obtain ⟨y, B⟩ := q
    rw [List.lookup_cons] at h
    by_cases hxy : x = y
    · subst hxy; simp at h; subst h; simp
    · have : (x == y) = false := beq_eq_false_iff_ne.mpr hxy
      simp only [this] at h
      exact List.mem_cons_of_mem _ (ih h)

/-- Transport of a semantic context to valuations agreeing on the relevant variables. -/
theorem SemCtx.agree {W : World} {Ψ : SizeCtx} {Θ : TyCtx} {Γ : TermCtx}
    (hΓ : TermCtxWf Ψ Θ Γ) {ρ ρ' : SizeVal} {θ θ' : TEnv} (hag : ∀ i ∈ Ψ.dom, ρ i = ρ' i)
    (hagθ : ∀ X ∈ Θ.map Prod.fst, θ X = θ' X) {σ : TmSubst} (h : SemCtx W ρ θ Γ σ) :
    SemCtx W ρ' θ' Γ σ := by
  refine ⟨?_, h.2⟩
  intro x A hx
  obtain ⟨v, hv, hmem⟩ := h.1 x A hx
  refine ⟨v, hv, ?_⟩
  have hA : TyWf Ψ (Θ.map Prod.fst) 0 0 A := by
    have := (hΓ (x, A) (lookup_mem_ctx hx)).tyWf
    simpa using this
  unfold interpT at hmem ⊢
  rwa [← interp_agree hA ρ ρ' θ θ' _ _ _ _ hag hagθ (fun _ h => absurd h (Nat.not_lt_zero _))
    (fun _ h => absurd h (Nat.not_lt_zero _))]

theorem lookup_cons_ty (k x : Nat) (b : Ty) (l : TermCtx) :
    ((k, b) :: l).lookup x = if x = k then some b else l.lookup x := by
  rw [List.lookup_cons]
  by_cases h : x = k
  · subst h; simp
  · have hb : (x == k) = false := beq_eq_false_iff_ne.mpr h
    simp [hb, h]

/-! ## Pattern matching soundness -/

/-- The conclusion of pattern matching soundness. -/
def PatOK (W : World) (Ψ Ψ' : SizeCtx) (Θ Θ' : TyCtx) (ρ : SizeVal) (θ : TEnv) (Γ : TermCtx)
    (σm : TmSubst) : Prop :=
  ∃ ρ' θ', ValidVal (Ψ ++ Ψ') ρ' ∧ (∀ i ∈ Ψ.dom, ρ' i = ρ i) ∧ TEnvOK W (Θ ++ Θ') θ' ∧
    (∀ X ∈ Θ.map Prod.fst, θ' X = θ X) ∧ SemCtx W ρ' θ' Γ σm

theorem pat_sound {W : World} (hW : WorldClosed W) {Ψ : SizeCtx} {Θ : TyCtx} {p : Pat}
    {A : Ty} {Γ : TermCtx} {Ψ' : SizeCtx} {Θ' : TyCtx} (hp : PatTy Ψ Θ p A Γ Ψ' Θ') :
    ∀ (ρ : SizeVal) (θ : TEnv) (v : Tm) (σm : TmSubst), ValidVal Ψ ρ → CtxBoundsWf Ψ →
      TEnvOK W Θ θ → KindingC Ψ Θ.toK A .star →
      v ∈ interpT W ρ θ A SzEnv.zero Env.empty →
      matchPat p v = .yes σm → PatOK W Ψ Ψ' Θ Θ' ρ θ Γ σm := by
  induction hp with
  | var Ψ Θ x A =>
    intro ρ θ v σm hv _ hθ hA hmem hm
    simp [matchPat] at hm; subst hm
    refine ⟨ρ, θ, by simpa using hv, fun _ _ => rfl, by simpa using hθ, fun _ _ => rfl, ?_, ?_⟩
    · intro y B hy
      rw [lookup_cons_ty] at hy
      by_cases hyx : y = x
      · simp [hyx] at hy; subst hy; subst hyx
        exact ⟨v, by simp, hmem⟩
      · simp [hyx] at hy
    · intro y w hy
      rw [lookup_cons_eq] at hy
      by_cases hyx : y = x
      · simp [hyx] at hy; subst hy; exact (interp_closed_mem hW hA ρ hθ hmem).1
      · simp [hyx] at hy
  | unit Ψ Θ =>
    intro ρ θ v σm hv _ hθ _ _ hm
    cases v <;> simp [matchPat] at hm
    subst hm
    exact ⟨ρ, θ, by simpa using hv, fun _ _ => rfl, by simpa using hθ, fun _ _ => rfl,
      SemCtx.nil W ρ θ⟩
  | @pair Ψ Ψ₁ Ψ₂ Θ Θ₁ Θ₂ p q A B Γ₁ Γ₂ hp₁ hp₂ ih₁ ih₂ =>
    intro ρ θ v σm hv hb hθ hAB hmem hm
    cases v <;> simp [matchPat] at hm
    rename_i t u
    obtain ⟨σ₁, σ₂, hm₁, hm₂, rfl⟩ := MatchRes.and_eq_yes hm
    obtain ⟨_, hA, hB⟩ := Kinding.inv_prod hAB
    unfold interpT at hmem
    rw [interp_prod_star] at hmem
    obtain ⟨t', u', heq, ht, hu⟩ := introSet_of_intro hmem (by simp [IsIntro])
    cases heq
    obtain ⟨ρ₁, θ₁, hv₁, hag₁, hθ₁, hagθ₁, hs₁⟩ := ih₁ ρ θ t σ₁ hv hb hθ hA ht hm₁
    have hb₁ := (patTy_ctx hp₁ hA hb).2
    have hB₁ : KindingC (Ψ ++ Ψ₁) (Θ ++ Θ₁).toK B .star := by
      rw [TyCtx.toK_append]; exact KindingC.mono_append hB
    have hBw : TyWf Ψ (Θ.map Prod.fst) 0 0 B := by simpa using hB.tyWf
    have hu₁ : u ∈ interpT W ρ₁ θ₁ B SzEnv.zero Env.empty := by
      unfold interpT
      rwa [interp_agree hBw ρ₁ ρ θ₁ θ _ _ _ _ hag₁ hagθ₁
        (fun _ h => absurd h (Nat.not_lt_zero _)) (fun _ h => absurd h (Nat.not_lt_zero _))]
    obtain ⟨ρ₂, θ₂, hv₂, hag₂, hθ₂, hagθ₂, hs₂⟩ := ih₂ ρ₁ θ₁ u σ₂ hv₁ hb₁ hθ₁ hB₁ hu₁ hm₂
    refine ⟨ρ₂, θ₂, by simpa using hv₂, ?_, by simpa using hθ₂, ?_, ?_⟩
    · intro i hi
      rw [hag₂ i (dom_append_left i hi), hag₁ i hi]
    · intro X hX
      rw [hagθ₂ X (by simp only [List.map_append]; exact mem_append_left' X hX), hagθ₁ X hX]
    · have hΓ₁ := (patTy_ctx hp₁ hA hb).1
      have hs₁' := hs₁.agree hΓ₁ (fun i hi => (hag₂ i hi).symm)
        (fun X hX => (hagθ₂ X hX).symm)
      apply hs₁'.append hs₂
      rw [(matchPat_facts p t σ₁ hm₁).1, patTy_dom hp₁]
  | @cons Ψ Ψ' Θ Θ' c j p a S Sc Γ hc hj hp' ih =>
    intro ρ θ v σm hv hb hθ hA hmem hm
    cases v <;> simp [matchPat] at hm
    rename_i c' t
    by_cases hcc : c = c'
    · simp [hcc] at hm
      subst hcc
      obtain ⟨_, _, _, ha, _⟩ := Kinding.inv_mu hA
      unfold interpT at hmem
      rw [interp_mu_star, MuSet_eq] at hmem
      obtain ⟨c₀, t₀, β, hβ, heq, ht⟩ := introSet_of_intro hmem (by simp [IsIntro])
      cases heq
      have hv₁ := hv.extend hb hj ha hβ
      have hb₁ := hb.extend (j := j) ha
      have hA' : KindingC (Ψ ++ [(j, a)]) Θ.toK (.mu a S) .star := hA.mono_append_sz
      have hunf := hA'.unfold_mu (TyCtx.toK_allMix Θ) (b := .var j 0) hc
        (sizeWf_fresh_var _ _ _)
      have hAw : TyWf Ψ (Θ.map Prod.fst) 0 0 (.mu a S) := by simpa using hA.tyWf
      have ht' : t ∈ interpT W (SizeVal.update ρ j β) θ (Sc.substTy 0 (.mu (.var j 0) S))
          SzEnv.zero Env.empty := by
        rw [interp_unfold_mu_fresh hAw hj hc β]; exact ht
      obtain ⟨ρ', θ', hv', hag', hθ', hagθ', hs'⟩ := ih _ θ t σm hv₁ hb₁ hθ hunf ht' hm
      refine ⟨ρ', θ', by simpa using hv', ?_, hθ', hagθ', hs'⟩
      intro i hi
      rw [hag' i (dom_append_left i hi), SizeVal.update_agree hj i hi]
    · simp [hcc] at hm
  | @packT Ψ Ψ' Θ Θ' X κ p B Γ hX hp' ih =>
    intro ρ θ v σm hv hb hθ hA hmem hm
    cases v <;> simp [matchPat] at hm
    rename_i t
    have hB := (Kinding.inv_exT hA).2
    have hBw : TyWf Ψ (Θ.map Prod.fst) 1 0 B := by simpa using hB.tyWf
    unfold interpT at hmem
    rw [interp_exT_star] at hmem
    obtain ⟨t₀, Y, heq, hY, ht⟩ := introSet_of_intro hmem (by simp [IsIntro])
    cases heq
    have hθ₁ := hθ.extend hX hY
    have ht' : t ∈ interpT W ρ (TEnv.update θ X (PSem.ofSem κ.erase Y)) (B.substTy 0 (.fvar X))
        SzEnv.zero Env.empty := by
      unfold interpT
      rw [interp_open_fresh_ty hBw hX]; exact ht
    obtain ⟨ρ', θ', hv', hag', hθ', hagθ', hs'⟩ :=
      ih ρ _ t σm hv hb hθ₁ (KindingC.open_fresh_ty hB hX) ht' hm
    refine ⟨ρ', θ', by simpa using hv', hag', by simpa using hθ', ?_, hs'⟩
    intro Y' hY'
    rw [hagθ' Y' (by simp only [List.map_append]; exact mem_append_left' Y' hY'),
      TEnv.update_agree hX Y' hY']
  | @packS Ψ Ψ' Θ Θ' j p a B Γ hj hp' ih =>
    intro ρ θ v σm hv hb hθ hA hmem hm
    cases v <;> simp [matchPat] at hm
    rename_i t
    obtain ⟨_, ha, hB⟩ := Kinding.inv_exS hA
    have hBw : TyWf Ψ (Θ.map Prod.fst) 0 1 B := by simpa using hB.tyWf
    unfold interpT at hmem
    rw [interp_exS_star] at hmem
    obtain ⟨t₀, β, heq, hβ, ht⟩ := introSet_of_intro hmem (by simp [IsIntro])
    cases heq
    have hv₁ := hv.extend hb hj ha hβ
    have hb₁ := hb.extend (j := j) ha
    have ht' : t ∈ interpT W (SizeVal.update ρ j β) θ (B.openSz 0 (.var j 0)) SzEnv.zero
        Env.empty := by
      unfold interpT
      rw [interp_open_fresh_sz hBw hj]; exact ht
    obtain ⟨ρ', θ', hv', hag', hθ', hagθ', hs'⟩ :=
      ih _ θ t σm hv₁ hb₁ hθ (KindingC.open_fresh_sz hB j a) ht' hm
    refine ⟨ρ', θ', by simpa using hv', ?_, hθ', hagθ', hs'⟩
    intro i hi
    rw [hag' i (dom_append_left i hi), SizeVal.update_agree hj i hi]

end NishtAbel2024V5

/-! ## Solutions/V5/Spine.lean -/

/-! # V5: semantic elimination spines and their alignment with copattern typing -/

namespace NishtAbel2024V5

/-- A semantic context: free sizes and type variables with their valuations. -/
structure SCtx where
  Ψ : SizeCtx
  Θ : TyCtx
  ρ : SizeVal
  θ : TEnv

def SCtx.extSz (c : SCtx) (j : Nat) (a : Size) (β : Ordinal.{0}) : SCtx :=
  ⟨c.Ψ ++ [(j, a)], c.Θ, SizeVal.update c.ρ j β, c.θ⟩

def SCtx.extTy (c : SCtx) (X : Nat) (κ : Kind) (Y : Sem κ.erase) : SCtx :=
  ⟨c.Ψ, c.Θ ++ [(X, κ)], c.ρ, TEnv.update c.θ X (PSem.ofSem κ.erase Y)⟩

/-- `⟦T⟧` in a semantic context. -/
noncomputable def SCtx.den (W : World) (c : SCtx) (T : Ty) : Set Tm :=
  interpT W c.ρ c.θ T SzEnv.zero Env.empty

/-- Semantic spines: eliminations valid for a locally closed type. Projections and size
instantiations pick an ordinal below the bound and name it by a fresh size variable; type
instantiations pick a candidate and name it by a fresh type variable. -/
inductive SemSpine (W : World) : SCtx → Ty → List Elim → SCtx → Ty → Prop where
  | nil (c : SCtx) (T : Ty) : SemSpine W c T [] c T
  | term {c c' : SCtx} {T₁ T₂ C : Ty} {s : Tm} {es : List Elim} :
      s ∈ c.den W T₁ → SemSpine W c T₂ es c' C → SemSpine W c (.arr T₁ T₂) (.term s :: es) c' C
  | proj {c c' : SCtx} {a : Size} {R : List Ty} {d j : Nat} {Rd C : Ty} {β : Ordinal.{0}}
      {es : List Elim} :
      R[d]? = some Rd → j ∉ c.Ψ.dom → β < sizeVal c.ρ SzEnv.zero a →
      SemSpine W (c.extSz j a β) (Rd.substTy 0 (.nu (.var j 0) R)) es c' C →
      SemSpine W c (.nu a R) (.proj d :: es) c' C
  | instT {c c' : SCtx} {κ : Kind} {B C : Ty} {X : Nat} {Y : Sem κ.erase} {es : List Elim} :
      X ∉ c.Θ.map Prod.fst → Good W κ Y →
      SemSpine W (c.extTy X κ Y) (B.substTy 0 (.fvar X)) es c' C →
      SemSpine W c (.allT κ B) (.inst :: es) c' C
  | instS {c c' : SCtx} {a : Size} {B C : Ty} {j : Nat} {β : Ordinal.{0}} {es : List Elim} :
      j ∉ c.Ψ.dom → β < sizeVal c.ρ SzEnv.zero a →
      SemSpine W (c.extSz j a β) (B.openSz 0 (.var j 0)) es c' C →
      SemSpine W c (.allS a B) (.inst :: es) c' C

/-- Positions reached by semantic spines satisfy the invariants. -/
def PosOK (W : World) (c : SCtx) (T : Ty) : Prop :=
  ValidVal c.Ψ c.ρ ∧ CtxBoundsWf c.Ψ ∧ TEnvOK W c.Θ c.θ ∧ KindingC c.Ψ c.Θ.toK T .star

theorem PosOK.tyWf {W : World} {c : SCtx} {T : Ty} (h : PosOK W c T) :
    TyWf c.Ψ (c.Θ.map Prod.fst) 0 0 T := by
  simpa using h.2.2.2.tyWf

theorem PosOK.term {W : World} {c : SCtx} {T₁ T₂ : Ty} (h : PosOK W c (.arr T₁ T₂)) :
    PosOK W c T₂ := by
  obtain ⟨hv, hb, hθ, hwf⟩ := h
  exact ⟨hv, hb, hθ, (Kinding.inv_arr hwf).2.2⟩

theorem PosOK.dom {W : World} {c : SCtx} {T₁ T₂ : Ty} (h : PosOK W c (.arr T₁ T₂)) :
    KindingC c.Ψ c.Θ.toK T₁ .star := by
  have := (Kinding.inv_arr h.2.2.2).2.1
  rw [(TyCtx.toK_allMix c.Θ).inv] at this
  simpa using this

theorem PosOK.proj {W : World} {c : SCtx} {a : Size} {R : List Ty} {d j : Nat} {Rd : Ty}
    {β : Ordinal.{0}} (h : PosOK W c (.nu a R)) (hd : R[d]? = some Rd) (hj : j ∉ c.Ψ.dom)
    (hβ : β < sizeVal c.ρ SzEnv.zero a) :
    PosOK W (c.extSz j a β) (Rd.substTy 0 (.nu (.var j 0) R)) := by
  obtain ⟨hv, hb, hθ, hwf⟩ := h
  obtain ⟨_, _, _, ha, _⟩ := Kinding.inv_nu hwf
  refine ⟨hv.extend hb hj ha hβ, hb.extend ha, hθ, ?_⟩
  exact (KindingC.mono_append_sz hwf).unfold_nu (TyCtx.toK_allMix _) hd (sizeWf_fresh_var _ _ _)

theorem PosOK.instT {W : World} {c : SCtx} {κ : Kind} {B : Ty} {X : Nat} {Y : Sem κ.erase}
    (h : PosOK W c (.allT κ B)) (hX : X ∉ c.Θ.map Prod.fst) (hY : Good W κ Y) :
    PosOK W (c.extTy X κ Y) (B.substTy 0 (.fvar X)) := by
  obtain ⟨hv, hb, hθ, hwf⟩ := h
  exact ⟨hv, hb, hθ.extend hX hY, KindingC.open_fresh_ty (Kinding.inv_allT hwf).2 hX⟩

theorem PosOK.instS {W : World} {c : SCtx} {a : Size} {B : Ty} {j : Nat} {β : Ordinal.{0}}
    (h : PosOK W c (.allS a B)) (hj : j ∉ c.Ψ.dom) (hβ : β < sizeVal c.ρ SzEnv.zero a) :
    PosOK W (c.extSz j a β) (B.openSz 0 (.var j 0)) := by
  obtain ⟨hv, hb, hθ, hwf⟩ := h
  obtain ⟨_, ha, hB⟩ := Kinding.inv_allS hwf
  exact ⟨hv.extend hb hj ha hβ, hb.extend ha, hθ, KindingC.open_fresh_sz hB j a⟩

/-- Applying a member of a type to a semantic spine for that type. -/
theorem semSpine_app {W : World} {c c' : SCtx} {T C : Ty} {es : List Elim}
    (hs : SemSpine W c T es c' C) :
    PosOK W c T → ∀ r, r ∈ c.den W T → Tm.appSpine r es ∈ c'.den W C := by
  induction hs with
  | nil => intro _ r hr; exact hr
  | term hsT _ ih =>
    intro hok r hr
    exact ih hok.term _ (hr.2 _ hsT)
  | @proj c c' a R d j Rd C β es hd hj hβ _ ih =>
    intro hok r hr
    apply ih (hok.proj hd hj hβ)
    have hdl : d < R.length := (List.getElem?_eq_some_iff.mp hd).1
    simp only [SCtx.den, SCtx.extSz]
    rw [interp_unfold_nu_fresh hok.tyWf hj hd β]
    simp only [SCtx.den, interpT] at hr
    rw [interp_nu_star, NuSet_eq] at hr
    exact hr.2 β hβ d hdl
  | @instT c c' κ B C X Y es hX hY _ ih =>
    intro hok r hr
    apply ih (hok.instT hX hY)
    have hB : TyWf c.Ψ (c.Θ.map Prod.fst) 1 0 B := by
      simpa using (Kinding.inv_allT hok.2.2.2).2.tyWf
    simp only [SCtx.den, SCtx.extTy, interpT]
    rw [interp_open_fresh_ty hB hX]
    simp only [SCtx.den, interpT] at hr
    rw [interp_allT_star] at hr
    exact hr.2 Y hY
  | @instS c c' a B C j β es hj hβ _ ih =>
    intro hok r hr
    apply ih (hok.instS hj hβ)
    have hB : TyWf c.Ψ (c.Θ.map Prod.fst) 0 1 B := by
      simpa using (Kinding.inv_allS hok.2.2.2).2.2.tyWf
    simp only [SCtx.den, SCtx.extSz, interpT]
    rw [interp_open_fresh_sz hB hj]
    simp only [SCtx.den, interpT] at hr
    rw [interp_allS_star] at hr
    exact hr.2 β hβ

theorem semSpine_split {W : World} :
    ∀ {es₁ es₂ : List Elim} {c c' : SCtx} {T C : Ty},
      SemSpine W c T (es₁ ++ es₂) c' C →
      ∃ cm Tm', SemSpine W c T es₁ cm Tm' ∧ SemSpine W cm Tm' es₂ c' C
  | [], es₂, c, c', T, C, h => ⟨c, T, .nil _ _, h⟩
  | e :: es₁, es₂, c, c', T, C, h => by
    cases h with
    | term hs h' =>
      obtain ⟨cm, Tm', h₁, h₂⟩ := semSpine_split h'
      exact ⟨cm, Tm', .term hs h₁, h₂⟩
    | proj hd hj hβ h' =>
      obtain ⟨cm, Tm', h₁, h₂⟩ := semSpine_split h'
      exact ⟨cm, Tm', .proj hd hj hβ h₁, h₂⟩
    | instT hX hY h' =>
      obtain ⟨cm, Tm', h₁, h₂⟩ := semSpine_split h'
      exact ⟨cm, Tm', .instT hX hY h₁, h₂⟩
    | instS hj hβ h' =>
      obtain ⟨cm, Tm', h₁, h₂⟩ := semSpine_split h'
      exact ⟨cm, Tm', .instS hj hβ h₁, h₂⟩

theorem semSpine_snoc {W : World} {c c' c'' : SCtx} {T C D : Ty} {es es' : List Elim}
    (h₁ : SemSpine W c T es c' C) (h₂ : SemSpine W c' C es' c'' D) :
    SemSpine W c T (es ++ es') c'' D := by
  induction h₁ with
  | nil => exact h₂
  | term hs _ ih => exact .term hs (ih h₂)
  | proj hd hj hβ _ ih => exact .proj hd hj hβ (ih h₂)
  | instT hX hY _ ih => exact .instT hX hY (ih h₂)
  | instS hj hβ _ ih => exact .instS hj hβ (ih h₂)

theorem semSpine_posOK {W : World} {c c' : SCtx} {T C : Ty} {es : List Elim}
    (hs : SemSpine W c T es c' C) : PosOK W c T → PosOK W c' C := by
  induction hs with
  | nil => intro h; exact h
  | term _ _ ih => intro h; exact ih h.term
  | proj hd hj hβ _ ih => intro h; exact ih (h.proj hd hj hβ)
  | instT hX hY _ ih => intro h; exact ih (h.instT hX hY)
  | instS hj hβ _ ih => intro h; exact ih (h.instS hj hβ)

/-- Elimination spines of a semantic spine are closed. -/
theorem semSpine_closed {W : World} (hW : WorldClosed W) {c c' : SCtx} {T C : Ty}
    {es : List Elim} (hs : SemSpine W c T es c' C) : PosOK W c T → ElimsClosed es := by
  induction hs with
  | nil => intro _; rfl
  | @term c c' T₁ T₂ C s es hsT _ ih =>
    intro hok
    have hc := (interp_closed_mem hW hok.dom c.ρ hok.2.2.1 hsT).1
    unfold ElimsClosed at ih ⊢
    simp only [List.flatMap_cons, Elim.fv]
    rw [ih hok.term]
    simpa [Tm.Closed] using hc
  | proj hd hj hβ _ ih =>
    intro hok
    unfold ElimsClosed at ih ⊢
    simp only [List.flatMap_cons, Elim.fv]
    rw [ih (hok.proj hd hj hβ)]
    rfl
  | instT hX hY _ ih =>
    intro hok
    unfold ElimsClosed at ih ⊢
    simp only [List.flatMap_cons, Elim.fv]
    rw [ih (hok.instT hX hY)]
    rfl
  | instS hj hβ _ ih =>
    intro hok
    unfold ElimsClosed at ih ⊢
    simp only [List.flatMap_cons, Elim.fv]
    rw [ih (hok.instS hj hβ)]
    rfl

/-! ## Identity substitutions and commutation -/

theorem Size.subst_nil : ∀ a : Size, a.subst [] = a
  | .inf _ => rfl
  | .var _ _ => rfl
  | .bvar _ _ => rfl
  | .meet a b => by simp only [Size.subst, Size.subst_nil a, Size.subst_nil b]

mutual
theorem Ty.substSize_nil : ∀ A : Ty, A.substSize [] = A
  | .unit => rfl
  | .prod A B => by simp only [Ty.substSize]; rw [Ty.substSize_nil A, Ty.substSize_nil B]
  | .arr A B => by simp only [Ty.substSize]; rw [Ty.substSize_nil A, Ty.substSize_nil B]
  | .var _ => rfl
  | .fvar _ => rfl
  | .lam ι F => by simp only [Ty.substSize]; rw [Ty.substSize_nil F]
  | .app F G ι => by simp only [Ty.substSize]; rw [Ty.substSize_nil F, Ty.substSize_nil G]
  | .mu a S => by simp only [Ty.substSize]; rw [Size.subst_nil, Ty.substSizeList_nil S]
  | .nu a R => by simp only [Ty.substSize]; rw [Size.subst_nil, Ty.substSizeList_nil R]
  | .allT κ B => by simp only [Ty.substSize]; rw [Ty.substSize_nil B]
  | .exT κ B => by simp only [Ty.substSize]; rw [Ty.substSize_nil B]
  | .allS a B => by simp only [Ty.substSize]; rw [Size.subst_nil, Ty.substSize_nil B]
  | .exS a B => by simp only [Ty.substSize]; rw [Size.subst_nil, Ty.substSize_nil B]
theorem Ty.substSizeList_nil : ∀ S : List Ty, Ty.substSizeList [] S = S
  | [] => rfl
  | A :: S => by simp only [Ty.substSizeList]; rw [Ty.substSize_nil A, Ty.substSizeList_nil S]
end

mutual
theorem Ty.substFTy_nil : ∀ A : Ty, A.substFTy [] = A
  | .unit => rfl
  | .prod A B => by simp only [Ty.substFTy]; rw [Ty.substFTy_nil A, Ty.substFTy_nil B]
  | .arr A B => by simp only [Ty.substFTy]; rw [Ty.substFTy_nil A, Ty.substFTy_nil B]
  | .var _ => rfl
  | .fvar _ => rfl
  | .lam ι F => by simp only [Ty.substFTy]; rw [Ty.substFTy_nil F]
  | .app F G ι => by simp only [Ty.substFTy]; rw [Ty.substFTy_nil F, Ty.substFTy_nil G]
  | .mu a S => by simp only [Ty.substFTy]; rw [Ty.substFTyList_nil S]
  | .nu a R => by simp only [Ty.substFTy]; rw [Ty.substFTyList_nil R]
  | .allT κ B => by simp only [Ty.substFTy]; rw [Ty.substFTy_nil B]
  | .exT κ B => by simp only [Ty.substFTy]; rw [Ty.substFTy_nil B]
  | .allS a B => by simp only [Ty.substFTy]; rw [Ty.substFTy_nil B]
  | .exS a B => by simp only [Ty.substFTy]; rw [Ty.substFTy_nil B]
theorem Ty.substFTyList_nil : ∀ S : List Ty, Ty.substFTyList [] S = S
  | [] => rfl
  | A :: S => by simp only [Ty.substFTyList]; rw [Ty.substFTy_nil A, Ty.substFTyList_nil S]
end

/-- Renamings of free type variables: every value is a free type variable. -/
def FVarSubst (τ : List (Nat × Ty)) : Prop := ∀ X T, τ.lookup X = some T → ∃ Y, T = .fvar Y

theorem FVarSubst.closed {τ : List (Nat × Ty)} (h : FVarSubst τ) : ClosedTSubst τ := by
  intro X T hT
  obtain ⟨Y, rfl⟩ := h X T hT
  exact ⟨[], [Y], .fvar (by simp)⟩

/-- Size substitutions whose values are free size variables with offsets. -/
def VarSubst (σ : List (Nat × Size)) : Prop :=
  ∀ i b, σ.lookup i = some b → ∃ j m, b = .var j m

theorem VarSubst.lc {σ : List (Nat × Size)} (h : VarSubst σ) : LCSubst σ := by
  intro i b hb
  obtain ⟨j, m, rfl⟩ := h i b hb
  trivial

mutual
theorem Ty.substSize_substFTy {τ : List (Nat × Ty)} (hτ : FVarSubst τ) (σ : List (Nat × Size)) :
    ∀ A : Ty, (A.substSize σ).substFTy τ = (A.substFTy τ).substSize σ
  | .unit => rfl
  | .prod A B => by
    simp only [Ty.substSize, Ty.substFTy]
    rw [Ty.substSize_substFTy hτ σ A, Ty.substSize_substFTy hτ σ B]
  | .arr A B => by
    simp only [Ty.substSize, Ty.substFTy]
    rw [Ty.substSize_substFTy hτ σ A, Ty.substSize_substFTy hτ σ B]
  | .var _ => rfl
  | .fvar X => by
    simp only [Ty.substSize, Ty.substFTy]
    cases h : τ.lookup X with
    | none => rfl
    | some T => obtain ⟨Y, rfl⟩ := hτ X T h; rfl
  | .lam ι F => by
    simp only [Ty.substSize, Ty.substFTy]
    rw [Ty.substSize_substFTy hτ σ F]
  | .app F G ι => by
    simp only [Ty.substSize, Ty.substFTy]
    rw [Ty.substSize_substFTy hτ σ F, Ty.substSize_substFTy hτ σ G]
  | .mu a S => by
    simp only [Ty.substSize, Ty.substFTy]
    rw [Ty.substSizeList_substFTyList hτ σ S]
  | .nu a R => by
    simp only [Ty.substSize, Ty.substFTy]
    rw [Ty.substSizeList_substFTyList hτ σ R]
  | .allT κ B => by simp only [Ty.substSize, Ty.substFTy]; rw [Ty.substSize_substFTy hτ σ B]
  | .exT κ B => by simp only [Ty.substSize, Ty.substFTy]; rw [Ty.substSize_substFTy hτ σ B]
  | .allS a B => by simp only [Ty.substSize, Ty.substFTy]; rw [Ty.substSize_substFTy hτ σ B]
  | .exS a B => by simp only [Ty.substSize, Ty.substFTy]; rw [Ty.substSize_substFTy hτ σ B]
theorem Ty.substSizeList_substFTyList {τ : List (Nat × Ty)} (hτ : FVarSubst τ)
    (σ : List (Nat × Size)) :
    ∀ S : List Ty, Ty.substFTyList τ (Ty.substSizeList σ S) =
      Ty.substSizeList σ (Ty.substFTyList τ S)
  | [] => rfl
  | A :: S => by
    simp only [Ty.substSizeList, Ty.substFTyList]
    rw [Ty.substSize_substFTy hτ σ A, Ty.substSizeList_substFTyList hτ σ S]
end

/-! ## The renaming invariant -/

/-- A clause-side context `cc` and a spine-side context `cs` related by renamings of sizes and
of type variables that preserve their valuations. -/
structure Renaming (W : World) (cc cs : SCtx) (πS : List (Nat × Size)) (πT : List (Nat × Ty)) :
    Prop where
  varS : VarSubst πS
  targetS : ∀ i b, πS.lookup i = some b → SizeWf cc.Ψ b
  untouchedS : ∀ i ∈ cs.Ψ.dom, πS.lookup i = none → i ∈ cc.Ψ.dom
  valS : ∀ i ∈ cs.Ψ.dom, substVal cc.ρ πS i = cs.ρ i
  varT : ∀ X T, πT.lookup X = some T → ∃ Y, T = .fvar Y ∧ Y ∈ cc.Θ.map Prod.fst
  untouchedT : ∀ X ∈ cs.Θ.map Prod.fst, πT.lookup X = none → X ∈ cc.Θ.map Prod.fst
  valT : ∀ X ∈ cs.Θ.map Prod.fst, substTVal W cc.ρ cc.θ πT X = cs.θ X

theorem Renaming.fvar {W : World} {cc cs : SCtx} {πS : List (Nat × Size)} {πT : List (Nat × Ty)}
    (h : Renaming W cc cs πS πT) : FVarSubst πT := by
  intro X T hT
  obtain ⟨Y, rfl, _⟩ := h.varT X T hT
  exact ⟨Y, rfl⟩

theorem tyVal_fvar (W : World) (ρ : SizeVal) (θ : TEnv) (Y : Nat) (ζ : SzEnv) (η : Env) :
    tyVal W ρ θ (.fvar Y) ζ η = θ Y := rfl

/-- The renamed type denotes the same set. -/
theorem Renaming.den_eq {W : World} {cc cs : SCtx} {πS : List (Nat × Size)}
    {πT : List (Nat × Ty)} (h : Renaming W cc cs πS πT) {T : Ty}
    (hT : TyWf cs.Ψ (cs.Θ.map Prod.fst) 0 0 T) :
    cc.den W ((T.substSize πS).substFTy πT) = cs.den W T := by
  simp only [SCtx.den, interpT]
  have hτ : ∀ X U, πT.lookup X = some U → EnvFree W cc.ρ cc.θ U := by
    intro X U hU
    obtain ⟨Y, rfl, _⟩ := h.varT X U hU
    intro ι ζ ζ' η η'; rfl
  rw [interp_substFTy W cc.ρ cc.θ hτ, interp_substSize W cc.ρ _ h.varS.lc]
  exact interp_agree hT _ _ _ _ _ _ _ _ h.valS h.valT (fun _ h => absurd h (Nat.not_lt_zero _))
    (fun _ h => absurd h (Nat.not_lt_zero _)) _

/-- Enlarging the clause side, with valuations agreeing on the old domains. -/
theorem Renaming.extend_clause {W : World} {cc cs cc' : SCtx} {πS : List (Nat × Size)}
    {πT : List (Nat × Ty)} (h : Renaming W cc cs πS πT) (hdom : ∀ i ∈ cc.Ψ.dom, i ∈ cc'.Ψ.dom)
    (hΘ : ∀ X ∈ cc.Θ.map Prod.fst, X ∈ cc'.Θ.map Prod.fst)
    (hag : ∀ i ∈ cc.Ψ.dom, cc'.ρ i = cc.ρ i)
    (hagθ : ∀ X ∈ cc.Θ.map Prod.fst, cc'.θ X = cc.θ X) : Renaming W cc' cs πS πT := by
  refine ⟨h.varS, fun i b hb => (h.targetS i b hb).weaken hdom le_rfl,
    fun i hi hn => hdom i (h.untouchedS i hi hn), ?_, ?_,
    fun X hX hn => hΘ X (h.untouchedT X hX hn), ?_⟩
  · intro i hi
    rw [← h.valS i hi]
    simp only [substVal]
    cases hl : πS.lookup i with
    | some b =>
      exact sizeVal_agree (fun x hx => hag x hx) (fun _ h => absurd h (Nat.not_lt_zero _))
        (h.targetS i b hl)
    | none => exact hag i (h.untouchedS i hi hl)
  · intro X T hT
    obtain ⟨Y, rfl, hY⟩ := h.varT X T hT
    exact ⟨Y, rfl, hΘ Y hY⟩
  · intro X hX
    rw [← h.valT X hX]
    simp only [substTVal]
    cases hl : πT.lookup X with
    | some T =>
      obtain ⟨Y, rfl, hY⟩ := h.varT X T hl
      simp only [tyVal_fvar]
      exact hagθ Y hY
    | none => exact hagθ X (h.untouchedT X hX hl)

theorem Renaming.refl (W : World) (c : SCtx) : Renaming W c c [] [] :=
  ⟨by intro i b h; simp at h, by intro i b h; simp at h, fun i hi _ => hi,
    fun i _ => by simp [substVal], by intro X T h; simp at h, fun X hX _ => hX,
    fun X _ => by simp [substTVal]⟩

theorem lookup_size_cons (k x : Nat) (b : Size) (l : List (Nat × Size)) :
    ((k, b) :: l).lookup x = if x = k then some b else l.lookup x := by
  rw [List.lookup_cons]
  by_cases h : x = k
  · subst h; simp
  · have hb : (x == k) = false := beq_eq_false_iff_ne.mpr h
    simp [hb, h]

theorem lookup_ty_cons (k x : Nat) (b : Ty) (l : List (Nat × Ty)) :
    ((k, b) :: l).lookup x = if x = k then some b else l.lookup x := by
  rw [List.lookup_cons]
  by_cases h : x = k
  · subst h; simp
  · have hb : (x == k) = false := beq_eq_false_iff_ne.mpr h
    simp [hb, h]

theorem mem_dom_extSz {c : SCtx} {j : Nat} {a : Size} {β : Ordinal.{0}} {i : Nat}
    (hi : i ∈ (c.extSz j a β).Ψ.dom) (hij : i ≠ j) : i ∈ c.Ψ.dom := by
  simp only [SCtx.extSz, SizeCtx.dom, List.map_append, List.mem_append, List.map_cons,
    List.map_nil, List.mem_singleton] at hi
  rcases hi with hi | hi
  · exact hi
  · exact absurd hi hij

/-- A fresh size on both sides extends the renaming. -/
theorem Renaming.extSz {W : World} {cc cs : SCtx} {πS : List (Nat × Size)} {πT : List (Nat × Ty)}
    (h : Renaming W cc cs πS πT) {j js : Nat} (hj : j ∉ cc.Ψ.dom) {a as : Size}
    {β : Ordinal.{0}} :
    Renaming W (cc.extSz j a β) (cs.extSz js as β) ((js, .var j 0) :: πS) πT := by
  have hag : ∀ i ∈ cc.Ψ.dom, (cc.extSz j a β).ρ i = cc.ρ i := SizeVal.update_agree hj
  have h' := h.extend_clause (cc' := cc.extSz j a β) dom_append_left (fun _ h => h) hag
    (fun _ _ => rfl)
  refine ⟨?_, ?_, ?_, ?_, h'.varT, ?_, ?_⟩
  · intro i b hb
    rw [lookup_size_cons] at hb
    by_cases hi : i = js
    · simp [hi] at hb; exact ⟨j, 0, hb.symm⟩
    · simp [hi] at hb; exact h.varS i b hb
  · intro i b hb
    rw [lookup_size_cons] at hb
    by_cases hi : i = js
    · simp [hi] at hb; subst hb; exact sizeWf_fresh_var _ _ _
    · simp [hi] at hb; exact h'.targetS i b hb
  · intro i hi hn
    rw [lookup_size_cons] at hn
    by_cases hij : i = js
    · simp [hij] at hn
    · simp only [hij, if_false] at hn
      exact h'.untouchedS i (mem_dom_extSz hi hij) hn
  · intro i hi
    simp only [substVal]
    rw [lookup_size_cons]
    by_cases hij : i = js
    · subst hij; simp [sizeVal, SCtx.extSz, SizeVal.update]
    · simp only [hij, if_false]
      have := h'.valS i (mem_dom_extSz hi hij)
      simp only [substVal] at this
      rw [this]
      simp [SCtx.extSz, SizeVal.update, hij]
  · intro X hX hn; exact h'.untouchedT X hX hn
  · intro X hX
    have := h'.valT X hX
    rw [this]; rfl

theorem mem_dom_extTy {c : SCtx} {X : Nat} {κ : Kind} {Y : Sem κ.erase} {Z : Nat}
    (hZ : Z ∈ (c.extTy X κ Y).Θ.map Prod.fst) (hZX : Z ≠ X) : Z ∈ c.Θ.map Prod.fst := by
  simp only [SCtx.extTy, List.map_append, List.mem_append, List.map_cons, List.map_nil,
    List.mem_singleton] at hZ
  rcases hZ with hZ | hZ
  · exact hZ
  · exact absurd hZ hZX

/-- A fresh type variable on both sides extends the renaming. -/
theorem Renaming.extTy {W : World} {cc cs : SCtx} {πS : List (Nat × Size)} {πT : List (Nat × Ty)}
    (h : Renaming W cc cs πS πT) {X Xs : Nat} (hX : X ∉ cc.Θ.map Prod.fst) {κ : Kind}
    {Y : Sem κ.erase} :
    Renaming W (cc.extTy X κ Y) (cs.extTy Xs κ Y) πS ((Xs, .fvar X) :: πT) := by
  have hagθ : ∀ Z ∈ cc.Θ.map Prod.fst, (cc.extTy X κ Y).θ Z = cc.θ Z :=
    TEnv.update_agree hX
  have h' := h.extend_clause (cc' := cc.extTy X κ Y) (fun _ h => h)
    (fun Z hZ => by simp only [SCtx.extTy, List.map_append]; exact mem_append_left' Z hZ)
    (fun _ _ => rfl) hagθ
  refine ⟨h'.varS, h'.targetS, h'.untouchedS, ?_, ?_, ?_, ?_⟩
  · intro i hi; exact h'.valS i hi
  · intro Z T hT
    rw [lookup_ty_cons] at hT
    by_cases hZ : Z = Xs
    · simp [hZ] at hT; subst hT; exact ⟨X, rfl, by simp [SCtx.extTy]⟩
    · simp [hZ] at hT; exact h'.varT Z T hT
  · intro Z hZ hn
    rw [lookup_ty_cons] at hn
    by_cases hZX : Z = Xs
    · simp [hZX] at hn
    · simp only [hZX, if_false] at hn
      exact h'.untouchedT Z (mem_dom_extTy hZ hZX) hn
  · intro Z hZ
    simp only [substTVal]
    rw [lookup_ty_cons]
    by_cases hZX : Z = Xs
    · subst hZX
      simp only [if_true, tyVal_fvar]
      simp [SCtx.extTy, TEnv.update]
    · simp only [hZX, if_false]
      have := h'.valT Z (mem_dom_extTy hZ hZX)
      simp only [substTVal] at this
      rw [this]
      simp [SCtx.extTy, TEnv.update, hZX]

/-! ## Alignment of copattern typing with semantic spines -/

/-- The conclusion of spine alignment. -/
def AlignOK (W : World) (Ψc : SizeCtx) (Θc : TyCtx) (ρc : SizeVal) (θc : TEnv)
    (Ψ'c : SizeCtx) (Θ'c : TyCtx) (Γ' : TermCtx) (σm : TmSubst) (C : Ty) (cs' : SCtx)
    (Bs : Ty) : Prop :=
  ∃ ρc' θc' πS' πT', ValidVal (Ψc ++ Ψ'c) ρc' ∧ CtxBoundsWf (Ψc ++ Ψ'c) ∧
    TEnvOK W (Θc ++ Θ'c) θc' ∧ (∀ i ∈ Ψc.dom, ρc' i = ρc i) ∧
    (∀ X ∈ Θc.map Prod.fst, θc' X = θc X) ∧
    SemCtx W ρc' θc' Γ' σm ∧ TermCtxWf (Ψc ++ Ψ'c) (Θc ++ Θ'c) Γ' ∧
    C = (Bs.substSize πS').substFTy πT' ∧ Renaming W ⟨Ψc ++ Ψ'c, Θc ++ Θ'c, ρc', θc'⟩ cs' πS' πT'

theorem TermCtxWf.merge {Ψ Ψ₁ Ψ₂ : SizeCtx} {Θ Θ₁ Θ₂ : TyCtx} {Γ₁ Γ₂ : TermCtx}
    (h₁ : TermCtxWf (Ψ ++ Ψ₁) (Θ ++ Θ₁) Γ₁) (h₂ : TermCtxWf (Ψ ++ Ψ₁ ++ Ψ₂) (Θ ++ Θ₁ ++ Θ₂) Γ₂) :
    TermCtxWf (Ψ ++ (Ψ₁ ++ Ψ₂)) (Θ ++ (Θ₁ ++ Θ₂)) (Γ₁ ++ Γ₂) := by
  intro q hq
  rcases List.mem_append.mp hq with hq | hq
  · have h' := h₁ q hq
    rw [TyCtx.toK_append] at h'
    have h'' : KindingC (Ψ ++ Ψ₁ ++ Ψ₂) ((Θ.toK ++ Θ₁.toK) ++ Θ₂.toK) q.2 .star :=
      KindingC.mono_append h'
    simpa using h''
  · simpa using h₂ q hq

/-- Spine matching soundness, aligned with a semantic spine up to renaming. -/
theorem spine_align {W : World} (hW : WorldClosed W) {Ψc : SizeCtx} {Θc : TyCtx}
    {qs : List Copat} {Tc : Ty} {Γ' : TermCtx} {Ψ'c : SizeCtx} {Θ'c : TyCtx} {C : Ty}
    (hsp : SpineTy Ψc Θc qs Tc Γ' Ψ'c Θ'c C) :
    ∀ (ρc : SizeVal) (θc : TEnv) (cs : SCtx) (Ts : Ty) (es : List Elim) (cs' : SCtx) (Bs : Ty)
      (σm : TmSubst) (πS : List (Nat × Size)) (πT : List (Nat × Ty)),
      PosOK W ⟨Ψc, Θc, ρc, θc⟩ Tc → PosOK W cs Ts → Tc = (Ts.substSize πS).substFTy πT →
      Renaming W ⟨Ψc, Θc, ρc, θc⟩ cs πS πT →
      SemSpine W cs Ts es cs' Bs → matchSpine qs es = .yes σm → es.length = qs.length →
      AlignOK W Ψc Θc ρc θc Ψ'c Θ'c Γ' σm C cs' Bs := by
  induction hsp with
  | nil Ψ Θ A =>
    intro ρc θc cs Ts es cs' Bs σm πS πT hokc _ hT hren hs hm hlen
    cases es with
    | cons _ _ => simp at hlen
    | nil =>
      cases hs
      simp [matchSpine] at hm; subst hm
      refine ⟨ρc, θc, πS, πT, by simpa using hokc.1, by simpa using hokc.2.1,
        by simpa using hokc.2.2.1, fun _ _ => rfl, fun _ _ => rfl, SemCtx.nil W ρc θc,
        by simp [TermCtxWf], hT, ?_⟩
      simpa using hren
  | @pat Ψ Ψ₁ Ψ₂ Θ Θ₁ Θ₂ p qs A B C Γ₁ Γ₂ hp _ ih =>
    intro ρc θc cs Ts es cs' Bs σm πS πT hokc hoks hT hren hs hm hlen
    cases es with
    | nil => simp at hlen
    | cons e es =>
      cases hs with
      | proj _ _ _ _ => simp [matchSpine, matchCopat, MatchRes.and] at hm
      | instT _ _ _ => simp [matchSpine, matchCopat, MatchRes.and] at hm
      | instS _ _ _ => simp [matchSpine, matchCopat, MatchRes.and] at hm
      | @term _ _ T₁ T₂ _ s _ hsT hs' =>
        simp only [matchSpine, matchCopat] at hm
        obtain ⟨σ₁, σ₂, hm₁, hm₂, rfl⟩ := MatchRes.and_eq_yes hm
        simp only [Ty.substSize, Ty.substFTy] at hT
        injection hT with hA hB
        have hwfA : KindingC Ψ Θ.toK A .star := PosOK.dom (c := ⟨Ψ, Θ, ρc, θc⟩) hokc
        have hwfB : KindingC Ψ Θ.toK B .star := (PosOK.term (c := ⟨Ψ, Θ, ρc, θc⟩) hokc).2.2.2
        have hwfT₁ : TyWf cs.Ψ (cs.Θ.map Prod.fst) 0 0 T₁ := by simpa using hoks.dom.tyWf
        have hsA : s ∈ interpT W ρc θc A SzEnv.zero Env.empty := by
          have := hren.den_eq hwfT₁
          simp only [SCtx.den] at this
          rw [hA, this]; exact hsT
        obtain ⟨ρ₁, θ₁, hv₁, hag₁, hθ₁, hagθ₁, hctx₁⟩ :=
          pat_sound hW hp ρc θc s σ₁ hokc.1 hokc.2.1 hokc.2.2.1 hwfA hsA hm₁
        obtain ⟨hΓ₁, hb₁⟩ := patTy_ctx hp hwfA hokc.2.1
        have hren₁ := hren.extend_clause (cc' := ⟨Ψ ++ Ψ₁, Θ ++ Θ₁, ρ₁, θ₁⟩) dom_append_left
          (fun X hX => by simp only [List.map_append]; exact mem_append_left' X hX) hag₁ hagθ₁
        have hwfB₁ : KindingC (Ψ ++ Ψ₁) (Θ ++ Θ₁).toK B .star := by
          rw [TyCtx.toK_append]; exact KindingC.mono_append hwfB
        obtain ⟨ρc', θc', πS', πT', hv', hb', hθ', hag', hagθ', hctx₂, hΓ₂, hC, hren'⟩ :=
          ih ρ₁ θ₁ cs T₂ es cs' Bs σ₂ πS πT ⟨hv₁, hb₁, hθ₁, hwfB₁⟩ hoks.term hB hren₁ hs'
            hm₂ (by simpa using hlen)
        refine ⟨ρc', θc', πS', πT', by simpa using hv', by simpa using hb', by simpa using hθ',
          ?_, ?_, ?_, TermCtxWf.merge hΓ₁ hΓ₂, hC, by simpa using hren'⟩
        · intro i hi; rw [hag' i (dom_append_left i hi), hag₁ i hi]
        · intro X hX
          rw [hagθ' X (by simp only [List.map_append]; exact mem_append_left' X hX), hagθ₁ X hX]
        · apply (hctx₁.agree hΓ₁ (fun i hi => (hag' i hi).symm)
            (fun X hX => (hagθ' X hX).symm)).append hctx₂
          rw [(matchPat_facts p s σ₁ hm₁).1, patTy_dom hp]
  | @proj Ψ Ψ' Θ Θ' d j qs a R Rd C Γ hd hj _ ih =>
    intro ρc θc cs Ts es cs' Bs σm πS πT hokc hoks hT hren hs hm hlen
    cases es with
    | nil => simp at hlen
    | cons e es =>
      cases hs with
      | term _ _ => simp [matchSpine, matchCopat, MatchRes.and] at hm
      | instT _ _ _ => simp [matchSpine, matchCopat, MatchRes.and] at hm
      | instS _ _ _ => simp [matchSpine, matchCopat, MatchRes.and] at hm
      | @proj _ _ as Rs d' js Rds _ β _ hds hjs hβ hs' =>
        simp only [matchSpine, matchCopat] at hm
        by_cases hdd : d = d'
        · subst hdd
          simp only [if_true] at hm
          obtain ⟨σ₁, σ₂, hm₁, hm₂, rfl⟩ := MatchRes.and_eq_yes hm
          cases hm₁
          simp only [Ty.substSize, Ty.substFTy] at hT
          injection hT with ha hR
          obtain ⟨_, πs, _, has, hRsk⟩ := Kinding.inv_nu hoks.2.2.2
          have hRs : ∀ T ∈ Rs, TyWf cs.Ψ (cs.Θ.map Prod.fst) 1 0 T :=
            fun T hT => by simpa using (hRsk T hT).tyWf
          have hRd : Rd = (Rds.substSize πS).substFTy πT := by
            have h1 := Ty.substSizeList_getElem? πS Rs d
            have h2 := Ty.substFTyList_getElem? πT (Ty.substSizeList πS Rs) d
            rw [h1, hds] at h2
            rw [← hR, hd] at h2
            simpa using h2
          have hβc : β < sizeVal ρc SzEnv.zero a := by
            rw [ha, sizeVal_subst hren.varS.lc]
            rw [sizeVal_agree (Ψ := cs.Ψ) (m := 0) (fun i hi => hren.valS i hi)
              (fun _ h => absurd h (Nat.not_lt_zero _)) has]
            exact hβ
          have hokc₁ := PosOK.proj (c := ⟨Ψ, Θ, ρc, θc⟩) hokc hd hj hβc
          have hoks₁ := hoks.proj hds hjs hβ
          have hren₁ := hren.extSz (j := j) (js := js) (a := a) (as := as) (β := β) hj
          have hRds_wf : TyWf cs.Ψ (cs.Θ.map Prod.fst) 1 0 Rds := hRs Rds (List.mem_of_getElem? hds)
          have hT' : Rd.substTy 0 (.nu (.var j 0) R) =
              ((Rds.substTy 0 (.nu (.var js 0) Rs)).substSize ((js, .var j 0) :: πS)).substFTy
                πT := by
            rw [Ty.substSize_substTy, Ty.substFTy_substTy hren.fvar.closed]
            have h1 : Rds.substSize ((js, .var j 0) :: πS) = Rds.substSize πS :=
              hRds_wf.substSize_cons_fresh hjs _ _
            have h2 : Ty.substSizeList ((js, .var j 0) :: πS) Rs = Ty.substSizeList πS Rs := by
              have := hoks.tyWf.substSize_cons_fresh hjs (.var j 0) πS
              simp only [Ty.substSize] at this
              injection this
            have h3 : (Size.var js 0).subst ((js, .var j 0) :: πS) = .var j 0 := by
              simp [Size.subst, lookup_size_cons, Size.shift]
            simp only [Ty.substSize, Ty.substFTy, h1, h2, h3, ← hR, ← hRd]
          obtain ⟨ρc', θc', πS', πT', hv', hb', hθ', hag', hagθ', hctx, hΓ, hC, hren'⟩ :=
            ih _ θc _ _ es cs' Bs σ₂ _ πT hokc₁ hoks₁ hT' hren₁ hs' hm₂ (by simpa using hlen)
          refine ⟨ρc', θc', πS', πT', by simpa using hv', by simpa using hb', hθ', ?_, hagθ',
            by simpa using hctx, by simpa using hΓ, hC, by simpa using hren'⟩
          intro i hi
          rw [hag' i (dom_append_left i hi)]
          exact SizeVal.update_agree hj i hi
        · simp [hdd, MatchRes.and_no_left] at hm
  | @instT Ψ Ψ' Θ Θ' X κ qs B C Γ hX _ ih =>
    intro ρc θc cs Ts es cs' Bs σm πS πT hokc hoks hT hren hs hm hlen
    cases es with
    | nil => simp at hlen
    | cons e es =>
      cases hs with
      | term _ _ => simp [matchSpine, matchCopat, MatchRes.and] at hm
      | proj _ _ _ _ => simp [matchSpine, matchCopat, MatchRes.and] at hm
      | instS _ _ _ =>
        simp only [Ty.substSize, Ty.substFTy] at hT
        cases hT
      | @instT _ _ κs Bs' _ Xs Y _ hXs hY hs' =>
        simp only [matchSpine, matchCopat] at hm
        obtain ⟨σ₁, σ₂, hm₁, hm₂, rfl⟩ := MatchRes.and_eq_yes hm
        cases hm₁
        simp only [Ty.substSize, Ty.substFTy] at hT
        injection hT with hκ hB
        subst hκ
        have hBs : TyWf cs.Ψ (cs.Θ.map Prod.fst) 1 0 Bs' := by
          simpa using (Kinding.inv_allT hoks.2.2.2).2.tyWf
        have hokc₁ := PosOK.instT (c := ⟨Ψ, Θ, ρc, θc⟩) hokc hX hY
        have hoks₁ := hoks.instT hXs hY
        have hren₁ := hren.extTy (X := X) (Xs := Xs) (κ := κ) (Y := Y) hX
        have hT' : B.substTy 0 (.fvar X) =
            ((Bs'.substTy 0 (.fvar Xs)).substSize πS).substFTy ((Xs, .fvar X) :: πT) := by
          have hfv : FVarSubst ((Xs, Ty.fvar X) :: πT) := by
            intro Z T hT
            rw [lookup_ty_cons] at hT
            by_cases hZ : Z = Xs
            · simp [hZ] at hT; exact ⟨X, hT.symm⟩
            · simp [hZ] at hT; exact hren.fvar Z T hT
          rw [Ty.substSize_substFTy hfv, Ty.substFTy_substTy hfv.closed, Ty.substSize_substTy]
          have h1 : Bs'.substFTy ((Xs, .fvar X) :: πT) = Bs'.substFTy πT :=
            hBs.substFTy_cons_fresh hXs _ _
          have h2 : (Ty.fvar Xs).substFTy ((Xs, .fvar X) :: πT) = .fvar X := by
            simp [Ty.substFTy, lookup_ty_cons]
          rw [h1, h2, ← Ty.substSize_substFTy hren.fvar, ← hB]
          rfl
        obtain ⟨ρc', θc', πS', πT', hv', hb', hθ', hag', hagθ', hctx, hΓ, hC, hren'⟩ :=
          ih ρc _ _ _ es cs' Bs σ₂ πS _ hokc₁ hoks₁ hT' hren₁ hs' hm₂ (by simpa using hlen)
        refine ⟨ρc', θc', πS', πT', hv', hb', by simpa using hθ', hag', ?_, by simpa using hctx,
          by simpa using hΓ, hC, by simpa using hren'⟩
        intro Z hZ
        rw [hagθ' Z (by simp only [List.map_append]; exact mem_append_left' Z hZ)]
        exact TEnv.update_agree hX Z hZ
  | @instS Ψ Ψ' Θ Θ' j qs a B C Γ hj _ ih =>
    intro ρc θc cs Ts es cs' Bs σm πS πT hokc hoks hT hren hs hm hlen
    cases es with
    | nil => simp at hlen
    | cons e es =>
      cases hs with
      | term _ _ => simp [matchSpine, matchCopat, MatchRes.and] at hm
      | proj _ _ _ _ => simp [matchSpine, matchCopat, MatchRes.and] at hm
      | instT _ _ _ =>
        simp only [Ty.substSize, Ty.substFTy] at hT
        cases hT
      | @instS _ _ as Bs' _ js β _ hjs hβ hs' =>
        simp only [matchSpine, matchCopat] at hm
        obtain ⟨σ₁, σ₂, hm₁, hm₂, rfl⟩ := MatchRes.and_eq_yes hm
        cases hm₁
        simp only [Ty.substSize, Ty.substFTy] at hT
        injection hT with ha hB
        obtain ⟨_, has, hBsk⟩ := Kinding.inv_allS hoks.2.2.2
        have hBs : TyWf cs.Ψ (cs.Θ.map Prod.fst) 0 1 Bs' := by simpa using hBsk.tyWf
        have hβc : β < sizeVal ρc SzEnv.zero a := by
          rw [ha, sizeVal_subst hren.varS.lc]
          rw [sizeVal_agree (Ψ := cs.Ψ) (m := 0) (fun i hi => hren.valS i hi)
            (fun _ h => absurd h (Nat.not_lt_zero _)) has]
          exact hβ
        have hokc₁ := PosOK.instS (c := ⟨Ψ, Θ, ρc, θc⟩) hokc hj hβc
        have hoks₁ := hoks.instS hjs hβ
        have hren₁ := hren.extSz (j := j) (js := js) (a := a) (as := as) (β := β) hj
        have hvar : VarSubst ((js, Size.var j 0) :: πS) := by
          intro i b hb
          rw [lookup_size_cons] at hb
          by_cases hi : i = js
          · simp [hi] at hb; exact ⟨j, 0, hb.symm⟩
          · simp [hi] at hb; exact hren.varS i b hb
        have hT' : B.openSz 0 (.var j 0) =
            ((Bs'.openSz 0 (.var js 0)).substSize ((js, .var j 0) :: πS)).substFTy πT := by
          rw [Ty.substSize_openSz hvar.lc, Ty.substFTy_openSz hren.fvar.closed]
          have h1 : Bs'.substSize ((js, .var j 0) :: πS) = Bs'.substSize πS :=
            hBs.substSize_cons_fresh hjs _ _
          have h3 : (Size.var js 0).subst ((js, .var j 0) :: πS) = .var j 0 := by
            simp [Size.subst, lookup_size_cons, Size.shift]
          rw [h1, h3, ← hB]
        obtain ⟨ρc', θc', πS', πT', hv', hb', hθ', hag', hagθ', hctx, hΓ, hC, hren'⟩ :=
          ih _ θc _ _ es cs' Bs σ₂ _ πT hokc₁ hoks₁ hT' hren₁ hs' hm₂ (by simpa using hlen)
        refine ⟨ρc', θc', πS', πT', by simpa using hv', by simpa using hb', hθ', ?_, hagθ',
          by simpa using hctx, by simpa using hΓ, hC, by simpa using hren'⟩
        intro i hi
        rw [hag' i (dom_append_left i hi)]
        exact SizeVal.update_agree hj i hi

end NishtAbel2024V5

/-! ## Solutions/V5/ClauseHead.lean -/

/-! # V5: soundness of clause-headed terms -/

namespace NishtAbel2024V5

/-- One argument of a spine takes a step. -/
inductive SpineStep (W : World) : List Elim → List Elim → Prop where
  | here {s s' : Tm} {es : List Elim} : Step W s s' → SpineStep W (.term s :: es) (.term s' :: es)
  | there {e : Elim} {es es' : List Elim} : SpineStep W es es' → SpineStep W (e :: es) (e :: es')

theorem spineStep_append {W : World} {es es' : List Elim} (h : SpineStep W es es') (e : Elim) :
    SpineStep W (es ++ [e]) (es' ++ [e]) := by
  induction h with
  | here hs => exact .here hs
  | there _ ih => exact .there ih

theorem spineStep_snoc {W : World} (es : List Elim) {s s' : Tm} (h : Step W s s') :
    SpineStep W (es ++ [.term s]) (es ++ [.term s']) := by
  induction es with
  | nil => exact .here h
  | cons e es ih => exact .there ih

/-- Atomic heads: `λ{D⃗}` or a function name. -/
def IsHead : Tm → Prop
  | .lam _ => True
  | .fn _ => True
  | _ => False

/-- Steps of a head applied to a spine: a head step, or a step inside an argument. -/
theorem step_appSpine_head {W : World} {h : Tm} (hh : IsHead h) :
    ∀ (es : List Elim) (u : Tm), Step W (Tm.appSpine h es) u →
      headStep W (Tm.appSpine h es) = some u ∨ ∃ es', SpineStep W es es' ∧ u = Tm.appSpine h es' := by
  intro es
  induction es using List.reverseRecOn with
  | nil =>
    intro u hs
    cases h <;> simp [IsHead] at hh <;> cases hs <;> simp_all
  | append_singleton es e ih =>
    intro u hs
    rw [Tm.appSpine_snoc] at hs ⊢
    cases hs with
    | head hh' => exact Or.inl hh'
    | appFun hr =>
      rcases ih _ hr with hh' | ⟨es', hst, rfl⟩
      · left
        have := headStep_appSpine hh' [e]
        simpa using this
      · right; exact ⟨es' ++ [e], spineStep_append hst e, by simp⟩
    | appArg hs' =>
      right; exact ⟨es ++ [.term _], spineStep_snoc es hs', by simp⟩

theorem spineStep_acc_cons {W : World} : ∀ (e : Elim), (∀ s, e = .term s → SN W s) →
    ∀ es, Acc (fun es' es => SpineStep W es es') es →
      Acc (fun es' es => SpineStep W es es') (e :: es)
  | .proj d, _, es, hes => by
    induction hes with
    | intro es _ ih =>
      refine Acc.intro _ fun es' hst => ?_
      cases hst with
      | there hst => exact ih _ hst
  | .inst, _, es, hes => by
    induction hes with
    | intro es _ ih =>
      refine Acc.intro _ fun es' hst => ?_
      cases hst with
      | there hst => exact ih _ hst
  | .term s, he, es, hes => by
    have hs : SN W s := he s rfl
    clear he
    induction hs generalizing es with
    | intro s _ ihs =>
      induction hes with
      | intro es hes' ihes =>
        refine Acc.intro _ fun es' hst => ?_
        cases hst with
        | here hss =>
          exact ihs _ hss es (Acc.intro (r := fun es' es => SpineStep W es es') es hes')
        | there hst' => exact ihes _ hst'

/-- Spines whose term arguments are strongly normalizing are accessible for `SpineStep`. -/
theorem spineStep_acc {W : World} :
    ∀ es : List Elim, (∀ s, Elim.term s ∈ es → SN W s) → Acc (fun es' es => SpineStep W es es') es
  | [], _ => Acc.intro _ fun _ h => by cases h
  | e :: es, h =>
    spineStep_acc_cons e (fun s hs => h s (by rw [hs]; simp)) es
      (spineStep_acc es (fun s hs => h s (List.mem_cons_of_mem _ hs)))

/-- Semantic spines are preserved by argument steps. -/
theorem semSpine_spineStep {W : World} (hW : WorldClosed W) {c c' : SCtx} {T C : Ty}
    {es : List Elim} (hs : SemSpine W c T es c' C) :
    PosOK W c T → ∀ es', SpineStep W es es' → SemSpine W c T es' c' C := by
  induction hs with
  | nil => intro _ es' h; cases h
  | @term c c' T₁ T₂ C s es hsT hs' ih =>
    intro hok es' h
    cases h with
    | here hss =>
      have hcand := interp_cand_closed hW hok.dom c.ρ hok.2.2.1
      exact .term (hcand.red _ hsT _ hss) hs'
    | there h => exact .term hsT (ih hok.term _ h)
  | proj hd hj hβ _ ih =>
    intro hok es' h
    cases h with
    | there h => exact .proj hd hj hβ (ih (hok.proj hd hj hβ) _ h)
  | instT hX hY _ ih =>
    intro hok es' h
    cases h with
    | there h => exact .instT hX hY (ih (hok.instT hX hY) _ h)
  | instS hj hβ _ ih =>
    intro hok es' h
    cases h with
    | there h => exact .instS hj hβ (ih (hok.instS hj hβ) _ h)

/-! ## Spine-length facts for clause selection -/

theorem matchSpine_append_of_le :
    ∀ (qs : List Copat) (es es₂ : List Elim), qs.length ≤ es.length →
      matchSpine qs (es ++ es₂) = matchSpine qs es
  | [], _, _, _ => rfl
  | _ :: _, [], _, h => by simp at h
  | q :: qs, e :: es, es₂, h => by
    simp only [matchSpine, List.cons_append]
    rw [matchSpine_append_of_le qs es es₂ (by simpa using h)]

def clauseLen : Clause → Nat
  | .mk qs _ => qs.length

def maxLen (D : List Clause) : Nat := D.foldr (fun cl m => max (clauseLen cl) m) 0

theorem le_maxLen {D : List Clause} {cl : Clause} (h : cl ∈ D) : clauseLen cl ≤ maxLen D := by
  induction D with
  | nil => simp at h
  | cons c D ih =>
    simp only [maxLen, List.foldr_cons] at ih ⊢
    rcases List.mem_cons.mp h with rfl | h
    · exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)

/-- If every clause longer than the spine already mismatches it, extending a stuck spine keeps
it stuck. -/
theorem selectClause_append_none {D : List Clause} {es : List Elim}
    (hlong : ∀ qs t, Clause.mk qs t ∈ D → es.length < qs.length → matchSpine qs es = .no)
    (h : selectClause D es = none) (es₂ : List Elim) : selectClause D (es ++ es₂) = none := by
  induction D with
  | nil => rfl
  | cons cl D ih =>
    obtain ⟨qs, t⟩ := cl
    have hD : ∀ qs' t', Clause.mk qs' t' ∈ D → es.length < qs'.length →
        matchSpine qs' es = .no :=
      fun qs' t' hm hl => hlong qs' t' (List.mem_cons_of_mem _ hm) hl
    simp only [selectClause] at h ⊢
    by_cases hq : qs.length ≤ es.length
    · rw [matchSpine_append_of_le qs es es₂ hq]
      cases hm : matchSpine qs es with
      | yes σ => rw [hm] at h; simp at h
      | no => rw [hm] at h; exact ih hD h
      | stuck => rfl
    · have hno := hlong qs t (by simp) (by omega)
      rw [matchSpine_append_no hno es₂]
      rw [hno] at h
      exact ih hD h

theorem exists_fresh (l : List Nat) : ∃ j, j ∉ l := by
  obtain ⟨j, hj⟩ := Infinite.exists_notMem_finset l.toFinset
  exact ⟨j, by simpa using hj⟩

/-! ## Shapes of positions that a longer clause can still consume -/

/-- Elimination types: the types a copattern can consume. -/
def IsElimTy : Ty → Prop
  | .arr _ _ => True
  | .nu _ _ => True
  | .allT _ _ => True
  | .allS _ _ => True
  | _ => False

theorem isElimTy_rename {πS : List (Nat × Size)} {πT : List (Nat × Ty)} (hfv : FVarSubst πT) :
    ∀ {T : Ty}, IsElimTy ((T.substSize πS).substFTy πT) → IsElimTy T
  | .fvar X, h => by
    simp only [Ty.substSize, Ty.substFTy] at h
    cases hl : πT.lookup X with
    | none => simp [hl, IsElimTy] at h
    | some U =>
      obtain ⟨Y, rfl⟩ := hfv X U hl
      simp [hl, IsElimTy] at h
  | .arr _ _, _ => by simp [IsElimTy]
  | .nu _ _, _ => by simp [IsElimTy]
  | .allT _ _, _ => by simp [IsElimTy]
  | .allS _ _, _ => by simp [IsElimTy]
  | .unit, h => by simpa [Ty.substSize, Ty.substFTy, IsElimTy] using h
  | .prod _ _, h => by simpa [Ty.substSize, Ty.substFTy, IsElimTy] using h
  | .var _, h => by simpa [Ty.substSize, Ty.substFTy, IsElimTy] using h
  | .lam _ _, h => by simpa [Ty.substSize, Ty.substFTy, IsElimTy] using h
  | .app _ _ _, h => by simpa [Ty.substSize, Ty.substFTy, IsElimTy] using h
  | .mu _ _, h => by simpa [Ty.substSize, Ty.substFTy, IsElimTy] using h
  | .exT _ _, h => by simpa [Ty.substSize, Ty.substFTy, IsElimTy] using h
  | .exS _ _, h => by simpa [Ty.substSize, Ty.substFTy, IsElimTy] using h

theorem VarSubst.cons {πS : List (Nat × Size)} (h : VarSubst πS) (js j : Nat) :
    VarSubst ((js, Size.var j 0) :: πS) := by
  intro i b hb
  rw [lookup_size_cons] at hb
  by_cases hi : i = js
  · simp [hi] at hb; exact ⟨j, 0, hb.symm⟩
  · simp [hi] at hb; exact h i b hb

theorem FVarSubst.cons {πT : List (Nat × Ty)} (h : FVarSubst πT) (Xs X : Nat) :
    FVarSubst ((Xs, Ty.fvar X) :: πT) := by
  intro Y T hT
  rw [lookup_ty_cons] at hT
  by_cases hY : Y = Xs
  · simp [hY] at hT; exact ⟨X, hT.symm⟩
  · simp [hY] at hT; exact h Y T hT

/-- Renamed types stay related after a projection at fresh size variables. -/
theorem align_proj_ty {cs : SCtx} {πS : List (Nat × Size)} {πT : List (Nat × Ty)}
    (hfv : FVarSubst πT) {a as : Size} {R Rs : List Ty}
    (hT : Ty.nu a R = ((Ty.nu as Rs).substSize πS).substFTy πT)
    (hwf : TyWf cs.Ψ (cs.Θ.map Prod.fst) 0 0 (.nu as Rs)) {d : Nat} {Rd Rds : Ty}
    (hd : R[d]? = some Rd) (hds : Rs[d]? = some Rds) {j js : Nat} (hjs : js ∉ cs.Ψ.dom) :
    Rd.substTy 0 (.nu (.var j 0) R) =
      ((Rds.substTy 0 (.nu (.var js 0) Rs)).substSize ((js, .var j 0) :: πS)).substFTy πT := by
  simp only [Ty.substSize, Ty.substFTy] at hT
  injection hT with _ hR
  have hRs : ∀ T ∈ Rs, TyWf cs.Ψ (cs.Θ.map Prod.fst) 1 0 T := by cases hwf with | nu _ h => exact h
  have hRd : Rd = (Rds.substSize πS).substFTy πT := by
    have h1 := Ty.substSizeList_getElem? πS Rs d
    have h2 := Ty.substFTyList_getElem? πT (Ty.substSizeList πS Rs) d
    rw [h1, hds] at h2
    rw [← hR, hd] at h2
    simpa using h2
  have hRds_wf : TyWf cs.Ψ (cs.Θ.map Prod.fst) 1 0 Rds := hRs Rds (List.mem_of_getElem? hds)
  rw [Ty.substSize_substTy, Ty.substFTy_substTy hfv.closed]
  have h1 : Rds.substSize ((js, .var j 0) :: πS) = Rds.substSize πS :=
    hRds_wf.substSize_cons_fresh hjs _ _
  have h2 : Ty.substSizeList ((js, .var j 0) :: πS) Rs = Ty.substSizeList πS Rs := by
    have := hwf.substSize_cons_fresh hjs (.var j 0) πS
    simp only [Ty.substSize] at this
    injection this
  have h3 : (Size.var js 0).subst ((js, .var j 0) :: πS) = .var j 0 := by
    simp [Size.subst, lookup_size_cons, Size.shift]
  simp only [Ty.substSize, Ty.substFTy, h1, h2, h3, ← hR, ← hRd]

/-- Renamed types stay related after a type instantiation at fresh type variables. -/
theorem align_instT_ty {cs : SCtx} {πS : List (Nat × Size)} {πT : List (Nat × Ty)}
    (hfv : FVarSubst πT) {B Bs' : Ty}
    (hB : B = (Bs'.substSize πS).substFTy πT)
    (hBs : TyWf cs.Ψ (cs.Θ.map Prod.fst) 1 0 Bs') {X Xs : Nat}
    (hXs : Xs ∉ cs.Θ.map Prod.fst) :
    B.substTy 0 (.fvar X) =
      ((Bs'.substTy 0 (.fvar Xs)).substSize πS).substFTy ((Xs, .fvar X) :: πT) := by
  have hfv' := hfv.cons Xs X
  rw [Ty.substSize_substFTy hfv', Ty.substFTy_substTy hfv'.closed, Ty.substSize_substTy]
  have h1 : Bs'.substFTy ((Xs, .fvar X) :: πT) = Bs'.substFTy πT :=
    hBs.substFTy_cons_fresh hXs _ _
  have h2 : (Ty.fvar Xs).substFTy ((Xs, .fvar X) :: πT) = .fvar X := by
    simp [Ty.substFTy, lookup_ty_cons]
  rw [h1, h2, ← Ty.substSize_substFTy hfv, ← hB]
  rfl

/-- Renamed types stay related after a size instantiation at fresh size variables. -/
theorem align_instS_ty {cs : SCtx} {πS : List (Nat × Size)} {πT : List (Nat × Ty)}
    (hvarS : VarSubst πS) (hfv : FVarSubst πT) {a as : Size} {B Bs' : Ty}
    (hT : Ty.allS a B = ((Ty.allS as Bs').substSize πS).substFTy πT)
    (hwf : TyWf cs.Ψ (cs.Θ.map Prod.fst) 0 0 (.allS as Bs')) {j js : Nat}
    (hjs : js ∉ cs.Ψ.dom) :
    B.openSz 0 (.var j 0) =
      ((Bs'.openSz 0 (.var js 0)).substSize ((js, .var j 0) :: πS)).substFTy πT := by
  simp only [Ty.substSize, Ty.substFTy] at hT
  injection hT with _ hB
  have hBs : TyWf cs.Ψ (cs.Θ.map Prod.fst) 0 1 Bs' := by cases hwf with | allS _ h => exact h
  rw [Ty.substSize_openSz (hvarS.cons js j).lc, Ty.substFTy_openSz hfv.closed]
  have h1 : Bs'.substSize ((js, .var j 0) :: πS) = Bs'.substSize πS :=
    hBs.substSize_cons_fresh hjs _ _
  have h3 : (Size.var js 0).subst ((js, .var j 0) :: πS) = .var j 0 := by
    simp [Size.subst, lookup_size_cons, Size.shift]
  rw [h1, h3, ← hB]

/-- A clause longer than a semantic spine, whose copatterns do not yet mismatch the spine, sees
an elimination type at the end of the spine. -/
theorem spine_shape {W : World} {Ψc : SizeCtx} {Θc : TyCtx}
    {qs : List Copat} {Tc : Ty} {Γ' : TermCtx} {Ψ'c : SizeCtx} {Θ'c : TyCtx} {C : Ty}
    (hsp : SpineTy Ψc Θc qs Tc Γ' Ψ'c Θ'c C) :
    ∀ (cs : SCtx) (Ts : Ty) (es : List Elim) (cs' : SCtx) (Bs : Ty)
      (πS : List (Nat × Size)) (πT : List (Nat × Ty)),
      VarSubst πS → FVarSubst πT → PosOK W cs Ts → Tc = (Ts.substSize πS).substFTy πT →
      SemSpine W cs Ts es cs' Bs → es.length < qs.length → matchSpine qs es ≠ .no →
      IsElimTy Bs := by
  induction hsp with
  | nil Ψ Θ A =>
    intro cs Ts es cs' Bs πS πT _ _ _ _ _ hlen _
    simp at hlen
  | @pat Ψ Ψ₁ Ψ₂ Θ Θ₁ Θ₂ p qs A B C Γ₁ Γ₂ hp _ ih =>
    intro cs Ts es cs' Bs πS πT hvarS hfv hoks hT hs hlen hm
    cases es with
    | nil =>
      cases hs
      exact isElimTy_rename hfv (by rw [← hT]; simp [IsElimTy])
    | cons e es =>
      cases hs with
      | proj _ _ _ _ =>
        exact (hm (by simp [matchSpine, matchCopat, MatchRes.and_no_left])).elim
      | instT _ _ _ =>
        exact (hm (by simp [matchSpine, matchCopat, MatchRes.and_no_left])).elim
      | instS _ _ _ =>
        exact (hm (by simp [matchSpine, matchCopat, MatchRes.and_no_left])).elim
      | @term _ _ T₁ T₂ _ s _ hsT hs' =>
        simp only [Ty.substSize, Ty.substFTy] at hT
        injection hT with _ hB
        refine ih cs T₂ es cs' Bs πS πT hvarS hfv hoks.term hB hs' (by simpa using hlen) ?_
        intro hno
        apply hm
        simp only [matchSpine, hno, MatchRes.and_no_right]
  | @proj Ψ Ψ' Θ Θ' d j qs a R Rd C Γ hd hj _ ih =>
    intro cs Ts es cs' Bs πS πT hvarS hfv hoks hT hs hlen hm
    cases es with
    | nil =>
      cases hs
      exact isElimTy_rename hfv (by rw [← hT]; simp [IsElimTy])
    | cons e es =>
      cases hs with
      | term _ _ =>
        exact (hm (by simp [matchSpine, matchCopat, MatchRes.and_no_left])).elim
      | instT _ _ _ =>
        exact (hm (by simp [matchSpine, matchCopat, MatchRes.and_no_left])).elim
      | instS _ _ _ =>
        exact (hm (by simp [matchSpine, matchCopat, MatchRes.and_no_left])).elim
      | @proj _ _ as Rs d' js Rds _ β _ hds hjs hβ hs' =>
        by_cases hdd : d = d'
        · subst hdd
          have hT' := align_proj_ty (cs := cs) (j := j) hfv hT hoks.tyWf hd hds hjs
          refine ih _ _ es cs' Bs _ πT (hvarS.cons js j) hfv (hoks.proj hds hjs hβ) hT' hs'
            (by simpa using hlen) ?_
          intro hno
          apply hm
          simp only [matchSpine, hno, MatchRes.and_no_right]
        · exact (hm (by simp [matchSpine, matchCopat, hdd, MatchRes.and_no_left])).elim
  | @instT Ψ Ψ' Θ Θ' X κ qs B C Γ hX _ ih =>
    intro cs Ts es cs' Bs πS πT hvarS hfv hoks hT hs hlen hm
    cases es with
    | nil =>
      cases hs
      exact isElimTy_rename hfv (by rw [← hT]; simp [IsElimTy])
    | cons e es =>
      cases hs with
      | term _ _ =>
        exact (hm (by simp [matchSpine, matchCopat, MatchRes.and_no_left])).elim
      | proj _ _ _ _ =>
        exact (hm (by simp [matchSpine, matchCopat, MatchRes.and_no_left])).elim
      | instS _ _ _ =>
        simp only [Ty.substSize, Ty.substFTy] at hT
        cases hT
      | @instT _ _ κs Bs' _ Xs Y _ hXs hY hs' =>
        simp only [Ty.substSize, Ty.substFTy] at hT
        injection hT with hκ hB
        subst hκ
        have hBs : TyWf cs.Ψ (cs.Θ.map Prod.fst) 1 0 Bs' := by
          simpa using (Kinding.inv_allT hoks.2.2.2).2.tyWf
        have hT' := align_instT_ty (cs := cs) (X := X) hfv hB hBs hXs
        refine ih _ _ es cs' Bs πS _ hvarS (hfv.cons Xs X) (hoks.instT hXs hY) hT' hs'
          (by simpa using hlen) ?_
        intro hno
        apply hm
        simp only [matchSpine, hno, MatchRes.and_no_right]
  | @instS Ψ Ψ' Θ Θ' j qs a B C Γ hj _ ih =>
    intro cs Ts es cs' Bs πS πT hvarS hfv hoks hT hs hlen hm
    cases es with
    | nil =>
      cases hs
      exact isElimTy_rename hfv (by rw [← hT]; simp [IsElimTy])
    | cons e es =>
      cases hs with
      | term _ _ =>
        exact (hm (by simp [matchSpine, matchCopat, MatchRes.and_no_left])).elim
      | proj _ _ _ _ =>
        exact (hm (by simp [matchSpine, matchCopat, MatchRes.and_no_left])).elim
      | instT _ _ _ =>
        simp only [Ty.substSize, Ty.substFTy] at hT
        cases hT
      | @instS _ _ as Bs' _ js β _ hjs hβ hs' =>
        have hT' := align_instS_ty (cs := cs) (j := j) hvarS hfv hT hoks.tyWf hjs
        refine ih _ _ es cs' Bs _ πT (hvarS.cons js j) hfv (hoks.instS hjs hβ) hT' hs'
          (by simpa using hlen) ?_
        intro hno
        apply hm
        simp only [matchSpine, hno, MatchRes.and_no_right]

theorem semSpine_args_sn {W : World} (hW : WorldClosed W) {c c' : SCtx} {T C : Ty}
    {es : List Elim} (hs : SemSpine W c T es c' C) :
    PosOK W c T → ∀ s, Elim.term s ∈ es → SN W s := by
  induction hs with
  | nil => intro _ s h; simp at h
  | @term c₀ c₁ T₁ T₂ C₀ s₀ es₀ hsT _ ih =>
    intro hok s h
    rcases List.mem_cons.mp h with h' | h'
    · injection h' with h'; subst h'
      exact (interp_closed_mem hW hok.dom c₀.ρ hok.2.2.1 hsT).2
    · exact ih hok.term s h'
  | proj hd hj hβ _ ih =>
    intro hok s h
    rcases List.mem_cons.mp h with h' | h'
    · cases h'
    · exact ih (hok.proj hd hj hβ) s h'
  | instT hX hY _ ih =>
    intro hok s h
    rcases List.mem_cons.mp h with h' | h'
    · cases h'
    · exact ih (hok.instT hX hY) s h'
  | instS hj hβ _ ih =>
    intro hok s h
    rcases List.mem_cons.mp h with h' | h'
    · cases h'
    · exact ih (hok.instS hj hβ) s h'

theorem spineStep_length {W : World} {es es' : List Elim} (h : SpineStep W es es') :
    es'.length = es.length := by
  induction h with
  | here => rfl
  | there _ ih => simp [ih]

theorem appSpine_head_not_intro {h : Tm} (hh : IsHead h) (es : List Elim) :
    ¬ IsIntro (Tm.appSpine h es) := by
  intro hi
  cases es using List.reverseRecOn with
  | nil => cases h <;> simp_all [IsHead, IsIntro]
  | append_singleton es e => simp [IsIntro] at hi

/-- The clause-head lemma. `hshape` says that a clause longer than the spine whose copatterns do
not yet mismatch it only occurs at elimination types; it follows from clause typing
(`spine_shape`). At all other types a stuck clause-headed term is neutral. -/
theorem clause_head {W : World} (hW : WorldClosed W) {h : Tm} {D : List Clause} (hh : IsHead h)
    (hclosed : h.Closed)
    (hsel : ∀ es, headStep W (Tm.appSpine h es) = selectClause D es)
    {c : SCtx} {A : Ty} (hok : PosOK W c A)
    (hsound : ∀ es u c' C, SemSpine W c A es c' C → selectClause D es = some u →
      u ∈ c'.den W C)
    (hshape : ∀ es c' C, SemSpine W c A es c' C → ∀ qs t, Clause.mk qs t ∈ D →
      es.length < qs.length → matchSpine qs es ≠ .no → IsElimTy C) :
    ∀ es c' C, SemSpine W c A es c' C → Tm.appSpine h es ∈ c'.den W C := by
  suffices H : ∀ n es c' C, maxLen D - es.length = n → SemSpine W c A es c' C →
      Tm.appSpine h es ∈ c'.den W C by
    intro es c' C hs; exact H _ es c' C rfl hs
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
  intro es c' C hn hs
  have hacc := spineStep_acc es (semSpine_args_sn hW hs hok)
  induction hacc generalizing c' C with
  | intro es _ ihacc =>
  have hpos := semSpine_posOK hs hok
  have hcand : Cand W (c'.den W C) := interp_cand_closed hW hpos.2.2.2 c'.ρ hpos.2.2.1
  have htc : (Tm.appSpine h es).Closed := by
    unfold Tm.Closed
    rw [Tm.fv_appSpine, hclosed, semSpine_closed hW hs hok]
    rfl
  have hni := appSpine_head_not_intro hh es
  have hred : ∀ t', Step W (Tm.appSpine h es) t' →
      (selectClause D es = some t') ∨ (∃ es', SpineStep W es es' ∧ t' = Tm.appSpine h es') := by
    intro t' hst
    rcases step_appSpine_head hh es t' hst with h' | h'
    · left; rw [← hsel]; exact h'
    · right; exact h'
  have hIH : ∀ es', SpineStep W es es' → Tm.appSpine h es' ∈ c'.den W C := by
    intro es' hst
    have hs' := semSpine_spineStep hW hs hok es' hst
    exact ihacc es' hst c' C (by rw [spineStep_length hst]; exact hn) hs'
  cases hselc : selectClause D es with
  | some u =>
    have hu := hsound es u c' C hs hselc
    apply hcand.neutral _ htc (neutral_of_headStep (by rw [hsel]; exact hselc))
    intro t' hst
    rcases hred t' hst with h' | ⟨es', hst', rfl⟩
    · rw [hselc] at h'; cases h'; exact hu
    · exact hIH es' hst'
  | none =>
    by_cases hlong : ∀ qs t, Clause.mk qs t ∈ D → es.length < qs.length →
        matchSpine qs es = .no
    · apply hcand.neutral _ htc
      · apply neutral_of_stuck hni
        intro es₂
        rw [← Tm.appSpine_append, hsel]
        exact selectClause_append_none hlong hselc es₂
      · intro t' hst
        rcases hred t' hst with h' | ⟨es', hst', rfl⟩
        · rw [hselc] at h'; cases h'
        · exact hIH es' hst'
    · push_neg at hlong
      obtain ⟨qs, t, hmem, hlt, hne⟩ := hlong
      have helim := hshape es c' C hs qs t hmem hlt hne
      have hL : es.length < maxLen D :=
        lt_of_lt_of_le hlt (le_maxLen (cl := .mk qs t) hmem)
      have hsn : SN W (Tm.appSpine h es) := SN.of_reducts fun t' hst => by
        rcases hred t' hst with h' | ⟨es', hst', rfl⟩
        · rw [hselc] at h'; cases h'
        · exact (hcand.sn _ (hIH es' hst')).2
      have hlt' : maxLen D - (es.length + 1) < n := by omega
      cases C with
      | arr C₁ C₂ =>
        simp only [SCtx.den, interpT]
        rw [interp_arr_star]
        refine ⟨⟨htc, hsn⟩, fun s hsC => ?_⟩
        have hs'' := semSpine_snoc hs (.term hsC (.nil _ _))
        have := ihn _ hlt' (es ++ [.term s]) c' C₂ (by simp) hs''
        simpa [SCtx.den] using this
      | nu a R =>
        simp only [SCtx.den, interpT]
        rw [interp_nu_star, NuSet_eq]
        refine ⟨⟨htc, hsn⟩, fun β hβ d hd => ?_⟩
        obtain ⟨j, hj⟩ := exists_fresh c'.Ψ.dom
        have hdR : R[d]? = some R[d] := List.getElem?_eq_getElem hd
        have hs'' := semSpine_snoc hs (.proj hdR hj hβ (.nil _ _))
        have := ihn _ hlt' (es ++ [.proj d]) _ _ (by simp) hs''
        simp only [SCtx.den, SCtx.extSz] at this
        rw [interp_unfold_nu_fresh hpos.tyWf hj hdR β] at this
        simpa using this
      | allT κ B =>
        simp only [SCtx.den, interpT]
        rw [interp_allT_star]
        refine ⟨⟨htc, hsn⟩, fun Y hY => ?_⟩
        obtain ⟨X, hX⟩ := exists_fresh (c'.Θ.map Prod.fst)
        have hB : TyWf c'.Ψ (c'.Θ.map Prod.fst) 1 0 B := by
          simpa using (Kinding.inv_allT hpos.2.2.2).2.tyWf
        have hs'' := semSpine_snoc hs (.instT hX hY (.nil _ _))
        have := ihn _ hlt' (es ++ [.inst]) _ _ (by simp) hs''
        simp only [SCtx.den, SCtx.extTy, interpT] at this
        rw [interp_open_fresh_ty hB hX] at this
        simpa using this
      | allS a B =>
        simp only [SCtx.den, interpT]
        rw [interp_allS_star]
        refine ⟨⟨htc, hsn⟩, fun β hβ => ?_⟩
        obtain ⟨j, hj⟩ := exists_fresh c'.Ψ.dom
        have hB : TyWf c'.Ψ (c'.Θ.map Prod.fst) 0 1 B := by
          simpa using (Kinding.inv_allS hpos.2.2.2).2.2.tyWf
        have hs'' := semSpine_snoc hs (.instS hj hβ (.nil _ _))
        have := ihn _ hlt' (es ++ [.inst]) _ _ (by simp) hs''
        simp only [SCtx.den, SCtx.extSz, interpT] at this
        rw [interp_open_fresh_sz hB hj] at this
        simpa using this
      | unit => simp [IsElimTy] at helim
      | prod _ _ => simp [IsElimTy] at helim
      | var _ => simp [IsElimTy] at helim
      | fvar _ => simp [IsElimTy] at helim
      | lam _ _ => simp [IsElimTy] at helim
      | app _ _ _ => simp [IsElimTy] at helim
      | mu _ _ => simp [IsElimTy] at helim
      | exT _ _ => simp [IsElimTy] at helim
      | exS _ _ => simp [IsElimTy] at helim

end NishtAbel2024V5


