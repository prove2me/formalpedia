-- Prove2me | Definitions.Def_NishtAbel2024V5_SemKinding
-- name    : NishtAbel2024V5_SemKinding
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-07T04:23:27.519929+00:00
-- url     : https://prove2.me/theorems/6dd968f3-2013-4e8f-b97f-11df16da2e5c
-- title:
--   Chapter 5.3 (V5 Support): Semantic Substitution Lemmas, Polarized Kinding Soundness, and Syntactic Well-Formedness
-- statement:
--   Establishes the semantic interpretation lemmas for shifting and substituting type and size variables, the relational kinding interpretation `KRel` and soundness of polarized higher-kinded kinding (`kinding_sound`, Theorem 2 part 2), and syntactic scope/kinding preservation under opening and substitution (`TyWf`, `Kinding`).
-- source:
--   Nisht & Abel 2024, Kind Inference and Termination Checking in a Language with Co-Patterns and Size-Change Termination, https://urn.kb.se/resolve?urn=urn:nbn:se:chalmers:diva-542843, Chapter 5, Section 5.3, pp. 35-36, Theorem 2

import Definitions.Def_NishtAbel2024V5_SemBasic

/-! ## Solutions/V5/Interp.lean -/

/-! # V5: scoping and substitution lemmas for the interpretation -/

namespace NishtAbel2024V5

/-! ## Scoping -/

/-- `Ψ; Θ; k; m ⊢ A` (scoping only): free sizes in `Ψ`, free type variables in `Θ`, bound type
variables below `k`, bound size variables below `m`. -/
inductive TyWf (Ψ : SizeCtx) (Θ : List Nat) : Nat → Nat → Ty → Prop where
  | unit (k m : Nat) : TyWf Ψ Θ k m .unit
  | prod {k m : Nat} {A B : Ty} : TyWf Ψ Θ k m A → TyWf Ψ Θ k m B → TyWf Ψ Θ k m (.prod A B)
  | arr {k m : Nat} {A B : Ty} : TyWf Ψ Θ k m A → TyWf Ψ Θ k m B → TyWf Ψ Θ k m (.arr A B)
  | var {k m X : Nat} : X < k → TyWf Ψ Θ k m (.var X)
  | fvar {k m X : Nat} : X ∈ Θ → TyWf Ψ Θ k m (.fvar X)
  | lam {k m : Nat} {ι : SKind} {F : Ty} : TyWf Ψ Θ (k + 1) m F → TyWf Ψ Θ k m (.lam ι F)
  | app {k m : Nat} {F G : Ty} {ι : SKind} :
      TyWf Ψ Θ k m F → TyWf Ψ Θ k m G → TyWf Ψ Θ k m (.app F G ι)
  | mu {k m : Nat} {a : Size} {S : List Ty} :
      SizeWfAt Ψ m a → (∀ T ∈ S, TyWf Ψ Θ (k + 1) m T) → TyWf Ψ Θ k m (.mu a S)
  | nu {k m : Nat} {a : Size} {R : List Ty} :
      SizeWfAt Ψ m a → (∀ T ∈ R, TyWf Ψ Θ (k + 1) m T) → TyWf Ψ Θ k m (.nu a R)
  | allT {k m : Nat} {κ : Kind} {B : Ty} : TyWf Ψ Θ (k + 1) m B → TyWf Ψ Θ k m (.allT κ B)
  | exT {k m : Nat} {κ : Kind} {B : Ty} : TyWf Ψ Θ (k + 1) m B → TyWf Ψ Θ k m (.exT κ B)
  | allS {k m : Nat} {a : Size} {B : Ty} :
      SizeWfAt Ψ m a → TyWf Ψ Θ k (m + 1) B → TyWf Ψ Θ k m (.allS a B)
  | exS {k m : Nat} {a : Size} {B : Ty} :
      SizeWfAt Ψ m a → TyWf Ψ Θ k (m + 1) B → TyWf Ψ Θ k m (.exS a B)

/-! ## Environments -/

/-- Insert `X` at position `k`, shifting the variables above. -/
def Env.insert (k : Nat) (X : PSem) (η : Env) : Env := fun n =>
  if n < k then η n else if n = k then X else η (n - 1)

theorem Env.insert_succ_cons (k : Nat) (X Y : PSem) (η : Env) :
    Env.insert (k + 1) X (Env.cons Y η) = Env.cons Y (Env.insert k X η) := by
  funext n
  cases n with
  | zero => simp [Env.insert, Env.cons]
  | succ n =>
    simp only [Env.insert, Env.cons]
    by_cases h1 : n < k
    · simp [h1]
    · by_cases h2 : n = k
      · subst h2; simp
      · have h3 : ¬ n + 1 < k + 1 := by omega
        have h4 : n + 1 ≠ k + 1 := by omega
        simp only [h1, h2, h3, h4, if_false]
        cases n with
        | zero => omega
        | succ n => rfl

theorem Env.insert_zero (X : PSem) (η : Env) : Env.insert 0 X η = Env.cons X η := by
  funext n
  cases n with
  | zero => simp [Env.insert, Env.cons]
  | succ n => simp [Env.insert, Env.cons]

theorem Env.cons_agree {η η' : Env} {k : Nat} (h : ∀ n < k, η n = η' n) (X : PSem) :
    ∀ n < k + 1, Env.cons X η n = Env.cons X η' n
  | 0, _ => rfl
  | n + 1, hn => h n (by omega)

/-! ## Agreement -/

theorem interpAt_congr {W : World} {ρ ρ' : SizeVal} {θ θ' : TEnv} {S : List Ty} {ζ ζ' : SzEnv}
    {η η' : Env} (h : ∀ c (hc : c < S.length),
      interp W ρ θ (S[c]'hc) .star ζ η = interp W ρ' θ' (S[c]'hc) .star ζ' η') (c : Nat) :
    interpAt W ρ θ S c ζ η = interpAt W ρ' θ' S c ζ' η' := by
  by_cases hc : c < S.length
  · rw [interpAt_eq W ρ θ S c _ _ hc, interpAt_eq W ρ' θ' S c _ _ hc]
    exact h c hc
  · rw [interpAt_out W ρ θ S c _ _ (by omega), interpAt_out W ρ' θ' S c _ _ (by omega)]

theorem interp_agree {W : World} {Ψ : SizeCtx} {Θ : List Nat} {k m : Nat} {A : Ty}
    (hA : TyWf Ψ Θ k m A) :
    ∀ (ρ ρ' : SizeVal) (θ θ' : TEnv) (ζ ζ' : SzEnv) (η η' : Env),
      (∀ i ∈ Ψ.dom, ρ i = ρ' i) → (∀ X ∈ Θ, θ X = θ' X) → (∀ x < m, ζ x = ζ' x) →
      (∀ X < k, η X = η' X) → ∀ ι, interp W ρ θ A ι ζ η = interp W ρ' θ' A ι ζ' η' := by
  induction hA with
  | unit k => intro _ _ _ _ _ _ _ _ _ _ _ _ _; rfl
  | prod _ _ ihA ihB =>
    intro ρ ρ' θ θ' ζ ζ' η η' hρ hθ hζ hη ι
    simp only [interp]
    rw [ihA ρ ρ' θ θ' ζ ζ' η η' hρ hθ hζ hη, ihB ρ ρ' θ θ' ζ ζ' η η' hρ hθ hζ hη]
  | arr _ _ ihA ihB =>
    intro ρ ρ' θ θ' ζ ζ' η η' hρ hθ hζ hη ι
    simp only [interp]
    rw [ihA ρ ρ' θ θ' ζ ζ' η η' hρ hθ hζ hη, ihB ρ ρ' θ θ' ζ ζ' η η' hρ hθ hζ hη]
  | var hX => intro _ _ _ _ _ _ η η' _ _ _ hη ι; simp only [interp]; rw [hη _ hX]
  | fvar hX => intro _ _ θ θ' _ _ _ _ _ hθ _ _ ι; simp only [interp]; rw [hθ _ hX]
  | lam _ ih =>
    intro ρ ρ' θ θ' ζ ζ' η η' hρ hθ hζ hη ι
    simp only [interp]
    congr 1
    funext ι₁ ι₂ X
    exact ih _ _ _ _ _ _ _ _ hρ hθ hζ (Env.cons_agree hη _) ι₂
  | app _ _ ihF ihG =>
    intro ρ ρ' θ θ' ζ ζ' η η' hρ hθ hζ hη ι
    simp only [interp]
    rw [ihF ρ ρ' θ θ' ζ ζ' η η' hρ hθ hζ hη, ihG ρ ρ' θ θ' ζ ζ' η η' hρ hθ hζ hη]
  | @mu k m a S ha _ ih =>
    intro ρ ρ' θ θ' ζ ζ' η η' hρ hθ hζ hη ι
    simp only [interp]
    rw [sizeVal_agree hρ hζ ha]
    congr 2
    funext c 𝒳
    exact interpAt_congr (fun c hc => ih _ (List.getElem_mem hc) _ _ _ _ _ _ _ _ hρ hθ hζ
      (Env.cons_agree hη _) _) c
  | @nu k m a R ha _ ih =>
    intro ρ ρ' θ θ' ζ ζ' η η' hρ hθ hζ hη ι
    simp only [interp]
    rw [sizeVal_agree hρ hζ ha]
    congr 2
    funext d 𝒳
    exact interpAt_congr (fun c hc => ih _ (List.getElem_mem hc) _ _ _ _ _ _ _ _ hρ hθ hζ
      (Env.cons_agree hη _) _) d
  | allT _ ih =>
    intro ρ ρ' θ θ' ζ ζ' η η' hρ hθ hζ hη ι
    simp only [interp]
    congr 2
    funext X
    exact ih _ _ _ _ _ _ _ _ hρ hθ hζ (Env.cons_agree hη _) _
  | exT _ ih =>
    intro ρ ρ' θ θ' ζ ζ' η η' hρ hθ hζ hη ι
    simp only [interp]
    congr 2
    funext X
    exact ih _ _ _ _ _ _ _ _ hρ hθ hζ (Env.cons_agree hη _) _
  | allS ha _ ih =>
    intro ρ ρ' θ θ' ζ ζ' η η' hρ hθ hζ hη ι
    simp only [interp]
    rw [sizeVal_agree hρ hζ ha]
    congr 2
    funext β
    exact ih _ _ _ _ _ _ _ _ hρ hθ (SzEnv.cons_agree hζ β) hη _
  | exS ha _ ih =>
    intro ρ ρ' θ θ' ζ ζ' η η' hρ hθ hζ hη ι
    simp only [interp]
    rw [sizeVal_agree hρ hζ ha]
    congr 2
    funext β
    exact ih _ _ _ _ _ _ _ _ hρ hθ (SzEnv.cons_agree hζ β) hη _

/-- Types whose interpretation ignores both bound environments. -/
def EnvFree (W : World) (ρ : SizeVal) (θ : TEnv) (T : Ty) : Prop :=
  ∀ (ι : SKind) (ζ ζ' : SzEnv) (η η' : Env), interp W ρ θ T ι ζ η = interp W ρ θ T ι ζ' η'

/-- Locally closed types depend on neither bound environment. -/
theorem envFree_of_closed {W : World} {Ψ : SizeCtx} {Θ : List Nat} {T : Ty}
    (hT : TyWf Ψ Θ 0 0 T) (ρ : SizeVal) (θ : TEnv) : EnvFree W ρ θ T :=
  fun ι ζ ζ' η η' => interp_agree hT ρ ρ θ θ ζ ζ' η η' (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ h => absurd h (Nat.not_lt_zero _)) (fun _ h => absurd h (Nat.not_lt_zero _)) ι

/-- The kind-polymorphic value denoted by a type. -/
noncomputable def tyVal (W : World) (ρ : SizeVal) (θ : TEnv) (T : Ty) (ζ : SzEnv) (η : Env) :
    PSem :=
  fun ι => interp W ρ θ T ι ζ η

/-! ## Lengths -/

theorem Ty.substSizeList_length (σ : List (Nat × Size)) :
    ∀ S : List Ty, (Ty.substSizeList σ S).length = S.length
  | [] => rfl
  | _ :: S => by simp [Ty.substSizeList, Ty.substSizeList_length σ S]

theorem Ty.substTyList_length (k : Nat) (T : Ty) :
    ∀ S : List Ty, (Ty.substTyList S k T).length = S.length
  | [] => rfl
  | _ :: S => by simp [Ty.substTyList, Ty.substTyList_length k T S]

theorem Ty.openSzList_length (k : Nat) (b : Size) :
    ∀ S : List Ty, (Ty.openSzList S k b).length = S.length
  | [] => rfl
  | _ :: S => by simp [Ty.openSzList, Ty.openSzList_length k b S]

theorem Ty.substFTyList_length (τ : List (Nat × Ty)) :
    ∀ S : List Ty, (Ty.substFTyList τ S).length = S.length
  | [] => rfl
  | _ :: S => by simp [Ty.substFTyList, Ty.substFTyList_length τ S]

/-! ## Substitution of free size variables -/

mutual

theorem interp_substSize (W : World) (ρ : SizeVal) (θ : TEnv) {σ : List (Nat × Size)}
    (hσ : LCSubst σ) :
    ∀ (A : Ty) (ι : SKind) (ζ : SzEnv) (η : Env),
      interp W ρ θ (A.substSize σ) ι ζ η = interp W (substVal ρ σ) θ A ι ζ η
  | .unit, _, _, _ => rfl
  | .prod A B, ι, ζ, η => by
    simp only [Ty.substSize, interp]
    rw [interp_substSize W ρ θ hσ A, interp_substSize W ρ θ hσ B]
  | .arr A B, ι, ζ, η => by
    simp only [Ty.substSize, interp]
    rw [interp_substSize W ρ θ hσ A, interp_substSize W ρ θ hσ B]
  | .var _, _, _, _ => rfl
  | .fvar _, _, _, _ => rfl
  | .lam ι' F, ι, ζ, η => by
    simp only [Ty.substSize, interp]
    congr 1
    funext ι₁ ι₂ X
    exact interp_substSize W ρ θ hσ F ι₂ ζ _
  | .app F G ι', ι, ζ, η => by
    simp only [Ty.substSize, interp]
    rw [interp_substSize W ρ θ hσ F, interp_substSize W ρ θ hσ G]
  | .mu a S, ι, ζ, η => by
    simp only [Ty.substSize, interp]
    rw [sizeVal_subst hσ]
    congr 2
    funext c 𝒳
    exact interpAt_substSize W ρ θ hσ S c ζ _
  | .nu a R, ι, ζ, η => by
    simp only [Ty.substSize, interp]
    rw [sizeVal_subst hσ, Ty.substSizeList_length]
    congr 2
    funext d 𝒳
    exact interpAt_substSize W ρ θ hσ R d ζ _
  | .allT κ B, ι, ζ, η => by
    simp only [Ty.substSize, interp]
    congr 2
    funext X
    exact interp_substSize W ρ θ hσ B _ ζ _
  | .exT κ B, ι, ζ, η => by
    simp only [Ty.substSize, interp]
    congr 2
    funext X
    exact interp_substSize W ρ θ hσ B _ ζ _
  | .allS a B, ι, ζ, η => by
    simp only [Ty.substSize, interp]
    rw [sizeVal_subst hσ]
    congr 2
    funext β
    exact interp_substSize W ρ θ hσ B _ _ η
  | .exS a B, ι, ζ, η => by
    simp only [Ty.substSize, interp]
    rw [sizeVal_subst hσ]
    congr 2
    funext β
    exact interp_substSize W ρ θ hσ B _ _ η

theorem interpAt_substSize (W : World) (ρ : SizeVal) (θ : TEnv) {σ : List (Nat × Size)}
    (hσ : LCSubst σ) :
    ∀ (S : List Ty) (c : Nat) (ζ : SzEnv) (η : Env),
      interpAt W ρ θ (Ty.substSizeList σ S) c ζ η = interpAt W (substVal ρ σ) θ S c ζ η
  | [], c, _, _ => by cases c <;> rfl
  | A :: _, 0, ζ, η => interp_substSize W ρ θ hσ A .star ζ η
  | _ :: S, c + 1, ζ, η => interpAt_substSize W ρ θ hσ S c ζ η

end

/-! ## Substitution of bound type variables -/

mutual

theorem interp_substTy (W : World) (ρ : SizeVal) (θ : TEnv) {T : Ty} (hT : EnvFree W ρ θ T) :
    ∀ (A : Ty) (k : Nat) (ι : SKind) (ζ : SzEnv) (η : Env),
      interp W ρ θ (A.substTy k T) ι ζ η =
        interp W ρ θ A ι ζ (Env.insert k (tyVal W ρ θ T ζ η) η)
  | .unit, _, _, _, _ => rfl
  | .prod A B, k, ι, ζ, η => by
    simp only [Ty.substTy, interp]
    rw [interp_substTy W ρ θ hT A k, interp_substTy W ρ θ hT B k]
  | .arr A B, k, ι, ζ, η => by
    simp only [Ty.substTy, interp]
    rw [interp_substTy W ρ θ hT A k, interp_substTy W ρ θ hT B k]
  | .var X, k, ι, ζ, η => by
    by_cases h1 : X = k
    · subst h1; simp [Ty.substTy, interp, Env.insert, tyVal]
    · by_cases h2 : k < X
      · have h3 : ¬ X < k := by omega
        simp [Ty.substTy, h1, h2, h3, interp, Env.insert]
      · have h3 : X < k := by omega
        simp [Ty.substTy, h1, h2, h3, interp, Env.insert]
  | .fvar _, _, _, _, _ => rfl
  | .lam ι' F, k, ι, ζ, η => by
    simp only [Ty.substTy, interp]
    congr 1
    funext ι₁ ι₂ X
    rw [interp_substTy W ρ θ hT F (k + 1), Env.insert_succ_cons]
    congr 3
    funext ι₃
    exact hT ι₃ ζ ζ _ η
  | .app F G ι', k, ι, ζ, η => by
    simp only [Ty.substTy, interp]
    rw [interp_substTy W ρ θ hT F k, interp_substTy W ρ θ hT G k]
  | .mu a S, k, ι, ζ, η => by
    simp only [Ty.substTy, interp]
    congr 2
    funext c 𝒳
    rw [interpAt_substTy W ρ θ hT S c (k + 1), Env.insert_succ_cons]
    congr 3
    funext ι₃
    exact hT ι₃ ζ ζ _ η
  | .nu a R, k, ι, ζ, η => by
    simp only [Ty.substTy, interp]
    rw [Ty.substTyList_length]
    congr 2
    funext d 𝒳
    rw [interpAt_substTy W ρ θ hT R d (k + 1), Env.insert_succ_cons]
    congr 3
    funext ι₃
    exact hT ι₃ ζ ζ _ η
  | .allT κ B, k, ι, ζ, η => by
    simp only [Ty.substTy, interp]
    congr 2
    funext X
    rw [interp_substTy W ρ θ hT B (k + 1), Env.insert_succ_cons]
    congr 3
    funext ι₃
    exact hT ι₃ ζ ζ _ η
  | .exT κ B, k, ι, ζ, η => by
    simp only [Ty.substTy, interp]
    congr 2
    funext X
    rw [interp_substTy W ρ θ hT B (k + 1), Env.insert_succ_cons]
    congr 3
    funext ι₃
    exact hT ι₃ ζ ζ _ η
  | .allS a B, k, ι, ζ, η => by
    simp only [Ty.substTy, interp]
    congr 2
    funext β
    rw [interp_substTy W ρ θ hT B k]
    congr 2
    funext ι₃
    exact hT ι₃ _ ζ η η
  | .exS a B, k, ι, ζ, η => by
    simp only [Ty.substTy, interp]
    congr 2
    funext β
    rw [interp_substTy W ρ θ hT B k]
    congr 2
    funext ι₃
    exact hT ι₃ _ ζ η η

theorem interpAt_substTy (W : World) (ρ : SizeVal) (θ : TEnv) {T : Ty} (hT : EnvFree W ρ θ T) :
    ∀ (S : List Ty) (c k : Nat) (ζ : SzEnv) (η : Env),
      interpAt W ρ θ (Ty.substTyList S k T) c ζ η =
        interpAt W ρ θ S c ζ (Env.insert k (tyVal W ρ θ T ζ η) η)
  | [], c, _, _, _ => by cases c <;> rfl
  | A :: _, 0, k, ζ, η => interp_substTy W ρ θ hT A k .star ζ η
  | _ :: S, c + 1, k, ζ, η => interpAt_substTy W ρ θ hT S c k ζ η

end

/-! ## Opening bound size variables -/

mutual

theorem interp_openSz (W : World) (ρ : SizeVal) (θ : TEnv) {b : Size} (hb : b.LC) :
    ∀ (A : Ty) (k : Nat) (ι : SKind) (ζ : SzEnv) (η : Env),
      interp W ρ θ (A.openSz k b) ι ζ η =
        interp W ρ θ A ι (SzEnv.insert k (sizeVal ρ ζ b) ζ) η
  | .unit, _, _, _, _ => rfl
  | .prod A B, k, ι, ζ, η => by
    simp only [Ty.openSz, interp]
    rw [interp_openSz W ρ θ hb A k, interp_openSz W ρ θ hb B k]
  | .arr A B, k, ι, ζ, η => by
    simp only [Ty.openSz, interp]
    rw [interp_openSz W ρ θ hb A k, interp_openSz W ρ θ hb B k]
  | .var _, _, _, _, _ => rfl
  | .fvar _, _, _, _, _ => rfl
  | .lam ι' F, k, ι, ζ, η => by
    simp only [Ty.openSz, interp]
    congr 1
    funext ι₁ ι₂ X
    exact interp_openSz W ρ θ hb F k ι₂ ζ _
  | .app F G ι', k, ι, ζ, η => by
    simp only [Ty.openSz, interp]
    rw [interp_openSz W ρ θ hb F k, interp_openSz W ρ θ hb G k]
  | .mu a S, k, ι, ζ, η => by
    simp only [Ty.openSz, interp]
    rw [sizeVal_openAt ρ ζ k hb]
    congr 2
    funext c 𝒳
    exact interpAt_openSz W ρ θ hb S c k ζ _
  | .nu a R, k, ι, ζ, η => by
    simp only [Ty.openSz, interp]
    rw [sizeVal_openAt ρ ζ k hb, Ty.openSzList_length]
    congr 2
    funext d 𝒳
    exact interpAt_openSz W ρ θ hb R d k ζ _
  | .allT κ B, k, ι, ζ, η => by
    simp only [Ty.openSz, interp]
    congr 2
    funext X
    exact interp_openSz W ρ θ hb B k _ ζ _
  | .exT κ B, k, ι, ζ, η => by
    simp only [Ty.openSz, interp]
    congr 2
    funext X
    exact interp_openSz W ρ θ hb B k _ ζ _
  | .allS a B, k, ι, ζ, η => by
    simp only [Ty.openSz, interp]
    rw [sizeVal_openAt ρ ζ k hb]
    congr 2
    funext β
    rw [interp_openSz W ρ θ hb B (k + 1), SzEnv.insert_succ_cons,
      sizeVal_lc ρ (SzEnv.cons β ζ) ζ hb]
  | .exS a B, k, ι, ζ, η => by
    simp only [Ty.openSz, interp]
    rw [sizeVal_openAt ρ ζ k hb]
    congr 2
    funext β
    rw [interp_openSz W ρ θ hb B (k + 1), SzEnv.insert_succ_cons,
      sizeVal_lc ρ (SzEnv.cons β ζ) ζ hb]

theorem interpAt_openSz (W : World) (ρ : SizeVal) (θ : TEnv) {b : Size} (hb : b.LC) :
    ∀ (S : List Ty) (c k : Nat) (ζ : SzEnv) (η : Env),
      interpAt W ρ θ (Ty.openSzList S k b) c ζ η =
        interpAt W ρ θ S c (SzEnv.insert k (sizeVal ρ ζ b) ζ) η
  | [], c, _, _, _ => by cases c <;> rfl
  | A :: _, 0, k, ζ, η => interp_openSz W ρ θ hb A k .star ζ η
  | _ :: S, c + 1, k, ζ, η => interpAt_openSz W ρ θ hb S c k ζ η

end

/-! ## Substitution of free type variables -/

/-- The type environment induced by a substitution of types for free type variables. -/
noncomputable def substTVal (W : World) (ρ : SizeVal) (θ : TEnv) (τ : List (Nat × Ty)) : TEnv :=
  fun X =>
    match τ.lookup X with
    | some T => tyVal W ρ θ T SzEnv.zero Env.empty
    | none => θ X

mutual

theorem interp_substFTy (W : World) (ρ : SizeVal) (θ : TEnv) {τ : List (Nat × Ty)}
    (hτ : ∀ X T, τ.lookup X = some T → EnvFree W ρ θ T) :
    ∀ (A : Ty) (ι : SKind) (ζ : SzEnv) (η : Env),
      interp W ρ θ (A.substFTy τ) ι ζ η = interp W ρ (substTVal W ρ θ τ) A ι ζ η
  | .unit, _, _, _ => rfl
  | .prod A B, ι, ζ, η => by
    simp only [Ty.substFTy, interp]
    rw [interp_substFTy W ρ θ hτ A, interp_substFTy W ρ θ hτ B]
  | .arr A B, ι, ζ, η => by
    simp only [Ty.substFTy, interp]
    rw [interp_substFTy W ρ θ hτ A, interp_substFTy W ρ θ hτ B]
  | .var _, _, _, _ => rfl
  | .fvar X, ι, ζ, η => by
    show interp W ρ θ ((τ.lookup X).getD (.fvar X)) ι ζ η = substTVal W ρ θ τ X ι
    unfold substTVal
    cases h : τ.lookup X with
    | none => rfl
    | some T => exact hτ X T h ι ζ SzEnv.zero η Env.empty
  | .lam ι' F, ι, ζ, η => by
    simp only [Ty.substFTy, interp]
    congr 1
    funext ι₁ ι₂ X
    exact interp_substFTy W ρ θ hτ F ι₂ ζ _
  | .app F G ι', ι, ζ, η => by
    simp only [Ty.substFTy, interp]
    rw [interp_substFTy W ρ θ hτ F, interp_substFTy W ρ θ hτ G]
  | .mu a S, ι, ζ, η => by
    simp only [Ty.substFTy, interp]
    congr 2
    funext c 𝒳
    exact interpAt_substFTy W ρ θ hτ S c ζ _
  | .nu a R, ι, ζ, η => by
    simp only [Ty.substFTy, interp]
    rw [Ty.substFTyList_length]
    congr 2
    funext d 𝒳
    exact interpAt_substFTy W ρ θ hτ R d ζ _
  | .allT κ B, ι, ζ, η => by
    simp only [Ty.substFTy, interp]
    congr 2
    funext X
    exact interp_substFTy W ρ θ hτ B _ ζ _
  | .exT κ B, ι, ζ, η => by
    simp only [Ty.substFTy, interp]
    congr 2
    funext X
    exact interp_substFTy W ρ θ hτ B _ ζ _
  | .allS a B, ι, ζ, η => by
    simp only [Ty.substFTy, interp]
    congr 2
    funext β
    exact interp_substFTy W ρ θ hτ B _ _ η
  | .exS a B, ι, ζ, η => by
    simp only [Ty.substFTy, interp]
    congr 2
    funext β
    exact interp_substFTy W ρ θ hτ B _ _ η

theorem interpAt_substFTy (W : World) (ρ : SizeVal) (θ : TEnv) {τ : List (Nat × Ty)}
    (hτ : ∀ X T, τ.lookup X = some T → EnvFree W ρ θ T) :
    ∀ (S : List Ty) (c : Nat) (ζ : SzEnv) (η : Env),
      interpAt W ρ θ (Ty.substFTyList τ S) c ζ η = interpAt W ρ (substTVal W ρ θ τ) S c ζ η
  | [], c, _, _ => by cases c <;> rfl
  | A :: _, 0, ζ, η => interp_substFTy W ρ θ hτ A .star ζ η
  | _ :: S, c + 1, ζ, η => interpAt_substFTy W ρ θ hτ S c ζ η

end

/-! ## Unfolding and opening -/

/-- A `*`-former denotes the same kind-polymorphic value as its `*`-component. -/
theorem tyVal_mu (W : World) (ρ : SizeVal) (θ : TEnv) (b : Size) (S : List Ty) (ζ : SzEnv)
    (η : Env) :
    tyVal W ρ θ (.mu b S) ζ η = PSem.ofSem .star (interp W ρ θ (.mu b S) .star ζ η) := by
  funext ι
  cases ι with
  | star => rfl
  | arr ι₁ ι₂ => rfl

theorem tyVal_nu (W : World) (ρ : SizeVal) (θ : TEnv) (b : Size) (R : List Ty) (ζ : SzEnv)
    (η : Env) :
    tyVal W ρ θ (.nu b R) ζ η = PSem.ofSem .star (interp W ρ θ (.nu b R) .star ζ η) := by
  funext ι
  cases ι with
  | star => rfl
  | arr ι₁ ι₂ => rfl

/-- Unfolding a branch: `⟦S_c[μ^b S]⟧ = ⟦S_c⟧(stage ⟦b⟧)`. -/
theorem interp_unfold_mu {W : World} {Ψ : SizeCtx} {Θ : List Nat} {ρ : SizeVal} {θ : TEnv}
    {b : Size} {S : List Ty} {c : Nat} (hc : c < S.length) (hwf : TyWf Ψ Θ 0 0 (.mu b S))
    (ζ : SzEnv) (η : Env) :
    interp W ρ θ ((S[c]'hc).substTy 0 (.mu b S)) .star ζ η =
      interpAt W ρ θ S c ζ (Env.cons (PSem.ofSem .star
        (MuSet W (fun c 𝒳 => interpAt W ρ θ S c ζ (Env.cons (PSem.ofSem .star 𝒳) η))
          (sizeVal ρ ζ b))) η) := by
  rw [interp_substTy W ρ θ (envFree_of_closed hwf ρ θ) _ 0 .star ζ η, Env.insert_zero,
    interpAt_eq W ρ θ S c _ _ hc, tyVal_mu]
  rfl

theorem interp_unfold_nu {W : World} {Ψ : SizeCtx} {Θ : List Nat} {ρ : SizeVal} {θ : TEnv}
    {b : Size} {R : List Ty} {d : Nat} (hd : d < R.length) (hwf : TyWf Ψ Θ 0 0 (.nu b R))
    (ζ : SzEnv) (η : Env) :
    interp W ρ θ ((R[d]'hd).substTy 0 (.nu b R)) .star ζ η =
      interpAt W ρ θ R d ζ (Env.cons (PSem.ofSem .star (NuSet W R.length
        (fun d 𝒳 => interpAt W ρ θ R d ζ (Env.cons (PSem.ofSem .star 𝒳) η))
          (sizeVal ρ ζ b))) η) := by
  rw [interp_substTy W ρ θ (envFree_of_closed hwf ρ θ) _ 0 .star ζ η, Env.insert_zero,
    interpAt_eq W ρ θ R d _ _ hd, tyVal_nu]
  rfl

/-- Opening a type binder with a type. -/
theorem interp_openTy {W : World} {ρ : SizeVal} {θ : TEnv} {T : Ty} (hT : EnvFree W ρ θ T)
    (B : Ty) (ι : SKind) (ζ : SzEnv) (η : Env) :
    interp W ρ θ (B.substTy 0 T) ι ζ η = interp W ρ θ B ι ζ (Env.cons (tyVal W ρ θ T ζ η) η) := by
  rw [interp_substTy W ρ θ hT B 0 ι ζ η, Env.insert_zero]

/-- Opening a size binder with a locally closed size. -/
theorem interp_openSz0 (W : World) (ρ : SizeVal) (θ : TEnv) {b : Size} (hb : b.LC) (B : Ty)
    (ι : SKind) (ζ : SzEnv) (η : Env) :
    interp W ρ θ (B.openSz 0 b) ι ζ η =
      interp W ρ θ B ι (SzEnv.cons (sizeVal ρ ζ b) ζ) η := by
  rw [interp_openSz W ρ θ hb B 0 ι ζ η, SzEnv.insert_zero]

end NishtAbel2024V5

/-! ## Solutions/V5/KindSound.lean -/

/-! # V5: soundness of kinding

Every well-kinded type denotes a good semantic value of its kind, and the interpretation respects
the polarities of the variables: for environments related along the declared polarities, the
interpretations are ordered. -/

namespace NishtAbel2024V5

/-! ## Stages for candidate-preserving functors -/

theorem muSet_cand {W : World} (hW : WorldClosed W) (F : Nat → Set Tm → Set Tm) (α : Ordinal.{0}) :
    Cand W (MuSet W F α) := by
  rw [MuSet_eq]; exact introSet_cand hW _

theorem muSet_mono_cand {W : World} (hW : WorldClosed W) {F F' : Nat → Set Tm → Set Tm}
    (h : ∀ c 𝒳 𝒴, Cand W 𝒳 → Cand W 𝒴 → 𝒳 ⊆ 𝒴 → F c 𝒳 ⊆ F' c 𝒴) (α : Ordinal.{0}) :
    MuSet W F α ⊆ MuSet W F' α := by
  induction α using WellFoundedLT.induction with
  | _ α ih =>
    rw [MuSet_eq, MuSet_eq]
    exact introSet_mono fun _ ⟨c, t, β, hβ, hv, ht⟩ =>
      ⟨c, t, β, hβ, hv, h c _ _ (muSet_cand hW F β) (muSet_cand hW F' β) (ih β hβ) ht⟩

theorem muSet_congr_cand {W : World} (hW : WorldClosed W) {F F' : Nat → Set Tm → Set Tm}
    (h : ∀ c 𝒳, Cand W 𝒳 → F c 𝒳 = F' c 𝒳) (α : Ordinal.{0}) :
    MuSet W F α = MuSet W F' α := by
  induction α using WellFoundedLT.induction with
  | _ α ih =>
    rw [MuSet_eq, MuSet_eq]
    congr 1
    funext v
    apply propext
    constructor
    · rintro ⟨c, t, β, hβ, hv, ht⟩
      refine ⟨c, t, β, hβ, hv, ?_⟩
      have e := h c _ (muSet_cand hW F β)
      rw [← ih β hβ, ← e]
      exact ht
    · rintro ⟨c, t, β, hβ, hv, ht⟩
      refine ⟨c, t, β, hβ, hv, ?_⟩
      have e := h c _ (muSet_cand hW F β)
      rw [e, ih β hβ]
      exact ht

theorem nuSet_mono_cand {W : World} (hW : WorldClosed W) {n : Nat}
    {G G' : Nat → Set Tm → Set Tm} (hG : ∀ d < n, ∀ 𝒳, Cand W 𝒳 → Cand W (G d 𝒳))
    (hG' : ∀ d < n, ∀ 𝒳, Cand W 𝒳 → Cand W (G' d 𝒳))
    (h : ∀ d < n, ∀ 𝒳 𝒴, Cand W 𝒳 → Cand W 𝒴 → 𝒳 ⊆ 𝒴 → G d 𝒳 ⊆ G' d 𝒴)
    (α : Ordinal.{0}) : NuSet W n G α ⊆ NuSet W n G' α := by
  induction α using WellFoundedLT.induction with
  | _ α ih =>
    rw [NuSet_eq, NuSet_eq]
    exact fun _ ht => ⟨ht.1, fun β hβ d hd =>
      h d hd _ _ (nuSet_cand hW n hG β) (nuSet_cand hW n hG' β) (ih β hβ) (ht.2 β hβ d hd)⟩

theorem nuSet_congr_cand {W : World} (hW : WorldClosed W) {n : Nat}
    {G G' : Nat → Set Tm → Set Tm} (hG : ∀ d < n, ∀ 𝒳, Cand W 𝒳 → Cand W (G d 𝒳))
    (h : ∀ d < n, ∀ 𝒳, Cand W 𝒳 → G d 𝒳 = G' d 𝒳) (α : Ordinal.{0}) :
    NuSet W n G α = NuSet W n G' α := by
  induction α using WellFoundedLT.induction with
  | _ α ih =>
    rw [NuSet_eq, NuSet_eq]
    ext t
    constructor
    · intro ht
      refine ⟨ht.1, fun β hβ d hd => ?_⟩
      rw [← ih β hβ, ← h d hd _ (nuSet_cand hW n hG β)]
      exact ht.2 β hβ d hd
    · intro ht
      refine ⟨ht.1, fun β hβ d hd => ?_⟩
      rw [h d hd _ (nuSet_cand hW n hG β), ih β hβ]
      exact ht.2 β hβ d hd

/-! ## Equations of the interpretation at kind `*` -/

theorem interp_unit_star (W : World) (ρ : SizeVal) (θ : TEnv) (ζ : SzEnv) (η : Env) :
    interp W ρ θ .unit .star ζ η = UnitSet W := rfl

theorem interp_prod_star (W : World) (ρ : SizeVal) (θ : TEnv) (A B : Ty) (ζ : SzEnv) (η : Env) :
    interp W ρ θ (.prod A B) .star ζ η =
      ProdSet W (interp W ρ θ A .star ζ η) (interp W ρ θ B .star ζ η) := rfl

theorem interp_arr_star (W : World) (ρ : SizeVal) (θ : TEnv) (A B : Ty) (ζ : SzEnv) (η : Env) :
    interp W ρ θ (.arr A B) .star ζ η =
      ArrSet W (interp W ρ θ A .star ζ η) (interp W ρ θ B .star ζ η) := rfl

theorem interp_mu_star (W : World) (ρ : SizeVal) (θ : TEnv) (a : Size) (S : List Ty)
    (ζ : SzEnv) (η : Env) :
    interp W ρ θ (.mu a S) .star ζ η =
      MuSet W (fun c 𝒳 => interpAt W ρ θ S c ζ (Env.cons (PSem.ofSem .star 𝒳) η))
        (sizeVal ρ ζ a) := rfl

theorem interp_nu_star (W : World) (ρ : SizeVal) (θ : TEnv) (a : Size) (R : List Ty)
    (ζ : SzEnv) (η : Env) :
    interp W ρ θ (.nu a R) .star ζ η =
      NuSet W R.length (fun d 𝒳 => interpAt W ρ θ R d ζ (Env.cons (PSem.ofSem .star 𝒳) η))
        (sizeVal ρ ζ a) := rfl

theorem interp_allT_star (W : World) (ρ : SizeVal) (θ : TEnv) (κ : Kind) (B : Ty) (ζ : SzEnv)
    (η : Env) :
    interp W ρ θ (.allT κ B) .star ζ η =
      AllTSet W κ (fun X => interp W ρ θ B .star ζ (Env.cons (PSem.ofSem κ.erase X) η)) := rfl

theorem interp_exT_star (W : World) (ρ : SizeVal) (θ : TEnv) (κ : Kind) (B : Ty) (ζ : SzEnv)
    (η : Env) :
    interp W ρ θ (.exT κ B) .star ζ η =
      ExTSet W κ (fun X => interp W ρ θ B .star ζ (Env.cons (PSem.ofSem κ.erase X) η)) := rfl

theorem interp_allS_star (W : World) (ρ : SizeVal) (θ : TEnv) (a : Size) (B : Ty) (ζ : SzEnv)
    (η : Env) :
    interp W ρ θ (.allS a B) .star ζ η =
      AllSSet W (sizeVal ρ ζ a) (fun β => interp W ρ θ B .star (SzEnv.cons β ζ) η) := rfl

theorem interp_exS_star (W : World) (ρ : SizeVal) (θ : TEnv) (a : Size) (B : Ty) (ζ : SzEnv)
    (η : Env) :
    interp W ρ θ (.exS a B) .star ζ η =
      ExSSet W (sizeVal ρ ζ a) (fun β => interp W ρ θ B .star (SzEnv.cons β ζ) η) := rfl

theorem interp_lam_arr (W : World) (ρ : SizeVal) (θ : TEnv) (ι : SKind) (F : Ty)
    (ι₁ ι₂ : SKind) (ζ : SzEnv) (η : Env) :
    interp W ρ θ (.lam ι F) (.arr ι₁ ι₂) ζ η =
      fun X => interp W ρ θ F ι₂ ζ (Env.cons (PSem.ofSem ι₁ X) η) := rfl

theorem interp_app (W : World) (ρ : SizeVal) (θ : TEnv) (F G : Ty) (ι₁ ι : SKind) (ζ : SzEnv)
    (η : Env) :
    interp W ρ θ (.app F G ι₁) ι ζ η =
      interp W ρ θ F (.arr ι₁ ι) ζ η (interp W ρ θ G ι₁ ζ η) := rfl

@[simp] theorem Kind.erase_star : Kind.star.erase = SKind.star := rfl

@[simp] theorem Kind.erase_arr (π : Pol) (κ₁ κ₂ : Kind) :
    (Kind.arr π κ₁ κ₂).erase = SKind.arr κ₁.erase κ₂.erase := rfl

/-! ## Related environments -/

/-- Free type variables: good at their kinds, and related along their polarities. -/
def TRel (W : World) (Δ : KCtx) (θ θ' : TEnv) : Prop :=
  ∀ X π κ, Δ.lookup X = some (π, κ) →
    Good W κ (θ X κ.erase) ∧ Good W κ (θ' X κ.erase) ∧ PolRel W π κ (θ X κ.erase) (θ' X κ.erase)

/-- Bound type variables: good at their kinds, and related along their polarities. -/
def BRel (W : World) (Δb : BCtx) (η η' : Env) : Prop :=
  ∀ k π κ, Δb[k]? = some (π, κ) →
    Good W κ (η k κ.erase) ∧ Good W κ (η' k κ.erase) ∧ PolRel W π κ (η k κ.erase) (η' k κ.erase)

theorem KCtx.lookup_inv (π : Pol) :
    ∀ (Δ : KCtx) (X : Nat), (Δ.inv π).lookup X = (Δ.lookup X).map fun e => (Pol.inv π e.1, e.2)
  | [], _ => rfl
  | (Y, π', κ) :: Δ, X => by
    have ih := KCtx.lookup_inv π Δ X
    simp only [KCtx.inv] at ih ⊢
    simp only [List.map, List.lookup]
    by_cases h : X = Y
    · subst h; simp
    · have hb : (X == Y) = false := by simpa using h
      rw [hb]
      exact ih

theorem BCtx.getElem?_inv (π : Pol) (Δb : BCtx) (k : Nat) :
    (Δb.inv π)[k]? = (Δb[k]?).map fun e => (Pol.inv π e.1, e.2) := by
  simp [BCtx.inv]

/-- How `π⁻¹` acts on related pairs. -/
theorem polRel_inv {W : World} {π π' : Pol} {κ : Kind} {ι : SKind} {X Y : Sem ι}
    (hX : Good W κ X) (hY : Good W κ Y) (h : PolRel W π' κ X Y) :
    (π = .pos → PolRel W (Pol.inv π π') κ X Y) ∧
    (π = .neg → PolRel W (Pol.inv π π') κ Y X) ∧
    (π = .mix → PolRel W (Pol.inv π π') κ X Y ∧ PolRel W (Pol.inv π π') κ Y X) ∧
    (π = .top → PolRel W (Pol.inv π π') κ X X) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro rfl; exact h
  · rintro rfl
    cases π' <;> simp_all [Pol.inv, Pol.negate, PolRel, polRelOf]
  · rintro rfl
    cases π' <;> simp_all [Pol.inv, PolRel, polRelOf]
  · rintro rfl
    exact PolRel.refl _ hX

theorem TRel.left {W : World} {Δ : KCtx} {θ θ' : TEnv} (h : TRel W Δ θ θ') : TRel W Δ θ θ :=
  fun X π κ hX => ⟨(h X π κ hX).1, (h X π κ hX).1, PolRel.refl π (h X π κ hX).1⟩

theorem TRel.right {W : World} {Δ : KCtx} {θ θ' : TEnv} (h : TRel W Δ θ θ') : TRel W Δ θ' θ' :=
  fun X π κ hX => ⟨(h X π κ hX).2.1, (h X π κ hX).2.1, PolRel.refl π (h X π κ hX).2.1⟩

theorem BRel.left {W : World} {Δb : BCtx} {η η' : Env} (h : BRel W Δb η η') : BRel W Δb η η :=
  fun k π κ hk => ⟨(h k π κ hk).1, (h k π κ hk).1, PolRel.refl π (h k π κ hk).1⟩

theorem BRel.right {W : World} {Δb : BCtx} {η η' : Env} (h : BRel W Δb η η') :
    BRel W Δb η' η' :=
  fun k π κ hk => ⟨(h k π κ hk).2.1, (h k π κ hk).2.1, PolRel.refl π (h k π κ hk).2.1⟩

theorem TRel.inv_pos {W : World} {Δ : KCtx} {θ θ' : TEnv} (h : TRel W Δ θ θ') :
    TRel W (Δ.inv .pos) θ θ' := by
  intro X π κ hX
  rw [KCtx.lookup_inv] at hX
  obtain ⟨⟨π', κ'⟩, hX', he⟩ := Option.map_eq_some_iff.mp hX
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  obtain ⟨h1, h2, h3⟩ := h X π' κ' hX'
  exact ⟨h1, h2, (polRel_inv (π := .pos) h1 h2 h3).1 rfl⟩

theorem TRel.inv_neg {W : World} {Δ : KCtx} {θ θ' : TEnv} (h : TRel W Δ θ θ') :
    TRel W (Δ.inv .neg) θ' θ := by
  intro X π κ hX
  rw [KCtx.lookup_inv] at hX
  obtain ⟨⟨π', κ'⟩, hX', he⟩ := Option.map_eq_some_iff.mp hX
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  obtain ⟨h1, h2, h3⟩ := h X π' κ' hX'
  exact ⟨h2, h1, (polRel_inv (π := .neg) h1 h2 h3).2.1 rfl⟩

theorem TRel.inv_mix {W : World} {Δ : KCtx} {θ θ' : TEnv} (h : TRel W Δ θ θ') :
    TRel W (Δ.inv .mix) θ θ' ∧ TRel W (Δ.inv .mix) θ' θ := by
  constructor <;>
  · intro X π κ hX
    rw [KCtx.lookup_inv] at hX
    obtain ⟨⟨π', κ'⟩, hX', he⟩ := Option.map_eq_some_iff.mp hX
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨h1, h2, h3⟩ := h X π' κ' hX'
    have := (polRel_inv (π := .mix) h1 h2 h3).2.2.1 rfl
    first
    | exact ⟨h1, h2, this.1⟩
    | exact ⟨h2, h1, this.2⟩

theorem TRel.inv_refl {W : World} {Δ : KCtx} {θ : TEnv} (h : TRel W Δ θ θ) (π : Pol) :
    TRel W (Δ.inv π) θ θ := by
  intro X π' κ hX
  rw [KCtx.lookup_inv] at hX
  obtain ⟨⟨π'', κ'⟩, hX', he⟩ := Option.map_eq_some_iff.mp hX
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  obtain ⟨h1, _, _⟩ := h X π'' κ' hX'
  exact ⟨h1, h1, PolRel.refl _ h1⟩

theorem BRel.inv_pos {W : World} {Δb : BCtx} {η η' : Env} (h : BRel W Δb η η') :
    BRel W (Δb.inv .pos) η η' := by
  intro k π κ hk
  rw [BCtx.getElem?_inv] at hk
  obtain ⟨⟨π', κ'⟩, hk', he⟩ := Option.map_eq_some_iff.mp hk
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  obtain ⟨h1, h2, h3⟩ := h k π' κ' hk'
  exact ⟨h1, h2, (polRel_inv (π := .pos) h1 h2 h3).1 rfl⟩

theorem BRel.inv_neg {W : World} {Δb : BCtx} {η η' : Env} (h : BRel W Δb η η') :
    BRel W (Δb.inv .neg) η' η := by
  intro k π κ hk
  rw [BCtx.getElem?_inv] at hk
  obtain ⟨⟨π', κ'⟩, hk', he⟩ := Option.map_eq_some_iff.mp hk
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  obtain ⟨h1, h2, h3⟩ := h k π' κ' hk'
  exact ⟨h2, h1, (polRel_inv (π := .neg) h1 h2 h3).2.1 rfl⟩

theorem BRel.inv_mix {W : World} {Δb : BCtx} {η η' : Env} (h : BRel W Δb η η') :
    BRel W (Δb.inv .mix) η η' ∧ BRel W (Δb.inv .mix) η' η := by
  constructor <;>
  · intro k π κ hk
    rw [BCtx.getElem?_inv] at hk
    obtain ⟨⟨π', κ'⟩, hk', he⟩ := Option.map_eq_some_iff.mp hk
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨h1, h2, h3⟩ := h k π' κ' hk'
    have := (polRel_inv (π := .mix) h1 h2 h3).2.2.1 rfl
    first
    | exact ⟨h1, h2, this.1⟩
    | exact ⟨h2, h1, this.2⟩

theorem BRel.inv_refl {W : World} {Δb : BCtx} {η : Env} (h : BRel W Δb η η) (π : Pol) :
    BRel W (Δb.inv π) η η := by
  intro k π' κ hk
  rw [BCtx.getElem?_inv] at hk
  obtain ⟨⟨π'', κ'⟩, hk', he⟩ := Option.map_eq_some_iff.mp hk
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  obtain ⟨h1, _, _⟩ := h k π'' κ' hk'
  exact ⟨h1, h1, PolRel.refl _ h1⟩

theorem BRel.cons {W : World} {Δb : BCtx} {η η' : Env} (h : BRel W Δb η η') {π : Pol}
    {κ : Kind} {X Y : Sem κ.erase} (hX : Good W κ X) (hY : Good W κ Y) (hXY : PolRel W π κ X Y) :
    BRel W ((π, κ) :: Δb) (Env.cons (PSem.ofSem κ.erase X) η)
      (Env.cons (PSem.ofSem κ.erase Y) η') := by
  intro k π' κ' hk
  cases k with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hk
    obtain ⟨rfl, rfl⟩ := hk
    simpa using ⟨hX, hY, hXY⟩
  | succ k => exact h k π' κ' (by simpa using hk)

/-! ## Soundness of kinding -/

/-- A usable polarity relates its arguments by the order. -/
theorem PolRel.le_of_usable {W : World} {π : Pol} (hπ : π.Usable) {κ : Kind} {ι : SKind}
    {X Y : Sem ι} (h : PolRel W π κ X Y) : SemLe W κ X Y := by
  cases π <;> simp_all [Pol.Usable, Pol.le, PolRel, polRelOf]

/-- The semantic statement of kinding: goodness of both interpretations and their order. -/
def KSound (W : World) (κ : Kind) {ι : SKind} (X Y : Sem ι) : Prop :=
  Good W κ X ∧ Good W κ Y ∧ SemLe W κ X Y

theorem kinding_sound {W : World} (hW : WorldClosed W) {Ψ : SizeCtx} {Δ : KCtx} {Δb : BCtx}
    {m : Nat} {A : Ty} {κ : Kind} (h : Kinding Ψ Δ Δb m A κ) :
    ∀ (ρ : SizeVal) (θ θ' : TEnv) (ζ : SzEnv) (η η' : Env), TRel W Δ θ θ' → BRel W Δb η η' →
      KSound W κ (interp W ρ θ A κ.erase ζ η) (interp W ρ θ' A κ.erase ζ η') := by
  induction h with
  | unit =>
    intro ρ θ θ' ζ η η' _ _
    exact ⟨introSet_cand hW _, introSet_cand hW _, subset_refl _⟩
  | prod _ _ ihA ihB =>
    intro ρ θ θ' ζ η η' hθ hη
    have hA := ihA ρ θ θ' ζ η η' hθ hη
    have hB := ihB ρ θ θ' ζ η η' hθ hη
    exact ⟨introSet_cand hW _, introSet_cand hW _, prodSet_mono hA.2.2 hB.2.2⟩
  | arr _ _ ihA ihB =>
    intro ρ θ θ' ζ η η' hθ hη
    have hA := ihA ρ θ' θ ζ η' η hθ.inv_neg hη.inv_neg
    have hB := ihB ρ θ θ' ζ η η' hθ hη
    exact ⟨arrSet_cand hW hA.2.1 hB.1, arrSet_cand hW hA.1 hB.2.1, arrSet_mono hA.2.2 hB.2.2⟩
  | var hk hπ =>
    intro ρ θ θ' ζ η η' _ hη
    obtain ⟨h1, h2, h3⟩ := hη _ _ _ hk
    exact ⟨h1, h2, PolRel.le_of_usable hπ h3⟩
  | fvar hX hπ =>
    intro ρ θ θ' ζ η η' hθ _
    obtain ⟨h1, h2, h3⟩ := hθ _ _ _ hX
    exact ⟨h1, h2, PolRel.le_of_usable hπ h3⟩
  | @lam Δ Δb m ι F π κ₁ κ₂ hι _ ih =>
    intro ρ θ θ' ζ η η' hθ hη
    subst hι
    refine ⟨⟨fun X hX => ?_, fun X Y hX hY hXY => ?_⟩, ⟨fun X hX => ?_, fun X Y hX hY hXY => ?_⟩,
      fun X Y hX hY hXY => ?_⟩
    · exact (ih ρ θ θ ζ _ _ hθ.left (hη.left.cons hX hX (PolRel.refl π hX))).1
    · exact (ih ρ θ θ ζ _ _ hθ.left (hη.left.cons hX hY hXY)).2.2
    · exact (ih ρ θ' θ' ζ _ _ hθ.right (hη.right.cons hX hX (PolRel.refl π hX))).1
    · exact (ih ρ θ' θ' ζ _ _ hθ.right (hη.right.cons hX hY hXY)).2.2
    · exact (ih ρ θ θ' ζ _ _ hθ (hη.cons hX hY hXY)).2.2
  | @app Δ Δb m F G ι π κ₁ κ₂ _ _ hι ihF ihG =>
    intro ρ θ θ' ζ η η' hθ hη
    subst hι
    have hF := ihF ρ θ θ' ζ η η' hθ hη
    have hGl := ihG ρ θ θ ζ η η (hθ.left.inv_refl π) (hη.left.inv_refl π)
    have hGr := ihG ρ θ' θ' ζ η' η' (hθ.right.inv_refl π) (hη.right.inv_refl π)
    have hrel : PolRel W π κ₁ (interp W ρ θ G κ₁.erase ζ η) (interp W ρ θ' G κ₁.erase ζ η') := by
      cases π with
      | pos => exact (ihG ρ θ θ' ζ η η' hθ.inv_pos hη.inv_pos).2.2
      | neg => exact (ihG ρ θ' θ ζ η' η hθ.inv_neg hη.inv_neg).2.2
      | mix =>
        exact ⟨(ihG ρ θ θ' ζ η η' hθ.inv_mix.1 hη.inv_mix.1).2.2,
          (ihG ρ θ' θ ζ η' η hθ.inv_mix.2 hη.inv_mix.2).2.2⟩
      | top => trivial
    exact ⟨hF.1.1 _ hGl.1, hF.2.1.1 _ hGr.1, hF.2.2 _ _ hGl.1 hGr.1 hrel⟩
  | @mu Δ Δb m a S π hπ _ _ ih =>
    intro ρ θ θ' ζ η η' hθ hη
    simp only [Kind.erase_star, interp_mu_star]
    refine ⟨muSet_cand hW _ _, muSet_cand hW _ _, ?_⟩
    rcases hπ with rfl | rfl
    · apply muSet_mono_cand hW
      intro c 𝒳 𝒴 h𝒳 h𝒴 hsub
      by_cases hc : c < S.length
      · rw [interpAt_eq W ρ θ S c _ _ hc, interpAt_eq W ρ θ' S c _ _ hc]
        exact (ih _ (List.getElem_mem hc) ρ θ θ' ζ _ _ hθ.inv_pos
          (hη.inv_pos.cons (κ := .star) h𝒳 h𝒴 hsub)).2.2
      · rw [interpAt_out W ρ θ S c _ _ (by omega)]
        exact Set.empty_subset _
    · apply subset_of_eq
      apply muSet_congr_cand hW
      intro c 𝒳 h𝒳
      by_cases hc : c < S.length
      · rw [interpAt_eq W ρ θ S c _ _ hc, interpAt_eq W ρ θ' S c _ _ hc]
        have hrel : PolRel W .mix .star (ι := .star) 𝒳 𝒳 := PolRel.refl _ (W := W) h𝒳
        exact Set.Subset.antisymm
          (ih _ (List.getElem_mem hc) ρ θ θ' ζ _ _ hθ.inv_mix.1
            (hη.inv_mix.1.cons (κ := .star) h𝒳 h𝒳 hrel)).2.2
          (ih _ (List.getElem_mem hc) ρ θ' θ ζ _ _ hθ.inv_mix.2
            (hη.inv_mix.2.cons (κ := .star) h𝒳 h𝒳 hrel)).2.2
      · rw [interpAt_out W ρ θ S c _ _ (by omega), interpAt_out W ρ θ' S c _ _ (by omega)]
  | @nu Δ Δb m a R π hπ _ _ ih =>
    intro ρ θ θ' ζ η η' hθ hη
    have hG : ∀ (θ₀ : TEnv) (η₀ : Env), TRel W Δ θ₀ θ₀ → BRel W Δb η₀ η₀ →
        ∀ d < R.length, ∀ 𝒳, Cand W 𝒳 →
          Cand W (interpAt W ρ θ₀ R d ζ (Env.cons (PSem.ofSem .star 𝒳) η₀)) := by
      intro θ₀ η₀ hθ₀ hη₀ d hd 𝒳 h𝒳
      rw [interpAt_eq W ρ θ₀ R d _ _ hd]
      exact (ih _ (List.getElem_mem hd) ρ θ₀ θ₀ ζ _ _ (hθ₀.inv_refl π)
        ((hη₀.inv_refl π).cons (κ := .star) h𝒳 h𝒳 (PolRel.refl π (W := W) h𝒳))).1
    simp only [Kind.erase_star, interp_nu_star]
    refine ⟨nuSet_cand hW _ (hG θ η hθ.left hη.left) _,
      nuSet_cand hW _ (hG θ' η' hθ.right hη.right) _, ?_⟩
    rcases hπ with rfl | rfl
    · apply nuSet_mono_cand hW (hG θ η hθ.left hη.left) (hG θ' η' hθ.right hη.right)
      intro d hd 𝒳 𝒴 h𝒳 h𝒴 hsub
      rw [interpAt_eq W ρ θ R d _ _ hd, interpAt_eq W ρ θ' R d _ _ hd]
      exact (ih _ (List.getElem_mem hd) ρ θ θ' ζ _ _ hθ.inv_pos
        (hη.inv_pos.cons (κ := .star) h𝒳 h𝒴 hsub)).2.2
    · apply subset_of_eq
      apply nuSet_congr_cand hW (hG θ η hθ.left hη.left)
      intro d hd 𝒳 h𝒳
      rw [interpAt_eq W ρ θ R d _ _ hd, interpAt_eq W ρ θ' R d _ _ hd]
      have hrel : PolRel W .mix .star (ι := .star) 𝒳 𝒳 := PolRel.refl _ (W := W) h𝒳
      exact Set.Subset.antisymm
        (ih _ (List.getElem_mem hd) ρ θ θ' ζ _ _ hθ.inv_mix.1
          (hη.inv_mix.1.cons (κ := .star) h𝒳 h𝒳 hrel)).2.2
        (ih _ (List.getElem_mem hd) ρ θ' θ ζ _ _ hθ.inv_mix.2
          (hη.inv_mix.2.cons (κ := .star) h𝒳 h𝒳 hrel)).2.2
  | @allT Δ Δb m κ B _ ih =>
    intro ρ θ θ' ζ η η' hθ hη
    refine ⟨allTSet_cand hW fun X hX => ?_, allTSet_cand hW fun X hX => ?_,
      allTSet_mono fun X hX => ?_⟩
    · exact (ih ρ θ θ ζ _ _ hθ.left (hη.left.cons hX hX (PolRel.refl _ hX))).1
    · exact (ih ρ θ' θ' ζ _ _ hθ.right (hη.right.cons hX hX (PolRel.refl _ hX))).1
    · exact (ih ρ θ θ' ζ _ _ hθ (hη.cons hX hX (PolRel.refl _ hX))).2.2
  | @exT Δ Δb m κ B _ ih =>
    intro ρ θ θ' ζ η η' hθ hη
    refine ⟨introSet_cand hW _, introSet_cand hW _, exTSet_mono fun X hX => ?_⟩
    exact (ih ρ θ θ' ζ _ _ hθ (hη.cons hX hX (PolRel.refl _ hX))).2.2
  | allS _ _ ih =>
    intro ρ θ θ' ζ η η' hθ hη
    refine ⟨allSSet_cand hW fun β _ => ?_, allSSet_cand hW fun β _ => ?_,
      allSSet_mono fun β => ?_⟩
    · exact (ih ρ θ θ _ η η hθ.left hη.left).1
    · exact (ih ρ θ' θ' _ η' η' hθ.right hη.right).1
    · exact (ih ρ θ θ' _ η η' hθ hη).2.2
  | exS _ _ ih =>
    intro ρ θ θ' ζ η η' hθ hη
    exact ⟨introSet_cand hW _, introSet_cand hW _,
      exSSet_mono fun β => (ih ρ θ θ' _ η η' hθ hη).2.2⟩
  | sub _ hsub ih =>
    intro ρ θ θ' ζ η η' hθ hη
    rw [← hsub.erase_eq]
    have h := ih ρ θ θ' ζ η η' hθ hη
    exact ⟨Good.sub hsub h.1, Good.sub hsub h.2.1, SemLe.sub hsub h.1 h.2.1 h.2.2⟩

/-! ## Agreement on the declared components -/

theorem interp_agree_kinded {W : World} {Ψ : SizeCtx} {Δ : KCtx} {Δb : BCtx} {m : Nat} {A : Ty}
    {κ : Kind} (h : Kinding Ψ Δ Δb m A κ) :
    ∀ (ρ : SizeVal) (θ θ' : TEnv) (ζ : SzEnv) (η η' : Env),
      (∀ X π κ', Δ.lookup X = some (π, κ') → θ X κ'.erase = θ' X κ'.erase) →
      (∀ k π κ', Δb[k]? = some (π, κ') → η k κ'.erase = η' k κ'.erase) →
      interp W ρ θ A κ.erase ζ η = interp W ρ θ' A κ.erase ζ η' := by
  induction h with
  | unit => intros; rfl
  | prod _ _ ihA ihB =>
    intro ρ θ θ' ζ η η' hθ hη
    have h1 := ihA ρ θ θ' ζ η η' hθ hη
    have h2 := ihB ρ θ θ' ζ η η' hθ hη
    simp only [Kind.erase_star] at h1 h2 ⊢
    rw [interp_prod_star, interp_prod_star, h1, h2]
  | @arr Δ Δb m A B _ _ ihA ihB =>
    intro ρ θ θ' ζ η η' hθ hη
    have hθ' : ∀ X π κ', (KCtx.inv .neg Δ).lookup X = some (π, κ') →
        θ X κ'.erase = θ' X κ'.erase := by
      intro X π κ' hX
      rw [KCtx.lookup_inv] at hX
      obtain ⟨⟨π', κ''⟩, hX', he⟩ := Option.map_eq_some_iff.mp hX
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact hθ X π' _ hX'
    have hη' : ∀ k π κ', (BCtx.inv .neg Δb)[k]? = some (π, κ') →
        η k κ'.erase = η' k κ'.erase := by
      intro k π κ' hk
      rw [BCtx.getElem?_inv] at hk
      obtain ⟨⟨π', κ''⟩, hk', he⟩ := Option.map_eq_some_iff.mp hk
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact hη k π' _ hk'
    have h1 := ihA ρ θ θ' ζ η η' hθ' hη'
    have h2 := ihB ρ θ θ' ζ η η' hθ hη
    simp only [Kind.erase_star] at h1 h2 ⊢
    rw [interp_arr_star, interp_arr_star, h1, h2]
  | var hk _ =>
    intro ρ θ θ' ζ η η' _ hη
    exact hη _ _ _ hk
  | fvar hX _ =>
    intro ρ θ θ' ζ η η' hθ _
    exact hθ _ _ _ hX
  | @lam Δ Δb m ι F π κ₁ κ₂ hι _ ih =>
    intro ρ θ θ' ζ η η' hθ hη
    subst hι
    simp only [Kind.erase_arr, interp_lam_arr]
    funext X
    apply ih ρ θ θ' ζ _ _ hθ
    intro k π' κ' hk
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hk
      obtain ⟨rfl, rfl⟩ := hk
      rfl
    | succ k => exact hη k π' κ' (by simpa using hk)
  | @app Δ Δb m F G ι π κ₁ κ₂ _ _ hι ihF ihG =>
    intro ρ θ θ' ζ η η' hθ hη
    subst hι
    have hθ' : ∀ X π' κ', (KCtx.inv π Δ).lookup X = some (π', κ') →
        θ X κ'.erase = θ' X κ'.erase := by
      intro X π' κ' hX
      rw [KCtx.lookup_inv] at hX
      obtain ⟨⟨π'', κ''⟩, hX', he⟩ := Option.map_eq_some_iff.mp hX
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact hθ X π'' _ hX'
    have hη' : ∀ k π' κ', (BCtx.inv π Δb)[k]? = some (π', κ') →
        η k κ'.erase = η' k κ'.erase := by
      intro k π' κ' hk
      rw [BCtx.getElem?_inv] at hk
      obtain ⟨⟨π'', κ''⟩, hk', he⟩ := Option.map_eq_some_iff.mp hk
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact hη k π'' _ hk'
    have h1 := ihF ρ θ θ' ζ η η' hθ hη
    have h2 := ihG ρ θ θ' ζ η η' hθ' hη'
    simp only [Kind.erase_arr] at h1
    rw [interp_app, interp_app, h1, h2]
  | @mu Δ Δb m a S π _ _ _ ih =>
    intro ρ θ θ' ζ η η' hθ hη
    have hθ' : ∀ X π' κ', (KCtx.inv π Δ).lookup X = some (π', κ') →
        θ X κ'.erase = θ' X κ'.erase := by
      intro X π' κ' hX
      rw [KCtx.lookup_inv] at hX
      obtain ⟨⟨π'', κ''⟩, hX', he⟩ := Option.map_eq_some_iff.mp hX
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact hθ X π'' _ hX'
    simp only [Kind.erase_star, interp_mu_star]
    congr 1
    funext c 𝒳
    apply interpAt_congr
    intro c hc
    apply ih _ (List.getElem_mem hc) ρ θ θ' ζ _ _ hθ'
    intro k π' κ' hk
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hk
      obtain ⟨rfl, rfl⟩ := hk
      rfl
    | succ k =>
      simp only [List.getElem?_cons_succ] at hk
      rw [BCtx.getElem?_inv] at hk
      obtain ⟨⟨π'', κ''⟩, hk', he⟩ := Option.map_eq_some_iff.mp hk
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact hη k π'' _ hk'
  | @nu Δ Δb m a R π _ _ _ ih =>
    intro ρ θ θ' ζ η η' hθ hη
    have hθ' : ∀ X π' κ', (KCtx.inv π Δ).lookup X = some (π', κ') →
        θ X κ'.erase = θ' X κ'.erase := by
      intro X π' κ' hX
      rw [KCtx.lookup_inv] at hX
      obtain ⟨⟨π'', κ''⟩, hX', he⟩ := Option.map_eq_some_iff.mp hX
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact hθ X π'' _ hX'
    simp only [Kind.erase_star, interp_nu_star]
    congr 1
    funext d 𝒳
    apply interpAt_congr
    intro c hc
    apply ih _ (List.getElem_mem hc) ρ θ θ' ζ _ _ hθ'
    intro k π' κ' hk
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hk
      obtain ⟨rfl, rfl⟩ := hk
      rfl
    | succ k =>
      simp only [List.getElem?_cons_succ] at hk
      rw [BCtx.getElem?_inv] at hk
      obtain ⟨⟨π'', κ''⟩, hk', he⟩ := Option.map_eq_some_iff.mp hk
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact hη k π'' _ hk'
  | @allT Δ Δb m κ B _ ih =>
    intro ρ θ θ' ζ η η' hθ hη
    simp only [Kind.erase_star, interp_allT_star]
    congr 1
    funext X
    apply ih ρ θ θ' ζ _ _ hθ
    intro k π' κ' hk
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hk
      obtain ⟨rfl, rfl⟩ := hk
      rfl
    | succ k => exact hη k π' κ' (by simpa using hk)
  | @exT Δ Δb m κ B _ ih =>
    intro ρ θ θ' ζ η η' hθ hη
    simp only [Kind.erase_star, interp_exT_star]
    congr 1
    funext X
    apply ih ρ θ θ' ζ _ _ hθ
    intro k π' κ' hk
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hk
      obtain ⟨rfl, rfl⟩ := hk
      rfl
    | succ k => exact hη k π' κ' (by simpa using hk)
  | allS _ _ ih =>
    intro ρ θ θ' ζ η η' hθ hη
    simp only [Kind.erase_star, interp_allS_star]
    congr 1
    funext β
    exact ih ρ θ θ' _ η η' hθ hη
  | exS _ _ ih =>
    intro ρ θ θ' ζ η η' hθ hη
    simp only [Kind.erase_star, interp_exS_star]
    congr 1
    funext β
    exact ih ρ θ θ' _ η η' hθ hη
  | sub _ hsub ih =>
    intro ρ θ θ' ζ η η' hθ hη
    rw [← hsub.erase_eq]
    exact ih ρ θ θ' ζ η η' hθ hη

end NishtAbel2024V5

/-! ## Solutions/V5/Wf.lean -/

/-! # V5: syntactic lemmas about scoping and kinding -/

namespace NishtAbel2024V5

/-! ## List membership under the list-mapping operations -/

theorem Ty.mem_substTyList {S : List Ty} {k : Nat} {T T' : Ty} (h : T' ∈ Ty.substTyList S k T) :
    ∃ B ∈ S, T' = B.substTy k T := by
  induction S with
  | nil => simp [Ty.substTyList] at h
  | cons A S ih =>
    simp only [Ty.substTyList, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨A, by simp, rfl⟩
    · obtain ⟨B, hB, rfl⟩ := ih h; exact ⟨B, by simp [hB], rfl⟩

theorem Ty.mem_openSzList {S : List Ty} {k : Nat} {b : Size} {T' : Ty}
    (h : T' ∈ Ty.openSzList S k b) : ∃ B ∈ S, T' = B.openSz k b := by
  induction S with
  | nil => simp [Ty.openSzList] at h
  | cons A S ih =>
    simp only [Ty.openSzList, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨A, by simp, rfl⟩
    · obtain ⟨B, hB, rfl⟩ := ih h; exact ⟨B, by simp [hB], rfl⟩

theorem Ty.mem_substSizeList {S : List Ty} {σ : List (Nat × Size)} {T' : Ty}
    (h : T' ∈ Ty.substSizeList σ S) : ∃ B ∈ S, T' = B.substSize σ := by
  induction S with
  | nil => simp [Ty.substSizeList] at h
  | cons A S ih =>
    simp only [Ty.substSizeList, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨A, by simp, rfl⟩
    · obtain ⟨B, hB, rfl⟩ := ih h; exact ⟨B, by simp [hB], rfl⟩

theorem Ty.mem_substFTyList {S : List Ty} {τ : List (Nat × Ty)} {T' : Ty}
    (h : T' ∈ Ty.substFTyList τ S) : ∃ B ∈ S, T' = B.substFTy τ := by
  induction S with
  | nil => simp [Ty.substFTyList] at h
  | cons A S ih =>
    simp only [Ty.substFTyList, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨A, by simp, rfl⟩
    · obtain ⟨B, hB, rfl⟩ := ih h; exact ⟨B, by simp [hB], rfl⟩

theorem Ty.substSizeList_getElem? (σ : List (Nat × Size)) :
    ∀ (S : List Ty) (d : Nat), (Ty.substSizeList σ S)[d]? = (S[d]?).map (Ty.substSize σ)
  | [], d => by simp [Ty.substSizeList]
  | A :: S, 0 => by simp [Ty.substSizeList]
  | A :: S, d + 1 => by
    simp only [Ty.substSizeList, List.getElem?_cons_succ]
    exact Ty.substSizeList_getElem? σ S d

theorem Ty.substFTyList_getElem? (τ : List (Nat × Ty)) :
    ∀ (S : List Ty) (d : Nat), (Ty.substFTyList τ S)[d]? = (S[d]?).map (Ty.substFTy τ)
  | [], d => by simp [Ty.substFTyList]
  | A :: S, 0 => by simp [Ty.substFTyList]
  | A :: S, d + 1 => by
    simp only [Ty.substFTyList, List.getElem?_cons_succ]
    exact Ty.substFTyList_getElem? τ S d

theorem Ty.substTyList_getElem? (k : Nat) (T : Ty) :
    ∀ (S : List Ty) (d : Nat), (Ty.substTyList S k T)[d]? = (S[d]?).map (Ty.substTy · k T)
  | [], d => by simp [Ty.substTyList]
  | A :: S, 0 => by simp [Ty.substTyList]
  | A :: S, d + 1 => by
    simp only [Ty.substTyList, List.getElem?_cons_succ]
    exact Ty.substTyList_getElem? k T S d

theorem Ty.openSzList_getElem? (k : Nat) (b : Size) :
    ∀ (S : List Ty) (d : Nat), (Ty.openSzList S k b)[d]? = (S[d]?).map (Ty.openSz · k b)
  | [], d => by simp [Ty.openSzList]
  | A :: S, 0 => by simp [Ty.openSzList]
  | A :: S, d + 1 => by
    simp only [Ty.openSzList, List.getElem?_cons_succ]
    exact Ty.openSzList_getElem? k b S d

/-! ## Scoping: weakening, substitution, opening -/

theorem SizeWfAt.weaken {Ψ Ψ' : SizeCtx} {m m' : Nat} (h : ∀ i ∈ Ψ.dom, i ∈ Ψ'.dom)
    (hm : m ≤ m') : ∀ {a : Size}, SizeWfAt Ψ m a → SizeWfAt Ψ' m' a
  | .inf _, _ => trivial
  | .var i _, ha => h i ha
  | .bvar k _, ha => lt_of_lt_of_le (show k < m from ha) hm
  | .meet _ _, ha => ⟨SizeWfAt.weaken h hm ha.1, SizeWfAt.weaken h hm ha.2⟩

theorem TyWf.weaken {Ψ : SizeCtx} {Θ : List Nat} {k m : Nat} {A : Ty} (hA : TyWf Ψ Θ k m A) :
    ∀ (Ψ' : SizeCtx) (Θ' : List Nat) (k' m' : Nat), (∀ i ∈ Ψ.dom, i ∈ Ψ'.dom) →
      (∀ X ∈ Θ, X ∈ Θ') → k ≤ k' → m ≤ m' → TyWf Ψ' Θ' k' m' A := by
  induction hA with
  | unit k m => intro _ _ _ _ _ _ _ _; exact .unit _ _
  | prod _ _ ihA ihB =>
    intro Ψ' Θ' k' m' h hΘ hk hm
    exact .prod (ihA Ψ' Θ' k' m' h hΘ hk hm) (ihB Ψ' Θ' k' m' h hΘ hk hm)
  | arr _ _ ihA ihB =>
    intro Ψ' Θ' k' m' h hΘ hk hm
    exact .arr (ihA Ψ' Θ' k' m' h hΘ hk hm) (ihB Ψ' Θ' k' m' h hΘ hk hm)
  | var hX => intro _ _ _ _ _ _ hk _; exact .var (by omega)
  | fvar hX => intro _ _ _ _ _ hΘ _ _; exact .fvar (hΘ _ hX)
  | lam _ ih =>
    intro Ψ' Θ' k' m' h hΘ hk hm
    exact .lam (ih Ψ' Θ' (k' + 1) m' h hΘ (by omega) hm)
  | app _ _ ihF ihG =>
    intro Ψ' Θ' k' m' h hΘ hk hm
    exact .app (ihF Ψ' Θ' k' m' h hΘ hk hm) (ihG Ψ' Θ' k' m' h hΘ hk hm)
  | mu ha _ ih =>
    intro Ψ' Θ' k' m' h hΘ hk hm
    exact .mu (ha.weaken h hm) (fun T hT => ih T hT Ψ' Θ' (k' + 1) m' h hΘ (by omega) hm)
  | nu ha _ ih =>
    intro Ψ' Θ' k' m' h hΘ hk hm
    exact .nu (ha.weaken h hm) (fun T hT => ih T hT Ψ' Θ' (k' + 1) m' h hΘ (by omega) hm)
  | allT _ ih =>
    intro Ψ' Θ' k' m' h hΘ hk hm
    exact .allT (ih Ψ' Θ' (k' + 1) m' h hΘ (by omega) hm)
  | exT _ ih =>
    intro Ψ' Θ' k' m' h hΘ hk hm
    exact .exT (ih Ψ' Θ' (k' + 1) m' h hΘ (by omega) hm)
  | allS ha _ ih =>
    intro Ψ' Θ' k' m' h hΘ hk hm
    exact .allS (ha.weaken h hm) (ih Ψ' Θ' k' (m' + 1) h hΘ hk (by omega))
  | exS ha _ ih =>
    intro Ψ' Θ' k' m' h hΘ hk hm
    exact .exS (ha.weaken h hm) (ih Ψ' Θ' k' (m' + 1) h hΘ hk (by omega))

theorem dom_append_left {Ψ Ψ' : SizeCtx} : ∀ i ∈ Ψ.dom, i ∈ (Ψ ++ Ψ').dom := by
  intro i hi
  simp only [SizeCtx.dom, List.map_append, List.mem_append]
  exact Or.inl hi

theorem mem_append_left' {Θ Θ' : List Nat} : ∀ X ∈ Θ, X ∈ Θ ++ Θ' :=
  fun _ h => List.mem_append_left _ h

/-- Weakening of locally closed types to larger contexts. -/
theorem TyWf.mono {Ψ : SizeCtx} {Θ : List Nat} {A : Ty} (hA : TyWf Ψ Θ 0 0 A) {Ψ' : SizeCtx}
    {Θ' : List Nat} (h : ∀ i ∈ Ψ.dom, i ∈ Ψ'.dom) (hΘ : ∀ X ∈ Θ, X ∈ Θ') : TyWf Ψ' Θ' 0 0 A :=
  hA.weaken Ψ' Θ' 0 0 h hΘ le_rfl le_rfl

theorem TyWf.substTy {Ψ : SizeCtx} {Θ : List Nat} {n m : Nat} {A : Ty} (hA : TyWf Ψ Θ n m A) :
    ∀ (k : Nat) (T : Ty), n = k + 1 → TyWf Ψ Θ 0 0 T → TyWf Ψ Θ k m (A.substTy k T) := by
  induction hA with
  | unit _ _ => intro _ _ _ _; exact .unit _ _
  | prod _ _ ihA ihB => intro k T hn hT; exact .prod (ihA k T hn hT) (ihB k T hn hT)
  | arr _ _ ihA ihB => intro k T hn hT; exact .arr (ihA k T hn hT) (ihB k T hn hT)
  | @var n m X hX =>
    intro k T hn hT
    simp only [Ty.substTy]
    by_cases h1 : X = k
    · simp only [h1, if_true]
      exact hT.weaken _ _ _ _ (fun i hi => hi) (fun X h => h) (by omega) (by omega)
    · have h2 : ¬ k < X := by omega
      simp only [h1, h2, if_false]; exact .var (by omega)
  | fvar hX => intro _ _ _ _; exact .fvar hX
  | lam _ ih => intro k T hn hT; exact .lam (ih (k + 1) T (by omega) hT)
  | app _ _ ihF ihG => intro k T hn hT; exact .app (ihF k T hn hT) (ihG k T hn hT)
  | mu ha _ ih =>
    intro k T hn hT
    simp only [Ty.substTy]
    refine .mu ha (fun T' hT' => ?_)
    obtain ⟨B, hB, rfl⟩ := Ty.mem_substTyList hT'
    exact ih B hB _ _ (by omega) hT
  | nu ha _ ih =>
    intro k T hn hT
    simp only [Ty.substTy]
    refine .nu ha (fun T' hT' => ?_)
    obtain ⟨B, hB, rfl⟩ := Ty.mem_substTyList hT'
    exact ih B hB _ _ (by omega) hT
  | allT _ ih => intro k T hn hT; exact .allT (ih (k + 1) T (by omega) hT)
  | exT _ ih => intro k T hn hT; exact .exT (ih (k + 1) T (by omega) hT)
  | allS ha _ ih => intro k T hn hT; exact .allS ha (ih k T hn hT)
  | exS ha _ ih => intro k T hn hT; exact .exS ha (ih k T hn hT)

theorem SizeWfAt.openAt {Ψ : SizeCtx} {n : Nat} (m : Nat) (hn : n = m + 1) {c : Size}
    (hc : SizeWf Ψ c) : ∀ {a : Size}, SizeWfAt Ψ n a → SizeWfAt Ψ m (a.openAt m c)
  | .inf _, _ => trivial
  | .var _ _, ha => ha
  | .bvar k' k, ha => by
    simp only [Size.openAt]
    have hk' : k' < n := ha
    by_cases h1 : k' = m
    · simp only [h1, if_true]
      exact (SizeWfAt.shift k hc).weaken (fun i h => h) (Nat.zero_le _)
    · have h2 : ¬ m < k' := by omega
      simp only [h1, h2, if_false]
      show k' < m
      omega
  | .meet _ _, ha => ⟨SizeWfAt.openAt m hn hc ha.1, SizeWfAt.openAt m hn hc ha.2⟩

/-- Opening the bound size variable at the level with a locally closed size lowers the level. -/
theorem TyWf.openSz {Ψ : SizeCtx} {Θ : List Nat} {k n : Nat} {A : Ty} (hA : TyWf Ψ Θ k n A) :
    ∀ (m : Nat) (c : Size), n = m + 1 → SizeWf Ψ c → TyWf Ψ Θ k m (A.openSz m c) := by
  induction hA with
  | unit _ _ => intro _ _ _ _; exact .unit _ _
  | prod _ _ ihA ihB => intro m c hn hc; exact .prod (ihA m c hn hc) (ihB m c hn hc)
  | arr _ _ ihA ihB => intro m c hn hc; exact .arr (ihA m c hn hc) (ihB m c hn hc)
  | var hX => intro _ _ _ _; exact .var hX
  | fvar hX => intro _ _ _ _; exact .fvar hX
  | lam _ ih => intro m c hn hc; exact .lam (ih m c hn hc)
  | app _ _ ihF ihG => intro m c hn hc; exact .app (ihF m c hn hc) (ihG m c hn hc)
  | mu ha _ ih =>
    intro m c hn hc
    simp only [Ty.openSz]
    refine .mu (SizeWfAt.openAt m hn hc ha) (fun T' hT' => ?_)
    obtain ⟨B, hB, rfl⟩ := Ty.mem_openSzList hT'
    exact ih B hB m c hn hc
  | nu ha _ ih =>
    intro m c hn hc
    simp only [Ty.openSz]
    refine .nu (SizeWfAt.openAt m hn hc ha) (fun T' hT' => ?_)
    obtain ⟨B, hB, rfl⟩ := Ty.mem_openSzList hT'
    exact ih B hB m c hn hc
  | allT _ ih => intro m c hn hc; exact .allT (ih m c hn hc)
  | exT _ ih => intro m c hn hc; exact .exT (ih m c hn hc)
  | allS ha _ ih =>
    intro m c hn hc
    exact .allS (SizeWfAt.openAt m hn hc ha) (ih (m + 1) c (by omega) hc)
  | exS ha _ ih =>
    intro m c hn hc
    exact .exS (SizeWfAt.openAt m hn hc ha) (ih (m + 1) c (by omega) hc)

theorem TyWf.unfold_mu {Ψ : SizeCtx} {Θ : List Nat} {a b : Size} {S : List Ty} {c : Nat}
    {Sc : Ty} (hwf : TyWf Ψ Θ 0 0 (.mu a S)) (hc : S[c]? = some Sc) (hb : SizeWf Ψ b) :
    TyWf Ψ Θ 0 0 (Sc.substTy 0 (.mu b S)) := by
  cases hwf with
  | mu _ hS =>
    exact (hS Sc (List.mem_of_getElem? hc)).substTy 0 _ rfl (.mu hb hS)

theorem TyWf.unfold_nu {Ψ : SizeCtx} {Θ : List Nat} {a b : Size} {R : List Ty} {d : Nat}
    {Rd : Ty} (hwf : TyWf Ψ Θ 0 0 (.nu a R)) (hd : R[d]? = some Rd) (hb : SizeWf Ψ b) :
    TyWf Ψ Θ 0 0 (Rd.substTy 0 (.nu b R)) := by
  cases hwf with
  | nu _ hR =>
    exact (hR Rd (List.mem_of_getElem? hd)).substTy 0 _ rfl (.nu hb hR)

theorem TyWf.open_ty {Ψ : SizeCtx} {Θ : List Nat} {B T : Ty} (hB : TyWf Ψ Θ 1 0 B)
    (hT : TyWf Ψ Θ 0 0 T) : TyWf Ψ Θ 0 0 (B.substTy 0 T) :=
  hB.substTy 0 T rfl hT

theorem TyWf.open_sz {Ψ : SizeCtx} {Θ : List Nat} {B : Ty} {c : Size} (hB : TyWf Ψ Θ 0 1 B)
    (hc : SizeWf Ψ c) : TyWf Ψ Θ 0 0 (B.openSz 0 c) :=
  hB.openSz 0 c rfl hc

/-! ## Identity substitutions -/

/-- Closed types are not affected by substituting for bound type variables. -/
theorem TyWf.substTy_id {Ψ : SizeCtx} {Θ : List Nat} {n m : Nat} {A : Ty} (hA : TyWf Ψ Θ n m A) :
    ∀ (k : Nat) (U : Ty), n ≤ k → A.substTy k U = A := by
  induction hA with
  | unit _ _ => intro _ _ _; rfl
  | prod _ _ ihA ihB => intro k U h; simp only [Ty.substTy]; rw [ihA k U h, ihB k U h]
  | arr _ _ ihA ihB => intro k U h; simp only [Ty.substTy]; rw [ihA k U h, ihB k U h]
  | var hX =>
    intro k U h
    rename_i n m X
    have h1 : X ≠ k := by omega
    have h2 : ¬ k < X := by omega
    simp [Ty.substTy, h1, h2]
  | fvar _ => intro _ _ _; rfl
  | lam _ ih => intro k U h; simp only [Ty.substTy]; rw [ih (k + 1) U (by omega)]
  | app _ _ ihF ihG => intro k U h; simp only [Ty.substTy]; rw [ihF k U h, ihG k U h]
  | @mu n m a S _ _ ih =>
    intro k U h
    simp only [Ty.substTy]
    congr 1
    exact listEq ih (k + 1) U (by omega)
  | @nu n m a R _ _ ih =>
    intro k U h
    simp only [Ty.substTy]
    congr 1
    exact listEq ih (k + 1) U (by omega)
  | allT _ ih => intro k U h; simp only [Ty.substTy]; rw [ih (k + 1) U (by omega)]
  | exT _ ih => intro k U h; simp only [Ty.substTy]; rw [ih (k + 1) U (by omega)]
  | allS _ _ ih => intro k U h; simp only [Ty.substTy]; rw [ih k U h]
  | exS _ _ ih => intro k U h; simp only [Ty.substTy]; rw [ih k U h]
where
  listEq {S : List Ty} {n : Nat} (ih : ∀ T ∈ S, ∀ (k : Nat) (U : Ty), n ≤ k → T.substTy k U = T)
      (k : Nat) (U : Ty) (h : n ≤ k) : Ty.substTyList S k U = S := by
    induction S with
    | nil => rfl
    | cons A S ihS =>
      simp only [Ty.substTyList]
      rw [ih A (by simp) k U h, ihS (fun T hT => ih T (by simp [hT]))]

theorem Size.openAt_id {Ψ : SizeCtx} {m k : Nat} (c : Size) (h : m ≤ k) :
    ∀ {a : Size}, SizeWfAt Ψ m a → a.openAt k c = a
  | .inf _, _ => rfl
  | .var _ _, _ => rfl
  | .bvar k' n, ha => by
    have hk : k' < m := ha
    have h1 : k' ≠ k := by omega
    have h2 : ¬ k < k' := by omega
    simp [Size.openAt, h1, h2]
  | .meet _ _, ha => by
    simp only [Size.openAt, Size.openAt_id c h ha.1, Size.openAt_id c h ha.2]

theorem Size.openAt_lc (k : Nat) (c : Size) : ∀ {a : Size}, a.LC → a.openAt k c = a
  | .inf _, _ => rfl
  | .var _ _, _ => rfl
  | .bvar _ _, h => absurd h id
  | .meet _ _, h => by simp only [Size.openAt, Size.openAt_lc k c h.1, Size.openAt_lc k c h.2]

/-- Closed types are not affected by opening bound size variables. -/
theorem TyWf.openSz_id {Ψ : SizeCtx} {Θ : List Nat} {n m : Nat} {A : Ty} (hA : TyWf Ψ Θ n m A) :
    ∀ (k : Nat) (c : Size), m ≤ k → A.openSz k c = A := by
  induction hA with
  | unit _ _ => intro _ _ _; rfl
  | prod _ _ ihA ihB => intro k c h; simp only [Ty.openSz]; rw [ihA k c h, ihB k c h]
  | arr _ _ ihA ihB => intro k c h; simp only [Ty.openSz]; rw [ihA k c h, ihB k c h]
  | var _ => intro _ _ _; rfl
  | fvar _ => intro _ _ _; rfl
  | lam _ ih => intro k c h; simp only [Ty.openSz]; rw [ih k c h]
  | app _ _ ihF ihG => intro k c h; simp only [Ty.openSz]; rw [ihF k c h, ihG k c h]
  | @mu n m a S ha _ ih =>
    intro k c h
    simp only [Ty.openSz]
    rw [Size.openAt_id c h ha]
    congr 1
    exact listEq ih k c h
  | @nu n m a R ha _ ih =>
    intro k c h
    simp only [Ty.openSz]
    rw [Size.openAt_id c h ha]
    congr 1
    exact listEq ih k c h
  | allT _ ih => intro k c h; simp only [Ty.openSz]; rw [ih k c h]
  | exT _ ih => intro k c h; simp only [Ty.openSz]; rw [ih k c h]
  | allS ha _ ih =>
    intro k c h; simp only [Ty.openSz]; rw [Size.openAt_id c h ha, ih (k + 1) c (by omega)]
  | exS ha _ ih =>
    intro k c h; simp only [Ty.openSz]; rw [Size.openAt_id c h ha, ih (k + 1) c (by omega)]
where
  listEq {S : List Ty} {m : Nat} (ih : ∀ T ∈ S, ∀ (k : Nat) (c : Size), m ≤ k → T.openSz k c = T)
      (k : Nat) (c : Size) (h : m ≤ k) : Ty.openSzList S k c = S := by
    induction S with
    | nil => rfl
    | cons A S ihS =>
      simp only [Ty.openSzList]
      rw [ih A (by simp) k c h, ihS (fun T hT => ih T (by simp [hT]))]

/-! ## Commutation of the substitutions -/

theorem Size.subst_shift {σ : List (Nat × Size)} :
    ∀ (a : Size) (n : Nat), (a.shift n).subst σ = (a.subst σ).shift n
  | .inf _, _ => rfl
  | .bvar _ _, _ => rfl
  | .var i m, n => by
    simp only [Size.shift, Size.subst]
    cases σ.lookup i with
    | none => rfl
    | some b => simp [Size.shift_shift]
  | .meet a b, n => by
    simp only [Size.shift, Size.subst, Size.subst_shift a n, Size.subst_shift b n]

theorem Size.subst_lc {σ : List (Nat × Size)} (hσ : LCSubst σ) : ∀ {a : Size}, a.LC → (a.subst σ).LC
  | .inf _, _ => trivial
  | .bvar _ _, h => absurd h id
  | .var i n, _ => by
    simp only [Size.subst]
    cases h : σ.lookup i with
    | none => trivial
    | some b => exact Size.LC.shift n (hσ i b h)
  | .meet _ _, h => ⟨Size.subst_lc hσ h.1, Size.subst_lc hσ h.2⟩

theorem Size.subst_openAt {σ : List (Nat × Size)} (hσ : LCSubst σ) (c : Size) (k : Nat) :
    ∀ a : Size, (a.openAt k c).subst σ = (a.subst σ).openAt k (c.subst σ)
  | .inf _ => rfl
  | .var i n => by
    simp only [Size.openAt, Size.subst]
    cases h : σ.lookup i with
    | none => rfl
    | some b => exact (Size.openAt_lc k _ (Size.LC.shift n (hσ i b h))).symm
  | .bvar k' n => by
    show (Size.openAt (.bvar k' n) k c).subst σ = Size.openAt (.bvar k' n) k (c.subst σ)
    simp only [Size.openAt]
    by_cases h1 : k' = k
    · simp only [h1, if_true]
      exact Size.subst_shift c n
    · by_cases h2 : k < k'
      · simp only [h1, h2, if_true, if_false]; rfl
      · simp only [h1, h2, if_false]; rfl
  | .meet a b => by
    simp only [Size.openAt, Size.subst, Size.subst_openAt hσ c k a, Size.subst_openAt hσ c k b]

mutual

theorem Ty.substSize_substTy (σ : List (Nat × Size)) (T : Ty) :
    ∀ (A : Ty) (k : Nat), (A.substTy k T).substSize σ = (A.substSize σ).substTy k (T.substSize σ)
  | .unit, _ => rfl
  | .prod A B, k => by
    simp only [Ty.substTy, Ty.substSize]
    rw [Ty.substSize_substTy σ T A k, Ty.substSize_substTy σ T B k]
  | .arr A B, k => by
    simp only [Ty.substTy, Ty.substSize]
    rw [Ty.substSize_substTy σ T A k, Ty.substSize_substTy σ T B k]
  | .var X, k => by
    simp only [Ty.substTy, Ty.substSize]
    by_cases h1 : X = k
    · simp [h1]
    · by_cases h2 : k < X
      · simp [h1, h2, Ty.substSize]
      · simp [h1, h2, Ty.substSize]
  | .fvar _, _ => rfl
  | .lam ι F, k => by
    simp only [Ty.substTy, Ty.substSize]
    rw [Ty.substSize_substTy σ T F (k + 1)]
  | .app F G ι, k => by
    simp only [Ty.substTy, Ty.substSize]
    rw [Ty.substSize_substTy σ T F k, Ty.substSize_substTy σ T G k]
  | .mu a S, k => by
    simp only [Ty.substTy, Ty.substSize]
    rw [Ty.substSizeList_substTyList σ T S (k + 1)]
  | .nu a R, k => by
    simp only [Ty.substTy, Ty.substSize]
    rw [Ty.substSizeList_substTyList σ T R (k + 1)]
  | .allT κ B, k => by
    simp only [Ty.substTy, Ty.substSize]
    rw [Ty.substSize_substTy σ T B (k + 1)]
  | .exT κ B, k => by
    simp only [Ty.substTy, Ty.substSize]
    rw [Ty.substSize_substTy σ T B (k + 1)]
  | .allS a B, k => by
    simp only [Ty.substTy, Ty.substSize]
    rw [Ty.substSize_substTy σ T B k]
  | .exS a B, k => by
    simp only [Ty.substTy, Ty.substSize]
    rw [Ty.substSize_substTy σ T B k]

theorem Ty.substSizeList_substTyList (σ : List (Nat × Size)) (T : Ty) :
    ∀ (S : List Ty) (k : Nat), Ty.substSizeList σ (Ty.substTyList S k T) =
      Ty.substTyList (Ty.substSizeList σ S) k (T.substSize σ)
  | [], _ => rfl
  | A :: S, k => by
    simp only [Ty.substTyList, Ty.substSizeList]
    rw [Ty.substSize_substTy σ T A k, Ty.substSizeList_substTyList σ T S k]

end

mutual

theorem Ty.substSize_openSz {σ : List (Nat × Size)} (hσ : LCSubst σ) (c : Size) :
    ∀ (A : Ty) (k : Nat), (A.openSz k c).substSize σ = (A.substSize σ).openSz k (c.subst σ)
  | .unit, _ => rfl
  | .prod A B, k => by
    simp only [Ty.openSz, Ty.substSize]
    rw [Ty.substSize_openSz hσ c A k, Ty.substSize_openSz hσ c B k]
  | .arr A B, k => by
    simp only [Ty.openSz, Ty.substSize]
    rw [Ty.substSize_openSz hσ c A k, Ty.substSize_openSz hσ c B k]
  | .var _, _ => rfl
  | .fvar _, _ => rfl
  | .lam ι F, k => by
    simp only [Ty.openSz, Ty.substSize]
    rw [Ty.substSize_openSz hσ c F k]
  | .app F G ι, k => by
    simp only [Ty.openSz, Ty.substSize]
    rw [Ty.substSize_openSz hσ c F k, Ty.substSize_openSz hσ c G k]
  | .mu a S, k => by
    simp only [Ty.openSz, Ty.substSize]
    rw [Size.subst_openAt hσ, Ty.substSizeList_openSzList hσ c S k]
  | .nu a R, k => by
    simp only [Ty.openSz, Ty.substSize]
    rw [Size.subst_openAt hσ, Ty.substSizeList_openSzList hσ c R k]
  | .allT κ B, k => by
    simp only [Ty.openSz, Ty.substSize]
    rw [Ty.substSize_openSz hσ c B k]
  | .exT κ B, k => by
    simp only [Ty.openSz, Ty.substSize]
    rw [Ty.substSize_openSz hσ c B k]
  | .allS a B, k => by
    simp only [Ty.openSz, Ty.substSize]
    rw [Size.subst_openAt hσ, Ty.substSize_openSz hσ c B (k + 1)]
  | .exS a B, k => by
    simp only [Ty.openSz, Ty.substSize]
    rw [Size.subst_openAt hσ, Ty.substSize_openSz hσ c B (k + 1)]

theorem Ty.substSizeList_openSzList {σ : List (Nat × Size)} (hσ : LCSubst σ) (c : Size) :
    ∀ (S : List Ty) (k : Nat), Ty.substSizeList σ (Ty.openSzList S k c) =
      Ty.openSzList (Ty.substSizeList σ S) k (c.subst σ)
  | [], _ => rfl
  | A :: S, k => by
    simp only [Ty.openSzList, Ty.substSizeList]
    rw [Ty.substSize_openSz hσ c A k, Ty.substSizeList_openSzList hσ c S k]

end

/-- Substitutions for free type variables whose values are closed types. -/
def ClosedTSubst (τ : List (Nat × Ty)) : Prop :=
  ∀ X T, τ.lookup X = some T → ∃ Ψ Θ, TyWf Ψ Θ 0 0 T

mutual

theorem Ty.substFTy_substTy {τ : List (Nat × Ty)} (hτ : ClosedTSubst τ) (T : Ty) :
    ∀ (A : Ty) (k : Nat), (A.substTy k T).substFTy τ = (A.substFTy τ).substTy k (T.substFTy τ)
  | .unit, _ => rfl
  | .prod A B, k => by
    simp only [Ty.substTy, Ty.substFTy]
    rw [Ty.substFTy_substTy hτ T A k, Ty.substFTy_substTy hτ T B k]
  | .arr A B, k => by
    simp only [Ty.substTy, Ty.substFTy]
    rw [Ty.substFTy_substTy hτ T A k, Ty.substFTy_substTy hτ T B k]
  | .var X, k => by
    simp only [Ty.substTy, Ty.substFTy]
    by_cases h1 : X = k
    · simp [h1]
    · by_cases h2 : k < X
      · simp [h1, h2, Ty.substFTy]
      · simp [h1, h2, Ty.substFTy]
  | .fvar X, k => by
    simp only [Ty.substTy, Ty.substFTy]
    cases h : τ.lookup X with
    | none => rfl
    | some U =>
      obtain ⟨Ψ, Θ, hU⟩ := hτ X U h
      simp only [Option.getD_some]
      exact (hU.substTy_id k _ (Nat.zero_le _)).symm
  | .lam ι F, k => by
    simp only [Ty.substTy, Ty.substFTy]
    rw [Ty.substFTy_substTy hτ T F (k + 1)]
  | .app F G ι, k => by
    simp only [Ty.substTy, Ty.substFTy]
    rw [Ty.substFTy_substTy hτ T F k, Ty.substFTy_substTy hτ T G k]
  | .mu a S, k => by
    simp only [Ty.substTy, Ty.substFTy]
    rw [Ty.substFTyList_substTyList hτ T S (k + 1)]
  | .nu a R, k => by
    simp only [Ty.substTy, Ty.substFTy]
    rw [Ty.substFTyList_substTyList hτ T R (k + 1)]
  | .allT κ B, k => by
    simp only [Ty.substTy, Ty.substFTy]
    rw [Ty.substFTy_substTy hτ T B (k + 1)]
  | .exT κ B, k => by
    simp only [Ty.substTy, Ty.substFTy]
    rw [Ty.substFTy_substTy hτ T B (k + 1)]
  | .allS a B, k => by
    simp only [Ty.substTy, Ty.substFTy]
    rw [Ty.substFTy_substTy hτ T B k]
  | .exS a B, k => by
    simp only [Ty.substTy, Ty.substFTy]
    rw [Ty.substFTy_substTy hτ T B k]

theorem Ty.substFTyList_substTyList {τ : List (Nat × Ty)} (hτ : ClosedTSubst τ) (T : Ty) :
    ∀ (S : List Ty) (k : Nat), Ty.substFTyList τ (Ty.substTyList S k T) =
      Ty.substTyList (Ty.substFTyList τ S) k (T.substFTy τ)
  | [], _ => rfl
  | A :: S, k => by
    simp only [Ty.substTyList, Ty.substFTyList]
    rw [Ty.substFTy_substTy hτ T A k, Ty.substFTyList_substTyList hτ T S k]

end

mutual

theorem Ty.substFTy_openSz {τ : List (Nat × Ty)} (hτ : ClosedTSubst τ) (c : Size) :
    ∀ (A : Ty) (k : Nat), (A.openSz k c).substFTy τ = (A.substFTy τ).openSz k c
  | .unit, _ => rfl
  | .prod A B, k => by
    simp only [Ty.openSz, Ty.substFTy]
    rw [Ty.substFTy_openSz hτ c A k, Ty.substFTy_openSz hτ c B k]
  | .arr A B, k => by
    simp only [Ty.openSz, Ty.substFTy]
    rw [Ty.substFTy_openSz hτ c A k, Ty.substFTy_openSz hτ c B k]
  | .var _, _ => rfl
  | .fvar X, k => by
    simp only [Ty.openSz, Ty.substFTy]
    cases h : τ.lookup X with
    | none => rfl
    | some U =>
      obtain ⟨Ψ, Θ, hU⟩ := hτ X U h
      simp only [Option.getD_some]
      exact (hU.openSz_id k c (Nat.zero_le _)).symm
  | .lam ι F, k => by
    simp only [Ty.openSz, Ty.substFTy]
    rw [Ty.substFTy_openSz hτ c F k]
  | .app F G ι, k => by
    simp only [Ty.openSz, Ty.substFTy]
    rw [Ty.substFTy_openSz hτ c F k, Ty.substFTy_openSz hτ c G k]
  | .mu a S, k => by
    simp only [Ty.openSz, Ty.substFTy]
    rw [Ty.substFTyList_openSzList hτ c S k]
  | .nu a R, k => by
    simp only [Ty.openSz, Ty.substFTy]
    rw [Ty.substFTyList_openSzList hτ c R k]
  | .allT κ B, k => by
    simp only [Ty.openSz, Ty.substFTy]
    rw [Ty.substFTy_openSz hτ c B k]
  | .exT κ B, k => by
    simp only [Ty.openSz, Ty.substFTy]
    rw [Ty.substFTy_openSz hτ c B k]
  | .allS a B, k => by
    simp only [Ty.openSz, Ty.substFTy]
    rw [Ty.substFTy_openSz hτ c B (k + 1)]
  | .exS a B, k => by
    simp only [Ty.openSz, Ty.substFTy]
    rw [Ty.substFTy_openSz hτ c B (k + 1)]

theorem Ty.substFTyList_openSzList {τ : List (Nat × Ty)} (hτ : ClosedTSubst τ) (c : Size) :
    ∀ (S : List Ty) (k : Nat),
      Ty.substFTyList τ (Ty.openSzList S k c) = Ty.openSzList (Ty.substFTyList τ S) k c
  | [], _ => rfl
  | A :: S, k => by
    simp only [Ty.openSzList, Ty.substFTyList]
    rw [Ty.substFTy_openSz hτ c A k, Ty.substFTyList_openSzList hτ c S k]

end

/-! ## Fresh variables do not matter to substitution -/

theorem Size.subst_cons_fresh {Ψ : SizeCtx} {m : Nat} {i : Nat} (hi : i ∉ Ψ.dom) (b : Size)
    (σ : List (Nat × Size)) : ∀ {a : Size}, SizeWfAt Ψ m a → a.subst ((i, b) :: σ) = a.subst σ
  | .inf _, _ => rfl
  | .bvar _ _, _ => rfl
  | .var x n, ha => by
    have hx : x ≠ i := fun h => hi (h ▸ ha)
    simp only [Size.subst, List.lookup_cons]
    have : (x == i) = false := beq_eq_false_iff_ne.mpr hx
    simp [this]
  | .meet _ _, ha => by
    simp only [Size.subst, Size.subst_cons_fresh hi b σ ha.1, Size.subst_cons_fresh hi b σ ha.2]

theorem substSizeList_congr {S : List Ty} {σ₁ σ₂ : List (Nat × Size)}
    (h : ∀ T ∈ S, T.substSize σ₁ = T.substSize σ₂) :
    Ty.substSizeList σ₁ S = Ty.substSizeList σ₂ S := by
  induction S with
  | nil => rfl
  | cons A S ih =>
    simp only [Ty.substSizeList]
    rw [h A (by simp), ih (fun T hT => h T (by simp [hT]))]

theorem substFTyList_congr {S : List Ty} {τ₁ τ₂ : List (Nat × Ty)}
    (h : ∀ T ∈ S, T.substFTy τ₁ = T.substFTy τ₂) :
    Ty.substFTyList τ₁ S = Ty.substFTyList τ₂ S := by
  induction S with
  | nil => rfl
  | cons A S ih =>
    simp only [Ty.substFTyList]
    rw [h A (by simp), ih (fun T hT => h T (by simp [hT]))]

theorem TyWf.substSize_cons_fresh {Ψ : SizeCtx} {Θ : List Nat} {k m : Nat} {A : Ty}
    (hA : TyWf Ψ Θ k m A) {i : Nat} (hi : i ∉ Ψ.dom) (b : Size) (σ : List (Nat × Size)) :
    A.substSize ((i, b) :: σ) = A.substSize σ := by
  induction hA with
  | unit _ _ => rfl
  | prod _ _ ihA ihB => simp only [Ty.substSize]; rw [ihA, ihB]
  | arr _ _ ihA ihB => simp only [Ty.substSize]; rw [ihA, ihB]
  | var _ => rfl
  | fvar _ => rfl
  | lam _ ih => simp only [Ty.substSize]; rw [ih]
  | app _ _ ihF ihG => simp only [Ty.substSize]; rw [ihF, ihG]
  | mu ha _ ih =>
    simp only [Ty.substSize]
    rw [Size.subst_cons_fresh hi b σ ha]
    congr 1
    exact substSizeList_congr ih
  | nu ha _ ih =>
    simp only [Ty.substSize]
    rw [Size.subst_cons_fresh hi b σ ha]
    congr 1
    exact substSizeList_congr ih
  | allT _ ih => simp only [Ty.substSize]; rw [ih]
  | exT _ ih => simp only [Ty.substSize]; rw [ih]
  | allS ha _ ih => simp only [Ty.substSize]; rw [Size.subst_cons_fresh hi b σ ha, ih]
  | exS ha _ ih => simp only [Ty.substSize]; rw [Size.subst_cons_fresh hi b σ ha, ih]

theorem TyWf.substFTy_cons_fresh {Ψ : SizeCtx} {Θ : List Nat} {k m : Nat} {A : Ty}
    (hA : TyWf Ψ Θ k m A) {X : Nat} (hX : X ∉ Θ) (T : Ty) (τ : List (Nat × Ty)) :
    A.substFTy ((X, T) :: τ) = A.substFTy τ := by
  induction hA with
  | unit _ _ => rfl
  | prod _ _ ihA ihB => simp only [Ty.substFTy]; rw [ihA, ihB]
  | arr _ _ ihA ihB => simp only [Ty.substFTy]; rw [ihA, ihB]
  | var _ => rfl
  | @fvar k m Y hY =>
    have hne : Y ≠ X := fun h => hX (h ▸ hY)
    simp only [Ty.substFTy, List.lookup_cons]
    have : (Y == X) = false := beq_eq_false_iff_ne.mpr hne
    simp [this]
  | lam _ ih => simp only [Ty.substFTy]; rw [ih]
  | app _ _ ihF ihG => simp only [Ty.substFTy]; rw [ihF, ihG]
  | mu _ _ ih =>
    simp only [Ty.substFTy]
    congr 1
    exact substFTyList_congr ih
  | nu _ _ ih =>
    simp only [Ty.substFTy]
    congr 1
    exact substFTyList_congr ih
  | allT _ ih => simp only [Ty.substFTy]; rw [ih]
  | exT _ ih => simp only [Ty.substFTy]; rw [ih]
  | allS _ _ ih => simp only [Ty.substFTy]; rw [ih]
  | exS _ _ ih => simp only [Ty.substFTy]; rw [ih]

end NishtAbel2024V5

/-! ## Solutions/V5/KindWf.lean -/

/-! # V5: syntactic lemmas about kinding -/

namespace NishtAbel2024V5

/-! ## Contexts -/

@[simp] theorem KCtx.dom_inv (π : Pol) (Δ : KCtx) : (Δ.inv π).dom = Δ.dom := by
  simp [KCtx.inv, KCtx.dom]

@[simp] theorem BCtx.length_inv (π : Pol) (Δb : BCtx) : (Δb.inv π).length = Δb.length := by
  simp [BCtx.inv]

@[simp] theorem BCtx.inv_append (π : Pol) (Δb Δb' : BCtx) :
    (Δb ++ Δb').inv π = Δb.inv π ++ Δb'.inv π := by
  simp [BCtx.inv]

@[simp] theorem BCtx.inv_cons (π : Pol) (e : Pol × Kind) (Δb : BCtx) :
    BCtx.inv π (e :: Δb) = (Pol.inv π e.1, e.2) :: Δb.inv π := rfl

@[simp] theorem BCtx.inv_nil (π : Pol) : BCtx.inv π [] = [] := rfl

@[simp] theorem KCtx.inv_append (π : Pol) (Δ Δ' : KCtx) : (Δ ++ Δ').inv π = Δ.inv π ++ Δ'.inv π := by
  simp [KCtx.inv]

theorem KCtx.lookup_some_dom {Δ : KCtx} {X : Nat} {e : Pol × Kind} (h : Δ.lookup X = some e) :
    X ∈ Δ.dom := by
  induction Δ with
  | nil => simp [List.lookup] at h
  | cons p Δ ih =>
    obtain ⟨Y, e'⟩ := p
    by_cases hXY : X = Y
    · subst hXY; simp [KCtx.dom]
    · have hb : (X == Y) = false := by simpa using hXY
      simp only [List.lookup, hb] at h
      simp only [KCtx.dom, List.map_cons, List.mem_cons]
      exact Or.inr (ih h)

/-- All variables have mixed polarity. -/
def KCtx.AllMix (Δ : KCtx) : Prop := ∀ e ∈ Δ, e.2.1 = .mix

theorem KCtx.AllMix.inv {Δ : KCtx} (h : Δ.AllMix) (π : Pol) : Δ.inv π = Δ := by
  unfold KCtx.inv
  conv_rhs => rw [← List.map_id Δ]
  apply List.map_congr_left
  intro e he
  obtain ⟨X, π', κ⟩ := e
  have : π' = .mix := h _ he
  subst this
  cases π <;> rfl

theorem TyCtx.toK_allMix (Θ : TyCtx) : Θ.toK.AllMix := by
  intro e he
  simp only [TyCtx.toK, List.mem_map] at he
  obtain ⟨_, _, rfl⟩ := he
  rfl

@[simp] theorem TyCtx.toK_append (Θ Θ' : TyCtx) : (Θ ++ Θ').toK = Θ.toK ++ Θ'.toK := by
  simp [TyCtx.toK]

@[simp] theorem TyCtx.toK_dom (Θ : TyCtx) : Θ.toK.dom = Θ.map Prod.fst := by
  simp [TyCtx.toK, KCtx.dom]

theorem TyCtx.toK_lookup (Θ : TyCtx) (X : Nat) :
    Θ.toK.lookup X = (Θ.lookup X).map fun κ => (Pol.mix, κ) := by
  induction Θ with
  | nil => rfl
  | cons p Θ ih =>
    obtain ⟨Y, κ⟩ := p
    by_cases h : X = Y
    · subst h; simp [TyCtx.toK, List.lookup]
    · have hb : (X == Y) = false := by simpa using h
      simp only [TyCtx.toK, List.map_cons, List.lookup, hb] at ih ⊢
      exact ih

/-! ## Subkinding -/

theorem SubKind.trans : ∀ {κ₁ κ₂ κ₃ : Kind}, SubKind κ₁ κ₂ → SubKind κ₂ κ₃ → SubKind κ₁ κ₃
  | _, .star, _, h₁, h₂ => by cases h₁; cases h₂; exact .star
  | _, .arr _ _ _, _, h₁, h₂ => by
    cases h₁ with
    | arr hπ ha hb =>
      cases h₂ with
      | arr hπ' ha' hb' => exact .arr (Pol.le_trans hπ' hπ) (SubKind.trans ha' ha) (SubKind.trans hb hb')

theorem SubKind.star_left {κ : Kind} (h : SubKind .star κ) : κ = .star := by
  cases h; rfl

theorem SubKind.star_right {κ : Kind} (h : SubKind κ .star) : κ = .star := by
  cases h; rfl

/-! ## Kinding implies scoping -/

theorem Kinding.tyWf {Ψ : SizeCtx} {Δ : KCtx} {Δb : BCtx} {m : Nat} {A : Ty} {κ : Kind}
    (h : Kinding Ψ Δ Δb m A κ) : TyWf Ψ Δ.dom Δb.length m A := by
  induction h with
  | unit => exact .unit _ _
  | prod _ _ ihA ihB => exact .prod ihA ihB
  | arr _ _ ihA ihB =>
    simp only [KCtx.dom_inv, BCtx.length_inv] at ihA
    exact .arr ihA ihB
  | var hk _ => exact .var (List.getElem?_eq_some_iff.mp hk).1
  | fvar hX _ => exact .fvar (KCtx.lookup_some_dom hX)
  | lam _ _ ih => exact .lam (by simpa using ih)
  | app _ _ _ ihF ihG =>
    simp only [KCtx.dom_inv, BCtx.length_inv] at ihG
    exact .app ihF ihG
  | mu _ ha _ ih =>
    refine .mu ha fun T hT => ?_
    have := ih T hT
    simpa using this
  | nu _ ha _ ih =>
    refine .nu ha fun T hT => ?_
    have := ih T hT
    simpa using this
  | allT _ ih => exact .allT (by simpa using ih)
  | exT _ ih => exact .exT (by simpa using ih)
  | allS ha _ ih => exact .allS ha ih
  | exS ha _ ih => exact .exS ha ih
  | sub _ _ ih => exact ih

theorem KindingC.tyWf {Ψ : SizeCtx} {Δ : KCtx} {A : Ty} {κ : Kind} (h : KindingC Ψ Δ A κ) :
    TyWf Ψ Δ.dom 0 0 A :=
  Kinding.tyWf h

/-! ## Inversion -/

theorem Kinding.inv_mu {Ψ : SizeCtx} {Δ : KCtx} {Δb : BCtx} {m : Nat} {a : Size} {S : List Ty}
    {κ : Kind} (h : Kinding Ψ Δ Δb m (.mu a S) κ) :
    κ = .star ∧ ∃ π, (π = .pos ∨ π = .mix) ∧ SizeWfAt Ψ m a ∧
      ∀ T ∈ S, Kinding Ψ (Δ.inv π) ((π, .star) :: Δb.inv π) m T .star := by
  generalize hA : Ty.mu a S = A at h
  induction h with
  | mu hπ ha hS => cases hA; exact ⟨rfl, _, hπ, ha, hS⟩
  | sub _ hsub ih =>
    obtain ⟨rfl, rest⟩ := ih hA
    exact ⟨hsub.star_left, rest⟩
  | _ => cases hA

theorem Kinding.inv_nu {Ψ : SizeCtx} {Δ : KCtx} {Δb : BCtx} {m : Nat} {a : Size} {R : List Ty}
    {κ : Kind} (h : Kinding Ψ Δ Δb m (.nu a R) κ) :
    κ = .star ∧ ∃ π, (π = .pos ∨ π = .mix) ∧ SizeWfAt Ψ m a ∧
      ∀ T ∈ R, Kinding Ψ (Δ.inv π) ((π, .star) :: Δb.inv π) m T .star := by
  generalize hA : Ty.nu a R = A at h
  induction h with
  | nu hπ ha hR => cases hA; exact ⟨rfl, _, hπ, ha, hR⟩
  | sub _ hsub ih =>
    obtain ⟨rfl, rest⟩ := ih hA
    exact ⟨hsub.star_left, rest⟩
  | _ => cases hA

theorem Kinding.inv_allT {Ψ : SizeCtx} {Δ : KCtx} {Δb : BCtx} {m : Nat} {κ₀ : Kind} {B : Ty}
    {κ : Kind} (h : Kinding Ψ Δ Δb m (.allT κ₀ B) κ) :
    κ = .star ∧ Kinding Ψ Δ ((.mix, κ₀) :: Δb) m B .star := by
  generalize hA : Ty.allT κ₀ B = A at h
  induction h with
  | allT hB => cases hA; exact ⟨rfl, hB⟩
  | sub _ hsub ih =>
    obtain ⟨rfl, rest⟩ := ih hA
    exact ⟨hsub.star_left, rest⟩
  | _ => cases hA

theorem Kinding.inv_exT {Ψ : SizeCtx} {Δ : KCtx} {Δb : BCtx} {m : Nat} {κ₀ : Kind} {B : Ty}
    {κ : Kind} (h : Kinding Ψ Δ Δb m (.exT κ₀ B) κ) :
    κ = .star ∧ Kinding Ψ Δ ((.mix, κ₀) :: Δb) m B .star := by
  generalize hA : Ty.exT κ₀ B = A at h
  induction h with
  | exT hB => cases hA; exact ⟨rfl, hB⟩
  | sub _ hsub ih =>
    obtain ⟨rfl, rest⟩ := ih hA
    exact ⟨hsub.star_left, rest⟩
  | _ => cases hA

theorem Kinding.inv_allS {Ψ : SizeCtx} {Δ : KCtx} {Δb : BCtx} {m : Nat} {a : Size} {B : Ty}
    {κ : Kind} (h : Kinding Ψ Δ Δb m (.allS a B) κ) :
    κ = .star ∧ SizeWfAt Ψ m a ∧ Kinding Ψ Δ Δb (m + 1) B .star := by
  generalize hA : Ty.allS a B = A at h
  induction h with
  | allS ha hB => cases hA; exact ⟨rfl, ha, hB⟩
  | sub _ hsub ih =>
    obtain ⟨rfl, rest⟩ := ih hA
    exact ⟨hsub.star_left, rest⟩
  | _ => cases hA

theorem Kinding.inv_exS {Ψ : SizeCtx} {Δ : KCtx} {Δb : BCtx} {m : Nat} {a : Size} {B : Ty}
    {κ : Kind} (h : Kinding Ψ Δ Δb m (.exS a B) κ) :
    κ = .star ∧ SizeWfAt Ψ m a ∧ Kinding Ψ Δ Δb (m + 1) B .star := by
  generalize hA : Ty.exS a B = A at h
  induction h with
  | exS ha hB => cases hA; exact ⟨rfl, ha, hB⟩
  | sub _ hsub ih =>
    obtain ⟨rfl, rest⟩ := ih hA
    exact ⟨hsub.star_left, rest⟩
  | _ => cases hA

theorem Kinding.inv_prod {Ψ : SizeCtx} {Δ : KCtx} {Δb : BCtx} {m : Nat} {A B : Ty} {κ : Kind}
    (h : Kinding Ψ Δ Δb m (.prod A B) κ) :
    κ = .star ∧ Kinding Ψ Δ Δb m A .star ∧ Kinding Ψ Δ Δb m B .star := by
  generalize hT : Ty.prod A B = T at h
  induction h with
  | prod hA hB => cases hT; exact ⟨rfl, hA, hB⟩
  | sub _ hsub ih =>
    obtain ⟨rfl, rest⟩ := ih hT
    exact ⟨hsub.star_left, rest⟩
  | _ => cases hT

theorem Kinding.inv_arr {Ψ : SizeCtx} {Δ : KCtx} {Δb : BCtx} {m : Nat} {A B : Ty} {κ : Kind}
    (h : Kinding Ψ Δ Δb m (.arr A B) κ) :
    κ = .star ∧ Kinding Ψ (Δ.inv .neg) (Δb.inv .neg) m A .star ∧ Kinding Ψ Δ Δb m B .star := by
  generalize hT : Ty.arr A B = T at h
  induction h with
  | arr hA hB => cases hT; exact ⟨rfl, hA, hB⟩
  | sub _ hsub ih =>
    obtain ⟨rfl, rest⟩ := ih hT
    exact ⟨hsub.star_left, rest⟩
  | _ => cases hT

theorem Kinding.inv_lam {Ψ : SizeCtx} {Δ : KCtx} {Δb : BCtx} {m : Nat} {ι : SKind} {F : Ty}
    {κ : Kind} (h : Kinding Ψ Δ Δb m (.lam ι F) κ) :
    ∃ π κ₁ κ₂, κ₁.erase = ι ∧ Kinding Ψ Δ ((π, κ₁) :: Δb) m F κ₂ ∧
      SubKind (.arr π κ₁ κ₂) κ := by
  generalize hT : Ty.lam ι F = T at h
  induction h with
  | lam hι hF => cases hT; exact ⟨_, _, _, hι, hF, SubKind.refl _⟩
  | sub _ hsub ih =>
    obtain ⟨π, κ₁, κ₂, hι, hF, hs⟩ := ih hT
    exact ⟨π, κ₁, κ₂, hι, hF, hs.trans hsub⟩
  | _ => cases hT

theorem Kinding.inv_app {Ψ : SizeCtx} {Δ : KCtx} {Δb : BCtx} {m : Nat} {F G : Ty} {ι : SKind}
    {κ : Kind} (h : Kinding Ψ Δ Δb m (.app F G ι) κ) :
    ∃ π κ₁ κ₂, Kinding Ψ Δ Δb m F (.arr π κ₁ κ₂) ∧ Kinding Ψ (Δ.inv π) (Δb.inv π) m G κ₁ ∧
      κ₁.erase = ι ∧ SubKind κ₂ κ := by
  generalize hT : Ty.app F G ι = T at h
  induction h with
  | app hF hG hι => cases hT; exact ⟨_, _, _, hF, hG, hι, SubKind.refl _⟩
  | sub _ hsub ih =>
    obtain ⟨π, κ₁, κ₂, hF, hG, hι, hs⟩ := ih hT
    exact ⟨π, κ₁, κ₂, hF, hG, hι, hs.trans hsub⟩
  | _ => cases hT

theorem Kinding.inv_fvar {Ψ : SizeCtx} {Δ : KCtx} {Δb : BCtx} {m X : Nat} {κ : Kind}
    (h : Kinding Ψ Δ Δb m (.fvar X) κ) :
    ∃ π κ', Δ.lookup X = some (π, κ') ∧ π.Usable ∧ SubKind κ' κ := by
  generalize hT : Ty.fvar X = T at h
  induction h with
  | fvar hX hπ => cases hT; exact ⟨_, _, hX, hπ, SubKind.refl _⟩
  | sub _ hsub ih =>
    obtain ⟨π, κ', hX, hπ, hs⟩ := ih hT
    exact ⟨π, κ', hX, hπ, hs.trans hsub⟩
  | _ => cases hT

/-! ## Weakening -/

theorem Kinding.weaken {Ψ : SizeCtx} {Δ : KCtx} {Δb : BCtx} {m : Nat} {A : Ty} {κ : Kind}
    (h : Kinding Ψ Δ Δb m A κ) :
    ∀ {Ψ' : SizeCtx} {Δ' : KCtx} {Δb' : BCtx} {m' : Nat}, (∀ i ∈ Ψ.dom, i ∈ Ψ'.dom) →
      (∀ (X : Nat) (e : Pol × Kind), Δ.lookup X = some e → Δ'.lookup X = some e) →
      (∀ (k : Nat) (e : Pol × Kind), Δb[k]? = some e → Δb'[k]? = some e) → m ≤ m' →
      Kinding Ψ' Δ' Δb' m' A κ := by
  have invΔ : ∀ (π : Pol) {Δ Δ' : KCtx},
      (∀ (X : Nat) (e : Pol × Kind), Δ.lookup X = some e → Δ'.lookup X = some e) →
      ∀ (X : Nat) (e : Pol × Kind), (Δ.inv π).lookup X = some e → (Δ'.inv π).lookup X = some e := by
    intro π Δ Δ' hΔ X e hX
    rw [KCtx.lookup_inv] at hX ⊢
    obtain ⟨e', hX', rfl⟩ := Option.map_eq_some_iff.mp hX
    rw [hΔ X e' hX']
    rfl
  have invΔb : ∀ (π : Pol) {Δb Δb' : BCtx},
      (∀ (k : Nat) (e : Pol × Kind), Δb[k]? = some e → Δb'[k]? = some e) →
      ∀ (k : Nat) (e : Pol × Kind), (Δb.inv π)[k]? = some e → (Δb'.inv π)[k]? = some e := by
    intro π Δb Δb' hΔb k e hk
    rw [BCtx.getElem?_inv] at hk ⊢
    obtain ⟨e', hk', rfl⟩ := Option.map_eq_some_iff.mp hk
    rw [hΔb k e' hk']
    rfl
  have consΔb : ∀ (e₀ : Pol × Kind) {Δb Δb' : BCtx},
      (∀ (k : Nat) (e : Pol × Kind), Δb[k]? = some e → Δb'[k]? = some e) →
      ∀ (k : Nat) (e : Pol × Kind), (e₀ :: Δb)[k]? = some e → (e₀ :: Δb')[k]? = some e := by
    intro e₀ Δb Δb' hΔb k e hk
    cases k with
    | zero => simpa using hk
    | succ k => simpa using hΔb k e (by simpa using hk)
  induction h with
  | unit => intros; exact .unit
  | prod _ _ ihA ihB =>
    intro Ψ' Δ' Δb' m' hΨ hΔ hΔb hm
    exact .prod (ihA hΨ hΔ hΔb hm) (ihB hΨ hΔ hΔb hm)
  | arr _ _ ihA ihB =>
    intro Ψ' Δ' Δb' m' hΨ hΔ hΔb hm
    exact .arr (ihA hΨ (invΔ _ hΔ) (invΔb _ hΔb) hm) (ihB hΨ hΔ hΔb hm)
  | var hk hπ =>
    intro Ψ' Δ' Δb' m' _ _ hΔb _
    exact .var (hΔb _ _ hk) hπ
  | fvar hX hπ =>
    intro Ψ' Δ' Δb' m' _ hΔ _ _
    exact .fvar (hΔ _ _ hX) hπ
  | lam hι _ ih =>
    intro Ψ' Δ' Δb' m' hΨ hΔ hΔb hm
    exact .lam hι (ih hΨ hΔ (consΔb _ hΔb) hm)
  | app _ _ hι ihF ihG =>
    intro Ψ' Δ' Δb' m' hΨ hΔ hΔb hm
    exact .app (ihF hΨ hΔ hΔb hm) (ihG hΨ (invΔ _ hΔ) (invΔb _ hΔb) hm) hι
  | mu hπ ha _ ih =>
    intro Ψ' Δ' Δb' m' hΨ hΔ hΔb hm
    exact .mu hπ (ha.weaken hΨ hm)
      (fun T hT => ih T hT hΨ (invΔ _ hΔ) (consΔb _ (invΔb _ hΔb)) hm)
  | nu hπ ha _ ih =>
    intro Ψ' Δ' Δb' m' hΨ hΔ hΔb hm
    exact .nu hπ (ha.weaken hΨ hm)
      (fun T hT => ih T hT hΨ (invΔ _ hΔ) (consΔb _ (invΔb _ hΔb)) hm)
  | allT _ ih =>
    intro Ψ' Δ' Δb' m' hΨ hΔ hΔb hm
    exact .allT (ih hΨ hΔ (consΔb _ hΔb) hm)
  | exT _ ih =>
    intro Ψ' Δ' Δb' m' hΨ hΔ hΔb hm
    exact .exT (ih hΨ hΔ (consΔb _ hΔb) hm)
  | allS ha _ ih =>
    intro Ψ' Δ' Δb' m' hΨ hΔ hΔb hm
    exact .allS (ha.weaken hΨ hm) (ih hΨ hΔ hΔb (by omega))
  | exS ha _ ih =>
    intro Ψ' Δ' Δb' m' hΨ hΔ hΔb hm
    exact .exS (ha.weaken hΨ hm) (ih hΨ hΔ hΔb (by omega))
  | sub _ hs ih =>
    intro Ψ' Δ' Δb' m' hΨ hΔ hΔb hm
    exact .sub (ih hΨ hΔ hΔb hm) hs

/-- A locally closed type is kinded under any bound contexts. -/
theorem KindingC.weakenB {Ψ : SizeCtx} {Δ : KCtx} {T : Ty} {κ : Kind} (h : KindingC Ψ Δ T κ)
    (Δb : BCtx) (m : Nat) : Kinding Ψ Δ Δb m T κ :=
  Kinding.weaken h (fun _ h => h) (fun _ _ h => h) (fun _ _ h => by simp at h) (Nat.zero_le _)

/-- Extending the contexts by fresh variables. -/
theorem KindingC.mono {Ψ Ψ' : SizeCtx} {Δ Δ' : KCtx} {T : Ty} {κ : Kind} (h : KindingC Ψ Δ T κ)
    (hΨ : ∀ i ∈ Ψ.dom, i ∈ Ψ'.dom)
    (hΔ : ∀ (X : Nat) (e : Pol × Kind), Δ.lookup X = some e → Δ'.lookup X = some e) :
    KindingC Ψ' Δ' T κ :=
  Kinding.weaken h hΨ hΔ (fun _ _ h => h) le_rfl

theorem lookup_append_left {Δ Δ' : KCtx} {X : Nat} {e : Pol × Kind} (h : Δ.lookup X = some e) :
    (Δ ++ Δ').lookup X = some e := by
  induction Δ with
  | nil => simp [List.lookup] at h
  | cons p Δ ih =>
    obtain ⟨Y, e'⟩ := p
    by_cases hXY : X = Y
    · subst hXY; simpa [List.lookup] using h
    · have hb : (X == Y) = false := by simpa using hXY
      simp only [List.lookup, hb, List.cons_append] at h ⊢
      exact ih h

/-! ## Substitution of the outermost bound type variable -/

theorem Kinding.substTy_last {Ψ : SizeCtx} {Δ : KCtx} {Δb' : BCtx} {m : Nat} {A : Ty}
    {κA : Kind} (h : Kinding Ψ Δ Δb' m A κA) :
    ∀ {Δb : BCtx} {π : Pol} {κ : Kind} {T : Ty}, Δb' = Δb ++ [(π, κ)] → Δ.AllMix →
      KindingC Ψ Δ T κ → Kinding Ψ Δ Δb m (A.substTy Δb.length T) κA := by
  induction h with
  | unit => intros; exact .unit
  | prod _ _ ihA ihB =>
    intro Δb π κ T he hΔ hT
    exact .prod (ihA he hΔ hT) (ihB he hΔ hT)
  | @arr Δ Δb₀ m A B _ _ ihA ihB =>
    intro Δb π κ T he hΔ hT
    have hA := @ihA (Δb.inv .neg) (Pol.inv .neg π) κ T (by rw [he]; simp)
      (by rw [hΔ.inv]; exact hΔ) (by rw [hΔ.inv]; exact hT)
    rw [BCtx.length_inv] at hA
    exact .arr hA (ihB he hΔ hT)
  | @var Δ Δb₀ m k π' κ' hk hπ' =>
    intro Δb π κ T he hΔ hT
    subst he
    simp only [Ty.substTy]
    by_cases h1 : k = Δb.length
    · subst h1
      simp only [if_true]
      simp at hk
      obtain ⟨rfl, rfl⟩ := hk
      exact hT.weakenB _ m
    · have hlt : k < Δb.length := by
        have := (List.getElem?_eq_some_iff.mp hk).1
        simp at this; omega
      have h2 : ¬ Δb.length < k := by omega
      simp only [h1, h2, if_false]
      refine .var ?_ hπ'
      rw [List.getElem?_append_left hlt] at hk
      exact hk
  | fvar hX hπ => intros; exact .fvar hX hπ
  | @lam Δ Δb₀ m ι F π' κ₁ κ₂ hι _ ih =>
    intro Δb π κ T he hΔ hT
    have := @ih ((π', κ₁) :: Δb) π κ T (by rw [he]; rfl) hΔ hT
    exact .lam hι (by simpa using this)
  | @app Δ Δb₀ m F G ι π' κ₁ κ₂ _ _ hι ihF ihG =>
    intro Δb π κ T he hΔ hT
    have hG := @ihG (Δb.inv π') (Pol.inv π' π) κ T (by rw [he]; simp)
      (by rw [hΔ.inv]; exact hΔ) (by rw [hΔ.inv]; exact hT)
    rw [BCtx.length_inv] at hG
    exact .app (ihF he hΔ hT) hG hι
  | @mu Δ Δb₀ m a S π' hπ' ha _ ih =>
    intro Δb π κ T he hΔ hT
    simp only [Ty.substTy]
    refine .mu hπ' ha fun T' hT' => ?_
    obtain ⟨B, hB, rfl⟩ := Ty.mem_substTyList hT'
    have := @ih B hB ((π', .star) :: Δb.inv π') (Pol.inv π' π) κ T (by rw [he]; simp)
      (by rw [hΔ.inv]; exact hΔ) (by rw [hΔ.inv]; exact hT)
    simpa using this
  | @nu Δ Δb₀ m a R π' hπ' ha _ ih =>
    intro Δb π κ T he hΔ hT
    simp only [Ty.substTy]
    refine .nu hπ' ha fun T' hT' => ?_
    obtain ⟨B, hB, rfl⟩ := Ty.mem_substTyList hT'
    have := @ih B hB ((π', .star) :: Δb.inv π') (Pol.inv π' π) κ T (by rw [he]; simp)
      (by rw [hΔ.inv]; exact hΔ) (by rw [hΔ.inv]; exact hT)
    simpa using this
  | @allT Δ Δb₀ m κ₀ B _ ih =>
    intro Δb π κ T he hΔ hT
    have := @ih ((.mix, κ₀) :: Δb) π κ T (by rw [he]; rfl) hΔ hT
    exact .allT (by simpa using this)
  | @exT Δ Δb₀ m κ₀ B _ ih =>
    intro Δb π κ T he hΔ hT
    have := @ih ((.mix, κ₀) :: Δb) π κ T (by rw [he]; rfl) hΔ hT
    exact .exT (by simpa using this)
  | allS ha _ ih =>
    intro Δb π κ T he hΔ hT
    exact .allS ha (ih he hΔ hT)
  | exS ha _ ih =>
    intro Δb π κ T he hΔ hT
    exact .exS ha (ih he hΔ hT)
  | sub _ hs ih =>
    intro Δb π κ T he hΔ hT
    exact .sub (ih he hΔ hT) hs

/-- Opening a type binder of a locally closed type. -/
theorem Kinding.open_ty {Ψ : SizeCtx} {Δ : KCtx} {π : Pol} {κ κB : Kind} {B T : Ty}
    (hB : Kinding Ψ Δ [(π, κ)] 0 B κB) (hΔ : Δ.AllMix) (hT : KindingC Ψ Δ T κ) :
    KindingC Ψ Δ (B.substTy 0 T) κB :=
  hB.substTy_last (Δb := []) rfl hΔ hT

/-! ## Opening the outermost bound size variable -/

theorem Kinding.openSz {Ψ : SizeCtx} {Δ : KCtx} {Δb : BCtx} {n : Nat} {A : Ty} {κ : Kind}
    (h : Kinding Ψ Δ Δb n A κ) :
    ∀ (m : Nat) (c : Size), n = m + 1 → SizeWf Ψ c → Kinding Ψ Δ Δb m (A.openSz m c) κ := by
  induction h with
  | unit => intros; exact .unit
  | prod _ _ ihA ihB => intro m c hn hc; exact .prod (ihA m c hn hc) (ihB m c hn hc)
  | arr _ _ ihA ihB => intro m c hn hc; exact .arr (ihA m c hn hc) (ihB m c hn hc)
  | var hk hπ => intros; exact .var hk hπ
  | fvar hX hπ => intros; exact .fvar hX hπ
  | lam hι _ ih => intro m c hn hc; exact .lam hι (ih m c hn hc)
  | app _ _ hι ihF ihG => intro m c hn hc; exact .app (ihF m c hn hc) (ihG m c hn hc) hι
  | mu hπ ha _ ih =>
    intro m c hn hc
    simp only [Ty.openSz]
    refine .mu hπ (SizeWfAt.openAt m hn hc ha) fun T' hT' => ?_
    obtain ⟨B, hB, rfl⟩ := Ty.mem_openSzList hT'
    exact ih B hB m c hn hc
  | nu hπ ha _ ih =>
    intro m c hn hc
    simp only [Ty.openSz]
    refine .nu hπ (SizeWfAt.openAt m hn hc ha) fun T' hT' => ?_
    obtain ⟨B, hB, rfl⟩ := Ty.mem_openSzList hT'
    exact ih B hB m c hn hc
  | allT _ ih => intro m c hn hc; exact .allT (ih m c hn hc)
  | exT _ ih => intro m c hn hc; exact .exT (ih m c hn hc)
  | allS ha _ ih =>
    intro m c hn hc
    exact .allS (SizeWfAt.openAt m hn hc ha) (ih (m + 1) c (by omega) hc)
  | exS ha _ ih =>
    intro m c hn hc
    exact .exS (SizeWfAt.openAt m hn hc ha) (ih (m + 1) c (by omega) hc)
  | sub _ hs ih => intro m c hn hc; exact .sub (ih m c hn hc) hs

theorem Kinding.open_sz {Ψ : SizeCtx} {Δ : KCtx} {B : Ty} {c : Size} {κ : Kind}
    (hB : Kinding Ψ Δ [] 1 B κ) (hc : SizeWf Ψ c) : KindingC Ψ Δ (B.openSz 0 c) κ :=
  hB.openSz 0 c rfl hc

/-! ## Substitution of free size variables -/

theorem SizeWfAt.subst {Ψ Ψ' : SizeCtx} {m : Nat} {σ : List (Nat × Size)}
    (hσ : ∀ i ∈ Ψ.dom, SizeWf Ψ' ((Size.var i 0).subst σ)) :
    ∀ {a : Size}, SizeWfAt Ψ m a → SizeWfAt Ψ' m (a.subst σ)
  | .inf _, _ => trivial
  | .bvar _ _, h => h
  | .var i n, h => by
    have hi := hσ i h
    simp only [Size.subst] at hi ⊢
    cases hl : σ.lookup i with
    | none =>
      simp only [hl] at hi ⊢
      exact hi
    | some b =>
      simp only [hl, Size.shift_zero] at hi ⊢
      exact (SizeWfAt.shift n hi).weaken (fun _ h => h) (Nat.zero_le _)
  | .meet _ _, h => ⟨SizeWfAt.subst hσ h.1, SizeWfAt.subst hσ h.2⟩

theorem Kinding.substSize {Ψ : SizeCtx} {Δ : KCtx} {Δb : BCtx} {m : Nat} {A : Ty} {κ : Kind}
    (h : Kinding Ψ Δ Δb m A κ) {Ψ' : SizeCtx} {σ : List (Nat × Size)}
    (hσ : ∀ i ∈ Ψ.dom, SizeWf Ψ' ((Size.var i 0).subst σ)) :
    Kinding Ψ' Δ Δb m (A.substSize σ) κ := by
  induction h with
  | unit => exact .unit
  | prod _ _ ihA ihB => exact .prod ihA ihB
  | arr _ _ ihA ihB => exact .arr ihA ihB
  | var hk hπ => exact .var hk hπ
  | fvar hX hπ => exact .fvar hX hπ
  | lam hι _ ih => exact .lam hι ih
  | app _ _ hι ihF ihG => exact .app ihF ihG hι
  | mu hπ ha _ ih =>
    simp only [Ty.substSize]
    refine .mu hπ (SizeWfAt.subst hσ ha) fun T' hT' => ?_
    obtain ⟨B, hB, rfl⟩ := Ty.mem_substSizeList hT'
    exact ih B hB
  | nu hπ ha _ ih =>
    simp only [Ty.substSize]
    refine .nu hπ (SizeWfAt.subst hσ ha) fun T' hT' => ?_
    obtain ⟨B, hB, rfl⟩ := Ty.mem_substSizeList hT'
    exact ih B hB
  | allT _ ih => exact .allT ih
  | exT _ ih => exact .exT ih
  | allS ha _ ih => exact .allS (SizeWfAt.subst hσ ha) ih
  | exS ha _ ih => exact .exS (SizeWfAt.subst hσ ha) ih
  | sub _ hs ih => exact .sub ih hs

/-! ## Substitution of free type variables (mixed contexts) -/

theorem Kinding.substFTy {Ψ : SizeCtx} {Δ : KCtx} {Δb : BCtx} {m : Nat} {A : Ty} {κ : Kind}
    (h : Kinding Ψ Δ Δb m A κ) :
    Δ.AllMix → ∀ {Δ' : KCtx} {τ : List (Nat × Ty)}, Δ'.AllMix →
      (∀ X π κ', Δ.lookup X = some (π, κ') →
        (∃ T, τ.lookup X = some T ∧ KindingC Ψ Δ' T κ') ∨
          (τ.lookup X = none ∧ Δ'.lookup X = some (π, κ'))) →
      Kinding Ψ Δ' Δb m (A.substFTy τ) κ := by
  induction h with
  | unit => intros; exact .unit
  | prod _ _ ihA ihB =>
    intro hΔ Δ' τ hΔ' hτ
    exact .prod (ihA hΔ hΔ' hτ) (ihB hΔ hΔ' hτ)
  | @arr Δ Δb m A B _ _ ihA ihB =>
    intro hΔ Δ' τ hΔ' hτ
    have hA := ihA (by rw [hΔ.inv]; exact hΔ) hΔ' (by rw [hΔ.inv]; exact hτ)
    exact .arr (by rw [hΔ'.inv]; exact hA) (ihB hΔ hΔ' hτ)
  | var hk hπ => intros; exact .var hk hπ
  | @fvar Δ Δb m X π κ' hX hπ =>
    intro hΔ Δ' τ hΔ' hτ
    simp only [Ty.substFTy]
    rcases hτ X π κ' hX with ⟨T, hT, hTk⟩ | ⟨hT, hX'⟩
    · rw [hT]; exact hTk.weakenB Δb m
    · rw [hT]; exact .fvar hX' hπ
  | lam hι _ ih =>
    intro hΔ Δ' τ hΔ' hτ
    exact .lam hι (ih hΔ hΔ' hτ)
  | @app Δ Δb m F G ι π κ₁ κ₂ _ _ hι ihF ihG =>
    intro hΔ Δ' τ hΔ' hτ
    have hG := ihG (by rw [hΔ.inv]; exact hΔ) hΔ' (by rw [hΔ.inv]; exact hτ)
    exact .app (ihF hΔ hΔ' hτ) (by rw [hΔ'.inv]; exact hG) hι
  | @mu Δ Δb m a S π hπ ha _ ih =>
    intro hΔ Δ' τ hΔ' hτ
    simp only [Ty.substFTy]
    refine .mu hπ ha fun T' hT' => ?_
    obtain ⟨B, hB, rfl⟩ := Ty.mem_substFTyList hT'
    have := ih B hB (by rw [hΔ.inv]; exact hΔ) hΔ' (by rw [hΔ.inv]; exact hτ)
    rw [hΔ'.inv]
    exact this
  | @nu Δ Δb m a R π hπ ha _ ih =>
    intro hΔ Δ' τ hΔ' hτ
    simp only [Ty.substFTy]
    refine .nu hπ ha fun T' hT' => ?_
    obtain ⟨B, hB, rfl⟩ := Ty.mem_substFTyList hT'
    have := ih B hB (by rw [hΔ.inv]; exact hΔ) hΔ' (by rw [hΔ.inv]; exact hτ)
    rw [hΔ'.inv]
    exact this
  | allT _ ih => intro hΔ Δ' τ hΔ' hτ; exact .allT (ih hΔ hΔ' hτ)
  | exT _ ih => intro hΔ Δ' τ hΔ' hτ; exact .exT (ih hΔ hΔ' hτ)
  | allS ha _ ih => intro hΔ Δ' τ hΔ' hτ; exact .allS ha (ih hΔ hΔ' hτ)
  | exS ha _ ih => intro hΔ Δ' τ hΔ' hτ; exact .exS ha (ih hΔ hΔ' hτ)
  | sub _ hs ih => intro hΔ Δ' τ hΔ' hτ; exact .sub (ih hΔ hΔ' hτ) hs

end NishtAbel2024V5


