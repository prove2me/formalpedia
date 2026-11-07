-- Prove2me | Definitions.Def_NishtAbel2024V5_SemFundamental
-- name    : NishtAbel2024V5_SemFundamental
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-07T04:28:25.816889+00:00
-- url     : https://prove2.me/theorems/0a1019e7-f577-4f03-86d2-fa1b3c823697
-- title:
--   Chapter 5.4–5.5 (V5 Support): Fundamental Theorem of Reducibility (Theorem 3), Strong Normalization (Theorems 4–5), and Lexicographic Embedding (Theorem 6)
-- statement:
--   Completes the semantic metatheory of Chapter 5 of Nisht and Abel (2024): proves the Fundamental Theorem of Reducibility for expressions and clauses (`fundamental`, Theorem 3), combines it with well-founded induction along the Ramsey-backed SCT call relation (`ramseyPairs`) to prove soundness of mutual blocks (`theorem_4_core`, Theorem 4), global signatures (`blocks_valid`, Lemma 2), and complete programs (`theorem_5_core`, Theorem 5), and constructs the SCT invocation graph embedding for lexicographic measures (`theorem_6_proof`, Theorem 6).
-- source:
--   Nisht & Abel 2024, Kind Inference and Termination Checking in a Language with Co-Patterns and Size-Change Termination, https://urn.kb.se/resolve?urn=urn:nbn:se:chalmers:diva-542843, Chapter 5, Sections 5.4-5.5, pp. 36-40, Theorems 3-6 & Lemma 2

import Definitions.Def_NishtAbel2024V5_SemSubSpine
import Definitions.Def_NishtAbel2024V5_SCT

/-! ## Solutions/V5/FundAux.lean -/

/-! # V5: auxiliary lemmas for the fundamental lemma -/

namespace NishtAbel2024V5

open NishtAbel2024V2 (InvGraph ConformsToGraph)

theorem step_pair_inv {W : World} {t u v : Tm} (h : Step W (.pair t u) v) :
    (∃ t', Step W t t' ∧ v = .pair t' u) ∨ (∃ u', Step W u u' ∧ v = .pair t u') := by
  cases h with
  | head hh => rw [headStep_intro (by simp [IsIntro])] at hh; cases hh
  | pairL h => exact Or.inl ⟨_, h, rfl⟩
  | pairR h => exact Or.inr ⟨_, h, rfl⟩

theorem step_cons_inv {W : World} {c : Nat} {t v : Tm} (h : Step W (.cons c t) v) :
    ∃ t', Step W t t' ∧ v = .cons c t' := by
  cases h with
  | head hh => rw [headStep_intro (by simp [IsIntro])] at hh; cases hh
  | cons h => exact ⟨_, h, rfl⟩

theorem step_unit_inv {W : World} {v : Tm} (h : Step W .unit v) : False := by
  cases h with
  | head hh => rw [headStep_intro (by simp [IsIntro])] at hh; cases hh

theorem steps_pair_inv {W : World} {t u v : Tm} (h : Steps W (.pair t u) v) :
    ∃ t' u', v = .pair t' u' ∧ Steps W t t' ∧ Steps W u u' := by
  induction h with
  | refl => exact ⟨t, u, rfl, .refl, .refl⟩
  | tail _ hs ih =>
    obtain ⟨t', u', rfl, ht, hu⟩ := ih
    rcases step_pair_inv hs with ⟨t'', h, rfl⟩ | ⟨u'', h, rfl⟩
    · exact ⟨t'', u', rfl, ht.tail h, hu⟩
    · exact ⟨t', u'', rfl, ht, hu.tail h⟩

theorem steps_cons_inv {W : World} {c : Nat} {t v : Tm} (h : Steps W (.cons c t) v) :
    ∃ t', v = .cons c t' ∧ Steps W t t' := by
  induction h with
  | refl => exact ⟨t, rfl, .refl⟩
  | tail _ hs ih =>
    obtain ⟨t', rfl, ht⟩ := ih
    obtain ⟨t'', h, rfl⟩ := step_cons_inv hs
    exact ⟨t'', rfl, ht.tail h⟩

theorem steps_unit_inv {W : World} {v : Tm} (h : Steps W .unit v) : v = .unit := by
  induction h with
  | refl => rfl
  | tail _ hs ih => rw [ih] at hs; exact (step_unit_inv hs).elim

theorem SN.pair {W : World} {t u : Tm} (ht : SN W t) (hu : SN W u) : SN W (.pair t u) := by
  induction ht generalizing u with
  | intro t _ iht =>
    induction hu with
    | intro u hu' ihu =>
      refine SN.of_reducts fun v hv => ?_
      rcases step_pair_inv hv with ⟨t', h, rfl⟩ | ⟨u', h, rfl⟩
      · exact iht t' h (Acc.intro u hu')
      · exact ihu u' h

theorem SN.cons {W : World} {c : Nat} {t : Tm} (ht : SN W t) : SN W (.cons c t) := by
  induction ht with
  | intro t _ ih =>
    refine SN.of_reducts fun v hv => ?_
    obtain ⟨t', h, rfl⟩ := step_cons_inv hv
    exact ih t' h

theorem SN.unit (W : World) : SN W .unit := SN.of_reducts fun _ h => (step_unit_inv h).elim

theorem step_pack_inv {W : World} {t v : Tm} (h : Step W (.pack t) v) :
    ∃ t', Step W t t' ∧ v = .pack t' := by
  cases h with
  | head hh => rw [headStep_intro (by simp [IsIntro])] at hh; cases hh
  | pack h => exact ⟨_, h, rfl⟩

theorem steps_pack_inv {W : World} {t v : Tm} (h : Steps W (.pack t) v) :
    ∃ t', v = .pack t' ∧ Steps W t t' := by
  induction h with
  | refl => exact ⟨t, rfl, .refl⟩
  | tail _ hs ih =>
    obtain ⟨t', rfl, ht⟩ := ih
    obtain ⟨t'', h, rfl⟩ := step_pack_inv hs
    exact ⟨t'', rfl, ht.tail h⟩

theorem SN.pack {W : World} {t : Tm} (ht : SN W t) : SN W (.pack t) := by
  induction ht with
  | intro t _ ih =>
    refine SN.of_reducts fun v hv => ?_
    obtain ⟨t', h, rfl⟩ := step_pack_inv hv
    exact ih t' h

theorem conforms_map {S T : Type} {lt₁ le₁ : S → S → Prop} {lt₂ le₂ : T → T → Prop}
    {G : InvGraph} {xs ys : List S} (f : S → T)
    (hlt : ∀ x y, lt₁ x y → lt₂ (f x) (f y)) (hle : ∀ x y, le₁ x y → le₂ (f x) (f y))
    (h : ConformsToGraph lt₁ le₁ G xs ys) : ConformsToGraph lt₂ le₂ G (xs.map f) (ys.map f) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by simpa using h1, by simpa using h2, ?_⟩
  intro i j hi hj
  have hi' : i < xs.length := by simpa using hi
  have hj' : j < ys.length := by simpa using hj
  obtain ⟨a, b⟩ := h3 i j hi' hj'
  exact ⟨fun e => by simpa using hlt _ _ (a e), fun e => by simpa using hle _ _ (b e)⟩

theorem selectClause_inv {D : List Clause} {es : List Elim} {u : Tm} (h : selectClause D es = some u) :
    ∃ qs t σm, Clause.mk qs t ∈ D ∧ matchSpine qs es = .yes σm ∧
      u = Tm.appSpine (t.subst σm) (es.drop qs.length) := by
  induction D with
  | nil => simp [selectClause] at h
  | cons cl D ih =>
    obtain ⟨qs, t⟩ := cl
    simp only [selectClause] at h
    cases hm : matchSpine qs es with
    | yes σ =>
      rw [hm] at h; simp at h
      exact ⟨qs, t, σ, by simp, hm, h.symm⟩
    | no =>
      rw [hm] at h
      obtain ⟨qs', t', σ', hmem, hm', hu⟩ := ih h
      exact ⟨qs', t', σ', List.mem_cons_of_mem _ hmem, hm', hu⟩
    | stuck => rw [hm] at h; simp at h

theorem mem_substList {σ : TmSubst} {D : List Clause} {qs : List Copat} {t : Tm}
    (h : Clause.mk qs t ∈ Clause.substList σ D) :
    ∃ t₀, Clause.mk qs t₀ ∈ D ∧ t = t₀.subst (σ.filter (fun p => decide (p.1 ∉ spineVars qs))) := by
  induction D with
  | nil => simp [Clause.substList] at h
  | cons cl D ih =>
    obtain ⟨qs', t'⟩ := cl
    simp only [Clause.substList, List.mem_cons] at h
    rcases h with h | h
    · cases h; exact ⟨t', by simp, rfl⟩
    · obtain ⟨t₀, hm, rfl⟩ := ih h; exact ⟨t₀, List.mem_cons_of_mem _ hm, rfl⟩

theorem matchSpine_take {qs : List Copat} {es : List Elim} {σ : TmSubst}
    (h : matchSpine qs es = .yes σ) : matchSpine qs (es.take qs.length) = .yes σ := by
  have hlen := matchSpine_yes_length h
  have := matchSpine_append_of_le qs (es.take qs.length) (es.drop qs.length)
    (by simp [List.length_take]; omega)
  rw [List.take_append_drop] at this
  rw [← this]; exact h

theorem spineTy_dom {Ψ : SizeCtx} {Θ : TyCtx} {qs : List Copat} {A : Ty} {Γ' : TermCtx}
    {Ψ' : SizeCtx} {Θ' : TyCtx} {C : Ty} (h : SpineTy Ψ Θ qs A Γ' Ψ' Θ' C) :
    Γ'.map Prod.fst = spineVars qs := by
  induction h with
  | nil => rfl
  | pat hp _ ih =>
    rw [List.map_append, patTy_dom hp, ih]
    simp [spineVars, Copat.vars]
  | proj _ _ _ ih => simpa [spineVars, Copat.vars] using ih
  | instT _ _ ih => simpa [spineVars, Copat.vars] using ih
  | instS _ _ ih => simpa [spineVars, Copat.vars] using ih

theorem headStep_lam (W : World) (D : List Clause) (es : List Elim) :
    headStep W (Tm.appSpine (.lam D) es) = selectClause D es := by
  unfold headStep
  rw [Tm.headSpine_appSpine]
  simp [Tm.headSpine]

theorem headStep_fn {W : World} {f : NishtAbel2024V2.FunName} {d : FunDecl}
    (h : W.lookup f = some d) (es : List Elim) :
    headStep W (Tm.appSpine (.fn f) es) = selectClause d.clauses es := by
  unfold headStep
  rw [Tm.headSpine_appSpine]
  simp [Tm.headSpine, h]

/-! ## Free variables of typed terms -/

theorem mem_dom_of_lookup {Γ : TermCtx} {x : Nat} {A : Ty} (h : Γ.lookup x = some A) :
    x ∈ Γ.map Prod.fst := by
  by_contra hn
  have := lookup_none_of_not_mem (σ := Γ.map (fun p => (p.1, Tm.unit))) (x := x) (by simpa using hn)
  induction Γ with
  | nil => simp at h
  | cons q Γ ih =>
    obtain ⟨y, B⟩ := q
    rw [List.lookup_cons] at h
    by_cases hxy : x = y
    · exact hn (by simp [hxy])
    · have hb : (x == y) = false := beq_eq_false_iff_ne.mpr hxy
      simp only [hb] at h
      exact ih h (fun h' => hn (List.mem_cons_of_mem _ h')) (by
        simp only [List.map_cons] at this
        rw [lookup_cons_eq] at this
        simpa [hxy] using this)

theorem clauses_fv_of {Γ : TermCtx} : ∀ (D : List Clause),
    (∀ cl ∈ D, ∀ x ∈ Clause.fvList [cl], x ∈ Γ.map Prod.fst) →
      ∀ x ∈ Clause.fvList D, x ∈ Γ.map Prod.fst
  | [], _, x, hx => by simp [Clause.fvList] at hx
  | .mk qs t :: D, ih, x, hx => by
    simp only [Clause.fvList, List.mem_append] at hx
    rcases hx with hx | hx
    · exact ih (.mk qs t) (by simp) x (by simp [Clause.fvList]; simpa using hx)
    · exact clauses_fv_of D (fun cl h => ih cl (List.mem_cons_of_mem _ h)) x hx

theorem exprTy_fv {Ω : TypingEnv} {Ψ : SizeCtx} {Θ : TyCtx} {Γ : TermCtx} {t : Tm} {A : Ty}
    (h : ExprTy Ω Ψ Θ Γ t A) : ∀ x ∈ t.fv, x ∈ Γ.map Prod.fst := by
  refine ExprTy.rec (motive_1 := fun _ _ Γ t _ _ => ∀ x ∈ t.fv, x ∈ Γ.map Prod.fst)
    (motive_2 := fun _ _ Γ cl _ _ => ∀ x ∈ Clause.fvList [cl], x ∈ Γ.map Prod.fst)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  · intro Ψ Θ Γ x A hx y hy
    simp [Tm.fv] at hy; subst hy; exact mem_dom_of_lookup hx
  · intro Ψ Θ Γ y hy; simp [Tm.fv] at hy
  · intro Ψ Θ Γ t u A B _ _ ih₁ ih₂ y hy
    simp only [Tm.fv, List.mem_append] at hy
    rcases hy with hy | hy
    · exact ih₁ y hy
    · exact ih₂ y hy
  · intro Ψ Θ Γ c t a b S Sc _ _ _ _ ih y hy
    exact ih y (by simpa [Tm.fv] using hy)
  · intro Ψ Θ Γ r s A B _ _ ih₁ ih₂ y hy
    simp only [Tm.fv, Elim.fv, List.mem_append] at hy
    rcases hy with hy | hy
    · exact ih₁ y hy
    · exact ih₂ y hy
  · intro Ψ Θ Γ r a b R d Rd _ _ _ ih y hy
    simp only [Tm.fv, Elim.fv, List.append_nil] at hy
    exact ih y hy
  · intro Ψ Θ Γ r κ B T _ _ ih y hy
    simp only [Tm.fv, Elim.fv, List.append_nil] at hy
    exact ih y hy
  · intro Ψ Θ Γ r a b B _ _ ih y hy
    simp only [Tm.fv, Elim.fv, List.append_nil] at hy
    exact ih y hy
  · intro Ψ Θ Γ t κ B T _ _ _ ih y hy
    simp only [Tm.fv] at hy
    exact ih y hy
  · intro Ψ Θ Γ t a b B _ _ _ ih y hy
    simp only [Tm.fv] at hy
    exact ih y hy
  · intro Ψ Θ Γ D A _ _ ih y hy
    simp only [Tm.fv] at hy
    exact clauses_fv_of D ih y hy
  · intro Ψ Θ Γ g as _ _ _ _ _ y hy; simp [Tm.fv] at hy
  · intro Ψ Θ Γ g as _ _ _ _ _ _ y hy; simp [Tm.fv] at hy
  · intro Ψ Θ Γ t A B _ _ _ ih y hy; exact ih y hy
  · intro Ψ Ψ' Θ Θ' Γ Γ' qs t A C hsp _ ih y hy
    simp only [Clause.fvList, List.append_nil, List.mem_filter, decide_eq_true_eq] at hy
    have := ih y hy.1
    simp only [List.map_append, List.mem_append] at this
    rcases this with h' | h'
    · rw [spineTy_dom hsp] at h'; exact absurd h' hy.2
    · exact h'

end NishtAbel2024V5

/-! ## Solutions/V5/Fundamental.lean -/

/-! # V5: the fundamental lemma (Theorem 3) -/

namespace NishtAbel2024V5

open NishtAbel2024V2 (InvGraph ConformsToGraph)

/-! ## Callee valuations -/

theorem SizeCtxWf.nodup {Ψ : SizeCtx} (h : SizeCtxWf Ψ) : Ψ.dom.Nodup := by
  induction h with
  | nil => simp [SizeCtx.dom]
  | @snoc Ψ i a _ hi _ ih =>
    simp only [SizeCtx.dom, List.map_append, List.map_cons, List.map_nil]
    rw [List.nodup_append]
    refine ⟨ih, by simp, ?_⟩
    intro x hx y hy
    simp at hy; subst hy
    exact fun h => hi (h ▸ hx)

theorem SizeCtxWf.bounds {Ψ : SizeCtx} (h : SizeCtxWf Ψ) : CtxBoundsWf Ψ := by
  induction h with
  | nil => intro p hp; simp at hp
  | snoc _ _ ha ih => exact ih.extend ha

theorem lookup_zip_getElem : ∀ (l : List Nat) (as : List Size), l.Nodup → l.length = as.length →
    ∀ k (hk : k < l.length) (ha : k < as.length), (l.zip as).lookup (l[k]'hk) = some (as[k]'ha)
  | [], _, _, _, k, hk, _ => by simp at hk
  | _ :: _, [], _, h, _, _, _ => by simp at h
  | x :: l, a :: as, hnd, hlen, 0, _, _ => by simp
  | x :: l, a :: as, hnd, hlen, k + 1, hk, ha => by
    have hk' : k < l.length := by simp at hk; omega
    have ha' : k < as.length := by simp at ha; omega
    have hne : l[k]'hk' ≠ x := by
      intro h
      have := (List.nodup_cons.mp hnd).1
      exact this (h ▸ List.getElem_mem hk')
    have hb : (l[k]'hk' == x) = false := beq_eq_false_iff_ne.mpr hne
    have := lookup_zip_getElem l as (List.nodup_cons.mp hnd).2 (by simpa using hlen) k hk' ha'
    simp only [List.zip_cons_cons, List.getElem_cons_succ, List.lookup_cons, hb]
    exact this

theorem lookup_mem_size {L : List (Nat × Size)} {i : Nat} {b : Size} (h : L.lookup i = some b) :
    (i, b) ∈ L := by
  induction L with
  | nil => simp at h
  | cons q r ih =>
    obtain ⟨y, c⟩ := q
    rw [lookup_size_cons] at h
    by_cases hiy : i = y
    · simp [hiy] at h; subst h; subst hiy; simp
    · simp [hiy] at h; exact List.mem_cons_of_mem _ (ih h)

theorem lookup_zip_mem {l : List Nat} {as : List Size} {i : Nat} {b : Size}
    (h : (l.zip as).lookup i = some b) : b ∈ as :=
  (List.of_mem_zip (lookup_mem_size h)).2

/-- Size arguments of a well-formed call give a valid callee valuation. -/
theorem callee_val {Ψ : SizeCtx} {ρ : SizeVal} (hv : ValidVal Ψ ρ) {as : List Size}
    {Ψg : SizeCtx} (hwf : SizeCtxWf Ψg) (hsub : SizeSubstWf Ψ as Ψg) :
    LCSubst (Ψg.dom.zip as) ∧ ValidVal Ψg (substVal ρ (Ψg.dom.zip as)) ∧
      Ψg.map (fun p => substVal ρ (Ψg.dom.zip as) p.1) = as.map (sizeVal ρ SzEnv.zero) := by
  obtain ⟨hlen, hlt⟩ := hsub
  have hnd := hwf.nodup
  have hdlen : Ψg.dom.length = as.length := by simp [SizeCtx.dom, hlen]
  have hlc : LCSubst (Ψg.dom.zip as) := by
    intro i b hb
    have hbm := lookup_zip_mem hb
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hbm
    have hkΨ : k < Ψg.length := by rw [← hlen]; exact hk
    exact Size.LC.of_wf (hlt k hkΨ hk).wf.1
  have hval : ∀ k (hk : k < Ψg.length) (ha : k < as.length),
      substVal ρ (Ψg.dom.zip as) (Ψg[k]).1 = sizeVal ρ SzEnv.zero as[k] := by
    intro k hk ha
    have hkd : k < Ψg.dom.length := by simpa [SizeCtx.dom] using hk
    have := lookup_zip_getElem Ψg.dom as hnd hdlen k hkd ha
    have hdk : Ψg.dom[k]'hkd = (Ψg[k]).1 := by simp [SizeCtx.dom]
    rw [hdk] at this
    simp only [substVal, this]
  refine ⟨hlc, ?_, ?_⟩
  · intro p hp
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hp
    have ha : k < as.length := by rw [hlen]; exact hk
    rw [hval k hk ha, ← sizeVal_subst hlc]
    exact sizeLt_sound hv (hlt k hk ha)
  · apply List.ext_getElem (by simp [hlen])
    intro k h1 h2
    simp only [List.getElem_map]
    exact hval k (by simpa using h1) (by simpa using h2)

/-! ## The guard on local calls -/

/-- Invariants of size contexts and valuations that are stable under extension. -/
def InvMono (Inv : SizeCtx → SizeVal → Prop) : Prop :=
  ∀ Ψ Ψ' ρ ρ', Inv Ψ ρ → (∀ i ∈ Ψ.dom, i ∈ Ψ'.dom) → (∀ i ∈ Ψ.dom, ρ' i = ρ i) → Inv Ψ' ρ'

/-- Calls into the current block admitted by `localOK` are semantically safe, in every valid
context satisfying the invariant `Inv`. -/
def GuardOK (W : World) (Ω : TypingEnv) (Inv : SizeCtx → SizeVal → Prop) : Prop :=
  ∀ (Ψ : SizeCtx) (ρ : SizeVal) (g : FunDecl) (as : List Size), g ∈ Ω.block →
    Ω.localOK Ψ g.name as → ValidVal Ψ ρ → Inv Ψ ρ →
    ∀ ρg : SizeVal, ValidVal g.sizeParams ρg →
      g.sizeParams.map (fun p => ρg p.1) = as.map (sizeVal ρ SzEnv.zero) →
      Tm.fn g.name ∈ interpT W ρg TEnv.empty g.ty SzEnv.zero Env.empty

/-- Semantic soundness of a clause under an outer substitution. -/
def ClauseSound (W : World) (c : SCtx) (A : Ty) (σ : TmSubst) : Clause → Prop
  | .mk qs t => ∀ es σm c' C', SemSpine W c A es c' C' → matchSpine qs es = .yes σm →
      Tm.appSpine ((t.subst (σ.filter (fun p => decide (p.1 ∉ spineVars qs)))).subst σm)
        (es.drop qs.length) ∈ c'.den W C'

/-- Hypotheses shared by every case of the fundamental lemma. -/
structure FundEnv (W : World) (Ω : TypingEnv) (Inv : SizeCtx → SizeVal → Prop) : Prop where
  closed : WorldClosed W
  sig : SemValid W Ω.sig
  guard : GuardOK W Ω Inv
  mono : InvMono Inv

/-- Invariants of a context in which a term is interpreted. -/
structure CtxOK (W : World) (Inv : SizeCtx → SizeVal → Prop) (Ψ : SizeCtx) (Θ : TyCtx)
    (Γ : TermCtx) (ρ : SizeVal) (θ : TEnv) (σ : TmSubst) : Prop where
  val : ValidVal Ψ ρ
  bounds : CtxBoundsWf Ψ
  tenv : TEnvOK W Θ θ
  types : TermCtxWf Ψ Θ Γ
  sem : SemCtx W ρ θ Γ σ
  inv : Inv Ψ ρ

theorem lookup_first {Γ : TermCtx} {y : Nat} {B : Ty} (hm : (y, B) ∈ Γ) :
    ∃ B', Γ.lookup y = some B' := by
  induction Γ with
  | nil => simp at hm
  | cons q Γ ih =>
    obtain ⟨z, C⟩ := q
    rw [List.lookup_cons]
    by_cases hyz : y = z
    · subst hyz; exact ⟨C, by simp⟩
    · have : (y == z) = false := beq_eq_false_iff_ne.mpr hyz
      simp only [this]
      rcases List.mem_cons.mp hm with hm | hm
      · simp at hm; exact absurd hm.1 hyz
      · exact ih hm

/-- A function type closed in type variables does not depend on the type environment. -/
theorem interp_fun_ty {W : World} {g : FunDecl} (hcl : KindingC g.sizeParams [] g.ty .star)
    (ρ : SizeVal) (θ : TEnv) :
    interpT W ρ θ g.ty SzEnv.zero Env.empty = interpT W ρ TEnv.empty g.ty SzEnv.zero Env.empty :=
  interp_agree (hcl.tyWf) ρ ρ θ TEnv.empty _ _ _ _ (fun _ _ => rfl)
    (fun X hX => by simp [KCtx.dom] at hX) (fun _ _ => rfl) (fun _ _ => rfl) _

theorem TEnvOK.trel {W : World} {Θ : TyCtx} {θ : TEnv} (h : TEnvOK W Θ θ) : TRel W Θ.toK θ θ := h

theorem BRel.nil (W : World) (η η' : Env) : BRel W [] η η' := fun _ _ _ hk => by simp at hk

/-- The value of a well-kinded type is good. -/
theorem good_of_kinding {W : World} (hW : WorldClosed W) {Ψ : SizeCtx} {Θ : TyCtx} {T : Ty}
    {κ : Kind} (hT : KindingC Ψ Θ.toK T κ) (ρ : SizeVal) {θ : TEnv} (hθ : TEnvOK W Θ θ) :
    Good W κ (interp W ρ θ T κ.erase SzEnv.zero Env.empty) :=
  (kinding_sound hW hT ρ θ θ SzEnv.zero Env.empty Env.empty hθ (BRel.nil W _ _)).1

/-- Instantiating a type binder with the denotation of a type. -/
theorem interp_inst_ty {W : World} {Ψ : SizeCtx} {Θ : TyCtx} {κ : Kind} {B T : Ty}
    (hB : Kinding Ψ Θ.toK [(.mix, κ)] 0 B .star) (hT : KindingC Ψ Θ.toK T κ) (ρ : SizeVal)
    (θ : TEnv) :
    interpT W ρ θ (B.substTy 0 T) SzEnv.zero Env.empty =
      interpT W ρ θ B SzEnv.zero
        (Env.cons (PSem.ofSem κ.erase (interp W ρ θ T κ.erase SzEnv.zero Env.empty)) Env.empty) := by
  have hTw : TyWf Ψ (Θ.toK.dom) 0 0 T := hT.tyWf
  unfold interpT
  rw [interp_openTy (envFree_of_closed hTw ρ θ)]
  apply interp_agree_kinded hB ρ θ θ SzEnv.zero
  · intros; rfl
  · intro k π κ' hk
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hk
      obtain ⟨rfl, rfl⟩ := hk
      simp [tyVal]
    | succ k => simp at hk

/-- The fundamental lemma: expressions and clauses. -/
theorem fundamental {W : World} {Ω : TypingEnv} {Inv : SizeCtx → SizeVal → Prop}
    (E : FundEnv W Ω Inv) {Ψ : SizeCtx} {Θ : TyCtx} {Γ : TermCtx} {t : Tm} {A : Ty}
    (h : ExprTy Ω Ψ Θ Γ t A) :
    ∀ ρ θ σ, CtxOK W Inv Ψ Θ Γ ρ θ σ →
      KindingC Ψ Θ.toK A .star ∧ t.subst σ ∈ interpT W ρ θ A SzEnv.zero Env.empty := by
  have hW := E.closed
  refine ExprTy.rec
    (motive_1 := fun Ψ Θ Γ t A _ => ∀ ρ θ σ, CtxOK W Inv Ψ Θ Γ ρ θ σ →
      KindingC Ψ Θ.toK A .star ∧ t.subst σ ∈ interpT W ρ θ A SzEnv.zero Env.empty)
    (motive_2 := fun Ψ Θ Γ cl A _ => ∀ ρ θ σ, CtxOK W Inv Ψ Θ Γ ρ θ σ →
      KindingC Ψ Θ.toK A .star → ClauseSound W ⟨Ψ, Θ, ρ, θ⟩ A σ cl)
    ?c_var ?c_unit ?c_pair ?c_cons ?c_app ?c_proj ?c_instT ?c_instS ?c_packT ?c_packS ?c_lam
    ?c_glob ?c_loc ?c_sub ?c_clause h
  case c_var =>
    intro Ψ Θ Γ x A hx ρ θ σ hok
    obtain ⟨v, hv, hmem⟩ := hok.sem.1 x A hx
    refine ⟨hok.types _ (lookup_mem_ctx hx), ?_⟩
    simp only [Tm.subst, hv, Option.getD_some]
    exact hmem
  case c_unit =>
    intro Ψ Θ Γ ρ θ σ hok
    exact ⟨.unit, ⟨⟨rfl, SN.unit W⟩, fun v hv _ => steps_unit_inv hv⟩⟩
  case c_pair =>
    intro Ψ Θ Γ t u A B _ _ ih₁ ih₂ ρ θ σ hok
    obtain ⟨hA, ht⟩ := ih₁ ρ θ σ hok
    obtain ⟨hB, hu⟩ := ih₂ ρ θ σ hok
    have cA := interp_cand_closed hW hA ρ hok.tenv
    have cB := interp_cand_closed hW hB ρ hok.tenv
    refine ⟨.prod hA hB, ?_⟩
    unfold interpT
    rw [interp_prod_star]
    refine ⟨⟨?_, SN.pair (cA.sn _ ht).2 (cB.sn _ hu).2⟩, ?_⟩
    · simp only [Tm.subst]
      unfold Tm.Closed; simp only [Tm.fv]
      rw [(cA.sn _ ht).1, (cB.sn _ hu).1]; rfl
    · intro v hv _
      simp only [Tm.subst] at hv
      obtain ⟨t', u', rfl, h1, h2⟩ := steps_pair_inv hv
      exact ⟨t', u', rfl, cA.red_steps ht h1, cB.red_steps hu h2⟩
  case c_cons =>
    intro Ψ Θ Γ c t a b S Sc hc hb hwf _ ih ρ θ σ hok
    obtain ⟨_, ht⟩ := ih ρ θ σ hok
    have hcl : c < S.length := (List.getElem?_eq_some_iff.mp hc).1
    have hScEq : S[c] = Sc := (List.getElem?_eq_some_iff.mp hc).2
    have hbwf : SizeWf Ψ b := hb.wf.1
    have hwfb := hwf.mu_size hbwf
    obtain ⟨_, π, _, _, hS⟩ := Kinding.inv_mu hwf
    have hwfbw : TyWf Ψ (Θ.toK.dom) 0 0 (.mu b S) := hwfb.tyWf
    unfold interpT at ht
    rw [← hScEq, interp_unfold_mu hcl hwfbw] at ht
    set F := fun c (𝒳 : Set Tm) =>
      interpAt W ρ θ S c SzEnv.zero (Env.cons (PSem.ofSem .star 𝒳) Env.empty) with hF
    have hFc : ∀ β, Cand W (F c (MuSet W F β)) := fun β =>
      functor_cand hW hok.tenv.trel hS c hcl _ (muSet_cand hW F β)
    refine ⟨hwf, ?_⟩
    simp only [Tm.subst]
    unfold interpT
    rw [interp_mu_star, MuSet_eq]
    have hsn := (hFc _).sn _ ht
    refine ⟨⟨by unfold Tm.Closed; simp only [Tm.fv]; exact hsn.1, SN.cons hsn.2⟩, ?_⟩
    intro v hv _
    obtain ⟨t'', rfl, hst⟩ := steps_cons_inv hv
    have ht'' := (hFc _).red_steps ht hst
    have hlt := sizeLt_sound hok.val hb
    rcases lt_up_cases ρ SzEnv.zero a hlt with hlt' | hΩ
    · exact ⟨c, t'', sizeVal ρ SzEnv.zero b, hlt', rfl, ht''⟩
    · by_cases hba : sizeVal ρ SzEnv.zero b < sizeVal ρ SzEnv.zero a
      · exact ⟨c, t'', sizeVal ρ SzEnv.zero b, hba, rfl, ht''⟩
      · have hbΩ : Omega ≤ sizeVal ρ SzEnv.zero b := hΩ.trans (not_lt.mp hba)
        rw [muSet_ge_omega W F hbΩ] at ht''
        obtain ⟨β, hβ, hβm⟩ := muSet_omega_closed ht''
        exact ⟨c, t'', β, lt_of_lt_of_le hβ hΩ, rfl, hβm⟩
  case c_app =>
    intro Ψ Θ Γ r s A B _ _ ih₁ ih₂ ρ θ σ hok
    obtain ⟨hAB, hr⟩ := ih₁ ρ θ σ hok
    obtain ⟨_, hs⟩ := ih₂ ρ θ σ hok
    refine ⟨(Kinding.inv_arr hAB).2.2, ?_⟩
    simp only [Tm.subst, Elim.subst]
    unfold interpT at hr
    rw [interp_arr_star] at hr
    exact hr.2 _ hs
  case c_proj =>
    intro Ψ Θ Γ r a b R d Rd _ hd hb ih ρ θ σ hok
    obtain ⟨hwf, hr⟩ := ih ρ θ σ hok
    have hdl : d < R.length := (List.getElem?_eq_some_iff.mp hd).1
    have hRdEq : R[d] = Rd := (List.getElem?_eq_some_iff.mp hd).2
    have hbwf : SizeWf Ψ b := hb.wf.1
    have hwfb := hwf.nu_size hbwf
    refine ⟨hwf.unfold_nu (TyCtx.toK_allMix Θ) hd hbwf, ?_⟩
    simp only [Tm.subst, Elim.subst]
    unfold interpT
    rw [← hRdEq, interp_unfold_nu hdl hwfb.tyWf]
    unfold interpT at hr
    rw [interp_nu_star] at hr
    have hlt := sizeLt_sound hok.val hb
    rcases lt_up_cases ρ SzEnv.zero a hlt with hlt' | hΩ
    · rw [NuSet_eq] at hr
      exact hr.2 _ hlt' d hdl
    · by_cases hba : sizeVal ρ SzEnv.zero b < sizeVal ρ SzEnv.zero a
      · rw [NuSet_eq] at hr
        exact hr.2 _ hba d hdl
      · have hbΩ : Omega ≤ sizeVal ρ SzEnv.zero b := hΩ.trans (not_lt.mp hba)
        rw [nuSet_ge_omega W _ _ hΩ] at hr
        rw [nuSet_ge_omega W _ _ hbΩ]
        exact nuSet_omega_proj hr hdl
  case c_instT =>
    intro Ψ Θ Γ r κ B T _ hT ih ρ θ σ hok
    obtain ⟨hwf, hr⟩ := ih ρ θ σ hok
    have hB := (Kinding.inv_allT hwf).2
    refine ⟨Kinding.open_ty hB (TyCtx.toK_allMix Θ) hT, ?_⟩
    simp only [Tm.subst, Elim.subst]
    rw [interp_inst_ty hB hT]
    unfold interpT at hr
    rw [interp_allT_star] at hr
    exact hr.2 _ (good_of_kinding hW hT ρ hok.tenv)
  case c_instS =>
    intro Ψ Θ Γ r a b B _ hb ih ρ θ σ hok
    obtain ⟨hwf, hr⟩ := ih ρ θ σ hok
    obtain ⟨_, _, hB⟩ := Kinding.inv_allS hwf
    have hlt := sizeLt_sound hok.val hb
    have hbwf := hb.wf.1
    refine ⟨Kinding.open_sz hB hbwf, ?_⟩
    simp only [Tm.subst, Elim.subst]
    unfold interpT
    rw [interp_openSz0 W ρ θ (Size.LC.of_wf hbwf)]
    unfold interpT at hr
    rw [interp_allS_star] at hr
    exact hr.2 _ hlt
  case c_packT =>
    intro Ψ Θ Γ t κ B T hwf hT _ ih ρ θ σ hok
    obtain ⟨hwfBT, ht⟩ := ih ρ θ σ hok
    have hB := (Kinding.inv_exT hwf).2
    have hY := good_of_kinding hW hT ρ hok.tenv
    have hcB := interp_cand_closed hW hwfBT ρ hok.tenv
    have hsn := hcB.sn _ ht
    rw [interp_inst_ty hB hT] at ht
    have hcB' : Cand W (interpT W ρ θ B SzEnv.zero (Env.cons (PSem.ofSem κ.erase
        (interp W ρ θ T κ.erase SzEnv.zero Env.empty)) Env.empty)) := by
      rw [← interp_inst_ty hB hT]; exact hcB
    refine ⟨hwf, ?_⟩
    simp only [Tm.subst]
    unfold interpT
    rw [interp_exT_star]
    refine ⟨⟨by unfold Tm.Closed; simp only [Tm.fv]; exact hsn.1, SN.pack hsn.2⟩, ?_⟩
    intro v hv _
    obtain ⟨t'', rfl, hst⟩ := steps_pack_inv hv
    exact ⟨t'', _, rfl, hY, hcB'.red_steps ht hst⟩
  case c_packS =>
    intro Ψ Θ Γ t a b B hwf hb _ ih ρ θ σ hok
    obtain ⟨hwfBb, ht⟩ := ih ρ θ σ hok
    have hlt := sizeLt_sound hok.val hb
    have hbwf := hb.wf.1
    have hcB := interp_cand_closed hW hwfBb ρ hok.tenv
    have hsn := hcB.sn _ ht
    have hcB' : Cand W (interpT W ρ θ B (SzEnv.cons (sizeVal ρ SzEnv.zero b) SzEnv.zero)
        Env.empty) := by
      unfold interpT
      rw [← interp_openSz0 W ρ θ (Size.LC.of_wf hbwf)]
      exact hcB
    unfold interpT at ht
    rw [interp_openSz0 W ρ θ (Size.LC.of_wf hbwf)] at ht
    refine ⟨hwf, ?_⟩
    simp only [Tm.subst]
    unfold interpT
    rw [interp_exS_star]
    refine ⟨⟨by unfold Tm.Closed; simp only [Tm.fv]; exact hsn.1, SN.pack hsn.2⟩, ?_⟩
    intro v hv _
    obtain ⟨t'', rfl, hst⟩ := steps_pack_inv hv
    exact ⟨t'', _, rfl, hlt, hcB'.red_steps ht hst⟩
  case c_lam =>
    intro Ψ Θ Γ D A hwfA hD ih ρ θ σ hok
    refine ⟨hwfA, ?_⟩
    simp only [Tm.subst]
    have hpos : PosOK W ⟨Ψ, Θ, ρ, θ⟩ A := ⟨hok.val, hok.bounds, hok.tenv, hwfA⟩
    have hclosed : (Tm.lam (Clause.substList σ D)).Closed := by
      have := Tm.closed_subst (t := .lam D) hok.sem.2 (fun x hx => by
        have hxΓ := exprTy_fv (ExprTy.lam hwfA hD) x hx
        obtain ⟨⟨y, B⟩, hm, rfl⟩ := List.mem_map.mp hxΓ
        obtain ⟨B', hB'⟩ := lookup_first hm
        obtain ⟨v, hv, _⟩ := hok.sem.1 y B' hB'
        exact ⟨v, hv⟩)
      simpa [Tm.subst] using this
    have := clause_head hW (h := .lam (Clause.substList σ D)) (D := Clause.substList σ D)
      (by simp [IsHead]) hclosed (headStep_lam W _) hpos ?_ ?_ [] ⟨Ψ, Θ, ρ, θ⟩ A (.nil _ _)
    · simpa [SCtx.den] using this
    · intro es u c' C hs hsel
      obtain ⟨qs, t', σm, hmem, hm, rfl⟩ := selectClause_inv hsel
      obtain ⟨t₀, hmem₀, rfl⟩ := mem_substList hmem
      exact ih (.mk qs t₀) hmem₀ ρ θ σ hok hwfA es σm c' C hs hm
    · intro es c' C hs qs t' hmem hlt hne
      obtain ⟨t₀, hmem₀, rfl⟩ := mem_substList hmem
      cases hD (.mk qs t₀) hmem₀ with
      | mk hsp _ =>
        exact spine_shape hsp ⟨Ψ, Θ, ρ, θ⟩ A es c' C [] [] (by intro i b h; simp at h)
          (by intro X T h; simp at h) hpos (by rw [Ty.substSize_nil, Ty.substFTy_nil]) hs hlt hne
  case c_glob =>
    intro Ψ Θ Γ g as hg hwfg hclg hsub hwfT ρ θ σ hok
    refine ⟨hwfT, ?_⟩
    obtain ⟨hlc, hvg, _⟩ := callee_val hok.val hwfg hsub
    simp only [Tm.subst]
    unfold interpT
    rw [interp_substSize W ρ θ hlc]
    have := interp_fun_ty (W := W) hclg (substVal ρ (g.sizeParams.dom.zip as)) θ
    unfold interpT at this
    rw [this]
    exact E.sig g hg _ hvg
  case c_loc =>
    intro Ψ Θ Γ g as hg hwfg hclg hsub hwfT hloc ρ θ σ hok
    refine ⟨hwfT, ?_⟩
    obtain ⟨hlc, hvg, hmap⟩ := callee_val hok.val hwfg hsub
    simp only [Tm.subst]
    unfold interpT
    rw [interp_substSize W ρ θ hlc]
    have := interp_fun_ty (W := W) hclg (substVal ρ (g.sizeParams.dom.zip as)) θ
    unfold interpT at this
    rw [this]
    exact E.guard Ψ ρ g as hg hloc hok.val hok.inv _ hvg hmap
  case c_sub =>
    intro Ψ Θ Γ t A B _ hAB hwfB ih ρ θ σ hok
    obtain ⟨_, ht⟩ := ih ρ θ σ hok
    exact ⟨hwfB, (subTy_sound hW hAB ρ θ hok.val hok.bounds hok.tenv.trel).2.2 ht⟩
  case c_clause =>
    intro Ψ Ψ' Θ Θ' Γ Γ' qs t A C hsp _ ih ρ θ σ hok hwfA
    intro es σm ce Ce hs hm
    have hlenq := matchSpine_yes_length hm
    have hes : es = es.take qs.length ++ es.drop qs.length := (List.take_append_drop _ _).symm
    rw [hes] at hs
    obtain ⟨cm, Tm', hs₁, hs₂⟩ := semSpine_split hs
    have hm₁ := matchSpine_take hm
    have hpos : PosOK W ⟨Ψ, Θ, ρ, θ⟩ A := ⟨hok.val, hok.bounds, hok.tenv, hwfA⟩
    obtain ⟨ρc, θc, πS', πT', hv', hb', hθ', hag', hagθ', hctx', hΓ', hC, hren'⟩ :=
      spine_align hW hsp ρ θ ⟨Ψ, Θ, ρ, θ⟩ A _ cm Tm' σm [] [] hpos hpos
        (by rw [Ty.substSize_nil, Ty.substFTy_nil]) (Renaming.refl W _) hs₁ hm₁
        (by simp [List.length_take]; omega)
    have hokb : CtxOK W Inv (Ψ ++ Ψ') (Θ ++ Θ') (Γ' ++ Γ) ρc θc (σm ++ σ) := by
      refine ⟨hv', hb', hθ', ?_, ?_, ?_⟩
      · intro p hp
        rcases List.mem_append.mp hp with hp | hp
        · exact hΓ' p hp
        · have := hok.types p hp
          rw [TyCtx.toK_append]
          exact KindingC.mono_append this
      · apply hctx'.append (hok.sem.agree hok.types (fun i hi => (hag' i hi).symm)
          (fun X hX => (hagθ' X hX).symm))
        rw [(matchSpine_facts qs _ σm hm₁).1, spineTy_dom hsp]
      · exact E.mono Ψ (Ψ ++ Ψ') ρ ρc hok.inv dom_append_left hag'
    obtain ⟨_, hbody⟩ := ih ρc θc (σm ++ σ) hokb
    have hσc : ∀ x v, (σ.filter (fun p => decide (p.1 ∉ spineVars qs))).lookup x = some v →
        v.Closed := by
      intro x v hx
      rw [lookup_filter_not_mem] at hx
      by_cases hmx : x ∈ spineVars qs
      · simp [hmx] at hx
      · simp only [hmx, if_false] at hx; exact hok.sem.2 x v hx
    have hdomm : σm.map Prod.fst = spineVars qs := (matchSpine_facts qs _ σm hm₁).1
    have heq : (t.subst (σ.filter (fun p => decide (p.1 ∉ spineVars qs)))).subst σm =
        t.subst (σm ++ σ) := by
      rw [Tm.subst_subst hσc]
      apply Tm.subst_congr
      intro x
      rw [List.lookup_append, List.lookup_append, lookup_filter_not_mem]
      by_cases hmx : x ∈ spineVars qs
      · obtain ⟨v, hv⟩ := lookup_isSome_of_mem (σ := σm) (by rw [hdomm]; exact hmx)
        simp [hmx, hv]
      · have hn : σm.lookup x = none := lookup_none_of_not_mem (by rw [hdomm]; exact hmx)
        simp [hmx, hn]
    rw [heq]
    have hposm := semSpine_posOK hs₁ hpos
    have hmem : t.subst (σm ++ σ) ∈ cm.den W Tm' := by
      rw [← hren'.den_eq hposm.tyWf, ← hC]; exact hbody
    exact semSpine_app hs₂ hposm _ hmem

end NishtAbel2024V5

/-! ## Solutions/V5/Main.lean -/

/-! # V5: size-change termination on ordinals, and the main theorems -/

namespace NishtAbel2024V5

open NishtAbel2024V2 (InvGraph InvGraphFamily SCTValid FunName InvGraphClosure)
open NishtAbel2024V2.SCTPort

/-- Infinite Ramsey's theorem for pairs with finitely many colours. Proved in `SCT/Ramsey.lean`
and supplied in `Final.lean`; taken as a hypothesis here to keep this file's imports light. -/
def RamseyPairs : Prop :=
  ∀ {C : Type} [Finite C] (color : Finset Nat → C), ∃ (M : Set Nat) (b : C), M.Infinite ∧
    ∀ s : Finset Nat, (↑s : Set Nat) ⊆ M → s.card = 2 → color s = b

/-! ## Theorem 1: the semantic call relation is well-founded -/

/-- `β⃗ ≺_G α⃗` for ordinals (the V2 `ConformsToGraph` is restricted to `Type`). -/
def OrdConforms (G : InvGraph) (βs αs : List Ordinal.{0}) : Prop :=
  βs.length = G.leftArity ∧ αs.length = G.rightArity ∧
  ∀ (i j : Nat) (hi : i < βs.length) (hj : j < αs.length),
    (G.edgeAt i j = some .lt → βs[i] < αs[j]) ∧ (G.edgeAt i j = some .le → βs[i] ≤ αs[j])

theorem conforms_sound {Ψ : SizeCtx} {ρ : SizeVal} (hv : ValidVal Ψ ρ) {G : InvGraph}
    {xs ys : List Size} (h : NishtAbel2024V2.ConformsToGraph (SizeLt Ψ) (SizeLe Ψ) G xs ys) :
    OrdConforms G (xs.map (sizeVal ρ SzEnv.zero)) (ys.map (sizeVal ρ SzEnv.zero)) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by simpa using h1, by simpa using h2, ?_⟩
  intro i j hi hj
  have hi' : i < xs.length := by simpa using hi
  have hj' : j < ys.length := by simpa using hj
  obtain ⟨a, b⟩ := h3 i j hi' hj'
  exact ⟨fun e => by simpa using sizeLt_sound hv (a e),
    fun e => by simpa using sizeLe_sound hv (b e)⟩

/-- `(g, β⃗) ≺ (f, α⃗)`: some invocation graph from `f` to `g` relates the sizes. -/
def CallRel (𝒢 : InvGraphFamily) (callee caller : FunName × List Ordinal.{0}) : Prop :=
  ∃ G ∈ 𝒢.graphs caller.1 callee.1, OrdConforms G callee.2 caller.2

theorem ordConforms_iff {G : InvGraph} {βs αs : List Ordinal.{0}} :
    OrdConforms G βs αs ↔ ConformsU (· < ·) (· ≤ ·) G βs αs := by
  simp only [OrdConforms, ConformsU, List.get_eq_getElem]

theorem callRel_wf (ramsey : RamseyPairs) (𝒢 : InvGraphFamily) (valid : SCTValid 𝒢) :
    WellFounded (CallRel 𝒢) := by
  apply NishtAbel2024V3.wellFounded_of_no_descending_sequence
  intro states steps
  classical
  choose g hg hc using steps
  have hclosed : ∀ i, InvGraphClosure 𝒢 (states i).1 (states (i + 1)).1 (g i) := by
    intro i
    have hn := (valid.1.2 (states i).1 (states (i + 1)).1 (g i) (hg i)).2.2
    simpa only [← hn] using (InvGraphClosure.base (hg i))
  have hconf : ∀ i, ConformsU (· < ·) (· ≤ ·) (g i) (states (i + 1)).2 (states i).2 :=
    fun i => ordConforms_iff.mp (hc i)
  obtain ⟨dom, hsupport⟩ := valid.1.1
  have hnames : ∀ n, (states n).1 ∈ dom := fun n => (closure_support 𝒢 dom hsupport (hclosed n)).1
  apply no_chain_from_finite_intervals (· < ·) (· ≤ ·) Ordinal.lt_wf 𝒢 valid dom
    (fun n => (states n).1) hnames (interval g) (fun n => (states n).2)
  · exact interval_concat_of_conforms (fun x1 x2 : Ordinal.{0} => x1 < x2)
      (fun x1 x2 : Ordinal.{0} => x1 ≤ x2) g (fun n => (states n).2) hconf
  · exact interval_closed 𝒢 (fun n => (states n).1) g hclosed
  · exact interval_conforms (fun x1 x2 : Ordinal.{0} => x1 < x2)
      (fun x1 x2 : Ordinal.{0} => x1 ≤ x2) (fun _ _ h => h.le) (fun _ _ _ => le_trans)
      (fun _ _ _ => lt_of_lt_of_le) (fun _ _ _ => lt_of_le_of_lt) g (fun n => (states n).2) hconf
  · exact ramsey

/-! ## Auxiliary facts -/

theorem World.lookup_of_mem {W : World} (hn : (W.map FunDecl.name).Nodup) {d : FunDecl}
    (hd : d ∈ W) : W.lookup d.name = some d := by
  unfold World.lookup
  cases h : W.find? (fun e => e.name == d.name) with
  | none =>
    have := List.find?_eq_none.mp h d hd
    simp at this
  | some e =>
    have he := List.mem_of_find?_eq_some h
    have hname : e.name = d.name := by simpa using List.find?_some h
    rw [List.inj_on_of_nodup_map hn he hd hname]

theorem Tm.subst_nil (t : Tm) : t.subst [] = t := Tm.subst_of_fv t (fun _ _ => rfl)

theorem clauses_closed {Ω : TypingEnv} {Ψ : SizeCtx} {Θ : TyCtx} {A : Ty} {D : List Clause}
    (hA : KindingC Ψ Θ.toK A .star) (hD : ∀ cl ∈ D, ClauseTy Ω Ψ Θ [] cl A) :
    (Tm.lam D).Closed := by
  unfold Tm.Closed
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro x hx
  have := exprTy_fv (ExprTy.lam hA hD) x hx
  simp at this

/-! ## Theorem 4: soundness of mutual blocks -/

/-- The context invariant used for the block of `d` at caller sizes `αc`. -/
def CallerInv (d : FunDecl) (αc : List Ordinal.{0}) (Ψ : SizeCtx) (ρ : SizeVal) : Prop :=
  (∀ p ∈ d.sizeParams, p.1 ∈ Ψ.dom) ∧ d.sizeParams.map (fun p => ρ p.1) = αc

theorem callerInv_mono (d : FunDecl) (αc : List Ordinal.{0}) : InvMono (CallerInv d αc) := by
  intro Ψ Ψ' ρ ρ' ⟨hdom, hval⟩ hsub hag
  refine ⟨fun p hp => hsub _ (hdom p hp), ?_⟩
  rw [← hval]
  apply List.map_congr_left
  intro p hp
  exact hag p.1 (hdom p hp)

theorem theorem_4_proof (ramsey : RamseyPairs) (W sig Ξ : List FunDecl)
    (hW : ∀ d ∈ sig ++ Ξ, d ∈ W)
    (hnames : (W.map FunDecl.name).Nodup)
    (hclosed : ∀ d ∈ W, (Tm.lam d.clauses).Closed)
    (htyped : BlockTy sig Ξ)
    (hsig : SemValid W sig) :
    SemValid W Ξ := by
  obtain ⟨𝒢, hsct, _, hdecl⟩ := htyped
  have hwc : WorldClosed W := hclosed
  have hwf := callRel_wf ramsey 𝒢 hsct
  suffices H : ∀ st : FunName × List Ordinal.{0}, ∀ d ∈ Ξ, d.name = st.1 →
      ∀ ρ, ValidVal d.sizeParams ρ → d.sizeParams.map (fun p => ρ p.1) = st.2 →
      Tm.fn d.name ∈ interpT W ρ TEnv.empty d.ty SzEnv.zero Env.empty by
    intro d hd ρ hv
    exact H (d.name, d.sizeParams.map (fun p => ρ p.1)) d hd rfl ρ hv rfl
  intro st
  induction st using hwf.induction with
  | _ st ih =>
  intro d hd hname ρ hv hst
  obtain ⟨hctxwf, htywf, hcls⟩ := hdecl d hd
  let Ω : TypingEnv := ⟨sig, Ξ, sctCallOK 𝒢 d.name d.sizeParams⟩
  have hguard : GuardOK W Ω (CallerInv d st.2) := by
    rintro Ψ ρ' g as hg ⟨G, hG, hconf⟩ hv' ⟨_, hinv⟩ ρg hvg hmap
    refine ih (g.name, g.sizeParams.map (fun p => ρg p.1)) ⟨G, ?_, ?_⟩ g hg rfl ρg hvg rfl
    · rw [← hname]; exact hG
    · have hc := conforms_sound hv' hconf
      rw [← hmap] at hc
      rw [← hinv]
      have : (d.sizeParams.map (fun p => Size.var p.1 0)).map (sizeVal ρ' SzEnv.zero) =
          d.sizeParams.map (fun p => ρ' p.1) := by
        simp [sizeVal]
      rw [← this]
      exact hc
  have E : FundEnv W Ω (CallerInv d st.2) := ⟨hwc, hsig, hguard, callerInv_mono d st.2⟩
  have hθ : TEnvOK W [] TEnv.empty := by intro X π κ hX; simp [TyCtx.toK] at hX
  have hok : CtxOK W (CallerInv d st.2) d.sizeParams [] [] ρ TEnv.empty [] :=
    ⟨hv, hctxwf.bounds, hθ, by simp [TermCtxWf], SemCtx.nil W ρ TEnv.empty,
      fun p hp => SizeCtx.mem_dom (a := p.2) (by simpa using hp), hst⟩
  have hlam := (fundamental E (ExprTy.lam htywf hcls) ρ TEnv.empty [] hok).2
  rw [Tm.subst_nil] at hlam
  have hpos : PosOK W ⟨d.sizeParams, [], ρ, TEnv.empty⟩ d.ty := ⟨hv, hctxwf.bounds, hθ, htywf⟩
  have hdW : d ∈ W := hW d (List.mem_append_right _ hd)
  have := clause_head hwc (h := .fn d.name) (D := d.clauses) (by simp [IsHead]) rfl
    (headStep_fn (World.lookup_of_mem hnames hdW)) hpos ?_ ?_ [] _ _ (.nil _ _)
  · simpa [SCtx.den] using this
  · intro es u c' C hs hsel
    have hl := semSpine_app hs hpos _ hlam
    have hst' : Step W (Tm.appSpine (.lam d.clauses) es) u :=
      Step.head (by rw [headStep_lam]; exact hsel)
    have hposC := semSpine_posOK hs hpos
    exact (interp_cand_closed hwc hposC.2.2.2 c'.ρ hposC.2.2.1).red _ hl _ hst'
  · intro es c' C hs qs t hmem hlt hne
    cases hcls (.mk qs t) hmem with
    | mk hsp _ =>
      exact spine_shape hsp _ d.ty es c' C [] [] (by intro i b h; simp at h)
        (by intro X T h; simp at h) hpos (by rw [Ty.substSize_nil, Ty.substFTy_nil]) hs hlt hne

/-! ## Theorem 5 -/

theorem blocks_closed {blocks : List (List FunDecl)} (h : BlocksTy blocks) :
    ∀ d ∈ blocks.flatten, (Tm.lam d.clauses).Closed := by
  induction h with
  | nil => intro d hd; simp at hd
  | snoc _ hΞ ih =>
    intro d hd
    simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil,
      List.mem_append] at hd
    rcases hd with hd | hd
    · exact ih d hd
    · obtain ⟨𝒢, _, _, hdecl⟩ := hΞ
      obtain ⟨_, hA, hcls⟩ := hdecl d hd
      exact clauses_closed hA hcls

theorem blocks_valid (ramsey : RamseyPairs) {W : World} (hnames : (W.map FunDecl.name).Nodup) (hwc : WorldClosed W)
    {blocks : List (List FunDecl)} (h : BlocksTy blocks) (hsub : ∀ d ∈ blocks.flatten, d ∈ W) :
    SemValid W blocks.flatten := by
  induction h with
  | nil => intro d hd; simp at hd
  | @snoc blocks Ξ _ hΞ ih =>
    have hsub' : ∀ d ∈ blocks.flatten, d ∈ W := fun d hd => hsub d (by simp [hd])
    have hprev := ih hsub'
    have hnew := theorem_4_proof ramsey W blocks.flatten Ξ (fun d hd => hsub d (by simpa using hd))
      hnames hwc hΞ hprev
    intro d hd ρ hv
    simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil,
      List.mem_append] at hd
    rcases hd with hd | hd
    · exact hprev d hd ρ hv
    · exact hnew d hd ρ hv

theorem theorem_5_proof (ramsey : RamseyPairs) (blocks : List (List FunDecl)) (main : Tm) (A : Ty)
    (htyped : ProgramTy blocks main A) :
    SN blocks.flatten main := by
  obtain ⟨hbt, hnames, hmain⟩ := htyped
  have hwc : WorldClosed blocks.flatten := blocks_closed hbt
  have hvalid := blocks_valid ramsey hnames hwc hbt (fun d hd => hd)
  let Ω : TypingEnv := ⟨blocks.flatten, [], fun _ _ _ => False⟩
  have E : FundEnv blocks.flatten Ω (fun _ _ => True) :=
    ⟨hwc, hvalid, fun _ _ g _ hg => by simp [Ω] at hg, fun _ _ _ _ _ _ _ => trivial⟩
  have hθ : TEnvOK blocks.flatten [] TEnv.empty := by intro X π κ hX; simp [TyCtx.toK] at hX
  have hok : CtxOK blocks.flatten (fun _ _ => True) [] [] [] (fun _ => 0) TEnv.empty [] :=
    ⟨by intro p hp; simp at hp, by intro p hp; simp at hp, hθ, by simp [TermCtxWf],
      SemCtx.nil _ _ _, trivial⟩
  obtain ⟨hA, hm⟩ := fundamental E hmain _ _ _ hok
  rw [Tm.subst_nil] at hm
  exact (interp_closed_mem hwc hA _ hθ hm).2

end NishtAbel2024V5

/-! ## Solutions/V5/LexSCT.lean -/

/-! # Ported from the accepted proof that lexicographic invocation graphs satisfy SCT
(theorem `cfeab656-…`, submission `5dffa624-…`), restated over the V2 graph definitions. -/


namespace NishtAbel2024V2

theorem canonical_mem (n m i j : Nat) (f : Nat → Nat → Option EdgeRel) (r : EdgeRel) :
    (i, j, r) ∈ InvGraph.canonicalEdges n m f ↔ i < n ∧ j < m ∧ f i j = some r := by
  simp [InvGraph.canonicalEdges, List.mem_flatMap, List.mem_filterMap, List.mem_range,
    Option.map_eq_some_iff, Prod.mk.injEq]
  try grind

private theorem fold_ne_none {α : Type} (f : α → EdgeRel) (xs : List α) (r : EdgeRel) :
    xs.foldl (fun acc x => EdgeRel.combine acc (some (f x))) (some r) ≠ none := by
  induction xs generalizing r with
  | nil => simp
  | cons x xs ih =>
    cases r <;> cases h : f x <;> simp_all [EdgeRel.combine]

private theorem fold_eq_none_iff {α : Type} (f : α → EdgeRel) (xs : List α) :
    xs.foldl (fun acc x => EdgeRel.combine acc (some (f x))) none = none ↔ xs = [] := by
  cases xs with
  | nil => simp
  | cons x xs =>
    simp only [List.foldl_cons, List.cons_ne_nil, iff_false]
    have hn := fold_ne_none f xs (f x)
    cases h : f x <;> simpa [EdgeRel.combine, h] using hn

private theorem fold_choose {α : Type} (f : α → EdgeRel) (xs : List α)
    (a : Option EdgeRel) (r : EdgeRel)
    (h : xs.foldl (fun acc x => EdgeRel.combine acc (some (f x))) a = some r) :
    a = some r ∨ ∃ x ∈ xs, f x = r := by
  induction xs generalizing a with
  | nil => simpa using h
  | cons x xs ih =>
    have h' := ih (EdgeRel.combine a (some (f x))) h
    cases a <;> cases r <;> cases hfx : f x <;> simp_all [EdgeRel.combine] <;> grind

private theorem edgeAt_mem (G : InvGraph) (i j : Nat) (r : EdgeRel)
    (h : G.edgeAt i j = some r) : (i, j, r) ∈ G.edges := by
  have h' := fold_choose (fun (e : Nat × Nat × EdgeRel) => e.2.2)
    (G.edges.filter (fun e => e.1 == i && e.2.1 == j)) none r h
  simp only [reduceCtorEq, false_or, List.mem_filter, Bool.and_eq_true, beq_iff_eq] at h'
  rcases h' with ⟨⟨x, y, z⟩, ⟨hx, rfl, rfl⟩, rfl⟩
  exact hx

private theorem edgeAt_ne_none_of_mem (G : InvGraph) (i j : Nat) (r : EdgeRel)
    (hm : (i, j, r) ∈ G.edges) : G.edgeAt i j ≠ none := by
  intro h
  have hf := (fold_eq_none_iff (fun (e : Nat × Nat × EdgeRel) => e.2.2)
    (G.edges.filter (fun e => e.1 == i && e.2.1 == j))).mp h
  have hm' : (i, j, r) ∈ G.edges.filter (fun e => e.1 == i && e.2.1 == j) := by
    simp [hm]
  rw [hf] at hm'
  exact List.not_mem_nil hm'

theorem canonical_lookup (n m : Nat) (f : Nat → Nat → Option EdgeRel) (i j : Nat)
    (hi : i < n) (hj : j < m) :
    (InvGraph.mk n m (InvGraph.canonicalEdges n m f)).edgeAt i j = f i j := by
  let G : InvGraph := ⟨n, m, InvGraph.canonicalEdges n m f⟩
  change G.edgeAt i j = f i j
  cases he : G.edgeAt i j with
  | none =>
    cases hf : f i j with
    | none => rfl
    | some r =>
      have hm : (i, j, r) ∈ G.edges := (canonical_mem n m i j f r).2 ⟨hi, hj, hf⟩
      exact False.elim (edgeAt_ne_none_of_mem G i j r hm he)
  | some r =>
    have hm : (i, j, r) ∈ G.edges := edgeAt_mem G i j r he
    exact ((canonical_mem n m i j f r).1 hm).2.2.symm

end NishtAbel2024V2


namespace NishtAbel2024V2.LexGraphBase

theorem getD_eq_elem (ms : List Nat) (k : Nat) (hk : k < ms.length) :
    ms.getD k 0 = ms[k] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]

theorem idxOf_getD (ms : List Nat) (h : ms.Nodup) (k : Nat) (hk : k < ms.length) :
    ms.idxOf? (ms.getD k 0) = some k := by
  rw [getD_eq_elem ms k hk]
  apply List.idxOf?_eq_some_iff.mpr
  refine ⟨hk, rfl, ?_⟩
  intro j hj he
  have hjlen : j < ms.length := by omega
  have heq : j = k := (List.getElem_inj (h₀ := hjlen) (h₁ := hk) h).mp he
  omega

theorem normalized_lookup (G : InvGraph) (i j : Nat)
    (hi : i < G.leftArity) (hj : j < G.rightArity) :
    G.normalize.edgeAt i j = G.edgeAt i j := by
  exact canonical_lookup G.leftArity G.rightArity G.edgeAt i j hi hj

theorem lex_lookup (ms : List Nat) (arity step i j : Nat) (hi : i < arity) (hj : j < arity) :
    (lexInvGraph ms arity step).edgeAt i j =
      (if i == j then
        match ms.idxOf? i with
        | some pos => if pos < step then some .le else if pos == step then some .lt else none
        | none => none
       else none) := by
  exact canonical_lookup arity arity _ i j hi hj

theorem lex_normalized_arities (ms : List Nat) (arity step : Nat) :
    (lexInvGraph ms arity step).normalize.leftArity = arity ∧
      (lexInvGraph ms arity step).normalize.rightArity = arity := by
  exact ⟨rfl, rfl⟩

theorem lex_graph_strict (ms : List Nat) (arity k : Nat)
    (hnd : ms.Nodup) (hb : ∀ i ∈ ms, i < arity) (hk : k < ms.length) :
    ((lexInvGraph ms arity k).normalize).edgeAt (ms.getD k 0) (ms.getD k 0) = some .lt := by
  have he : ms.getD k 0 = ms[k] := getD_eq_elem ms k hk
  have hbound : ms.getD k 0 < arity := by rw [he]; exact hb _ (List.getElem_mem hk)
  rw [normalized_lookup _ _ _ hbound hbound, lex_lookup _ _ _ _ _ hbound hbound]
  rw [idxOf_getD ms hnd k hk]
  simp

theorem lex_graph_earlier (ms : List Nat) (arity k t : Nat)
    (hnd : ms.Nodup) (hb : ∀ i ∈ ms, i < arity)
    (hk : k < ms.length) (ht : t < k) :
    ((lexInvGraph ms arity k).normalize).edgeAt (ms.getD t 0) (ms.getD t 0) = some .le := by
  have htlen : t < ms.length := by omega
  have he : ms.getD t 0 = ms[t] := getD_eq_elem ms t htlen
  have hbound : ms.getD t 0 < arity := by rw [he]; exact hb _ (List.getElem_mem htlen)
  rw [normalized_lookup _ _ _ hbound hbound, lex_lookup _ _ _ _ _ hbound hbound]
  rw [idxOf_getD ms hnd t htlen]
  simp [ht]

end NishtAbel2024V2.LexGraphBase


namespace NishtAbel2024V2.LexComposition

private def edgeMul : Option EdgeRel → Option EdgeRel → Option EdgeRel
  | some a, some b => some (a.seq b)
  | _, _ => none

private def edgeSum (n : Nat) (f : Nat → Option EdgeRel) : Option EdgeRel :=
  ((List.range n).map f).foldr EdgeRel.combine none

private theorem combine_assoc (a b c : Option EdgeRel) :
    EdgeRel.combine (EdgeRel.combine a b) c = EdgeRel.combine a (EdgeRel.combine b c) := by
  rcases a with _ | (_ | _) <;> rcases b with _ | (_ | _) <;> rcases c with _ | (_ | _) <;> rfl

private theorem combine_none_right (a : Option EdgeRel) : EdgeRel.combine a none = a := by
  rcases a with _ | (_ | _) <;> rfl

private theorem combine_foldl_eq_foldr (xs : List (Option EdgeRel)) :
    xs.foldl EdgeRel.combine none = xs.foldr EdgeRel.combine none := by
  have h : ∀ acc, xs.foldl EdgeRel.combine acc = EdgeRel.combine acc (xs.foldr EdgeRel.combine none) := by
    induction xs with
    | nil => intro acc; simp only [List.foldl_nil, List.foldr_nil, combine_none_right]
    | cons x xs ih =>
      intro acc
      simp only [List.foldl_cons, List.foldr_cons, ih, combine_assoc]
  rw [h none]
  rcases xs.foldr EdgeRel.combine none with _ | (_ | _) <;> rfl

private def compEdges (A B : InvGraph) (i j : Nat) : Option EdgeRel :=
  (List.range A.rightArity).foldl
    (fun acc k => match A.edgeAt i k, B.edgeAt k j with
      | some r₁, some r₂ => EdgeRel.combine acc (some (EdgeRel.seq r₁ r₂))
      | _, _ => acc) none

private theorem compEdges_eq (A B : InvGraph) (i j : Nat) :
    compEdges A B i j = edgeSum A.rightArity (fun k => edgeMul (A.edgeAt i k) (B.edgeAt k j)) := by
  unfold compEdges edgeSum
  have hstep : ∀ acc k, (match A.edgeAt i k, B.edgeAt k j with
      | some r₁, some r₂ => EdgeRel.combine acc (some (EdgeRel.seq r₁ r₂))
      | _, _ => acc) = EdgeRel.combine acc (edgeMul (A.edgeAt i k) (B.edgeAt k j)) := by
    intro acc k
    rcases acc with _ | (_ | _) <;> rcases A.edgeAt i k with _ | (_ | _) <;> rcases B.edgeAt k j with _ | (_ | _) <;> rfl
  simp only [hstep, ← List.foldl_map, combine_foldl_eq_foldr]

private theorem comp_def (A B : InvGraph) :
    A.comp B = ⟨A.leftArity, B.rightArity, InvGraph.canonicalEdges A.leftArity B.rightArity (compEdges A B)⟩ := rfl

private theorem foldr_some_ne_none (xs : List (Option EdgeRel)) (r : EdgeRel)
    (h : some r ∈ xs) : xs.foldr EdgeRel.combine none ≠ none := by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
    simp only [List.mem_cons] at h
    cases x with
    | none =>
      simp only [List.foldr_cons]
      have hx : some r ∈ xs := by simpa using h
      have ht := ih hx
      cases he : xs.foldr EdgeRel.combine none with
      | none => exact (ht he).elim
      | some s => cases s <;> simp [EdgeRel.combine]
    | some s =>
      cases s <;> cases he : xs.foldr EdgeRel.combine none with
      | none => simp [List.foldr_cons, he, EdgeRel.combine]
      | some s => cases s <;> simp [List.foldr_cons, he, EdgeRel.combine]

private theorem foldr_lt_of_mem (xs : List (Option EdgeRel))
    (h : some .lt ∈ xs) : xs.foldr EdgeRel.combine none = some .lt := by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
    simp only [List.mem_cons] at h
    rcases h with h | h
    · subst x
      simp [EdgeRel.combine]
    · have ht := ih h
      cases x with
      | none => simp [List.foldr_cons, ht, EdgeRel.combine]
      | some r => cases r <;> simp [List.foldr_cons, ht, EdgeRel.combine]

theorem edgeSum_has_edge {n k : Nat} {f : Nat → Option EdgeRel} {r : EdgeRel}
    (hk : k < n) (h : f k = some r) : ∃ s, edgeSum n f = some s := by
  have hm : some r ∈ (List.range n).map f :=
    List.mem_map.mpr ⟨k, List.mem_range.mpr hk, h⟩
  have hn := foldr_some_ne_none ((List.range n).map f) r hm
  cases he : edgeSum n f with
  | none => exact False.elim (hn he)
  | some s => exact ⟨s, rfl⟩

theorem edgeSum_has_lt {n k : Nat} {f : Nat → Option EdgeRel}
    (hk : k < n) (h : f k = some .lt) : edgeSum n f = some .lt := by
  apply foldr_lt_of_mem
  exact List.mem_map.mpr ⟨k, List.mem_range.mpr hk, h⟩

theorem comp_diagonal_has_edge {A B : InvGraph} {i : Nat} {r s : EdgeRel}
    (hiA : i < A.leftArity) (hiM : i < A.rightArity) (hiB : i < B.rightArity)
    (hA : A.edgeAt i i = some r) (hB : B.edgeAt i i = some s) :
    ∃ t, (A.comp B).edgeAt i i = some t := by
  rw [comp_def, canonical_lookup _ _ _ _ _ hiA hiB, compEdges_eq]
  apply edgeSum_has_edge hiM (r := r.seq s)
  simp [edgeMul, hA, hB]

theorem comp_diagonal_strict_left {A B : InvGraph} {i : Nat} {s : EdgeRel}
    (hiA : i < A.leftArity) (hiM : i < A.rightArity) (hiB : i < B.rightArity)
    (hA : A.edgeAt i i = some .lt) (hB : B.edgeAt i i = some s) :
    (A.comp B).edgeAt i i = some .lt := by
  rw [comp_def, canonical_lookup _ _ _ _ _ hiA hiB, compEdges_eq]
  apply edgeSum_has_lt hiM
  simp [edgeMul, hA, hB, EdgeRel.seq]

theorem comp_diagonal_strict_right {A B : InvGraph} {i : Nat} {r : EdgeRel}
    (hiA : i < A.leftArity) (hiM : i < A.rightArity) (hiB : i < B.rightArity)
    (hA : A.edgeAt i i = some r) (hB : B.edgeAt i i = some .lt) :
    (A.comp B).edgeAt i i = some .lt := by
  rw [comp_def, canonical_lookup _ _ _ _ _ hiA hiB, compEdges_eq]
  apply edgeSum_has_lt hiM
  cases r <;> simp [edgeMul, hA, hB, EdgeRel.seq]

end NishtAbel2024V2.LexComposition


namespace NishtAbel2024V2.LexicographicEmbedding
open LexComposition

/-- A graph contains the non-strict prefix and a strict first decrease
    required by a lexicographic measure. -/
def LexWitness (m : List Nat) (n : Nat) (G : InvGraph) : Prop :=
  G.leftArity = n ∧ G.rightArity = n ∧
    ∃ k, k < m.length ∧
      G.edgeAt (m.getD k 0) (m.getD k 0) = some .lt ∧
      ∀ t, t < k → ∃ r, G.edgeAt (m.getD t 0) (m.getD t 0) = some r

private theorem getD_mem {m : List Nat} {k : Nat} (hk : k < m.length) :
    m.getD k 0 ∈ m := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, List.getElem_mem]

private theorem flatMap_congr {α β : Type} (xs : List α) (f g : α → List β)
    (h : ∀ x ∈ xs, f x = g x) : xs.flatMap f = xs.flatMap g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons]
    rw [h x (by simp), ih (by intro y hy; exact h y (by simp [hy]))]

private theorem filterMap_congr {α β : Type} (xs : List α) (f g : α → Option β)
    (h : ∀ x ∈ xs, f x = g x) : xs.filterMap f = xs.filterMap g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.filterMap_cons]
    rw [h x (by simp), ih (by intro y hy; exact h y (by simp [hy]))]

theorem canonical_normalized (n : Nat) (f : Nat → Nat → Option EdgeRel) :
    (InvGraph.mk n n (InvGraph.canonicalEdges n n f)).normalize =
      InvGraph.mk n n (InvGraph.canonicalEdges n n f) := by
  simp only [InvGraph.normalize, InvGraph.mk.injEq, true_and]
  unfold InvGraph.canonicalEdges
  apply flatMap_congr
  intro i hi
  apply filterMap_congr
  intro j hj
  change Option.map (fun r => (i, j, r))
    ((InvGraph.mk n n (InvGraph.canonicalEdges n n f)).edgeAt i j) = _
  rw [canonical_lookup n n f i j (List.mem_range.mp hi) (List.mem_range.mp hj)]

/-- Composition preserves the earliest of the two strict positions. -/
theorem lexWitness_comp {m : List Nat} {n : Nat} {A B : InvGraph}
    (hbound : ∀ i ∈ m, i < n) (hA : LexWitness m n A) (hB : LexWitness m n B) :
    LexWitness m n (A.comp B) := by
  obtain ⟨hAl, hAr, k, hk, hAk, hApre⟩ := hA
  obtain ⟨hBl, hBr, l, hl, hBl', hBpre⟩ := hB
  have hindex : ∀ t, t < m.length → m.getD t 0 < n := by
    intro t ht
    exact hbound _ (getD_mem ht)
  refine ⟨hAl, hBr, ?_⟩
  by_cases hkl : k ≤ l
  · refine ⟨k, hk, ?_, ?_⟩
    · have h := hindex k hk
      have hBedge : ∃ r, B.edgeAt (m.getD k 0) (m.getD k 0) = some r := by
        by_cases heq : k = l
        · subst l
          exact ⟨.lt, hBl'⟩
        · exact hBpre k (Nat.lt_of_le_of_ne hkl heq)
      obtain ⟨r, hr⟩ := hBedge
      apply comp_diagonal_strict_left (i := m.getD k 0) (s := r)
      · simpa [hAl] using h
      · simpa [hAr] using h
      · simpa [hBr] using h
      · exact hAk
      · exact hr
    · intro t ht
      have ht' : t < m.length := Nat.lt_trans ht hk
      have h := hindex t ht'
      obtain ⟨r, hr⟩ := hApre t ht
      obtain ⟨s, hs⟩ := hBpre t (Nat.lt_of_lt_of_le ht hkl)
      apply comp_diagonal_has_edge (r := r) (s := s)
      · simpa [hAl] using h
      · simpa [hAr] using h
      · simpa [hBr] using h
      · exact hr
      · exact hs
  · have hlk : l < k := Nat.lt_of_not_ge hkl
    refine ⟨l, hl, ?_, ?_⟩
    · have h := hindex l hl
      obtain ⟨r, hr⟩ := hApre l hlk
      apply comp_diagonal_strict_right (i := m.getD l 0) (r := r)
      · simpa [hAl] using h
      · simpa [hAr] using h
      · simpa [hBr] using h
      · exact hr
      · exact hBl'
    · intro t ht
      have ht' : t < m.length := Nat.lt_trans ht hl
      have h := hindex t ht'
      obtain ⟨r, hr⟩ := hApre t (Nat.lt_trans ht hlk)
      obtain ⟨s, hs⟩ := hBpre t ht
      apply comp_diagonal_has_edge (r := r) (s := s)
      · simpa [hAl] using h
      · simpa [hAr] using h
      · simpa [hBr] using h
      · exact hr
      · exact hs

theorem lex_family_arity_wf (dom : List FunName) (n : Nat) (m : List Nat) :
    (lexInvGraphFamily dom n m).ArityWf := by
  constructor
  · refine ⟨dom, ?_⟩
    intro f g hg
    by_cases h : f ∈ dom ∧ g ∈ dom
    · exact h
    · simp [lexInvGraphFamily, h] at hg
  · intro f g G hG
    simp only [lexInvGraphFamily] at hG ⊢
    split at hG
    next h =>
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hG
      simp only [lexInvGraph]
      refine ⟨True.intro, True.intro, ?_⟩
      exact (canonical_normalized n _).symm
    next h => simp at hG

theorem lex_graph_witness (m : List Nat) (n k : Nat) (hnd : m.Nodup)
    (hbound : ∀ i ∈ m, i < n) (hk : k < m.length) :
    LexWitness m n (lexInvGraph m n k).normalize := by
  refine ⟨rfl, rfl, k, hk, LexGraphBase.lex_graph_strict m n k hnd hbound hk, ?_⟩
  intro t ht
  exact ⟨.le, LexGraphBase.lex_graph_earlier m n k t hnd hbound hk ht⟩

theorem lex_closure_witness {dom : List FunName} {n : Nat} {m : List Nat}
    (hnd : m.Nodup) (hbound : ∀ i ∈ m, i < n) {f g : FunName} {G : InvGraph}
    (hG : InvGraphClosure (lexInvGraphFamily dom n m) f g G) :
    LexWitness m n G := by
  induction hG with
  | base h =>
    simp only [lexInvGraphFamily] at h
    split at h
    next =>
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp h
      exact lex_graph_witness m n k hnd hbound (List.mem_range.mp hk)
    next => simp at h
  | comp _ _ ih₁ ih₂ => exact lexWitness_comp hbound ih₁ ih₂

theorem lex_family_sct (dom : List FunName) (n : Nat) (m : List Nat)
    (hnd : m.Nodup) (hbound : ∀ i ∈ m, i < n) :
    SCTValid (lexInvGraphFamily dom n m) := by
  refine ⟨lex_family_arity_wf dom n m, ?_⟩
  intro f G hG _
  obtain ⟨hl, _, k, hk, hstrict, _⟩ := lex_closure_witness hnd hbound hG
  refine ⟨m.getD k 0, ?_, hstrict⟩
  rw [hl]
  exact hbound _ (getD_mem hk)


end NishtAbel2024V2.LexicographicEmbedding


/-! ## Solutions/V5/Theorem6.lean -/

/-! # V5: Theorem 6 — System `F_ω^{cop}` (lexicographic measures) embeds into `F_ω^{cop,SCT}` -/

namespace NishtAbel2024V5

open NishtAbel2024V2 (InvGraph InvGraphFamily SCTValid ConformsToGraph FunName lexInvGraph
  lexInvGraphFamily)

/-! ## Typing is monotone in the admissibility of block calls -/

theorem exprTy_mono_local {sig Ξ : List FunDecl}
    {ok₁ ok₂ : SizeCtx → FunName → List Size → Prop}
    (hok : ∀ Ψ (g : FunDecl) as, g ∈ Ξ → ok₁ Ψ g.name as → ok₂ Ψ g.name as)
    {Ψ : SizeCtx} {Θ : TyCtx} {Γ : TermCtx} {t : Tm} {A : Ty}
    (h : ExprTy ⟨sig, Ξ, ok₁⟩ Ψ Θ Γ t A) : ExprTy ⟨sig, Ξ, ok₂⟩ Ψ Θ Γ t A := by
  refine ExprTy.rec (motive_1 := fun Ψ Θ Γ t A _ => ExprTy ⟨sig, Ξ, ok₂⟩ Ψ Θ Γ t A)
    (motive_2 := fun Ψ Θ Γ cl A _ => ClauseTy ⟨sig, Ξ, ok₂⟩ Ψ Θ Γ cl A)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  · intro Ψ Θ Γ x A hx; exact .var hx
  · intro Ψ Θ Γ; exact .unit Ψ Θ Γ
  · intro Ψ Θ Γ t u A B _ _ ih₁ ih₂; exact .pair ih₁ ih₂
  · intro Ψ Θ Γ c t a b S Sc hc hb hwf _ ih; exact .cons hc hb hwf ih
  · intro Ψ Θ Γ r s A B _ _ ih₁ ih₂; exact .app ih₁ ih₂
  · intro Ψ Θ Γ r a b R d Rd _ hd hb ih; exact .proj ih hd hb
  · intro Ψ Θ Γ r κ B T _ hT ih; exact .instT ih hT
  · intro Ψ Θ Γ r a b B _ hb ih; exact .instS ih hb
  · intro Ψ Θ Γ t κ B T hwf hT _ ih; exact .packT hwf hT ih
  · intro Ψ Θ Γ t a b B hwf hb _ ih; exact .packS hwf hb ih
  · intro Ψ Θ Γ D A hA _ ih; exact .lam hA ih
  · intro Ψ Θ Γ g as hg hwf hcl hsub hT; exact .globalFun hg hwf hcl hsub hT
  · intro Ψ Θ Γ g as hg hwf hcl hsub hT hloc
    exact .localFun hg hwf hcl hsub hT (hok Ψ g as hg hloc)
  · intro Ψ Θ Γ t A B _ hAB hB ih; exact .sub ih hAB hB
  · intro Ψ Ψ' Θ Θ' Γ Γ' qs t A C hsp _ ih; exact .mk hsp ih

theorem clauseTy_mono_local {sig Ξ : List FunDecl}
    {ok₁ ok₂ : SizeCtx → FunName → List Size → Prop}
    (hok : ∀ Ψ (g : FunDecl) as, g ∈ Ξ → ok₁ Ψ g.name as → ok₂ Ψ g.name as)
    {Ψ : SizeCtx} {Θ : TyCtx} {Γ : TermCtx} {cl : Clause} {A : Ty}
    (h : ClauseTy ⟨sig, Ξ, ok₁⟩ Ψ Θ Γ cl A) : ClauseTy ⟨sig, Ξ, ok₂⟩ Ψ Θ Γ cl A := by
  cases h with
  | mk hsp ht => exact .mk hsp (exprTy_mono_local hok ht)

/-! ## Lexicographic calls conform to the lexicographic graphs -/

theorem idxOf?_getElem? {m : List Nat} {x pos : Nat} (h : m.idxOf? x = some pos) :
    m[pos]? = some x := by
  obtain ⟨hlt, heq, _⟩ := List.idxOf?_eq_some_iff.mp h
  rw [List.getElem?_eq_getElem hlt, heq]

theorem getElem?_idxOf? {m : List Nat} (hnd : m.Nodup) {x pos : Nat} (h : m[pos]? = some x) :
    m.idxOf? x = some pos := by
  obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp h
  apply List.idxOf?_eq_some_iff.mpr
  refine ⟨hlt, heq, ?_⟩
  intro j hj he
  have hjlen : j < m.length := by omega
  have : j = pos := (List.getElem_inj (h₀ := hjlen) (h₁ := hlt) hnd).mp (he.trans heq.symm)
  omega

theorem lex_to_sct {Ξ : List FunDecl} {n : Nat} {m : List Nat} (hnd : m.Nodup)
    (hbound : ∀ i ∈ m, i < n) {d : FunDecl} (hd : d ∈ Ξ) (hdn : d.sizeParams.length = n) :
    ∀ Ψ (g : FunDecl) as, g ∈ Ξ → lexCallOK m d.sizeParams Ψ g.name as →
      sctCallOK (lexInvGraphFamily (Ξ.map FunDecl.name) n m) d.name d.sizeParams Ψ g.name as := by
  intro Ψ g as hg ⟨hlen, k, hk, hpre, i, hmi, hi, hj, hlt⟩
  refine ⟨lexInvGraph m n k, ?_, ?_⟩
  · simp only [lexInvGraphFamily]
    rw [if_pos ⟨List.mem_map_of_mem hd, List.mem_map_of_mem hg⟩]
    exact List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩
  · refine ⟨by simp [lexInvGraph, hlen, hdn], by simp [lexInvGraph, hdn], ?_⟩
    intro i' j' hi' hj'
    have hi'n : i' < n := by rw [← hdn, ← hlen]; exact hi'
    have hj'n : j' < n := by simpa [hdn] using hj'
    rw [NishtAbel2024V2.LexGraphBase.lex_lookup m n k i' j' hi'n hj'n]
    by_cases hij : i' = j'
    · subst hij
      simp only [beq_self_eq_true, if_true]
      cases hpos : m.idxOf? i' with
      | none => simp
      | some pos =>
        simp only
        have hmpos := idxOf?_getElem? hpos
        refine ⟨fun hcase => ?_, fun hcase => ?_⟩
        · have hposk : pos = k := by
            by_contra hne
            by_cases hlt' : pos < k
            · simp [hlt'] at hcase
            · simp [hlt', hne] at hcase
          subst hposk
          rw [hmi] at hmpos
          injection hmpos with hii
          subst hii
          simpa [List.get_eq_getElem] using hlt
        · have hposk : pos < k := by
            by_contra hnlt
            by_cases heq : pos = k
            · simp [heq] at hcase
            · simp [hnlt, heq] at hcase
          obtain ⟨hi₂, hj₂, hle⟩ := hpre pos hposk i' hmpos
          simpa [List.get_eq_getElem] using hle
    · have : (i' == j') = false := by simpa using hij
      simp [this]

/-! ## Theorem 6 -/

theorem theorem_6_proof {sig Ξ : List FunDecl} (h : LexBlockTy sig Ξ) : BlockTy sig Ξ := by
  obtain ⟨n, m, hnd, hbound, harity, hdecl⟩ := h
  refine ⟨lexInvGraphFamily (Ξ.map FunDecl.name) n m,
    NishtAbel2024V2.LexicographicEmbedding.lex_family_sct _ n m hnd hbound,
    fun d hd => (harity d hd).symm, ?_⟩
  intro d hd
  obtain ⟨hwf, hty, hcls⟩ := hdecl d hd
  exact ⟨hwf, hty, fun cl hcl =>
    clauseTy_mono_local (lex_to_sct hnd hbound hd (harity d hd)) (hcls cl hcl)⟩

end NishtAbel2024V5

/-! ## Solutions/V5/FinalCore.lean -/

/-! # V5: the semantic core with Ramsey's theorem discharged -/

namespace NishtAbel2024V5

theorem ramseyPairs : RamseyPairs := by
  intro C _ color
  obtain ⟨M, b, _, hInf, hcolor⟩ :=
    NishtAbel2024V3.RamseyPort.SeparableQuotient.InfiniteRamsey.homogeneous_subset_oai 2 color
      Set.univ Set.infinite_univ
  exact ⟨M, b, hInf, hcolor⟩

theorem theorem_4_core (W sig Ξ : List FunDecl) (hW : ∀ d ∈ sig ++ Ξ, d ∈ W)
    (hnames : (W.map FunDecl.name).Nodup) (hclosed : ∀ d ∈ W, (Tm.lam d.clauses).Closed)
    (htyped : BlockTy sig Ξ) (hsig : SemValid W sig) : SemValid W Ξ :=
  theorem_4_proof ramseyPairs W sig Ξ hW hnames hclosed htyped hsig

theorem theorem_5_core (blocks : List (List FunDecl)) (main : Tm) (A : Ty)
    (htyped : ProgramTy blocks main A) : SN blocks.flatten main :=
  theorem_5_proof ramseyPairs blocks main A htyped

end NishtAbel2024V5


