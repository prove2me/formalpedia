-- Prove2me | Definitions.Def_NishtAbel2024V5_SemBasic
-- name    : NishtAbel2024V5_SemBasic
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-07T04:20:41.890134+00:00
-- url     : https://prove2.me/theorems/306cb731-bae7-4f0e-858e-66749aedae19
-- title:
--   Chapter 5.1 & 5.3 (V5 Support): Spines, Reducibility Candidates, Ordinal Fixpoint Stabilization, and Size Soundness
-- statement:
--   Foundational operational and semantic infrastructure for System $F_\omega^{\mathsf{cop,SCT}}$ (Chapter 5, Sections 5.1 and 5.3 of Nisht and Abel 2024): evaluation spine decomposition, determinism of first-match clause head reduction, Girard reducibility candidates (`IsCand`), cardinality-based stabilization of transfinite inductive and coinductive stages at $\Omega = (\mathsf{succ}\,\#\mathsf{Tm}).\mathsf{ord}$, higher-kinded candidate lattice properties (`Good`, `SemLe`), and the proof of Theorem 2 for size judgments (`sizeWf_sound`, `sizeLe_sound2`, `sizeLt_sound2`).
-- source:
--   Nisht & Abel 2024, Kind Inference and Termination Checking in a Language with Co-Patterns and Size-Change Termination, https://urn.kb.se/resolve?urn=urn:nbn:se:chalmers:diva-542843, Chapter 5, Sections 5.1 & 5.3, pp. 31-36

import Definitions.Def_NishtAbel2024V5_Semantics
import Mathlib.SetTheory.Ordinal.FixedPointApproximants

/-! ## Solutions/V5/Basic.lean -/

/-! # V5 basics: spines, matching, determinism of head steps -/

namespace NishtAbel2024V5

namespace Tm

@[simp] theorem appSpine_nil (r : Tm) : appSpine r [] = r := rfl

@[simp] theorem appSpine_cons (r : Tm) (e : Elim) (es : List Elim) :
    appSpine r (e :: es) = appSpine (.app r e) es := rfl

theorem appSpine_append (r : Tm) (es es' : List Elim) :
    appSpine r (es ++ es') = appSpine (appSpine r es) es' := by
  simp [appSpine, List.foldl_append]

@[simp] theorem appSpine_snoc (r : Tm) (es : List Elim) (e : Elim) :
    appSpine r (es ++ [e]) = .app (appSpine r es) e := by
  rw [appSpine_append]; rfl

theorem headSpine_appSpine (r : Tm) (es : List Elim) :
    (appSpine r es).headSpine = (r.headSpine.1, r.headSpine.2 ++ es) := by
  induction es generalizing r with
  | nil => simp
  | cons e es ih =>
    rw [appSpine_cons, ih]
    simp [headSpine]

end Tm

/-! ## Matching -/

theorem MatchRes.and_eq_yes {m₁ m₂ : MatchRes} {σ : TmSubst} (h : m₁.and m₂ = .yes σ) :
    ∃ σ₁ σ₂, m₁ = .yes σ₁ ∧ m₂ = .yes σ₂ ∧ σ = σ₁ ++ σ₂ := by
  cases m₁ <;> cases m₂ <;> simp_all [MatchRes.and]

theorem MatchRes.and_no_left (m : MatchRes) : MatchRes.and .no m = .no := by
  cases m <;> rfl

theorem MatchRes.and_no_right (m : MatchRes) : m.and .no = .no := by
  cases m <;> rfl

theorem matchSpine_yes_length {qs : List Copat} {es : List Elim} {σ : TmSubst}
    (h : matchSpine qs es = .yes σ) : qs.length ≤ es.length := by
  induction qs generalizing es σ with
  | nil => simp
  | cons q qs ih =>
    cases es with
    | nil => simp [matchSpine] at h
    | cons e es =>
      obtain ⟨_, σ₂, _, h₂, _⟩ := MatchRes.and_eq_yes h
      simpa using ih h₂

theorem matchSpine_append_yes {qs : List Copat} {es : List Elim} {σ : TmSubst}
    (h : matchSpine qs es = .yes σ) (es' : List Elim) :
    matchSpine qs (es ++ es') = .yes σ := by
  induction qs generalizing es σ with
  | nil => simpa [matchSpine] using h
  | cons q qs ih =>
    cases es with
    | nil => simp [matchSpine] at h
    | cons e es =>
      simp only [matchSpine, List.cons_append] at h ⊢
      obtain ⟨σ₁, σ₂, h₁, h₂, rfl⟩ := MatchRes.and_eq_yes h
      rw [h₁, ih h₂]
      rfl

theorem matchSpine_append_no {qs : List Copat} {es : List Elim}
    (h : matchSpine qs es = .no) (es' : List Elim) :
    matchSpine qs (es ++ es') = .no := by
  induction qs generalizing es with
  | nil => simp [matchSpine] at h
  | cons q qs ih =>
    cases es with
    | nil => simp [matchSpine] at h
    | cons e es =>
      simp only [matchSpine, List.cons_append] at h ⊢
      cases hq : matchCopat q e with
      | no => rfl
      | yes σ =>
        rw [hq] at h
        cases hm : matchSpine qs es with
        | no => rw [ih hm]; rfl
        | yes _ => rw [hm] at h; simp [MatchRes.and] at h
        | stuck => rw [hm] at h; simp [MatchRes.and] at h
      | stuck =>
        rw [hq] at h
        cases hm : matchSpine qs es with
        | no => rw [ih hm]; rfl
        | yes _ => rw [hm] at h; simp [MatchRes.and] at h
        | stuck => rw [hm] at h; simp [MatchRes.and] at h

theorem selectClause_append {D : List Clause} {es : List Elim} {u : Tm}
    (h : selectClause D es = some u) (es' : List Elim) :
    selectClause D (es ++ es') = some (Tm.appSpine u es') := by
  induction D with
  | nil => simp [selectClause] at h
  | cons cl D ih =>
    obtain ⟨qs, t⟩ := cl
    simp only [selectClause] at h ⊢
    cases hm : matchSpine qs es with
    | yes σ =>
      rw [hm] at h
      simp only [Option.some.injEq] at h
      subst h
      rw [matchSpine_append_yes hm]
      simp only [Option.some.injEq]
      rw [List.drop_append_of_le_length (matchSpine_yes_length hm), Tm.appSpine_append]
    | no =>
      rw [hm] at h
      rw [matchSpine_append_no hm]
      exact ih h
    | stuck => rw [hm] at h; simp at h

/-! ## Head steps -/

theorem headStep_appSpine {W : World} {t u : Tm} (h : headStep W t = some u) (es : List Elim) :
    headStep W (Tm.appSpine t es) = some (Tm.appSpine u es) := by
  unfold headStep at h ⊢
  rw [Tm.headSpine_appSpine]
  generalize t.headSpine = p at h ⊢
  obtain ⟨hd, sp⟩ := p
  simp only at h ⊢
  cases hd with
  | lam D => exact selectClause_append h es
  | fn f =>
    cases hl : W.lookup f with
    | none => simp [hl] at h
    | some d =>
      simp only [hl] at h ⊢
      exact selectClause_append h es
  | _ => simp at h

theorem headStep_intro {W : World} {t : Tm} (h : IsIntro t) : headStep W t = none := by
  cases t <;> simp_all [IsIntro, headStep, Tm.headSpine]

theorem not_intro_of_headStep {W : World} {t u : Tm} (h : headStep W t = some u) : ¬ IsIntro t := by
  intro hi
  rw [headStep_intro hi] at h
  cases h

/-- A term with a head step is neutral. -/
theorem neutral_of_headStep {W : World} {t u : Tm} (h : headStep W t = some u) :
    IsNeutral W t := by
  refine ⟨not_intro_of_headStep h, ?_⟩
  intro es u' h'
  refine ⟨u, h, ?_⟩
  rw [headStep_appSpine h es] at h'
  cases h'
  rfl

/-- A term none of whose extensions has a head step is neutral. -/
theorem neutral_of_stuck {W : World} {t : Tm} (hi : ¬ IsIntro t)
    (h : ∀ es, headStep W (Tm.appSpine t es) = none) : IsNeutral W t := by
  refine ⟨hi, ?_⟩
  intro es u hu
  rw [h es] at hu
  cases hu

/-- Neutrality is preserved by adding eliminations. -/
theorem neutral_app {W : World} {t : Tm} (h : IsNeutral W t) (e : Elim) :
    IsNeutral W (.app t e) := by
  refine ⟨by simp [IsIntro], ?_⟩
  intro es u hu
  have hu' : headStep W (Tm.appSpine t (e :: es)) = some u := hu
  obtain ⟨t', ht', rfl⟩ := h.2 _ _ hu'
  refine ⟨.app t' e, ?_, rfl⟩
  have := headStep_appSpine ht' [e]
  simpa using this

end NishtAbel2024V5

/-! ## Solutions/V5/Closed.lean -/

/-! # V5: free variables, closed substitution, closedness of reducts -/

namespace NishtAbel2024V5

/-! ## Association-list lookups -/

theorem lookup_cons_eq (k x : Nat) (b : Tm) (l : TmSubst) :
    ((k, b) :: l).lookup x = if x = k then some b else l.lookup x := by
  rw [List.lookup_cons]
  by_cases h : x = k
  · subst h; simp
  · have hb : (x == k) = false := beq_eq_false_iff_ne.mpr h
    simp [hb, h]

theorem lookup_filter_not_mem (σ : TmSubst) (L : List Nat) (x : Nat) :
    (σ.filter (fun p => decide (p.1 ∉ L))).lookup x = if x ∈ L then none else σ.lookup x := by
  induction σ with
  | nil => simp
  | cons p σ ih =>
    obtain ⟨y, v⟩ := p
    by_cases hy : y ∈ L
    · rw [List.filter_cons_of_neg (by simpa using hy), ih, lookup_cons_eq]
      by_cases hx : x ∈ L
      · simp [hx]
      · have : x ≠ y := fun h => hx (h ▸ hy)
        simp [hx, this]
    · rw [List.filter_cons_of_pos (by simpa using hy), lookup_cons_eq, lookup_cons_eq, ih]
      by_cases hx : x ∈ L
      · have : x ≠ y := fun h => hy (h ▸ hx)
        simp [hx, this]
      · simp [hx]

theorem lookup_isSome_of_mem {σ : TmSubst} {x : Nat} (h : x ∈ σ.map Prod.fst) :
    ∃ v, σ.lookup x = some v := by
  induction σ with
  | nil => simp at h
  | cons p σ ih =>
    obtain ⟨y, v⟩ := p
    rw [lookup_cons_eq]
    by_cases hx : x = y
    · exact ⟨v, by simp [hx]⟩
    · simp only [List.map_cons, List.mem_cons] at h
      rcases h with h | h
      · exact absurd h hx
      · simpa [hx] using ih h

theorem lookup_mem {σ : TmSubst} {x : Nat} {v : Tm} (h : σ.lookup x = some v) : (x, v) ∈ σ := by
  induction σ with
  | nil => simp at h
  | cons p σ ih =>
    obtain ⟨y, w⟩ := p
    rw [lookup_cons_eq] at h
    by_cases hx : x = y
    · simp [hx] at h; subst hx; subst h; simp
    · simp [hx] at h; exact List.mem_cons_of_mem _ (ih h)

/-! ## Substitution -/

mutual

theorem Tm.subst_congr {σ σ' : TmSubst} (h : ∀ x, σ.lookup x = σ'.lookup x) :
    ∀ t : Tm, t.subst σ = t.subst σ'
  | .var x => by simp only [Tm.subst, h x]
  | .fn _ => rfl
  | .app r e => by simp only [Tm.subst]; rw [Tm.subst_congr h r, Elim.subst_congr h e]
  | .unit => rfl
  | .pair t u => by simp only [Tm.subst]; rw [Tm.subst_congr h t, Tm.subst_congr h u]
  | .cons c t => by simp only [Tm.subst]; rw [Tm.subst_congr h t]
  | .pack t => by simp only [Tm.subst]; rw [Tm.subst_congr h t]
  | .lam D => by simp only [Tm.subst]; rw [Clause.substList_congr h D]

theorem Elim.subst_congr {σ σ' : TmSubst} (h : ∀ x, σ.lookup x = σ'.lookup x) :
    ∀ e : Elim, e.subst σ = e.subst σ'
  | .term t => by simp only [Elim.subst]; rw [Tm.subst_congr h t]
  | .proj _ => rfl
  | .inst => rfl

theorem Clause.substList_congr {σ σ' : TmSubst} (h : ∀ x, σ.lookup x = σ'.lookup x) :
    ∀ D : List Clause, Clause.substList σ D = Clause.substList σ' D
  | [] => rfl
  | .mk qs t :: D => by
    simp only [Clause.substList]
    rw [Tm.subst_congr (σ := σ.filter (fun p => decide (p.1 ∉ spineVars qs)))
        (σ' := σ'.filter (fun p => decide (p.1 ∉ spineVars qs)))
        (fun x => by simp only [lookup_filter_not_mem, h x]) t,
      Clause.substList_congr h D]

end

mutual

theorem Tm.subst_of_fv {σ : TmSubst} :
    ∀ t : Tm, (∀ x ∈ t.fv, σ.lookup x = none) → t.subst σ = t
  | .var x, h => by simp [Tm.subst, h x (by simp [Tm.fv])]
  | .fn _, _ => rfl
  | .app r e, h => by
    simp only [Tm.subst]
    rw [Tm.subst_of_fv r (fun x hx => h x (by simp [Tm.fv, hx])),
      Elim.subst_of_fv e (fun x hx => h x (by simp [Tm.fv, hx]))]
  | .unit, _ => rfl
  | .pair t u, h => by
    simp only [Tm.subst]
    rw [Tm.subst_of_fv t (fun x hx => h x (by simp [Tm.fv, hx])),
      Tm.subst_of_fv u (fun x hx => h x (by simp [Tm.fv, hx]))]
  | .cons c t, h => by
    simp only [Tm.subst]
    rw [Tm.subst_of_fv t (fun x hx => h x (by simp [Tm.fv, hx]))]
  | .pack t, h => by
    simp only [Tm.subst]
    rw [Tm.subst_of_fv t (fun x hx => h x (by simp [Tm.fv, hx]))]
  | .lam D, h => by
    simp only [Tm.subst]
    rw [Clause.substList_of_fv D (fun x hx => h x (by simpa [Tm.fv] using hx))]

theorem Elim.subst_of_fv {σ : TmSubst} :
    ∀ e : Elim, (∀ x ∈ e.fv, σ.lookup x = none) → e.subst σ = e
  | .term t, h => by simp only [Elim.subst]; rw [Tm.subst_of_fv t (fun x hx => h x hx)]
  | .proj _, _ => rfl
  | .inst, _ => rfl

theorem Clause.substList_of_fv {σ : TmSubst} :
    ∀ D : List Clause, (∀ x ∈ Clause.fvList D, σ.lookup x = none) → Clause.substList σ D = D
  | [], _ => rfl
  | .mk qs t :: D, h => by
    simp only [Clause.substList]
    rw [Tm.subst_of_fv t (fun x hx => by
        rw [lookup_filter_not_mem]
        by_cases hm : x ∈ spineVars qs
        · simp [hm]
        · simp only [hm, if_false]
          exact h x (by simp [Clause.fvList, hx, hm])),
      Clause.substList_of_fv D (fun x hx => h x (by simp [Clause.fvList, hx]))]

end

theorem Tm.subst_closed {t : Tm} (h : t.Closed) (σ : TmSubst) : t.subst σ = t :=
  Tm.subst_of_fv t (fun x hx => by simp [Tm.Closed] at h; simp [h] at hx)

/-! Composition, when the first substitution has closed values. -/

mutual

theorem Tm.subst_subst {σ₁ σ₂ : TmSubst} (hc : ∀ x v, σ₁.lookup x = some v → v.Closed) :
    ∀ t : Tm, (t.subst σ₁).subst σ₂ = t.subst (σ₁ ++ σ₂)
  | .var x => by
    cases h : σ₁.lookup x with
    | none => simp [Tm.subst, h, List.lookup_append]
    | some v => simp [Tm.subst, h, List.lookup_append, Tm.subst_closed (hc x v h)]
  | .fn _ => rfl
  | .app r e => by simp only [Tm.subst]; rw [Tm.subst_subst hc r, Elim.subst_subst hc e]
  | .unit => rfl
  | .pair t u => by simp only [Tm.subst]; rw [Tm.subst_subst hc t, Tm.subst_subst hc u]
  | .cons c t => by simp only [Tm.subst]; rw [Tm.subst_subst hc t]
  | .pack t => by simp only [Tm.subst]; rw [Tm.subst_subst hc t]
  | .lam D => by simp only [Tm.subst]; rw [Clause.substList_subst hc D]

theorem Elim.subst_subst {σ₁ σ₂ : TmSubst} (hc : ∀ x v, σ₁.lookup x = some v → v.Closed) :
    ∀ e : Elim, (e.subst σ₁).subst σ₂ = e.subst (σ₁ ++ σ₂)
  | .term t => by simp only [Elim.subst]; rw [Tm.subst_subst hc t]
  | .proj _ => rfl
  | .inst => rfl

theorem Clause.substList_subst {σ₁ σ₂ : TmSubst} (hc : ∀ x v, σ₁.lookup x = some v → v.Closed) :
    ∀ D : List Clause, Clause.substList σ₂ (Clause.substList σ₁ D) = Clause.substList (σ₁ ++ σ₂) D
  | [] => rfl
  | .mk qs t :: D => by
    simp only [Clause.substList]
    have hc' : ∀ x v, (σ₁.filter (fun p => decide (p.1 ∉ spineVars qs))).lookup x = some v →
        v.Closed := by
      intro x v h
      rw [lookup_filter_not_mem] at h
      by_cases hm : x ∈ spineVars qs
      · simp [hm] at h
      · simp only [hm, if_false] at h; exact hc x v h
    rw [Tm.subst_subst hc' t, List.filter_append, Clause.substList_subst hc D]

end

/-! ## Free variables of substitutions -/

mutual

theorem Tm.fv_subst {σ : TmSubst} (hc : ∀ x v, σ.lookup x = some v → v.Closed) :
    ∀ t : Tm, ∀ x ∈ (t.subst σ).fv, x ∈ t.fv ∧ σ.lookup x = none
  | .var y, x, hx => by
    cases h : σ.lookup y with
    | none =>
      simp [Tm.subst, h, Tm.fv] at hx
      subst hx; exact ⟨by simp [Tm.fv], h⟩
    | some v =>
      have hv := hc y v h
      simp [Tm.Closed] at hv
      simp [Tm.subst, h, hv] at hx
  | .fn _, x, hx => by simp [Tm.subst, Tm.fv] at hx
  | .app r e, x, hx => by
    simp only [Tm.subst, Tm.fv, List.mem_append] at hx
    rcases hx with hx | hx
    · obtain ⟨h1, h2⟩ := Tm.fv_subst hc r x hx; exact ⟨by simp [Tm.fv, h1], h2⟩
    · obtain ⟨h1, h2⟩ := Elim.fv_subst hc e x hx; exact ⟨by simp [Tm.fv, h1], h2⟩
  | .unit, x, hx => by simp [Tm.subst, Tm.fv] at hx
  | .pair t u, x, hx => by
    simp only [Tm.subst, Tm.fv, List.mem_append] at hx
    rcases hx with hx | hx
    · obtain ⟨h1, h2⟩ := Tm.fv_subst hc t x hx; exact ⟨by simp [Tm.fv, h1], h2⟩
    · obtain ⟨h1, h2⟩ := Tm.fv_subst hc u x hx; exact ⟨by simp [Tm.fv, h1], h2⟩
  | .cons c t, x, hx => by
    simp only [Tm.subst, Tm.fv] at hx
    obtain ⟨h1, h2⟩ := Tm.fv_subst hc t x hx; exact ⟨by simp [Tm.fv, h1], h2⟩
  | .pack t, x, hx => by
    simp only [Tm.subst, Tm.fv] at hx
    obtain ⟨h1, h2⟩ := Tm.fv_subst hc t x hx; exact ⟨by simp [Tm.fv, h1], h2⟩
  | .lam D, x, hx => by
    simp only [Tm.subst, Tm.fv] at hx ⊢
    exact Clause.fvList_subst hc D x hx

theorem Elim.fv_subst {σ : TmSubst} (hc : ∀ x v, σ.lookup x = some v → v.Closed) :
    ∀ e : Elim, ∀ x ∈ (e.subst σ).fv, x ∈ e.fv ∧ σ.lookup x = none
  | .term t, x, hx => Tm.fv_subst hc t x hx
  | .proj _, x, hx => by simp [Elim.subst, Elim.fv] at hx
  | .inst, x, hx => by simp [Elim.subst, Elim.fv] at hx

theorem Clause.fvList_subst {σ : TmSubst} (hc : ∀ x v, σ.lookup x = some v → v.Closed) :
    ∀ D : List Clause, ∀ x ∈ Clause.fvList (Clause.substList σ D),
      x ∈ Clause.fvList D ∧ σ.lookup x = none
  | [], x, hx => by simp [Clause.substList, Clause.fvList] at hx
  | .mk qs t :: D, x, hx => by
    simp only [Clause.substList, Clause.fvList, List.mem_append, List.mem_filter,
      decide_eq_true_eq] at hx
    rcases hx with ⟨hx, hm⟩ | hx
    · have hc' : ∀ x v, (σ.filter (fun p => decide (p.1 ∉ spineVars qs))).lookup x = some v →
          v.Closed := by
        intro x v h
        rw [lookup_filter_not_mem] at h
        by_cases hm : x ∈ spineVars qs
        · simp [hm] at h
        · simp only [hm, if_false] at h; exact hc x v h
      obtain ⟨h1, h2⟩ := Tm.fv_subst hc' t x hx
      rw [lookup_filter_not_mem] at h2
      simp only [hm, if_false] at h2
      exact ⟨by simp [Clause.fvList, h1, hm], h2⟩
    · obtain ⟨h1, h2⟩ := Clause.fvList_subst hc D x hx
      exact ⟨by simp [Clause.fvList, h1], h2⟩

end

/-- Substituting closed values for all free variables gives a closed term. -/
theorem Tm.closed_subst {σ : TmSubst} {t : Tm} (hc : ∀ x v, σ.lookup x = some v → v.Closed)
    (hcov : ∀ x ∈ t.fv, ∃ v, σ.lookup x = some v) : (t.subst σ).Closed := by
  unfold Tm.Closed
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro x hx
  obtain ⟨h1, h2⟩ := Tm.fv_subst hc t x hx
  obtain ⟨v, hv⟩ := hcov x h1
  rw [hv] at h2; cases h2

end NishtAbel2024V5

/-! ## Solutions/V5/Reduct.lean -/

/-! # V5: matching facts and closedness of reducts -/

namespace NishtAbel2024V5

open NishtAbel2024V2 (FunName)

theorem Tm.fv_appSpine (r : Tm) (es : List Elim) :
    (Tm.appSpine r es).fv = r.fv ++ es.flatMap Elim.fv := by
  induction es generalizing r with
  | nil => simp
  | cons e es ih => simp [ih, Tm.fv, List.append_assoc]

theorem Tm.appSpine_headSpine : ∀ t : Tm, Tm.appSpine t.headSpine.1 t.headSpine.2 = t
  | .app r e => by
    simp only [Tm.headSpine]
    rw [Tm.appSpine_snoc, Tm.appSpine_headSpine r]
  | .var _ => rfl
  | .fn _ => rfl
  | .unit => rfl
  | .pair _ _ => rfl
  | .cons _ _ => rfl
  | .pack _ => rfl
  | .lam _ => rfl

/-- Facts about a successful match: its domain, and free variables of its values. -/
def MatchFacts (σ : TmSubst) (vars : List Nat) (fvs : List Nat) : Prop :=
  σ.map Prod.fst = vars ∧ ∀ q ∈ σ, ∀ x ∈ q.2.fv, x ∈ fvs

theorem MatchFacts.append {σ₁ σ₂ : TmSubst} {v₁ v₂ f₁ f₂ : List Nat}
    (h₁ : MatchFacts σ₁ v₁ f₁) (h₂ : MatchFacts σ₂ v₂ f₂) :
    MatchFacts (σ₁ ++ σ₂) (v₁ ++ v₂) (f₁ ++ f₂) := by
  refine ⟨by simp [h₁.1, h₂.1], ?_⟩
  intro q hq x hx
  rcases List.mem_append.mp hq with hq | hq
  · exact List.mem_append_left _ (h₁.2 q hq x hx)
  · exact List.mem_append_right _ (h₂.2 q hq x hx)

theorem matchPat_facts : ∀ (p : Pat) (v : Tm) (σ : TmSubst),
    matchPat p v = .yes σ → MatchFacts σ p.vars v.fv
  | .var x, v, σ, h => by
    simp [matchPat] at h; subst h
    exact ⟨by simp [Pat.vars], by simp⟩
  | .unit, v, σ, h => by
    cases v <;> simp [matchPat] at h
    subst h; exact ⟨by simp [Pat.vars], by simp⟩
  | .pair p q, v, σ, h => by
    cases v <;> simp [matchPat] at h
    rename_i t u
    obtain ⟨σ₁, σ₂, h₁, h₂, rfl⟩ := MatchRes.and_eq_yes h
    have := (matchPat_facts p t σ₁ h₁).append (matchPat_facts q u σ₂ h₂)
    simpa [Pat.vars, Tm.fv] using this
  | .cons c p, v, σ, h => by
    cases v <;> simp [matchPat] at h
    rename_i c' t
    by_cases hc : c = c'
    · simp [hc] at h
      have := matchPat_facts p t σ h
      simpa [Pat.vars, Tm.fv] using this
    · simp [hc] at h
  | .pack p, v, σ, h => by
    cases v <;> simp [matchPat] at h
    rename_i t
    have := matchPat_facts p t σ h
    simpa [Pat.vars, Tm.fv] using this

theorem matchCopat_facts : ∀ (q : Copat) (e : Elim) (σ : TmSubst),
    matchCopat q e = .yes σ → MatchFacts σ q.vars e.fv
  | .pat p, .term t, σ, h => by
    simpa [Copat.vars, Elim.fv] using matchPat_facts p t σ h
  | .pat _, .proj _, σ, h => by simp [matchCopat] at h
  | .proj d, .proj d', σ, h => by
    by_cases hd : d = d'
    · simp [matchCopat, hd] at h; subst h; exact ⟨by simp [Copat.vars], by simp⟩
    · simp [matchCopat, hd] at h
  | .proj _, .term _, σ, h => by simp [matchCopat] at h
  | .pat _, .inst, σ, h => by simp [matchCopat] at h
  | .proj _, .inst, σ, h => by simp [matchCopat] at h
  | .inst, .inst, σ, h => by
    simp [matchCopat] at h; subst h; exact ⟨by simp [Copat.vars], by simp⟩
  | .inst, .term _, σ, h => by simp [matchCopat] at h
  | .inst, .proj _, σ, h => by simp [matchCopat] at h

theorem matchSpine_facts : ∀ (qs : List Copat) (es : List Elim) (σ : TmSubst),
    matchSpine qs es = .yes σ → MatchFacts σ (spineVars qs) (es.flatMap Elim.fv)
  | [], es, σ, h => by
    simp [matchSpine] at h; subst h; exact ⟨by simp [spineVars], by simp⟩
  | _ :: _, [], σ, h => by simp [matchSpine] at h
  | q :: qs, e :: es, σ, h => by
    simp only [matchSpine] at h
    obtain ⟨σ₁, σ₂, h₁, h₂, rfl⟩ := MatchRes.and_eq_yes h
    have := (matchCopat_facts q e σ₁ h₁).append (matchSpine_facts qs es σ₂ h₂)
    simpa [spineVars] using this

/-- Elimination spines with no free variables. -/
def ElimsClosed (es : List Elim) : Prop := es.flatMap Elim.fv = []

theorem selectClause_closed {D : List Clause} {es : List Elim} {u : Tm}
    (hD : Clause.fvList D = []) (hes : ElimsClosed es) (h : selectClause D es = some u) :
    u.Closed := by
  induction D with
  | nil => simp [selectClause] at h
  | cons cl D ih =>
    obtain ⟨qs, t⟩ := cl
    simp only [Clause.fvList, List.append_eq_nil_iff] at hD
    simp only [selectClause] at h
    cases hm : matchSpine qs es with
    | yes σ =>
      rw [hm] at h
      simp only [Option.some.injEq] at h
      subst h
      obtain ⟨hdom, hfv⟩ := matchSpine_facts qs es σ hm
      have hc : ∀ x v, σ.lookup x = some v → v.Closed := by
        intro x v hx
        have hmem := lookup_mem hx
        unfold Tm.Closed
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro y hy
        have := hfv _ hmem y hy
        simp only [ElimsClosed, List.flatMap_eq_nil_iff] at hes
        simp only [List.mem_flatMap] at this
        obtain ⟨a, ha, hya⟩ := this
        rw [hes a ha] at hya
        simp at hya
      have hbody : (t.subst σ).Closed := by
        apply Tm.closed_subst hc
        intro x hx
        apply lookup_isSome_of_mem
        rw [hdom]
        by_contra hn
        have : x ∈ t.fv.filter (fun x => decide (x ∉ spineVars qs)) := by simp [hx, hn]
        rw [hD.1] at this; simp at this
      unfold Tm.Closed
      rw [Tm.fv_appSpine, hbody]
      simp only [List.nil_append]
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro x hx
      simp only [List.mem_flatMap] at hx
      obtain ⟨e, he, hxe⟩ := hx
      have : x ∈ es.flatMap Elim.fv := List.mem_flatMap.mpr ⟨e, List.mem_of_mem_drop he, hxe⟩
      rw [hes] at this; simp at this
    | no => rw [hm] at h; exact ih hD.2 h
    | stuck => rw [hm] at h; simp at h

/-- Clause bodies of all declarations are closed. -/
def WorldClosed (W : World) : Prop := ∀ d ∈ W, (Tm.lam d.clauses).Closed

theorem World.lookup_mem {W : World} {f : FunName} {d : FunDecl} (h : W.lookup f = some d) :
    d ∈ W := List.mem_of_find?_eq_some h

theorem headStep_closed {W : World} (hW : WorldClosed W) {t u : Tm} (ht : t.Closed)
    (h : headStep W t = some u) : u.Closed := by
  have hsplit := Tm.appSpine_headSpine t
  have hfv : t.fv = t.headSpine.1.fv ++ t.headSpine.2.flatMap Elim.fv := by
    conv_lhs => rw [← hsplit]
    rw [Tm.fv_appSpine]
  have hall : t.headSpine.1.fv ++ t.headSpine.2.flatMap Elim.fv = [] := by
    rw [← hfv]; exact ht
  rw [List.append_eq_nil_iff] at hall
  unfold headStep at h
  generalize hp : t.headSpine = p at h hall
  obtain ⟨hd, sp⟩ := p
  simp only at h hall
  cases hd with
  | lam D =>
    exact selectClause_closed (by simpa [Tm.fv] using hall.1) hall.2 h
  | fn f =>
    cases hl : W.lookup f with
    | none => simp [hl] at h
    | some d =>
      simp only [hl] at h
      have := hW d (World.lookup_mem hl)
      exact selectClause_closed (by simpa [Tm.Closed, Tm.fv] using this) hall.2 h
  | _ => simp at h

theorem step_closed {W : World} (hW : WorldClosed W) {t u : Tm} (h : Step W t u) (ht : t.Closed) :
    u.Closed := by
  induction h with
  | head hs => exact headStep_closed hW ht hs
  | appFun _ ih =>
    simp [Tm.Closed, Tm.fv] at ht ⊢
    exact ⟨ih ht.1, ht.2⟩
  | appArg _ ih =>
    simp [Tm.Closed, Tm.fv, Elim.fv] at ht ⊢
    exact ⟨ht.1, ih ht.2⟩
  | pairL _ ih =>
    simp [Tm.Closed, Tm.fv] at ht ⊢
    exact ⟨ih ht.1, ht.2⟩
  | pairR _ ih =>
    simp [Tm.Closed, Tm.fv] at ht ⊢
    exact ⟨ht.1, ih ht.2⟩
  | cons _ ih =>
    simp [Tm.Closed, Tm.fv] at ht ⊢
    exact ih ht
  | pack _ ih =>
    simp [Tm.Closed, Tm.fv] at ht ⊢
    exact ih ht

theorem steps_closed {W : World} (hW : WorldClosed W) {t u : Tm} (h : Steps W t u) (ht : t.Closed) :
    u.Closed := by
  induction h with
  | refl => exact ht
  | tail _ hs ih => exact step_closed hW hs ih

end NishtAbel2024V5

/-! ## Solutions/V5/Cand.lean -/

/-! # V5: reducibility candidates -/

namespace NishtAbel2024V5

theorem SN.step {W : World} {t t' : Tm} (h : SN W t) (hs : Step W t t') : SN W t' :=
  Acc.inv h hs

theorem SN.of_reducts {W : World} {t : Tm} (h : ∀ t', Step W t t' → SN W t') : SN W t :=
  Acc.intro t h

theorem Cand.red_steps {W : World} {𝒜 : Set Tm} (h : Cand W 𝒜) {t u : Tm} (ht : t ∈ 𝒜)
    (hs : Steps W t u) : u ∈ 𝒜 := by
  induction hs with
  | refl => exact ht
  | tail _ hs ih => exact h.red _ ih _ hs

/-- Intro sets contain every closed non-introduction term whose reducts they contain. -/
theorem introSet_of_reducts {W : World} {P : Tm → Prop} {t : Tm} (hc : t.Closed)
    (hi : ¬ IsIntro t) (h : ∀ t', Step W t t' → t' ∈ IntroSet W P) : t ∈ IntroSet W P := by
  refine ⟨⟨hc, SN.of_reducts fun t' hs => (h t' hs).1.2⟩, ?_⟩
  intro v hv hvi
  rcases Relation.ReflTransGen.cases_head hv with rfl | ⟨t₁, hs, hrest⟩
  · exact absurd hvi hi
  · exact (h t₁ hs).2 v hrest hvi

theorem introSet_cand {W : World} (hW : WorldClosed W) (P : Tm → Prop) :
    Cand W (IntroSet W P) where
  sn _ h := h.1
  red t ht t' hs := by
    refine ⟨⟨step_closed hW hs ht.1.1, ht.1.2.step hs⟩, ?_⟩
    intro v hv hvi
    exact ht.2 v (Relation.ReflTransGen.head hs hv) hvi
  neutral t hc hn h := introSet_of_reducts hc hn.1 h

theorem introSet_of_intro {W : World} {P : Tm → Prop} {v : Tm} (h : v ∈ IntroSet W P)
    (hv : IsIntro v) : P v :=
  h.2 v Relation.ReflTransGen.refl hv

theorem arrSet_cand {W : World} (hW : WorldClosed W) {𝒜 ℬ : Set Tm} (hA : Cand W 𝒜)
    (hB : Cand W ℬ) : Cand W (ArrSet W 𝒜 ℬ) where
  sn _ h := h.1
  red t ht t' hs := by
    refine ⟨⟨step_closed hW hs ht.1.1, ht.1.2.step hs⟩, ?_⟩
    intro s hs'
    exact hB.red _ (ht.2 s hs') _ (Step.appFun hs)
  neutral t hc hn h := by
    refine ⟨⟨hc, SN.of_reducts fun t' hs => (h t' hs).1.2⟩, ?_⟩
    intro s hs
    have hsn : SN W s := (hA.sn s hs).2
    induction hsn with
    | intro s _ ih =>
      apply hB.neutral
      · simp [Tm.Closed, Tm.fv, Elim.fv] at hc ⊢
        exact ⟨hc, (hA.sn s hs).1⟩
      · exact neutral_app hn _
      · intro u hu
        cases hu with
        | head hh =>
          obtain ⟨t', ht', hu⟩ := hn.2 [.term s] _ hh
          subst hu
          exact (h t' (Step.head ht')).2 s hs
        | appFun hs' => exact (h _ hs').2 s hs
        | appArg hs' => exact ih _ hs' (hA.red s hs _ hs')

theorem MuSet_eq (W : World) (F : Nat → Set Tm → Set Tm) (α : Ordinal.{0}) :
    MuSet W F α = IntroSet W (fun v => ∃ c t β, ∃ _ : β < α, v = .cons c t ∧ t ∈ F c (MuSet W F β)) := by
  unfold MuSet
  rw [WellFounded.fix_eq]

theorem NuSet_eq (W : World) (n : Nat) (G : Nat → Set Tm → Set Tm) (α : Ordinal.{0}) :
    NuSet W n G α = {t | SNc W t ∧ ∀ β (_ : β < α), ∀ d < n,
      Tm.app t (.proj d) ∈ G d (NuSet W n G β)} := by
  unfold NuSet
  rw [WellFounded.fix_eq]

theorem nuSet_cand {W : World} (hW : WorldClosed W) (n : Nat) {G : Nat → Set Tm → Set Tm}
    (hG : ∀ d < n, ∀ 𝒳, Cand W 𝒳 → Cand W (G d 𝒳)) (α : Ordinal.{0}) :
    Cand W (NuSet W n G α) := by
  induction α using WellFoundedLT.induction with
  | _ α ih =>
    rw [NuSet_eq]
    refine ⟨fun _ h => h.1, ?_, ?_⟩
    · intro t ht t' hs
      refine ⟨⟨step_closed hW hs ht.1.1, ht.1.2.step hs⟩, ?_⟩
      intro β hβ d hd
      exact (hG d hd _ (ih β hβ)).red _ (ht.2 β hβ d hd) _ (Step.appFun hs)
    · intro t hc hn h
      refine ⟨⟨hc, SN.of_reducts fun t' hs => (h t' hs).1.2⟩, ?_⟩
      intro β hβ d hd
      apply (hG d hd _ (ih β hβ)).neutral
      · simpa [Tm.Closed, Tm.fv, Elim.fv] using hc
      · exact neutral_app hn _
      · intro u hu
        cases hu with
        | head hh =>
          obtain ⟨t', ht', hu⟩ := hn.2 [.proj d] _ hh
          subst hu
          exact (h t' (Step.head ht')).2 β hβ d hd
        | appFun hs' => exact (h _ hs').2 β hβ d hd

/-- Sets defined by an instantiation behave like function sets. -/
theorem instSet_cand.{u} {W : World} (hW : WorldClosed W) {I : Sort u} (P : I → Prop)
    (F : I → Set Tm) (hF : ∀ i, P i → Cand W (F i)) :
    Cand W {t | SNc W t ∧ ∀ i, P i → Tm.app t .inst ∈ F i} where
  sn _ h := h.1
  red t ht t' hs := by
    refine ⟨⟨step_closed hW hs ht.1.1, ht.1.2.step hs⟩, ?_⟩
    intro i hi
    exact (hF i hi).red _ (ht.2 i hi) _ (Step.appFun hs)
  neutral t hc hn h := by
    refine ⟨⟨hc, SN.of_reducts fun t' hs => (h t' hs).1.2⟩, ?_⟩
    intro i hi
    apply (hF i hi).neutral
    · simpa [Tm.Closed, Tm.fv, Elim.fv] using hc
    · exact neutral_app hn _
    · intro u hu
      cases hu with
      | head hh =>
        obtain ⟨t', ht', hu⟩ := hn.2 [.inst] _ hh
        subst hu
        exact (h t' (Step.head ht')).2 i hi
      | appFun hs' => exact (h _ hs').2 i hi

theorem allTSet_cand {W : World} (hW : WorldClosed W) {κ : Kind} {F : Sem κ.erase → Set Tm}
    (hF : ∀ X, Good W κ X → Cand W (F X)) : Cand W (AllTSet W κ F) :=
  instSet_cand (I := Sem κ.erase) hW (fun X => Good W κ X) F hF

theorem allSSet_cand {W : World} (hW : WorldClosed W) {α : Ordinal.{0}}
    {F : Ordinal.{0} → Set Tm} (hF : ∀ β, β < α → Cand W (F β)) : Cand W (AllSSet W α F) :=
  instSet_cand (I := Ordinal.{0}) hW (fun β => β < α) F hF

theorem interpAt_eq (W : World) (ρ : SizeVal) (θ : TEnv) :
    ∀ (S : List Ty) (c : Nat) (ζ : SzEnv) (η : Env) (h : c < S.length),
      interpAt W ρ θ S c ζ η = interp W ρ θ (S[c]'h) .star ζ η
  | [], c, ζ, η, h => by simp at h
  | A :: S, 0, ζ, η, _ => rfl
  | A :: S, c + 1, ζ, η, h => by
    simp only [interpAt]
    exact interpAt_eq W ρ θ S c ζ η (by simpa using h)

end NishtAbel2024V5

/-! ## Solutions/V5/Monotone.lean -/

/-! # V5: monotonicity of the interpretation -/

namespace NishtAbel2024V5

theorem introSet_mono {W : World} {P Q : Tm → Prop} (h : ∀ v, P v → Q v) :
    IntroSet W P ⊆ IntroSet W Q :=
  fun _ ht => ⟨ht.1, fun v hv hi => h v (ht.2 v hv hi)⟩

theorem arrSet_mono {W : World} {𝒜 𝒜' ℬ ℬ' : Set Tm} (hA : 𝒜' ⊆ 𝒜) (hB : ℬ ⊆ ℬ') :
    ArrSet W 𝒜 ℬ ⊆ ArrSet W 𝒜' ℬ' :=
  fun _ ht => ⟨ht.1, fun s hs => hB (ht.2 s (hA hs))⟩

theorem prodSet_mono {W : World} {𝒜 𝒜' ℬ ℬ' : Set Tm} (hA : 𝒜 ⊆ 𝒜') (hB : ℬ ⊆ ℬ') :
    ProdSet W 𝒜 ℬ ⊆ ProdSet W 𝒜' ℬ' :=
  introSet_mono fun _ ⟨t, u, hv, ht, hu⟩ => ⟨t, u, hv, hA ht, hB hu⟩

/-- Monotone set operators. -/
def SetMono (F : Set Tm → Set Tm) : Prop := ∀ 𝒳 𝒴, 𝒳 ⊆ 𝒴 → F 𝒳 ⊆ F 𝒴

theorem muSet_mono_ord {W : World} {F : Nat → Set Tm → Set Tm} {α α' : Ordinal.{0}}
    (h : α ≤ α') : MuSet W F α ⊆ MuSet W F α' := by
  rw [MuSet_eq, MuSet_eq]
  exact introSet_mono fun _ ⟨c, t, β, hβ, hv, ht⟩ => ⟨c, t, β, lt_of_lt_of_le hβ h, hv, ht⟩

theorem nuSet_anti_ord {W : World} {n : Nat} {G : Nat → Set Tm → Set Tm} {α α' : Ordinal.{0}}
    (h : α ≤ α') : NuSet W n G α' ⊆ NuSet W n G α := by
  rw [NuSet_eq, NuSet_eq]
  exact fun _ ht => ⟨ht.1, fun β hβ d hd => ht.2 β (lt_of_lt_of_le hβ h) d hd⟩

theorem muSet_mono_fun {W : World} {F F' : Nat → Set Tm → Set Tm}
    (hle : ∀ c 𝒳, F c 𝒳 ⊆ F' c 𝒳) (hmono : ∀ c, SetMono (F' c)) (α : Ordinal.{0}) :
    MuSet W F α ⊆ MuSet W F' α := by
  induction α using WellFoundedLT.induction with
  | _ α ih =>
    rw [MuSet_eq, MuSet_eq]
    exact introSet_mono fun _ ⟨c, t, β, hβ, hv, ht⟩ =>
      ⟨c, t, β, hβ, hv, hmono c _ _ (ih β hβ) (hle c _ ht)⟩

theorem nuSet_mono_fun {W : World} {n : Nat} {G G' : Nat → Set Tm → Set Tm}
    (hle : ∀ d < n, ∀ 𝒳, G d 𝒳 ⊆ G' d 𝒳) (hmono : ∀ d < n, SetMono (G' d)) (α : Ordinal.{0}) :
    NuSet W n G α ⊆ NuSet W n G' α := by
  induction α using WellFoundedLT.induction with
  | _ α ih =>
    rw [NuSet_eq, NuSet_eq]
    exact fun _ ht => ⟨ht.1, fun β hβ d hd =>
      hmono d hd _ _ (ih β hβ) (hle d hd _ (ht.2 β hβ d hd))⟩

theorem interpAt_out (W : World) (ρ : SizeVal) (θ : TEnv) :
    ∀ (S : List Ty) (c : Nat) (ζ : SzEnv) (η : Env), S.length ≤ c → interpAt W ρ θ S c ζ η = ∅
  | [], c, ζ, η, _ => by cases c <;> rfl
  | A :: S, 0, ζ, η, h => by simp at h
  | A :: S, c + 1, ζ, η, h => by
    simp only [interpAt]
    exact interpAt_out W ρ θ S c ζ η (by simpa using h)

theorem allTSet_mono {W : World} {κ : Kind} {F F' : Sem κ.erase → Set Tm}
    (h : ∀ X, Good W κ X → F X ⊆ F' X) : AllTSet W κ F ⊆ AllTSet W κ F' :=
  fun _ ht => ⟨ht.1, fun 𝒳 h𝒳 => h 𝒳 h𝒳 (ht.2 𝒳 h𝒳)⟩

theorem exTSet_mono {W : World} {κ : Kind} {F F' : Sem κ.erase → Set Tm}
    (h : ∀ X, Good W κ X → F X ⊆ F' X) : ExTSet W κ F ⊆ ExTSet W κ F' :=
  introSet_mono fun _ ⟨t, 𝒳, hv, h𝒳, ht⟩ => ⟨t, 𝒳, hv, h𝒳, h 𝒳 h𝒳 ht⟩

theorem allSSet_mono {W : World} {α : Ordinal.{0}} {F F' : Ordinal.{0} → Set Tm}
    (h : ∀ β, F β ⊆ F' β) : AllSSet W α F ⊆ AllSSet W α F' :=
  fun _ ht => ⟨ht.1, fun β hβ => h β (ht.2 β hβ)⟩

theorem exSSet_mono {W : World} {α : Ordinal.{0}} {F F' : Ordinal.{0} → Set Tm}
    (h : ∀ β, F β ⊆ F' β) : ExSSet W α F ⊆ ExSSet W α F' :=
  introSet_mono fun _ ⟨t, β, hv, hβ, ht⟩ => ⟨t, β, hv, hβ, h β ht⟩

end NishtAbel2024V5

/-! ## Solutions/V5/Stable.lean -/

/-! # V5: `Ω` and stabilization of the `μ`/`ν` stages -/

namespace NishtAbel2024V5

open Cardinal Ordinal Order Set

instance : Infinite Tm := Infinite.of_injective Tm.var (fun a b h => by cases h; rfl)

theorem omega_isSuccLimit : IsSuccLimit Omega := by
  unfold Omega
  apply Cardinal.isSuccLimit_ord
  exact (Cardinal.aleph0_le_mk Tm).trans (Order.le_succ _)

theorem add_nat_lt_omega {α : Ordinal.{0}} (h : α < Omega) (n : Nat) : α + n < Omega := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    rw [Nat.cast_succ, ← add_assoc, Ordinal.add_one_eq_succ]
    exact omega_isSuccLimit.succ_lt ih

/-- An increasing family of term sets is constant on some successor step below `Ω`. -/
theorem exists_succ_subset_of_mono {P : Ordinal.{0} → Set Tm} (hP : Monotone P) :
    ∃ β < Omega, P (succ β) ⊆ P β := by
  by_contra h
  push_neg at h
  have hex : ∀ β, β < Omega → ∃ v, v ∈ P (succ β) ∧ v ∉ P β :=
    fun β hβ => Set.not_subset.mp (h β hβ)
  classical
  let g : Ordinal.{0} → Tm := fun β => if hβ : β < Omega then (hex β hβ).choose else .unit
  apply Cardinal.not_injective_limitation_set g
  have key : ∀ β₁ β₂, β₁ < Omega → β₂ < Omega → β₁ < β₂ → g β₁ ≠ g β₂ := by
    intro β₁ β₂ h₁ h₂ hlt heq
    have m1 := (hex β₁ h₁).choose_spec.1
    have m2 := (hex β₂ h₂).choose_spec.2
    simp only [g, dif_pos h₁, dif_pos h₂] at heq
    rw [heq] at m1
    exact m2 (hP (Order.succ_le_of_lt hlt) m1)
  intro β₁ h₁ β₂ h₂ heq
  have h₁' : β₁ < Omega := h₁
  have h₂' : β₂ < Omega := h₂
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact key β₁ β₂ h₁' h₂' hlt heq
  · exact key β₂ β₁ h₂' h₁' hlt heq.symm

/-- A decreasing family of term sets is constant on some successor step below `Ω`. -/
theorem exists_subset_succ_of_anti {N : Ordinal.{0} → Set Tm} (hN : Antitone N) :
    ∃ β < Omega, N β ⊆ N (succ β) := by
  by_contra h
  push_neg at h
  have hex : ∀ β, β < Omega → ∃ v, v ∈ N β ∧ v ∉ N (succ β) :=
    fun β hβ => Set.not_subset.mp (h β hβ)
  classical
  let g : Ordinal.{0} → Tm := fun β => if hβ : β < Omega then (hex β hβ).choose else .unit
  apply Cardinal.not_injective_limitation_set g
  have key : ∀ β₁ β₂, β₁ < Omega → β₂ < Omega → β₁ < β₂ → g β₁ ≠ g β₂ := by
    intro β₁ β₂ h₁ h₂ hlt heq
    have m1 := (hex β₁ h₁).choose_spec.2
    have m2 := (hex β₂ h₂).choose_spec.1
    simp only [g, dif_pos h₁, dif_pos h₂] at heq
    rw [← heq] at m2
    exact m1 (hN (Order.succ_le_of_lt hlt) m2)
  intro β₁ h₁ β₂ h₂ heq
  have h₁' : β₁ < Omega := h₁
  have h₂' : β₂ < Omega := h₂
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact key β₁ β₂ h₁' h₂' hlt heq
  · exact key β₂ β₁ h₂' h₁' hlt heq.symm

/-- The value predicate of stage `α` of an inductive type. -/
def MuPred (W : World) (F : Nat → Set Tm → Set Tm) (α : Ordinal.{0}) : Set Tm :=
  fun v => ∃ c t β, ∃ _ : β < α, v = .cons c t ∧ t ∈ F c (MuSet W F β)

theorem MuSet_eq' (W : World) (F : Nat → Set Tm → Set Tm) (α : Ordinal.{0}) :
    MuSet W F α = IntroSet W (MuPred W F α) := MuSet_eq W F α

/-- The stages of an inductive type are constant from some `β₀ < Ω` on. -/
theorem muSet_eventually_const (W : World) (F : Nat → Set Tm → Set Tm) :
    ∃ β₀ < Omega, ∀ γ, β₀ ≤ γ → MuSet W F γ = MuSet W F β₀ := by
  have hmono : Monotone (MuPred W F) := by
    intro α α' h v ⟨c, t, β, hβ, hv, ht⟩
    exact ⟨c, t, β, lt_of_lt_of_le hβ h, hv, ht⟩
  obtain ⟨β₀, hβ₀, hstep⟩ := exists_succ_subset_of_mono hmono
  have hconst : ∀ γ, β₀ ≤ γ → MuPred W F γ = MuPred W F β₀ := by
    intro γ
    induction γ using WellFoundedLT.induction with
    | _ γ ih =>
      intro hγ
      apply Set.Subset.antisymm _ (hmono hγ)
      rintro v ⟨c, t, β, hβ, hv, ht⟩
      by_cases hlt : β < β₀
      · exact ⟨c, t, β, hlt, hv, ht⟩
      · have hβeq : MuSet W F β = MuSet W F β₀ := by
          rw [MuSet_eq', MuSet_eq', ih β hβ (not_lt.mp hlt)]
        rw [hβeq] at ht
        exact hstep ⟨c, t, β₀, Order.lt_succ β₀, hv, ht⟩
  refine ⟨β₀, hβ₀, fun γ hγ => ?_⟩
  rw [MuSet_eq', MuSet_eq', hconst γ hγ]

theorem muSet_stable (W : World) (F : Nat → Set Tm → Set Tm) :
    ∃ β₀ < Omega, MuSet W F β₀ = MuSet W F Omega := by
  obtain ⟨β₀, hβ₀, h⟩ := muSet_eventually_const W F
  exact ⟨β₀, hβ₀, (h Omega hβ₀.le).symm⟩

/-- Stages at or above `Ω` coincide. -/
theorem muSet_ge_omega (W : World) (F : Nat → Set Tm → Set Tm) {γ : Ordinal.{0}}
    (hγ : Omega ≤ γ) : MuSet W F γ = MuSet W F Omega := by
  obtain ⟨β₀, hβ₀, h⟩ := muSet_eventually_const W F
  rw [h γ (hβ₀.le.trans hγ), h Omega hβ₀.le]

/-- The stages of a coinductive type are constant from some `β₀ < Ω` on. -/
theorem nuSet_eventually_const (W : World) (n : Nat) (G : Nat → Set Tm → Set Tm) :
    ∃ β₀ < Omega, ∀ γ, β₀ ≤ γ → NuSet W n G γ = NuSet W n G β₀ := by
  have hanti : Antitone (NuSet W n G) := fun α α' h => nuSet_anti_ord h
  obtain ⟨β₀, hβ₀, hstep⟩ := exists_subset_succ_of_anti hanti
  have hconst : ∀ γ, β₀ ≤ γ → NuSet W n G γ = NuSet W n G β₀ := by
    intro γ
    induction γ using WellFoundedLT.induction with
    | _ γ ih =>
      intro hγ
      apply Set.Subset.antisymm (hanti hγ)
      intro t ht
      have ht' := hstep ht
      rw [NuSet_eq] at ht'
      have ht0 := ht
      rw [NuSet_eq] at ht0
      rw [NuSet_eq]
      refine ⟨ht0.1, ?_⟩
      intro β hβ d hd
      by_cases hlt : β < β₀
      · exact ht0.2 β hlt d hd
      · rw [ih β hβ (not_lt.mp hlt)]
        exact ht'.2 β₀ (Order.lt_succ β₀) d hd
  exact ⟨β₀, hβ₀, hconst⟩

theorem nuSet_stable (W : World) (n : Nat) (G : Nat → Set Tm → Set Tm) :
    ∃ β₀ < Omega, NuSet W n G β₀ = NuSet W n G Omega := by
  obtain ⟨β₀, hβ₀, h⟩ := nuSet_eventually_const W n G
  exact ⟨β₀, hβ₀, (h Omega hβ₀.le).symm⟩

/-- Stages at or above `Ω` coincide. -/
theorem nuSet_ge_omega (W : World) (n : Nat) (G : Nat → Set Tm → Set Tm) {γ : Ordinal.{0}}
    (hγ : Omega ≤ γ) : NuSet W n G γ = NuSet W n G Omega := by
  obtain ⟨β₀, hβ₀, h⟩ := nuSet_eventually_const W n G
  rw [h γ (hβ₀.le.trans hγ), h Omega hβ₀.le]

/-- `μ^∞` is closed under constructors: a payload at stage `Ω` is a payload at some stage below. -/
theorem muSet_omega_closed {W : World} {F : Nat → Set Tm → Set Tm} {c : Nat} {t : Tm}
    (ht : t ∈ F c (MuSet W F Omega)) : ∃ β < Omega, t ∈ F c (MuSet W F β) := by
  obtain ⟨β₀, hβ₀, heq⟩ := muSet_stable W F
  exact ⟨β₀, hβ₀, by rw [heq]; exact ht⟩

/-- Projections of `ν^∞` land at stage `Ω`. -/
theorem nuSet_omega_proj {W : World} {n : Nat} {G : Nat → Set Tm → Set Tm} {t : Tm}
    (ht : t ∈ NuSet W n G Omega) {d : Nat} (hd : d < n) :
    Tm.app t (.proj d) ∈ G d (NuSet W n G Omega) := by
  obtain ⟨β₀, hβ₀, heq⟩ := nuSet_stable W n G
  rw [NuSet_eq] at ht
  rw [← heq]
  exact ht.2 β₀ hβ₀ d hd

end NishtAbel2024V5

/-! ## Solutions/V5/Kind.lean -/

/-! # V5: semantic domains of kinds, goodness and order -/

namespace NishtAbel2024V5

/-! ## Kind-polymorphic values -/

@[simp] theorem PSem.ofSem_self (ι : SKind) (X : Sem ι) : PSem.ofSem ι X ι = X := by
  simp [PSem.ofSem]

theorem PSem.ofSem_ne {ι ι' : SKind} (X : Sem ι) (h : ι ≠ ι') :
    PSem.ofSem ι X ι' = Sem.dflt ι' := by
  simp [PSem.ofSem, h]

@[simp] theorem Sem.ofStar_star (S : Set Tm) : Sem.ofStar S .star = S := rfl

@[simp] theorem Sem.ofFun_arr (f : (ι₁ ι₂ : SKind) → Sem ι₁ → Sem ι₂) (ι₁ ι₂ : SKind) :
    Sem.ofFun f (.arr ι₁ ι₂) = f ι₁ ι₂ := rfl

@[simp] theorem Env.cons_zero (X : PSem) (η : Env) : Env.cons X η 0 = X := rfl

@[simp] theorem Env.cons_succ (X : PSem) (η : Env) (n : Nat) : Env.cons X η (n + 1) = η n := rfl

/-! ## Polarities -/

/-- `PolRel W π κ X Y`: `X` and `Y` are related along the variance `π` at kind `κ`. -/
def PolRel (W : World) (π : Pol) (κ : Kind) {ι : SKind} (X Y : Sem ι) : Prop :=
  polRelOf (SemLe W κ) π X Y

theorem polRelOf_mono {α : Type} {le : α → α → Prop} {π π' : Pol} (h : Pol.le π' π) {X Y : α}
    (hr : polRelOf le π' X Y) : polRelOf le π X Y := by
  cases π' <;> cases π <;> simp_all [Pol.le, polRelOf]

theorem Pol.le_refl (π : Pol) : Pol.le π π := by cases π <;> simp [Pol.le]

theorem Pol.le_trans {π₁ π₂ π₃ : Pol} (h₁ : Pol.le π₁ π₂) (h₂ : Pol.le π₂ π₃) : Pol.le π₁ π₃ := by
  cases π₁ <;> cases π₂ <;> cases π₃ <;> simp_all [Pol.le]

/-! ## Equations for goodness and order -/

theorem good_star {W : World} {A : Set Tm} : Good W .star (ι := .star) A ↔ Cand W A := Iff.rfl

theorem semLe_star {W : World} {A B : Set Tm} : SemLe W .star (ι := .star) A B ↔ A ⊆ B :=
  Iff.rfl

theorem good_arr {W : World} {π : Pol} {κ₁ κ₂ : Kind} {ι₁ ι₂ : SKind} {F : Sem (.arr ι₁ ι₂)} :
    Good W (.arr π κ₁ κ₂) F ↔
      (∀ X, Good W κ₁ X → Good W κ₂ (F X)) ∧
      ∀ X Y, Good W κ₁ X → Good W κ₁ Y → PolRel W π κ₁ X Y → SemLe W κ₂ (F X) (F Y) :=
  Iff.rfl

theorem semLe_arr {W : World} {π : Pol} {κ₁ κ₂ : Kind} {ι₁ ι₂ : SKind}
    {F G : Sem (.arr ι₁ ι₂)} :
    SemLe W (.arr π κ₁ κ₂) F G ↔
      ∀ X Y, Good W κ₁ X → Good W κ₁ Y → PolRel W π κ₁ X Y → SemLe W κ₂ (F X) (G Y) :=
  Iff.rfl

theorem good_star_arr {W : World} {ι₁ ι₂ : SKind} {F : Sem (.arr ι₁ ι₂)} :
    ¬ Good W .star F := fun h => h

theorem good_arr_star {W : World} {π : Pol} {κ₁ κ₂ : Kind} {A : Sem .star} :
    ¬ Good W (.arr π κ₁ κ₂) A := fun h => h

/-! ## Reflexivity and transitivity -/

theorem Good.refl {W : World} : ∀ {κ : Kind} {ι : SKind} {X : Sem ι}, Good W κ X → SemLe W κ X X
  | .star, .star, _, _ => subset_refl _
  | .arr _ _ _, .arr _ _, _, h => h.2
  | .arr _ _ _, .star, _, h => absurd h good_arr_star
  | .star, .arr _ _, _, h => absurd h good_star_arr

theorem PolRel.refl {W : World} (π : Pol) {κ : Kind} {ι : SKind} {X : Sem ι}
    (h : Good W κ X) : PolRel W π κ X X := by
  have := Good.refl h
  cases π <;> simp [PolRel, polRelOf, this]

theorem SemLe.trans {W : World} :
    ∀ {κ : Kind} {ι : SKind} {X Y Z : Sem ι}, Good W κ X → Good W κ Y → Good W κ Z →
      SemLe W κ X Y → SemLe W κ Y Z → SemLe W κ X Z
  | .star, .star, _, _, _, _, _, _, h₁, h₂ => Set.Subset.trans h₁ h₂
  | .arr π κ₁ κ₂, .arr ι₁ ι₂, F, G, H, hF, hG, hH, h₁, h₂ => by
    intro X Y hX hY hXY
    exact SemLe.trans (hF.1 X hX) (hG.1 X hX) (hH.1 Y hY)
      (h₁ X X hX hX (PolRel.refl π hX)) (h₂ X Y hX hY hXY)
  | .arr _ _ _, .star, _, _, _, h, _, _, _, _ => absurd h good_arr_star
  | .star, .arr _ _, _, _, _, h, _, _, _, _ => absurd h good_star_arr

/-- Antisymmetry at kind `*`. -/
theorem semLe_star_antisymm {W : World} {A B : Set Tm} (h₁ : SemLe W .star (ι := .star) A B)
    (h₂ : SemLe W .star (ι := .star) B A) : A = B :=
  Set.Subset.antisymm h₁ h₂

/-! ## Subkinding -/

theorem SubKind.erase_eq {κ κ' : Kind} (h : SubKind κ κ') : κ.erase = κ'.erase := by
  induction h with
  | star => rfl
  | arr _ _ _ ih₁ ih₂ => simp [Kind.erase, ih₁, ih₂]

theorem SubKind.refl : ∀ κ : Kind, SubKind κ κ
  | .star => .star
  | .arr π κ₁ κ₂ => .arr (Pol.le_refl π) (SubKind.refl κ₁) (SubKind.refl κ₂)

/-- Goodness and order are transported along subkinding. -/
theorem SubKind.sem {W : World} {κ κ' : Kind} (h : SubKind κ κ') :
    ∀ {ι : SKind}, (∀ X : Sem ι, Good W κ X → Good W κ' X) ∧
      (∀ X Y : Sem ι, Good W κ X → Good W κ Y → SemLe W κ X Y → SemLe W κ' X Y) := by
  induction h with
  | star =>
    intro ι
    exact ⟨fun _ h => h, fun _ _ _ _ h => h⟩
  | @arr π π' κ₁ κ₁' κ₂ κ₂' hπ _ _ ih₁ ih₂ =>
    intro ι
    cases ι with
    | star => exact ⟨fun _ h => absurd h good_arr_star, fun _ _ h => absurd h good_arr_star⟩
    | arr ι₁ ι₂ =>
      have hrel : ∀ X Y : Sem ι₁, Good W κ₁' X → Good W κ₁' Y → PolRel W π' κ₁' X Y →
          PolRel W π κ₁ X Y := by
        intro X Y hX hY hXY
        apply polRelOf_mono hπ
        cases π' <;> simp only [PolRel, polRelOf] at hXY ⊢
        · exact ⟨ih₁.2 X Y hX hY hXY.1, ih₁.2 Y X hY hX hXY.2⟩
        · exact ih₁.2 X Y hX hY hXY
        · exact ih₁.2 Y X hY hX hXY
      refine ⟨fun F hF => ⟨fun X hX => ih₂.1 _ (hF.1 X (ih₁.1 X hX)), ?_⟩, ?_⟩
      · intro X Y hX hY hXY
        exact ih₂.2 _ _ (hF.1 X (ih₁.1 X hX)) (hF.1 Y (ih₁.1 Y hY))
          (hF.2 X Y (ih₁.1 X hX) (ih₁.1 Y hY) (hrel X Y hX hY hXY))
      · intro F G hF hG hFG X Y hX hY hXY
        exact ih₂.2 _ _ (hF.1 X (ih₁.1 X hX)) (hG.1 Y (ih₁.1 Y hY))
          (hFG X Y (ih₁.1 X hX) (ih₁.1 Y hY) (hrel X Y hX hY hXY))

theorem Good.sub {W : World} {κ κ' : Kind} (h : SubKind κ κ') {ι : SKind} {X : Sem ι}
    (hX : Good W κ X) : Good W κ' X :=
  (SubKind.sem h).1 X hX

theorem SemLe.sub {W : World} {κ κ' : Kind} (h : SubKind κ κ') {ι : SKind} {X Y : Sem ι}
    (hX : Good W κ X) (hY : Good W κ Y) (hXY : SemLe W κ X Y) : SemLe W κ' X Y :=
  (SubKind.sem h).2 X Y hX hY hXY

/-! ## Variance-directed relations -/

theorem PolRel.symm_mix {W : World} {κ : Kind} {ι : SKind} {X Y : Sem ι}
    (h : PolRel W .mix κ X Y) : PolRel W .mix κ Y X := ⟨h.2, h.1⟩

theorem PolRel.top {W : World} {κ : Kind} {ι : SKind} (X Y : Sem ι) : PolRel W .top κ X Y :=
  trivial

theorem PolRel.of_mix {W : World} (π : Pol) {κ : Kind} {ι : SKind} {X Y : Sem ι}
    (h : PolRel W .mix κ X Y) : PolRel W π κ X Y :=
  polRelOf_mono (π' := .mix) trivial h

end NishtAbel2024V5

/-! ## Solutions/V5/Size.lean -/

/-! # V5: sizes — increments, bound normalization, soundness of size judgments (Theorem 2) -/

namespace NishtAbel2024V5

open Order

theorem add_nat_lt_add_nat {α β : Ordinal.{0}} (h : α < β) (n : Nat) : α + n < β + n := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    rw [Nat.cast_succ, ← add_assoc, ← add_assoc, ← Order.succ_eq_add_one, ← Order.succ_eq_add_one]
    exact Order.succ_lt_succ ih

theorem add_nat_le_add_nat {α β : Ordinal.{0}} (h : α ≤ β) (n : Nat) : α + n ≤ β + n :=
  add_le_add h le_rfl

theorem min_add_nat (α β : Ordinal.{0}) (n : Nat) : min α β + n = min (α + n) (β + n) := by
  rcases le_total α β with h | h
  · rw [min_eq_left h, min_eq_left (add_nat_le_add_nat h n)]
  · rw [min_eq_right h, min_eq_right (add_nat_le_add_nat h n)]

theorem lt_add_one_iff_le' {α β : Ordinal.{0}} : α < β + 1 ↔ α ≤ β := by
  rw [← Order.succ_eq_add_one, Order.lt_succ_iff]

theorem omega_le_add_nat (n : Nat) : Omega ≤ Omega + n := le_self_add

theorem SizeCtx.mem_dom {Ψ : SizeCtx} {i : Nat} {a : Size} (h : (i, a) ∈ Ψ) : i ∈ Ψ.dom :=
  List.mem_map.mpr ⟨(i, a), h, rfl⟩

@[simp] theorem SizeCtx.dom_append (Ψ Ψ' : SizeCtx) : (Ψ ++ Ψ').dom = Ψ.dom ++ Ψ'.dom := by
  simp [SizeCtx.dom]

@[simp] theorem SizeCtx.dom_cons (p : Nat × Size) (Ψ : SizeCtx) :
    SizeCtx.dom (p :: Ψ) = p.1 :: Ψ.dom := rfl

@[simp] theorem SizeCtx.dom_nil : SizeCtx.dom [] = [] := rfl

/-! ## Increments -/

theorem sizeVal_shift (ρ : SizeVal) (ζ : SzEnv) :
    ∀ (a : Size) (n : Nat), sizeVal ρ ζ (a.shift n) = sizeVal ρ ζ a + n
  | .inf m, n => by simp [Size.shift, sizeVal, Nat.cast_add, add_assoc]
  | .var i m, n => by simp [Size.shift, sizeVal, Nat.cast_add, add_assoc]
  | .bvar k m, n => by simp [Size.shift, sizeVal, Nat.cast_add, add_assoc]
  | .meet a b, n => by
    simp only [Size.shift, sizeVal]
    rw [sizeVal_shift ρ ζ a n, sizeVal_shift ρ ζ b n, min_add_nat]

theorem Size.shift_zero : ∀ a : Size, a.shift 0 = a
  | .inf _ => rfl
  | .var _ _ => rfl
  | .bvar _ _ => rfl
  | .meet a b => by simp [Size.shift, Size.shift_zero a, Size.shift_zero b]

theorem Size.shift_shift : ∀ (a : Size) (m n : Nat), (a.shift m).shift n = a.shift (m + n)
  | .inf _, m, n => by simp [Size.shift, Nat.add_assoc]
  | .var _ _, m, n => by simp [Size.shift, Nat.add_assoc]
  | .bvar _ _, m, n => by simp [Size.shift, Nat.add_assoc]
  | .meet a b, m, n => by simp [Size.shift, Size.shift_shift a, Size.shift_shift b]

theorem SizeWfAt.shift {Ψ : SizeCtx} {m : Nat} :
    ∀ {a : Size} (n : Nat), SizeWfAt Ψ m a → SizeWfAt Ψ m (a.shift n)
  | .inf _, _, _ => trivial
  | .var _ _, _, h => h
  | .bvar _ _, _, h => h
  | .meet _ _, n, h => ⟨SizeWfAt.shift n h.1, SizeWfAt.shift n h.2⟩

theorem SizeWfAt.of_shift {Ψ : SizeCtx} {m : Nat} :
    ∀ {a : Size} {n : Nat}, SizeWfAt Ψ m (a.shift n) → SizeWfAt Ψ m a
  | .inf _, _, _ => trivial
  | .var _ _, _, h => h
  | .bvar _ _, _, h => h
  | .meet _ _, _, h => ⟨SizeWfAt.of_shift h.1, SizeWfAt.of_shift h.2⟩

/-! ## Bound normalization -/

theorem omega_le_sizeVal_up (ρ : SizeVal) (ζ : SzEnv) :
    ∀ a : Size, Omega ≤ sizeVal ρ ζ a → Omega ≤ sizeVal ρ ζ a.up
  | .inf _, _ => by simp only [Size.up, sizeVal]; exact omega_le_add_nat 1
  | .var _ _, h => h
  | .bvar _ _, h => h
  | .meet a b, h => by
    simp only [Size.up, sizeVal, le_min_iff] at h ⊢
    exact ⟨omega_le_sizeVal_up ρ ζ a h.1, omega_le_sizeVal_up ρ ζ b h.2⟩

theorem sizeVal_up_of_lt (ρ : SizeVal) (ζ : SzEnv) :
    ∀ a : Size, sizeVal ρ ζ a < Omega → sizeVal ρ ζ a.up = sizeVal ρ ζ a
  | .inf n, h => by
    simp only [sizeVal] at h
    exact absurd h (not_lt.mpr (omega_le_add_nat n))
  | .var _ _, _ => rfl
  | .bvar _ _, _ => rfl
  | .meet a b, h => by
    simp only [Size.up, sizeVal] at h ⊢
    rcases le_total (sizeVal ρ ζ a) (sizeVal ρ ζ b) with hab | hab
    · rw [min_eq_left hab] at h ⊢
      rw [sizeVal_up_of_lt ρ ζ a h]
      by_cases hb : sizeVal ρ ζ b < Omega
      · rw [sizeVal_up_of_lt ρ ζ b hb, min_eq_left hab]
      · have := omega_le_sizeVal_up ρ ζ b (not_lt.mp hb)
        exact min_eq_left (h.le.trans this)
    · rw [min_eq_right hab] at h ⊢
      rw [sizeVal_up_of_lt ρ ζ b h]
      by_cases ha : sizeVal ρ ζ a < Omega
      · rw [sizeVal_up_of_lt ρ ζ a ha, min_eq_right hab]
      · have := omega_le_sizeVal_up ρ ζ a (not_lt.mp ha)
        exact min_eq_right (h.le.trans this)

/-- An ordinal below `⟦a^↑⟧` is below `⟦a⟧`, unless `⟦a⟧ ≥ Ω`. -/
theorem lt_up_cases (ρ : SizeVal) (ζ : SzEnv) (a : Size) {β : Ordinal.{0}}
    (h : β < sizeVal ρ ζ a.up) : β < sizeVal ρ ζ a ∨ Omega ≤ sizeVal ρ ζ a := by
  by_cases ha : sizeVal ρ ζ a < Omega
  · rw [sizeVal_up_of_lt ρ ζ a ha] at h
    exact Or.inl h
  · exact Or.inr (not_lt.mp ha)

/-- Comparison of bound normalizations. -/
theorem le_of_up_le (ρ : SizeVal) (ζ : SzEnv) (a b : Size)
    (h : sizeVal ρ ζ a.up ≤ sizeVal ρ ζ b.up) :
    sizeVal ρ ζ a ≤ sizeVal ρ ζ b ∨ (Omega ≤ sizeVal ρ ζ a ∧ Omega ≤ sizeVal ρ ζ b) := by
  by_cases ha : sizeVal ρ ζ a < Omega
  · left
    rw [sizeVal_up_of_lt ρ ζ a ha] at h
    by_cases hb : sizeVal ρ ζ b < Omega
    · rwa [sizeVal_up_of_lt ρ ζ b hb] at h
    · exact ha.le.trans (not_lt.mp hb)
  · right
    refine ⟨not_lt.mp ha, ?_⟩
    by_contra hb
    have hb' := not_le.mp hb
    have hu := omega_le_sizeVal_up ρ ζ a (not_lt.mp ha)
    rw [sizeVal_up_of_lt ρ ζ b hb'] at h
    exact absurd (hu.trans h) (not_le.mpr hb')

/-- Comparison with a bound normalization. -/
theorem le_of_le_up (ρ : SizeVal) (ζ : SzEnv) (a b : Size)
    (h : sizeVal ρ ζ a ≤ sizeVal ρ ζ b.up) :
    sizeVal ρ ζ a ≤ sizeVal ρ ζ b ∨ (Omega ≤ sizeVal ρ ζ a ∧ Omega ≤ sizeVal ρ ζ b) := by
  by_cases hb : sizeVal ρ ζ b < Omega
  · left; rwa [sizeVal_up_of_lt ρ ζ b hb] at h
  · by_cases ha : sizeVal ρ ζ a < Omega
    · left; exact ha.le.trans (not_lt.mp hb)
    · right; exact ⟨not_lt.mp ha, not_lt.mp hb⟩

/-! ## Well-formedness of compared sizes -/

theorem SizeLt.wf {Ψ : SizeCtx} {a b : Size} (h : SizeLt Ψ a b) : SizeWf Ψ a ∧ SizeWf Ψ b := by
  induction h with
  | inf_inf _ => exact ⟨trivial, trivial⟩
  | var_var hi _ => exact ⟨hi, hi⟩
  | bound hm _ ih => exact ⟨SizeCtx.mem_dom hm, SizeWfAt.of_shift ih.2⟩
  | var_inf hm _ _ => exact ⟨SizeCtx.mem_dom hm, trivial⟩
  | meet_l _ hb ih => exact ⟨⟨ih.1, hb⟩, ih.2⟩
  | meet_r _ ha ih => exact ⟨⟨ha, ih.1⟩, ih.2⟩
  | lt_meet _ _ ih₁ ih₂ => exact ⟨ih₁.1, ih₁.2, ih₂.2⟩
  | trans _ _ ih₁ ih₂ => exact ⟨ih₁.1, ih₂.2⟩

/-! ## Theorem 2: soundness of size judgments -/

/-- `ρ ≤ ρ'` on the variables of `Ψ`. -/
def ValLe (Ψ : SizeCtx) (ρ ρ' : SizeVal) : Prop := ∀ i ∈ Ψ.dom, ρ i ≤ ρ' i

theorem ValLe.refl (Ψ : SizeCtx) (ρ : SizeVal) : ValLe Ψ ρ ρ := fun _ _ => le_rfl

/-- Theorem 2.1: well-formed sizes are monotone in the valuation. -/
theorem sizeWf_sound {Ψ : SizeCtx} {ρ ρ' : SizeVal} (hle : ValLe Ψ ρ ρ') (ζ : SzEnv) :
    ∀ {a : Size}, SizeWf Ψ a → sizeVal ρ ζ a ≤ sizeVal ρ' ζ a
  | .inf _, _ => le_rfl
  | .var i n, h => add_nat_le_add_nat (hle i h) n
  | .bvar _ _, h => absurd h (Nat.not_lt_zero _)
  | .meet _ _, h => min_le_min (sizeWf_sound hle ζ h.1) (sizeWf_sound hle ζ h.2)

/-- Theorem 2.3: strict size comparison is sound for ordered valid valuations. -/
theorem sizeLt_sound2 {Ψ : SizeCtx} {a b : Size} (h : SizeLt Ψ a b) :
    ∀ {ρ ρ' : SizeVal}, ValidVal Ψ ρ → ValidVal Ψ ρ' → ValLe Ψ ρ ρ' →
      sizeVal ρ SzEnv.zero a < sizeVal ρ' SzEnv.zero b := by
  induction h with
  | inf_inf hnm =>
    intro ρ ρ' _ _ _
    simp only [sizeVal]
    exact (add_lt_add_iff_left _).mpr (by exact_mod_cast hnm)
  | var_var hi hnm =>
    intro ρ ρ' _ _ hle
    simp only [sizeVal]
    exact lt_of_le_of_lt (add_nat_le_add_nat (hle _ hi) _)
      ((add_lt_add_iff_left _).mpr (by exact_mod_cast hnm))
  | @bound i n a b hm _ ih =>
    intro ρ ρ' hv hv' hle
    have h1 := ih hv hv' hle
    rw [sizeVal_shift, sizeVal_shift] at h1
    have h2 : sizeVal ρ SzEnv.zero a + n ≤ sizeVal ρ' SzEnv.zero b :=
      lt_add_one_iff_le'.mp (by simpa using h1)
    have h3 : ρ i + n < sizeVal ρ SzEnv.zero a + n := add_nat_lt_add_nat (hv _ hm) n
    exact lt_of_lt_of_le h3 h2
  | @var_inf i n m a hm _ ih =>
    intro ρ ρ' hv hv' hle
    have h1 := ih hv hv (ValLe.refl _ _)
    simp only [sizeVal] at h1 ⊢
    have h2 : sizeVal ρ SzEnv.zero a ≤ Omega := by
      have : sizeVal ρ SzEnv.zero a < Omega + 1 := by exact_mod_cast h1
      exact lt_add_one_iff_le'.mp this
    have h3 : ρ i < Omega := lt_of_lt_of_le (hv _ hm) h2
    exact lt_of_lt_of_le (add_nat_lt_omega h3 n) (omega_le_add_nat m)
  | meet_l _ _ ih =>
    intro ρ ρ' hv hv' hle
    exact lt_of_le_of_lt (min_le_left _ _) (ih hv hv' hle)
  | meet_r _ _ ih =>
    intro ρ ρ' hv hv' hle
    exact lt_of_le_of_lt (min_le_right _ _) (ih hv hv' hle)
  | lt_meet _ _ ih₁ ih₂ =>
    intro ρ ρ' hv hv' hle
    exact lt_min (ih₁ hv hv' hle) (ih₂ hv hv' hle)
  | trans _ _ ih₁ ih₂ =>
    intro ρ ρ' hv hv' hle
    exact lt_trans (ih₁ hv hv' hle) (ih₂ hv' hv' (ValLe.refl _ _))

/-- Theorem 2.2: non-strict size comparison is sound for ordered valid valuations. -/
theorem sizeLe_sound2 {Ψ : SizeCtx} {a b : Size} (h : SizeLe Ψ a b) {ρ ρ' : SizeVal}
    (hv : ValidVal Ψ ρ) (hv' : ValidVal Ψ ρ') (hle : ValLe Ψ ρ ρ') :
    sizeVal ρ SzEnv.zero a ≤ sizeVal ρ' SzEnv.zero b := by
  have := sizeLt_sound2 h hv hv' hle
  rw [sizeVal_shift] at this
  exact lt_add_one_iff_le'.mp (by exact_mod_cast this)

theorem sizeLt_sound {Ψ : SizeCtx} {ρ : SizeVal} (hv : ValidVal Ψ ρ) {a b : Size}
    (h : SizeLt Ψ a b) : sizeVal ρ SzEnv.zero a < sizeVal ρ SzEnv.zero b :=
  sizeLt_sound2 h hv hv (ValLe.refl _ _)

theorem sizeLe_sound {Ψ : SizeCtx} {ρ : SizeVal} (hv : ValidVal Ψ ρ) {a b : Size}
    (h : SizeLe Ψ a b) : sizeVal ρ SzEnv.zero a ≤ sizeVal ρ SzEnv.zero b :=
  sizeLe_sound2 h hv hv (ValLe.refl _ _)

/-! ## Size environments -/

def SzEnv.insert (k : Nat) (β : Ordinal.{0}) (ζ : SzEnv) : SzEnv := fun x =>
  if x < k then ζ x else if x = k then β else ζ (x - 1)

theorem SzEnv.insert_succ_cons (k : Nat) (β γ : Ordinal.{0}) (ζ : SzEnv) :
    SzEnv.insert (k + 1) β (SzEnv.cons γ ζ) = SzEnv.cons γ (SzEnv.insert k β ζ) := by
  funext x
  cases x with
  | zero => simp [SzEnv.insert, SzEnv.cons]
  | succ y =>
    simp only [SzEnv.insert, SzEnv.cons]
    by_cases h1 : y < k
    · simp [h1]
    · by_cases h2 : y = k
      · subst h2; simp
      · have h3 : ¬ y + 1 < k + 1 := by omega
        have h4 : y + 1 ≠ k + 1 := by omega
        simp only [h1, h2, h3, h4, if_false]
        cases y with
        | zero => omega
        | succ z => rfl

theorem SzEnv.insert_zero (β : Ordinal.{0}) (ζ : SzEnv) :
    SzEnv.insert 0 β ζ = SzEnv.cons β ζ := by
  funext x
  cases x with
  | zero => simp [SzEnv.insert, SzEnv.cons]
  | succ y => simp [SzEnv.insert, SzEnv.cons]

/-! ## Agreement -/

theorem sizeVal_agree {Ψ : SizeCtx} {m : Nat} {ρ ρ' : SizeVal} {ζ ζ' : SzEnv}
    (hρ : ∀ i ∈ Ψ.dom, ρ i = ρ' i) (hζ : ∀ x < m, ζ x = ζ' x) :
    ∀ {a : Size}, SizeWfAt Ψ m a → sizeVal ρ ζ a = sizeVal ρ' ζ' a
  | .inf _, _ => rfl
  | .var i n, ha => by simp only [sizeVal, hρ i ha]
  | .bvar k n, ha => by simp only [sizeVal, hζ k ha]
  | .meet _ _, ha => by
    simp only [sizeVal, sizeVal_agree hρ hζ ha.1, sizeVal_agree hρ hζ ha.2]

theorem SzEnv.cons_agree {ζ ζ' : SzEnv} {m : Nat} (h : ∀ x < m, ζ x = ζ' x) (β : Ordinal.{0}) :
    ∀ x < m + 1, SzEnv.cons β ζ x = SzEnv.cons β ζ' x
  | 0, _ => rfl
  | x + 1, hx => h x (by omega)

/-- Locally closed sizes do not depend on the bound-size environment. -/
theorem sizeVal_closed {Ψ : SizeCtx} {a : Size} (ha : SizeWf Ψ a) (ρ : SizeVal) (ζ ζ' : SzEnv) :
    sizeVal ρ ζ a = sizeVal ρ ζ' a :=
  sizeVal_agree (fun _ _ => rfl) (fun _ h => absurd h (Nat.not_lt_zero _)) ha

/-! ## Locally closed sizes and substitution -/

/-- A size without bound size variables. -/
def Size.LC : Size → Prop
  | .inf _ => True
  | .var _ _ => True
  | .bvar _ _ => False
  | .meet a b => a.LC ∧ b.LC

theorem Size.LC.of_wf {Ψ : SizeCtx} : ∀ {a : Size}, SizeWf Ψ a → a.LC
  | .inf _, _ => trivial
  | .var _ _, _ => trivial
  | .bvar _ _, h => absurd h (Nat.not_lt_zero _)
  | .meet _ _, h => ⟨Size.LC.of_wf h.1, Size.LC.of_wf h.2⟩

theorem sizeVal_lc (ρ : SizeVal) (ζ ζ' : SzEnv) : ∀ {a : Size}, a.LC → sizeVal ρ ζ a = sizeVal ρ ζ' a
  | .inf _, _ => rfl
  | .var _ _, _ => rfl
  | .bvar _ _, h => absurd h id
  | .meet _ _, h => by simp only [sizeVal, sizeVal_lc ρ ζ ζ' h.1, sizeVal_lc ρ ζ ζ' h.2]

theorem Size.LC.shift : ∀ {a : Size} (n : Nat), a.LC → (a.shift n).LC
  | .inf _, _, _ => trivial
  | .var _ _, _, _ => trivial
  | .bvar _ _, _, h => h
  | .meet _ _, n, h => ⟨Size.LC.shift n h.1, Size.LC.shift n h.2⟩

/-- Substitutions of locally closed sizes. -/
def LCSubst (σ : List (Nat × Size)) : Prop := ∀ i b, σ.lookup i = some b → b.LC

/-- The valuation induced by a size substitution. -/
noncomputable def substVal (ρ : SizeVal) (σ : List (Nat × Size)) : SizeVal := fun i =>
  match σ.lookup i with
  | some b => sizeVal ρ SzEnv.zero b
  | none => ρ i

theorem sizeVal_subst {σ : List (Nat × Size)} (hσ : LCSubst σ) (ρ : SizeVal) (ζ : SzEnv) :
    ∀ a : Size, sizeVal ρ ζ (a.subst σ) = sizeVal (substVal ρ σ) ζ a
  | .inf _ => rfl
  | .bvar _ _ => rfl
  | .var i n => by
    simp only [Size.subst, sizeVal, substVal]
    cases h : σ.lookup i with
    | none => rfl
    | some b =>
      simp only
      rw [sizeVal_shift, sizeVal_lc ρ ζ SzEnv.zero (hσ i b h)]
  | .meet a b => by
    simp only [Size.subst, sizeVal, sizeVal_subst hσ ρ ζ a, sizeVal_subst hσ ρ ζ b]

/-! ## Opening bound size variables -/

theorem sizeVal_openAt (ρ : SizeVal) (ζ : SzEnv) (k : Nat) {b : Size} (hb : b.LC) :
    ∀ a : Size, sizeVal ρ ζ (a.openAt k b) = sizeVal ρ (SzEnv.insert k (sizeVal ρ ζ b) ζ) a
  | .inf _ => rfl
  | .var _ _ => rfl
  | .bvar k' n => by
    by_cases h1 : k' = k
    · subst h1
      simp [Size.openAt, sizeVal, SzEnv.insert, sizeVal_shift]
    · by_cases h2 : k < k'
      · have h3 : ¬ k' < k := by omega
        simp [Size.openAt, h1, h2, h3, sizeVal, SzEnv.insert]
      · have h3 : k' < k := by omega
        simp [Size.openAt, h1, h2, h3, sizeVal, SzEnv.insert]
  | .meet a₁ a₂ => by
    simp only [Size.openAt, sizeVal, sizeVal_openAt ρ ζ k hb a₁, sizeVal_openAt ρ ζ k hb a₂]

end NishtAbel2024V5


