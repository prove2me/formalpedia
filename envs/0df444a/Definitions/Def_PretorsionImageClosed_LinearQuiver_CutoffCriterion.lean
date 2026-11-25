-- Prove2me | Definitions.Def_PretorsionImageClosed_LinearQuiver_CutoffCriterion
-- name    : PretorsionImageClosed_LinearQuiver_CutoffCriterion
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T05:51:01.425802+00:00
-- url     : https://prove2.me/theorems/859387cb-86cc-46a7-afde-a8e22d01075d
-- title:
--   Cutoff Criterion
-- statement:
--   Definitions and structural lemmas for Cutoff Criterion, from Haruhisa Enomoto (haruhisa-enomoto/pretorsion-image-closed; see pinned Apache-2.0 LICENSE)'s pinned Pretorsion theories and image-closed subcategories of finite-dimensional algebras development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/CutoffCriterion.lean

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Cutoffs
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_IntervalTraceReject
public import Definitions.Def_PretorsionImageClosed_Pretorsion_DirectSums
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_eq_bot_or_eq_suffix
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_imageSubobject_intervalIncl_comp_intervalProj
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_intervalIncl_comp
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_intervalSum
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_prop_cokernel_suffix_iff
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_prop_interval_of_prop_suffix
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_reject_interval_eq_suffix
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_reject_interval_eq_top
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_suffix_eq_bot_of_lt
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_suffix_le_suffix
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_suffix_self
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_trace_interval_eq_bot
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_trace_interval_eq_suffix
public import Theorems.Thm_PretorsionImageClosed_Statement_IsPretorsionTheory_isQuotientClosed
public import Theorems.Thm_PretorsionImageClosed_Statement_IsPretorsionTheory_isSubobjectClosed
public import Theorems.Thm_PretorsionImageClosed_Statement_IsPretorsionTheory_prop_iff_prop_cokernel_reject
public import Theorems.Thm_PretorsionImageClosed_Statement_IsPretorsionTheory_prop_iff_prop_trace
public import Theorems.Thm_PretorsionImageClosed_Statement_IsShortPreexact_biprod
public import Theorems.Thm_PretorsionImageClosed_Statement_IsShortPreexact_of_iso
public import Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_ext
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_le_def
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_prop_cokernel_reject
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_reject_eq_bot_iff
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_trace_eq_top_iff
public import Theorems.Thm_PretorsionImageClosed_Statement_TraceRejectCondition_isPrecokernel
public import Theorems.Thm_PretorsionImageClosed_Statement_TraceRejectCondition_isPrekernel
public import Theorems.Thm_PretorsionImageClosed_Statement_isShortPreexact_id
public import Theorems.Thm_PretorsionImageClosed_Statement_isTrivial_of_closed
public import Theorems.Thm_PretorsionImageClosed_Statement_reject_coe_eq_mk_ofLE
public import Theorems.Thm_PretorsionImageClosed_Statement_traceRejectCondition_of_eq_top
public import Theorems.Thm_PretorsionImageClosed_Statement_traceRejectCondition_of_prop
public import Theorems.Thm_PretorsionImageClosed_Statement_traceRejectCondition_of_quotient

set_option autoImplicit true
@[expose] public section
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace PretorsionImageClosed
open CategoryTheory Limits Statement Subcategory
namespace LinearQuiver
universe u
variable {k : Type u} [Field k] {n : ℕ}
theorem isPretorsionTheory_of_forall_interval {T F : Subcategory (Statement.LinRep k n)}
    (hT : T.IsQuotientClosed) (hF : F.IsSubobjectClosed)
    (h : ∀ c d : Fin n, c ≤ d → TraceRejectCondition T F (interval k c d)) :
    IsPretorsionTheory T.prop F.prop := by
  refine ⟨fun f hX hY => isTrivial_of_closed hT hF f hX hY, fun X => ?_⟩
  induction intervalSum X with
  | zero hz =>
    exact ⟨_, _, 𝟙 _, 𝟙 _, T.prop_of_isZero hz, F.prop_of_isZero hz,
      isShortPreexact_id (Zs := T ⊓ F) ⟨T.prop_of_isZero hz, F.prop_of_isZero hz⟩⟩
  | @step X X' a d had _ e ih =>
    obtain ⟨T', F', u, v, hT', hF', hs⟩ := ih
    have hc := h a d had
    exact ⟨_, _, biprod.map (T.trace (interval k a d)).arrow u ≫ e.inv,
      e.hom ≫ biprod.map (cokernel.π (F.reject (interval k a d)).arrow) v,
      T.prop_biprod (T.prop_trace _) hT', F.prop_biprod (F.prop_cokernel_reject _) hF',
      (IsShortPreexact.biprod (Zs := T ⊓ F) ⟨hc.isPrekernel hT hF, hc.isPrecokernel hT hF⟩ hs).of_iso
        e.symm⟩
def ColumnCriterion (β : RowCutoff n) (α : ColCutoff n) (d : Fin n) : Prop :=
  α.α d = 0 ∨ ∃ e : Fin n, e.val + 1 = α.α d ∧ d.val < β.β e ∧ ∀ a, a < e → β.β a ≠ d.val
def Criterion (β : RowCutoff n) (α : ColCutoff n) : Prop :=
  ∀ d, ColumnCriterion β α d
theorem beta_lt_of_criterion (β : RowCutoff n) (α : ColCutoff n) (hcrit : Criterion β α)
    {c d u : Fin n} (hcu : c ≤ u) (hud : u ≤ d)
    (hmin : ∀ i, c ≤ i → i < u → ¬ d.val < β.β i) (bp : ℕ) (hcb : c.val ≤ bp)
    (hP2 : ∀ j : Fin n, bp ≤ j.val → j ≤ d → c.val < α.α j) :
    ∀ i, c ≤ i → i < u → β.β i < bp := by
  intro i hci hiu
  by_contra hcon
  have hbi : bp ≤ β.β i := not_lt.1 hcon
  have hne : (Finset.univ.filter (fun i : Fin n => c ≤ i ∧ i < u ∧ bp ≤ β.β i)).Nonempty :=
    ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hci, hiu, hbi⟩⟩
  obtain ⟨i₀, hi₀, hmax⟩ := Finset.exists_max_image _ β.β hne
  rw [Finset.mem_filter] at hi₀
  obtain ⟨-, hci₀, hi₀u, hbi₀⟩ := hi₀
  have hβd : β.β i₀ ≤ d.val := not_lt.1 (hmin i₀ hci₀ hi₀u)
  have hjd : (⟨β.β i₀, lt_of_le_of_lt hβd d.isLt⟩ : Fin n) ≤ d := Fin.le_def.2 hβd
  have hcj : c.val < α.α ⟨β.β i₀, lt_of_le_of_lt hβd d.isLt⟩ := hP2 _ hbi₀ hjd
  rcases hcrit ⟨β.β i₀, lt_of_le_of_lt hβd d.isLt⟩ with h0 | ⟨e', he', hje', hprev⟩
  · omega
  · have hce' : c ≤ e' := Fin.le_def.2 (by omega)
    have he'i₀ : ¬ i₀ < e' := fun hlt => hprev i₀ hlt rfl
    have he'ne : e' ≠ i₀ := by
      intro h
      subst h
      exact lt_irrefl _ hje'
    have he'lt : e' < i₀ := lt_of_le_of_ne (not_lt.1 he'i₀) he'ne
    have hmem : e' ∈ Finset.univ.filter (fun i : Fin n => c ≤ i ∧ i < u ∧ bp ≤ β.β i) :=
      Finset.mem_filter.2 ⟨Finset.mem_univ _, hce', he'lt.trans hi₀u, (hbi₀.trans_lt hje').le⟩
    exact absurd hje' (not_lt.2 (hmax e' hmem))
theorem traceRejectCondition_interval (β : RowCutoff n) (α : ColCutoff n) (hcrit : Criterion β α)
    {c d : Fin n} (hcd : c ≤ d) :
    TraceRejectCondition (β.subcategory (k := k)) α.subcategory (interval k c d) := by
  have hT : (β.subcategory (k := k)).IsQuotientClosed := β.isQuotientClosed
  have hF : (α.subcategory (k := k)).IsSubobjectClosed := α.isSubobjectClosed
  have hTi : ∀ {a d : Fin n}, a ≤ d →
      ((β.subcategory (k := k)).prop (interval k a d) ↔ d.val < β.β a) :=
    fun h => β.prop_interval_iff h
  have hFi : ∀ {a d : Fin n}, a ≤ d →
      ((α.subcategory (k := k)).prop (interval k a d) ↔ α.α d ≤ a.val) :=
    fun h => α.prop_interval_iff h
  by_cases hXF : α.α d ≤ c.val
  · exact traceRejectCondition_of_prop hT hF ((hFi hcd).2 hXF)
  have hcα : c.val < α.α d := not_le.1 hXF
  -- the pivot row of column `d`
  obtain ⟨e, he, hde, -⟩ : ∃ e : Fin n, e.val + 1 = α.α d ∧ d.val < β.β e ∧
      ∀ a, a < e → β.β a ≠ d.val := by
    rcases hcrit d with h0 | h
    · omega
    · exact h
  have hce : c ≤ e := Fin.le_def.2 (by omega)
  have hed : e ≤ d := Fin.le_def.2 (by have := α.α_le d; omega)
  -- the trace row `u`
  set S := Finset.univ.filter (fun i : Fin n => c ≤ i ∧ i ≤ d ∧ d.val < β.β i) with hS
  have hSne : S.Nonempty := ⟨e, Finset.mem_filter.2 ⟨Finset.mem_univ _, hce, hed, hde⟩⟩
  set u := S.min' hSne with hu
  have huS : u ∈ S := Finset.min'_mem S hSne
  rw [Finset.mem_filter] at huS
  obtain ⟨-, hcu, hud, hdu⟩ := huS
  have hmin : ∀ i, c ≤ i → i < u → ¬ d.val < β.β i := by
    intro i hci hiu hlt
    have hui : u ≤ i :=
      Finset.min'_le S i (Finset.mem_filter.2 ⟨Finset.mem_univ _, hci, hiu.le.trans hud, hlt⟩)
    exact absurd hiu (not_lt.2 hui)
  have ht : (β.subcategory (k := k)).trace (interval k c d) = suffix c d u hcu :=
    trace_interval_eq_suffix hT hcu ((hTi hud).2 hdu)
      (fun i hci hiu h => hmin i hci hiu ((hTi (hiu.le.trans hud)).1 h))
  -- the columns `ℓ ∈ [c, d]` with `M_{c,ℓ} ∈ F`
  set Q := Finset.univ.filter (fun ℓ : Fin n => c ≤ ℓ ∧ ℓ ≤ d ∧ α.α ℓ ≤ c.val) with hQ
  by_cases hQne : Q.Nonempty
  · -- `b` is the last such column and `v = b + 1`
    set b := Q.max' hQne with hb
    have hbQ : b ∈ Q := Finset.max'_mem Q hQne
    rw [Finset.mem_filter] at hbQ
    obtain ⟨-, hcb, hbd, hαb⟩ := hbQ
    have hbd' : b < d := by
      refine lt_of_le_of_ne hbd fun h => ?_
      rw [h] at hαb
      exact hXF hαb
    obtain ⟨v, hv⟩ : ∃ v : Fin n, b.val + 1 = v.val :=
      ⟨⟨b.val + 1, by have := Fin.lt_def.1 hbd'; omega⟩, rfl⟩
    have hcv : c ≤ v := Fin.le_def.2 (by have := Fin.le_def.1 hcb; omega)
    have hP2 : ∀ j : Fin n, v.val ≤ j.val → j ≤ d → c.val < α.α j := by
      intro j hvj hjd
      by_contra hle
      have hcj : c ≤ j := Fin.le_def.2 (by have := Fin.le_def.1 hcb; omega)
      have hjQ : j ∈ Q := Finset.mem_filter.2 ⟨Finset.mem_univ _, hcj, hjd, not_lt.1 hle⟩
      have hjb : j ≤ b := Finset.le_max' Q j hjQ
      have := Fin.le_def.1 hjb
      omega
    have hr : (α.subcategory (k := k)).reject (interval k c d) = suffix c d v hcv :=
      reject_interval_eq_suffix hF hbd hcv hv ((hFi hcb).2 hαb) (fun j hbj hjd hFj =>
        absurd ((hFi (hcb.trans hbj.le)).1 hFj)
          (not_le.2 (hP2 j (by have := Fin.lt_def.1 hbj; omega) hjd)))
    -- Step 1
    have hstep1 : ∀ i, c ≤ i → i < u → β.β i < v.val :=
      beta_lt_of_criterion β α hcrit hcu hud hmin v.val (Fin.le_def.1 hcv) hP2
    -- Step 2: `u ≤ v`, so `r(X) ⊆ t(X)`
    have huv : u ≤ v := by
      rcases eq_or_lt_of_le hcu with hcu' | hcu'
      · rw [← hcu']
        exact hcv
      · obtain ⟨i, hi⟩ : ∃ i : Fin n, i.val + 1 = u.val :=
          ⟨⟨u.val - 1, by omega⟩, by simp only; have := Fin.lt_def.1 hcu'; omega⟩
        have hci : c ≤ i := Fin.le_def.2 (by have := Fin.lt_def.1 hcu'; omega)
        have hiu : i < u := Fin.lt_def.2 (by omega)
        have h1 := hstep1 i hci hiu
        have h2 := β.le_β i
        exact Fin.le_def.2 (by omega)
    have h1 : (α.subcategory (k := k)).reject (interval k c d) ≤
        (β.subcategory (k := k)).trace (interval k c d) := by
      rw [hr, ht]
      exact suffix_le_suffix hcu huv
    -- no quotient `M_{u,j}` with `j ≥ v` lies in `F`
    have hnoF : ∀ j : Fin n, v.val ≤ j.val → j ≤ d → ¬ α.α j ≤ u.val := by
      intro j hvj hjd hle
      have hcj := hP2 j hvj hjd
      rcases hcrit j with h0 | ⟨e', he', hje', -⟩
      · omega
      · have hce' : c ≤ e' := Fin.le_def.2 (by omega)
        have he'u : e' < u := Fin.lt_def.2 (by omega)
        have := hstep1 e' hce' he'u
        omega
    -- `r(t(X)) = r(X)`
    have hA : (α.subcategory (k := k)).reject (interval k u d) = suffix u d v huv := by
      rcases eq_or_lt_of_le huv with huv' | huv'
      · have key : ∀ (v' : Fin n) (h : u ≤ v'), v' = u → suffix (k := k) u d v' h = ⊤ := by
          rintro _ _ rfl
          exact suffix_self _ _
        rw [key v huv huv'.symm]
        exact reject_interval_eq_top hF hud (fun j huj hjd hFj =>
          hnoF j (by have := Fin.le_def.1 huj; omega) hjd ((hFi huj).1 hFj))
      · have hub : u ≤ b := Fin.le_def.2 (by have := Fin.lt_def.1 huv'; omega)
        exact reject_interval_eq_suffix hF hbd huv hv ((hFi hub).2 (hαb.trans (Fin.le_def.1 hcu)))
          (fun j hbj hjd hFj =>
            hnoF j (by have := Fin.lt_def.1 hbj; omega) hjd ((hFi (hub.trans hbj.le)).1 hFj))
    have h2 : (α.subcategory (k := k)).reject
        ((β.subcategory (k := k)).trace (interval k c d) : Statement.LinRep k n) =
        Subobject.mk (Subobject.ofLE _ _ h1) :=
      reject_coe_eq_mk_ofLE hF h1 (intervalIncl k d hcu) (intervalIncl k d huv) ht
        (by
          rw [hr]
          exact Subobject.mk_eq_mk_of_comm _ _ (Iso.refl _)
            (by rw [Iso.refl_hom, Category.id_comp, intervalIncl_comp])) hA
    -- Step 3: `t(X / r(X)) = t(X) / r(X)`
    have h3 : (β.subcategory (k := k)).trace (interval k c b) =
        imageSubobject (((β.subcategory (k := k)).trace (interval k c d)).arrow ≫
          intervalProj k c hbd) := by
      rw [ht, suffix, ← Subobject.underlyingIso_hom_comp_eq_mk, Category.assoc,
        imageSubobject_iso_comp, imageSubobject_intervalIncl_comp_intervalProj]
      rcases le_or_gt u b with hub | hbu
      · exact trace_interval_eq_suffix hT hcu ((hTi hub).2 (lt_of_le_of_lt (Fin.le_def.1 hbd) hdu))
          (fun i hci hiu h => by
            have := hstep1 i hci hiu
            have := (hTi (hiu.le.trans hub)).1 h
            omega)
      · rw [suffix_eq_bot_of_lt hcu hbu]
        exact trace_interval_eq_bot (fun i hci hib h => by
          have := hstep1 i hci (lt_of_le_of_lt hib hbu)
          have := (hTi hib).1 h
          omega)
    exact traceRejectCondition_of_quotient hT (intervalProj k c hbd)
      (by rw [kernelSubobject_intervalProj hbd hcv hv, hr]) h1 h2 h3
  · -- no quotient of `X` lies in `F`: `r(X) = X`, and Step 1 forces `t(X) = X`
    have hnone : ∀ ℓ : Fin n, c ≤ ℓ → ℓ ≤ d → ¬ α.α ℓ ≤ c.val := fun ℓ hcℓ hℓd hle =>
      hQne ⟨ℓ, Finset.mem_filter.2 ⟨Finset.mem_univ _, hcℓ, hℓd, hle⟩⟩
    have hP2 : ∀ j : Fin n, c.val ≤ j.val → j ≤ d → c.val < α.α j := fun j hcj hjd =>
      not_le.1 (hnone j (Fin.le_def.2 hcj) hjd)
    have hstep1 := beta_lt_of_criterion β α hcrit hcu hud hmin c.val le_rfl hP2
    have huc : u = c := by
      rcases eq_or_lt_of_le hcu with h | h
      · exact h.symm
      · exfalso
        have := hstep1 c le_rfl h
        have := β.le_β c
        omega
    have ht' : (β.subcategory (k := k)).trace (interval k c d) = ⊤ := by
      rw [trace_eq_top_iff hT, hTi hcd, ← huc]
      exact hdu
    have hr' : (α.subcategory (k := k)).reject (interval k c d) = ⊤ :=
      reject_interval_eq_top hF hcd (fun j hcj hjd hFj => hnone j hcj hjd ((hFi hcj).1 hFj))
    exact traceRejectCondition_of_eq_top hT hF hr' ht'
theorem criterion_of_isPretorsionTheory (β : RowCutoff n) (α : ColCutoff n)
    (hP : IsPretorsionTheory (β.subcategory (k := k)).prop α.subcategory.prop) : Criterion β α := by
  intro d
  have hTi : ∀ {a d : Fin n}, a ≤ d →
      ((β.subcategory (k := k)).prop (interval k a d) ↔ d.val < β.β a) :=
    fun h => β.prop_interval_iff h
  have hFi : ∀ {a d : Fin n}, a ≤ d →
      ((α.subcategory (k := k)).prop (interval k a d) ↔ α.α d ≤ a.val) :=
    fun h => α.prop_interval_iff h
  by_cases h0 : α.α d = 0
  · exact Or.inl h0
  right
  obtain ⟨e, he⟩ : ∃ e : Fin n, e.val + 1 = α.α d :=
    ⟨⟨α.α d - 1, by have := α.α_le d; have := d.isLt; omega⟩, by simp only; omega⟩
  have hed : e ≤ d := Fin.le_def.2 (by have := α.α_le d; omega)
  refine ⟨e, he, ?_, ?_⟩
  · -- `M_{e,d} ∈ T`: otherwise `t(M_{e,d}) ∈ F` and Corollary 2.13 gives `M_{e,d} ∈ F`
    by_contra hlt
    have hXF : ¬ (α.subcategory (k := k)).prop (interval k e d) := fun h => by
      have := (hFi hed).1 h
      omega
    apply hXF
    rw [hP.prop_iff_prop_trace]
    refine ⟨(β.subcategory (k := k)).prop_trace _, ?_⟩
    rcases eq_bot_or_eq_suffix ((β.subcategory (k := k)).trace (interval k e d)) with
      h0' | ⟨u', heu', hu'd, hK⟩
    · rw [h0']
      exact (α.subcategory (k := k)).prop_of_isZero
        ((isZero_zero _).of_iso Subobject.botCoeIsoZero)
    · have hu'T : (β.subcategory (k := k)).prop (interval k u' d) :=
        prop_interval_of_prop_suffix _ heu' (by rw [← hK]; exact Subcategory.prop_trace _ _)
      have hne : e ≠ u' := by
        intro h
        subst h
        exact hlt ((hTi hed).1 hu'T)
      have heu'' : e < u' := lt_of_le_of_ne heu' hne
      rw [hK]
      exact (α.subcategory (k := k)).prop_of_iso (Subobject.underlyingIso _).symm
        ((hFi hu'd).2 (by have := Fin.lt_def.1 heu''; omega))
  · -- no earlier row ends at `d`: otherwise `X/r(X) ∈ T ∩ F` for `X = M_{a,d} ∉ T`
    intro a hae hβa
    have had : a ≤ d := hae.le.trans hed
    have hXT : ¬ (β.subcategory (k := k)).prop (interval k a d) := fun h => by
      have := (hTi had).1 h
      omega
    apply hXT
    rw [hP.prop_iff_prop_cokernel_reject]
    rcases eq_bot_or_eq_suffix ((α.subcategory (k := k)).reject (interval k a d)) with
      h0' | ⟨v, hav, hvd, hK⟩
    · exfalso
      have := (hFi had).1 ((reject_eq_bot_iff hP.isSubobjectClosed).1 h0')
      have := Fin.lt_def.1 hae
      omega
    · rw [hK]
      rcases eq_or_lt_of_le hav with hav' | hav'
      · have key : ∀ (v' : Fin n) (h : a ≤ v'), v' = a → suffix (k := k) a d v' h = ⊤ := by
          rintro _ _ rfl
          exact suffix_self _ _
        rw [key v hav hav'.symm]
        exact ⟨(β.subcategory (k := k)).prop_of_isZero ((isZero_zero _).of_iso (cokernel.ofEpi _)),
          (α.subcategory (k := k)).prop_of_isZero ((isZero_zero _).of_iso (cokernel.ofEpi _))⟩
      · obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : Fin n, ℓ.val + 1 = v.val :=
          ⟨⟨v.val - 1, by omega⟩, by simp only; have := Fin.lt_def.1 hav'; omega⟩
        have hℓd : ℓ ≤ d := Fin.le_def.2 (by have := Fin.le_def.1 hvd; omega)
        have haℓ : a ≤ ℓ := Fin.le_def.2 (by have := Fin.lt_def.1 hav'; omega)
        refine ⟨(prop_cokernel_suffix_iff _ hℓd hav hℓ).2
          ((hTi haℓ).2 (by have := Fin.le_def.1 hvd; omega)), ?_⟩
        rw [← hK]
        exact Subcategory.prop_cokernel_reject _ _
theorem isPretorsionTheory_iff_criterion (β : RowCutoff n) (α : ColCutoff n) :
    IsPretorsionTheory (β.subcategory (k := k)).prop α.subcategory.prop ↔ Criterion β α :=
  ⟨criterion_of_isPretorsionTheory β α, fun h =>
    isPretorsionTheory_of_forall_interval β.isQuotientClosed α.isSubobjectClosed
      (fun _ _ hcd => traceRejectCondition_interval β α h hcd)⟩
def CutoffPair (n : ℕ) : Type := {p : RowCutoff n × ColCutoff n // Criterion p.1 p.2}
def pretorsionEquiv : PretorsionTheory (Statement.LinRep k n) ≃ CutoffPair n where
  toFun P := ⟨(rowCutoff P.T, colCutoff P.F),
    (isPretorsionTheory_iff_criterion (k := k) (rowCutoff P.T) (colCutoff P.F)).1 (by
    rw [rowCutoff_subcategory P.isPretorsionTheory.isQuotientClosed,
      colCutoff_subcategory P.isPretorsionTheory.isSubobjectClosed]
    exact P.isPretorsionTheory)⟩
  invFun p := ⟨p.1.1.subcategory, p.1.2.subcategory, (isPretorsionTheory_iff_criterion _ _).2 p.2⟩
  left_inv P := PretorsionTheory.ext (rowCutoff_subcategory P.isPretorsionTheory.isQuotientClosed)
    (colCutoff_subcategory P.isPretorsionTheory.isSubobjectClosed)
  right_inv p := Subtype.ext (Prod.ext (rowCutoff_of_subcategory _) (colCutoff_of_subcategory _))
instance : Finite (RowCutoff n) :=
  Finite.of_injective (fun β : RowCutoff n => fun a => (⟨β.β a, Nat.lt_succ_of_le (β.β_le a)⟩ : Fin (n + 1)))
    (by
      intro β β' h
      ext a
      have := congrArg Fin.val (congrFun h a)
      simpa using this)
instance : Finite (ColCutoff n) :=
  Finite.of_injective (fun α : ColCutoff n => fun d =>
      (⟨α.α d, by have := α.α_le d; have := d.isLt; omega⟩ : Fin (n + 1)))
    (by
      intro α α' h
      ext d
      have := congrArg Fin.val (congrFun h d)
      simpa using this)
instance : Finite (CutoffPair n) := Subtype.finite
instance : Finite (PretorsionTheory (Statement.LinRep k n)) :=
  Finite.of_equiv _ (pretorsionEquiv (k := k) (n := n)).symm
end LinearQuiver
end PretorsionImageClosed


