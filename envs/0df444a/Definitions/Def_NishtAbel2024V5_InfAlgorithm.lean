-- Prove2me | Definitions.Def_NishtAbel2024V5_InfAlgorithm
-- name    : NishtAbel2024V5_InfAlgorithm
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-07T04:30:22.101207+00:00
-- url     : https://prove2.me/theorems/1eefe7ee-d230-49de-9153-6bb7a4c021e9
-- title:
--   Chapter 6.1–6.5 (V5 Support): Encoding (Thm 7), Polarity (Lemmas 3–5), Constraints (Thms 10–12), and Algorithms 1–2 (Thms 14–15)
-- statement:
--   Completes Chapter 6 of Nisht and Abel (2024): proves well-kindedness and exclusive polarity of signature encoding (`theorem_7`, `lemma_3`), rigid variable polarity invariants for pattern and copattern spine elaboration (`lemma_4`, `lemma_5`), constraint orientation in subtype comparison and call-site checking (`theorem_10`, `theorems_11_and_12`), soundness of the checked Algorithm 1 solver (`theorem_14`), well-typedness of mutual blocks accepted by Algorithm 2 (`algorithm2_typing`), and end-to-end termination soundness (`theorem_15_proof`, Theorem 15).
-- source:
--   Nisht & Abel 2024, Kind Inference and Termination Checking in a Language with Co-Patterns and Size-Change Termination, https://urn.kb.se/resolve?urn=urn:nbn:se:chalmers:diva-542843, Chapter 6, Sections 6.1-6.5, pp. 42-61, Theorems 7, 10-12, 14-15 & Lemmas 3-5

import Definitions.Def_NishtAbel2024V5_InfCore
import Definitions.Def_NishtAbel2024V5_SemFundamental

/-! ## Solutions/V5/InfEncode.lean -/

/-! # V5 inference: signature encoding (Theorem 7 and Lemma 3) -/

namespace NishtAbel2024V5

/-! ## Theorem 7: Kinding of encoded types -/

mutual

theorem Unsized.eraseSz_eq : ∀ {A : Ty}, Unsized A → A.eraseSz = A
  | _, .unit => rfl
  | _, .prod hA hB => by simp [Ty.eraseSz, hA.eraseSz_eq, hB.eraseSz_eq]
  | _, .arr hA hB => by simp [Ty.eraseSz, hA.eraseSz_eq, hB.eraseSz_eq]
  | _, .var _ => rfl
  | _, .fvar _ => rfl
  | _, .lam hF => by simp [Ty.eraseSz, hF.eraseSz_eq]
  | _, .app hF hG => by simp [Ty.eraseSz, hF.eraseSz_eq, hG.eraseSz_eq]
  | _, .mu hS => by simp [Ty.eraseSz, hS.eraseSzList_eq]
  | _, .nu hR => by simp [Ty.eraseSz, hR.eraseSzList_eq]
  | _, .allT hB => by simp [Ty.eraseSz, hB.eraseSz_eq]
  | _, .exT hB => by simp [Ty.eraseSz, hB.eraseSz_eq]

theorem UnsizedList.eraseSzList_eq : ∀ {S : List Ty}, UnsizedList S → Ty.eraseSzList S = S
  | _, .nil => rfl
  | _, .cons hT hS => by simp [Ty.eraseSzList, hT.eraseSz_eq, hS.eraseSzList_eq]

end

theorem Unsized.ekinding {Δ : KCtx} {Δb : BCtx} {A : Ty} {κ : Kind}
    (h : Unsized A) (hk : Kinding [] Δ Δb 0 A κ) : EKinding Δ Δb A κ := by
  unfold EKinding
  rwa [h.eraseSz_eq]

theorem encode_dom_nodup {πs : Pol} {ok : Nat → Prop} {π : Pol} {Δ : KCtx} {Δb : BCtx}
    {G G' : Ty} {Ψ : SizeCtx} (h : Encode πs ok π Δ Δb G Ψ G') : Ψ.dom.Nodup := by
  refine Encode.rec
    (motive_1 := fun _ _ _ _ Ψ _ _ => Ψ.dom.Nodup)
    (motive_2 := fun _ _ _ _ Ψ _ _ => Ψ.dom.Nodup)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  · simp [SizeCtx.dom]
  · intro _ _ _ _ _ _ _ Ψ₁ Ψ₂ _ _ hdisj ih₁ ih₂
    simp only [SizeCtx.dom, List.map_append]
    exact List.nodup_append.mpr ⟨ih₁, ih₂, fun x hx y hy hxy => hdisj x hx (hxy ▸ hy)⟩
  · intro _ _ _ _ _ _ _ Ψ₁ Ψ₂ _ _ hdisj ih₁ ih₂
    simp only [SizeCtx.dom, List.map_append]
    exact List.nodup_append.mpr ⟨ih₁, ih₂, fun x hx y hy hxy => hdisj x hx (hxy ▸ hy)⟩
  · intro _ _ _ _; simp [SizeCtx.dom]
  · intro _ _ _ _; simp [SizeCtx.dom]
  · intro _ _ _ _ _ _ _ _ ih; exact ih
  · intro _ _ _ _ _ _ _ _ _ _ _ Ψ₁ Ψ₂ _ _ _ hdisj ih₁ ih₂
    simp only [SizeCtx.dom, List.map_append]
    exact List.nodup_append.mpr ⟨ih₁, ih₂, fun x hx y hy hxy => hdisj x hx (hxy ▸ hy)⟩
  · intro _ _ _ _ _ Ψ i _ _ hi _ ih
    simp only [SizeCtx.dom, List.map_cons]
    exact List.nodup_cons.mpr ⟨hi, ih⟩
  · intro _ _ _ _ _ _ _ _ ih; exact ih
  · intro _ _ _ _ _ Ψ i _ _ hi _ ih
    simp only [SizeCtx.dom, List.map_cons]
    exact List.nodup_cons.mpr ⟨hi, ih⟩
  · intro _ _ _ _ _ _ _ _ ih; exact ih
  · intro _ _ _ _ _ _ _ _ ih; exact ih
  · intro _ _ _ _ _ _ _ _ ih; exact ih
  · simp [SizeCtx.dom]
  · intro _ _ _ _ _ _ _ Ψ₁ Ψ₂ _ _ hdisj ih₁ ih₂
    simp only [SizeCtx.dom, List.map_append]
    exact List.nodup_append.mpr ⟨ih₁, ih₂, fun x hx y hy hxy => hdisj x hx (hxy ▸ hy)⟩

theorem sizeCtxWf_of_nodup_inf {Ψ : SizeCtx} (hn : Ψ.dom.Nodup) (hb : ∀ p ∈ Ψ, p.2 = .inf 0) :
    SizeCtxWf Ψ := by
  induction Ψ using List.reverseRecOn with
  | nil => exact .nil
  | append_singleton Ψ p ih =>
    rcases p with ⟨i, a⟩
    simp only [SizeCtx.dom, List.map_append, List.map_cons, List.map_nil] at hn
    obtain ⟨hnΨ, _, hdisj⟩ := List.nodup_append.mp hn
    have hi : i ∉ SizeCtx.dom Ψ := fun hmem => hdisj i hmem i (by simp) rfl
    have ha : a = .inf 0 := hb (i, a) (by simp)
    subst ha
    exact .snoc (ih hnΨ (fun q hq => hb q (List.mem_append_left _ hq))) hi trivial

theorem encode_sizeCtxWf {πs : Pol} {ok : Nat → Prop} {π : Pol} {Δ : KCtx} {Δb : BCtx}
    {G G' : Ty} {Ψ : SizeCtx} (h : Encode πs ok π Δ Δb G Ψ G') : SizeCtxWf Ψ :=
  sizeCtxWf_of_nodup_inf (encode_dom_nodup h) (encode_facts h).2.2.2

/-- **Theorem 7** (Encoding of function signatures, Section 6.1): if `A` has size-erased kind `κ`
and `π; Δ ⊢_SCT^{πs} A ⇒ Ψ; A'`, then `⊢ Ψ` and `Ψ; Δ ⊢ A' : κ`. -/
theorem theorem_7 {πs : Pol} {ok : Nat → Prop} {π : Pol} {Δ : KCtx} {Δb : BCtx} {A A' : Ty}
    {Ψ : SizeCtx} {κ : Kind} (hk : EKinding Δ Δb A κ) (henc : Encode πs ok π Δ Δb A Ψ A') :
    SizeCtxWf Ψ ∧ Kinding Ψ Δ Δb 0 A' κ := by
  obtain ⟨herase, hswf, _, _⟩ := encode_facts henc
  exact ⟨encode_sizeCtxWf henc, kinding_of_erase hk herase hswf⟩

theorem EncodedDecl.wf {d d' : FunDecl} (h : EncodedDecl d d') :
    SizeCtxWf d'.sizeParams ∧ KindingC d'.sizeParams [] d'.ty .star :=
  theorem_7 h.2.2.2.2.1 h.2.2.2.2.2

/-! ## Lemma 3: Polarities of encoded size variables -/

def FixKind.other : FixKind → FixKind
  | .mu => .nu
  | .nu => .mu

def FixKind.encPol (πs : Pol) : FixKind → Pol
  | .mu => πs
  | .nu => πs.negate

theorem SizeWfAt.fvars_sub {Ψ : SizeCtx} {m : Nat} :
    ∀ {a : Size}, SizeWfAt Ψ m a → ∀ i ∈ a.fvars, i ∈ Ψ.dom
  | .inf _, _, _, hi => by simp [Size.fvars] at hi
  | .var j _, h, i, hi => by
    simp only [Size.fvars, List.mem_singleton] at hi
    subst hi; exact h
  | .bvar _ _, _, _, hi => by simp [Size.fvars] at hi
  | .meet a b, ⟨ha, hb⟩, i, hi => by
    simp only [Size.fvars, List.mem_append] at hi
    rcases hi with hi | hi
    · exact ha.fvars_sub i hi
    · exact hb.fvars_sub i hi

theorem SizesWf.sizeVars_sub {Ψ : SizeCtx} {m : Nat} {A : Ty} (h : SizesWf Ψ m A) :
    ∀ i ∈ A.sizeVars, i ∈ Ψ.dom := by
  induction h with
  | unit | var | fvar => intro i hi; simp [Ty.sizeVars] at hi
  | prod _ _ ihA ihB | arr _ _ ihA ihB | app _ _ ihA ihB =>
    intro i hi
    simp only [Ty.sizeVars, List.mem_append] at hi
    rcases hi with hi | hi
    · exact ihA i hi
    · exact ihB i hi
  | lam _ ih | allT _ ih | exT _ ih =>
    intro i hi; exact ih i hi
  | allS ha _ ih | exS ha _ ih =>
    intro i hi
    simp only [Ty.sizeVars, List.mem_append] at hi
    rcases hi with hi | hi
    · exact ha.fvars_sub i hi
    · exact ih i hi
  | @mu _ a S ha hS ih =>
    intro i hi
    simp only [Ty.sizeVars, List.mem_append] at hi
    rcases hi with hi | hi
    · exact ha.fvars_sub i hi
    · clear ha hS
      induction S with
      | nil => simp [Ty.sizeVarsList] at hi
      | cons T S ihS =>
        simp only [Ty.sizeVarsList, List.mem_append] at hi
        rcases hi with hi | hi
        · exact ih T (by simp) i hi
        · exact ihS (fun U hU => ih U (by simp [hU])) hi
  | @nu _ a R ha hR ih =>
    intro i hi
    simp only [Ty.sizeVars, List.mem_append] at hi
    rcases hi with hi | hi
    · exact ha.fvars_sub i hi
    · clear ha hR
      induction R with
      | nil => simp [Ty.sizeVarsList] at hi
      | cons T R ihR =>
        simp only [Ty.sizeVarsList, List.mem_append] at hi
        rcases hi with hi | hi
        · exact ih T (by simp) i hi
        · exact ihR (fun U hU => ih U (by simp [hU])) hi

theorem encode_sizeVars_sub {πs : Pol} {ok : Nat → Prop} {π : Pol} {Δ : KCtx} {Δb : BCtx}
    {G G' : Ty} {Ψ : SizeCtx} (h : Encode πs ok π Δ Δb G Ψ G') :
    ∀ i ∈ G'.sizeVars, i ∈ Ψ.dom :=
  (encode_facts h).2.1.sizeVars_sub

theorem encodeList_sizeVars_sub {πs : Pol} {ok : Nat → Prop} {π : Pol} {Δ : KCtx} {Δb : BCtx}
    {S S' : List Ty} {Ψ : SizeCtx} (h : EncodeList πs ok π Δ Δb S Ψ S') :
    ∀ i ∈ Ty.sizeVarsList S', i ∈ Ψ.dom := by
  induction S' generalizing S Ψ with
  | nil => intro i hi; simp [Ty.sizeVarsList] at hi
  | cons T' S' ih =>
    cases h with
    | cons hT hS _ =>
      intro i hi
      simp only [Ty.sizeVarsList, List.mem_append, SizeCtx.dom, List.map_append] at hi ⊢
      rcases hi with hi | hi
      · exact Or.inl (encode_sizeVars_sub hT i hi)
      · exact Or.inr (ih hS i hi)

theorem mem_sizeVarsList_of_mem {S : List Ty} {T : Ty} (hT : T ∈ S) {i : Nat}
    (hi : i ∈ T.sizeVars) : i ∈ Ty.sizeVarsList S := by
  induction S with
  | nil => simp at hT
  | cons A S ih =>
    simp only [Ty.sizeVarsList, List.mem_append]
    rcases List.mem_cons.mp hT with rfl | hT
    · exact Or.inl hi
    · exact Or.inr (ih hT)

theorem SizeOcc.mem_sizeVars {fk : FixKind} {i : Nat} {Δ : KCtx} {Δb : BCtx} {π : Pol} {A : Ty}
    (h : SizeOcc fk i Δ Δb π A) : i ∈ A.sizeVars := by
  induction h with
  | prodL _ ih | arrL _ ih | appF _ ih =>
    simp only [Ty.sizeVars, List.mem_append]; exact Or.inl ih
  | prodR _ ih | arrR _ ih | appG _ _ ih =>
    simp only [Ty.sizeVars, List.mem_append]; exact Or.inr ih
  | lam _ ih | allT _ ih | exT _ ih => exact ih
  | allS _ ih | exS _ ih =>
    simp only [Ty.sizeVars, List.mem_append]; exact Or.inr ih
  | mu_here _ hi | nu_here _ hi =>
    simp only [Ty.sizeVars, List.mem_append]; exact Or.inl hi
  | mu_body hT _ ih | nu_body hT _ ih =>
    simp only [Ty.sizeVars, List.mem_append]
    exact Or.inr (mem_sizeVarsList_of_mem hT ih)

mutual

theorem Ty.indexes_mem_sizeVars {fk : FixKind} {i : Nat} :
    ∀ (A : Ty), A.indexes fk i = true → i ∈ A.sizeVars
  | .unit, h => by simp [Ty.indexes] at h
  | .var _, h => by simp [Ty.indexes] at h
  | .fvar _, h => by simp [Ty.indexes] at h
  | .prod A B, h => by
    simp only [Ty.indexes, Bool.or_eq_true] at h
    simp only [Ty.sizeVars, List.mem_append]
    rcases h with h | h
    · exact Or.inl (Ty.indexes_mem_sizeVars A h)
    · exact Or.inr (Ty.indexes_mem_sizeVars B h)
  | .arr A B, h => by
    simp only [Ty.indexes, Bool.or_eq_true] at h
    simp only [Ty.sizeVars, List.mem_append]
    rcases h with h | h
    · exact Or.inl (Ty.indexes_mem_sizeVars A h)
    · exact Or.inr (Ty.indexes_mem_sizeVars B h)
  | .app A B _, h => by
    simp only [Ty.indexes, Bool.or_eq_true] at h
    simp only [Ty.sizeVars, List.mem_append]
    rcases h with h | h
    · exact Or.inl (Ty.indexes_mem_sizeVars A h)
    · exact Or.inr (Ty.indexes_mem_sizeVars B h)
  | .lam _ F, h => Ty.indexes_mem_sizeVars F h
  | .allT _ F, h => Ty.indexes_mem_sizeVars F h
  | .exT _ F, h => Ty.indexes_mem_sizeVars F h
  | .allS _ B, h => by
    simp only [Ty.sizeVars, List.mem_append]
    exact Or.inr (Ty.indexes_mem_sizeVars B h)
  | .exS _ B, h => by
    simp only [Ty.sizeVars, List.mem_append]
    exact Or.inr (Ty.indexes_mem_sizeVars B h)
  | .mu _ S, h => by
    simp only [Ty.indexes, Bool.or_eq_true, Bool.and_eq_true, List.contains_iff_mem] at h
    simp only [Ty.sizeVars, List.mem_append]
    rcases h with ⟨_, hi⟩ | h
    · exact Or.inl hi
    · exact Or.inr (Ty.indexesList_mem_sizeVarsList S h)
  | .nu _ S, h => by
    simp only [Ty.indexes, Bool.or_eq_true, Bool.and_eq_true, List.contains_iff_mem] at h
    simp only [Ty.sizeVars, List.mem_append]
    rcases h with ⟨_, hi⟩ | h
    · exact Or.inl hi
    · exact Or.inr (Ty.indexesList_mem_sizeVarsList S h)

theorem Ty.indexesList_mem_sizeVarsList {fk : FixKind} {i : Nat} :
    ∀ (S : List Ty), Ty.indexesList fk i S = true → i ∈ Ty.sizeVarsList S
  | [], h => by simp [Ty.indexesList] at h
  | A :: S, h => by
    simp only [Ty.indexesList, Bool.or_eq_true] at h
    simp only [Ty.sizeVarsList, List.mem_append]
    rcases h with h | h
    · exact Or.inl (Ty.indexes_mem_sizeVars A h)
    · exact Or.inr (Ty.indexesList_mem_sizeVarsList S h)

end

theorem Ty.indexes_eq_false_of_not_mem {fk : FixKind} {i : Nat} {A : Ty}
    (h : i ∉ A.sizeVars) : A.indexes fk i = false := by
  cases hidx : A.indexes fk i with
  | false => rfl
  | true => exact False.elim (h (Ty.indexes_mem_sizeVars A hidx))

theorem Ty.indexesList_eq_false_of_not_mem {fk : FixKind} {i : Nat} {S : List Ty}
    (h : i ∉ Ty.sizeVarsList S) : Ty.indexesList fk i S = false := by
  cases hidx : Ty.indexesList fk i S with
  | false => rfl
  | true => exact False.elim (h (Ty.indexesList_mem_sizeVarsList S hidx))

def EncodeOccInv (πs π : Pol) (Δ : KCtx) (Δb : BCtx) (Ψ : SizeCtx) (A' : Ty) : Prop :=
  ∀ i ∈ Ψ.dom, ∃ fk q,
    (q = .pos ∨ q = .neg) ∧
    Pol.comp π q = fk.encPol πs ∧
    SizeOcc fk i Δ Δb q A' ∧
    A'.indexes fk i = true ∧
    A'.indexes fk.other i = false ∧
    (∀ Δ' Δb' q', ¬ SizeOcc fk.other i Δ' Δb' q' A')

def EncodeListOccInv (πs π : Pol) (Δ : KCtx) (Δb : BCtx) (Ψ : SizeCtx) (S' : List Ty) : Prop :=
  ∀ i ∈ Ψ.dom, ∃ fk q,
    (q = .pos ∨ q = .neg) ∧
    Pol.comp π q = fk.encPol πs ∧
    (∃ T' ∈ S', SizeOcc fk i Δ Δb q T') ∧
    Ty.indexesList fk i S' = true ∧
    Ty.indexesList fk.other i S' = false ∧
    (∀ T' ∈ S', ∀ Δ' Δb' q', ¬ SizeOcc fk.other i Δ' Δb' q' T')

theorem encode_occ_inv {πs : Pol} {ok : Nat → Prop} {π : Pol} {Δ : KCtx} {Δb : BCtx}
    {A A' : Ty} {Ψ : SizeCtx} (h : Encode πs ok π Δ Δb A Ψ A') (hπs : πs = .pos ∨ πs = .neg) :
    EncodeOccInv πs π Δ Δb Ψ A' := by
  refine Encode.rec
    (motive_1 := fun π Δ Δb _ Ψ A' _ => EncodeOccInv πs π Δ Δb Ψ A')
    (motive_2 := fun π Δ Δb _ Ψ S' _ => EncodeListOccInv πs π Δ Δb Ψ S')
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  · intro _ _ _ i hi; simp [SizeCtx.dom] at hi
  · intro π Δ Δb A B A' B' Ψ₁ Ψ₂ hA hB hdisj ihA ihB i hi
    simp only [SizeCtx.dom, List.map_append, List.mem_append] at hi
    rcases hi with hi | hi
    · obtain ⟨fk, q, hq, hcomp, hocc, hidx, hno_idx, hno_occ⟩ := ihA i hi
      have hnotB : i ∉ B'.sizeVars := fun hm => hdisj i hi (encode_sizeVars_sub hB i hm)
      refine ⟨fk, q, hq, hcomp, .prodL hocc, ?_, ?_, ?_⟩
      · simp [Ty.indexes, hidx]
      · simp [Ty.indexes, hno_idx, Ty.indexes_eq_false_of_not_mem hnotB]
      · intro Δ' Δb' q' ho
        cases ho with
        | prodL ho => exact hno_occ Δ' Δb' q' ho
        | prodR ho => exact hnotB ho.mem_sizeVars
    · obtain ⟨fk, q, hq, hcomp, hocc, hidx, hno_idx, hno_occ⟩ := ihB i hi
      have hnotA : i ∉ A'.sizeVars :=
        fun hm => hdisj i (encode_sizeVars_sub hA i hm) hi
      refine ⟨fk, q, hq, hcomp, .prodR hocc, ?_, ?_, ?_⟩
      · simp [Ty.indexes, hidx]
      · simp [Ty.indexes, hno_idx, Ty.indexes_eq_false_of_not_mem hnotA]
      · intro Δ' Δb' q' ho
        cases ho with
        | prodL ho => exact hnotA ho.mem_sizeVars
        | prodR ho => exact hno_occ Δ' Δb' q' ho
  · intro π Δ Δb A B A' B' Ψ₁ Ψ₂ hA hB hdisj ihA ihB i hi
    simp only [SizeCtx.dom, List.map_append, List.mem_append] at hi
    rcases hi with hi | hi
    · obtain ⟨fk, q, hq, hcomp, hocc, hidx, hno_idx, hno_occ⟩ := ihA i hi
      have hnotB : i ∉ B'.sizeVars := fun hm => hdisj i hi (encode_sizeVars_sub hB i hm)
      have hq' : q.negate = .pos ∨ q.negate = .neg := by cases q <;> simp_all [Pol.negate]
      have hq_neg : q.negate.negate = q := by rcases hq with rfl | rfl <;> rfl
      have hcomp' : Pol.comp π q.negate = fk.encPol πs := by
        rcases hq with rfl | rfl <;> cases π <;> simpa [Pol.comp, Pol.negate] using hcomp
      refine ⟨fk, q.negate, hq', hcomp', .arrL (hq_neg.symm ▸ hocc), ?_, ?_, ?_⟩
      · simp [Ty.indexes, hidx]
      · simp [Ty.indexes, hno_idx, Ty.indexes_eq_false_of_not_mem hnotB]
      · intro Δ' Δb' q' ho
        cases ho with
        | arrL ho => exact hno_occ Δ' Δb' q'.negate ho
        | arrR ho => exact hnotB ho.mem_sizeVars
    · obtain ⟨fk, q, hq, hcomp, hocc, hidx, hno_idx, hno_occ⟩ := ihB i hi
      have hnotA : i ∉ A'.sizeVars :=
        fun hm => hdisj i (encode_sizeVars_sub hA i hm) hi
      refine ⟨fk, q, hq, hcomp, .arrR hocc, ?_, ?_, ?_⟩
      · simp [Ty.indexes, hidx]
      · simp [Ty.indexes, hno_idx, Ty.indexes_eq_false_of_not_mem hnotA]
      · intro Δ' Δb' q' ho
        cases ho with
        | arrL ho => exact hnotA ho.mem_sizeVars
        | arrR ho => exact hno_occ Δ' Δb' q' ho
  · intro _ _ _ _ i hi; simp [SizeCtx.dom] at hi
  · intro _ _ _ _ i hi; simp [SizeCtx.dom] at hi
  · intro π Δ Δb ι F F' Ψ _ ih i hi
    obtain ⟨fk, q, hq, hcomp, hocc, hidx, hno_idx, hno_occ⟩ := ih i hi
    refine ⟨fk, q, hq, hcomp, .lam hocc, hidx, hno_idx, ?_⟩
    intro Δ' Δb' q' ho
    cases ho with
    | lam ho => exact hno_occ _ _ _ ho
  · intro π π' Δ Δb F G F' G' ι κ₁ κ₂ Ψ₁ Ψ₂ hkF hF hG hdisj ihF ihG i hi
    simp only [SizeCtx.dom, List.map_append, List.mem_append] at hi
    rcases hi with hi | hi
    · obtain ⟨fk, q, hq, hcomp, hocc, hidx, hno_idx, hno_occ⟩ := ihF i hi
      have hnotG : i ∉ G'.sizeVars := fun hm => hdisj i hi (encode_sizeVars_sub hG i hm)
      refine ⟨fk, q, hq, hcomp, .appF hocc, ?_, ?_, ?_⟩
      · simp [Ty.indexes, hidx]
      · simp [Ty.indexes, hno_idx, Ty.indexes_eq_false_of_not_mem hnotG]
      · intro Δ' Δb' q' ho
        cases ho with
        | appF ho => exact hno_occ _ _ _ ho
        | appG _ ho => exact hnotG ho.mem_sizeVars
    · obtain ⟨fk, q, hq, hcomp, hocc, hidx, hno_idx, hno_occ⟩ := ihG i hi
      have hnotF : i ∉ F'.sizeVars :=
        fun hm => hdisj i (encode_sizeVars_sub hF i hm) hi
      have hekF' : EKinding Δ Δb F' (.arr π' κ₁ κ₂) := by
        unfold EKinding
        rw [(encode_facts hF).1]
        exact hkF.erase
      have htarget : fk.encPol πs = .pos ∨ fk.encPol πs = .neg := by
        cases fk <;> rcases hπs with rfl | rfl <;> simp [FixKind.encPol, Pol.negate]
      have hπ' : π' = .pos ∨ π' = .neg := by
        cases π' <;> cases π <;> rcases hq with rfl | rfl <;>
          rcases htarget with ht | ht <;> simp_all [Pol.comp]
      have hq' : Pol.comp π' q = .pos ∨ Pol.comp π' q = .neg := by
        rcases hπ' with rfl | rfl <;> rcases hq with rfl | rfl <;> simp [Pol.comp, Pol.negate]
      have hcomp' : Pol.comp π (Pol.comp π' q) = fk.encPol πs := by
        rcases hπ' with rfl | rfl <;> rcases hq with rfl | rfl <;> cases π <;>
          simpa [Pol.comp, Pol.negate] using hcomp
      have hinv : Pol.comp π' (Pol.comp π' q) = q := by
        rcases hπ' with rfl | rfl <;> rcases hq with rfl | rfl <;> rfl
      refine ⟨fk, Pol.comp π' q, hq', hcomp', .appG hekF' (hinv.symm ▸ hocc), ?_, ?_, ?_⟩
      · simp [Ty.indexes, hidx]
      · simp [Ty.indexes, hno_idx, Ty.indexes_eq_false_of_not_mem hnotF]
      · intro Δ' Δb' q' ho
        cases ho with
        | appF ho => exact hnotF ho.mem_sizeVars
        | appG _ ho => exact hno_occ _ _ _ ho
  · intro π Δ Δb S S' Ψ j hπ _ hj hS ih i hi
    simp only [SizeCtx.dom, List.map_cons, List.mem_cons] at hi
    rcases hi with rfl | hi
    · have hnotS : i ∉ Ty.sizeVarsList S' := fun hm => hj (encodeList_sizeVars_sub hS i hm)
      have hcomp : Pol.comp π .pos = FixKind.encPol πs .mu := by
        subst hπ; rcases hπs with rfl | rfl <;> rfl
      refine ⟨.mu, .pos, Or.inl rfl, hcomp, .mu_here rfl (by simp [Size.fvars]), ?_, ?_, ?_⟩
      · simp [Ty.indexes, Size.fvars]
      · simp [FixKind.other, Ty.indexes, Ty.indexesList_eq_false_of_not_mem hnotS]
      · intro Δ' Δb' q' ho
        cases ho with
        | mu_here hfk => cases hfk
        | mu_body hT ho => exact hnotS (mem_sizeVarsList_of_mem hT ho.mem_sizeVars)
    · obtain ⟨fk, q, hq, hcomp, ⟨T', hT', hocc⟩, hidx, hno_idx, hno_occ⟩ := ih i hi
      have hij : i ≠ j := fun heq => hj (heq ▸ hi)
      refine ⟨fk, q, hq, hcomp, .mu_body hT' hocc, ?_, ?_, ?_⟩
      · simp [Ty.indexes, hidx]
      · simp [Ty.indexes, Size.fvars, hij, hno_idx]
      · intro Δ' Δb' q' ho
        cases ho with
        | mu_here _ hmem =>
          simp [Size.fvars] at hmem
          exact hij hmem
        | mu_body hT ho => exact hno_occ _ hT _ _ _ ho
  · intro π Δ Δb S S' Ψ _ _ ih i hi
    obtain ⟨fk, q, hq, hcomp, ⟨T', hT', hocc⟩, hidx, hno_idx, hno_occ⟩ := ih i hi
    refine ⟨fk, q, hq, hcomp, .mu_body hT' hocc, ?_, ?_, ?_⟩
    · simp [Ty.indexes, hidx]
    · simp [Ty.indexes, Size.fvars, hno_idx]
    · intro Δ' Δb' q' ho
      cases ho with
      | mu_here _ hmem => simp [Size.fvars] at hmem
      | mu_body hT ho => exact hno_occ _ hT _ _ _ ho
  · intro π Δ Δb R R' Ψ j hπ _ hj hR ih i hi
    simp only [SizeCtx.dom, List.map_cons, List.mem_cons] at hi
    rcases hi with rfl | hi
    · have hnotR : i ∉ Ty.sizeVarsList R' := fun hm => hj (encodeList_sizeVars_sub hR i hm)
      have hcomp : Pol.comp π .pos = FixKind.encPol πs .nu := by
        subst hπ; rcases hπs with rfl | rfl <;> rfl
      refine ⟨.nu, .pos, Or.inl rfl, hcomp, .nu_here rfl (by simp [Size.fvars]), ?_, ?_, ?_⟩
      · simp [Ty.indexes, Size.fvars]
      · simp [FixKind.other, Ty.indexes, Ty.indexesList_eq_false_of_not_mem hnotR]
      · intro Δ' Δb' q' ho
        cases ho with
        | nu_here hfk => cases hfk
        | nu_body hT ho => exact hnotR (mem_sizeVarsList_of_mem hT ho.mem_sizeVars)
    · obtain ⟨fk, q, hq, hcomp, ⟨T', hT', hocc⟩, hidx, hno_idx, hno_occ⟩ := ih i hi
      have hij : i ≠ j := fun heq => hj (heq ▸ hi)
      refine ⟨fk, q, hq, hcomp, .nu_body hT' hocc, ?_, ?_, ?_⟩
      · simp [Ty.indexes, hidx]
      · simp [Ty.indexes, Size.fvars, hij, hno_idx]
      · intro Δ' Δb' q' ho
        cases ho with
        | nu_here _ hmem =>
          simp [Size.fvars] at hmem
          exact hij hmem
        | nu_body hT ho => exact hno_occ _ hT _ _ _ ho
  · intro π Δ Δb R R' Ψ _ _ ih i hi
    obtain ⟨fk, q, hq, hcomp, ⟨T', hT', hocc⟩, hidx, hno_idx, hno_occ⟩ := ih i hi
    refine ⟨fk, q, hq, hcomp, .nu_body hT' hocc, ?_, ?_, ?_⟩
    · simp [Ty.indexes, hidx]
    · simp [Ty.indexes, Size.fvars, hno_idx]
    · intro Δ' Δb' q' ho
      cases ho with
      | nu_here _ hmem => simp [Size.fvars] at hmem
      | nu_body hT ho => exact hno_occ _ hT _ _ _ ho
  · intro π Δ Δb κ B B' Ψ _ ih i hi
    obtain ⟨fk, q, hq, hcomp, hocc, hidx, hno_idx, hno_occ⟩ := ih i hi
    refine ⟨fk, q, hq, hcomp, .allT hocc, hidx, hno_idx, ?_⟩
    intro Δ' Δb' q' ho
    cases ho with
    | allT ho => exact hno_occ _ _ _ ho
  · intro π Δ Δb κ B B' Ψ _ ih i hi
    obtain ⟨fk, q, hq, hcomp, hocc, hidx, hno_idx, hno_occ⟩ := ih i hi
    refine ⟨fk, q, hq, hcomp, .exT hocc, hidx, hno_idx, ?_⟩
    intro Δ' Δb' q' ho
    cases ho with
    | exT ho => exact hno_occ _ _ _ ho
  · intro _ _ _ i hi; simp [SizeCtx.dom] at hi
  · intro π Δ Δb T T' S S' Ψ₁ Ψ₂ hT hS hdisj ihT ihS i hi
    simp only [SizeCtx.dom, List.map_append, List.mem_append] at hi
    rcases hi with hi | hi
    · obtain ⟨fk, q, hq, hcomp, hocc, hidx, hno_idx, hno_occ⟩ := ihT i hi
      have hnotS : i ∉ Ty.sizeVarsList S' := fun hm => hdisj i hi (encodeList_sizeVars_sub hS i hm)
      refine ⟨fk, q, hq, hcomp, ⟨T', by simp, hocc⟩, ?_, ?_, ?_⟩
      · simp [Ty.indexesList, hidx]
      · simp [Ty.indexesList, hno_idx, Ty.indexesList_eq_false_of_not_mem hnotS]
      · intro U hU Δ' Δb' q' ho
        rcases List.mem_cons.mp hU with rfl | hU
        · exact hno_occ _ _ _ ho
        · exact hnotS (mem_sizeVarsList_of_mem hU ho.mem_sizeVars)
    · obtain ⟨fk, q, hq, hcomp, ⟨U, hU, hocc⟩, hidx, hno_idx, hno_occ⟩ := ihS i hi
      have hnotT : i ∉ T'.sizeVars :=
        fun hm => hdisj i (encode_sizeVars_sub hT i hm) hi
      refine ⟨fk, q, hq, hcomp, ⟨U, by simp [hU], hocc⟩, ?_, ?_, ?_⟩
      · simp [Ty.indexesList, hidx]
      · simp [Ty.indexesList, hno_idx, Ty.indexes_eq_false_of_not_mem hnotT]
      · intro U' hU' Δ' Δb' q' ho
        rcases List.mem_cons.mp hU' with rfl | hU'
        · exact hnotT ho.mem_sizeVars
        · exact hno_occ U' hU' _ _ _ ho

/-- **Lemma 3** (Polarities of encoded size variables, Section 6.1, p. 43): if
`+; Δ ⊢_SCT^− A ⇒ Ψ; A'`, then every `i ∈ Ψ.dom` either occurs negatively as a `μ`-index in `A'`
(with `paramPol A' i = .pos` and no `ν`-occurrence) or occurs positively as a `ν`-index in `A'`
(with `paramPol A' i = .neg` and no `μ`-occurrence). -/
theorem lemma_3 {ok : Nat → Prop} {Δ : KCtx} {Δb : BCtx} {A A' : Ty} {Ψ : SizeCtx}
    (henc : Encode .neg ok .pos Δ Δb A Ψ A') :
    ∀ i ∈ Ψ.dom,
      (SizeOcc .mu i Δ Δb .neg A' ∧ paramPol A' i = .pos ∧
        (∀ Δ' Δb' q, ¬ SizeOcc .nu i Δ' Δb' q A')) ∨
      (SizeOcc .nu i Δ Δb .pos A' ∧ paramPol A' i = .neg ∧
        (∀ Δ' Δb' q, ¬ SizeOcc .mu i Δ' Δb' q A')) := by
  intro i hi
  obtain ⟨fk, q, hq, hcomp, hocc, hidx, hno_idx, hno_occ⟩ := encode_occ_inv henc (Or.inr rfl) i hi
  cases fk with
  | mu =>
    have hq_eq : q = .neg := by rcases hq with rfl | rfl <;> simp_all [Pol.comp, FixKind.encPol]
    subst hq_eq
    exact Or.inl ⟨hocc, by simp [paramPol, hidx], hno_occ⟩
  | nu =>
    have hq_eq : q = .pos := by
      rcases hq with rfl | rfl <;> simp_all [Pol.comp, FixKind.encPol, Pol.negate]
    subst hq_eq
    have hmu_false : A'.indexes .mu i = false := hno_idx
    exact Or.inr ⟨hocc, by simp [paramPol, hmu_false, hidx], hno_occ⟩

end NishtAbel2024V5

/-! ## Solutions/V5/InfGraph.lean -/

/-! # V5 inference: rigid variable classification (Lemmas 4–5) and constraint analysis
(Theorems 10–12) -/

namespace NishtAbel2024V5

/-! ## Fixpoint-index occurrences and `Ty.indexes` -/

theorem mem_indexesList_of_mem {fk : FixKind} {i : Nat} {S : List Ty} {T : Ty}
    (hT : T ∈ S) (hi : T.indexes fk i = true) : Ty.indexesList fk i S = true := by
  induction S with
  | nil => simp at hT
  | cons A S ih =>
    simp only [Ty.indexesList, Bool.or_eq_true]
    rcases List.mem_cons.mp hT with rfl | hT
    · exact Or.inl hi
    · exact Or.inr (ih hT)

theorem SizeOcc.indexes {fk : FixKind} {i : Nat} {Δ : KCtx} {Δb : BCtx} {π : Pol} {A : Ty}
    (h : SizeOcc fk i Δ Δb π A) : A.indexes fk i = true := by
  induction h with
  | prodL _ ih | arrL _ ih | appF _ ih =>
    simp [Ty.indexes, ih]
  | prodR _ ih | arrR _ ih | appG _ _ ih =>
    simp [Ty.indexes, ih]
  | lam _ ih | allT _ ih | exT _ ih | allS _ ih | exS _ ih =>
    simpa [Ty.indexes] using ih
  | mu_here hfk hi =>
    subst hfk
    simp [Ty.indexes, hi]
  | nu_here hfk hi =>
    subst hfk
    simp [Ty.indexes, hi]
  | mu_body hT _ ih =>
    simp [Ty.indexes, mem_indexesList_of_mem hT ih]
  | nu_body hT _ ih =>
    simp [Ty.indexes, mem_indexesList_of_mem hT ih]

mutual

theorem Ty.indexes_substTy_sub (fk : FixKind) (i k : Nat) (U : Ty) :
    ∀ (A : Ty), (A.substTy k U).indexes fk i = true →
      A.indexes fk i = true ∨ U.indexes fk i = true
  | .unit, h => by simp [Ty.substTy, Ty.indexes] at h
  | .fvar _, h => by simp [Ty.substTy, Ty.indexes] at h
  | .var X, h => by
    simp only [Ty.substTy] at h
    split at h
    · exact Or.inr h
    · split at h <;> simp [Ty.indexes] at h
  | .prod A B, h => by
    simp only [Ty.substTy, Ty.indexes, Bool.or_eq_true] at h ⊢
    rcases h with h | h
    · rcases Ty.indexes_substTy_sub fk i k U A h with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
    · rcases Ty.indexes_substTy_sub fk i k U B h with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
  | .arr A B, h => by
    simp only [Ty.substTy, Ty.indexes, Bool.or_eq_true] at h ⊢
    rcases h with h | h
    · rcases Ty.indexes_substTy_sub fk i k U A h with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
    · rcases Ty.indexes_substTy_sub fk i k U B h with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
  | .app A B _, h => by
    simp only [Ty.substTy, Ty.indexes, Bool.or_eq_true] at h ⊢
    rcases h with h | h
    · rcases Ty.indexes_substTy_sub fk i k U A h with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
    · rcases Ty.indexes_substTy_sub fk i k U B h with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
  | .lam _ F, h => Ty.indexes_substTy_sub fk i (k + 1) U F h
  | .allT _ F, h => Ty.indexes_substTy_sub fk i (k + 1) U F h
  | .exT _ F, h => Ty.indexes_substTy_sub fk i (k + 1) U F h
  | .allS _ F, h => Ty.indexes_substTy_sub fk i k U F h
  | .exS _ F, h => Ty.indexes_substTy_sub fk i k U F h
  | .mu a S, h => by
    simp only [Ty.substTy, Ty.indexes, Bool.or_eq_true] at h ⊢
    rcases h with h | h
    · exact Or.inl (Or.inl h)
    · rcases Ty.indexesList_substTyList_sub fk i (k + 1) U S h with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
  | .nu a S, h => by
    simp only [Ty.substTy, Ty.indexes, Bool.or_eq_true] at h ⊢
    rcases h with h | h
    · exact Or.inl (Or.inl h)
    · rcases Ty.indexesList_substTyList_sub fk i (k + 1) U S h with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr h

theorem Ty.indexesList_substTyList_sub (fk : FixKind) (i k : Nat) (U : Ty) :
    ∀ (S : List Ty), Ty.indexesList fk i (Ty.substTyList S k U) = true →
      Ty.indexesList fk i S = true ∨ U.indexes fk i = true
  | [], h => by simp [Ty.substTyList, Ty.indexesList] at h
  | A :: S, h => by
    simp only [Ty.substTyList, Ty.indexesList, Bool.or_eq_true] at h ⊢
    rcases h with h | h
    · rcases Ty.indexes_substTy_sub fk i k U A h with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
    · rcases Ty.indexesList_substTyList_sub fk i k U S h with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr h

end

/-! ## Lemmas 4 & 5: Rigid variables in patterns and copattern spines (Section 6.2) -/

theorem inferPat_rigid {Ψ : SizeCtx} {Θ : TyCtx} {p : Pat} {A : Ty} {Γ : TermCtx} {Ψ' : SizeCtx}
    {Θ' : TyCtx} (h : InferPat Ψ Θ p A Γ Ψ' Θ') : ∀ q ∈ Ψ', RigidName q.1 := by
  induction h with
  | var => intro _ h; simp at h
  | unit => intro _ h; simp at h
  | pair _ _ ih₁ ih₂ =>
    intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact ih₁ q hq
    · exact ih₂ q hq
  | cons _ hj _ _ ih =>
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact hj
    · exact ih q hq
  | pack _ _ ih => exact ih

theorem inferPat_indexes {Ψ : SizeCtx} {Θ : TyCtx} {p : Pat} {A : Ty} {Γ : TermCtx}
    {Ψ' : SizeCtx} {Θ' : TyCtx} (h : InferPat Ψ Θ p A Γ Ψ' Θ') :
    ∀ {fk : FixKind} {i : Nat} {xB : Nat × Ty}, xB ∈ Γ → xB.2.indexes fk i = true →
      A.indexes fk i = true ∨ (fk = .mu ∧ i ∈ Ψ'.dom) := by
  induction h with
  | var =>
    intro fk i xB hxB hidx
    simp only [List.mem_singleton] at hxB
    subst hxB
    exact Or.inl hidx
  | unit =>
    intro _ _ _ hxB
    simp at hxB
  | pair _ _ ih₁ ih₂ =>
    intro fk i xB hxB hidx
    rcases List.mem_append.mp hxB with hxB | hxB
    · rcases ih₁ hxB hidx with hA | ⟨rfl, hi⟩
      · exact Or.inl (by simp [Ty.indexes, hA])
      · exact Or.inr ⟨rfl, by simp only [SizeCtx.dom_append, List.mem_append]; exact Or.inl hi⟩
    · rcases ih₂ hxB hidx with hB | ⟨rfl, hi⟩
      · exact Or.inl (by simp [Ty.indexes, hB])
      · exact Or.inr ⟨rfl, by simp only [SizeCtx.dom_append, List.mem_append]; exact Or.inr hi⟩
  | cons hc _ _ _ ih =>
    intro fk i xB hxB hidx
    rcases ih hxB hidx with hsub | ⟨rfl, hi⟩
    · rcases Ty.indexes_substTy_sub fk i 0 (.mu (.var _ 0) _) _ hsub with hSc | hmu
      · exact Or.inl (by simp [Ty.indexes, mem_indexesList_of_mem (List.mem_of_getElem? hc) hSc])
      · simp only [Ty.indexes, Size.fvars, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
          List.contains_iff_mem, List.mem_singleton] at hmu
        rcases hmu with ⟨rfl, rfl⟩ | hS
        · exact Or.inr ⟨rfl, by simp [SizeCtx.dom]⟩
        · exact Or.inl (by simp [Ty.indexes, hS])
    · exact Or.inr ⟨rfl, by simp only [SizeCtx.dom_cons, List.mem_cons]; exact Or.inr hi⟩
  | pack _ _ ih =>
    intro fk i xB hxB hidx
    rcases ih hxB hidx with hsub | ⟨rfl, hi⟩
    · rcases Ty.indexes_substTy_sub fk i 0 (.fvar _) _ hsub with hB | hfvar
      · exact Or.inl hB
      · simp [Ty.indexes] at hfvar
    · exact Or.inr ⟨rfl, hi⟩

/-- **Lemma 4** (Rigid variables of patterns, Section 6.2, pp. 45–46): in `Ψ; Θ ⊢_SCT p : A ⇒ Γ;
Ψ'; Θ'`, every variable in `Ψ'` has a rigid name, and every fixpoint occurrence `SizeOcc fk i Δ Δb
q B` in a pattern-bound variable `(x, B) ∈ Γ` either already indexes `fk` in `A` (`A.indexes fk i
= true`) or is one of the newly bound pattern variables `i ∈ Ψ'.dom` with `fk = .mu` (in
particular, fresh pattern variables `j ∈ Ψ'.dom` with `A.indexes .nu j = false` never occur as
`ν`-indices in `Γ`). -/
theorem lemma_4 {Ψ : SizeCtx} {Θ : TyCtx} {p : Pat} {A : Ty} {Γ : TermCtx} {Ψ' : SizeCtx}
    {Θ' : TyCtx} (h : InferPat Ψ Θ p A Γ Ψ' Θ') :
    (∀ q ∈ Ψ', RigidName q.1) ∧
    (∀ {fk : FixKind} {i : Nat} {Δ : KCtx} {Δb : BCtx} {π : Pol} {xB : Nat × Ty},
      xB ∈ Γ → SizeOcc fk i Δ Δb π xB.2 → A.indexes fk i = true ∨ (fk = .mu ∧ i ∈ Ψ'.dom)) ∧
    (∀ j ∈ Ψ'.dom, A.indexes .nu j = false →
      ∀ xB ∈ Γ, ∀ Δ Δb π, ¬ SizeOcc .nu j Δ Δb π xB.2) := by
  refine ⟨inferPat_rigid h, fun hxB hocc => inferPat_indexes h hxB hocc.indexes, ?_⟩
  intro j _ hAnu xB hxB Δ Δb π hocc
  rcases inferPat_indexes h hxB hocc.indexes with hnu | ⟨hfk, _⟩
  · rw [hAnu] at hnu; cases hnu
  · cases hfk

theorem inferSpine_indexes {Ψ : SizeCtx} {Θ : TyCtx} {qs : List Copat} {A : Ty} {Γ : TermCtx}
    {Ψ' : SizeCtx} {Θ' : TyCtx} {C : Ty} (h : InferSpine Ψ Θ qs A Γ Ψ' Θ' C) :
    ∀ {fk : FixKind} {i : Nat},
      ((∃ xB ∈ Γ, xB.2.indexes fk i = true) ∨ C.indexes fk i = true) →
      A.indexes fk i = true ∨ i ∈ Ψ'.dom := by
  induction h with
  | nil =>
    intro fk i hocc
    rcases hocc with ⟨xB, hxB, _⟩ | hC
    · simp at hxB
    · exact Or.inl hC
  | pat hp _ ih =>
    intro fk i hocc
    rcases hocc with ⟨xB, hxB, hidx⟩ | hC
    · rcases List.mem_append.mp hxB with hxB | hxB
      · rcases inferPat_indexes hp hxB hidx with hA | ⟨_, hi⟩
        · exact Or.inl (by simp [Ty.indexes, hA])
        · exact Or.inr (by simp only [SizeCtx.dom_append, List.mem_append]; exact Or.inl hi)
      · rcases ih (Or.inl ⟨xB, hxB, hidx⟩) with hB | hi
        · exact Or.inl (by simp [Ty.indexes, hB])
        · exact Or.inr (by simp only [SizeCtx.dom_append, List.mem_append]; exact Or.inr hi)
    · rcases ih (Or.inr hC) with hB | hi
      · exact Or.inl (by simp [Ty.indexes, hB])
      · exact Or.inr (by simp only [SizeCtx.dom_append, List.mem_append]; exact Or.inr hi)
  | proj hd _ _ _ ih =>
    intro fk i hocc
    rcases ih hocc with hsub | hi
    · rcases Ty.indexes_substTy_sub fk i 0 (.nu (.var _ 0) _) _ hsub with hRd | hnu
      · exact Or.inl (by simp [Ty.indexes, mem_indexesList_of_mem (List.mem_of_getElem? hd) hRd])
      · simp only [Ty.indexes, Size.fvars, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
          List.contains_iff_mem, List.mem_singleton] at hnu
        rcases hnu with ⟨rfl, rfl⟩ | hR
        · exact Or.inr (by simp [SizeCtx.dom])
        · exact Or.inl (by simp [Ty.indexes, hR])
    · exact Or.inr (by simp only [SizeCtx.dom_cons, List.mem_cons]; exact Or.inr hi)
  | inst _ _ ih =>
    intro fk i hocc
    rcases ih hocc with hsub | hi
    · rcases Ty.indexes_substTy_sub fk i 0 (.fvar _) _ hsub with hB | hfvar
      · exact Or.inl hB
      · simp [Ty.indexes] at hfvar
    · exact Or.inr hi

/-- **Lemma 5** (Rigid variables of copattern spines, Section 6.2, pp. 46–47): in
`Ψ; Θ ⊢_SCT q⃗ : A ⇒ C; Γ; Ψ'; Θ'`, every variable in `Ψ'` has a rigid name, and every fixpoint
occurrence `SizeOcc fk i Δ Δb π B` in `(x, B) ∈ Γ` or `SizeOcc fk i Δ Δb π C` in `C` satisfies
`A.indexes fk i = true ∨ i ∈ Ψ'.dom`. In particular, when `A` is produced by signature encoding
`+; Δ₀ ⊢_SCT^− A₀ ⇒ Ψ; A` and `NamesDisjoint Ψ.dom Ψ'.dom`, every signature parameter `i ∈ Ψ.dom`
either has `paramPol A i = .pos` and never occurs as a `ν`-index in `Γ` or `C`, or has
`paramPol A i = .neg` and never occurs as a `μ`-index in `Γ` or `C`. -/
theorem lemma_5 {Ψ : SizeCtx} {Θ : TyCtx} {qs : List Copat} {A : Ty} {Γ : TermCtx}
    {Ψ' : SizeCtx} {Θ' : TyCtx} {C : Ty} (h : InferSpine Ψ Θ qs A Γ Ψ' Θ' C) :
    (∀ i ∈ Ψ'.dom, RigidName i) ∧
    (∀ {fk : FixKind} {i : Nat} {Δ : KCtx} {Δb : BCtx} {π : Pol},
      ((∃ xB ∈ Γ, SizeOcc fk i Δ Δb π xB.2) ∨ SizeOcc fk i Δ Δb π C) →
      A.indexes fk i = true ∨ i ∈ Ψ'.dom) ∧
    (∀ {ok : Nat → Prop} {Δ₀ : KCtx} {Δb₀ : BCtx} {A₀ : Ty},
      Encode .neg ok .pos Δ₀ Δb₀ A₀ Ψ A →
      NamesDisjoint Ψ.dom Ψ'.dom →
      ∀ i ∈ Ψ.dom,
        (paramPol A i = .pos ∧
          (∀ xB ∈ Γ, ∀ Δ Δb π, ¬ SizeOcc .nu i Δ Δb π xB.2) ∧
          (∀ Δ Δb π, ¬ SizeOcc .nu i Δ Δb π C)) ∨
        (paramPol A i = .neg ∧
          (∀ xB ∈ Γ, ∀ Δ Δb π, ¬ SizeOcc .mu i Δ Δb π xB.2) ∧
          (∀ Δ Δb π, ¬ SizeOcc .mu i Δ Δb π C))) := by
  refine ⟨inferSpine_rigid h, ?_, ?_⟩
  · intro fk i Δ Δb π hocc
    rcases hocc with ⟨xB, hxB, ho⟩ | ho
    · exact inferSpine_indexes h (Or.inl ⟨xB, hxB, ho.indexes⟩)
    · exact inferSpine_indexes h (Or.inr ho.indexes)
  · intro ok Δ₀ Δb₀ A₀ henc hdisj i hi
    have hnotΨ' : i ∉ Ψ'.dom := hdisj i hi
    obtain ⟨fk, q, hq, hcomp, _, hidx, hno_idx, _⟩ := encode_occ_inv henc (Or.inr rfl) i hi
    cases fk with
    | mu =>
      refine Or.inl ⟨by simp [paramPol, hidx], ?_, ?_⟩
      · intro xB hxB Δ Δb π ho
        rcases inferSpine_indexes h (Or.inl ⟨xB, hxB, ho.indexes⟩) with hnu | hi'
        · rw [show A.indexes .nu i = false from hno_idx] at hnu; cases hnu
        · exact hnotΨ' hi'
      · intro Δ Δb π ho
        rcases inferSpine_indexes h (Or.inr ho.indexes) with hnu | hi'
        · rw [show A.indexes .nu i = false from hno_idx] at hnu; cases hnu
        · exact hnotΨ' hi'
    | nu =>
      have hmu_false : A.indexes .mu i = false := hno_idx
      refine Or.inr ⟨by simp [paramPol, hmu_false, hidx], ?_, ?_⟩
      · intro xB hxB Δ Δb π ho
        rcases inferSpine_indexes h (Or.inl ⟨xB, hxB, ho.indexes⟩) with hmu | hi'
        · rw [hmu_false] at hmu; cases hmu
        · exact hnotΨ' hi'
      · intro Δ Δb π ho
        rcases inferSpine_indexes h (Or.inr ho.indexes) with hmu | hi'
        · rw [hmu_false] at hmu; cases hmu
        · exact hnotΨ' hi'

/-! ## Theorem 10: Constraints generated by type comparison (`Compare`) -/

def CompareConstrOrigin (Ψ : SizeCtx) (A B : Ty) (c : SConstr) : Prop :=
  c.ctx = Ψ ∧ c.strict = false ∧ c.up = true ∧
  ((∀ i ∈ c.lhs.fvars ++ c.rhs.fvars, A.indexes .mu i = true ∨ B.indexes .mu i = true) ∨
   (∀ i ∈ c.lhs.fvars ++ c.rhs.fvars, A.indexes .nu i = true ∨ B.indexes .nu i = true))

def CompareListConstrOrigin (Ψ : SizeCtx) (S S' : List Ty) (c : SConstr) : Prop :=
  c.ctx = Ψ ∧ c.strict = false ∧ c.up = true ∧
  ((∀ i ∈ c.lhs.fvars ++ c.rhs.fvars,
      Ty.indexesList .mu i S = true ∨ Ty.indexesList .mu i S' = true) ∨
   (∀ i ∈ c.lhs.fvars ++ c.rhs.fvars,
      Ty.indexesList .nu i S = true ∨ Ty.indexesList .nu i S' = true))

theorem CompareConstrOrigin.symm {Ψ : SizeCtx} {A B : Ty} {c : SConstr}
    (h : CompareConstrOrigin Ψ A B c) : CompareConstrOrigin Ψ B A c := by
  refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
  rcases h.2.2.2 with hmu | hnu
  · exact Or.inl fun i hi => (hmu i hi).symm
  · exact Or.inr fun i hi => (hnu i hi).symm

theorem CompareConstrOrigin.mono {Ψ : SizeCtx} {A B A' B' : Ty} {c : SConstr}
    (h : CompareConstrOrigin Ψ A B c)
    (hAB : ∀ fk i, A.indexes fk i = true ∨ B.indexes fk i = true →
      A'.indexes fk i = true ∨ B'.indexes fk i = true) :
    CompareConstrOrigin Ψ A' B' c := by
  refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
  rcases h.2.2.2 with hmu | hnu
  · exact Or.inl fun i hi => hAB .mu i (hmu i hi)
  · exact Or.inr fun i hi => hAB .nu i (hnu i hi)

theorem CompareListConstrOrigin.symm {Ψ : SizeCtx} {S S' : List Ty} {c : SConstr}
    (h : CompareListConstrOrigin Ψ S S' c) : CompareListConstrOrigin Ψ S' S c := by
  refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
  rcases h.2.2.2 with hmu | hnu
  · exact Or.inl fun i hi => (hmu i hi).symm
  · exact Or.inr fun i hi => (hnu i hi).symm

/-- **Theorem 10** (Constraints in type comparison, Section 6.3.3, pp. 52–53): in
`Ψ; Δ ⊢_SCT A ≤ B : κ ⇒ C`, every emitted constraint `c ∈ C` is a non-strict upper-bound-normalized
constraint `lhs ≤ rhs^↑` in context `Ψ`, and all size variables in `c.lhs` and `c.rhs` come either
from `μ`-indices of `A` and `B` or from `ν`-indices of `A` and `B`. -/
theorem theorem_10 {Ψ : SizeCtx} {Δ : KCtx} {A B : Ty} {κ : Kind} {C : List SConstr}
    (h : Compare Ψ Δ A B κ C) : ∀ c ∈ C, CompareConstrOrigin Ψ A B c := by
  refine Compare.rec
    (motive_1 := fun _ A B _ C _ => ∀ c ∈ C, CompareConstrOrigin Ψ A B c)
    (motive_2 := fun _ _ S S' C _ => ∀ c ∈ C, CompareListConstrOrigin Ψ S S' c)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  · intro _ _ _ _ _ hp; simp at hp
  · intro Δ F G B ι κ C _ _ ih c hc
    refine (ih c hc).mono fun fk i hi => ?_
    rcases hi with hFG | hB
    · rcases Ty.indexes_substTy_sub fk i 0 G F hFG with hF | hG
      · exact Or.inl (by simp [Ty.indexes, hF])
      · exact Or.inl (by simp [Ty.indexes, hG])
    · exact Or.inr hB
  · intro Δ F G A ι κ C _ _ ih c hc
    refine (ih c hc).mono fun fk i hi => ?_
    rcases hi with hA | hFG
    · exact Or.inl hA
    · rcases Ty.indexes_substTy_sub fk i 0 G F hFG with hF | hG
      · exact Or.inr (by simp [Ty.indexes, hF])
      · exact Or.inr (by simp [Ty.indexes, hG])
  · intro Δ A A' B B' C₁ C₂ _ _ ih₁ ih₂ c hc
    rcases List.mem_append.mp hc with hc | hc
    · refine (ih₁ c hc).mono fun fk i hi => ?_
      rcases hi with hA | hA'
      · exact Or.inl (by simp [Ty.indexes, hA])
      · exact Or.inr (by simp [Ty.indexes, hA'])
    · refine (ih₂ c hc).mono fun fk i hi => ?_
      rcases hi with hB | hB'
      · exact Or.inl (by simp [Ty.indexes, hB])
      · exact Or.inr (by simp [Ty.indexes, hB'])
  · intro Δ A A' B B' C₁ C₂ _ _ ih₁ ih₂ c hc
    rcases List.mem_append.mp hc with hc | hc
    · refine (ih₁ c hc).symm.mono fun fk i hi => ?_
      rcases hi with hA | hA'
      · exact Or.inl (by simp [Ty.indexes, hA])
      · exact Or.inr (by simp [Ty.indexes, hA'])
    · refine (ih₂ c hc).mono fun fk i hi => ?_
      rcases hi with hB | hB'
      · exact Or.inl (by simp [Ty.indexes, hB])
      · exact Or.inr (by simp [Ty.indexes, hB'])
  · intro Δ F F' G G' ι κ₁ κ₂ C₁ C₂ _ _ _ _ _ ih₁ ih₂ c hc
    rcases List.mem_append.mp hc with hc | hc
    · refine (ih₁ c hc).mono fun fk i hi => ?_
      rcases hi with hF | hF'
      · exact Or.inl (by simp [Ty.indexes, hF])
      · exact Or.inr (by simp [Ty.indexes, hF'])
    · refine (ih₂ c hc).mono fun fk i hi => ?_
      rcases hi with hG | hG'
      · exact Or.inl (by simp [Ty.indexes, hG])
      · exact Or.inr (by simp [Ty.indexes, hG'])
  · intro Δ F F' G G' ι κ₁ κ₂ C₁ C₂ _ _ _ _ _ ih₁ ih₂ c hc
    rcases List.mem_append.mp hc with hc | hc
    · refine (ih₁ c hc).mono fun fk i hi => ?_
      rcases hi with hF | hF'
      · exact Or.inl (by simp [Ty.indexes, hF])
      · exact Or.inr (by simp [Ty.indexes, hF'])
    · refine (ih₂ c hc).symm.mono fun fk i hi => ?_
      rcases hi with hG | hG'
      · exact Or.inl (by simp [Ty.indexes, hG])
      · exact Or.inr (by simp [Ty.indexes, hG'])
  · intro Δ F F' G G' ι κ₁ κ₂ C₁ C₂ C₃ _ _ _ _ _ _ ih₁ ih₂ ih₃ c hc
    rcases List.mem_append.mp hc with hc | hc
    · rcases List.mem_append.mp hc with hc | hc
      · refine (ih₁ c hc).mono fun fk i hi => ?_
        rcases hi with hF | hF'
        · exact Or.inl (by simp [Ty.indexes, hF])
        · exact Or.inr (by simp [Ty.indexes, hF'])
      · refine (ih₂ c hc).mono fun fk i hi => ?_
        rcases hi with hG | hG'
        · exact Or.inl (by simp [Ty.indexes, hG])
        · exact Or.inr (by simp [Ty.indexes, hG'])
    · refine (ih₃ c hc).symm.mono fun fk i hi => ?_
      rcases hi with hG | hG'
      · exact Or.inl (by simp [Ty.indexes, hG])
      · exact Or.inr (by simp [Ty.indexes, hG'])
  · intro Δ F F' G G' ι κ₁ κ₂ C₁ _ _ _ _ ih₁ c hc
    refine (ih₁ c hc).mono fun fk i hi => ?_
    rcases hi with hF | hF'
    · exact Or.inl (by simp [Ty.indexes, hF])
    · exact Or.inr (by simp [Ty.indexes, hF'])
  · intro Δ F F' ι ι' π κ₁ κ₂ X C _ _ _ _ ih c hc
    refine (ih c hc).mono fun fk i hi => ?_
    rcases hi with hF | hF'
    · rcases Ty.indexes_substTy_sub fk i 0 (.fvar X) F hF with hF | hf
      · exact Or.inl hF
      · simp [Ty.indexes] at hf
    · rcases Ty.indexes_substTy_sub fk i 0 (.fvar X) F' hF' with hF' | hf
      · exact Or.inr hF'
      · simp [Ty.indexes] at hf
  · intro Δ κ B B' X C _ _ _ _ ih c hc
    refine (ih c hc).mono fun fk i hi => ?_
    rcases hi with hB | hB'
    · rcases Ty.indexes_substTy_sub fk i 0 (.fvar X) B hB with hB | hf
      · exact Or.inl hB
      · simp [Ty.indexes] at hf
    · rcases Ty.indexes_substTy_sub fk i 0 (.fvar X) B' hB' with hB' | hf
      · exact Or.inr hB'
      · simp [Ty.indexes] at hf
  · intro Δ κ B B' X C _ _ _ _ ih c hc
    refine (ih c hc).mono fun fk i hi => ?_
    rcases hi with hB | hB'
    · rcases Ty.indexes_substTy_sub fk i 0 (.fvar X) B hB with hB | hf
      · exact Or.inl hB
      · simp [Ty.indexes] at hf
    · rcases Ty.indexes_substTy_sub fk i 0 (.fvar X) B' hB' with hB' | hf
      · exact Or.inr hB'
      · simp [Ty.indexes] at hf
  · intro Δ a b S S' X C _ _ _ _ _ ih c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · refine ⟨rfl, rfl, rfl, Or.inl fun i hi => ?_⟩
      rcases List.mem_append.mp hi with ha | hb
      · exact Or.inl (by simp [Ty.indexes, ha])
      · exact Or.inr (by simp [Ty.indexes, hb])
    · obtain ⟨hctx, hstr, hup, hvars⟩ := ih c hc
      refine ⟨hctx, hstr, hup, ?_⟩
      rcases hvars with hmu | hnu
      · exact Or.inl fun i hi => (hmu i hi).imp
          (fun hS => by simp [Ty.indexes, hS]) (fun hS' => by simp [Ty.indexes, hS'])
      · exact Or.inr fun i hi => (hnu i hi).imp
          (fun hS => by simp [Ty.indexes, hS]) (fun hS' => by simp [Ty.indexes, hS'])
  · intro Δ a b S S' X C₁ C₂ _ _ _ _ _ ih₁ ih₂ c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · refine ⟨rfl, rfl, rfl, Or.inl fun i hi => ?_⟩
      rcases List.mem_append.mp hi with ha | hb
      · exact Or.inl (by simp [Ty.indexes, ha])
      · exact Or.inr (by simp [Ty.indexes, hb])
    · have hcl : CompareListConstrOrigin Ψ S S' c := by
        rcases List.mem_append.mp hc with hc | hc
        · exact ih₁ c hc
        · exact (ih₂ c hc).symm
      obtain ⟨hctx, hstr, hup, hvars⟩ := hcl
      refine ⟨hctx, hstr, hup, ?_⟩
      rcases hvars with hmu | hnu
      · exact Or.inl fun i hi => (hmu i hi).imp
          (fun hS => by simp [Ty.indexes, hS]) (fun hS' => by simp [Ty.indexes, hS'])
      · exact Or.inr fun i hi => (hnu i hi).imp
          (fun hS => by simp [Ty.indexes, hS]) (fun hS' => by simp [Ty.indexes, hS'])
  · intro Δ a b R R' X C _ _ _ _ _ ih c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · refine ⟨rfl, rfl, rfl, Or.inr fun i hi => ?_⟩
      rcases List.mem_append.mp hi with hb | ha
      · exact Or.inr (by simp [Ty.indexes, hb])
      · exact Or.inl (by simp [Ty.indexes, ha])
    · obtain ⟨hctx, hstr, hup, hvars⟩ := ih c hc
      refine ⟨hctx, hstr, hup, ?_⟩
      rcases hvars with hmu | hnu
      · exact Or.inl fun i hi => (hmu i hi).imp
          (fun hR => by simp [Ty.indexes, hR]) (fun hR' => by simp [Ty.indexes, hR'])
      · exact Or.inr fun i hi => (hnu i hi).imp
          (fun hR => by simp [Ty.indexes, hR]) (fun hR' => by simp [Ty.indexes, hR'])
  · intro Δ a b R R' X C₁ C₂ _ _ _ _ _ ih₁ ih₂ c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · refine ⟨rfl, rfl, rfl, Or.inr fun i hi => ?_⟩
      rcases List.mem_append.mp hi with hb | ha
      · exact Or.inr (by simp [Ty.indexes, hb])
      · exact Or.inl (by simp [Ty.indexes, ha])
    · have hcl : CompareListConstrOrigin Ψ R R' c := by
        rcases List.mem_append.mp hc with hc | hc
        · exact ih₁ c hc
        · exact (ih₂ c hc).symm
      obtain ⟨hctx, hstr, hup, hvars⟩ := hcl
      refine ⟨hctx, hstr, hup, ?_⟩
      rcases hvars with hmu | hnu
      · exact Or.inl fun i hi => (hmu i hi).imp
          (fun hR => by simp [Ty.indexes, hR]) (fun hR' => by simp [Ty.indexes, hR'])
      · exact Or.inr fun i hi => (hnu i hi).imp
          (fun hR => by simp [Ty.indexes, hR]) (fun hR' => by simp [Ty.indexes, hR'])
  · intro _ _ _ h; simp at h
  · intro Δ X T T' S S' C₁ C₂ _ _ ih₁ ih₂ c hc
    rcases List.mem_append.mp hc with hc | hc
    · obtain ⟨hctx, hstr, hup, hvars⟩ := ih₁ c hc
      refine ⟨hctx, hstr, hup, ?_⟩
      rcases hvars with hmu | hnu
      · refine Or.inl fun i hi => ?_
        rcases hmu i hi with hT | hT'
        · rcases Ty.indexes_substTy_sub .mu i 0 (.fvar X) T hT with hT | hf
          · exact Or.inl (by simp [Ty.indexesList, hT])
          · simp [Ty.indexes] at hf
        · rcases Ty.indexes_substTy_sub .mu i 0 (.fvar X) T' hT' with hT' | hf
          · exact Or.inr (by simp [Ty.indexesList, hT'])
          · simp [Ty.indexes] at hf
      · refine Or.inr fun i hi => ?_
        rcases hnu i hi with hT | hT'
        · rcases Ty.indexes_substTy_sub .nu i 0 (.fvar X) T hT with hT | hf
          · exact Or.inl (by simp [Ty.indexesList, hT])
          · simp [Ty.indexes] at hf
        · rcases Ty.indexes_substTy_sub .nu i 0 (.fvar X) T' hT' with hT' | hf
          · exact Or.inr (by simp [Ty.indexesList, hT'])
          · simp [Ty.indexes] at hf
    · obtain ⟨hctx, hstr, hup, hvars⟩ := ih₂ c hc
      refine ⟨hctx, hstr, hup, ?_⟩
      rcases hvars with hmu | hnu
      · exact Or.inl fun i hi => (hmu i hi).imp
          (fun hS => by simp [Ty.indexesList, hS]) (fun hS' => by simp [Ty.indexesList, hS'])
      · exact Or.inr fun i hi => (hnu i hi).imp
          (fun hS => by simp [Ty.indexesList, hS]) (fun hS' => by simp [Ty.indexesList, hS'])

/-! ## Theorems 11 & 12: Constraints generated by call-site inference and clause checking -/

/-- Classification of every constraint generated during call-site inference and checking:
1. A strict step constraint `j < a^↑` from a constructor (`cons`) or projection (`proj`), with
   `FlexName j` and `(j, π, c.ctx) ∈ Φ`;
2. A call-bound constraint `k < b[a⃗/Ψ_g]` from `callBounds`, with `FlexName k`; or
3. A comparison constraint `lhs ≤ rhs^↑` from `Compare Ψ' Δ' A₁ B₁ .star C₂` satisfying
   `CompareConstrOrigin Ψ' A₁ B₁ c`. -/
def InfConstrOrigin (Φ : List FlexVar) (c : SConstr) : Prop :=
  (∃ j π, FlexName j ∧ ⟨j, π, c.ctx⟩ ∈ Φ ∧ (π = .pos ∨ π = .neg) ∧
    c.lhs = .var j 0 ∧ c.strict = true ∧ c.up = true) ∨
  (∃ k, FlexName k ∧ c.lhs = .var k 0 ∧ c.strict = true ∧ c.up = false) ∨
  (∃ A₁ B₁, CompareConstrOrigin c.ctx A₁ B₁ c)

theorem InfConstrOrigin.mono_flex {Φ Φ' : List FlexVar} {c : SConstr}
    (hsub : ∀ v ∈ Φ, v ∈ Φ') (h : InfConstrOrigin Φ c) : InfConstrOrigin Φ' c := by
  rcases h with ⟨j, π, hj, hv, hπ, hlhs, hstr, hup⟩ | hcall | hcmp
  · exact Or.inl ⟨j, π, hj, hsub _ hv, hπ, hlhs, hstr, hup⟩
  · exact Or.inr (Or.inl hcall)
  · exact Or.inr (Or.inr hcmp)

theorem callBounds_origin {Ψ : SizeCtx} {g : FunDecl} {as : List Nat}
    (hflex : ∀ k ∈ as, FlexName k) {Φ : List FlexVar} {c : SConstr}
    (hc : c ∈ callBounds Ψ g (as.map fun k => .var k 0)) : InfConstrOrigin Φ c := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc
  have hm := (List.of_mem_zip hp).2
  obtain ⟨k, hk, heq⟩ := List.mem_map.mp hm
  exact Or.inr (Or.inl ⟨k, hflex k hk, heq.symm, rfl, rfl⟩)

/-- **Theorems 11 & 12** (Structure of constraints in call-site inference, checking, and clauses,
Sections 6.3.4–6.3.5, pp. 53–56): every constraint `c ∈ C` emitted by `InferTm`, `CheckTm`, or
`CheckClause` satisfies `InfConstrOrigin Φ c`: strict constraints always have a fresh flexible
variable `.var j 0` (`FlexName j`) on the left-hand side (never a rigid variable), and non-strict
constraints come from `Compare` (`CompareConstrOrigin`). -/
theorem theorems_11_and_12 {Ω : InfEnv} :
    (∀ {Ψ Θ Γ r A Φ C T K},
      InferTm Ω Ψ Θ Γ r A Φ C T K → ∀ c ∈ C, InfConstrOrigin Φ c) ∧
    (∀ {Ψ Θ Γ A t Φ C T K},
      CheckTm Ω Ψ Θ Γ A t Φ C T K → ∀ c ∈ C, InfConstrOrigin Φ c) ∧
    (∀ {Ψ Θ Γ A cl Φ C T K},
      CheckClause Ω Ψ Θ Γ A cl Φ C T K → ∀ c ∈ C, InfConstrOrigin Φ c) := by
  let P₁ := fun (Ψ : SizeCtx) (Θ : TyCtx) (Γ : TermCtx) (r : Tm) (A : Ty) (Φ : List FlexVar)
      (C : List SConstr) (T : List Nat) (K : List CallRec)
      (_ : InferTm Ω Ψ Θ Γ r A Φ C T K) => ∀ c ∈ C, InfConstrOrigin Φ c
  let P₂ := fun (Ψ : SizeCtx) (Θ : TyCtx) (Γ : TermCtx) (A : Ty) (t : Tm) (Φ : List FlexVar)
      (C : List SConstr) (T : List Nat) (K : List CallRec)
      (_ : CheckTm Ω Ψ Θ Γ A t Φ C T K) => ∀ c ∈ C, InfConstrOrigin Φ c
  let P₃ := fun (Ψ : SizeCtx) (Θ : TyCtx) (Γ : TermCtx) (A : Ty) (D : List Clause)
      (Φ : List FlexVar) (C : List SConstr) (T : List Nat) (K : List CallRec)
      (_ : CheckClauses Ω Ψ Θ Γ A D Φ C T K) => ∀ c ∈ C, InfConstrOrigin Φ c
  let P₄ := fun (Ψ : SizeCtx) (Θ : TyCtx) (Γ : TermCtx) (A : Ty) (cl : Clause)
      (Φ : List FlexVar) (C : List SConstr) (T : List Nat) (K : List CallRec)
      (_ : CheckClause Ω Ψ Θ Γ A cl Φ C T K) => ∀ c ∈ C, InfConstrOrigin Φ c
  have sVar : ∀ {Ψ Θ Γ x A} (hx : Γ.lookup x = some A), P₁ Ψ Θ Γ (.var x) A [] [] [] []
      (.var hx) := by intro _ _ _ _ _ _ _ h; simp at h
  have sApp : ∀ {Ψ Θ Γ r s A B Φ₁ Φ₂ C₁ C₂ T₁ T₂ K₁ K₂}
      (hr : InferTm Ω Ψ Θ Γ r (.arr A B) Φ₁ C₁ T₁ K₁) (hs : CheckTm Ω Ψ Θ Γ A s Φ₂ C₂ T₂ K₂),
      P₁ Ψ Θ Γ r (.arr A B) Φ₁ C₁ T₁ K₁ hr → P₂ Ψ Θ Γ A s Φ₂ C₂ T₂ K₂ hs →
      P₁ Ψ Θ Γ (.app r (.term s)) B (Φ₁ ++ Φ₂) (C₁ ++ C₂) (T₁ ++ T₂) (K₁ ++ K₂) (.app hr hs) := by
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih₁ ih₂ c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact (ih₁ c hc).mono_flex (fun v hv => List.mem_append_left _ hv)
    · exact (ih₂ c hc).mono_flex (fun v hv => List.mem_append_right _ hv)
  have sProj : ∀ {Ψ Θ Γ r a R d j Rd Φ C T K} (hr : InferTm Ω Ψ Θ Γ r (.nu a R) Φ C T K)
      (hd : R[d]? = some Rd) (hj : FlexName j),
      P₁ Ψ Θ Γ r (.nu a R) Φ C T K hr →
      P₁ Ψ Θ Γ (.app r (.proj d)) (Rd.substTy 0 (.nu (.var j 0) R))
        (⟨j, .neg, Ψ⟩ :: Φ) (⟨Ψ, .var j 0, a, true, true⟩ :: C)
        ((if Rd.hasBVar 0 then [] else [j]) ++ T) K (.proj hr hd hj) := by
    intro _ _ _ _ _ _ _ j _ _ _ _ _ _ _ hj ih c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact Or.inl ⟨j, .neg, hj, by simp, Or.inr rfl, rfl, rfl, rfl⟩
    · exact (ih c hc).mono_flex (fun v hv => List.mem_cons_of_mem _ hv)
  have sInst : ∀ {Ψ Θ Γ r κ B G G' ΨG Φ C T K} (hr : InferTm Ω Ψ Θ Γ r (.allT κ B) Φ C T K)
      (hG : Unsized G) (hkG : EKinding Θ.toK [] G κ)
      (henc : Encode .mix FlexName .mix Θ.toK [] G ΨG G'),
      P₁ Ψ Θ Γ r (.allT κ B) Φ C T K hr →
      P₁ Ψ Θ Γ (.app r .inst) (B.substTy 0 G') (encFlex Ψ ΨG ++ Φ) C T K
        (.inst hr hG hkG henc) := by
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih c hc
    exact (ih c hc).mono_flex (fun v hv => List.mem_append_right _ hv)
  have sGlobal : ∀ {Ψ Θ Γ g as} (hg : g ∈ Ω.sig) (hlen : as.length = g.sizeParams.length)
      (hflex : ∀ k ∈ as, FlexName k),
      P₁ Ψ Θ Γ (.fn g.name) (g.ty.substSize (g.sizeParams.dom.zip (as.map fun k => .var k 0)))
        (callFlex Ψ g as) (callBounds Ψ g (as.map fun k => .var k 0)) [] []
        (.global hg hlen hflex) := by
    intro _ _ _ _ _ _ _ hflex c hc
    exact callBounds_origin hflex hc
  have sLocal : ∀ {Ψ Θ Γ g as} (hg : g ∈ Ω.block) (hlen : as.length = g.sizeParams.length)
      (hflex : ∀ k ∈ as, FlexName k),
      P₁ Ψ Θ Γ (.fn g.name) (g.ty.substSize (g.sizeParams.dom.zip (as.map fun k => .var k 0)))
        (callFlex Ψ g as) (callBounds Ψ g (as.map fun k => .var k 0)) []
        [⟨Ψ, g.name, as.map fun k => .var k 0⟩] (.local hg hlen hflex) := by
    intro _ _ _ _ _ _ _ hflex c hc
    exact callBounds_origin hflex hc
  have sUnit : ∀ {Ψ Θ Γ}, P₂ Ψ Θ Γ .unit .unit [] [] [] [] .unit := by
    intro _ _ _ _ h; simp at h
  have sPair : ∀ {Ψ Θ Γ t u A B Φ₁ Φ₂ C₁ C₂ T₁ T₂ K₁ K₂}
      (ht : CheckTm Ω Ψ Θ Γ A t Φ₁ C₁ T₁ K₁) (hu : CheckTm Ω Ψ Θ Γ B u Φ₂ C₂ T₂ K₂),
      P₂ Ψ Θ Γ A t Φ₁ C₁ T₁ K₁ ht → P₂ Ψ Θ Γ B u Φ₂ C₂ T₂ K₂ hu →
      P₂ Ψ Θ Γ (.prod A B) (.pair t u) (Φ₁ ++ Φ₂) (C₁ ++ C₂) (T₁ ++ T₂) (K₁ ++ K₂)
        (.pair ht hu) := by
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih₁ ih₂ c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact (ih₁ c hc).mono_flex (fun v hv => List.mem_append_left _ hv)
    · exact (ih₂ c hc).mono_flex (fun v hv => List.mem_append_right _ hv)
  have sCons : ∀ {Ψ Θ Γ c j t a S Sc Φ C T K} (hc : S[c]? = some Sc) (hj : FlexName j)
      (ht : CheckTm Ω Ψ Θ Γ (Sc.substTy 0 (.mu (.var j 0) S)) t Φ C T K),
      P₂ Ψ Θ Γ (Sc.substTy 0 (.mu (.var j 0) S)) t Φ C T K ht →
      P₂ Ψ Θ Γ (.mu a S) (.cons c t) (⟨j, .pos, Ψ⟩ :: Φ)
        (⟨Ψ, .var j 0, a, true, true⟩ :: C) ((if Sc.hasBVar 0 then [] else [j]) ++ T) K
        (.cons hc hj ht) := by
    intro _ _ _ _ j _ _ _ _ _ _ _ _ _ hj _ ih c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact Or.inl ⟨j, .pos, hj, by simp, Or.inl rfl, rfl, rfl, rfl⟩
    · exact (ih c hc).mono_flex (fun v hv => List.mem_cons_of_mem _ hv)
  have sPack : ∀ {Ψ Θ Γ t κ B G G' ΨG Φ C T K} (hG : Unsized G) (hkG : EKinding Θ.toK [] G κ)
      (henc : Encode .mix FlexName .mix Θ.toK [] G ΨG G')
      (ht : CheckTm Ω Ψ Θ Γ (B.substTy 0 G') t Φ C T K),
      P₂ Ψ Θ Γ (B.substTy 0 G') t Φ C T K ht →
      P₂ Ψ Θ Γ (.exT κ B) (.pack t) (encFlex Ψ ΨG ++ Φ) C T K (.pack hG hkG henc ht) := by
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih c hc
    exact (ih c hc).mono_flex (fun v hv => List.mem_append_right _ hv)
  have sLam : ∀ {Ψ Θ Γ A D Φ C T K} (hD : CheckClauses Ω Ψ Θ Γ A D Φ C T K),
      P₃ Ψ Θ Γ A D Φ C T K hD → P₂ Ψ Θ Γ A (.lam D) Φ C T K (.lam hD) := by
    intro _ _ _ _ _ _ _ _ _ _ ih; exact ih
  have sSub : ∀ {Ψ Θ Γ r A B Φ C₁ C₂ T K} (hr : InferTm Ω Ψ Θ Γ r A Φ C₁ T K)
      (hcmp : Compare Ψ Θ.toK A B .star C₂),
      P₁ Ψ Θ Γ r A Φ C₁ T K hr → P₂ Ψ Θ Γ B r Φ (C₁ ++ C₂) T K (.sub hr hcmp) := by
    intro Ψ _ _ _ A B _ _ _ _ _ _ hcmp ih c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact ih c hc
    · have h10 := theorem_10 hcmp c hc
      exact Or.inr (Or.inr ⟨A, B, h10.1.symm ▸ h10⟩)
  have sNil : ∀ {Ψ Θ Γ A}, P₃ Ψ Θ Γ A [] [] [] [] [] .nil := by
    intro _ _ _ _ _ h; simp at h
  have sConsCl : ∀ {Ψ Θ Γ A cl D Φ₁ Φ₂ C₁ C₂ T₁ T₂ K₁ K₂}
      (hcl : CheckClause Ω Ψ Θ Γ A cl Φ₁ C₁ T₁ K₁)
      (hD : CheckClauses Ω Ψ Θ Γ A D Φ₂ C₂ T₂ K₂),
      P₄ Ψ Θ Γ A cl Φ₁ C₁ T₁ K₁ hcl → P₃ Ψ Θ Γ A D Φ₂ C₂ T₂ K₂ hD →
      P₃ Ψ Θ Γ A (cl :: D) (Φ₁ ++ Φ₂) (C₁ ++ C₂) (T₁ ++ T₂) (K₁ ++ K₂) (.cons hcl hD) := by
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih₁ ih₂ c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact (ih₁ c hc).mono_flex (fun v hv => List.mem_append_left _ hv)
    · exact (ih₂ c hc).mono_flex (fun v hv => List.mem_append_right _ hv)
  have sClause : ∀ {Ψ Ψ' Θ Θ' Γ Γ' A C qs t Φ Cs T K}
      (hsp : InferSpine Ψ Θ qs A Γ' Ψ' Θ' C)
      (ht : CheckTm Ω (Ψ ++ Ψ') (Θ ++ Θ') (Γ' ++ Γ) C t Φ Cs T K),
      P₂ (Ψ ++ Ψ') (Θ ++ Θ') (Γ' ++ Γ) C t Φ Cs T K ht →
      P₄ Ψ Θ Γ A (.mk qs t) Φ Cs T K (.mk hsp ht) := by
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih; exact ih
  exact ⟨fun h => @InferTm.rec Ω P₁ P₂ P₃ P₄ @sVar @sApp @sProj @sInst @sGlobal @sLocal @sUnit
      @sPair @sCons @sPack @sLam @sSub @sNil @sConsCl @sClause _ _ _ _ _ _ _ _ _ h,
    fun h => @CheckTm.rec Ω P₁ P₂ P₃ P₄ @sVar @sApp @sProj @sInst @sGlobal @sLocal @sUnit
      @sPair @sCons @sPack @sLam @sSub @sNil @sConsCl @sClause _ _ _ _ _ _ _ _ _ h,
    fun h => @CheckClause.rec Ω P₁ P₂ P₃ P₄ @sVar @sApp @sProj @sInst @sGlobal @sLocal @sUnit
      @sPair @sCons @sPack @sLam @sSub @sNil @sConsCl @sClause _ _ _ _ _ _ _ _ _ h⟩

end NishtAbel2024V5

/-! ## Solutions/V5/InfMain.lean -/

/-! # V5 inference: solver post-check soundness (Theorem 14) and Algorithm 2 soundness (Theorem 15) -/

namespace NishtAbel2024V5

open NishtAbel2024V2 (InvGraph InvGraphFamily SCTValid ConformsToGraph FunName EdgeRel)

/-! ## Flexible domain of Algorithm 1 (`solve`) and Theorem 14 -/

theorem foldl_preserves {α β : Type} {P : α → Prop} {f : α → β → α}
    (hf : ∀ a b, P a → P (f a b)) : ∀ (L : List β) {a : α}, P a → P (L.foldl f a)
  | [], _, ha => ha
  | b :: L, _, ha => foldl_preserves hf L (hf _ b ha)

theorem solveRound_flexDom (fuel : Nat) (Φ : List FlexVar) (C : List SConstr) (T : List Nat)
    (hΦ : ∀ v ∈ Φ, FlexName v.name) {φ : FlexSubst} (hφ : FlexDom φ) :
    FlexDom (solveRound fuel Φ C T φ) := by
  unfold solveRound
  refine foldl_preserves (fun ψ v hψ => ?_) Φ hφ
  split
  · exact hψ
  · dsimp only
    split
    · exact hψ
    · intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hp
        have hm' : m ∈ Φ.map FlexVar.name := (List.mem_filter.mp hm).1
        obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hm'
        exact hΦ w hw
      · exact hψ p hp

theorem solve_flexDom (fuel : Nat) (Φ : List FlexVar) (C : List SConstr) (T : List Nat)
    (hΦ : ∀ v ∈ Φ, FlexName v.name) : FlexDom (solve fuel Φ C T) := by
  unfold solve
  have hfold : FlexDom ((List.range (Φ.length + 1)).foldl
      (fun φ _ => solveRound fuel Φ C T φ) []) :=
    foldl_preserves (fun φ _ hφ => solveRound_flexDom fuel Φ C T hΦ hφ)
      (List.range (Φ.length + 1)) (fun _ h => by simp at h)
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · exact hfold p hp
  · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hp
    exact hΦ v hv

/-- **Theorem 14** (Soundness of the post-checked constraint solver, Section 6.4): if all flexible
variables in `Φ` have odd names and the solution `φ* = solve fuel Φ C T` passes `checkScope` and
`checkCoherent`, then `φ*` has flexible domain, satisfies `ScopeOK φ* Φ`, and is coherent with `C`
(`Coherent φ* C`). -/
theorem theorem_14 (fuel : Nat) (Φ : List FlexVar) (C : List SConstr) (T : List Nat)
    (hΦ : ∀ v ∈ Φ, FlexName v.name)
    (hscope : checkScope (solve fuel Φ C T) Φ = true)
    (hcoh : checkCoherent fuel (solve fuel Φ C T) C = true) :
    FlexDom (solve fuel Φ C T) ∧
      ScopeOK (solve fuel Φ C T) Φ ∧
      Coherent (solve fuel Φ C T) C :=
  ⟨solve_flexDom fuel Φ C T hΦ, checkScope_sound hscope, checkCoherent_sound hcoh⟩

/-! ## Inference only generates flexible variable names -/

theorem encFlex_flex {Ψ ΨG : SizeCtx} (h : ∀ i ∈ ΨG.dom, FlexName i) :
    ∀ v ∈ encFlex Ψ ΨG, FlexName v.name := by
  intro v hv
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hv
  exact h p.1 (List.mem_map.mpr ⟨p, hp, rfl⟩)

theorem callFlex_flex {Ψ : SizeCtx} {g : FunDecl} {as : List Nat} (h : ∀ k ∈ as, FlexName k) :
    ∀ v ∈ callFlex Ψ g as, FlexName v.name := by
  intro v hv
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hv
  exact h p.2 (List.of_mem_zip hp).2

theorem inference_flex {Ω : InfEnv} :
    (∀ {Ψ Θ Γ r A Φ C T K}, InferTm Ω Ψ Θ Γ r A Φ C T K → ∀ v ∈ Φ, FlexName v.name) ∧
    (∀ {Ψ Θ Γ A t Φ C T K}, CheckTm Ω Ψ Θ Γ A t Φ C T K → ∀ v ∈ Φ, FlexName v.name) ∧
    (∀ {Ψ Θ Γ A cl Φ C T K}, CheckClause Ω Ψ Θ Γ A cl Φ C T K → ∀ v ∈ Φ, FlexName v.name) := by
  let P₁ := fun (Ψ : SizeCtx) (Θ : TyCtx) (Γ : TermCtx) (r : Tm) (A : Ty) (Φ : List FlexVar)
      (C : List SConstr) (T : List Nat) (K : List CallRec)
      (_ : InferTm Ω Ψ Θ Γ r A Φ C T K) => ∀ v ∈ Φ, FlexName v.name
  let P₂ := fun (Ψ : SizeCtx) (Θ : TyCtx) (Γ : TermCtx) (A : Ty) (t : Tm) (Φ : List FlexVar)
      (C : List SConstr) (T : List Nat) (K : List CallRec)
      (_ : CheckTm Ω Ψ Θ Γ A t Φ C T K) => ∀ v ∈ Φ, FlexName v.name
  let P₃ := fun (Ψ : SizeCtx) (Θ : TyCtx) (Γ : TermCtx) (A : Ty) (D : List Clause)
      (Φ : List FlexVar) (C : List SConstr) (T : List Nat) (K : List CallRec)
      (_ : CheckClauses Ω Ψ Θ Γ A D Φ C T K) => ∀ v ∈ Φ, FlexName v.name
  let P₄ := fun (Ψ : SizeCtx) (Θ : TyCtx) (Γ : TermCtx) (A : Ty) (cl : Clause)
      (Φ : List FlexVar) (C : List SConstr) (T : List Nat) (K : List CallRec)
      (_ : CheckClause Ω Ψ Θ Γ A cl Φ C T K) => ∀ v ∈ Φ, FlexName v.name
  have sVar : ∀ {Ψ Θ Γ x A} (hx : Γ.lookup x = some A), P₁ Ψ Θ Γ (.var x) A [] [] [] []
      (.var hx) := by intro _ _ _ _ _ _ _ h; simp at h
  have sApp : ∀ {Ψ Θ Γ r s A B Φ₁ Φ₂ C₁ C₂ T₁ T₂ K₁ K₂}
      (hr : InferTm Ω Ψ Θ Γ r (.arr A B) Φ₁ C₁ T₁ K₁) (hs : CheckTm Ω Ψ Θ Γ A s Φ₂ C₂ T₂ K₂),
      P₁ Ψ Θ Γ r (.arr A B) Φ₁ C₁ T₁ K₁ hr → P₂ Ψ Θ Γ A s Φ₂ C₂ T₂ K₂ hs →
      P₁ Ψ Θ Γ (.app r (.term s)) B (Φ₁ ++ Φ₂) (C₁ ++ C₂) (T₁ ++ T₂) (K₁ ++ K₂) (.app hr hs) := by
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih₁ ih₂ v hv
    rcases List.mem_append.mp hv with hv | hv
    · exact ih₁ v hv
    · exact ih₂ v hv
  have sProj : ∀ {Ψ Θ Γ r a R d j Rd Φ C T K} (hr : InferTm Ω Ψ Θ Γ r (.nu a R) Φ C T K)
      (hd : R[d]? = some Rd) (hj : FlexName j),
      P₁ Ψ Θ Γ r (.nu a R) Φ C T K hr →
      P₁ Ψ Θ Γ (.app r (.proj d)) (Rd.substTy 0 (.nu (.var j 0) R))
        (⟨j, .neg, Ψ⟩ :: Φ) (⟨Ψ, .var j 0, a, true, true⟩ :: C)
        ((if Rd.hasBVar 0 then [] else [j]) ++ T) K (.proj hr hd hj) := by
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hj ih v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact hj
    · exact ih v hv
  have sInst : ∀ {Ψ Θ Γ r κ B G G' ΨG Φ C T K} (hr : InferTm Ω Ψ Θ Γ r (.allT κ B) Φ C T K)
      (hG : Unsized G) (hkG : EKinding Θ.toK [] G κ)
      (henc : Encode .mix FlexName .mix Θ.toK [] G ΨG G'),
      P₁ Ψ Θ Γ r (.allT κ B) Φ C T K hr →
      P₁ Ψ Θ Γ (.app r .inst) (B.substTy 0 G') (encFlex Ψ ΨG ++ Φ) C T K
        (.inst hr hG hkG henc) := by
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ henc ih v hv
    rcases List.mem_append.mp hv with hv | hv
    · exact encFlex_flex (encode_facts henc).2.2.1 v hv
    · exact ih v hv
  have sGlobal : ∀ {Ψ Θ Γ g as} (hg : g ∈ Ω.sig) (hlen : as.length = g.sizeParams.length)
      (hflex : ∀ k ∈ as, FlexName k),
      P₁ Ψ Θ Γ (.fn g.name) (g.ty.substSize (g.sizeParams.dom.zip (as.map fun k => .var k 0)))
        (callFlex Ψ g as) (callBounds Ψ g (as.map fun k => .var k 0)) [] []
        (.global hg hlen hflex) := by
    intro _ _ _ _ _ _ _ hflex v hv
    exact callFlex_flex hflex v hv
  have sLocal : ∀ {Ψ Θ Γ g as} (hg : g ∈ Ω.block) (hlen : as.length = g.sizeParams.length)
      (hflex : ∀ k ∈ as, FlexName k),
      P₁ Ψ Θ Γ (.fn g.name) (g.ty.substSize (g.sizeParams.dom.zip (as.map fun k => .var k 0)))
        (callFlex Ψ g as) (callBounds Ψ g (as.map fun k => .var k 0)) []
        [⟨Ψ, g.name, as.map fun k => .var k 0⟩] (.local hg hlen hflex) := by
    intro _ _ _ _ _ _ _ hflex v hv
    exact callFlex_flex hflex v hv
  have sUnit : ∀ {Ψ Θ Γ}, P₂ Ψ Θ Γ .unit .unit [] [] [] [] .unit := by
    intro _ _ _ _ h; simp at h
  have sPair : ∀ {Ψ Θ Γ t u A B Φ₁ Φ₂ C₁ C₂ T₁ T₂ K₁ K₂}
      (ht : CheckTm Ω Ψ Θ Γ A t Φ₁ C₁ T₁ K₁) (hu : CheckTm Ω Ψ Θ Γ B u Φ₂ C₂ T₂ K₂),
      P₂ Ψ Θ Γ A t Φ₁ C₁ T₁ K₁ ht → P₂ Ψ Θ Γ B u Φ₂ C₂ T₂ K₂ hu →
      P₂ Ψ Θ Γ (.prod A B) (.pair t u) (Φ₁ ++ Φ₂) (C₁ ++ C₂) (T₁ ++ T₂) (K₁ ++ K₂)
        (.pair ht hu) := by
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih₁ ih₂ v hv
    rcases List.mem_append.mp hv with hv | hv
    · exact ih₁ v hv
    · exact ih₂ v hv
  have sCons : ∀ {Ψ Θ Γ c j t a S Sc Φ C T K} (hc : S[c]? = some Sc) (hj : FlexName j)
      (ht : CheckTm Ω Ψ Θ Γ (Sc.substTy 0 (.mu (.var j 0) S)) t Φ C T K),
      P₂ Ψ Θ Γ (Sc.substTy 0 (.mu (.var j 0) S)) t Φ C T K ht →
      P₂ Ψ Θ Γ (.mu a S) (.cons c t) (⟨j, .pos, Ψ⟩ :: Φ)
        (⟨Ψ, .var j 0, a, true, true⟩ :: C) ((if Sc.hasBVar 0 then [] else [j]) ++ T) K
        (.cons hc hj ht) := by
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ hj _ ih v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact hj
    · exact ih v hv
  have sPack : ∀ {Ψ Θ Γ t κ B G G' ΨG Φ C T K} (hG : Unsized G) (hkG : EKinding Θ.toK [] G κ)
      (henc : Encode .mix FlexName .mix Θ.toK [] G ΨG G')
      (ht : CheckTm Ω Ψ Θ Γ (B.substTy 0 G') t Φ C T K),
      P₂ Ψ Θ Γ (B.substTy 0 G') t Φ C T K ht →
      P₂ Ψ Θ Γ (.exT κ B) (.pack t) (encFlex Ψ ΨG ++ Φ) C T K (.pack hG hkG henc ht) := by
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ henc _ ih v hv
    rcases List.mem_append.mp hv with hv | hv
    · exact encFlex_flex (encode_facts henc).2.2.1 v hv
    · exact ih v hv
  have sLam : ∀ {Ψ Θ Γ A D Φ C T K} (hD : CheckClauses Ω Ψ Θ Γ A D Φ C T K),
      P₃ Ψ Θ Γ A D Φ C T K hD → P₂ Ψ Θ Γ A (.lam D) Φ C T K (.lam hD) := by
    intro _ _ _ _ _ _ _ _ _ _ ih; exact ih
  have sSub : ∀ {Ψ Θ Γ r A B Φ C₁ C₂ T K} (hr : InferTm Ω Ψ Θ Γ r A Φ C₁ T K)
      (hcmp : Compare Ψ Θ.toK A B .star C₂),
      P₁ Ψ Θ Γ r A Φ C₁ T K hr → P₂ Ψ Θ Γ B r Φ (C₁ ++ C₂) T K (.sub hr hcmp) := by
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ ih; exact ih
  have sNil : ∀ {Ψ Θ Γ A}, P₃ Ψ Θ Γ A [] [] [] [] [] .nil := by
    intro _ _ _ _ _ h; simp at h
  have sConsCl : ∀ {Ψ Θ Γ A cl D Φ₁ Φ₂ C₁ C₂ T₁ T₂ K₁ K₂}
      (hcl : CheckClause Ω Ψ Θ Γ A cl Φ₁ C₁ T₁ K₁)
      (hD : CheckClauses Ω Ψ Θ Γ A D Φ₂ C₂ T₂ K₂),
      P₄ Ψ Θ Γ A cl Φ₁ C₁ T₁ K₁ hcl → P₃ Ψ Θ Γ A D Φ₂ C₂ T₂ K₂ hD →
      P₃ Ψ Θ Γ A (cl :: D) (Φ₁ ++ Φ₂) (C₁ ++ C₂) (T₁ ++ T₂) (K₁ ++ K₂) (.cons hcl hD) := by
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih₁ ih₂ v hv
    rcases List.mem_append.mp hv with hv | hv
    · exact ih₁ v hv
    · exact ih₂ v hv
  have sClause : ∀ {Ψ Ψ' Θ Θ' Γ Γ' A C qs t Φ Cs T K}
      (hsp : InferSpine Ψ Θ qs A Γ' Ψ' Θ' C)
      (ht : CheckTm Ω (Ψ ++ Ψ') (Θ ++ Θ') (Γ' ++ Γ) C t Φ Cs T K),
      P₂ (Ψ ++ Ψ') (Θ ++ Θ') (Γ' ++ Γ) C t Φ Cs T K ht →
      P₄ Ψ Θ Γ A (.mk qs t) Φ Cs T K (.mk hsp ht) := by
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih; exact ih
  exact ⟨fun h => @InferTm.rec Ω P₁ P₂ P₃ P₄ @sVar @sApp @sProj @sInst @sGlobal @sLocal @sUnit
      @sPair @sCons @sPack @sLam @sSub @sNil @sConsCl @sClause _ _ _ _ _ _ _ _ _ h,
    fun h => @CheckTm.rec Ω P₁ P₂ P₃ P₄ @sVar @sApp @sProj @sInst @sGlobal @sLocal @sUnit
      @sPair @sCons @sPack @sLam @sSub @sNil @sConsCl @sClause _ _ _ _ _ _ _ _ _ h,
    fun h => @CheckClause.rec Ω P₁ P₂ P₃ P₄ @sVar @sApp @sProj @sInst @sGlobal @sLocal @sUnit
      @sPair @sCons @sPack @sLam @sSub @sNil @sConsCl @sClause _ _ _ _ _ _ _ _ _ h⟩

/-! ## Rigid types and contexts are invariant under flexible substitutions -/

theorem Size.subst_eq_self (φ : FlexSubst) :
    ∀ (a : Size), (∀ i ∈ a.fvars, φ.lookup i = none) → a.subst φ = a
  | .inf _, _ => rfl
  | .bvar _ _, _ => rfl
  | .var i n, h => by simp [Size.subst, h i (by simp [Size.fvars])]
  | .meet a b, h => by
    simp only [Size.fvars, List.mem_append] at h
    simp [Size.subst, Size.subst_eq_self φ a (fun i hi => h i (Or.inl hi)),
      Size.subst_eq_self φ b (fun i hi => h i (Or.inr hi))]

mutual

theorem Ty.substSize_eq_self (φ : FlexSubst) :
    ∀ (A : Ty), (∀ i ∈ A.sizeVars, φ.lookup i = none) → A.substSize φ = A
  | .unit, _ => rfl
  | .var _, _ => rfl
  | .fvar _, _ => rfl
  | .prod A B, h => by
    simp only [Ty.sizeVars, List.mem_append] at h
    simp [Ty.substSize, Ty.substSize_eq_self φ A (fun i hi => h i (Or.inl hi)),
      Ty.substSize_eq_self φ B (fun i hi => h i (Or.inr hi))]
  | .arr A B, h => by
    simp only [Ty.sizeVars, List.mem_append] at h
    simp [Ty.substSize, Ty.substSize_eq_self φ A (fun i hi => h i (Or.inl hi)),
      Ty.substSize_eq_self φ B (fun i hi => h i (Or.inr hi))]
  | .app F G _, h => by
    simp only [Ty.sizeVars, List.mem_append] at h
    simp [Ty.substSize, Ty.substSize_eq_self φ F (fun i hi => h i (Or.inl hi)),
      Ty.substSize_eq_self φ G (fun i hi => h i (Or.inr hi))]
  | .lam _ F, h => by simp [Ty.substSize, Ty.substSize_eq_self φ F h]
  | .allT _ B, h => by simp [Ty.substSize, Ty.substSize_eq_self φ B h]
  | .exT _ B, h => by simp [Ty.substSize, Ty.substSize_eq_self φ B h]
  | .allS a B, h => by
    simp only [Ty.sizeVars, List.mem_append] at h
    simp [Ty.substSize, Size.subst_eq_self φ a (fun i hi => h i (Or.inl hi)),
      Ty.substSize_eq_self φ B (fun i hi => h i (Or.inr hi))]
  | .exS a B, h => by
    simp only [Ty.sizeVars, List.mem_append] at h
    simp [Ty.substSize, Size.subst_eq_self φ a (fun i hi => h i (Or.inl hi)),
      Ty.substSize_eq_self φ B (fun i hi => h i (Or.inr hi))]
  | .mu a S, h => by
    simp only [Ty.sizeVars, List.mem_append] at h
    simp [Ty.substSize, Size.subst_eq_self φ a (fun i hi => h i (Or.inl hi)),
      Ty.substSizeList_eq_self φ S (fun i hi => h i (Or.inr hi))]
  | .nu a R, h => by
    simp only [Ty.sizeVars, List.mem_append] at h
    simp [Ty.substSize, Size.subst_eq_self φ a (fun i hi => h i (Or.inl hi)),
      Ty.substSizeList_eq_self φ R (fun i hi => h i (Or.inr hi))]

theorem Ty.substSizeList_eq_self (φ : FlexSubst) :
    ∀ (S : List Ty), (∀ i ∈ Ty.sizeVarsList S, φ.lookup i = none) → Ty.substSizeList φ S = S
  | [], _ => rfl
  | A :: S, h => by
    simp only [Ty.sizeVarsList, List.mem_append] at h
    simp [Ty.substSizeList, Ty.substSize_eq_self φ A (fun i hi => h i (Or.inl hi)),
      Ty.substSizeList_eq_self φ S (fun i hi => h i (Or.inr hi))]

end

theorem SizeCtx.substBounds_of_inf (φ : FlexSubst) :
    ∀ (Ψ : SizeCtx), (∀ p ∈ Ψ, p.2 = .inf 0) → Ψ.substBounds φ = Ψ
  | [], _ => rfl
  | (i, a) :: Ψ, hb => by
    have ha : a = .inf 0 := hb (i, a) (by simp)
    subst ha
    simp only [SizeCtx.substBounds_cons, Size.subst]
    rw [SizeCtx.substBounds_of_inf φ Ψ (fun p hp => hb p (List.mem_cons_of_mem _ hp))]

/-! ## Invocation graphs and Algorithm 2 -/

theorem callGraph_conforms (fuel : Nat) (Ψf : SizeCtx) (φ : FlexSubst) (k : CallRec) :
    ConformsToGraph (SizeLt (k.ctx.substBounds φ)) (SizeLe (k.ctx.substBounds φ))
      (callGraph fuel Ψf φ k) (k.args.map (Size.subst φ)) (Ψf.map fun p => Size.var p.1 0) := by
  refine ⟨rfl, by simp [callGraph], ?_⟩
  intro i j hi hj
  have hi' : i < (k.args.map (Size.subst φ)).length := hi
  have hj' : j < Ψf.length := by simpa [callGraph] using hj
  have hlook := NishtAbel2024V2.canonical_lookup (k.args.map (Size.subst φ)).length Ψf.length
    (fun i j =>
      match (k.args.map (Size.subst φ))[i]?, Ψf[j]? with
      | some a, some p =>
        if sizeLtB fuel (k.ctx.substBounds φ) a (.var p.1 0) then some .lt
        else if sizeLeB fuel (k.ctx.substBounds φ) a (.var p.1 0) then some .le
        else none
      | _, _ => none) i j hi' hj'
  have hlook' : (callGraph fuel Ψf φ k).edgeAt i j = _ := hlook
  rw [hlook', List.getElem?_eq_getElem hi', List.getElem?_eq_getElem hj']
  simp only [List.get_eq_getElem, List.getElem_map]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · split at h
    · rename_i hlt
      exact sizeLtB_sound _ _ _ _ hlt
    · split at h <;> simp at h
  · split at h
    · simp at h
    · split at h
      · rename_i hle
        exact sizeLeB_sound hle
      · simp at h

theorem blockGraphs_mem (fuel : Nat) (Ξ : List FunDecl) (runs : FunName → Clause → ClauseRun)
    {d : FunDecl} (hd : d ∈ Ξ) {cl : Clause} (hcl : cl ∈ d.clauses)
    {k : CallRec} (hk : k ∈ (runs d.name cl).calls) :
    callGraph fuel d.sizeParams ((runs d.name cl).solution fuel) k ∈
      (blockGraphs fuel Ξ runs).graphs d.name k.callee := by
  simp only [blockGraphs, List.mem_flatMap]
  refine ⟨d, hd, ?_⟩
  simp only [↓reduceIte, List.mem_flatMap, List.mem_map, List.mem_filter, beq_iff_eq]
  exact ⟨cl, hcl, k, ⟨hk, rfl⟩, rfl⟩

theorem blockGraphs_arity (fuel : Nat) (Ξ : List FunDecl) (runs : FunName → Clause → ClauseRun)
    (hnd : (Ξ.map FunDecl.name).Nodup) {d : FunDecl} (hd : d ∈ Ξ) :
    (blockGraphs fuel Ξ runs).arity d.name = d.sizeParams.length := by
  simp only [blockGraphs]
  cases hf : Ξ.find? (fun d' => d'.name == d.name) with
  | none =>
    have := List.find?_eq_none.mp hf d hd
    simp at this
  | some d' =>
    have hd' := List.mem_of_find?_eq_some hf
    have hname : d'.name = d.name := by simpa using List.find?_some hf
    have heq : d' = d := List.inj_on_of_nodup_map hnd hd' hd hname
    rw [heq]

theorem ListRel.mem_right {α β : Type} {R : α → β → Prop} {l₁ : List α} {l₂ : List β}
    (h : ListRel R l₁ l₂) {b : β} (hb : b ∈ l₂) : ∃ a ∈ l₁, R a b := by
  induction h with
  | nil => simp at hb
  | cons hr _ ih =>
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨_, by simp, hr⟩
    · obtain ⟨a, ha, hab⟩ := ih hb
      exact ⟨a, by simp [ha], hab⟩

/-- **Corollary to Theorems 13 & 14** (Section 6.5, p. 59): if `Σ` is well-formed and Algorithm 2
accepts `Ξ` with annotated declarations `Ξannot`, then `Σ ⊢ Ξannot` (`BlockTy sig Ξannot`). -/
theorem algorithm2_typing {sig Ξ Ξannot : List FunDecl} (hsigwf : DeclsWf sig)
    (hacc : Algorithm2Accepts sig Ξ Ξannot) : BlockTy sig Ξannot := by
  obtain ⟨henc_rel, hnd, fuel, runs, hclauses, hsct⟩ := hacc
  have hblockwf : DeclsWf Ξannot := by
    intro d hd
    obtain ⟨d₀, _, hd_enc⟩ := henc_rel.mem_right hd
    exact hd_enc.wf
  refine ⟨blockGraphs fuel Ξannot runs, hsct,
    fun d hd => blockGraphs_arity fuel Ξannot runs hnd hd, ?_⟩
  intro d hd
  obtain ⟨d₀, _, hd_enc⟩ := henc_rel.mem_right hd
  obtain ⟨hwf_Ψ, hwf_ty⟩ := hd_enc.wf
  have henc := hd_enc.2.2.2.2.2
  have hfacts := encode_facts henc
  refine ⟨hwf_Ψ, hwf_ty, fun cl hcl => ?_⟩
  obtain ⟨hcheck, hscope, hcoh⟩ := hclauses d hd cl hcl
  let r := runs d.name cl
  let φ := solve fuel r.flex r.constraints r.nonrecVars
  have hflex : ∀ v ∈ r.flex, FlexName v.name := inference_flex.2.2 hcheck
  obtain ⟨hφ, hsc, hco⟩ := theorem_14 fuel r.flex r.constraints r.nonrecVars hflex hscope hcoh
  have hΨ_eq : d.sizeParams.substBounds φ = d.sizeParams :=
    SizeCtx.substBounds_of_inf φ d.sizeParams hfacts.2.2.2
  have hty_eq : d.ty.substSize φ = d.ty :=
    Ty.substSize_eq_self φ d.ty (fun i hi =>
      hφ.lookup_rigid (hfacts.2.2.1 i (encode_sizeVars_sub henc i hi)))
  have hK : ∀ k ∈ r.calls, sctCallOK (blockGraphs fuel Ξannot runs) d.name d.sizeParams
      (k.ctx.substBounds φ) k.callee (k.args.map (Size.subst φ)) := by
    intro k hk
    exact ⟨callGraph fuel d.sizeParams φ k,
      blockGraphs_mem fuel Ξannot runs hd hcl hk,
      callGraph_conforms fuel d.sizeParams φ k⟩
  have hcl_ty := (inference_sound (Ω := ⟨sig, Ξannot⟩)
    (Ωd := ⟨sig, Ξannot, sctCallOK (blockGraphs fuel Ξannot runs) d.name d.sizeParams⟩)
    (φ := φ) rfl rfl hsigwf hblockwf hφ).2.2 hcheck hco hsc hK
    (fun _ hp => by simp [TermCtx.substSize] at hp)
    (by change KindingC (d.sizeParams.substBounds φ) [] (d.ty.substSize φ) .star
        rw [hΨ_eq, hty_eq]; exact hwf_ty)
  have hΓ_eq : TermCtx.substSize φ [] = [] := rfl
  rw [hΨ_eq, hΓ_eq, hty_eq] at hcl_ty
  exact hcl_ty

/-- **Theorem 15** (Soundness of type-based termination checking, Section 6.5, p. 59): if a mutual
block `Ξ` is accepted by Algorithm 2 with size-annotated declarations `Ξannot` against a
well-formed and semantically valid signature `Σ` in a run-time world `W` with distinct names and
closed clauses, then `Ξannot` is well-typed in System `F_ω^{cop,SCT}` (`BlockTy sig Ξannot`) and is
semantically valid / strongly normalizing in `W` (`SemValid W Ξannot`). -/
theorem theorem_15_proof (ramsey : RamseyPairs) (W sig Ξ Ξannot : List FunDecl)
    (hsigwf : DeclsWf sig)
    (hacc : Algorithm2Accepts sig Ξ Ξannot)
    (hW : ∀ d ∈ sig ++ Ξannot, d ∈ W)
    (hnames : (W.map FunDecl.name).Nodup)
    (hclosed : ∀ d ∈ W, (Tm.lam d.clauses).Closed)
    (hsig : SemValid W sig) :
    BlockTy sig Ξannot ∧ SemValid W Ξannot := by
  have hbt := algorithm2_typing hsigwf hacc
  exact ⟨hbt, theorem_4_proof ramsey W sig Ξannot hW hnames hclosed hbt hsig⟩

end NishtAbel2024V5


