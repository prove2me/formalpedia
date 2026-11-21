-- Prove2me | Definitions.Def_LeanPool_LeanModelChecking_NNFABW
-- name    : LeanPool_LeanModelChecking_NNFABW
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-20T22:44:29.170504+00:00
-- url     : https://prove2.me/theorems/734b39db-d507-42ae-b114-b1655234ef20
-- title:
--   NNFABW
-- statement:
--   Definitions and structural lemmas for NNFABW, from György Kurucz; maintained by LeanPool contributors's pinned Formalizations of theorems related to model checking development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/NNFABW.lean

module
public import Definitions.Def_LeanPool_LeanModelChecking_LTLNNF
public import Definitions.Def_LeanPool_LeanModelChecking_ABW
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Tactic.Continuity
public import Mathlib.Topology.Instances.Discrete
public import Mathlib.Topology.Order.MonotoneConvergence
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace LeanModelChecking
abbrev Iic {α} [LE α] (v : α) := { x // x ≤ v }
end LeanModelChecking
abbrev Subtype.embedLe {α} [Preorder α] {x y : α} (hle : x ≤ y) : LeanModelChecking.Iic x
    → LeanModelChecking.Iic y := fun v => ⟨v.val, v.prop.trans hle⟩
namespace LeanModelChecking
def NNF.repeatAndNext {AP} (f g : NNF AP) : ℕ → NNF AP
| 0 => g
| n + 1 => f.and (repeatAndNext f g n).next
namespace PositiveBool
def map {Q P} (f : Q → P) : PositiveBool Q → PositiveBool P
| atom q => .atom (f q)
| true => true
| false => false
| and ψ₁ ψ₂ => .and (map f ψ₁) (map f ψ₂)
| or ψ₁ ψ₂ => .or (map f ψ₁) (map f ψ₂)
instance : Functor PositiveBool where
  map := map
def Forall (p : α → Prop) : PositiveBool α → Prop
| atom q => p q
| true | false => True
| and f g | or f g => f.Forall p ∧ g.Forall p
theorem Forall.imp {α} {p q : α → Prop} (h : ∀ x, p x
    → q x) {φ : PositiveBool α} (pf : φ.Forall p) : φ.Forall q := by
  induction φ <;> simp [PositiveBool.Forall] at pf ⊢ <;> grind
def mapSubtype {α} {p : α
    → Prop} (ψ : PositiveBool α) (pf : ψ.Forall p) : PositiveBool (Subtype p) :=
  match ψ, pf with
  | atom q, h => .atom ⟨q, h⟩
  | true, _ => .true
  | false, _ => .false
  | and ψ₁ ψ₂, pf =>
      .and (mapSubtype ψ₁ (by simp [Forall] at pf; exact pf.left))
        ((mapSubtype ψ₂ (by simp [Forall] at pf; exact pf.right)))
  | or ψ₁ ψ₂, pf =>
      .or (mapSubtype ψ₁ (by simp [Forall] at pf; exact pf.left))
        ((mapSubtype ψ₂ (by simp [Forall] at pf; exact pf.right)))
def mapSubtypeImp {α : Type} {p q : α → Prop} (ψ : PositiveBool (Subtype p)) (h : ∀ x,
    p x → q x) : PositiveBool (Subtype q) :=
  (fun x => ⟨x.val, by grind⟩) <$> ψ
@[simp]
lemma mapSubtypeImp_collapse
  {α} {p q : α → Prop} (ψ : PositiveBool α)
  {pf : ψ.Forall p} {h : ∀ x, p x → q x}
    : (ψ.mapSubtype pf).mapSubtypeImp h = ψ.mapSubtype (pf.imp h) := by
  induction ψ <;> simp [mapSubtypeImp, Functor.map,
      map, mapSubtype] at * <;> constructor <;> grind
lemma map_sat_le
  {T} {Q Q' : T} [Preorder T] (hle : Q' ≤ Q) {ψ : PositiveBool (Iic Q')} {Y : Set (Iic Q)}
  (Hsat : (ψ.mapSubtypeImp (fun _ qp => qp.trans hle)).Sat Y)
    : ψ.Sat { q | q.embedLe hle ∈ Y } := by
  induction ψ <;> simp only [mapSubtypeImp, Functor.map, map, Sat, Set.mem_ofPred_eq] at Hsat ⊢
  next a => exact Hsat
  next f g f_ih g_ih => exact ⟨f_ih Hsat.left, g_ih Hsat.right⟩
  next f g f_ih g_ih => exact Hsat.imp f_ih g_ih
lemma mapSubtypeImp_embed
  {T : Type} [PartialOrder T] {x y : T} (hle : x ≤ y)
  (ψ : PositiveBool {q // q ≤ x}) (Y : Set {q // q ≤ x})
    : PositiveBool.Sat (Subtype.embedLe hle ''
        Y) (ψ.mapSubtypeImp (fun _ x => x.trans hle)) ↔ ψ.Sat Y := by
  induction ψ <;> simp [Sat, mapSubtypeImp, Functor.map, map] at * <;> grind
end PositiveBool
namespace DAG
instance : Functor DAG where
  map f G := {
    V := (fun (q, l) => (f q, l)) '' G.V,
    E := (fun ((q, l), q') => ((f q, l), f q')) '' G.E
    edge_closure := by
      rintro ⟨⟨_, _⟩, _⟩
      simp only [Set.mem_image, Prod.mk.injEq, Prod.exists, ↓existsAndEq, and_true,
        exists_eq_right_right, forall_exists_index, and_imp]
      rintro _ _ hE rfl rfl
      have := G.edge_closure _ hE
      grind
  }
end DAG
namespace replaceRoot
variable
  {T : Type} [PartialOrder T] [DecidableEq T]
  {φ₁ φ₂ : T} (hle : φ₁ ≤ φ₂)
section
variable (r₁ : Iic φ₁) (r₂ : Iic φ₂) (G : DAG (Iic φ₁))
def base : DAG.Base {q // q ≤ φ₂} := {
  V := {(r₂, 0)} ∪ (fun (q, l) => (⟨q.val, by grind⟩, l)) '' (G.V \ {(r₁, 0)})
  E := (fun ((q, l), q') =>
    if (q, l) = (r₁, 0) then
      ((r₂, 0), ⟨q'.val, by grind⟩)
    else
      ((⟨q.val, by grind⟩, l), ⟨q'.val, by grind⟩)
    ) '' G.E
}
def dag : DAG {q // q ≤ φ₂} := {
  replaceRoot.base hle r₁ r₂ G with
  edge_closure := by
    simp only [replaceRoot.base]
    have := G.edge_closure
    intros e he
    simp; grind
}
lemma path_after_1_prop (p : ℕ
    → {q // q ≤ φ₂}) (p_path : (dag hle r₁ r₂ G).path p) : ∀ i > 0, (p i).val ≤ φ₁ := by
  simp only [DAG.path, dag, base] at p_path
  grind
end
def runDag
  {S}
  {M : ABW S (Iic φ₁)} {M' : ABW S (Iic φ₂)} {w : ℕ → S}
  (G : RunDAG M w)
  (h_delta_root : ∀ Q, PositiveBool.Sat Q (M.δ M.q₀ (w 0))
      → PositiveBool.Sat ((Subtype.embedLe hle) '' Q) (M'.δ M'.q₀ (w 0)))
  (h_delta_eq : ∀ (q : Iic φ₁) i,
      M'.δ (q.embedLe hle) (w i) = (M.δ q (w i)).mapSubtypeImp (fun _ p => p.trans hle))
    : RunDAG M' w := {
  dag hle M.q₀ M'.q₀ G.toDAG with
  p_root := by simp [dag, base]
  p_sat := by
    have p_sat := G.p_sat
    simp only [Prod.mk.eta, Prod.forall, Subtype.forall] at p_sat
    simp only [dag, base]
    rintro ⟨q, l⟩
    intros hq
    simp only [Set.mem_union] at hq
    rcases hq with hq|hq
    · simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hq; cases hq; subst_vars
      simp only [Prod.mk.eta]
      obtain ⟨Y, p_sat, p_sub⟩ := p_sat M.q₀ _ 0 G.p_root
      exists Subtype.embedLe hle '' Y
      constructor
      · simp_all
      · rw [Set.subset_def]
        simp only [Set.mem_image, Set.mem_prod]
        rintro ⟨⟨q, l⟩, q'⟩ H
        simp only [Set.mem_singleton_iff, Prod.mk.injEq, Subtype.exists] at H
        rcases H with ⟨⟨rfl, rfl⟩, q, qp, qY, rfl⟩
        rw [Set.subset_def] at p_sub
        simp only [Set.mem_prod] at p_sub
        specialize p_sub ((M.q₀, 0), ⟨q, qp⟩)
        grind
    · simp only [Set.mem_image, Set.mem_sdiff, Set.mem_singleton_iff, Prod.mk.injEq, Prod.exists,
      not_and, exists_eq_right_right, Subtype.exists] at hq
      rcases hq with ⟨q, qp, ⟨hV, not_root⟩, rfl⟩
      obtain ⟨Y, p_sat, p_sub⟩ := p_sat q qp l hV
      exists Subtype.embedLe hle '' Y
      constructor
      · specialize h_delta_eq ⟨q, qp⟩ l
        rwa [h_delta_eq, PositiveBool.mapSubtypeImp_embed hle]
      · rw [Set.subset_def]
        simp only [Set.mem_image, Set.mem_prod]
        rintro ⟨⟨q, l⟩, q'⟩ H
        simp only [Set.mem_singleton_iff, Prod.mk.injEq, Subtype.exists] at H
        rcases H with ⟨⟨rfl, rfl⟩, q', q'p, qY, rfl⟩
        rw [Set.subset_def] at p_sub
        simp only [Set.mem_prod] at p_sub
        specialize p_sub ((⟨q, qp⟩, l), ⟨q', q'p⟩)
        grind
}
end replaceRoot
namespace shiftDag
variable
  {T : Type} [PartialOrder T]
  {φ₁ φ₂ : T} (hle : φ₁ ≤ φ₂)
section
variable (r₁ : {q // q ≤ φ₁}) (r₂ : {q // q ≤ φ₂}) (G : DAG (Iic φ₁))
def dag (hrx : (r₁, 0) ∈ G.V) : DAG (Iic φ₂) := {
  V := {(r₂, 0)} ∪ (fun (q, i) => (q.embedLe hle, i + 1)) '' G.V
  E := {((r₂, 0), r₁.embedLe hle)} ∪ (fun ((q, i), q') =>
      ((q.embedLe hle, i + 1), q'.embedLe hle)) '' G.E
  edge_closure := by have := G.edge_closure; grind
}
lemma path_after_1_prop (hrx : (r₁, 0) ∈ G.V) (p : ℕ
    → Iic φ₂) (p_path : (dag hle r₁ r₂ G hrx).path p) : ∀ i > 0, (p i).val ≤ φ₁ := by
  grind [DAG.path, dag]
end
def runDag
  {S}
  {M : ABW S (Iic φ₁)} {M' : ABW S (Iic φ₂)} {w : ℕ → S}
  (G : RunDAG M (fun j => w (j + 1)))
  (h_root : PositiveBool.Sat {⟨M.q₀.val, M.q₀.prop.trans hle⟩} (M'.δ M'.q₀ (w 0)))
  (h_delta_eq : ∀ (q : Iic φ₁) i,
      M'.δ (q.embedLe hle) (w i) = (M.δ q (w i)).mapSubtypeImp (fun _ q => q.trans hle))
    : RunDAG M' w := {
  dag hle M.q₀ M'.q₀ G.toDAG G.p_root with
  p_root := by simp [dag]
  p_sat := by
    have p_sat := G.p_sat
    rintro ⟨q, l⟩
    intros hV
    simp only
    simp only [dag, Set.singleton_union, Set.mem_insert_iff, Prod.mk.injEq, Set.mem_image,
      Prod.exists, Subtype.exists] at hV ⊢
    rcases hV with ⟨rfl, rfl⟩|⟨z, hz, l, hV, rfl, rfl⟩
    · exists {⟨M.q₀.val, M.q₀.prop.trans hle⟩}
      simp_all
    · specialize p_sat _ hV
      simp only at p_sat
      obtain ⟨Y, p_sat, p_sub⟩ := p_sat
      exists Subtype.embedLe hle '' Y
      constructor
      · specialize h_delta_eq ⟨z, hz⟩ (l + 1)
        rwa [h_delta_eq, PositiveBool.mapSubtypeImp_embed hle]
      · rw [Set.subset_def]
        simp only [Set.mem_image, Set.mem_prod]
        rintro ⟨⟨q, l⟩, q'⟩ H
        simp only [Set.mem_singleton_iff, Prod.mk.injEq, Subtype.exists] at H
        rcases H with ⟨⟨rfl, rfl⟩, q', q'p, qY, rfl⟩
        rw [Set.subset_def] at p_sub
        simp only [Set.mem_prod] at p_sub
        specialize p_sub ((⟨z, hz⟩, l), ⟨q', q'p⟩)
        grind
}
end shiftDag
namespace conjoinDag
variable
  {T : Type} [PartialOrder T] [DecidableEq T]
  {φ₁ φ₂ Φ : T}
  (leφ₁ : φ₁ ≤ Φ) (leφ₂ : φ₂ ≤ Φ)
section
variable
  (r₁ : Iic φ₁) (r₂ : Iic φ₂) (R : Iic Φ)
  (G₁ : DAG (Iic φ₁)) (G₂ : DAG (Iic φ₂))
def base : DAG.Base (Iic Φ) := {
  V :=
    {(R, 0)} ∪
    ((fun (q, l) => (q.embedLe leφ₁, l)) '' (G₁.V \ {(r₁, 0)})) ∪
    (fun (q, l) => (q.embedLe leφ₂, l)) '' (G₂.V \ { (q, l) | l = 0 ∧ (q.val = r₁ ∨ q.val = r₂)})
  E :=
    ((fun ((q, l), q') => (((if (q, l) = (r₁,
        0) then R else q.embedLe leφ₁), l), q'.embedLe leφ₁) ) '' G₁.E) ∪
    {
      ((q.embedLe leφ₂, l), q'.embedLe leφ₂) | (q) (l) (q') (_ :
        (q, l) ∈ G₂.V ∧
        (q.val, l) ∉ (Subtype.val <$> G₁).V ∧
        (q.val, l) ≠ (r₁.val, 0) ∧
        (q.val, l) ≠ (r₂.val, 0) ∧
        ((q, l), q') ∈ G₂.E)
    } ∪
    { ((R, 0), q'.embedLe leφ₂) | (q') (_ : ((r₂, 0), q') ∈ G₂.E) }
}
def dag : DAG (Iic Φ) := {
  base leφ₁ leφ₂ r₁ r₂ R G₁ G₂ with
  edge_closure := by
    have G₁_closure := G₁.edge_closure
    have G₂_closure := G₂.edge_closure
    simp only [base]
    intros e he
    simp only [Set.mem_union] at he
    rcases he with (he|he)|he
    · simp only [Set.mem_image, Prod.exists] at he
      obtain ⟨q, qp, l, q', q'p, hqe, rfl⟩ := he
      constructor
      · split
        next q_root =>
          simp_all
        · left; right
          simp only [Set.mem_image, Set.mem_sdiff]
          grind
      · simp only [Set.singleton_union, Set.mem_union, Set.mem_insert_iff,
          Set.mem_image, Set.mem_sdiff, Set.mem_singleton_iff]
        grind
    · simp only [exists_prop, Subtype.exists] at he
      obtain ⟨q, qp, l, q', q'p, ⟨hV₂, hnV₁, hE₂⟩, rfl⟩ := he
      constructor
      · right
        simp only [Set.mem_image, Set.mem_sdiff]
        exists (⟨q, qp⟩, l)
        simp only [hV₂, Set.mem_ofPred_eq, not_and, not_or, true_and, and_true]
        rintro rfl
        grind
      · simp only [Set.singleton_union, Set.mem_union, Set.mem_insert_iff,
          Set.mem_image, Set.mem_sdiff, Set.mem_singleton_iff]
        grind
    · simp only [exists_prop, Subtype.exists, Set.mem_ofPred_eq] at he
      rcases he with ⟨q, pq, he, rfl⟩
      simp only [Set.mem_union, Set.mem_image, Set.mem_sdiff]
      grind
}
end
lemma runDag_p_sat
  {S}
  {M₁ : ABW S (Iic φ₁)} {M₂ : ABW S (Iic φ₂)} {M : ABW S (Iic Φ)}
  {w : ℕ → S}
  (G₁ : RunDAG M₁ w) (G₂ : RunDAG M₂ w)
  (delta_eq_1 : ∀ (q : Iic φ₁) i,
      M.δ (q.embedLe leφ₁) (w i) = (M₁.δ q (w i)).mapSubtypeImp (fun _ q => q.trans leφ₁))
  (delta_eq_2 : ∀ (q : Iic φ₂) i,
      M.δ (q.embedLe leφ₂) (w i) = (M₂.δ q (w i)).mapSubtypeImp (fun _ q => q.trans leφ₂))
  (delta_root : ∀ Y₁ Y₂, (M₁.δ M₁.q₀ (w 0)).Sat Y₁ → (M₂.δ M₂.q₀ (w 0)).Sat Y₂
      → (M.δ M.q₀ (w 0)).Sat (((Subtype.embedLe leφ₁) '' Y₁) ∪ ((Subtype.embedLe leφ₂) '' Y₂))) :
    ∀ v ∈ (dag leφ₁ leφ₂ M₁.q₀ M₂.q₀ M.q₀ G₁.toDAG G₂.toDAG).V,
      let (q, i) := v
      ∃ Y, PositiveBool.Sat Y (M.δ q (w i)) ∧
        {(q, i)} ×ˢ Y ⊆ (dag leφ₁ leφ₂ M₁.q₀ M₂.q₀ M.q₀ G₁.toDAG G₂.toDAG).E := by
  have first (q : Iic φ₁) (l : ℕ) (hq : (q, l) ∈ G₁.V)
      (hne : (q, l) ≠ (M₁.q₀, 0)) :
      ∃ Y, PositiveBool.Sat Y (M.δ (q.embedLe leφ₁) (w l)) ∧
        {(q.embedLe leφ₁, l)} ×ˢ Y ⊆
          (dag leφ₁ leφ₂ M₁.q₀ M₂.q₀ M.q₀ G₁.toDAG G₂.toDAG).E := by
    obtain ⟨Y, hY, hE⟩ := G₁.p_sat _ hq
    refine ⟨Subtype.embedLe leφ₁ '' Y, ?_, ?_⟩
    · rwa [delta_eq_1, PositiveBool.mapSubtypeImp_embed leφ₁]
    · rintro ⟨v, q'⟩ ⟨rfl, y, hy, rfl⟩
      exact Or.inl (Or.inl ⟨((q, l), y), hE ⟨rfl, hy⟩, by simp [hne]⟩)
  intro v hv
  rcases hv with (hv | hv) | hv
  · rcases hv with rfl
    obtain ⟨Y₁, hY₁, hE₁⟩ := G₁.p_sat _ G₁.p_root
    obtain ⟨Y₂, hY₂, hE₂⟩ := G₂.p_sat _ G₂.p_root
    refine ⟨Subtype.embedLe leφ₁ '' Y₁ ∪ Subtype.embedLe leφ₂ '' Y₂,
      delta_root _ _ hY₁ hY₂, ?_⟩
    rintro ⟨v, q'⟩ ⟨rfl, hq'⟩
    rcases hq' with ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩
    · exact Or.inl (Or.inl ⟨((M₁.q₀, 0), y), hE₁ ⟨rfl, hy⟩, by simp⟩)
    · exact Or.inr ⟨y, hE₂ ⟨rfl, hy⟩, rfl⟩
  · rcases hv with ⟨⟨q, l⟩, ⟨hq, hne⟩, rfl⟩
    exact first q l hq hne
  · rcases hv with ⟨⟨q, l⟩, ⟨hq, hne⟩, rfl⟩
    by_cases hshared : (q.val, l) ∈ (Subtype.val <$> G₁.toDAG).V
    · simp only [Functor.map, Set.mem_image, Prod.mk.injEq, Prod.exists,
        exists_eq_right_right, Subtype.exists, exists_and_right, exists_eq_right] at hshared
      obtain ⟨hq₁, hV₁⟩ := hshared
      apply first ⟨q.val, hq₁⟩ l hV₁
      intro h
      exact hne ⟨(Prod.mk.inj h).2, Or.inl (congrArg Subtype.val (Prod.mk.inj h).1)⟩
    · obtain ⟨Y, hY, hE⟩ := G₂.p_sat _ hq
      refine ⟨Subtype.embedLe leφ₂ '' Y, ?_, ?_⟩
      · rwa [delta_eq_2, PositiveBool.mapSubtypeImp_embed leφ₂]
      · rintro ⟨v, q'⟩ ⟨rfl, y, hy, rfl⟩
        refine Or.inl (Or.inr ⟨q, l, y, ⟨hq, hshared, ?_, ?_, hE ⟨rfl, hy⟩⟩, rfl⟩)
        · intro h
          exact hne ⟨(Prod.mk.inj h).2, Or.inl (Prod.mk.inj h).1⟩
        · intro h
          exact hne ⟨(Prod.mk.inj h).2, Or.inr (Prod.mk.inj h).1⟩
def runDag
  {S}
  {M₁ : ABW S (Iic φ₁)} {M₂ : ABW S (Iic φ₂)} {M : ABW S (Iic Φ)}
  {w : ℕ → S}
  (G₁ : RunDAG M₁ w) (G₂ : RunDAG M₂ w)
  (delta_eq_1 : ∀ (q : Iic φ₁) i,
      M.δ (q.embedLe leφ₁) (w i) = (M₁.δ q (w i)).mapSubtypeImp (fun _ q => q.trans leφ₁))
  (delta_eq_2 : ∀ (q : Iic φ₂) i,
      M.δ (q.embedLe leφ₂) (w i) = (M₂.δ q (w i)).mapSubtypeImp (fun _ q => q.trans leφ₂))
  (delta_root : ∀ Y₁ Y₂, (M₁.δ M₁.q₀ (w 0)).Sat Y₁ → (M₂.δ M₂.q₀ (w 0)).Sat Y₂
      → (M.δ M.q₀ (w 0)).Sat (((Subtype.embedLe leφ₁) '' Y₁) ∪ ((Subtype.embedLe leφ₂) '' Y₂)))
    : RunDAG M w := {
  dag leφ₁ leφ₂ M₁.q₀ M₂.q₀ M.q₀ G₁.toDAG G₂.toDAG with
  p_root := by simp only [dag, base, Set.singleton_union,
      Set.mem_union, Set.mem_insert_iff, true_or]
  p_sat := runDag_p_sat leφ₁ leφ₂ G₁ G₂ delta_eq_1 delta_eq_2 delta_root
}
end conjoinDag
def shiftConjoinDag.runDag
  {S T} [PartialOrder T] [DecidableEq T]
  {φ₁ φ₂ : T}
  (leφ₁ : φ₁ ≤ φ₂)
  {M₁ : ABW S (Iic φ₁)} {M₂ : ABW S (Iic φ₂)}
  {w : ℕ → S}
  (G₁ : RunDAG M₁ w) (G₂ : RunDAG M₂ (fun j => w (j + 1)))
  (delta_eq_1 : ∀ (q : Iic φ₁) i,
      M₂.δ (q.embedLe leφ₁) (w i) = (M₁.δ q (w i)).mapSubtypeImp (fun _ q => q.trans leφ₁))
  (delta_root : ∀ Y₁, (M₁.δ M₁.q₀ (w 0)).Sat Y₁
      → (M₂.δ M₂.q₀ (w 0)).Sat (((Subtype.embedLe leφ₁) '' Y₁) ∪ {M₂.q₀}))
    : RunDAG M₂ w := {
  conjoinDag.dag leφ₁ (le_refl φ₂) M₁.q₀ M₂.q₀ M₂.q₀ G₁.toDAG
    (shiftDag.dag (le_refl φ₂) M₂.q₀ M₂.q₀ G₂.toDAG G₂.p_root) with
  p_root := by simp [conjoinDag.dag, conjoinDag.base]
  p_sat := by
    intros v hv
    simp only [conjoinDag.dag, conjoinDag.base, shiftDag.dag, Set.mem_union, Set.mem_image] at hv
    rcases hv with (hv|hv)|hv
    · simp only [Set.mem_singleton_iff] at hv; subst hv
      simp only
      obtain ⟨Y₁, p_sat₁, p_sub₁⟩ := G₁.p_sat _ G₁.p_root
      exists ((Subtype.embedLe leφ₁) '' Y₁) ∪ {M₂.q₀}
      constructor
      · exact delta_root _ p_sat₁
      · rw [Set.subset_def]
        simp only [
          conjoinDag.dag, conjoinDag.base, shiftDag.dag,
          Set.mem_image, Subtype.exists, Set.singleton_union,
          Prod.exists, exists_prop, Set.mem_union, Set.mem_ofPred_eq
        ]
        grind
    · simp only [Set.mem_sdiff, Set.mem_singleton_iff, Prod.exists, Prod.mk.injEq, not_and,
      Subtype.exists] at hv
      rcases hv with ⟨q, qp, l, ⟨hV₁, not_root⟩, rfl⟩
      simp only
      obtain ⟨Y₁, p_sat₁, p_sub₁⟩ := G₁.p_sat _ hV₁
      exists Subtype.embedLe leφ₁ '' Y₁
      constructor
      · rw [delta_eq_1, PositiveBool.mapSubtypeImp_embed leφ₁]
        exact p_sat₁
      · rw [Set.subset_def]
        simp only [
          conjoinDag.dag, conjoinDag.base,
          Set.mem_image, Subtype.exists,
          Prod.mk.injEq, Prod.exists, Set.mem_union, Prod.forall, Set.mem_prod
        ]
        grind
    · simp only [Subtype.coe_eta, Set.singleton_union, Set.mem_ofPred_eq, or_true, and_self,
      Set.insert_sdiff_of_mem, Set.mem_sdiff, Set.mem_image, Prod.exists, Subtype.exists, not_and,
      not_or, Prod.mk.eta, exists_eq_right] at hv
      rcases hv with ⟨⟨q, pq, l, hV₂, rfl⟩, not_root⟩
      simp at not_root
      by_cases H₁ : (q, l + 1) ∈ (Subtype.val <$> G₁.toDAG).V
      · simp only [Functor.map, Set.mem_image, Prod.mk.injEq, Prod.exists, exists_eq_right_right,
        Subtype.exists, exists_and_right, exists_eq_right] at H₁
        rcases H₁ with ⟨hq1, hV₁⟩
        obtain ⟨Y₁, p_sat₁, p_sub₁⟩ := G₁.p_sat _ hV₁
        exists Subtype.embedLe leφ₁ '' Y₁
        constructor
        · rw [delta_eq_1 ⟨q, hq1⟩, PositiveBool.mapSubtypeImp_embed leφ₁]
          exact p_sat₁
        · rw [Set.subset_def]
          simp only [conjoinDag.dag, conjoinDag.base, shiftDag.dag]
          intros e he
          simp only [Set.mem_union, Set.mem_image]
          left; left
          simp only [Set.mem_prod, Set.mem_singleton_iff, Set.mem_image, Subtype.exists] at he
          rcases he with ⟨e1_eq, q', pq', q'_in_Y₁, e2_eq⟩
          exists ((⟨q, hq1⟩, l + 1), ⟨q', pq'⟩)
          simp
          grind
      · obtain ⟨Y₂, p_sat₂, p_sub₂⟩ := G₂.p_sat _ hV₂
        simp only
        exists Y₂
        constructor
        · exact p_sat₂
        · rw [Set.subset_def]
          intros e he
          simp only [conjoinDag.dag, conjoinDag.base]
          simp only [Set.mem_union]
          left; right
          simp only [shiftDag.dag]
          simp only [Subtype.coe_eta, Set.singleton_union, Set.mem_insert_iff, Prod.mk.injEq,
            Set.mem_image, Prod.exists, Subtype.exists, Functor.map, exists_eq_right_right,
            exists_and_right, exists_eq_right, not_exists, ne_eq, not_and, exists_prop,
            Subtype.mk.injEq, Set.mem_ofPred_eq]
          simp at he
          exists q, pq, l + 1, e.2.val, e.2.prop
          simp [Functor.map] at H₁
          grind
  }
namespace filterDag
variable
  {T : Type} [PartialOrder T]
  {φ Φ : T}
  (leφ : φ ≤ Φ)
section
variable (G : DAG (Iic Φ)) (rΦ : Iic Φ) (rφ : Iic φ) (shift : ℕ)
def dag : DAG (Iic φ) := {
  V := { (q, l) | (q.embedLe leφ, shift + l) ∈ G.V } ∪ {(rφ, 0)}
  E := { ((q, l), q') : _ | ((q.embedLe leφ, shift + l), q'.embedLe leφ) ∈
      G.E ∨ (l = 0 ∧ q = rφ ∧ ((rΦ, shift), q'.embedLe leφ) ∈ G.E) }
  edge_closure := by cases G; simp; grind
}
end
def runDag
  {S} {M : ABW S (Iic Φ)} {M' : ABW S (Iic φ)} {w : ℕ → S} (G : RunDAG M w)
  (rΦ : Iic Φ)
  (shift : ℕ)
  (h_root : ∃ Y, (M'.δ M'.q₀ (w shift)).Sat Y ∧ Y ⊆ { q | ((rΦ, shift), q.embedLe leφ) ∈ G.E })
  (h_delta_eq : ∀ (q : Iic φ) i,
      M.δ (q.embedLe leφ) (w i) = (M'.δ q (w i)).mapSubtypeImp (fun _ q => q.trans leφ))
    : RunDAG M' (fun j => w (j + shift)) := {
  dag leφ G.toDAG rΦ M'.q₀ shift with
  p_root := by simp [dag]
  p_sat := by
    intros v hv
    simp only [dag, Set.union_singleton, Set.mem_insert_iff, Set.mem_ofPred_eq] at hv
    rcases hv with rfl|hv
    · grind [dag]
    · obtain ⟨Y, p_sat, p_sub⟩ := G.p_sat _ hv
      exists { q | q.embedLe leφ ∈ Y }
      constructor
      · rw [h_delta_eq] at p_sat
        rw [show v.2 + shift = shift + v.2 by omega]
        exact PositiveBool.map_sat_le leφ p_sat
      · grind [dag]
}
end filterDag
namespace alwaysDag
variable
  {T : Type} [PartialOrder T]
  {φ Φ : T}
  (ltφ : φ < Φ)
section
variable (G : ℕ → DAG (Iic φ))
def Vb := ⋃ k, { (q, i + k) | (q) (i) (_ : (q, i) ∈ (G k).V) }
def V : Set (Iic Φ × ℕ) := { (q, _) | q = ⟨Φ, le_refl _⟩ }
    ∪ (fun (q, l) => ⟨q.embedLe ltφ.le, l⟩) '' Vb G
noncomputable def mini (v : Iic φ × ℕ) : ℕ := sInf { i | i ≤ v.2 ∧ (v.1, v.2 - i) ∈ (G i).V }
lemma mini_le q l (H : (q, l) ∈ Vb G) : mini G (q, l) ≤ l := by
  simp only [mini]
  simp only [Vb, exists_prop, Subtype.exists, Set.mem_iUnion, Set.mem_ofPred_eq, Prod.mk.injEq] at H
  rcases H with ⟨i, q, pq, l, hV, rfl, rfl⟩
  apply (show ∀ x y z, x ≤ z → x ≤ y + z by omega)
  apply csInf_le ⟨0, by intro i _; exact Nat.zero_le i⟩
  simp_all
lemma mini_in q l (H : (q, l) ∈ Vb G) : let i' := mini G (q, l); (q, l - i') ∈ (G i').V := by
  have hne : Set.Nonempty { i | i ≤ l ∧ (q, l - i) ∈ (G i).V } := by
    simp only [Vb, exists_prop, Subtype.exists, Set.mem_iUnion, Set.mem_ofPred_eq, Prod.mk.injEq
      ] at H
    rcases H with ⟨i, q, pq, l, hV, rfl, rfl⟩
    simp [Set.Nonempty]
    grind
  exact (csInf_mem hne).2
def E : Set ((Iic Φ × ℕ) × Iic Φ) := { ((q, l), q') : _ |
  q = ⟨Φ, le_refl _⟩ ∧ (q' = ⟨Φ, le_refl _⟩ ∨ ∃ (hq' : q' ≤ φ),
      ((⟨φ, le_refl _⟩, 0), ⟨q'.val, hq'⟩) ∈ (G l).E)
} ∪ { ((q, l), q') : _ |
  q ≠ ⟨Φ, le_refl _⟩ ∧ ∃ (hq : q ≤ φ) (hq' : q' ≤ φ) (_ : (⟨q.val, hq⟩, l) ∈ Vb G),
      let i' := mini G (⟨q.val, hq⟩, l); ((⟨q.val, hq⟩, l - i'), ⟨q'.val, hq'⟩) ∈ (G i').E
}
def base : DAG.Base (Iic Φ) := { V := V ltφ G, E := E G }
def dag : DAG (Iic Φ) := {
  base ltφ G with
  edge_closure := by
    rintro ⟨⟨q, l⟩, q'⟩ he
    simp only [base, V, E, Set.mem_ofPred, Set.mem_union] at he
    rcases he with ⟨rfl, he⟩|⟨h_not_root, qp, q'p, qvb, he⟩
    · rcases he with rfl|⟨q'p, he⟩
      · simp [base, V]
      · constructor
        · simp [base, V]
        · simp only [base, V, Set.mem_union]
          right
          simp only [Set.mem_image, Vb]
          exists (⟨q', q'p⟩, l + 1)
          simp only [exists_prop, Subtype.exists, Set.mem_iUnion, Set.mem_ofPred_eq, Prod.mk.injEq,
            Subtype.mk.injEq, Subtype.coe_eta, and_true]
          exists l, q'.val, q'p, 1
          have := (G l).edge_closure _ he
          grind
    · constructor
      · simp only [base, V, Set.mem_union, Set.mem_ofPred_eq, h_not_root, Set.mem_image,
        Prod.mk.injEq, Prod.exists, exists_eq_right_right, Subtype.exists, false_or]
        exists q, qp
      · simp only [base, V, Set.mem_union, Set.mem_ofPred_eq, Set.mem_image, Prod.mk.injEq,
        Prod.exists, exists_eq_right_right, Subtype.exists]; right
        exists q', q'p
        simp only [Subtype.coe_eta, and_true]
        obtain ⟨-, ec⟩ := DAG.edge_closure _ _ he
        simp only at ec
        simp only [Vb, exists_prop, Subtype.exists, Set.mem_iUnion, Set.mem_ofPred_eq,
          Prod.mk.injEq, Subtype.mk.injEq]
        exists mini _ _, _, q'p, _, ec
        have := mini_le G ⟨q, qp⟩ l
        grind
}
end
def runDag
  {S} {M : ABW S (Iic Φ)} {M' : ABW S (Iic φ)} {w : ℕ
      → S} (G : ∀ (i : ℕ), RunDAG M' (fun j => w (j + i)))
  (h_M_root : M.q₀ = ⟨Φ, le_refl _⟩) (h_M'_root : M'.q₀ = ⟨φ, le_refl _⟩)
  (h_delta_root : ∀ Y l, (M'.δ M'.q₀ (w l)).Sat Y → (M.δ ⟨Φ,
      le_refl _⟩ (w l)).Sat (Subtype.embedLe ltφ.le '' Y ∪ {M.q₀}))
  (h_delta_eq : ∀ (q : Iic φ) i,
      M.δ (q.embedLe ltφ.le) (w i) = (M'.δ q (w i)).mapSubtypeImp (fun _ q => q.trans ltφ.le))
    : RunDAG M w := {
  dag ltφ (fun i => (G i).toDAG) with
  p_root := by simp only [dag, base, V, Set.mem_union, Set.mem_ofPred_eq, Set.mem_image,
    Prod.mk.injEq, Prod.exists, exists_eq_right_right, Subtype.exists]; left; exact h_M_root
  p_sat := by
    rintro ⟨q, l⟩ hv
    simp only [dag, base, V, Set.mem_union, Set.mem_ofPred_eq, Set.mem_image, Prod.mk.injEq,
      Prod.exists, exists_eq_right_right, Subtype.exists] at hv
    rcases hv with rfl|⟨q, pq, ⟨hv, rfl⟩⟩
    · obtain ⟨Y, p_sat, p_sub⟩ := (G l).p_sat _ (G l).p_root
      exists ((Subtype.embedLe ltφ.le) '' Y) ∪ {M.q₀}
      constructor
      · simp_all
      · simp only [dag, base, E]
        grind only [
          = Set.subset_def,
          = Set.mem_union,
          = Set.mem_prod,
          = Set.mem_singleton_iff,
          = Set.mem_image,
          usr Set.mem_ofPred_eq
        ]
    · let i' := mini (fun i => (G i).toDAG) (⟨q, pq⟩, l)
      obtain ⟨Y, p_sat, _⟩ := (G i').p_sat (⟨q, pq⟩,
          l - i') (by apply mini_in (G := (fun i => (G i).toDAG)); exact hv)
      exists Subtype.embedLe ltφ.le '' Y
      constructor
      · rw [h_delta_eq, PositiveBool.mapSubtypeImp_embed]
        have eq : l - i' + i' = l := by have := mini_le (fun i => (G i).toDAG); grind
        rwa [eq] at p_sat
      · simp only [dag, base, E]
        grind only [
          = Set.subset_def,
          = Set.mem_union,
          = Set.mem_prod,
          = Set.mem_singleton_iff,
          = Set.mem_image,
          usr Set.mem_ofPred_eq
        ]
}
end alwaysDag
section sub
inductive sub {AP} : NNF AP → NNF AP → Prop where
| refl {φ} : sub φ φ
| and_left {φ f g} : sub φ f → sub φ (.and f g)
| and_right {φ f g} : sub φ g → sub φ (.and f g)
| or_left {φ f g} : sub φ f → sub φ (.or f g)
| or_right {φ f g} : sub φ g → sub φ (.or f g)
| next {φ f} : sub φ f → sub φ (.next f)
| until_left {φ f g} : sub φ f → sub φ (.until f g)
| until_right {φ f g} : sub φ g → sub φ (.until f g)
| release_left {φ f g} : sub φ f → sub φ (.release f g)
| release_right {φ f g} : sub φ g → sub φ (.release f g)
instance {AP} : LE (NNF AP) := ⟨sub⟩
def size {AP} : NNF AP → ℕ
| .atom _ => 1
| .not_atom _ => 1
| .next φ₁ => size φ₁ + 1
| .and φ₁ φ₂ | .or φ₁ φ₂ | .until φ₁ φ₂ | .release φ₁ φ₂ => max (size φ₁) (size φ₂) + 1
lemma size_le_of_sub {AP} {φ ψ : NNF AP} (h : φ ≤ ψ) : size φ ≤ size ψ := by
  induction h
  case refl => rfl
  all_goals (rename_i ih; simp only [size]; omega)
lemma size_lt_of_sub {AP} {φ ψ : NNF AP} (h : φ ≤ ψ) (hne : ψ ≠ φ) : size φ < size ψ := by
  cases h
  case refl => contradiction
  all_goals (rename_i hsub; have := size_le_of_sub hsub; simp only [size]; omega)
theorem sub_antisymm {AP} {φ₁ φ₂ : NNF AP} (h1 : φ₁ ≤ φ₂) (h2 : φ₂ ≤ φ₁) : φ₁ = φ₂ := by
  by_contra hne
  have : size φ₁ < size φ₂ := size_lt_of_sub h1 (Ne.symm hne)
  have : size φ₂ < size φ₁ := size_lt_of_sub h2 hne
  omega
theorem sub_trans {AP} {a b c : NNF AP} (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
  induction h2 generalizing a
  case refl => exact h1
  all_goals rename_i ih; first
    | exact sub.and_left (ih h1) | exact sub.and_right (ih h1)
    | exact sub.or_left (ih h1) | exact sub.or_right (ih h1)
    | exact sub.next (ih h1)
    | exact sub.until_left (ih h1) | exact sub.until_right (ih h1)
    | exact sub.release_left (ih h1) | exact sub.release_right (ih h1)
instance {AP} : PartialOrder (NNF AP) where
  le_refl _ := sub.refl
  le_trans _ _ _ := sub_trans
  le_antisymm _ _ := sub_antisymm
instance {AP} {ψ : NNF AP} : Nonempty { q // q ≤ ψ } := ⟨ψ, sub.refl⟩
def subFinset {AP} [DecidableEq AP] : NNF AP → Finset (NNF AP)
| .atom p        => { .atom p }
| .not_atom p    => { .not_atom p }
| .next f        => insert (.next f) (subFinset f)
| .and f g       => insert (.and f g) (subFinset f ∪ subFinset g)
| .or f g        => insert (.or f g) (subFinset f ∪ subFinset g)
| .until f g     => insert (.until f g) (subFinset f ∪ subFinset g)
| .release f g   => insert (.release f g) (subFinset f ∪ subFinset g)
end sub
def delta {AP} (φ : NNF AP) (σ : Letter AP) [DecidablePred (· ∈ σ)] : PositiveBool (NNF AP) :=
  match φ with
  | .atom p => if p ∈ σ then .true else .false
  | .not_atom p => if p ∈ σ then .false else .true
  | .and φ₁ φ₂ => (delta φ₁ σ).and (delta φ₂ σ)
  | .or φ₁ φ₂ => (delta φ₁ σ).or (delta φ₂ σ)
  | .next φ₁ => .atom φ₁
  | .until φ₁ φ₂ => (delta φ₂ σ).or ((delta φ₁ σ).and (.atom (.until φ₁ φ₂)))
  | .release φ₁ φ₂ => (delta φ₂ σ).and ((delta φ₁ σ).or (.atom (.release φ₁ φ₂)))
theorem delta_forall {AP} {φ : NNF AP} {σ : Letter AP} [DecidablePred (· ∈
    σ)] : (delta φ σ).Forall (· ≤ φ) := by
  induction φ with
  | atom q => by_cases h : q ∈ σ <;> simp [PositiveBool.Forall, delta, h]
  | not_atom q => by_cases h : q ∈ σ <;> simp [PositiveBool.Forall, delta, h]
  | and f g f_ih g_ih => exact ⟨f_ih.imp (fun _ => sub.and_left), g_ih.imp (fun _ => sub.and_right)⟩
  | or f g f_ih g_ih => exact ⟨f_ih.imp (fun _ => sub.or_left), g_ih.imp (fun _ => sub.or_right)⟩
  | next f f_ih => exact sub.next sub.refl
  | «until» f g f_ih g_ih => exact ⟨g_ih.imp (fun _ =>
      sub.until_right), f_ih.imp (fun _ => sub.until_left), sub.refl⟩
  | «release» f g f_ih g_ih => exact ⟨g_ih.imp (fun _ =>
      sub.release_right), f_ih.imp (fun _ => sub.release_left), sub.refl⟩
open Classical in
/-- The alternating Büchi automaton recognising the language of the NNF formula
`ψ`: its states are the subformulas of `ψ`, its initial state is `ψ`, and its
transitions are given by `delta`. -/
noncomputable def NNF.toABW {AP} (ψ : NNF AP) : ABW (Letter AP) { x // x ≤ ψ } := {
  q₀ := ⟨ψ, sub.refl⟩
  δ φ σ :=
      (delta φ σ).mapSubtype (by classical apply PositiveBool.Forall.imp ?_ delta_forall; grind)
  F := { φ |
    match φ.val with
    | .release _ _ => True
    | _ => False
  }
}
namespace or_mpr
variable {S} [DecidableEq S] {φ₁ φ₂ : NNF S} {w : ℕ → Letter S}
end or_mpr
namespace release_mp
variable {S} {φ₁ φ₂ : NNF S} {w : ℕ → Letter S} {G : RunDAG (φ₁.release φ₂).toABW w}
end release_mp
namespace release_mpr
variable {S} [DecidableEq S] {φ₁ φ₂ : NNF S} {w : ℕ → Letter S}
end release_mpr
end LeanModelChecking


