-- Prove2me | Definitions.Def_OAI_NumberTheory_SingleFold_PolynomialCompiler
-- name    : OAI_NumberTheory_SingleFold_PolynomialCompiler
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T16:01:59.603044+00:00
-- url     : https://prove2.me/theorems/67107efa-6abd-4c08-88f1-9dc64ea8bfa3
-- title:
--   Single-fold Diophantine representations and their closure rules
-- statement:
--   Let $\alpha$ be a type of input variables and $R$ a relation on $\mathbb{N}^\alpha$.
--
--   1. **Representation.** A single-fold representation of $R$ consists of a finite set $V$ of witness variables and an integer polynomial $P$ in the variables $\alpha\sqcup V$ such that, for all $x\in\mathbb{N}^\alpha$,
--   $$
--   R(x)\iff\exists\,w\in\mathbb{N}^V\ P(x,w)=0,\qquad P(x,w)=P(x,w')=0\implies w=w' .
--   $$
--      $R$ is **SF** if it has such a representation.
--   2. **Closure rules.** Representations transfer along logically equivalent relations and along reindexing of the inputs. A polynomial equation $p(x)=0$ is represented with no witnesses. Conjunctions use $p^2+q^2$ on disjoint witness sets, finite conjunctions iterate this, and $p\le q$ is $\exists!\,y\ (p+y=q)$; $p<q$ is $p+1\le q$.
--   3. **Existential projection.** If $R(x,y)$ determines $y$ uniquely from $x$, then $\exists y\,R(x,y)$ is represented by treating $y$ as additional witnesses.
--   4. **Disjoint disjunction.** If $R$ and $S$ are never true together, then $R\vee S$ is represented with a selector bit $b$ by the sum of squares of
--   $$
--   b(b-1),\quad bP_R,\quad(1-b)P_S,\quad(1-b)Z_R,\quad bZ_S,
--   $$
--      where $Z_V=\sum_{v\in V}v^2$ forces the unused witnesses to vanish.
--
--   Uniqueness of the witness is what distinguishes these single-fold representations from ordinary Diophantine ones. Every rule above preserves it.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/SingleFold/PolynomialCompiler.lean

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/SingleFold/PolynomialCompiler.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SingleFold mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SingleFold

namespace OAI

namespace SingleFold.Compiler

@[simp] lemma elim_comp_map {α β γ δ ε : Type} (x : γ → ε) (w : δ → ε)
    (f : α → γ) (g : β → δ) :
    Sum.elim x w ∘ Sum.map f g = Sum.elim (x ∘ f) (w ∘ g) := by
  funext i; cases i <;> rfl

@[simp] lemma elim_comp_assoc {α β γ δ : Type} (x : α → δ) (w : β ⊕ γ → δ) :
    Sum.elim x w ∘ (Equiv.sumAssoc α β γ) =
      Sum.elim (Sum.elim x (w ∘ Sum.inl)) (w ∘ Sum.inr) := by
  funext i; rcases i with (i|i)|i <;> rfl

structure Representation {α : Type} (R : (α → ℕ) → Prop) where
  vars : Type
  finite : Finite vars
  poly : Poly (α ⊕ vars)
  sound : ∀ x w, poly (Sum.elim x w) = 0 → R x
  complete : ∀ x, R x → ∃ w, poly (Sum.elim x w) = 0
  unique : ∀ x w w', poly (Sum.elim x w) = 0 → poly (Sum.elim x w') = 0 → w = w'

attribute [instance] Representation.finite

def SF {α : Type} (R : (α → ℕ) → Prop) : Prop := Nonempty (Representation R)

namespace Representation
variable {α β γ : Type} {R S : (α → ℕ) → Prop}

noncomputable def congr (r : Representation R) (h : ∀ x, R x ↔ S x) : Representation S where
  vars := r.vars
  finite := r.finite
  poly := r.poly
  sound x w hw := (h x).mp (r.sound x w hw)
  complete x hx := r.complete x ((h x).mpr hx)
  unique := r.unique

noncomputable def atom (p : Poly α) : Representation (fun x => p x = 0) where
  vars := Empty
  finite := inferInstance
  poly := p.map Sum.inl
  sound _x _w hw := hw
  complete _x hx := ⟨Empty.elim,hx⟩
  unique _x _w _w' _ _ := funext fun i => Empty.elim i

noncomputable def reindex (r : Representation R) (f : α → β) :
    Representation (fun x => R (x ∘ f)) where
  vars := r.vars
  finite := r.finite
  poly := r.poly.map (Sum.map f id)
  sound x w hw := r.sound (x ∘ f) w (by simpa using hw)
  complete x hx := by simpa using r.complete (x ∘ f) hx
  unique x w w' hw hw' := r.unique (x ∘ f) w w' (by simpa using hw) (by simpa using hw')

noncomputable def and (r : Representation R) (s : Representation S) :
    Representation (fun x => R x ∧ S x) := by
  let p : Poly (α ⊕ (r.vars ⊕ s.vars)) := r.poly.map (Sum.map id Sum.inl)
  let q : Poly (α ⊕ (r.vars ⊕ s.vars)) := s.poly.map (Sum.map id Sum.inr)
  have eval (x : α → ℕ) (w : r.vars ⊕ s.vars → ℕ) :
      (p*p+q*q) (Sum.elim x w) = 0 ↔
      r.poly (Sum.elim x (w ∘ Sum.inl)) = 0 ∧
      s.poly (Sum.elim x (w ∘ Sum.inr)) = 0 := by
    simp only [p,q,Poly.add_apply,Poly.mul_apply,Poly.map_apply,elim_comp_map,Function.comp_id]
    constructor
    · intro h
      constructor <;> nlinarith only [sq_nonneg (r.poly (Sum.elim x (w ∘ Sum.inl))),
        sq_nonneg (s.poly (Sum.elim x (w ∘ Sum.inr))),h]
    · rintro ⟨hp,hq⟩
      rw [hp,hq]; ring
  refine ⟨r.vars ⊕ s.vars,inferInstance,p*p+q*q,?_,?_,?_⟩
  · intro x w hw
    obtain ⟨hp,hq⟩ := (eval x w).mp hw
    exact ⟨r.sound _ _ hp,s.sound _ _ hq⟩
  · rintro x ⟨hx,hy⟩
    obtain ⟨w,hw⟩ := r.complete x hx
    obtain ⟨v,hv⟩ := s.complete x hy
    exact ⟨Sum.elim w v,(eval _ _).mpr ⟨hw,hv⟩⟩
  · intro x w w' hw hw'
    obtain ⟨hp,hq⟩ := (eval x w).mp hw
    obtain ⟨hp',hq'⟩ := (eval x w').mp hw'
    have hr := r.unique _ _ _ hp hp'
    have hs := s.unique _ _ _ hq hq'
    funext i
    cases i with
    | inl i => exact congrFun hr i
    | inr i => exact congrFun hs i

noncomputable def ex {R : (α ⊕ β → ℕ) → Prop} [Finite β]
    (r : Representation R)
    (hu : ∀ x y y', R (Sum.elim x y) → R (Sum.elim x y') → y=y') :
    Representation (fun x => ∃ y, R (Sum.elim x y)) := by
  let p := r.poly.map (Equiv.sumAssoc α β r.vars)
  have eval (x : α → ℕ) (w : β ⊕ r.vars → ℕ) :
      p (Sum.elim x w) = r.poly (Sum.elim (Sum.elim x (w ∘ Sum.inl)) (w ∘ Sum.inr)) := by simp [p]
  refine ⟨β ⊕ r.vars,inferInstance,p,?_,?_,?_⟩
  · intro x w hw
    exact ⟨w ∘ Sum.inl,r.sound _ _ ((eval _ _).symm.trans hw)⟩
  · rintro x ⟨y,hy⟩
    obtain ⟨w,hw⟩ := r.complete (Sum.elim x y) hy
    exact ⟨Sum.elim y w,(eval _ _).trans hw⟩
  · intro x w w' hw hw'
    rw [eval] at hw hw'
    have h := hu x (w ∘ Sum.inl) (w' ∘ Sum.inl) (r.sound _ _ hw) (r.sound _ _ hw')
    have hh : w ∘ Sum.inr = w' ∘ Sum.inr := by
      apply r.unique (Sum.elim x (w ∘ Sum.inl))
      · exact hw
      · rw [h]; exact hw'
    funext i
    cases i with
    | inl i => exact congrFun h i
    | inr i => exact congrFun hh i

noncomputable def zeros (β : Type) [Finite β] : Poly β := by
  classical
  let := Fintype.ofFinite β
  exact Poly.sumsq (Finset.univ.toList.map Poly.proj)

lemma zeros_eq {β : Type} [Finite β] (w : β → ℕ) : zeros β w = 0 ↔ w=0 := by
  classical
  let := Fintype.ofFinite β
  rw [zeros,Poly.sumsq_eq_zero,List.forall_map_iff]
  simp only [List.forall_iff_forall_mem,Finset.mem_toList,Finset.mem_univ,
    true_implies,Function.comp_apply,Poly.proj_apply,Int.natCast_eq_zero]
  exact ⟨fun h => funext h,fun h i => congrFun h i⟩

noncomputable def or (r : Representation R) (s : Representation S)
    (hd : ∀ x, ¬(R x ∧ S x)) : Representation (fun x => R x ∨ S x) := by
  let V := Unit ⊕ (r.vars ⊕ s.vars)
  let b : Poly (α ⊕ V) := Poly.proj (Sum.inr (Sum.inl ()))
  let p : Poly (α ⊕ V) := r.poly.map (Sum.map id (Sum.inr ∘ Sum.inl))
  let q : Poly (α ⊕ V) := s.poly.map (Sum.map id (Sum.inr ∘ Sum.inr))
  let z : Poly (α ⊕ V) := (zeros r.vars).map (Sum.inr ∘ Sum.inr ∘ Sum.inl)
  let z' : Poly (α ⊕ V) := (zeros s.vars).map (Sum.inr ∘ Sum.inr ∘ Sum.inr)
  let L := [b*(b-1),b*p,(1-b)*q,(1-b)*z,b*z']
  have eval (x : α → ℕ) (w : V → ℕ) :
      Poly.sumsq L (Sum.elim x w)=0 ↔
      (w (Sum.inl ())=1 ∧ r.poly (Sum.elim x (w ∘ Sum.inr ∘ Sum.inl))=0 ∧
        w ∘ Sum.inr ∘ Sum.inr=0) ∨
      (w (Sum.inl ())=0 ∧ s.poly (Sum.elim x (w ∘ Sum.inr ∘ Sum.inr))=0 ∧
        w ∘ Sum.inr ∘ Sum.inl=0) := by
    rw [Poly.sumsq_eq_zero]
    simp only [L,List.Forall,Poly.mul_apply,Poly.sub_apply,
      Poly.one_apply,p,q,z,z',b,Poly.proj_apply,Poly.map_apply,elim_comp_map,Function.comp_id]
    constructor
    · rintro ⟨h,hp,hq,hz,hz'⟩
      rcases mul_eq_zero.mp h with h|h
      · have hb : w (Sum.inl ())=0 := by exact_mod_cast h
        right
        refine ⟨hb,?_,?_⟩
        · simpa [hb] using hq
        · apply (zeros_eq _).mp
          simpa [hb,Function.comp_def] using hz
      · have hb : w (Sum.inl ())=1 := by exact_mod_cast (sub_eq_zero.mp h)
        left
        refine ⟨hb,?_,?_⟩
        · simpa [hb] using hp
        · apply (zeros_eq _).mp
          simpa [hb,Function.comp_def] using hz'
    · rintro (⟨hb,hp,hz⟩|⟨hb,hq,hz⟩)
      · have hh := (zeros_eq _).mpr hz
        simpa [hb,Function.comp_def] using And.intro hp hh
      · have hh := (zeros_eq _).mpr hz
        simpa [hb,Function.comp_def] using And.intro hq hh
  refine ⟨V,inferInstance,Poly.sumsq L,?_,?_,?_⟩
  · intro x w hw
    rcases (eval _ _).mp hw with ⟨_,hp,_⟩|⟨_,hq,_⟩
    · exact Or.inl (r.sound _ _ hp)
    · exact Or.inr (s.sound _ _ hq)
  · intro x hx
    rcases hx with hx|hx
    · obtain ⟨w,hw⟩ := r.complete x hx
      exact ⟨Sum.elim (fun _ => 1) (Sum.elim w 0),(eval _ _).mpr (Or.inl ⟨rfl,hw,rfl⟩)⟩
    · obtain ⟨w,hw⟩ := s.complete x hx
      exact ⟨Sum.elim (fun _ => 0) (Sum.elim 0 w),(eval _ _).mpr (Or.inr ⟨rfl,hw,rfl⟩)⟩
  · intro x w w' hw hw'
    rcases (eval _ _).mp hw with ⟨hb,hp,hz⟩|⟨hb,hq,hz⟩ <;>
      rcases (eval _ _).mp hw' with ⟨hb',hp',hz'⟩|⟨hb',hq',hz'⟩
    · have hh := r.unique _ _ _ hp hp'
      funext i
      rcases i with ⟨⟩|(i|i)
      · exact hb.trans hb'.symm
      · exact congrFun hh i
      · exact (congrFun hz i).trans (congrFun hz' i).symm
    · exact False.elim (hd x ⟨r.sound _ _ hp,s.sound _ _ hq'⟩)
    · exact False.elim (hd x ⟨r.sound _ _ hp',s.sound _ _ hq⟩)
    · have hh := s.unique _ _ _ hq hq'
      funext i
      rcases i with ⟨⟩|(i|i)
      · exact hb.trans hb'.symm
      · exact (congrFun hz i).trans (congrFun hz' i).symm
      · exact congrFun hh i

noncomputable def allFin : ∀ (n : ℕ) (R : Fin n → (α → ℕ) → Prop),
    (∀ i, Representation (R i)) → Representation (fun x => ∀ i, R i x)
  | 0, R, _ => (atom (Poly.const 0)).congr (by simp)
  | n+1, R, r => ((r 0).and (allFin n (fun i => R i.succ) (fun i => r i.succ))).congr
      (fun x => by rw [Fin.forall_fin_succ])

noncomputable def all [Finite β] (R : β → (α → ℕ) → Prop) (r : ∀ i, Representation (R i)) :
    Representation (fun x => ∀ i, R i x) := by
  let := Fintype.ofFinite β
  let e := Fintype.equivFin β
  exact (allFin _ (fun i => R (e.symm i)) (fun i => r (e.symm i))).congr
    (fun _ => by
      constructor
      · intro h i; simpa using h (e i)
      · intro h i; exact h (e.symm i))

noncomputable def eq (p q : Poly α) : Representation (fun x => p x=q x) :=
  (atom (p-q)).congr (by intro x; simp only [Poly.sub_apply,sub_eq_zero])

noncomputable def le (p q : Poly α) : Representation (fun x => p x≤q x) := by
  let a : Poly (α ⊕ Unit) := (p.map Sum.inl)+Poly.proj (Sum.inr ())
  let b : Poly (α ⊕ Unit) := q.map Sum.inl
  let r := eq a b
  have hu : ∀ (x : α → ℕ) (y y' : Unit → ℕ),
      a (Sum.elim x y) = b (Sum.elim x y) →
      a (Sum.elim x y') = b (Sum.elim x y') → y=y' := by
    intro x y y' h h'
    change p x+(y ():ℤ)=q x at h
    change p x+(y' ():ℤ)=q x at h'
    have hh : y () = y' () := by omega
    funext i
    exact (congrArg y (Subsingleton.elim i ())).trans (hh.trans (congrArg y' (Subsingleton.elim () i)))
  exact (r.ex hu).congr (by
    intro x
    change (∃ y : Unit → ℕ, p x+(y ():ℤ)=q x) ↔ _
    constructor
    · rintro ⟨y,hy⟩; omega
    · intro h
      exact ⟨fun _ => (q x-p x).toNat,by rw [Int.toNat_of_nonneg (by omega)]; omega⟩)

noncomputable def lt (p q : Poly α) : Representation (fun x => p x<q x) :=
  (le (p+1) q).congr (by intro x; simp only [Poly.add_apply,Poly.one_apply]; omega)

end Representation

end SingleFold.Compiler

end OAI


