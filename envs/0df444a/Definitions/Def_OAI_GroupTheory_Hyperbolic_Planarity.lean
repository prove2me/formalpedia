-- Prove2me | Definitions.Def_OAI_GroupTheory_Hyperbolic_Planarity
-- name    : OAI_GroupTheory_Hyperbolic_Planarity
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T06:39:42.754719+00:00
-- url     : https://prove2.me/theorems/88eea23e-76a5-4da0-940d-e86343794eb3
-- title:
--   Genus-zero combinatorial maps via the Euler count
-- statement:
--   A purely combinatorial notion of planarity for maps given by permutations of a finite set $A$ of darts.
--
--   1. **Planar maps.** With $\mathrm{cyc}$ the number of cycles (fixed points included) and $\mathrm{comp}(r,f)$ the number of classes of the join of the same-cycle relations of $r$ and $f$, the pair (reverse $r$, face $f$) is a planar map if equality holds in the Euler bound:
--   $$
--   \mathrm{cyc}(r)+\mathrm{cyc}(f)+\mathrm{cyc}(rf)=|A|+2\,\mathrm{comp}(r,f).
--   $$
--   This says that every connected component has genus zero, with no embedding or Jordan curve theorem involved.
--   2. **Re-pairing.** For darts $a,b$, $\mathrm{rePair}(r,a,b)=(r(a)\ b)\,r\,(r(a)\ b)$ conjugates $r$ by a transposition; it pairs $a$ with $b$ and $r(a)$ with $r(b)$, and it stays a fixed-point-free involution when $r$ is one.
--   3. **Restriction.** For a predicate on $A$ invariant under both permutations, cycle and component counts split as sums over the predicate and its complement. Hence planarity passes to the restrictions to any union of components.
--   4. **Transport.** Cycle counts are preserved under bijections intertwining two permutations; the left and right summands of $A\sqcup B$ are identified with $A$ and $B$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/Planarity.lean

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/Planarity.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TorsionFreeHyperbolic mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Incidence
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Presentation
import Definitions.Def_OAI_GroupTheory_Hyperbolic_WordPaths
import Definitions.Def_OAI_GroupTheory_Hyperbolic_PermutationCycles

namespace OAI

namespace Release075.PermCycles
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*} [Fintype A]

/-- Change the pairing on two edges, creating pairs `(a,b)` and `(reverse a,
reverse b)`. Formulated by conjugation, so involutivity and absence of fixed
points are inherited rather than assumed for the result. -/
noncomputable def rePair (reverse : Perm A) (a b : A) : Perm A :=
  Equiv.swap (reverse a) b * reverse * Equiv.swap (reverse a) b

/-- Genus zero for every connected component, expressed without an embedding or
an unproved Jordan-curve theorem. This uses the universal Euler upper bound. -/
def PlanarMap (reverse face : Perm A) : Prop :=
  cycleCount reverse + cycleCount face + cycleCount (reverse*face) =
    Fintype.card A + 2*componentCount reverse face

end Release075.PermCycles

namespace Release075.PermCycles
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*} [Fintype A]

theorem invariant_pred_sameCycle (f : Perm A) (p : A → Prop)
    (hp : ∀ a, p (f a) ↔ p a) {a b : A} (h : f.SameCycle a b) : p a ↔ p b := by
  obtain ⟨n,rfl⟩ := h.exists_nat_pow_eq
  clear h
  induction n with
  | zero => rfl
  | succ n ih => simpa only [pow_succ',Perm.mul_apply,hp] using ih

/-- Decompose the number of classes along a union of equivalence classes. -/
theorem card_quotient_partition (s : Setoid A) (p : A → Prop)
    (hp : ∀ a b, s a b → (p a ↔ p b)) :
    Nat.card (Quotient s) = Nat.card (Quotient (s.comap (Subtype.val : {a // p a} → A))) +
      Nat.card (Quotient (s.comap (Subtype.val : {a // ¬p a} → A))) := by
  let q : Quotient s → Prop := Quotient.lift p (fun a b h => propext (hp a b h))
  let e₁ := Equiv.subtypeQuotientEquivQuotientSubtype p (s₁ := s)
    (s₂ := s.comap Subtype.val) q (fun _ => Iff.rfl) (fun _ _ => Iff.rfl)
  let e₂ := Equiv.subtypeQuotientEquivQuotientSubtype (fun a => ¬p a) (s₁ := s)
    (s₂ := s.comap Subtype.val) (fun a => ¬ q a) (fun _ => Iff.rfl) (fun _ _ => Iff.rfl)
  rw [← Nat.card_congr e₁,← Nat.card_congr e₂,← Nat.card_sum]
  exact (Nat.card_congr (Equiv.sumCompl q)).symm

theorem cycleCount_partition (f : Perm A) (p : A → Prop) (hp : ∀ a, p (f a) ↔ p a) :
    cycleCount f = cycleCount (f.subtypePerm hp) +
      cycleCount (f.subtypePerm (p := fun a => ¬p a) (fun a => not_congr (hp a))) := by
  have h := card_quotient_partition (Perm.SameCycle.setoid f) p
    (fun _ _ h => invariant_pred_sameCycle f p hp h)
  have hs : Perm.SameCycle.setoid (f.subtypePerm hp) =
      (Perm.SameCycle.setoid f).comap Subtype.val := by
    ext; exact Perm.sameCycle_subtypePerm
  have ht : Perm.SameCycle.setoid (f.subtypePerm (p := fun a => ¬p a) (fun a => not_congr (hp a))) =
      (Perm.SameCycle.setoid f).comap Subtype.val := by
    ext; exact Perm.sameCycle_subtypePerm
  simpa only [cycleCount,Cycles,hs,ht] using h

/-- Restriction to an invariant set commutes with connected components. -/
theorem components_subtype (f g : Perm A) (p : A → Prop)
    (hf : ∀ a, p (f a) ↔ p a) (hg : ∀ a, p (g a) ↔ p a) :
    components (f.subtypePerm hf) (g.subtypePerm hg) = (components f g).comap Subtype.val := by
  have hinv : ∀ a b, components f g a b → (p a ↔ p b) := by
    intro a b h
    have hh : components f g ≤ Setoid.ker p := by
      apply sup_le
      · intro a b h; exact propext (invariant_pred_sameCycle f p hf h)
      · intro a b h; exact propext (invariant_pred_sameCycle g p hg h)
    exact propext_iff.mp (hh h)
  apply le_antisymm
  · apply sup_le
    · intro x y h
      exact (show Perm.SameCycle.setoid f ≤ components f g from le_sup_left)
        (Perm.sameCycle_subtypePerm.mp h)
    · intro x y h
      exact (show Perm.SameCycle.setoid g ≤ components f g from le_sup_right)
        (Perm.sameCycle_subtypePerm.mp h)
  · intro x y h
    change components f g x.val y.val at h
    rw [components,Setoid.sup_def] at h
    have hh (a b : A) (h : Relation.EqvGen (⇑(Perm.SameCycle.setoid f) ⊔
        ⇑(Perm.SameCycle.setoid g)) a b) :
        ∀ ha : p a, ∀ hb : p b,
          components (f.subtypePerm hf) (g.subtypePerm hg) ⟨a,ha⟩ ⟨b,hb⟩ := by
      induction h with
      | rel a b h =>
        intro ha hb
        rcases h with h | h
        · exact (show Perm.SameCycle.setoid (f.subtypePerm hf) ≤ _ from le_sup_left)
            (Perm.sameCycle_subtypePerm.mpr h)
        · exact (show Perm.SameCycle.setoid (g.subtypePerm hg) ≤ _ from le_sup_right)
            (Perm.sameCycle_subtypePerm.mpr h)
      | refl a => intros; exact (components (f.subtypePerm hf) (g.subtypePerm hg)).refl _
      | symm a b h ih => intros; exact (components (f.subtypePerm hf) (g.subtypePerm hg)).symm (ih _ _)
      | trans a b c hab hbc ih₁ ih₂ =>
        intro ha hc
        have hab' : components f g a b := by rwa [components,Setoid.sup_def]
        have hb : p b := (hinv a b hab').mp ha
        exact (components (f.subtypePerm hf) (g.subtypePerm hg)).trans (ih₁ ha hb) (ih₂ hb hc)
    exact hh _ _ h x.property y.property

theorem componentCount_partition (f g : Perm A) (p : A → Prop)
    (hf : ∀ a, p (f a) ↔ p a) (hg : ∀ a, p (g a) ↔ p a) :
    componentCount f g = componentCount (f.subtypePerm hf) (g.subtypePerm hg) +
      componentCount (f.subtypePerm (p := fun a => ¬p a) (fun a => not_congr (hf a)))
        (g.subtypePerm (p := fun a => ¬p a) (fun a => not_congr (hg a))) := by
  have hh : components f g ≤ Setoid.ker p := by
    apply sup_le
    · intro a b h; exact propext (invariant_pred_sameCycle f p hf h)
    · intro a b h; exact propext (invariant_pred_sameCycle g p hg h)
  simpa only [componentCount,components_subtype] using
    card_quotient_partition (components f g) p (fun _ _ h => propext_iff.mp (hh h))

/-- Genus-zero is inherited by every union of connected components. -/
theorem PlanarMap.restrict {f g : Perm A} (h : PlanarMap f g) (p : A → Prop)
    (hf : ∀ a, p (f a) ↔ p a) (hg : ∀ a, p (g a) ↔ p a) :
    PlanarMap (f.subtypePerm hf) (g.subtypePerm hg) := by
  have hfg : ∀ a, p ((f*g) a) ↔ p a := fun a => (hf (g a)).trans (hg a)
  have hF := cycleCount_partition f p hf
  have hG := cycleCount_partition g p hg
  have hFG := cycleCount_partition (f*g) p hfg
  rw [← Perm.subtypePerm_mul f g hf hg,
    ← Perm.subtypePerm_mul (p := fun a => ¬p a) f g (fun a => not_congr (hf a))
      (fun a => not_congr (hg a))] at hFG
  have hC := componentCount_partition f g p hf hg
  have hA : Fintype.card A = Fintype.card {a // p a} + Fintype.card {a // ¬p a} := by
    simpa only [Fintype.card_sum] using (Fintype.card_congr (Equiv.sumCompl p)).symm
  have hB := euler_bound (f.subtypePerm (p := fun a => ¬p a) (fun a => not_congr (hf a)))
    (g.subtypePerm (p := fun a => ¬p a) (fun a => not_congr (hg a)))
  have hB' := euler_bound (f.subtypePerm hf) (g.subtypePerm hg)
  unfold PlanarMap at h ⊢
  omega

end Release075.PermCycles

namespace Release075.PermCycles
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A B : Type*} [Fintype A] [Fintype B]

omit [Fintype A] [Fintype B] in
theorem pow_intertwine (f : Perm A) (g : Perm B) (e : A → B)
    (he : ∀ a, e (f a) = g (e a)) (n : ℕ) (a : A) :
    e ((f^n) a) = (g^n) (e a) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ',Perm.mul_apply,he,ih,pow_succ',Perm.mul_apply]

theorem sameCycle_intertwine (f : Perm A) (g : Perm B) (e : A ≃ B)
    (he : ∀ a, e (f a) = g (e a)) (a b : A) : f.SameCycle a b ↔ g.SameCycle (e a) (e b) := by
  constructor
  · intro h
    obtain ⟨n,hn⟩ := h.exists_nat_pow_eq
    exact ⟨(n:ℤ),by rw [zpow_natCast,← pow_intertwine f g e he,hn]⟩
  · intro h
    obtain ⟨n,hn⟩ := h.exists_nat_pow_eq
    refine ⟨(n:ℤ),e.injective ?_⟩
    rwa [zpow_natCast,pow_intertwine f g e he]

theorem cycleCount_intertwine (f : Perm A) (g : Perm B) (e : A ≃ B)
    (he : ∀ a, e (f a) = g (e a)) : cycleCount f = cycleCount g :=
  Nat.card_congr (Quotient.congr e (sameCycle_intertwine f g e he))

def leftPred : A ⊕ B → Prop := Sum.elim (fun _ => True) (fun _ => False)

def leftEquiv : {z : A ⊕ B // leftPred z} ≃ A where
  toFun z := match z with
    | ⟨.inl a,_⟩ => a
    | ⟨.inr _,h⟩ => False.elim h
  invFun a := ⟨.inl a,True.intro⟩
  left_inv z := by rcases z with ⟨a|b,h⟩; rfl; exact h.elim
  right_inv _ := rfl

def rightEquiv : {z : A ⊕ B // ¬leftPred z} ≃ B where
  toFun z := match z with
    | ⟨.inl _,h⟩ => False.elim (h True.intro)
    | ⟨.inr b,_⟩ => b
  invFun b := ⟨.inr b,not_false⟩
  left_inv z := by rcases z with ⟨a|b,h⟩; exact (h True.intro).elim; rfl
  right_inv _ := rfl

omit [Fintype A] [Fintype B] in
theorem leftPred_sumCongr (f : Perm A) (g : Perm B) (z : A ⊕ B) :
    leftPred ((f.sumCongr g) z) ↔ leftPred z := by cases z <;> rfl

end Release075.PermCycles

end OAI


