-- Prove2me | Definitions.Def_OAI_ModelTheory_Categoricity_Collapse
-- name    : OAI_ModelTheory_Categoricity_Collapse
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T02:29:05.641985+00:00
-- url     : https://prove2.me/theorems/354a2c51-8afb-4879-9ef4-46ff892cb239
-- title:
--   Tagged Mostowski collapse, an $\omega_2$-sequence of functions $\omega_1 \to \omega_1$, countable separating closures and tagged direct limits
-- statement:
--   This file collects four general set-theoretic tools. Throughout, sets are well-founded (ZF) sets, $\operatorname{rank}(z)$ is the von Neumann rank of a set $z$, $V_\delta = \{ z : \operatorname{rank}(z) < \delta \}$ for an ordinal $\delta$, and $\omega_1$, $\omega_2$ are the first and second uncountable initial ordinals (the countable ordinals, and the ordinals of cardinality at most $\aleph_1$).
--
--   1. **Collapse of a well-founded relation.** Let $R$ be a well-founded relation on a set $Q$, and read $R(y,x)$ as "$y$ lies below $x$". The collapse $\pi_R$ is defined by well-founded recursion,
--   $$
--   \pi_R(x) = \{\, \pi_R(y) : R(y,x) \,\},
--   $$
--   so $z \in \pi_R(x)$ exactly when $z = \pi_R(y)$ for some $y$ with $R(y,x)$. The file shows: (a) if $R$ is extensional, i.e. two elements with the same $R$-predecessors are equal, then $\pi_R$ is injective; (b) if $\rho$ assigns ordinals to the elements of $Q$ and strictly decreases along $R$, i.e. $R(y,x)$ implies $\rho(y) < \rho(x)$, then $\operatorname{rank} \pi_R(x) \le \rho(x)$ for every $x$; (c) if $R$ is extensional, $\rho$ strictly decreases along $R$ and $\rho(x) < \delta$ for every $x$, then $\pi_R$ is an injection $Q \hookrightarrow V_\delta$; (d) every relation that admits such a strictly decreasing ordinal tag is well-founded.
--
--   2. **An $\omega_2$-sequence of functions $\omega_1 \to \omega_1$.** For every ordinal $\alpha < \omega_2$ fix an injection $\iota_\alpha : \{ \gamma : \gamma < \alpha \} \hookrightarrow \omega_1$ (one exists because $|\alpha| \le \aleph_1$). For $\beta < \omega_1$ let $P(\alpha, \beta) = \{ \gamma < \alpha : \iota_\alpha(\gamma) < \beta \}$; this set is countable, as is every initial segment $\{ x : x < \beta \}$ of $\omega_1$. The functions $f_\alpha : \omega_1 \to \omega_1$ are defined by recursion on $\alpha < \omega_2$:
--   $$
--   f_\alpha(\beta) = \sup_{\gamma \in P(\alpha, \beta)} \bigl( f_\gamma(\beta) + 1 \bigr) \qquad (\beta < \omega_1),
--   $$
--   where the supremum of the empty family is $0$; the value is again a countable ordinal, being a countable supremum of countable ordinals. In particular $f_\gamma(\beta) < f_\alpha(\beta)$ whenever $\gamma < \alpha$ and $\beta > \iota_\alpha(\gamma)$.
--
--   3. **Countable separating closures.** Let $R$ be a binary relation on a set $A$ that separates points: for $a \neq b$ there is $w \in A$ such that $R(w,a)$ and $R(w,b)$ do not have the same truth value. Fix such a witness $w(a,b)$ for each pair $a \neq b$, and put $w(a,a) = a$. For $S \subseteq A$ the stages are $S_0 = S$ and $S_{n+1} = S_n \cup \{ w(a,b) : a, b \in S_n \}$, and the closure is $\operatorname{cl}(S) = \bigcup_{n \in \mathbb{N}} S_n$; it contains $S$, and it is countable when $S$ is. For a nonempty finite seed $X \subseteq A$, the entries of $X$ form the countable nonempty set $\operatorname{cl}(X)$, and the enumeration $e_X : \mathbb{N} \to \operatorname{cl}(X)$ sends $0$ to a chosen element of $X$ and $n + 1$ to $s_X(n)$, where $s_X : \mathbb{N} \to \operatorname{cl}(X)$ is a chosen surjection. Finally, on a transitive set $D$ the membership relation separates points, with witnesses in $D$.
--
--   4. **Tagged direct limits.** Let $(F_i, f_{ij})$ be a directed system of sets over a directed preorder $\mathcal{I}$, with injective transition maps $f_{ij} : F_i \hookrightarrow F_j$ for $i \le j$ satisfying $f_{ii} = \mathrm{id}$ and $f_{jk} \circ f_{ij} = f_{ik}$. Suppose each $F_i$ carries a relation $R_i$ and an ordinal tag $\rho_i$ preserved by the transitions: $R_i(x,y) \Leftrightarrow R_j(f_{ij}(x), f_{ij}(y))$ and $\rho_i(x) = \rho_j(f_{ij}(x))$. They induce a relation $R_\infty$ and a tag $\rho_\infty$ on the direct limit $F_\infty = \varinjlim F_i$, determined by
--   $$
--   R_\infty([x]_i, [y]_i) \Leftrightarrow R_i(x, y), \qquad \rho_\infty([x]_i) = \rho_i(x),
--   $$
--   where $[x]_i$ is the class of $x \in F_i$. If every $R_i$ is extensional, so is $R_\infty$; if every $\rho_i$ strictly decreases along $R_i$, then $\rho_\infty$ strictly decreases along $R_\infty$; and if both hold and all tags are smaller than an ordinal $\delta$, the collapse of item 1 gives an injection $F_\infty \hookrightarrow V_\delta$.
--
--   These tools serve the cardinality arguments of the construction. Items 1 and 4 show that a structure assembled as a direct limit of extensional relations whose well-foundedness is witnessed by countable ordinals embeds into $V_{\omega_1}$, so its size is at most $|V_{\omega_1}|$; this is how coherent systems of finite diagrams are ruled out. Item 2 is a sequence of length $\omega_2$ that increases modulo countable sets and is used to attach countable-ordinal tags to sets of rank below $\omega_2$, and item 3 produces the countable hulls of finite sets that labels refer to.
--
--   **Formalization Note** All objects are universe-polymorphic; sets are `ZFSet` and $V_\delta$ is `ZFSet.vonNeumann`. The four parts live in the namespaces `TaggedCollapse` (`collapse`, `injective`, `rank_le`, `embedding`, `wellFounded_of_tags`), `Domination`, `CountableClosures` and `TaggedLimit`. In `Domination`, `Alpha` and `Beta` are the subtypes of ordinals below $\omega_2$ and $\omega_1$, `indexEmbedding` is $\iota_\alpha$ (obtained by `Classical.choice`), `Prior` is $P(\alpha, \beta)$ and `values` is $\alpha \mapsto f_\alpha$, written with the ordinal successor and Lean's `iSup`, which is $0$ over an empty index type. In `CountableClosures`, `witness`, `stage`, `closure`, `FiniteSeed` (nonempty finsets), `entries` and `enumeration` are the objects of item 3 and `membership_separates` is its last claim. In `TaggedLimit`, `relation`, `rankTag` and `embedding` are built on `DirectLimit` of an injective directed system.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/ModelTheory/Categoricity/Collapse.lean

-- Generated from openai/math@1581d4c lean/OAI/ModelTheory/Categoricity/Collapse.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the CHObstruction mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_CHObstruction

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u v w

noncomputable section

namespace CHObstruction

open Cardinal Ordinal Order

namespace TaggedCollapse

variable {Q : Type u} (R : Q → Q → Prop) (wf : WellFounded R)

def collapse (x : Q) : ZFSet.{u} :=
  wf.fix (fun x rec => ZFSet.range (fun y : {y // R y x} => rec y.val y.property)) x

theorem collapse_eq (x : Q) :
    collapse R wf x = ZFSet.range (fun y : {y // R y x} => collapse R wf y.val) := by
  exact wf.fix_eq _ x

theorem mem_collapse {x : Q} {z : ZFSet.{u}} :
    z ∈ collapse R wf x ↔ ∃ y, R y x ∧ collapse R wf y = z := by
  rw [collapse_eq]
  simp only [ZFSet.mem_range, Subtype.exists, exists_prop]

theorem injective
    (extensional : ∀ x y, (∀ z, R z x ↔ R z y) → x = y) :
    Function.Injective (collapse R wf) := by
  intro x
  induction x using wf.induction with
  | h x ih =>
    intro x' heq
    apply extensional x x'
    intro y
    constructor
    · intro hy
      have hm : collapse R wf y ∈ collapse R wf x :=
        (mem_collapse R wf).2 ⟨y, hy, rfl⟩
      rw [heq] at hm
      obtain ⟨y', hy', hh⟩ := (mem_collapse R wf).1 hm
      have : y = y' := ih y hy hh.symm
      simpa only [this] using hy'
    · intro hy'
      have hm : collapse R wf y ∈ collapse R wf x' :=
        (mem_collapse R wf).2 ⟨y, hy', rfl⟩
      rw [← heq] at hm
      obtain ⟨y', hy, hh⟩ := (mem_collapse R wf).1 hm
      have : y' = y := ih y' hy hh
      simpa only [← this] using hy

theorem rank_le (ρ : Q → Ordinal.{u})
    (decreases : ∀ {x y}, R y x → ρ y < ρ x) (x : Q) :
    ZFSet.rank (collapse R wf x) ≤ ρ x := by
  induction x using wf.induction with
  | h x ih =>
    rw [collapse_eq, ZFSet.rank_range]
    apply Ordinal.iSup_le
    intro y
    exact Order.succ_le_of_lt ((ih y.val y.property).trans_lt (decreases y.property))

def embedding (extensional : ∀ x y, (∀ z, R z x ↔ R z y) → x = y)
    (ρ : Q → Ordinal.{u}) (decreases : ∀ {x y}, R y x → ρ y < ρ x)
    (δ : Ordinal.{u}) (bounded : ∀ x, ρ x < δ) :
    Q ↪ (ZFSet.vonNeumann δ) where
  toFun x := ⟨collapse R wf x,
    ZFSet.mem_vonNeumann.2 ((rank_le R wf ρ decreases x).trans_lt (bounded x))⟩
  inj' _x _y h := injective R wf extensional (congrArg Subtype.val h)

theorem wellFounded_of_tags (ρ : Q → Ordinal.{u})
    (decreases : ∀ {x y}, R y x → ρ y < ρ x) : WellFounded R :=
  (InvImage.wf ρ Ordinal.lt_wf).mono (fun _ _ h => decreases h)

end TaggedCollapse

namespace Domination

abbrev Alpha := {a : Ordinal.{u} // a < ω_ 2}
abbrev Beta := {b : Ordinal.{u} // b < ω_ 1}

def indexEmbedding (a : Alpha.{u}) : Set.Iio a.val ↪ Beta.{u} := by
  apply Classical.choice
  apply (Cardinal.le_def _ _).1
  change #(Set.Iio a.val) ≤ #(Set.Iio (ω_ (1 : Ordinal.{u})))
  rw [Cardinal.mk_Iio_ordinal, Cardinal.mk_Iio_ordinal, Cardinal.lift_le]
  have h : a.val.card < ℵ_ (2 : Ordinal.{u}) :=
    Cardinal.lt_omega_iff_card_lt.1 a.property
  have hs : ℵ_ (2 : Ordinal.{u}) = succ (ℵ_ (1 : Ordinal.{u})) := by
    rw [Cardinal.succ_aleph]
    norm_num
  simpa only [Ordinal.card_omega] using (Order.lt_succ_iff.1 (h.trans_eq hs))

theorem countable_Iio {b : Ordinal.{u}} (hb : b < ω_ 1) : Countable (Set.Iio b) := by
  apply Cardinal.mk_le_aleph0_iff.1
  rw [Cardinal.mk_Iio_ordinal, ← Cardinal.lift_aleph0.{u+1,u}, Cardinal.lift_le]
  exact Cardinal.lt_aleph_one_iff.1 (Cardinal.lt_omega_iff_card_lt.1 hb)

def Prior (a : Alpha.{u}) (b : Beta.{u}) :=
  {g : Set.Iio a.val // (indexEmbedding a g).val < b.val}

instance prior_countable (a : Alpha.{u}) (b : Beta.{u}) : Countable (Prior a b) := by
  have := countable_Iio b.property
  let f : Prior a b → Set.Iio b.val := fun g => ⟨(indexEmbedding a g.val).val, g.property⟩
  apply Function.Injective.countable (f := f)
  intro g h heq
  apply Subtype.ext
  apply (indexEmbedding a).injective
  apply Subtype.ext
  exact congrArg (fun x : Set.Iio b.val => x.val) heq

def values (a : Alpha.{u}) : Beta.{u} → Beta.{u} :=
  (InvImage.wf (fun a : Alpha.{u} => a.val) Ordinal.lt_wf).fix
    (C := fun _ => Beta.{u} → Beta.{u})
    (fun a rec b =>
      ⟨⨆ g : Prior a b, succ (rec ⟨g.val.val, lt_trans g.val.property a.property⟩ g.val.property b).val,
       Ordinal.iSup_lt_omega_one (fun g =>
         (Cardinal.isSuccLimit_omega 1).succ_lt
           (rec ⟨g.val.val, lt_trans g.val.property a.property⟩ g.val.property b).property)⟩) a

end Domination

namespace CountableClosures

variable {A : Type u} (R : A → A → Prop)
  (separates : ∀ a b, a ≠ b → ∃ w, ¬ (R w a ↔ R w b))

def witness (a b : A) : A := by
  classical
  exact if h : a = b then a else Classical.choose (separates a b h)

def stage (S : Set A) : ℕ → Set A
  | 0 => S
  | n + 1 => stage S n ∪ Set.image2 (witness R separates) (stage S n) (stage S n)

def closure (S : Set A) : Set A := ⋃ n, stage R separates S n

theorem subset_closure (S : Set A) : S ⊆ closure R separates S :=
  fun _ hx => Set.mem_iUnion.2 ⟨0, hx⟩

theorem closure_countable {S : Set A} (hS : S.Countable) :
    (closure R separates S).Countable := by
  apply Set.countable_iUnion
  intro n
  induction n with
  | zero => exact hS
  | succ n ih => exact ih.union (ih.image2 ih _)

abbrev FiniteSeed (A : Type u) := {X : Finset A // X.Nonempty}

def entries (X : FiniteSeed A) : Set A := closure R separates X.val

theorem entries_countable (X : FiniteSeed A) : (entries R separates X).Countable :=
  closure_countable R separates X.val.countable_toSet

theorem seed_subset (X : FiniteSeed A) : (X.val : Set A) ⊆ entries R separates X :=
  subset_closure R separates X.val

theorem entries_nonempty (X : FiniteSeed A) : (entries R separates X).Nonempty :=
  X.property.to_set.mono (seed_subset R separates X)

def enumeration (X : FiniteSeed A) : ℕ → entries R separates X :=
  let first : entries R separates X :=
    ⟨Classical.choose X.property, seed_subset R separates X (Classical.choose_spec X.property)⟩
  let e : ℕ → entries R separates X :=
    Classical.choose (Set.Countable.exists_surjective (entries_nonempty R separates X)
      (entries_countable R separates X))
  fun n => match n with | 0 => first | n + 1 => e n

theorem membership_separates (D : ZFSet.{u}) (hD : D.IsTransitive) :
    ∀ a b : D, a ≠ b → ∃ w : D, ¬ (w.val ∈ a.val ↔ w.val ∈ b.val) := by
  intro a b h
  have hab : a.val ≠ b.val := fun heq => h (Subtype.ext heq)
  obtain ⟨w, hw⟩ : ∃ w, ¬ (w ∈ a.val ↔ w ∈ b.val) := by
    by_contra hn
    exact hab (ZFSet.ext (by simpa only [not_exists, not_not] using hn))
  have hwD : w ∈ D := by
    by_cases hwa : w ∈ a.val
    · exact hD a.val a.property hwa
    · have hwb : w ∈ b.val := by tauto
      exact hD b.val b.property hwb
  exact ⟨⟨w, hwD⟩, hw⟩

end CountableClosures

namespace TaggedLimit

variable {ι : Type u} [Preorder ι] [IsDirectedOrder ι]
  (F : ι → Type u) (f : ∀ i j, i ≤ j → F i ↪ F j)
  [DirectedSystem F (fun i j h => f i j h)]
  (R : ∀ i, F i → F i → Prop)
  (respect : ∀ i j h x y, R i x y ↔ R j (f i j h x) (f i j h y))
  (ρ : ∀ i, F i → Ordinal.{u})
  (tags : ∀ i j h x, ρ i x = ρ j (f i j h x))

def relation : DirectLimit F f → DirectLimit F f → Prop :=
  DirectLimit.lift₂ f f R (fun i j h x y => propext (respect i j h x y))

def rankTag : DirectLimit F f → Ordinal.{u} :=
  DirectLimit.lift f ρ tags

theorem relation_mk (i) (x y : F i) :
    relation F f R respect ⟦⟨i, x⟩⟧ ⟦⟨i, y⟩⟧ ↔ R i x y := by
  rw [relation, DirectLimit.lift₂_def]

theorem rankTag_mk (i) (x : F i) :
    rankTag F f ρ tags ⟦⟨i, x⟩⟧ = ρ i x := rfl

theorem extensional (hext : ∀ i x y, (∀ z, R i z x ↔ R i z y) → x = y) :
    ∀ x y, (∀ z, relation F f R respect z x ↔ relation F f R respect z y) → x = y := by
  intro x y h
  obtain ⟨i, a, b, rfl, rfl⟩ := DirectLimit.exists_eq_mk₂ f x y
  congr 1
  congr 1
  apply hext i a b
  intro z
  exact (relation_mk F f R respect i z a).symm.trans
    ((h ⟦⟨i, z⟩⟧).trans (relation_mk F f R respect i z b))

theorem decreases (hdec : ∀ i x y, R i y x → ρ i y < ρ i x) :
    ∀ {x y}, relation F f R respect y x → rankTag F f ρ tags y < rankTag F f ρ tags x := by
  intro x y
  obtain ⟨i, a, b, rfl, rfl⟩ := DirectLimit.exists_eq_mk₂ f x y
  rw [relation_mk, rankTag_mk, rankTag_mk]
  exact hdec i a b

def embedding
    (hext : ∀ i x y, (∀ z, R i z x ↔ R i z y) → x = y)
    (hdec : ∀ i x y, R i y x → ρ i y < ρ i x)
    (δ : Ordinal.{u}) (hbound : ∀ i x, ρ i x < δ) :
    DirectLimit F f ↪ ZFSet.vonNeumann δ := by
  let rel := relation F f R respect
  let tag := rankTag F f ρ tags
  have hd : ∀ {x y}, rel y x → tag y < tag x := decreases F f R respect ρ tags hdec
  apply TaggedCollapse.embedding rel (TaggedCollapse.wellFounded_of_tags rel tag hd)
      (extensional F f R respect hext) tag hd δ
  intro x
  obtain ⟨i, a, rfl⟩ := DirectLimit.exists_eq_mk f x
  exact hbound i a

end TaggedLimit

end CHObstruction

end

end OAI


