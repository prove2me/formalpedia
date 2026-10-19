-- Prove2me | Definitions.Def_OAI_ModelTheory_Categoricity_ArrayEmbeddings
-- name    : OAI_ModelTheory_Categoricity_ArrayEmbeddings
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T02:44:41.439878+00:00
-- url     : https://prove2.me/theorems/e1626613-9abf-4618-bde5-f2d090eda0c6
-- title:
--   Colors along array maps, strong array maps, and array maps induced by structure embeddings
-- statement:
--   This file introduces the colors that an array map induces at base points, the *strong* array maps that encode the strong substructure relation of a CH-based abstract elementary class, a construction of array maps between array data with countable base, and the passage from abstract structure embeddings to array maps.
--
--   **Array data and array maps.** A *tuple* over a set $I$ is a nonempty finite injective sequence $t=(t_0,\dots,t_k)$ of elements of $I$; for an injection $g\colon I\to I'$ write $g t=(g(t_0),\dots,g(t_k))$. For a statement $P$ let $[P]\in\{0,1\}$ be $1$ if $P$ holds and $0$ otherwise. An *array datum* $M$ consists of a nonempty index set $I_M$, a nonempty dense linear order $B_M$ without endpoints (the *base*) in which every closed interval $[a,b]$ is countable, and bits $a^M_t(n,b)\in\{0,1\}$ for all tuples $t$ over $I_M$, levels $n\in\mathbb{N}$ and base elements $b\in B_M$. The universe $|M|$ of the structure attached to $M$ is the disjoint union of index points $i\in I_M$, base points $b\in B_M$, group points $\langle s\rangle$ and star points $\langle v\rangle_*$ (for finite $s\subseteq B_M$ and finite $v\subseteq\mathbb{N}$), row points $(t,n,s)$ and column points $(t,b,v)$, where $t$ is a tuple over $I_M$, $n\in\mathbb{N}$ and $b\in B_M$. The countable relational language consists of: unary predicates for index, base, group and star points; for all $k,n\in\mathbb{N}$ the unary predicate of the row points $(t,n,s)$ whose tuple has $k+1$ entries, and for each $k$ the unary predicate of the column points whose tuple has $k+1$ entries; for each finite $v\subseteq\mathbb{N}$ a label holding only at $\langle v\rangle_*$; the row projections, holding exactly of the lists $((t,n,s),t_0,\dots,t_k)$, and the column projections, holding exactly of the lists $((t,b,v),b,t_0,\dots,t_k)$ (one symbol for each tuple length and, for rows, each level); the order $b<b'$ of base points; incidence between $b$ and $\langle s\rangle$ when $b\in s$; the graphs $(\langle s\rangle,\langle s'\rangle,\langle s\triangle s'\rangle)$ and $(\langle v\rangle_*,\langle v'\rangle_*,\langle v\triangle v'\rangle_*)$ of symmetric difference $\triangle$; the row action $((t,n,s),\langle u\rangle,(t,n,s\triangle u))$ and the column action $((t,b,v),\langle u\rangle_*,(t,b,v\triangle u))$; and the bit relation, which holds between a row point $(t,n,s)$ and a column point $(t',b,v)$ if and only if $t=t'$ and
--   $$
--   a^M_t(n,b)+[b\in s]+[n\in v]\equiv 1\pmod 2 .
--   $$
--   No other lists of points are related. We write $M\models R(\bar x)$ when the relation $R$ holds of the finite list $\bar x$ of points.
--
--   An *array map* $f\colon M\to N$ consists of an injection $f_I\colon I_M\to I_N$, an order embedding $f_B\colon B_M\to B_N$, finite *row shifts* $\rho^f_{t,n}\subseteq B_N$ and finite *column shifts* $\gamma^f_{t,b}\subseteq\mathbb{N}$ (for tuples $t$ over $I_M$, $n\in\mathbb{N}$ and $b\in B_M$) such that for all $t,n,b$
--   $$
--   a^N_{f_I t}(n,f_B b)+[f_B b\in\rho^f_{t,n}]+[n\in\gamma^f_{t,b}]\equiv a^M_t(n,b)\pmod 2 .
--   $$
--   It acts on points by $\hat f(i)=f_I(i)$, $\hat f(b)=f_B(b)$, $\hat f\langle s\rangle=\langle f_B[s]\rangle$, $\hat f\langle v\rangle_*=\langle v\rangle_*$ and
--   $$
--   \hat f(t,n,s)=\bigl(f_I t,\ n,\ \rho^f_{t,n}\triangle f_B[s]\bigr),\qquad \hat f(t,b,v)=\bigl(f_I t,\ f_B b,\ \gamma^f_{t,b}\triangle v\bigr).
--   $$
--
--   **Colors and the test.** Let $\mathcal{C}=\{0,1\}^{\mathbb{N}}/{=^*}$, where $x=^*y$ means that the sequences $x$ and $y$ differ at only finitely many $n$, and write $[x]_*\in\mathcal{C}$ for the class of $x$. The *color* of an array datum $M$ at a tuple $t$ over $I_M$ and $b\in B_M$ is $c^M_t(b)=[\,n\mapsto a^M_t(n,b)\,]_*$, the class of the bit sequence read off at the origin points $(t,n,\emptyset)$ and $(t,b,\emptyset)$. Assume CH, that is $2^{\aleph_0}=\aleph_1$. A *diagram* on a finite set $A$ equips the labels $(X,n)$, with $\emptyset\ne X\subseteq A$ and $n\in\mathbb{N}$, with two binary relations and with tags that are countable ordinals; it is *valid* if the first relation is an equivalence relation respected by the second relation and by the tags, the second relation is extensional (labels with the same predecessors are equivalent) and strictly increases tags, and the labels $(\{x\},0)$ for distinct $x\in A$ are inequivalent. Under CH there are at most continuum many pairs $(m,D)$ with $D$ a diagram on $\{0,\dots,m\}$, and a fixed injection $\iota$ of these pairs into $\mathcal{C}$ is chosen. For a coloring $c$ of the tuples over a set $I$ by elements of $\mathcal{C}$ and a tuple $t=(t_0,\dots,t_k)$, the *test* $T(c,t)$ holds if there is a diagram $D$ on $\{0,\dots,k\}$ such that for every nonempty subsequence $t|_J$ of $t$ (kept in its original order, $t$ itself included) the restriction $D|_J$ of $D$ to the positions in $J$ (renumbered as $\{0,\dots,m\}$ when $J$ has $m+1$ elements) is valid and $\iota(D|_J)=c(t|_J)$.
--
--   The file defines:
--
--   1. **Colors along a map.** For an array map $f\colon M\to N$, a tuple $t$ over $I_M$ and $b\in B_N$,
--   $$
--   c^f_t(b)=\bigl[\,n\mapsto a^N_{f_I t}(n,b)+[b\in\rho^f_{t,n}]\bmod 2\,\bigr]_*\in\mathcal{C},
--   $$
--   the color read off in $N$ at the column point $(f_I t,b,\emptyset)$ against the images $\hat f(t,n,\emptyset)$ of the origin rows of $M$. Changing a sequence at finitely many levels does not change its class, and consequently $c^f_t(f_B b)=c^M_t(b)$ for every $b\in B_M$.
--
--   2. **Exceptional set.** For a tuple $t$ over $I_M$, $E^f_t=\bigcup_{J}\bigcup_{n\in\mathbb{N}}\rho^f_{t|_J,\,n}\subseteq B_N$, the union over all nonempty subsequences $t|_J$ of $t$ and all levels $n$. It is a countable union of finite sets, and at every $b\notin E^f_t$ the colors $c^f_{t|_J}(b)$ coincide with the colors $c^N_{f_I(t|_J)}(b)$ of $N$ itself.
--
--   3. **Strong maps.** Under CH, an array map $f\colon M\to N$ is *strong* if (i) the image $f_B[B_M]$ is convex in $B_N$ (whenever $x\le z\le y$ in $B_N$ with $x,y$ in the image, $z$ is in the image), and (ii) for every tuple $t$ over $I_M$ and every $b\in B_N\setminus f_B[B_M]$,
--   $$
--   T\bigl(s\mapsto c^f_s(b),\ t\bigr).
--   $$
--   The identity array map is strong.
--
--   4. **Relabelling tuples.** A bijection $e\colon I\to I'$ induces the bijection $t\mapsto e t$ between the tuples over $I$ and over $I'$. The test is invariant under relabelling along any injection $g$: $T(c,g t)$ holds if and only if $T(s\mapsto c(g s),t)$ holds.
--
--   5. **Maps between countable-base data.** If $B_M$ is countable, $e_I\colon I_M\to I_N$ is a bijection and $e_B\colon B_M\to B_N$ is an order isomorphism, a choice of shifts gives an array map $M\to N$ with index part $e_I$ and base part $e_B$: its row shifts are $e_B[U_{t,n}]$ and its column shifts are $V_{t,b}$, for finite sets $U_{t,n}\subseteq B_M$ and $V_{t,b}\subseteq\mathbb{N}$ with
--   $$
--   a^N_{e_I t}(n,e_B b)+[b\in U_{t,n}]+[n\in V_{t,b}]\equiv a^M_t(n,b)\pmod 2 ,
--   $$
--   which exist because $B_M$ is countable.
--
--   6. **Raw embeddings.** A raw embedding $\phi\colon M\to N$ is an injective map $\phi\colon|M|\to|N|$ such that $N\models R(\phi\bar x)\iff M\models R(\bar x)$ for every relation symbol $R$ and every finite list $\bar x$ of points of $M$, and which preserves supports: for every finite $s\subseteq B_M$ and every $b\in B_N$, the base point $b$ is incident to $\phi\langle s\rangle$ in $N$ if and only if $\phi(a)=b$ for some $a\in s$. Such a $\phi$ sends index points to index points and base points to base points, giving an injection $\phi_I\colon I_M\to I_N$ and an order embedding $\phi_B\colon B_M\to B_N$; it satisfies $\phi\langle s\rangle=\langle\phi_B[s]\rangle$ and $\phi\langle v\rangle_*=\langle v\rangle_*$; and if $\rho_{t,n}$ and $\gamma_{t,b}$ are defined by $\phi(t,n,\emptyset)=(\phi_I t,n,\rho_{t,n})$ and $\phi(t,b,\emptyset)=(\phi_I t,\phi_B b,\gamma_{t,b})$, then
--   $$
--   \phi(t,n,s)=\bigl(\phi_I t,\ n,\ \rho_{t,n}\triangle\phi_B[s]\bigr),\qquad \phi(t,b,v)=\bigl(\phi_I t,\ \phi_B b,\ \gamma_{t,b}\triangle v\bigr).
--   $$
--   These data form an array map $f_\phi\colon M\to N$ whose action on points is exactly $\phi$.
--
--   Strong maps formalize strong inclusions: the old base is convex in the new one, and at every new base point every old tuple passes the test, with colors computed from the old rows and with no exceptions at all, whereas membership in the class only asks that, for each tuple, the test fail at no more than countably many base points. Since every array map is itself a support-preserving embedding, item 6 shows that array maps correspond exactly to the support-preserving embeddings of the attached structures, so the class can be defined on abstract structures while all arguments are carried out with array maps.
--
--   **Formalization Note** `Map.colors` takes values in `Colors.Palette`, a universe-lifted copy of $\mathcal{C}$; `color_column` is the invariance under finite changes and `Map.colors_base` the identity at old base points. `Map.exceptions` indexes subsequences by order embeddings of `Fin (m+1)` into `Fin (k+1)`. `Map.Strong hCH f` is a `Prop`-valued structure with fields `convex` (Mathlib's `Set.OrdConnected`) and `outside`; the test is `Tests.Test hCH`, whose coding $\iota$ is `Colors.code hCH`; the identity is strong by `Map.id_strong`, and relabelling invariance is the definitional lemma `Tests.map`. `Tuples.mapEquiv` is the bijection of item 4, and `countableMap` is item 5 (its shifts are chosen with the normalization lemma `Matrix.normalize` for countable bases). `Tuples.entriesList` lists the entries of a tuple and is injective. `RawEmbedding` has fields `toEmbedding`, `relates` and `supports`; the derived `RawEmbedding.index`, `base`, `indexEmb`, `baseEmb`, `rowShift` and `colShift` are obtained by choice, `group_apply`, `star_apply`, `row_apply` and `col_apply` are the formulas above, and `RawEmbedding.toMap` with `toMap_onPoint` is $f_\phi$. A private helper `dite_eq_left` restates a core lemma.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/ModelTheory/Categoricity/ArrayEmbeddings.lean

-- Generated from openai/math@1581d4c lean/OAI/ModelTheory/Categoricity/ArrayEmbeddings.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the CHObstruction mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_CHObstruction
import Definitions.Def_OAI_ModelTheory_Categoricity_Collapse
import Definitions.Def_OAI_ModelTheory_Categoricity_Diagrams
import Definitions.Def_OAI_ModelTheory_Categoricity_Partition
import Definitions.Def_OAI_ModelTheory_Categoricity_Colors
import Definitions.Def_OAI_ModelTheory_Categoricity_EndpointDiagrams
import Definitions.Def_OAI_ModelTheory_Categoricity_TailBound
import Definitions.Def_OAI_ModelTheory_Categoricity_Arrays
import Definitions.Def_OAI_ModelTheory_Categoricity_ArrayMaps

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e

namespace OAI

universe u v w

noncomputable section

namespace CHObstruction

open Cardinal Ordinal Order

namespace Tests

open Tuples

@[simp] theorem map {I J : Type u} (hCH : CH.{u}) (f : I ↪ J)
    (c : Tuple J → Colors.Palette.{u}) (t : Tuple I) :
    Test hCH c (Tuples.map f t) ↔ Test hCH (fun s => c (Tuples.map f s)) t := Iff.rfl

end Tests

namespace Arrays

open Tuples
open scoped symmDiff

variable {M N P : Data.{u}}
local instance instDecidableEqB_8 : DecidableEq M.B := Classical.decEq M.B
local instance instDecidableEqB_9 : DecidableEq N.B := Classical.decEq N.B
local instance instDecidableEqB_10 : DecidableEq P.B := Classical.decEq P.B

def Map.colors (f : Map M N) (t : Tuple M.I) (b : N.B) : Colors.Palette.{u} :=
  ⟨Colors.color (fun n => N.bits (Tuples.map f.index t) n b ^^ decide (b ∈ f.rowShift t n))⟩

theorem color_column (a : ℕ → Bool) (v : Finset ℕ) :
    Colors.color (fun n => a n ^^ decide (n ∈ v)) = Colors.color a := by
  apply Quotient.sound
  apply v.finite_toSet.subset
  intro n hn
  by_contra h
  have h' : n ∉ v := h
  exact hn (by simp [h'])

@[simp] theorem Map.colors_base (f : Map M N) (t : Tuple M.I) (b : M.B) :
    f.colors t (f.base b) = M.colors t b := by
  apply ULift.ext
  change Colors.color _ = Colors.color _
  have he : (fun n => N.bits (Tuples.map f.index t) n (f.base b) ^^
      decide (f.base b ∈ f.rowShift t n)) =
      (fun n => M.bits t n b ^^ decide (n ∈ f.colShift t b)) := by
    funext n
    have h := f.bit_agrees t n b
    dsimp [Matrix.bit] at h
    rw [← h, Bool.xor_assoc, Bool.xor_self, Bool.xor_false]
  rw [he, color_column]

def Map.exceptions (f : Map M N) (t : Tuple M.I) : Set N.B :=
  ⋃ m : ℕ, ⋃ e : Fin (m + 1) ↪o Fin (t.1 + 1), ⋃ n : ℕ,
    (f.rowShift (sub t e) n : Set N.B)

structure Map.Strong (hCH : CH.{u}) (f : Map M N) : Prop where
  convex : Set.OrdConnected (Set.range f.base)
  outside : ∀ (t : Tuple M.I) (b : N.B), b ∉ Set.range f.base →
    Tests.Test hCH (fun s => f.colors s b) t

@[simp] theorem Map.id_strong (hCH : CH.{u}) (M : Data.{u}) : (Map.id M).Strong hCH := by
  constructor
  · simpa only [Map.id, OrderIso.coe_toOrderEmbedding, OrderIso.coe_refl, Set.range_id] using
      (Set.ordConnected_univ : Set.OrdConnected (Set.univ : Set M.B))
  · intro t b hb
    exact (hb ⟨b, rfl⟩).elim

end Arrays

namespace Tuples

variable {I J : Type u}

def mapEquiv (e : I ≃ J) : Tuple I ≃ Tuple J where
  toFun := map e.toEmbedding
  invFun := map e.symm.toEmbedding
  left_inv t := by
    have h : e.toEmbedding.trans e.symm.toEmbedding = Function.Embedding.refl I := by ext x; simp
    rw [map_comp, h, map_refl]
  right_inv t := by
    have h : e.symm.toEmbedding.trans e.toEmbedding = Function.Embedding.refl J := by ext x; simp
    rw [map_comp, h, map_refl]

end Tuples

namespace Arrays

open Tuples
open scoped symmDiff

variable {M N : Data.{u}}
local instance instDecidableEqB_11 : DecidableEq M.B := Classical.decEq M.B
local instance instDecidableEqB_12 : DecidableEq N.B := Classical.decEq N.B

def countableMap [Countable M.B] (ei : M.I ≃ N.I) (eb : M.B ≃o N.B) : Map M N := by
  have h := fun t : Tuple M.I => Matrix.normalize (M.bits t)
    (fun n b => N.bits (Tuples.map ei.toEmbedding t) n (eb b))
  choose U V hUV using h
  exact {
    index := ei.toEmbedding
    base := eb.toOrderEmbedding
    rowShift := fun t n => (U t n).map eb.toOrderEmbedding.toEmbedding
    colShift := V
    bit_agrees := fun t n b => by
      simpa only [Matrix.bit, Finset.mem_map, OrderIso.coe_toOrderEmbedding,
        RelEmbedding.coe_toEmbedding, eb.injective.eq_iff, exists_eq_right] using hUV t n b }

end Arrays

namespace Tuples

def entriesList {I : Type u} (t : Tuple I) : List I := List.ofFn t.2

theorem entriesList_injective {I : Type u} : Function.Injective (@entriesList I) := by
  rintro ⟨n, a⟩ ⟨m, b⟩ h
  have hn := congrArg List.length h
  simp only [entriesList, List.length_ofFn] at hn
  have he : n = m := Nat.add_right_cancel hn
  subst m
  congr 1
  apply Function.Embedding.ext
  intro i
  have hv := congrArg (fun l : List I => l[i.val]?) h
  simpa only [entriesList, List.getElem?_ofFn, i.isLt, dite_eq_left, Option.some.injEq] using hv

end Tuples

namespace Arrays

open Tuples
open scoped symmDiff

variable {M N : Data.{u}}
local instance instDecidableEqB_13 : DecidableEq M.B := Classical.decEq M.B
local instance instDecidableEqB_14 : DecidableEq N.B := Classical.decEq N.B

structure RawEmbedding (M N : Data.{u}) where
  toEmbedding : M.Carrier ↪ N.Carrier
  relates : ∀ s xs, N.rawRel s (xs.map toEmbedding) ↔ M.rawRel s xs
  supports : ∀ (s : Finset M.B) (b : N.B),
    N.rawRel .incidence [.base b, toEmbedding (.group s)] ↔
      ∃ a ∈ s, toEmbedding (.base a) = .base b

variable (f : RawEmbedding M N)

theorem RawEmbedding.index_exists (i : M.I) : ∃ j, f.toEmbedding (.index i) = .index j := by
  have h := (f.relates .index [.index i]).2 trivial
  cases he : f.toEmbedding (.index i) <;> simp_all [Data.rawRel]

theorem RawEmbedding.base_exists (b : M.B) : ∃ c, f.toEmbedding (.base b) = .base c := by
  have h := (f.relates .base [.base b]).2 trivial
  cases he : f.toEmbedding (.base b) <;> simp_all [Data.rawRel]

def RawEmbedding.index (i : M.I) : N.I := (f.index_exists i).choose

def RawEmbedding.base (b : M.B) : N.B := (f.base_exists b).choose

@[simp] theorem RawEmbedding.index_apply (i : M.I) :
    f.toEmbedding (.index i) = .index (f.index i) := (f.index_exists i).choose_spec

@[simp] theorem RawEmbedding.base_apply (b : M.B) :
    f.toEmbedding (.base b) = .base (f.base b) := (f.base_exists b).choose_spec

def RawEmbedding.indexEmb : M.I ↪ N.I where
  toFun := f.index
  inj' a b h := Point.index.inj (f.toEmbedding.injective (by simp only [f.index_apply, h]))

def RawEmbedding.baseEmb : M.B ↪o N.B := OrderEmbedding.ofStrictMono f.base (by
  intro a b hab
  have h := (f.relates .order [.base a, .base b]).2 hab
  simpa only [List.map_cons, List.map_nil, f.base_apply, Data.rawRel] using h)

@[simp] theorem RawEmbedding.indexEmb_apply (i : M.I) : f.indexEmb i = f.index i := rfl
@[simp] theorem RawEmbedding.baseEmb_apply (b : M.B) : f.baseEmb b = f.base b := rfl

@[simp] theorem RawEmbedding.group_apply (s : Finset M.B) :
    f.toEmbedding (.group s) = .group (s.map f.baseEmb.toEmbedding) := by
  have h := (f.relates .group [.group s]).2 trivial
  cases he : f.toEmbedding (.group s) <;> simp only [List.map_cons, List.map_nil, he,
    Data.rawRel] at h
  case group v =>
    congr 1
    ext b
    have hs := f.supports s b
    simp only [he, Data.rawRel, f.base_apply, Point.base.injEq] at hs
    simpa only [Finset.mem_map, RelEmbedding.coe_toEmbedding, RawEmbedding.baseEmb_apply] using hs

@[simp] theorem RawEmbedding.star_apply (v : Finset ℕ) : f.toEmbedding (.star v) = .star v := by
  have h := (f.relates (.label v) [.star v]).2 rfl
  cases he : f.toEmbedding (.star v) <;> simp only [List.map_cons, List.map_nil, he,
    Data.rawRel] at h
  case star w => exact congrArg Point.star h.symm

theorem RawEmbedding.row_exists (t : Tuple M.I) (n : ℕ) (s : Finset M.B) :
    ∃ v, f.toEmbedding (.row t n s) = .row (Tuples.map f.indexEmb t) n v := by
  have hu := (f.relates (.row t.1 n) [.row t n s]).2 ⟨rfl, rfl⟩
  have hp := (f.relates (.rowProjection t.1 n)
    (.row t n s :: List.ofFn (fun i => Point.index (t.2 i)))).2 ⟨rfl, rfl, rfl⟩
  cases he : f.toEmbedding (.row t n s) <;>
    simp only [List.map_cons, List.map_nil, he, Data.rawRel] at hu
  case row r m v =>
    obtain ⟨hk, rfl⟩ := hu
    simp only [List.map_cons, List.map_ofFn, Function.comp_def, he, f.index_apply, Data.rawRel, true_and] at hp
    have ht : r = Tuples.map f.indexEmb t := by
      apply Tuples.entriesList_injective
      apply (show Function.Injective (Point.index (I := N.I) (B := N.B)) from fun _ _ h => Point.index.inj h).list_map
      simp only [Tuples.entriesList, List.map_ofFn]
      exact hp.2.symm
    exact ⟨v, by rw [ht]⟩

theorem RawEmbedding.col_exists (t : Tuple M.I) (b : M.B) (v : Finset ℕ) :
    ∃ w, f.toEmbedding (.col t b v) = .col (Tuples.map f.indexEmb t) (f.base b) w := by
  have hu := (f.relates (.col t.1) [.col t b v]).2 rfl
  have hp := (f.relates (.colProjection t.1)
    (.col t b v :: .base b :: List.ofFn (fun i => Point.index (t.2 i)))).2 ⟨rfl, rfl, rfl⟩
  cases he : f.toEmbedding (.col t b v) <;>
    simp only [List.map_cons, List.map_nil, he, Data.rawRel] at hu
  case col r c w =>
    simp only [List.map_cons, List.map_ofFn, Function.comp_def, he, f.index_apply, f.base_apply, Data.rawRel,
      Point.base.injEq] at hp
    have ht : r = Tuples.map f.indexEmb t := by
      apply Tuples.entriesList_injective
      apply (show Function.Injective (Point.index (I := N.I) (B := N.B)) from fun _ _ h => Point.index.inj h).list_map
      simp only [Tuples.entriesList, List.map_ofFn]
      exact hp.2.2.symm
    exact ⟨w, by rw [ht, ← hp.2.1]⟩

def RawEmbedding.rowShift (t : Tuple M.I) (n : ℕ) : Finset N.B :=
  (f.row_exists t n ∅).choose

def RawEmbedding.colShift (t : Tuple M.I) (b : M.B) : Finset ℕ :=
  (f.col_exists t b ∅).choose

@[simp] theorem RawEmbedding.row_zero (t : Tuple M.I) (n : ℕ) :
    f.toEmbedding (.row t n ∅) = .row (Tuples.map f.indexEmb t) n (f.rowShift t n) :=
  (f.row_exists t n ∅).choose_spec

@[simp] theorem RawEmbedding.col_zero (t : Tuple M.I) (b : M.B) :
    f.toEmbedding (.col t b ∅) = .col (Tuples.map f.indexEmb t) (f.base b) (f.colShift t b) :=
  (f.col_exists t b ∅).choose_spec

@[simp] theorem RawEmbedding.row_apply (t : Tuple M.I) (n : ℕ) (s : Finset M.B) :
    f.toEmbedding (.row t n s) = .row (Tuples.map f.indexEmb t) n
      (f.rowShift t n ∆ s.map f.baseEmb.toEmbedding) := by
  obtain ⟨v, hv⟩ := f.row_exists t n s
  have h := (f.relates .rowAct [.row t n ∅, .group s, .row t n s]).2
    ⟨rfl, rfl, (bot_symmDiff s).symm⟩
  simp only [List.map_cons, List.map_nil, f.row_zero, f.group_apply, hv, Data.rawRel,
    true_and] at h
  rw [hv, h]

@[simp] theorem RawEmbedding.col_apply (t : Tuple M.I) (b : M.B) (v : Finset ℕ) :
    f.toEmbedding (.col t b v) = .col (Tuples.map f.indexEmb t) (f.base b)
      (f.colShift t b ∆ v) := by
  obtain ⟨w, hw⟩ := f.col_exists t b v
  have h := (f.relates .colAct [.col t b ∅, .star v, .col t b v]).2
    ⟨rfl, rfl, (bot_symmDiff v).symm⟩
  simp only [List.map_cons, List.map_nil, f.col_zero, f.star_apply, hw, Data.rawRel,
    true_and] at h
  rw [hw, h]

def RawEmbedding.toMap : Map M N where
  index := f.indexEmb
  base := f.baseEmb
  rowShift := f.rowShift
  colShift := f.colShift
  bit_agrees t n b := by
    have h := f.relates .bit [.row t n ∅, .col t b ∅]
    simp only [List.map_cons, List.map_nil, f.row_zero, f.col_zero, Data.rawRel,
      true_and] at h
    have he : Matrix.bit (M.bits t) n ∅ b ∅ = M.bits t n b := by simp [Matrix.bit]
    rw [he] at h
    exact Bool.eq_iff_iff.2 h

@[simp] theorem RawEmbedding.toMap_onPoint (x : M.Carrier) :
    f.toMap.onPoint x = f.toEmbedding x := by
  cases x <;> simp [RawEmbedding.toMap, Map.onPoint]

end Arrays

end CHObstruction

end

end OAI


