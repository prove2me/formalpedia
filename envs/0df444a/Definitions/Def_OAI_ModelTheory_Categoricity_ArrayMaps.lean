-- Prove2me | Definitions.Def_OAI_ModelTheory_Categoricity_ArrayMaps
-- name    : OAI_ModelTheory_Categoricity_ArrayMaps
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T02:42:35.224552+00:00
-- url     : https://prove2.me/theorems/aa07fc3a-925c-45f4-a63f-230039be5084
-- title:
--   Identity and composition of array maps, and array maps as embeddings of array structures
-- statement:
--   This file defines the identity and the composition of *array maps*, the morphisms between the array data from which the structures of a CH-based abstract elementary class are built, and shows that array maps are embeddings of the attached relational structures.
--
--   **Array data and their structures.** A *tuple* over a set $I$ is a nonempty finite injective sequence $t=(t_0,\dots,t_k)$ of elements of $I$; for an injection $g\colon I\to I'$ write $g t=(g(t_0),\dots,g(t_k))$. For a statement $P$ let $[P]\in\{0,1\}$ be $1$ if $P$ holds and $0$ otherwise. An *array datum* $M$ consists of a nonempty index set $I_M$, a nonempty dense linear order $B_M$ without endpoints (the *base*) in which every closed interval $[a,b]$ is countable, and bits $a^M_t(n,b)\in\{0,1\}$ for all tuples $t$ over $I_M$, levels $n\in\mathbb{N}$ and base elements $b\in B_M$. The universe $|M|$ of the structure attached to $M$ is the disjoint union of index points $i\in I_M$, base points $b\in B_M$, group points $\langle s\rangle$ and star points $\langle v\rangle_*$ (for finite $s\subseteq B_M$ and finite $v\subseteq\mathbb{N}$), row points $(t,n,s)$ and column points $(t,b,v)$, where $t$ is a tuple over $I_M$, $n\in\mathbb{N}$ and $b\in B_M$. The countable relational language consists of: unary predicates for index, base, group and star points; for all $k,n\in\mathbb{N}$ the unary predicate of the row points $(t,n,s)$ whose tuple has $k+1$ entries, and for each $k$ the unary predicate of the column points whose tuple has $k+1$ entries; for each finite $v\subseteq\mathbb{N}$ a label holding only at $\langle v\rangle_*$; the row projections, holding exactly of the lists $((t,n,s),t_0,\dots,t_k)$, and the column projections, holding exactly of the lists $((t,b,v),b,t_0,\dots,t_k)$ (one symbol for each tuple length and, for rows, each level); the order $b<b'$ of base points; incidence between $b$ and $\langle s\rangle$ when $b\in s$; the graphs $(\langle s\rangle,\langle s'\rangle,\langle s\triangle s'\rangle)$ and $(\langle v\rangle_*,\langle v'\rangle_*,\langle v\triangle v'\rangle_*)$ of symmetric difference $\triangle$; the row action $((t,n,s),\langle u\rangle,(t,n,s\triangle u))$ and the column action $((t,b,v),\langle u\rangle_*,(t,b,v\triangle u))$; and the bit relation, which holds between a row point $(t,n,s)$ and a column point $(t',b,v)$ if and only if $t=t'$ and
--   $$
--   a^M_t(n,b)+[b\in s]+[n\in v]\equiv 1\pmod 2 .
--   $$
--   No other lists of points are related. We write $M\models R(\bar x)$ when the relation $R$ holds of the finite list $\bar x$ of points.
--
--   **Array maps.** An *array map* $f\colon M\to N$ consists of an injection $f_I\colon I_M\to I_N$, an order embedding $f_B\colon B_M\to B_N$, finite *row shifts* $\rho^f_{t,n}\subseteq B_N$ and finite *column shifts* $\gamma^f_{t,b}\subseteq\mathbb{N}$ (for tuples $t$ over $I_M$, $n\in\mathbb{N}$ and $b\in B_M$) such that for all $t,n,b$
--   $$
--   a^N_{f_I t}(n,f_B b)+[f_B b\in\rho^f_{t,n}]+[n\in\gamma^f_{t,b}]\equiv a^M_t(n,b)\pmod 2 .
--   $$
--   It acts on points by $\hat f(i)=f_I(i)$, $\hat f(b)=f_B(b)$, $\hat f\langle s\rangle=\langle f_B[s]\rangle$, $\hat f\langle v\rangle_*=\langle v\rangle_*$ and
--   $$
--   \hat f(t,n,s)=\bigl(f_I t,\ n,\ \rho^f_{t,n}\triangle f_B[s]\bigr),\qquad \hat f(t,b,v)=\bigl(f_I t,\ f_B b,\ \gamma^f_{t,b}\triangle v\bigr).
--   $$
--
--   The file defines:
--
--   1. **Identity.** The identity array map $\mathrm{id}_M\colon M\to M$ has the identity maps of $I_M$ and $B_M$ as index and base parts, and all its row and column shifts are empty.
--
--   2. **Composition.** For array maps $f\colon M\to N$ and $g\colon N\to P$, the composite $g\circ f\colon M\to P$ has index part $g_I\circ f_I$, base part $g_B\circ f_B$, and shifts
--   $$
--   \rho^{g\circ f}_{t,n}=\rho^g_{f_I t,\,n}\ \triangle\ g_B\bigl[\rho^f_{t,n}\bigr],\qquad
--   \gamma^{g\circ f}_{t,b}=\gamma^g_{f_I t,\,f_B b}\ \triangle\ \gamma^f_{t,b}.
--   $$
--
--   Alongside these definitions the file establishes that every array map $f\colon M\to N$ is an embedding of structures: for every relation symbol $R$ of the language and every finite list $\bar x$ of points of $M$,
--   $$
--   N\models R(\hat f\bar x)\iff M\models R(\bar x).
--   $$
--   It also shows that $\widehat{\mathrm{id}_M}$ is the identity of $|M|$, that $\widehat{g\circ f}=\hat g\circ\hat f$, that an array map is determined by its action on points, and that $f\circ\mathrm{id}_M=f=\mathrm{id}_N\circ f$.
--
--   Array data with array maps therefore behave as a category of concrete structure embeddings. This is the frame in which the strong substructure relation of the class is expressed (a strong inclusion is witnessed by an array map with additional properties), and identities and composites are the basic operations used for directed systems of array data and their limits.
--
--   **Formalization Note** The structure `Map M N` (introduced with the array data) has fields `index`, `base`, `rowShift`, `colShift` and the compatibility axiom `bit_agrees`; `Map.onPoint` is the action $\hat f$. Bits are Booleans and the sum modulo $2$ is exclusive or (`Matrix.bit`). A tuple is a number $k$ together with an injection of `Fin (k+1)`, so the Lean indices of the row and column predicates are the tuple length minus one. Relations are given by `Data.rawRel` on lists of points (a list of the wrong length satisfies no relation) and by `Data.rel` for symbols of a fixed arity; the embedding property is `Map.rawRel` and `Map.rel`, proved symbol by symbol (`raw_map_index`, ..., `raw_map_colAct`) from the algebraic equivalences `row_action_iff`, `col_action_iff`, `bit_relation_iff`, `group_add_iff`, `tuple_list_eq_iff` and `base_point_eq_iff`. The category facts are `Map.id_onPoint`, `Map.comp_onPoint`, `Map.ext_onPoint`, `Map.comp_id` and `Map.id_comp`. Decidable equality on base orders is supplied classically.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/ModelTheory/Categoricity/ArrayMaps.lean

-- Generated from openai/math@1581d4c lean/OAI/ModelTheory/Categoricity/ArrayMaps.lean by skeleton subtraction
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

namespace OAI

universe u v w

noncomputable section

namespace CHObstruction

open Cardinal Ordinal Order

namespace Arrays

section

open Tuples
open scoped symmDiff

variable {M N : Data.{u}} (f : Map M N)
local instance instDecidableEqB_3 : DecidableEq M.B := Classical.decEq M.B
local instance instDecidableEqB_4 : DecidableEq N.B := Classical.decEq N.B

 theorem row_action_iff (t t' : Tuple M.I) (n n' : ℕ) (s u s' : Finset M.B) :
    (Tuples.map f.index t' = Tuples.map f.index t ∧ n' = n ∧
      f.rowShift t' n' ∆ s'.map f.base.toEmbedding =
        (f.rowShift t n ∆ s.map f.base.toEmbedding) ∆ u.map f.base.toEmbedding) ↔
      (t' = t ∧ n' = n ∧ s' = s ∆ u) := by
  rw [Tuples.map_eq_iff]
  constructor
  · rintro ⟨rfl, rfl, h⟩
    refine ⟨rfl, rfl, ?_⟩
    rw [symmDiff_assoc, ← FiniteSupports.map_symmDiff, symmDiff_right_inj] at h
    exact Finset.map_injective _ h
  · rintro ⟨rfl, rfl, rfl⟩
    exact ⟨rfl, rfl, by rw [FiniteSupports.map_symmDiff, symmDiff_assoc]⟩

 theorem col_action_iff (t t' : Tuple M.I) (b b' : M.B) (v u v' : Finset ℕ) :
    (Tuples.map f.index t' = Tuples.map f.index t ∧ f.base b' = f.base b ∧
      f.colShift t' b' ∆ v' = (f.colShift t b ∆ v) ∆ u) ↔
      (t' = t ∧ b' = b ∧ v' = v ∆ u) := by
  rw [Tuples.map_eq_iff, f.base.injective.eq_iff]
  constructor
  · rintro ⟨rfl, rfl, h⟩
    exact ⟨rfl, rfl, by simpa only [symmDiff_assoc, symmDiff_right_inj] using h⟩
  · rintro ⟨rfl, rfl, rfl⟩
    exact ⟨rfl, rfl, (symmDiff_assoc _ _ _).symm⟩

 theorem bit_relation_iff (t t' : Tuple M.I) (n : ℕ) (b : M.B)
    (s : Finset M.B) (v : Finset ℕ) :
    (Tuples.map f.index t = Tuples.map f.index t' ∧
      Matrix.bit (N.bits (Tuples.map f.index t)) n
        (f.rowShift t n ∆ s.map f.base.toEmbedding) (f.base b) (f.colShift t' b ∆ v) = true) ↔
      (t = t' ∧ Matrix.bit (M.bits t) n s b v = true) := by
  rw [Tuples.map_eq_iff]
  constructor
  · rintro ⟨rfl, hb⟩
    exact ⟨rfl, by simpa only [f.bit_all] using hb⟩
  · rintro ⟨rfl, hb⟩
    exact ⟨rfl, by simpa only [f.bit_all] using hb⟩

 theorem group_add_iff (s t w : Finset M.B) :
    w.map f.base.toEmbedding = s.map f.base.toEmbedding ∆ t.map f.base.toEmbedding ↔
      w = s ∆ t := by
  rw [← FiniteSupports.map_symmDiff]
  exact (Finset.map_injective _).eq_iff

attribute [local simp] Data.rawRel Map.onPoint group_add_iff row_action_iff
  col_action_iff bit_relation_iff

 theorem raw_map_index (xs : List M.Carrier) :
    N.rawRel (.index) (xs.map f.onPoint) ↔ M.rawRel (.index) xs := by
  rcases xs with _ | ⟨x, xs⟩
  · simp
  rcases xs with _ | ⟨q, qs⟩
  · cases x <;> simp
  · cases x <;> simp

 theorem raw_map_base (xs : List M.Carrier) :
    N.rawRel (.base) (xs.map f.onPoint) ↔ M.rawRel (.base) xs := by
  rcases xs with _ | ⟨x, xs⟩
  · simp
  rcases xs with _ | ⟨q, qs⟩
  · cases x <;> simp
  · cases x <;> simp

 theorem raw_map_group (xs : List M.Carrier) :
    N.rawRel (.group) (xs.map f.onPoint) ↔ M.rawRel (.group) xs := by
  rcases xs with _ | ⟨x, xs⟩
  · simp
  rcases xs with _ | ⟨q, qs⟩
  · cases x <;> simp
  · cases x <;> simp

 theorem raw_map_star (xs : List M.Carrier) :
    N.rawRel (.star) (xs.map f.onPoint) ↔ M.rawRel (.star) xs := by
  rcases xs with _ | ⟨x, xs⟩
  · simp
  rcases xs with _ | ⟨q, qs⟩
  · cases x <;> simp
  · cases x <;> simp

 theorem raw_map_row (k n : ℕ) (xs : List M.Carrier) :
    N.rawRel (.row k n) (xs.map f.onPoint) ↔ M.rawRel (.row k n) xs := by
  rcases xs with _ | ⟨x, xs⟩
  · simp
  rcases xs with _ | ⟨q, qs⟩
  · cases x <;> simp
  · cases x <;> simp

 theorem raw_map_col (k : ℕ) (xs : List M.Carrier) :
    N.rawRel (.col k) (xs.map f.onPoint) ↔ M.rawRel (.col k) xs := by
  rcases xs with _ | ⟨x, xs⟩
  · simp
  rcases xs with _ | ⟨q, qs⟩
  · cases x <;> simp
  · cases x <;> simp

 theorem raw_map_label (s : Finset ℕ) (xs : List M.Carrier) :
    N.rawRel (.label s) (xs.map f.onPoint) ↔ M.rawRel (.label s) xs := by
  rcases xs with _ | ⟨x, xs⟩
  · simp
  rcases xs with _ | ⟨q, qs⟩
  · cases x <;> simp
  · cases x <;> simp

 theorem raw_map_order (xs : List M.Carrier) :
    N.rawRel (.order) (xs.map f.onPoint) ↔ M.rawRel (.order) xs := by
  rcases xs with _ | ⟨x, xs⟩
  · simp
  rcases xs with _ | ⟨y, xs⟩
  · cases x <;> simp
  rcases xs with _ | ⟨q, qs⟩
  · cases x <;> cases y <;> simp
  · cases x <;> cases y <;> simp

 theorem raw_map_incidence (xs : List M.Carrier) :
    N.rawRel (.incidence) (xs.map f.onPoint) ↔ M.rawRel (.incidence) xs := by
  rcases xs with _ | ⟨x, xs⟩
  · simp
  rcases xs with _ | ⟨y, xs⟩
  · cases x <;> simp
  rcases xs with _ | ⟨q, qs⟩
  · cases x <;> cases y <;> simp
  · cases x <;> cases y <;> simp

 theorem raw_map_bit (xs : List M.Carrier) :
    N.rawRel (.bit) (xs.map f.onPoint) ↔ M.rawRel (.bit) xs := by
  rcases xs with _ | ⟨x, xs⟩
  · simp
  rcases xs with _ | ⟨y, xs⟩
  · cases x <;> simp
  rcases xs with _ | ⟨q, qs⟩
  · cases x <;> cases y <;> simp
    rintro rfl
    exact f.bit_all _ _ _ _ _
  · cases x <;> cases y <;> simp

 theorem raw_map_groupAdd (xs : List M.Carrier) :
    N.rawRel (.groupAdd) (xs.map f.onPoint) ↔ M.rawRel (.groupAdd) xs := by
  rcases xs with _ | ⟨x, xs⟩
  · simp
  rcases xs with _ | ⟨y, xs⟩
  · cases x <;> simp
  rcases xs with _ | ⟨z, xs⟩
  · cases x <;> cases y <;> simp
  rcases xs with _ | ⟨q, qs⟩
  · cases x <;> cases y <;> cases z <;> simp
  · cases x <;> cases y <;> cases z <;> simp

 theorem raw_map_starAdd (xs : List M.Carrier) :
    N.rawRel (.starAdd) (xs.map f.onPoint) ↔ M.rawRel (.starAdd) xs := by
  rcases xs with _ | ⟨x, xs⟩
  · simp
  rcases xs with _ | ⟨y, xs⟩
  · cases x <;> simp
  rcases xs with _ | ⟨z, xs⟩
  · cases x <;> cases y <;> simp
  rcases xs with _ | ⟨q, qs⟩
  · cases x <;> cases y <;> cases z <;> simp
  · cases x <;> cases y <;> cases z <;> simp

 theorem raw_map_rowAct (xs : List M.Carrier) :
    N.rawRel (.rowAct) (xs.map f.onPoint) ↔ M.rawRel (.rowAct) xs := by
  rcases xs with _ | ⟨x, xs⟩
  · simp
  rcases xs with _ | ⟨y, xs⟩
  · cases x <;> simp
  rcases xs with _ | ⟨z, xs⟩
  · cases x <;> cases y <;> simp
  rcases xs with _ | ⟨q, qs⟩
  · cases x <;> cases y <;> cases z <;> simp
    rintro rfl rfl
    rw [symmDiff_assoc, ← FiniteSupports.map_symmDiff, symmDiff_right_inj]
    exact (Finset.map_injective _).eq_iff
  · cases x <;> cases y <;> cases z <;> simp

 theorem raw_map_colAct (xs : List M.Carrier) :
    N.rawRel (.colAct) (xs.map f.onPoint) ↔ M.rawRel (.colAct) xs := by
  rcases xs with _ | ⟨x, xs⟩
  · simp
  rcases xs with _ | ⟨y, xs⟩
  · cases x <;> simp
  rcases xs with _ | ⟨z, xs⟩
  · cases x <;> cases y <;> simp
  rcases xs with _ | ⟨q, qs⟩
  · cases x <;> cases y <;> cases z <;> simp
    rintro rfl rfl
    rw [symmDiff_assoc, symmDiff_right_inj]
  · cases x <;> cases y <;> cases z <;> simp

 theorem tuple_list_eq_iff (t : Tuple M.I) (xs : List M.Carrier) :
    xs.map f.onPoint = List.ofFn (fun i => Point.index ((Tuples.map f.index t).2 i)) ↔
      xs = List.ofFn (fun i => Point.index (t.2 i)) := by
  have he : List.ofFn (fun i => Point.index ((Tuples.map f.index t).2 i)) =
      (List.ofFn (fun i => Point.index (t.2 i))).map f.onPoint := by
    rw [List.map_ofFn]
    rfl
  rw [he]
  exact f.injective.list_map.eq_iff

 theorem base_point_eq_iff (x : M.Carrier) (b : M.B) :
    f.onPoint x = Point.base (f.base b) ↔ x = Point.base b := by
  change f.onPoint x = f.onPoint (.base b) ↔ _
  exact f.injective.eq_iff

 theorem raw_map_rowProjection (k n : ℕ) (xs : List M.Carrier) :
    N.rawRel (.rowProjection k n) (xs.map f.onPoint) ↔ M.rawRel (.rowProjection k n) xs := by
  rcases xs with _ | ⟨x, xs⟩
  · simp
  cases x <;> simp
  intro _ _
  simpa only [Tuples.map, List.ofFn_succ] using tuple_list_eq_iff f _ xs

 theorem raw_map_colProjection (k : ℕ) (xs : List M.Carrier) :
    N.rawRel (.colProjection k) (xs.map f.onPoint) ↔ M.rawRel (.colProjection k) xs := by
  rcases xs with _ | ⟨x, xs⟩
  · simp
  rcases xs with _ | ⟨y, ys⟩
  · cases x <;> simp
  cases x <;> simp
  intro _
  exact and_congr (base_point_eq_iff f y _) (by
    simpa only [Tuples.map, List.ofFn_succ] using tuple_list_eq_iff f _ ys)

theorem Map.rawRel (s : Symbol) (xs : List M.Carrier) :
    N.rawRel s (xs.map f.onPoint) ↔ M.rawRel s xs := by
  cases s with
  | index => exact raw_map_index f xs
  | base => exact raw_map_base f xs
  | group => exact raw_map_group f xs
  | star => exact raw_map_star f xs
  | row k n => exact raw_map_row f k n xs
  | col k => exact raw_map_col f k xs
  | label v => exact raw_map_label f v xs
  | rowProjection k n => exact raw_map_rowProjection f k n xs
  | colProjection k => exact raw_map_colProjection f k xs
  | order => exact raw_map_order f xs
  | incidence => exact raw_map_incidence f xs
  | bit => exact raw_map_bit f xs
  | groupAdd => exact raw_map_groupAdd f xs
  | starAdd => exact raw_map_starAdd f xs
  | rowAct => exact raw_map_rowAct f xs
  | colAct => exact raw_map_colAct f xs

theorem Map.rel (n : ℕ) (s : Language n) (a : Fin n → M.Carrier) :
    N.rel n s (f.onPoint ∘ a) ↔ M.rel n s a := by
  simpa only [Data.rel, List.map_ofFn] using f.rawRel s.val (List.ofFn a)

end

open Tuples
open scoped symmDiff

variable {M N P : Data.{u}}
local instance instDecidableEqB_5 : DecidableEq M.B := Classical.decEq M.B
local instance instDecidableEqB_6 : DecidableEq N.B := Classical.decEq N.B
local instance instDecidableEqB_7 : DecidableEq P.B := Classical.decEq P.B

def Map.id (M : Data.{u}) : Map M M where
  index := Function.Embedding.refl _
  base := (OrderIso.refl _).toOrderEmbedding
  rowShift _ _ := ∅
  colShift _ _ := ∅
  bit_agrees t n b := by simp [Matrix.bit]

def Map.comp (g : Map N P) (f : Map M N) : Map M P where
  index := f.index.trans g.index
  base := f.base.trans g.base
  rowShift t n := g.rowShift (Tuples.map f.index t) n ∆
    (f.rowShift t n).map g.base.toEmbedding
  colShift t b := g.colShift (Tuples.map f.index t) (f.base b) ∆ f.colShift t b
  bit_agrees t n b := by
    exact (g.bit_all (Tuples.map f.index t) n (f.rowShift t n) (f.base b)
      (f.colShift t b)).trans (f.bit_agrees t n b)

@[simp] theorem Map.id_onPoint (M : Data.{u}) (x : M.Carrier) : (Map.id M).onPoint x = x := by
  have he : (OrderIso.refl M.B).toOrderEmbedding.toEmbedding = Function.Embedding.refl M.B := rfl
  cases x <;> simp [Map.id, Map.onPoint, he]

@[simp] theorem Map.comp_onPoint (g : Map N P) (f : Map M N) (x : M.Carrier) :
    (g.comp f).onPoint x = g.onPoint (f.onPoint x) := by
  have he : (f.base.trans g.base).toEmbedding = f.base.toEmbedding.trans g.base.toEmbedding := rfl
  cases x <;> simp [Map.comp, Map.onPoint, Finset.map_map, symmDiff_assoc, he]

theorem Map.ext_onPoint {f g : Map M N} (h : ∀ x, f.onPoint x = g.onPoint x) : f = g := by
  have hi : f.index = g.index := by
    ext i
    exact Point.index.inj (h (.index i))
  have hb : f.base = g.base := by
    ext b
    exact Point.base.inj (h (.base b))
  have hr : f.rowShift = g.rowShift := by
    funext t n
    have he := (Point.row.inj (h (.row t n ∅))).2.2
    simpa using he
  have hc : f.colShift = g.colShift := by
    funext t b
    have he := (Point.col.inj (h (.col t b ∅))).2.2
    simpa using he
  cases f
  cases g
  cases hi
  cases hb
  cases hr
  cases hc
  rfl

@[simp] theorem Map.comp_id (f : Map M N) : f.comp (Map.id M) = f :=
  Map.ext_onPoint (fun x => by simp)

@[simp] theorem Map.id_comp (f : Map M N) : (Map.id N).comp f = f :=
  Map.ext_onPoint (fun x => by simp)

end Arrays

end CHObstruction

end

end OAI


