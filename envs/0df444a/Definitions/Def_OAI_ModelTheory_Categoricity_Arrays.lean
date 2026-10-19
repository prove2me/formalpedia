-- Prove2me | Definitions.Def_OAI_ModelTheory_Categoricity_Arrays
-- name    : OAI_ModelTheory_Categoricity_Arrays
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T02:37:05.483655+00:00
-- url     : https://prove2.me/theorems/6c0b1be3-d49c-43fd-8a2a-b60e5567b0a6
-- title:
--   Arrays: many-sorted bit structures over a dense base order, their countable signature, and their maps
-- statement:
--   This file defines arrays, the many-sorted relational structures from which the abstract elementary class of the main theorem is built, together with their countable signature and the maps between them. A tuple in a set $I$ is a nonempty finite injective sequence $t = (t_0, \dots, t_k)$ of elements of $I$, of length $k + 1$; for an injection $g : I \hookrightarrow I'$, $g \circ t = (g(t_0), \dots, g(t_k))$. For a statement $P$, $[P] \in \{0, 1\}$ is its truth value, $\oplus$ is addition modulo $2$ (exclusive or) and $s \mathbin{\triangle} s'$ is the symmetric difference of sets.
--
--   1. **Flipped bits.** For a bit matrix $a : \mathbb{N} \times B \to \{0, 1\}$, a row index $n \in \mathbb{N}$, a column index $b \in B$ and finite sets $U \subseteq B$, $V \subseteq \mathbb{N}$,
--   $$
--   \mathrm{bit}_a(n, U, b, V) = a(n, b) \oplus [b \in U] \oplus [n \in V].
--   $$
--   If $B$ is countable, every $d : \mathbb{N} \times B \to \{0, 1\}$ has the form $d(n, b) = [b \in U_n] \oplus [n \in V_b]$ for some finite sets $U_n \subseteq B$ ($n \in \mathbb{N}$) and $V_b \subseteq \mathbb{N}$ ($b \in B$); consequently, for any two matrices $a, a'$ there are such sets with $\mathrm{bit}_{a'}(n, U_n, b, V_b) = a(n, b)$ for all $n$ and $b$.
--
--   2. **Points.** For sets $I$ (indices) and $B$ (base), the carrier $P(I, B)$ is the disjoint union of six sorts: index points $i \in I$; base points $b \in B$; group points, the finite subsets $s \subseteq B$; star points, the finite subsets $v \subseteq \mathbb{N}$; row points $(t, n, s)$ with $t$ a tuple in $I$, $n \in \mathbb{N}$ and $s \subseteq B$ finite; and column points $(t, b, v)$ with $t$ a tuple in $I$, $b \in B$ and $v \subseteq \mathbb{N}$ finite.
--
--   3. **Signature.** The relation symbols are the unary sort symbols $\mathsf{index}, \mathsf{base}, \mathsf{group}, \mathsf{star}$; unary symbols $\mathsf{row}_{k,n}$ and $\mathsf{col}_k$ for $k, n \in \mathbb{N}$; a unary symbol $\mathsf{label}_s$ for each finite $s \subseteq \mathbb{N}$; $\mathsf{rowProj}_{k,n}$ of arity $k + 2$ and $\mathsf{colProj}_k$ of arity $k + 3$; the binary symbols $\mathsf{order}, \mathsf{incidence}, \mathsf{bit}$; and the ternary symbols $\mathsf{groupAdd}, \mathsf{starAdd}, \mathsf{rowAct}, \mathsf{colAct}$. The language $L(n)$ consists of the symbols of arity $n$, and there are countably many symbols in total.
--
--   4. **Array data.** An array $M$ consists of nonempty sets $I$ and $B$, a dense linear order on $B$ without least or greatest element in which every closed interval $[a, b]$ is countable, and a bit assignment $\beta$ giving for each tuple $t$ in $I$ a matrix $\beta_t : \mathbb{N} \times B \to \{0, 1\}$.
--
--   5. **The structure of an array.** On $P(I, B)$ the symbols are interpreted as follows, every combination not listed being false:
--      - each sort symbol holds exactly of the points of its sort; $\mathsf{row}_{k,n}$ holds of the row points $(t, n, s)$ with $t$ of length $k + 1$; $\mathsf{col}_k$ holds of the column points $(t, b, v)$ with $t$ of length $k + 1$; $\mathsf{label}_s$ holds only of the star point $s$;
--      - $\mathsf{rowProj}_{k,n}(x, y_0, \dots, y_k)$ holds iff $x = (t, n, s)$ is a row point with $t$ of length $k + 1$ and $y_i = t_i$ for all $i$; $\mathsf{colProj}_k(x, y, y_0, \dots, y_k)$ holds iff $x = (t, b, v)$ is a column point with $t$ of length $k + 1$, $y = b$ and $y_i = t_i$ for all $i$;
--      - $\mathsf{order}(b, b')$ holds iff $b < b'$ for base points $b, b'$; $\mathsf{incidence}(b, s)$ holds iff $b \in s$ for a base point $b$ and a group point $s$;
--      - $\mathsf{bit}(x, y)$ holds iff $x = (t, n, s)$ and $y = (t, b, v)$ are a row point and a column point of the same tuple and $\mathrm{bit}_{\beta_t}(n, s, b, v) = 1$;
--      - $\mathsf{groupAdd}(s, s', s'')$ holds iff $s'' = s \mathbin{\triangle} s'$ for group points, and likewise $\mathsf{starAdd}$ for star points;
--      - $\mathsf{rowAct}(x, u, x')$ holds iff $x = (t, n, s)$ is a row point, $u$ is a group point and $x' = (t, n, s \mathbin{\triangle} u)$; $\mathsf{colAct}(y, w, y')$ holds iff $y = (t, b, v)$ is a column point, $w$ is a star point and $y' = (t, b, v \mathbin{\triangle} w)$.
--
--   6. **Colors and objects.** The color of a tuple $t$ at a base point $b$ is the class of the column sequence $n \mapsto \beta_t(n, b)$ modulo finite change, an element of the palette of binary sequences modulo finite change. Assuming CH, i.e. $2^{\aleph_0} = \aleph_1$, the array $M$ is an object if for every tuple $t$ in $I$
--   $$
--   \{\, b \in B : t \text{ fails the diagram test for the coloring } t' \mapsto \mathrm{color}(t', b) \,\} \text{ is countable}.
--   $$
--   Here a tuple $t$ of length $n + 1$ passes the diagram test for a coloring $c$ of tuples if some diagram $d$ on $\{0, \dots, n\}$ has, for every $m$ and every strictly increasing $e : \{0, \dots, m\} \to \{0, \dots, n\}$, a valid restriction $d|_e$ with $\mathrm{code}(m, d|_e) = c(t \circ e)$, where $\mathrm{code}$ is the fixed injection of finite diagrams into the palette available under CH.
--
--   7. **Maps of arrays.** A map $f : M \to N$ consists of an injection $f_I : I_M \hookrightarrow I_N$, an order embedding $f_B : B_M \to B_N$, finite row shifts $R(t, n) \subseteq B_N$ and finite column shifts $C(t, b) \subseteq \mathbb{N}$, for tuples $t$ in $I_M$, $n \in \mathbb{N}$ and $b \in B_M$, such that
--   $$
--   \mathrm{bit}_{\beta^N_{f_I \circ t}}\bigl(n, R(t, n), f_B(b), C(t, b)\bigr) = \beta^M_t(n, b) \qquad \text{for all } t, n, b.
--   $$
--   It acts on points by $i \mapsto f_I(i)$, $b \mapsto f_B(b)$, $s \mapsto f_B[s]$ on group points, $v \mapsto v$ on star points, $(t, n, s) \mapsto (f_I \circ t, n, R(t, n) \mathbin{\triangle} f_B[s])$ on row points and $(t, b, v) \mapsto (f_I \circ t, f_B(b), C(t, b) \mathbin{\triangle} v)$ on column points. This point map is injective and preserves flipped bits:
--   $$
--   \mathrm{bit}_{\beta^N_{f_I \circ t}}\bigl(n, R(t, n) \mathbin{\triangle} f_B[s], f_B(b), C(t, b) \mathbin{\triangle} v\bigr) = \mathrm{bit}_{\beta^M_t}(n, s, b, v).
--   $$
--
--   The file also records basic facts on tuples (pushing forward along an injection is injective, functorial and commutes with taking subtuples) and on symmetric differences: $g[s \mathbin{\triangle} s'] = g[s] \mathbin{\triangle} g[s']$ for injective $g$, $[b \in s \mathbin{\triangle} s'] = [b \in s] \oplus [b \in s']$ and $[g(b) \in g[s]] = [b \in s]$.
--
--   The class of the main theorem consists of the relational structures, with carriers that are ZF sets, admitting a presentation as an array that is an object, and maps of arrays underlie its strong-substructure relation. Row and column shifts let a map absorb finitely supported changes of bits; by the decomposition in item 1, over a countable base any two bit matrices differ only by such changes.
--
--   **Formalization Note** `Matrix.bit`, `decompose` and `normalize` form item 1. `Point I B` is an inductive type with constructors `index`, `base`, `group`, `star`, `row`, `col`; `Symbol` is an inductive type with decidable equality and an `Encodable` instance, `Symbol.arity` gives the arities and `Language n` is the subtype of symbols of arity `n`, with `language_countable` the countability of the total signature. `Data` is a structure with fields `I`, `B`, `indexNonempty`, `baseNonempty`, `order`, `dense`, `noMin`, `noMax`, `locallyCountable`, `bits`; `Data.rawRel` interprets a symbol on a list of points and `Data.rel` on a tuple `Fin n → Carrier`. `Data.colors` and `Data.IsObject` are item 6 (the latter takes the proof of CH). `Tuples.map` and the lemmas in `FiniteSupports` are plumbing. `Map` is a structure with fields `index`, `base`, `rowShift`, `colShift`, `bit_agrees`; `Map.onPoint`, `Map.injective`, `Map.toEmbedding` and `Map.bit_all` are item 7. Decidable equality on the base is supplied classically.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/ModelTheory/Categoricity/Arrays.lean

-- Generated from openai/math@1581d4c lean/OAI/ModelTheory/Categoricity/Arrays.lean by skeleton subtraction
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

namespace OAI

universe u v w

noncomputable section

namespace CHObstruction

open Cardinal Ordinal Order

namespace Matrix

open scoped symmDiff

variable {B : Type u}

local instance instDecidableEq_oAI : DecidableEq B := Classical.decEq B

def bit (a : ℕ → B → Bool) (n : ℕ) (u : Finset B) (b : B) (v : Finset ℕ) : Bool :=
  a n b ^^ decide (b ∈ u) ^^ decide (n ∈ v)

theorem decompose [Countable B] (d : ℕ → B → Bool) :
    ∃ (U : ℕ → Finset B) (V : B → Finset ℕ),
      ∀ n b, (decide (b ∈ U n) ^^ decide (n ∈ V b)) = d n b := by
  classical
  obtain ⟨e⟩ := nonempty_encodable B
  let ix : B → ℕ := Encodable.encode
  have hi : Function.Injective ix := Encodable.encode_injective
  let U : ℕ → Finset B := fun n =>
    ((Finset.range (n + 1)).preimage ix (hi.injOn)).filter (fun b => d n b)
  let V : B → Finset ℕ := fun b => (Finset.range (ix b)).filter (fun n => d n b)
  refine ⟨U, V, ?_⟩
  intro n b
  simp only [U, V, Finset.mem_filter, Finset.mem_preimage, Finset.mem_range]
  by_cases h : ix b ≤ n
  · have hn : ¬ n < ix b := not_lt_of_ge h
    simp only [Nat.lt_succ_iff, h, hn, true_and, false_and, decide_false, Bool.xor_false,
      Bool.decide_coe]
  · have hn : n < ix b := lt_of_not_ge h
    simp only [Nat.lt_succ_iff, h, hn, true_and, false_and, decide_false, Bool.false_xor,
      Bool.decide_coe]

theorem normalize [Countable B] (a a' : ℕ → B → Bool) :
    ∃ (U : ℕ → Finset B) (V : B → Finset ℕ),
      ∀ n b, bit a' n (U n) b (V b) = a n b := by
  obtain ⟨U, V, h⟩ := decompose (fun n b => a n b ^^ a' n b)
  refine ⟨U, V, ?_⟩
  intro n b
  rw [bit, Bool.xor_assoc, h]
  cases a n b <;> cases a' n b <;> rfl

end Matrix

namespace Arrays

open Tuples
open scoped symmDiff

inductive Point (I B : Type u) : Type u
  | index : I → Point I B
  | base : B → Point I B
  | group : Finset B → Point I B
  | star : Finset ℕ → Point I B
  | row : Tuple I → ℕ → Finset B → Point I B
  | col : Tuple I → B → Finset ℕ → Point I B

inductive Symbol : Type
  | index | base | group | star
  | row (k n : ℕ) | col (k : ℕ) | label (s : Finset ℕ)
  | rowProjection (k n : ℕ) | colProjection (k : ℕ)
  | order | incidence | bit
  | groupAdd | starAdd | rowAct | colAct
  deriving DecidableEq, Encodable

def Symbol.arity : Symbol → ℕ
  | .index | .base | .group | .star | .row _ _ | .col _ | .label _ => 1
  | .rowProjection k _ => k + 2
  | .colProjection k => k + 3
  | .order | .incidence | .bit => 2
  | .groupAdd | .starAdd | .rowAct | .colAct => 3

def Language (n : ℕ) := {s : Symbol // s.arity = n}

instance language_countable : Countable (Σ n, Language n) := by
  have hi : Function.Injective (fun x : Σ n, Language n => x.2.val) := by
    rintro ⟨n, s, hs⟩ ⟨m, r, hr⟩ h
    dsimp at h
    subst r
    cases hs
    cases hr
    rfl
  exact hi.countable

structure Data where
  I : Type u
  B : Type u
  indexNonempty : Nonempty I
  baseNonempty : Nonempty B
  order : LinearOrder B
  dense : @DenselyOrdered B order.toLT
  noMin : @NoMinOrder B order.toLT
  noMax : @NoMaxOrder B order.toLT
  locallyCountable : ∀ a b : B, (@Set.Icc B order.toPreorder a b).Countable
  bits : Tuple I → ℕ → B → Bool

attribute [instance] Data.indexNonempty Data.baseNonempty Data.order Data.dense Data.noMin Data.noMax

abbrev Data.Carrier (M : Data.{u}) := Point M.I M.B

variable (M : Data.{u})

local instance instDecidableEqB : DecidableEq M.B := Classical.decEq M.B

def Data.rawRel : Symbol → List M.Carrier → Prop
  | .index, [.index _] => True
  | .base, [.base _] => True
  | .group, [.group _] => True
  | .star, [.star _] => True
  | .row k n, [.row t m _] => t.1 = k ∧ m = n
  | .col k, [.col t _ _] => t.1 = k
  | .label s, [.star t] => s = t
  | .rowProjection k n, (.row t m _) :: xs =>
      t.1 = k ∧ m = n ∧ xs = List.ofFn (fun i => Point.index (t.2 i))
  | .colProjection k, (.col t b _) :: x :: xs =>
      t.1 = k ∧ x = .base b ∧ xs = List.ofFn (fun i => Point.index (t.2 i))
  | .order, [.base a, .base b] => a < b
  | .incidence, [.base b, .group s] => b ∈ s
  | .bit, [.row t n s, .col t' b v] => t = t' ∧ Matrix.bit (M.bits t) n s b v = true
  | .groupAdd, [.group s, .group t, .group w] => w = s ∆ t
  | .starAdd, [.star s, .star t, .star w] => w = s ∆ t
  | .rowAct, [.row t n s, .group u, .row t' n' s'] => t' = t ∧ n' = n ∧ s' = s ∆ u
  | .colAct, [.col t b v, .star u, .col t' b' v'] => t' = t ∧ b' = b ∧ v' = v ∆ u
  | _, _ => False

def Data.rel (n : ℕ) (s : Language n) (a : Fin n → M.Carrier) : Prop :=
  M.rawRel s.val (List.ofFn a)

def Data.colors (t : Tuple M.I) (b : M.B) : Colors.Palette.{u} :=
  ⟨Colors.color (fun n => M.bits t n b)⟩

def Data.IsObject (hCH : CH.{u}) : Prop :=
  ∀ t : Tuple M.I, {b | ¬ Tests.Test hCH (fun t => M.colors t b) t}.Countable

end Arrays

namespace Tuples

variable {I J K : Type u}

def map (f : I ↪ J) (t : Tuple I) : Tuple J := ⟨t.1, t.2.trans f⟩

@[simp] theorem map_fst (f : I ↪ J) (t : Tuple I) : (map f t).1 = t.1 := rfl

theorem map_injective (f : I ↪ J) : Function.Injective (map f) := by
  rintro ⟨n, t⟩ ⟨m, s⟩ heq
  have hn : n = m := congrArg Sigma.fst heq
  subst m
  have he : t.trans f = s.trans f := (Sigma.mk.inj heq).2 |> eq_of_heq
  congr 1
  ext i
  exact f.injective (congrArg (fun g : Fin (n + 1) ↪ J => g i) he)

@[simp] theorem map_refl (t : Tuple I) : map (Function.Embedding.refl I) t = t := by
  cases t
  rfl

@[simp] theorem map_comp (f : I ↪ J) (g : J ↪ K) (t : Tuple I) :
    map g (map f t) = map (f.trans g) t := rfl

@[simp] theorem map_sub (f : I ↪ J) (t : Tuple I) {m : ℕ}
    (e : Fin (m + 1) ↪o Fin (t.1 + 1)) : map f (sub t e) = sub (map f t) e := rfl

end Tuples

namespace FiniteSupports

open scoped symmDiff

variable {A : Type u} {B : Type v} [DecidableEq A] [DecidableEq B]

@[simp] theorem map_symmDiff (f : A ↪ B) (s t : Finset A) :
    (s ∆ t).map f = s.map f ∆ t.map f := by
  ext b
  by_cases hb : ∃ a, f a = b
  · obtain ⟨a, rfl⟩ := hb
    simp only [Finset.mem_map, Function.Embedding.apply_eq_iff_eq, exists_eq_right,
      Finset.mem_symmDiff]
  · have hn : ∀ s : Finset A, b ∉ s.map f := by
      intro s hs
      obtain ⟨a, _, ha⟩ := Finset.mem_map.1 hs
      exact hb ⟨a, ha⟩
    simp only [hn, Finset.mem_symmDiff, not_false_eq_true, false_and, or_self]

@[simp] theorem bit_symmDiff (b : A) (s t : Finset A) :
    decide (b ∈ s ∆ t) = (decide (b ∈ s) ^^ decide (b ∈ t)) := by
  simp only [Finset.mem_symmDiff]
  by_cases hs : b ∈ s <;> by_cases ht : b ∈ t <;> simp [hs, ht]

@[simp] theorem bit_map (f : A ↪ B) (b : A) (s : Finset A) :
    decide (f b ∈ s.map f) = decide (b ∈ s) := by
  simp

end FiniteSupports

namespace Arrays

open Tuples
open scoped symmDiff

variable {M N : Data.{u}}
local instance instDecidableEqB_1 : DecidableEq M.B := Classical.decEq M.B
local instance instDecidableEqB_2 : DecidableEq N.B := Classical.decEq N.B

structure Map (M N : Data.{u}) where
  index : M.I ↪ N.I
  base : M.B ↪o N.B
  rowShift : Tuple M.I → ℕ → Finset N.B
  colShift : Tuple M.I → M.B → Finset ℕ
  bit_agrees : ∀ t n b, Matrix.bit (N.bits (Tuples.map index t)) n (rowShift t n)
    (base b) (colShift t b) = M.bits t n b

def Map.onPoint (f : Map M N) : M.Carrier → N.Carrier
  | .index i => .index (f.index i)
  | .base b => .base (f.base b)
  | .group s => .group (s.map f.base.toEmbedding)
  | .star v => .star v
  | .row t n s => .row (Tuples.map f.index t) n (f.rowShift t n ∆ s.map f.base.toEmbedding)
  | .col t b v => .col (Tuples.map f.index t) (f.base b) (f.colShift t b ∆ v)

theorem Map.injective (f : Map M N) : Function.Injective f.onPoint := by
  intro x y h
  cases x <;> cases y <;> simp only [Map.onPoint, Point.index.injEq, Point.base.injEq,
    Point.group.injEq, Point.star.injEq, Point.row.injEq, Point.col.injEq,
    reduceCtorEq] at h ⊢
  · exact f.index.injective h
  · exact f.base.injective h
  · exact Finset.map_injective _ h
  · exact h
  · obtain ⟨ht, hn, hs⟩ := h
    have ht' := Tuples.map_injective f.index ht
    subst_vars
    exact ⟨rfl, rfl, Finset.map_injective _ (symmDiff_right_inj.1 hs)⟩
  · obtain ⟨ht, hb, hv⟩ := h
    have ht' := Tuples.map_injective f.index ht
    have hb' := f.base.injective hb
    subst_vars
    exact ⟨rfl, rfl, symmDiff_right_inj.1 hv⟩

def Map.toEmbedding (f : Map M N) : M.Carrier ↪ N.Carrier :=
  ⟨f.onPoint, f.injective⟩

@[simp] theorem Map.base_embedding_apply (f : Map M N) (b : M.B) :
    f.base.toEmbedding b = f.base b := rfl

theorem Map.bit_all (f : Map M N) (t : Tuple M.I) (n : ℕ) (s : Finset M.B)
    (b : M.B) (v : Finset ℕ) :
    Matrix.bit (N.bits (Tuples.map f.index t)) n
      (f.rowShift t n ∆ s.map f.base.toEmbedding) (f.base b) (f.colShift t b ∆ v) =
      Matrix.bit (M.bits t) n s b v := by
  have hb := f.bit_agrees t n b
  simp only [Matrix.bit, FiniteSupports.bit_symmDiff, Finset.mem_map,
    Map.base_embedding_apply, f.base.injective.eq_iff, exists_eq_right] at *
  rw [← hb]
  generalize N.bits (Tuples.map f.index t) n (f.base b) = a
  generalize decide (f.base b ∈ f.rowShift t n) = c
  generalize decide (b ∈ s) = d
  generalize decide (n ∈ f.colShift t b) = e
  generalize decide (n ∈ v) = g
  cases a <;> cases c <;> cases d <;> cases e <;> cases g <;> rfl

end Arrays

namespace Tuples

@[simp] theorem map_eq_iff {I J : Type u} (f : I ↪ J) (s t : Tuple I) :
    map f s = map f t ↔ s = t := (map_injective f).eq_iff

end Tuples

end CHObstruction

end

end OAI


