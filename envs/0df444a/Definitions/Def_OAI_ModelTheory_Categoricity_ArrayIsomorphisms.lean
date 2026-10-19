-- Prove2me | Definitions.Def_OAI_ModelTheory_Categoricity_ArrayIsomorphisms
-- name    : OAI_ModelTheory_Categoricity_ArrayIsomorphisms
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T02:48:20.355674+00:00
-- url     : https://prove2.me/theorems/904f3839-d950-4945-85ee-7e768656cec6
-- title:
--   Isomorphisms of array structures as array maps, and index and base supports of points
-- statement:
--   This file shows that isomorphisms between the structures attached to array data are induced by array maps, and defines the index and base supports of points.
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
--   The file defines:
--
--   1. **Raw isomorphisms.** A raw isomorphism $\phi\colon M\to N$ is a bijection $\phi\colon|M|\to|N|$ such that for every relation symbol $R$ and every finite list $\bar x$ of points of $M$
--   $$
--   N\models R(\phi\bar x)\iff M\models R(\bar x),
--   $$
--   that is, an isomorphism of the attached structures. Every base point of $N$ is then the image of a base point of $M$; consequently $\phi$ preserves supports: for every finite $s\subseteq B_M$ and every $b\in B_N$, the base point $b$ is incident to $\phi\langle s\rangle$ if and only if $\phi(a)=b$ for some $a\in s$. Thus $\phi$ is a *raw embedding* (an injective, relation-preserving and relation-reflecting, support-preserving map of points), and it is converted into an array map $f_\phi\colon M\to N$ with $\hat f_\phi=\phi$: the index and base parts of $f_\phi$ are the maps $\phi_I$, $\phi_B$ induced by $\phi$ on index and base points, and its shifts are read off from $\phi(t,n,\emptyset)=(\phi_I t,n,\rho_{t,n})$ and $\phi(t,b,\emptyset)=(\phi_I t,\phi_B b,\gamma_{t,b})$.
--
--   2. **Index support.** The finite set $\operatorname{supp}_I(x)\subseteq I_M$ of index elements mentioned by a point $x$: $\operatorname{supp}_I(i)=\{i\}$, $\operatorname{supp}_I(t,n,s)=\operatorname{supp}_I(t,b,v)=\{t_0,\dots,t_k\}$ for $t=(t_0,\dots,t_k)$, and $\operatorname{supp}_I(x)=\emptyset$ for base, group and star points.
--
--   3. **Base support.** The finite set $\operatorname{supp}_B(x)\subseteq B_M$ of base elements mentioned by $x$: $\operatorname{supp}_B(b)=\operatorname{supp}_B(t,b,v)=\{b\}$, $\operatorname{supp}_B\langle s\rangle=\operatorname{supp}_B(t,n,s)=s$, and $\operatorname{supp}_B(x)=\emptyset$ for index and star points.
--
--   Raw isomorphisms arise when one abstract structure is presented by two array data; item 1 turns the comparison of the two presentations into an array map, which makes statements about array maps independent of the chosen presentation. The supports record the finitely many indices and base elements a point depends on: a point whose index support lies in a set $J\subseteq I_M$ and whose base support lies in a suitable suborder $S\subseteq B_M$ lies in the image of the inclusion of the subarray with index set $J$, base $S$ and inherited bits, and this is used to build small strong substructures for the downward Löwenheim–Skolem property.
--
--   **Formalization Note** `RawIso M N` has fields `toEquiv` (a bijection of carriers) and `relates` (for raw relation symbols on lists of points of any length). `RawIso.base_surjective_point`, `RawIso.toRawEmbedding`, `RawIso.toMap` and `RawIso.toMap_onPoint` give item 1, reusing the construction `RawEmbedding.toMap`. `Point.indexSupport` and `Point.baseSupport` are `Finset`-valued; the index support of a row or column point is the image of its tuple's injection. Bits are Booleans and the sum modulo $2$ is exclusive or. An empty namespace `CardinalTools` declares nothing, and decidable equality is supplied classically.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/ModelTheory/Categoricity/ArrayIsomorphisms.lean

-- Generated from openai/math@1581d4c lean/OAI/ModelTheory/Categoricity/ArrayIsomorphisms.lean by skeleton subtraction
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
import Definitions.Def_OAI_ModelTheory_Categoricity_ArrayEmbeddings
import Definitions.Def_OAI_ModelTheory_Categoricity_Subarrays

namespace OAI

universe u v w

noncomputable section

namespace CHObstruction

open Cardinal Ordinal Order

namespace Arrays

open Tuples
open scoped symmDiff

variable {M N P : Data.{u}}
local instance instDecidableEqB_16 : DecidableEq M.B := Classical.decEq M.B
local instance instDecidableEqB_17 : DecidableEq N.B := Classical.decEq N.B
local instance instDecidableEqB_18 : DecidableEq P.B := Classical.decEq P.B

structure RawIso (M N : Data.{u}) where
  toEquiv : M.Carrier ≃ N.Carrier
  relates : ∀ s xs, N.rawRel s (xs.map toEquiv) ↔ M.rawRel s xs

variable (e : RawIso M N)

theorem RawIso.base_surjective_point (b : N.B) : ∃ a, e.toEquiv (.base a) = .base b := by
  obtain ⟨x, hx⟩ := e.toEquiv.surjective (.base b)
  have h := (e.relates .base [x]).1 (by simp only [List.map_cons, List.map_nil, hx, Data.rawRel])
  cases x <;> simp only [Data.rawRel] at h
  case base a => exact ⟨a, hx⟩

def RawIso.toRawEmbedding : RawEmbedding M N where
  toEmbedding := e.toEquiv.toEmbedding
  relates := e.relates
  supports s b := by
    obtain ⟨a, ha⟩ := e.base_surjective_point b
    have hr := e.relates .incidence [.base a, .group s]
    simp only [List.map_cons, List.map_nil, ha] at hr
    change N.rawRel .incidence [.base b, e.toEquiv (.group s)] ↔ a ∈ s at hr
    change N.rawRel .incidence [.base b, e.toEquiv (.group s)] ↔ _
    rw [hr]
    constructor
    · intro h; exact ⟨a, h, ha⟩
    · rintro ⟨c, hc, he⟩
      have hca : c = a := Point.base.inj (e.toEquiv.injective (he.trans ha.symm))
      exact hca ▸ hc

def RawIso.toMap : Map M N := e.toRawEmbedding.toMap

theorem RawIso.toMap_onPoint (x : M.Carrier) : e.toMap.onPoint x = e.toEquiv x :=
  e.toRawEmbedding.toMap_onPoint x

end Arrays

namespace CardinalTools

end CardinalTools

namespace Arrays

open Tuples
open scoped symmDiff

variable {M : Data.{u}}
local instance instDecidableEqI : DecidableEq M.I := Classical.decEq M.I
local instance instDecidableEqB_19 : DecidableEq M.B := Classical.decEq M.B

def Point.indexSupport : M.Carrier → Finset M.I
  | .index i => {i}
  | .row t _ _ | .col t _ _ => (Finset.univ.map t.2)
  | _ => ∅

def Point.baseSupport : M.Carrier → Finset M.B
  | .base b | .col _ b _ => {b}
  | .group s | .row _ _ s => s
  | _ => ∅

end Arrays

end CHObstruction

end

end OAI


