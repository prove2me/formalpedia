-- Prove2me | Definitions.Def_OAI_ModelTheory_Categoricity_Subarrays
-- name    : OAI_ModelTheory_Categoricity_Subarrays
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T02:45:38.237784+00:00
-- url     : https://prove2.me/theorems/cfcf852c-fb90-433a-8e01-149f7745c611
-- title:
--   Subarrays: restricting array data to an index subset and a dense base suborder
-- statement:
--   This file constructs *subarrays*: the restriction of an array datum to a subset of its index set and a suitable suborder of its base, together with the inclusion map into the original datum.
--
--   **Setting.** A *tuple* over a set $I$ is a nonempty finite injective sequence $t=(t_0,\dots,t_k)$ of elements of $I$; for an injection $g\colon I\to I'$ write $g t=(g(t_0),\dots,g(t_k))$. For a statement $P$ let $[P]\in\{0,1\}$ be $1$ if $P$ holds and $0$ otherwise. An *array datum* $M$ consists of a nonempty index set $I_M$, a nonempty dense linear order $B_M$ without endpoints (the *base*) in which every closed interval $[a,b]$ is countable, and bits $a^M_t(n,b)\in\{0,1\}$ for all tuples $t$ over $I_M$, levels $n\in\mathbb{N}$ and base elements $b\in B_M$. The universe $|M|$ of the structure attached to $M$ is the disjoint union of index points $i\in I_M$, base points $b\in B_M$, group points $\langle s\rangle$ and star points $\langle v\rangle_*$ (for finite $s\subseteq B_M$ and finite $v\subseteq\mathbb{N}$), row points $(t,n,s)$ and column points $(t,b,v)$, where $t$ is a tuple over $I_M$, $n\in\mathbb{N}$ and $b\in B_M$. The bit relation holds between a row point $(t,n,s)$ and a column point $(t',b,v)$ if and only if $t=t'$ and $a^M_t(n,b)+[b\in s]+[n\in v]\equiv 1\pmod 2$.
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
--   Let $\mathcal{C}=\{0,1\}^{\mathbb{N}}/{=^*}$, where $x=^*y$ means that the sequences $x$ and $y$ differ at only finitely many $n$, and write $[x]_*\in\mathcal{C}$ for the class of $x$. The *color* of an array datum $M$ at a tuple $t$ over $I_M$ and $b\in B_M$ is $c^M_t(b)=[\,n\mapsto a^M_t(n,b)\,]_*$, the class of the bit sequence read off at the origin points $(t,n,\emptyset)$ and $(t,b,\emptyset)$. For an array map $f\colon M\to N$, a tuple $t$ over $I_M$ and $b\in B_N$, the *color along $f$* is $c^f_t(b)=\bigl[\,n\mapsto a^N_{f_I t}(n,b)+[b\in\rho^f_{t,n}]\bmod 2\,\bigr]_*$, the color read off in $N$ at the column point $(f_I t,b,\emptyset)$ against the images $\hat f(t,n,\emptyset)$ of the origin rows of $M$.
--
--   Let $M$ be an array datum, $J\subseteq I_M$ a nonempty set, and $S\subseteq B_M$ a nonempty set which, with the order induced from $B_M$, is dense and has neither a least nor a greatest element. The file defines:
--
--   1. **Restriction.** The array datum $M|_{J,S}$ with index set $J$, base $S$ (with the induced order) and bits
--   $$
--   a^{M|_{J,S}}_t(n,b)=a^M_t(n,b)\qquad(t\text{ a tuple over }J,\ n\in\mathbb{N},\ b\in S),
--   $$
--   where on the right $t$ is regarded as a tuple over $I_M$. Every closed interval of $S$ lies in a closed interval of $B_M$ and is therefore countable, so $M|_{J,S}$ is again an array datum.
--
--   2. **Inclusion map.** The array map $\iota_{J,S}\colon M|_{J,S}\to M$ whose index and base parts are the inclusions $J\subseteq I_M$ and $S\subseteq B_M$ and whose row and column shifts are all empty; the compatibility condition holds because the bits are inherited. On points it keeps all coordinates, for instance $\hat\iota_{J,S}(t,n,s)=(t,n,s)$ and $\hat\iota_{J,S}(t,b,v)=(t,b,v)$.
--
--   3. **Colors along the inclusion.** For every tuple $t$ over $J$ and every $b\in B_M$, whether or not $b\in S$,
--   $$
--   c^{\iota_{J,S}}_t(b)=c^M_t(b).
--   $$
--
--   No convexity of $S$ is required in the definition. Subarrays provide the small strong substructures in the downward Löwenheim–Skolem argument for the class: given a set of points of $M$, one restricts to a small index set and a small dense suborder of the base containing everything these points mention. The identity in item 3 shows that the colors entering the strong-map condition for the inclusion, at base points outside $S$, are just the colors of $M$, so that condition can be checked inside $M$.
--
--   **Formalization Note** `Data.restrict M J S` takes `J : Set M.I` and `S : Set M.B` together with instances `Nonempty J`, `Nonempty S`, `DenselyOrdered S`, `NoMinOrder S` and `NoMaxOrder S`; tuples over `J` are pushed to tuples over `M.I` along the subtype embedding. `Data.restrictMap` is $\iota_{J,S}$ and `Data.restrictMap_colors` is item 3, with colors valued in `Colors.Palette`, a universe-lifted copy of $\mathcal{C}$. Bits are Booleans and the sum modulo $2$ is exclusive or. An empty variable section `BaseOrders` declares nothing, and decidable equality is supplied classically.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/ModelTheory/Categoricity/Subarrays.lean

-- Generated from openai/math@1581d4c lean/OAI/ModelTheory/Categoricity/Subarrays.lean by skeleton subtraction
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

namespace OAI

universe u v w

noncomputable section

namespace CHObstruction

open Cardinal Ordinal Order

namespace BaseOrders

variable {B : Type u} [LinearOrder B] [DenselyOrdered B] [NoMinOrder B]
  [NoMaxOrder B] [Nonempty B]

end BaseOrders

namespace Arrays

open Tuples
open scoped symmDiff

variable (M : Data.{u})

def Data.restrict (J : Set M.I) (S : Set M.B) [Nonempty J] [Nonempty S]
    [DenselyOrdered S] [NoMinOrder S] [NoMaxOrder S] : Data.{u} where
  I := J
  B := S
  indexNonempty := inferInstance
  baseNonempty := inferInstance
  order := inferInstance
  dense := inferInstance
  noMin := inferInstance
  noMax := inferInstance
  locallyCountable a b := (M.locallyCountable a b).preimage Subtype.val_injective
  bits t n b := M.bits (Tuples.map (Function.Embedding.subtype J) t) n b

variable {M}
variable (J : Set M.I) (S : Set M.B) [Nonempty J] [Nonempty S]
  [DenselyOrdered S] [NoMinOrder S] [NoMaxOrder S]

local instance instDecidableEqB_15 : DecidableEq M.B := Classical.decEq M.B
local instance instDecidableEqElemB : DecidableEq S := Classical.decEq S

def Data.restrictMap : Map (M.restrict J S) M where
  index := Function.Embedding.subtype J
  base := OrderEmbedding.subtype S
  rowShift _ _ := ∅
  colShift _ _ := ∅
  bit_agrees _ _ _ := by simp only [Matrix.bit, Finset.notMem_empty, decide_false, Bool.xor_false]; rfl

@[simp] theorem Data.restrictMap_colors (t : Tuple J) (b : M.B) :
    (M.restrictMap J S).colors t b = M.colors (Tuples.map (Function.Embedding.subtype J) t) b := by
  simp only [Map.colors, Data.restrictMap, Finset.notMem_empty, decide_false, Bool.xor_false,
    Data.colors]
  rfl

end Arrays

end CHObstruction

end

end OAI


