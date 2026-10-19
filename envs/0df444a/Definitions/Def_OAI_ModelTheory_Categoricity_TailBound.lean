-- Prove2me | Definitions.Def_OAI_ModelTheory_Categoricity_TailBound
-- name    : OAI_ModelTheory_Categoricity_TailBound
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T02:35:32.240329+00:00
-- url     : https://prove2.me/theorems/db76557e-39fb-46d0-9257-01da220d4f51
-- title:
--   Increasing enumerations of finite sets and set colorings induced by tuple colorings
-- statement:
--   This short file converts colorings of tuples into colorings of finite sets. Let $I$ be a linearly ordered set. A tuple in $I$ is a nonempty finite injective sequence $t = (t_0, \dots, t_n)$ of elements of $I$, i.e. an injection $\{0, \dots, n\} \hookrightarrow I$.
--
--   1. **Sorted tuple of a finite set.** For a finite $s \subseteq I$ with $|s| = n + 1$, $\mathrm{sorted}(s)$ is the tuple listing $s$ in increasing order, $(s_0, s_1, \dots, s_n)$ with $s_0 < s_1 < \dots < s_n$.
--
--   2. **Support.** The support of a tuple $t = (t_0, \dots, t_n)$ is $\operatorname{supp}(t) = \{ t_0, \dots, t_n \}$. It has exactly $n + 1$ elements (this holds for tuples in any set, ordered or not), and $\operatorname{supp}(\mathrm{sorted}(s)) = s$.
--
--   3. **Induced set coloring.** For a coloring $c$ of the tuples in $I$ with values in a set $C$ and a default color $p_0 \in C$, the induced coloring of the finite subsets of $I$ is
--   $$
--   \hat c(s) = \begin{cases} c(\mathrm{sorted}(s)) & \text{if } s \neq \emptyset, \\ p_0 & \text{if } s = \emptyset. \end{cases}
--   $$
--
--   These conversions let partition theorems for finite sets be applied to colorings of tuples. In the tail bound of the main construction, a tuple coloring whose values are functions from a base set $B$ (uncountable, of cardinality at most $\aleph_1$) to palette colors is turned into the set coloring $\hat c$; the partition calculus then yields finite sets of every size on which $\hat c$ depends only on the size, and since every subtuple of a sorted tuple is the sorted tuple of its support, the colors of its subtuples depend only on their length. This is how one shows that if, for every tuple, all but countably many base points pass the diagram tests, then the index set has cardinality below the tail threshold $\beth_{(2^{\aleph_1})^+}$.
--
--   **Formalization Note** `sorted` is built from `Finset.orderEmbOfFin`, `support` is the image of `Finset.univ` under the tuple's embedding, `support_card` and `support_sorted` are simp lemmas, and `setColor` branches on whether the cardinality of `s` is nonzero. The namespaces `TailBound` and `BaseOrders` are opened here without new definitions; their results (the bound on index sets and the cardinality bound for locally countable orders) are separate theorems.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/ModelTheory/Categoricity/TailBound.lean

-- Generated from openai/math@1581d4c lean/OAI/ModelTheory/Categoricity/TailBound.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u v w

noncomputable section

namespace CHObstruction

open Cardinal Ordinal Order

namespace TuplePatterns

open Tuples

variable {I : Type u} [LinearOrder I]

def sorted (s : Finset I) {n : ℕ} (hs : s.card = n + 1) : Tuple I :=
  ⟨n, (s.orderEmbOfFin hs).toEmbedding⟩

def support (t : Tuple I) : Finset I := Finset.univ.map t.2

omit [LinearOrder I] in
@[simp] theorem support_card (t : Tuple I) : (support t).card = t.1 + 1 := by
  simp only [support, Finset.card_map, Finset.card_univ, Fintype.card_fin]

@[simp] theorem support_sorted (s : Finset I) {n : ℕ} (hs : s.card = n + 1) :
    support (sorted s hs) = s := Finset.map_orderEmbOfFin_univ s hs

variable {C : Type u}

def setColor (c : Tuple I → C) (p0 : C) (s : Finset I) : C :=
  if h : s.card ≠ 0 then
    c (sorted s (Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 h)).symm)
  else p0

end TuplePatterns

namespace TailBound

open Tuples Diagrams Colors Tests ThresholdArithmetic

variable {I B : Type u} (hCH : CH.{u})

end TailBound

namespace BaseOrders

variable {B : Type u} [LinearOrder B]

end BaseOrders

end CHObstruction

end

end OAI


