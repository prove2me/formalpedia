-- Prove2me | Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FirstDefault
-- name    : OAI_MeasureTheory_DyadicAvoidance_FirstDefault
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T03:07:51.820111+00:00
-- url     : https://prove2.me/theorems/32baa393-2f22-4ec9-857f-01f7e4db5578
-- title:
--   Path cylinders for first-success routing along nondefault paths
-- statement:
--   This file encodes, as explicit conditions on finitely many selector bits, the event that first-success routing follows a prescribed path that never uses the default child. Fix $M, d \in \mathbb{N}$. Children are $0,1,\dots,M$; the letter $M$ is the default child and $0,\dots,M-1$ are the nondefault children, each carrying a selector. Boolean values are written $0$ (false) and $1$ (true).
--
--   1. **Addresses.** An address is a pair $(P,j)$ consisting of a word $P$ over $\{0,\dots,M\}$ (a node) and a selector index $j \in \{0,\dots,M-1\}$. It is *bounded* if $|P| < d$.
--
--   2. **Nondefault paths and their tests.** A nondefault path of depth $d$ is a map $f : \{0,\dots,d-1\} \to \{0,\dots,M-1\}$. Its set of tests is
--   $$
--   T_f = \big\{ (k,j) : 0 \le k < d,\ \ 0 \le j \le f(k) \big\}.
--   $$
--
--   3. **Prefixes, tested addresses and required bits.** The node at which the $k$-th decision along $f$ is made is the word $P^f_k = f(0)\,f(1) \cdots f(k-1)$ of length $k$. The test $(k,j) \in T_f$ inspects the address $(P^f_k, j)$, and its required bit is $1$ if $j = f(k)$ and $0$ if $j < f(k)$. Every tested address is bounded, since $|P^f_k| = k < d$, and the file packages it as a bounded address.
--
--   4. **Path cylinders.** Let $\Omega$ be any set and $S$ a family of bits, assigning to each address $a$ and each $\omega \in \Omega$ a value $S_a(\omega) \in \{0,1\}$. The cylinder of the path $f$ is
--   $$
--   C_f = \Big\{ \omega \in \Omega : S_{(P^f_k,\, j)}(\omega) = \mathbf{1}[\,j = f(k)\,] \ \text{ for all } (k,j) \in T_f \Big\}.
--   $$
--   On $C_f$, at each node $P^f_k$ the selectors $0,\dots,f(k)-1$ fail and the selector $f(k)$ succeeds, so under the first-success rule the route from the root chooses $f(0), f(1), \dots, f(d-1)$ in turn.
--
--   Cylinders of distinct paths are disjoint, and their union is the event that the first-success route from the root avoids the default child during its first $d$ steps. Because $C_f$ prescribes exactly $\sum_{k<d} (f(k)+1)$ selector bits, these cylinders are used to show that this no-default event has probability $(1 - 2^{-M})^d$ when the selector bits are independent and fair.
--
--   **Formalization Note** Addresses are `List (Fin (M + 1)) × Fin M`, paths are `Fin d → Fin M`, and tests form the dependent pair type `(k : Fin d) × Fin (f k + 1)`. The prefix is `List.ofFn` of the earlier choices embedded by `castSucc`, the required bit is `decide (j = f k)`, bounded addresses form a subtype, and `address_length_lt` gives the bound used by `boundedAddress`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/FirstDefault.lean

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/FirstDefault.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the DyadicAvoidance mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_DyadicAvoidance
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_PeriodicBasic
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GridSeparation
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FiniteTableModel
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_OrderedRouting
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RoutingPath
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_CenterRouteExposure
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_ExceptionalCenters
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_CenterFailureBound

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u_Ω

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Problem310.FirstDefault

abbrev Address (M : ℕ) := List (Fin (M + 1)) × Fin M
abbrev Path (M d : ℕ) := Fin d → Fin M
abbrev Tests {M d : ℕ} (f : Path M d) := (k : Fin d) × Fin ((f k).val + 1)

/-- The node immediately before the `k`th decision along a nondefault path. -/
def pathPrefix {M d : ℕ} (f : Path M d) (k : Fin d) : List (Fin (M + 1)) :=
  List.ofFn fun j : Fin k.val => (f ⟨j.val, lt_trans j.isLt k.isLt⟩).castSucc

/-- Every earlier rejected selector and the selected selector are tested. -/
def address {M d : ℕ} (f : Path M d) (i : Tests f) : Address M :=
  (pathPrefix f i.1, ⟨i.2.val, lt_of_lt_of_le i.2.isLt (Nat.succ_le_of_lt (f i.1).isLt)⟩)

def requiredBit {M d : ℕ} (f : Path M d) (i : Tests f) : Bool :=
  decide (i.2.val = (f i.1).val)

/-- The selector cylinder expressing that a prescribed path is followed. -/
def cylinder {M d : ℕ} {Ω : Type u_Ω} (S : Address M → Ω → Bool)
    (f : Path M d) : Set Ω :=
  {ω | ∀ i : Tests f, S (address f i) ω = requiredBit f i}

abbrev BoundedAddress (M d : ℕ) := {a : Address M // a.1.length < d}

lemma address_length_lt {M d : ℕ} (f : Path M d) (i : Tests f) :
    (address f i).1.length < d := by
  simpa only [address, pathPrefix, List.length_ofFn] using i.1.isLt

def boundedAddress {M d : ℕ} (f : Path M d) (i : Tests f) : BoundedAddress M d :=
  ⟨address f i, address_length_lt f i⟩

end Problem310.FirstDefault

end

end OAI


