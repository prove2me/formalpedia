-- Prove2me | Definitions.Def_OAI_Analysis_DiamondDistortion_Ancestry
-- name    : OAI_Analysis_DiamondDistortion_Ancestry
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T00:00:36.867489+00:00
-- url     : https://prove2.me/theorems/0bc925f2-cab2-4a5f-ae03-2166e86980eb
-- title:
--   Downward-closed heads, gates and segment tails in an ancestral order
-- statement:
--   Let $(\iota,\le)$ be an *ancestral order*: a partial order in which the predecessors of every vertex form a chain, that is, $a\le c$ and $b\le c$ imply $a\le b$ or $b\le a$ (the ancestor relation of a rooted forest is the guiding example). Its *segments* are the finite order intervals
--
--   $$
--   [a,b]=\{v\in\iota:\ a\le v\le b\},\qquad a\le b,
--   $$
--
--   more precisely the finite sets $S$ for which there are $a\le b$ with $S=[a,b]$; every singleton $\{v\}=[v,v]$ is a segment. A segment family $\mathbf F=(S_1,\dots,S_n)$ is a finite list of pairwise disjoint segments, and $c_{00}(\iota)$ denotes the finitely supported real functions on $\iota$. The file defines:
--
--   1. **Ancestral sets.** A set $H\subseteq\iota$ is ancestral (a head) if it is downward closed: $a\le b$ and $b\in H$ imply $a\in H$.
--
--   2. **Gates.** A vertex $g$ is a gate of a set $H\subseteq\iota$ if $g\notin H$ and every strict predecessor $v<g$ lies in $H$. Two distinct gates of the same $H$ are incomparable, since a gate lying strictly below another gate would have to belong to $H$.
--
--   3. **Lower endpoint.** For a segment $S_i$ of $\mathbf F$, $\mathrm{first}(S_i)$ is a vertex $a$ such that $S_i=[a,b]$ for some $b\ge a$; it is the least element of $S_i$, hence uniquely determined.
--
--   4. **Boundary coefficient.** For $p\in c_{00}(\iota)$ and $g\in\iota$,
--   $$
--   \beta_{\mathbf F}(p,g)=\sum_{i:\ g\in S_i}\ \sum_{v\in S_i}p(v).
--   $$
--   Since the segments are disjoint, this is the sum of $p$ over the segment of $\mathbf F$ that contains $g$, and $0$ if no segment contains $g$.
--
--   5. **Tail at a vertex.** For a finite set $H\subseteq\iota$ and $g\in\iota$, $\mathrm{tail}_{\mathbf F,H}(g)=S_i\setminus H$ if $g$ lies in the segment $S_i$ of $\mathbf F$, and $\mathrm{tail}_{\mathbf F,H}(g)=\varnothing$ if $g$ lies in no segment of $\mathbf F$.
--
--   6. **Gate set.** For finite sets $H,K\subseteq\iota$, $\mathrm{Gates}(H,K)=\{g\in K:\ g\text{ is a gate of }H\}$.
--
--   These notions describe how a disjoint family of segments meets a finite downward-closed head $H$: the parts of segments lying outside $H$ (tails), the minimal vertices outside $H$ (gates), and the mass of a finite array carried by the segment through a given vertex. They are used to split segment norms, and functionals on the corresponding James-type spaces, into a head part and a tail part.
--
--   **Formalization Note** The order is the class `Ancestry` (a partial order with the field `predecessors_total`), and segments and families are those of the segment system `Ancestry.segments`. `first` applies `Classical.choose` to the segment witness, and `tailAt` chooses an index of a segment containing $g$; by the uniqueness and disjointness noted above, these choices do not affect the values. `Ancestral` and `Gate` take a `Set`, while `tailAt` and `gateSet` take finsets.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DiamondDistortion/Ancestry.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DiamondDistortion/Ancestry.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the DiamondDistortion mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_DiamondDistortion
import Definitions.Def_OAI_Analysis_DiamondDistortion_SegmentNorm

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

namespace Ancestry
open scoped Classical
variable {ι : Type*} [A : Ancestry ι]
attribute [local instance] OAI.DiamondDistortion.Ancestry.instPartialOrder
/-- Downward closed sets are precisely ancestral heads. -/
def Ancestral (H : Set ι) : Prop := ∀ ⦃a b : ι⦄, a ≤ b → b ∈ H → a ∈ H

/-- A minimal vertex outside a head. Gates in a tree form an antichain. -/
def Gate (H : Set ι) (g : ι) : Prop :=
  g ∉ H ∧ ∀ v, v < g → v ∈ H

/-- Canonical lower endpoint; no ordering is imposed on segment families. -/
def first (F : A.segments.Family) (i : Fin F.n) : ι :=
  Classical.choose (F.allowed i)

/-- The (possibly zero) head sum carried by the unique segment at a gate. -/
def boundaryCoeff (F : A.segments.Family) (p : ι →₀ ℝ) (g : ι) : ℝ :=
  ∑ i : Fin F.n, if g ∈ F.seg i then (∑ v ∈ F.seg i, p v) else 0

/-- The tail from the unique segment through g, or the empty segment if absent. -/
def tailAt (F : A.segments.Family) (H : Finset ι) (g : ι) : Finset ι :=
  if h : ∃ i, g ∈ F.seg i then (F.seg h.choose).filter (· ∉ H) else ∅

/-- The represented finite set of all gates of H in K. -/
def gateSet (H K : Finset ι) : Finset ι := K.filter (A.Gate (H : Set ι))

end Ancestry

end DiamondDistortion

end

end OAI


