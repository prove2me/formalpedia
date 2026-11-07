-- Prove2me | Definitions.Def_SteinerAPX_CableLayout
-- name    : SteinerAPX_CableLayout
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:34:54.802708+00:00
-- url     : https://prove2.me/theorems/b8942c2f-58f7-4ab3-9150-db1adb6df1eb
-- title:
--   Cable instances: gadgets, ports, labels and cables
-- statement:
--   Let $H=(U,E)$ be a three-dimensional matching instance. The **cable instance** has one **square gadget** for each triple and one **fallback gadget** for each element, with centres $z_s\in\mathbb R^D$, and uses two orthonormal vectors $b_1,b_2$ for every gadget. **Labels** are the elements of $U$ and a symbol $0$. The **ports** are:
--
--   1. at the square $s$ of a triple $\{u,v,w\}$, the four points $z_s\pm b_1$, $z_s\pm b_2$, labelled $0,u,v,w$ in some order;
--   2. at the fallback $s$ of an element $u$, the two points $z_s\pm\frac23 b_1$, labelled $0$ and $u$.
--
--   So $p_{s,i}=z_s+\alpha_s v_{s,i}$ with $v_{s,i}\in\{\pm b_1,\pm b_2\}$, $\alpha_s=1$ at squares and $\alpha_s=\frac23$ at fallbacks. For each label $i$, the **cable** $\Gamma_i$ is a tree of line segments through all ports labelled $i$; $\Gamma_0$ is the **backbone**, and different cables are disjoint. $L=\sum_i\operatorname{len}(\Gamma_i)$ is the **total cable length**, and $B_s$ is the closed ball of radius $20$ around $z_s$. The constant
--   $$
--   \Delta=4-\sqrt2-\sqrt6>0
--   $$
--   is the saving of a four-port Steiner tree over three fallback connections.
--
--   **Formalization Note** The paper fixes the four port positions of a square but not which label sits where; the layout records the choice as a bijection from the labels of a gadget onto $\{\pm b_1,\pm b_2\}$ (onto $\{\pm b_1\}$ at a fallback), and statements quantify over it. A layout is data; the conditions above form the predicate `WellFormed`. Cables are trees of segments, as §4.1 says (Definition 5's "connected union" is weaker, but the cable reduction uses the tree property).
-- source:
--   S. Bartlmae, Inapproximability of Euclidean Steiner Tree, STOC 2027 submission (manuscript sha256 6f78a9ea…), §4.1, p.13 (PDF p.15); ∆ from §3.1, p.5 (PDF p.7)

import Mathlib
import Definitions.Def_SteinerAPX_Network
import Definitions.Def_SteinerAPX_IsTreeNet
import Definitions.Def_SteinerAPX_Inst3DM

namespace SteinerAPX

open Inst3DM

/-- **Cable instances: gadgets, ports, labels and cables.** S. Bartlmae, *Inapproximability of
Euclidean Steiner Tree*, STOC 2027 submission (manuscript sha256 6f78a9ea…), §4.1, p.13 (PDF
p.15): "Our instance has one square gadget for each triple and one fallback gadget for each
element; these m gadgets are indexed by s = 1, …, m and have centres zs ∈ RD. We use the same two
orthogonal unit coordinate vectors b1, b2 for every gadget and define the ports, where the cables
attach, by the following coordinates and labels. (a) For the square of a triple {u, v, w}, the
ports ps,0, ps,u, ps,v, ps,w are the four points zs ± b1 and zs ± b2. … (b) For the fallback of an
element u, the ports ps,0, ps,u are the points zs ± (2/3)b1. … For each label i, we join the ports
labelled i by a tree of line segments, the cable Γi, so that different cables are disjoint; we call
Γ0 the backbone. Let L be the total cable length and, for each gadget s, let Bs be the closed ball
of radius 20 centred at zs." Also `∆ = 4 − √2 − √6` (§3.1, p.5).

Labels are `none` (the symbol 0, the backbone) and `some u` for elements `u`. Gadgets are the
triples of `E` (squares) and the elements (fallbacks). A layout gives the centres `z s`, the
vectors `b₁, b₂`, a direction `dir s i ∈ {±b₁, ±b₂}` for each label `i` of `s`, and one network
(cable) per label; the port is `p_{s,i} = z s + α_s · dir s i` with `α = 1` at squares and
`α = 2/3` at fallbacks. `WellFormed` collects the conditions of the quoted paragraph.

**Formalization Note** The paper fixes the four points of a square but not which label sits at
which point; `dir` records this choice, a bijection from the four labels onto `{±b₁, ±b₂}` (onto
`{±b₁}` at a fallback), and every statement quantifies over it. Each cable is a tree of line
segments (`IsTreeNet`), as §4.1 says; Definition 5's "connected union" is weaker, but the proof of
Lemma 8 uses the tree property. Values of `dir s i` for labels `i` not at `s` are never used. -/
structure CableLayout (H : Inst3DM) (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    where
  /-- Gadget centres. -/
  z : (H.triples ⊕ H.Element) → V
  /-- The two orthogonal unit vectors. -/
  b₁ : V
  b₂ : V
  /-- Direction of the port of label `i` at gadget `s`. -/
  dir : (H.triples ⊕ H.Element) → Option H.Element → V
  /-- The cable `Γᵢ`. -/
  cable : Option H.Element → Network V

/-- Labels: `none` is the backbone symbol 0, `some u` the element `u`. -/
abbrev Label (H : Inst3DM) := Option H.Element

/-- Gadgets: squares (triples of `E`) and fallbacks (elements). -/
abbrev Gadget (H : Inst3DM) := H.triples ⊕ H.Element

/-- `∆ = 4 − √2 − √6`. -/
noncomputable def Delta : ℝ := 4 - Real.sqrt 2 - Real.sqrt 6

/-- The labels of the ports of a gadget: `0, u, v, w` at the square of `{u, v, w}`, `0, u` at the
fallback of `u`. -/
def labels (H : Inst3DM) : Gadget H → Finset (Label H)
  | .inl t => insert none ((H.elems t.1).image some)
  | .inr u => {none, some u}

/-- The scale `α`: `1` at squares, `2/3` at fallbacks. -/
noncomputable def alpha {H : Inst3DM} : Gadget H → ℝ
  | .inl _ => 1
  | .inr _ => 2 / 3

namespace CableLayout

variable {H : Inst3DM} {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The port `p_{s,i} = z_s + α_s · dir`. -/
noncomputable def port (L : CableLayout H V) (s : Gadget H) (i : Label H) : V :=
  L.z s + alpha s • L.dir s i

/-- The radial segment from the port `p_{s,i}` straight away from `z_s` to the boundary of `B_s`. -/
noncomputable def radial (L : CableLayout H V) (s : Gadget H) (i : Label H) : Set V :=
  segment ℝ (L.port s i) (L.z s + (20 : ℝ) • L.dir s i)

/-- The ball `B_s`: closed, radius 20, centre `z_s`. -/
def ball (L : CableLayout H V) (s : Gadget H) : Set V := Metric.closedBall (L.z s) 20

/-- The total cable length `L`. -/
noncomputable def totalLen (L : CableLayout H V) : ℝ := ∑ i : Label H, len (L.cable i)

/-- The conditions of §4.1: `b₁, b₂` orthonormal; at every square the four labels are sent
bijectively to `{±b₁, ±b₂}`, at every fallback the two labels to `{±b₁}`; every cable is a tree of
line segments through all ports with its label; different cables are disjoint. -/
def WellFormed (L : CableLayout H V) : Prop :=
  Orthonormal ℝ ![L.b₁, L.b₂] ∧
  (∀ t : H.triples, Set.BijOn (L.dir (.inl t)) ↑(labels H (.inl t))
      ({L.b₁, -L.b₁, L.b₂, -L.b₂} : Set V)) ∧
  (∀ u : H.Element, Set.BijOn (L.dir (.inr u)) ↑(labels H (.inr u)) ({L.b₁, -L.b₁} : Set V)) ∧
  (∀ i, IsTreeNet (L.cable i)) ∧
  (∀ s, ∀ i ∈ labels H s, L.port s i ∈ carrier (L.cable i)) ∧
  (∀ i j, i ≠ j → Disjoint (carrier (L.cable i)) (carrier (L.cable j)))

end CableLayout

end SteinerAPX


