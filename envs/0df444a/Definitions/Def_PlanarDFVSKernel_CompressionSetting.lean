-- Prove2me | Definitions.Def_PlanarDFVSKernel_CompressionSetting
-- name    : PlanarDFVSKernel_CompressionSetting
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:36:38.903182+00:00
-- url     : https://prove2.me/theorems/083a1a79-a019-4c68-af64-d521d05a9592
-- title:
--   The setting of §5: a GSCA instance after Rule 6, with $W$, $d_L$ and the records $\theta$
-- statement:
--   A **compression setting** is a GSCA instance $(H,\mathcal G,k)$ on a finite vertex set together with a designation of some groups as **ordinary** (the others are **special**) such that
--   1. $H$ is acyclic;
--   2. every ordinary group contains exactly one arc;
--   3. every available reverse arc $v\to u$ (an arc in some group) closes a base path $u\rightsquigarrow v$;
--   4. every base arc $u\to v$ lies on a base path $s\rightsquigarrow u\to v\rightsquigarrow t$ whose reverse $t\to s$ is available.
--
--   From it one defines the **retained set** $W$ (all sources and sinks of $H$ and all endpoints of special-group arcs); the auxiliary graph $L$ (base arcs of length $0$, ordinary reverse arcs of length $1$) and its distances $d_L(a,v)\in\mathbb N\cup\{\infty\}$; and the **distance records**
--   $$\theta(v)=\bigl(\min\{d_L(w,v),k+1\}\bigr)_{w\in W}.$$
--
--   **Formalization Note** These are the properties of Lemmas 4.3 and 4.4 that §5 uses; no planarity or dual is assumed (Lemma 4.4's reachability from and to $W$ follows from 1). Several weakly connected components are allowed.
-- source:
--   Sheng, Xiao, A Polynomial Kernel for Planar Directed Feedback Vertex Set, arXiv:2609.23669 (held version, sha256 75cfca8f…), §4.3, p.17 (PDF 18); §5.1, p.17–18 (PDF 18–19)

import Mathlib
import Definitions.Def_PlanarDFVSKernel_GSCA

set_option autoImplicit false

namespace PlanarDFVSKernel

/-- **The setting of Section 5: the GSCA instance after Reduction Rule 6** (Sheng, Xiao, *A
Polynomial Kernel for Planar Directed Feedback Vertex Set*, arXiv:2609.23669 (held version, sha256
75cfca8f…), §5.1, p.17–18 (PDF 18–19), with the properties of Lemma 4.3, p.16 (PDF 17), and
Lemma 4.4, p.17 (PDF 18)).

A GSCA instance `I` on a finite vertex type, together with the set `ordinary` of indices of its
ordinary groups (the other groups are special), such that:
1. `acyclic`: the base digraph `H` is acyclic ("The graph H is acyclic", p.18);
2. `ordinary_card`: every ordinary group contains exactly one arc (Lemma 4.3(i): "Every ordinary
   group contains one arc");
3. `available_closes`: every available reverse arc `v → u` has a base path `u ⇝ v` (p.18: "By
   Reduction Rule 6, every available reverse arc v → u has a corresponding base path u ⇝ v");
4. `base_covered`: every base arc `u → v` lies on a base path `s ⇝ u → v ⇝ t` whose reverse arc
   `t → s` belongs to some group (Lemma 4.3(ii)).

**Formalization Note** This is a `generalization` of the paper's instance `I₂`: no planarity and no
dual are assumed. Lemma 4.4's reachability property ("every vertex is reachable from, and can reach,
a vertex of W using base arcs alone") follows from 1, since `W` (below) contains all sources and
sinks; it is not a separate field. The paper treats each weakly connected component separately; here
the instance may have several components (available arcs stay inside one by 3). -/
structure CompressionSetting (V : Type*) [Fintype V] [DecidableEq V] where
  /-- the GSCA instance `(H, 𝒢, k)` -/
  I : GSCA V
  /-- the indices of the ordinary groups -/
  ordinary : Finset (Fin I.groups.length)
  /-- the base digraph is acyclic -/
  acyclic : ∀ a ∈ I.base, ¬ ArcReach I.base a.2 a.1
  /-- every ordinary group contains exactly one arc -/
  ordinary_card : ∀ i ∈ ordinary, (I.groups[i]).card = 1
  /-- every available reverse arc `v → u` closes a base path `u ⇝ v` -/
  available_closes : ∀ g ∈ I.groups, ∀ a ∈ g, ArcReach I.base a.2 a.1
  /-- every base arc `u → v` lies on a base path `s ⇝ u → v ⇝ t` with `t → s` available -/
  base_covered : ∀ a ∈ I.base, ∃ g ∈ I.groups, ∃ b ∈ g,
    ArcReach I.base b.2 a.1 ∧ ArcReach I.base a.2 b.1

namespace CompressionSetting

variable {V : Type*} [Fintype V] [DecidableEq V] (C : CompressionSetting V)

/-- **Available reverse arcs** (ibid., p.18 (PDF 19)): "An available reverse arc is an arc
occurring in at least one group, whether or not that group has been selected. Let R be the set of
all such arcs". -/
def available (a : V × V) : Prop := ∃ g ∈ C.I.groups, a ∈ g

/-- **The retained vertices `W`** (ibid., §4.3, p.17 (PDF 18)): "Let W consist of all sources and
sinks of H, together with all endpoints of reverse arcs in special groups." A source has no
incoming base arc and a sink no outgoing base arc (p.7 (PDF 8)). -/
noncomputable def W : Finset V := by
  classical exact Finset.univ.filter fun v =>
    (∀ a ∈ C.I.base, a.2 ≠ v) ∨ (∀ a ∈ C.I.base, a.1 ≠ v) ∨
      ∃ i, i ∉ C.ordinary ∧ ∃ a ∈ C.I.groups[i], a.1 = v ∨ a.2 = v

/-- Walks in the auxiliary graph `L` with their cost: `LReach c a v` holds when some walk from `a`
to `v` uses base arcs (length zero) and exactly `c` arcs of ordinary groups (length one)
(ibid., p.18 (PDF 19)): "Construct an auxiliary graph L on V(H) by taking all base arcs and all
reverse arcs in ordinary groups. Give base arcs length zero and ordinary reverse arcs length
one." -/
inductive LReach : ℕ → V → V → Prop
  | refl (a : V) : LReach 0 a a
  | base {c : ℕ} {a u v : V} : LReach c a u → (u, v) ∈ C.I.base → LReach c a v
  | ord {c : ℕ} {a u v : V} : LReach c a u → (∃ i ∈ C.ordinary, (u, v) ∈ C.I.groups[i]) →
      LReach (c + 1) a v

/-- **The distance `d_L(a, v)`** (ibid., p.18 (PDF 19)): "the shortest-path distance d_L(a, v)
counts the minimum number of ordinary reverse arcs needed to reach v from a. We use d_L(a, v) = ∞
when no such path exists." It is the least `c` with `LReach c a v`, and `⊤` if there is none. -/
noncomputable def dL (a v : V) : ℕ∞ := by
  classical exact if h : ∃ c, C.LReach c a v then (Nat.find h : ℕ∞) else ⊤

/-- **The distance record `θ(v)`** (ibid., p.18 (PDF 19)): "Order the retained vertices as
w₁, …, w_|W|. For each v ∉ W, define its distance record by θ(v) = (θ₁(v), …, θ_|W|(v)),
θᵢ(v) = min{d_L(wᵢ, v), k + 1}, where min{∞, k + 1} = k + 1."

`theta v w = min (d_L(w, v), k + 1)` for each retained `w`, with `k` the instance's budget.

**Formalization Note** The record is indexed by `W` itself rather than by an enumeration
`w₁, …, w_|W|`; two records are equal exactly when they are equal as tuples. It is defined for every
vertex; the paper uses it for `v ∉ W`. -/
noncomputable def theta (v : V) : C.W → ℕ :=
  fun w => (min (C.dL (w : V) v) ((C.I.k + 1 : ℕ) : ℕ∞)).toNat

end CompressionSetting

end PlanarDFVSKernel


