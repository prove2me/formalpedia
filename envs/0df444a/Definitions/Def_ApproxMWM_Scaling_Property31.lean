-- Prove2me | Definitions.Def_ApproxMWM_Scaling_Property31
-- name    : ApproxMWM_Scaling_Property31
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T13:06:57.54362+00:00
-- url     : https://prove2.me/theorems/a58fffc0-39a9-4f61-9d54-87d8edbe2738
-- title:
--   Property 3.1 — relaxed feasibility and complementary slackness at scale $i$
-- statement:
--   Let $i\in[0,L]$ be the current scale and consider a state $(M,\Omega,y,z)$ of the scaling algorithm. **Property 3.1** consists of:
--
--   1. **Granularity.** $z(B)$ is a nonnegative multiple of $\delta_i$ for every odd set $B$, and $y(u)$ is a nonnegative multiple of $\delta_i/2$ for every vertex $u$.
--   2. **Active Blossoms.** $\Omega$ contains every odd set $B$ with $z(B)>0$, and every root blossom $B$ has $z(B)>0$.
--   3. **Near Domination.** $yz(e)\ge w_i(e)-\delta_i$ for every edge $e$.
--   4. **Near Tightness.** A matched or blossom edge is of type $j$ if it last entered $M\cup\bigcup_{B\in\Omega}E_B$ in scale $j\le i$; such an edge satisfies
--   $$yz(e)\le w_i(e)+2(\delta_j-\delta_i).$$
--   5. **Free Vertex Duals.** The $y$-values of free vertices are equal and strictly less than the $y$-values of matched vertices.
--
--   Lemma 3.5 shows that the algorithm with Definition 3.2 maintains this property; Lemma 3.11 shows which parts survive under Definition 3.10.
--
--   **Formalization Note** Items (3) and (4) are also provided edge by edge (`NearDomAt`, `NearTightAt`) because Lemma 3.11 asserts them per edge. The type of an edge is the ghost field `entered` of the state.
-- source:
--   Duan and Pettie, Linear-Time Approximation for Maximum Weight Matching, J. ACM 61(1), Article 1 (2014), https://doi.org/10.1145/2529989, p. 1:12, Property 3.1

import Mathlib
import Definitions.Def_ApproxMWM_Scaling_Algorithm

namespace ApproxMWM.Scaling

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Property 3.1(1), Granularity, at scale `i`: `z(B)` is a nonnegative multiple of `δ_i` for every
odd set `B`, and `y(u)` is a nonnegative multiple of `δ_i / 2` for every vertex `u`. -/
def Granularity (P : Params) (i : ℕ) (s : State V) : Prop :=
  (∀ B : Finset V, Odd B.card → ∃ k : ℕ, s.z B = k * P.δ i) ∧
  ∀ u : V, ∃ k : ℕ, s.y u = k * (P.δ i / 2)

/-- Property 3.1(2) = Property 2.2(2), Active Blossoms: `Ω` contains every odd set `B` with
`z(B) > 0`, and every root blossom `B` of `Ω` has `z(B) > 0`. -/
def ActiveBlossoms (s : State V) : Prop :=
  (∀ B : Finset V, Odd B.card → 0 < s.z B → B ∈ s.Ω) ∧
  ∀ B : Finset V, IsRoot s.Ω B → 0 < s.z B

/-- Property 3.1(3) for one edge, Near Domination at scale `i`: `yz(e) ≥ w_i(e) - δ_i`. -/
def NearDomAt (P : Params) (w : Sym2 V → ℕ) (i : ℕ) (s : State V) (e : Sym2 V) : Prop :=
  truncW P w i e - P.δ i ≤ yz s.y s.z e

/-- Property 3.1(4) for one edge, Near Tightness at scale `i`: if `e` is a matched or blossom
edge, it is of type `j = entered e ≤ i` and `yz(e) ≤ w_i(e) + 2 (δ_j - δ_i)`. -/
def NearTightAt (P : Params) (w : Sym2 V → ℕ) (i : ℕ) (s : State V) (e : Sym2 V) : Prop :=
  e ∈ s.tight →
    s.entered e ≤ i ∧ yz s.y s.z e ≤ truncW P w i e + 2 * (P.δ (s.entered e) - P.δ i)

/-- Property 3.1(5), Free Vertex Duals: the `y`-values of free vertices are all equal and strictly
less than the `y`-values of matched vertices. -/
def FreeVertexDuals (s : State V) : Prop :=
  (∀ u v : V, IsFree s.M u → IsFree s.M v → s.y u = s.y v) ∧
  ∀ u v : V, IsFree s.M u → IsMatched s.M v → s.y u < s.y v

/-- Property 3.1 (Relaxed Feasibility and Complementary Slackness, p. 1:12) at scale `i`. -/
def Property31 (P : Params) (G : SimpleGraph V) (w : Sym2 V → ℕ) (i : ℕ) (s : State V) :
    Prop :=
  Granularity P i s ∧ ActiveBlossoms s ∧
  (∀ e ∈ G.edgeSet, NearDomAt P w i s e) ∧
  (∀ e, NearTightAt P w i s e) ∧
  FreeVertexDuals s

end ApproxMWM.Scaling


