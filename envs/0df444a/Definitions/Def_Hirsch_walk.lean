-- Prove2me | Definitions.Def_Hirsch_walk
-- name    : Hirsch_walk
-- status  : Definition
-- author  : @WillR
-- created : 2026-09-06T05:47:59.589063+00:00
-- url     : https://prove2.me/theorems/21028eb8-ac2a-4010-9ad0-13006359b264
-- title:
--   Walks and graph distance in the vertex-edge graph of a polytope
-- statement:
--   Vocabulary for diameter inductions on H-polytopes, extending the mission's base model `Hirsch_model` (which defines the H-polytope $P=\{x\in\mathbb{R}^d:\langle a_i,x\rangle\le b_i\}$, adjacency $\mathrm{Adj}(P,u,v)$, and the walk predicate $\mathrm{DiamLE}(P,B)$).
--
--   **`Reach P L u v`** — there is a walk $w_0=u,\,w_1,\dots,w_L=v$ of exactly $L$ steps in the vertex-edge graph of $P$, each step either stationary ($w_i=w_{i+1}$) or along an edge ($\mathrm{Adj}(P,w_i,w_{i+1})$). This is precisely the body of $\mathrm{DiamLE}$: by definition,
--
--   $$\mathrm{DiamLE}(P,B)\iff \forall\, u,v\in\operatorname{ext}(P),\ \mathrm{Reach}(P,B,u,v),$$
--
--   recorded as the (definitional) lemma `diamLE_iff_reach`. Since stationary steps are allowed, $\mathrm{Reach}$ is monotone in $L$.
--
--   **`gdist P u v`** — the combinatorial (graph) distance from $u$ to $v$ in the vertex-edge graph of $P$: the least $L$ with $\mathrm{Reach}(P,L,u,v)$, and the junk value $0$ when no walk exists (Lean's `sInf` of an empty set of naturals).
--
--   These are the objects every layer-by-distance argument on polytope graphs (Barnette–Larman, Kalai–Kleitman) manipulates: distance layers from a base vertex, monotonicity and concatenation of walks, and distance comparison between a polytope and its relaxations. Publishing them as a shared definition lets such lemmas be stated on the platform without each proof re-minting a private `Reach`.
--
--   **Formalization Note** `Reach` and `gdist` are defined for an arbitrary real vector space $E$ and set $P\subseteq E$, exactly as `Adj` and `DiamLE` are in `Hirsch_model`. `gdist` is noncomputable. The only lemmas included are the definitional unfolding `diamLE_iff_reach` and the trivial `reach_zero`.
-- source:
--   Definitional vocabulary for the Prove2Me mission 'The Polynomial Hirsch Conjecture' (definition Hirsch_model, 5d9574b6-1600-4e27-9161-d12946cc4a96). Context: G. Kalai, D. Kleitman, A quasi-polynomial bound for the diameter of graphs of polyhedra, Bull. AMS 26 (1992), p. 315 (distance layers); F. Santos, TOP 21 (2013), arXiv:1307.5900, Section 3 (connected layer families).

import Mathlib
import Definitions.Def_Hirsch_model

/-!
# Walks and graph distance in the vertex-edge graph of a polytope

Vocabulary for diameter inductions on H-polytopes.  `Reach P L u v` is the body of
`DiamLE`: a walk of exactly `L` steps from `u` to `v`, each step either stationary or
along an edge of `P`.  `gdist P u v` is the least such `L` (the combinatorial distance),
with the junk value `0` when no walk exists.
-/

namespace Hirsch

/-- `Reach P L u v`: there is a walk `w 0 = u, …, w L = v` of exactly `L` steps in the
vertex-edge graph of `P`, each step either stationary (`w i = w (i+1)`) or along an
edge (`Adj P (w i) (w (i+1))`).  `DiamLE P B` is exactly `∀ u v` extreme, `Reach P B u v`. -/
def Reach {E : Type*} [AddCommGroup E] [Module ℝ E] (P : Set E) (L : ℕ) (u v : E) : Prop :=
  ∃ w : ℕ → E, w 0 = u ∧ w L = v ∧ ∀ i < L, w i = w (i + 1) ∨ Adj P (w i) (w (i + 1))

/-- The combinatorial (graph) distance from `u` to `v` in the vertex-edge graph of `P`:
the least `L` with `Reach P L u v`, and `0` if there is no walk at all. -/
noncomputable def gdist {E : Type*} [AddCommGroup E] [Module ℝ E] (P : Set E) (u v : E) : ℕ :=
  sInf {L | Reach P L u v}

theorem diamLE_iff_reach {E : Type*} [AddCommGroup E] [Module ℝ E] (P : Set E) (B : ℕ) :
    DiamLE P B ↔ ∀ u ∈ Set.extremePoints ℝ P, ∀ v ∈ Set.extremePoints ℝ P, Reach P B u v :=
  Iff.rfl

theorem reach_zero {E : Type*} [AddCommGroup E] [Module ℝ E] (P : Set E) (u : E) :
    Reach P 0 u u :=
  ⟨fun _ => u, rfl, rfl, fun i hi => absurd hi (Nat.not_lt_zero i)⟩

end Hirsch


