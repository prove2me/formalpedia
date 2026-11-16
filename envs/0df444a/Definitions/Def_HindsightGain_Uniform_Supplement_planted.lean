-- Prove2me | Definitions.Def_HindsightGain_Uniform_Supplement_planted
-- name    : HindsightGain_Uniform_Supplement_planted
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:52:30.493203+00:00
-- url     : https://prove2.me/theorems/e5e7ee8a-9015-4bf6-8b75-1420a1be170a
-- title:
--   The planted-bipartition input laws, answer laws, χ²-divergence and even edge sets
-- statement:
--   Fix $0<\varepsilon\le1/64$ and put $\theta=32\varepsilon\le\tfrac12$. The law $D_0$ on graphs with vertex set $[n]$ is $G(n,\tfrac12)$. To sample $D_1$, draw independent uniform labels $\sigma_u\in\{\pm1\}$ and then include each pair $uv$ independently with
--   $$\mathbb P(uv\in E\mid\sigma)=\tfrac12\big(1-\theta\sigma_u\sigma_v\big).$$
--   For a fixed set $F$ of distinct pairs, $D_b^F$ is the law of the answers $(X_e)_{e\in F}$, with $X_e=+1$ for an edge and $-1$ otherwise. For laws on a finite set, $\chi^2(P\|Q)=\sum_x(P(x)-Q(x))^2/Q(x)$. An edge set $J$ is **even** if every vertex has even degree in $([n],J)$.
--
--   These are the objects of the nonadaptive lower bound in Appendix A.
--
--   **Formalization Note** Laws are given by their point masses on the finitely many graphs on `Fin n`; answers are Booleans (`true` for an edge).
-- source:
--   Xiaohui Bei, Wenhao Wu, The Optimizer's Windfall: Bounding Hindsight Gain under Random Restrictions, STOC 2027 submission #464 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/464.pdf, Appendix A pp.33-34

import Mathlib
import Definitions.Def_HindsightGain_Uniform_Supplement_graphs

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical

namespace HindsightGain.Uniform.Supplement

/-- A label `b` read as the sign `+1` (`true`) or `-1` (`false`). -/
def sgn (b : Bool) : ℝ := if b then 1 else -1

/-- The unordered pairs of distinct vertices, written `u < v`. -/
def vertexPairs (n : ℕ) : Finset (Fin n × Fin n) :=
  (Finset.univ : Finset (Fin n × Fin n)).filter (fun uv => uv.1 < uv.2)

/-- `D_0 = G(n, 1/2)` (p.33): every pair is an edge independently with probability `1/2`. -/
def lawD0 (n : ℕ) (_G : SimpleGraph (Fin n)) : ℝ :=
  ∏ _uv ∈ vertexPairs n, (1 / 2 : ℝ)

/-- `D_1` (p.33) with `θ = 32ε`: independent uniform labels `σ_u ∈ {±1}`, then, given `σ`,
independent edges with `P(uv ∈ E | σ) = (1 - θ σ_u σ_v)/2`. -/
def lawD1 (n : ℕ) (ε : ℝ) (G : SimpleGraph (Fin n)) : ℝ :=
  ∑ σ : Fin n → Bool, (1 / 2 : ℝ) ^ n *
    ∏ uv ∈ vertexPairs n,
      (if G.Adj uv.1 uv.2 then (1 - 32 * ε * sgn (σ uv.1) * sgn (σ uv.2)) / 2
        else (1 + 32 * ε * sgn (σ uv.1) * sgn (σ uv.2)) / 2)

/-- Probability of a graph event under a law given by its point masses. -/
def graphProb {n : ℕ} (law : SimpleGraph (Fin n) → ℝ) (E : SimpleGraph (Fin n) → Prop) : ℝ :=
  ∑ G : SimpleGraph (Fin n), if E G then law G else 0

/-- `D_b^F` (p.34): the law of the answers on a fixed query set `F` (`true` for an edge, i.e.
`X_e = +1`; `false` for a non-edge, `X_e = -1`). -/
def answerLaw {n : ℕ} (law : SimpleGraph (Fin n) → ℝ) (F : Finset (Sym2 (Fin n)))
    (x : {z // z ∈ F} → Bool) : ℝ :=
  ∑ G : SimpleGraph (Fin n), if (∀ z : {z // z ∈ F}, (z.1 ∈ G.edgeSet ↔ x z = true)) then law G else 0

/-- `χ²(P ‖ Q) = Σ_x (P(x) - Q(x))² / Q(x)` for laws on a finite set. -/
def chiSq {X : Type} [Fintype X] (P Q : X → ℝ) : ℝ := ∑ x, (P x - Q x) ^ 2 / Q x

/-- An edge set `J` is even if every vertex has even degree in `(V, J)` (p.34). -/
def IsEvenEdgeSet {V : Type} (J : Finset (Sym2 V)) : Prop :=
  ∀ v : V, Even (J.filter (fun z => v ∈ z)).card

end HindsightGain.Uniform.Supplement


