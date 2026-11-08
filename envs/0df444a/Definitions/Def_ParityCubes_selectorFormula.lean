-- Prove2me | Definitions.Def_ParityCubes_selectorFormula
-- name    : ParityCubes_selectorFormula
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T10:15:12.444193+00:00
-- url     : https://prove2.me/theorems/5ef48a0d-a14d-4229-852c-f79a2fdd14c8
-- title:
--   The selector formula $Q(a,y)$, the indicator $C_G$, and multicolored cliques
-- statement:
--   Two distinct vertices of a vertex-colored graph are **incompatible** if they belong to the same class, or to different classes without being adjacent. With a variable $y_v$ for each vertex and a selector $a_i$ for each class,
--
--   $$Q(a,y)=\bigwedge_{\{u,v\}\text{ incompatible}}(\neg y_u\vee\neg y_v)\ \wedge\ \bigwedge_i\bigwedge_{v\in V_i}(a_i\vee\neg y_v),$$
--
--   $$C_G(y)=\bigwedge_{\{u,v\}\text{ incompatible}}(\neg y_u\vee\neg y_v)\cdot\prod_i\Big(\bigvee_{v\in V_i}y_v\Big).$$
--
--   A **multicolored clique** consists of one vertex of every class, pairwise adjacent. Summing $Q$ over all selectors gives $C_G$, by eq. (2).
-- source:
--   Sheshadri, Smirnov, The Complexity of Choosing Parity Projections, arXiv:2611.00289 (manuscript sha256 95994d2d…), proof of Theorem 4.1, pp.8–9 (PDF pp.9–10); §2.3, p.5 (PDF p.6)

import Mathlib

set_option autoImplicit false

namespace ParityCubes

/-- Two **incompatible** vertices of a vertex-colored graph (Sheshadri–Smirnov, arXiv:2611.00289,
manuscript sha256 95994d2d…, proof of Theorem 4.1, p.8 (PDF p.9)): "Two distinct vertices are
incompatible if they belong to the same class, or to different classes without being adjacent."
The color classes are `V_i = col⁻¹(i)`, `i < r`. -/
def Incompatible {V : Type*} {r : ℕ} (col : V → Fin r) (G : SimpleGraph V) (u v : V) : Prop :=
  u ≠ v ∧ (col u = col v ∨ ¬ G.Adj u v)

instance {V : Type*} [DecidableEq V] {r : ℕ} (col : V → Fin r) (G : SimpleGraph V)
    [DecidableRel G.Adj] (u v : V) : Decidable (Incompatible col G u v) := by
  unfold Incompatible; infer_instance

/-- The formula `Q(a, y) = ⋀_{{u,v} incompatible} (¬y_u ∨ ¬y_v) ∧ ⋀_i ⋀_{v ∈ V_i} (a_i ∨ ¬y_v)`
(proof of Theorem 4.1, p.8 (PDF p.9)), as a Boolean function of the selectors `a_i` (`Sum.inl i`)
and the vertex variables `y_v` (`Sum.inr v`). -/
def selectorFormula {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ} (col : V → Fin r)
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : Fin r ⊕ V → Bool) : Bool :=
  decide ((∀ u v : V, Incompatible col G u v → (!x (Sum.inr u) || !x (Sum.inr v)) = true) ∧
    ∀ v : V, (x (Sum.inl (col v)) || !x (Sum.inr v)) = true)

/-- `C_G(y) = ⋀_{{u,v} incompatible} (¬y_u ∨ ¬y_v) · ∏_i (⋁_{v ∈ V_i} y_v)`, the right-hand side of
eq. (2) (p.9 (PDF p.10)). -/
def cliqueIndicator {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ} (col : V → Fin r)
    (G : SimpleGraph V) [DecidableRel G.Adj] (y : V → Bool) : Bool :=
  decide ((∀ u v : V, Incompatible col G u v → (!y u || !y v) = true) ∧
    ∀ i : Fin r, ∃ v : V, col v = i ∧ y v = true)

/-- The graph `G` with color classes `col⁻¹(i)`, `i < r`, has a **multicolored clique**
(§2.3, p.5 (PDF p.6)): one vertex `s i` of every class, pairwise adjacent. -/
def HasMulticoloredClique {V : Type*} {r : ℕ} (col : V → Fin r) (G : SimpleGraph V) : Prop :=
  ∃ s : Fin r → V, (∀ i : Fin r, col (s i) = i) ∧ ∀ i j : Fin r, i ≠ j → G.Adj (s i) (s j)

end ParityCubes


