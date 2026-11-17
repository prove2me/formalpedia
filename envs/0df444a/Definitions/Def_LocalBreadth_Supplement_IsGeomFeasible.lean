-- Prove2me | Definitions.Def_LocalBreadth_Supplement_IsGeomFeasible
-- name    : LocalBreadth_Supplement_IsGeomFeasible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:21:19.146047+00:00
-- url     : https://prove2.me/theorems/4790bcc4-08d0-4269-b730-441ee5b6b410
-- title:
--   Geometric $q$-feasibility outside $Q_a$
-- statement:
--   For $a\ge0$ let $Q_a=[-a,a]^d\cap\mathbb Z^d$. Given cutoffs $s_0,\dots,s_r\ge1$, a chain $L_0\supseteq\dots\supseteq L_r$ is **geometrically $q$-feasible at these cutoffs outside $Q_a$** if every finite rectangle packet $(\mathcal R_0,\dots,\mathcal R_r)$ is feasible in the finite stopping game whenever each $R\in\mathcal R_i$ is disjoint from $Q_a$ and satisfies
--   $$m_{L_i}(R)\ge s_i\,h(V(R)).$$
--
--   This is the local quantitative condition carried along every path of a protected tree.
--
--   **Formalization Note** The quota is given per level; the bound $s_i\ge1$ is imposed by the trees and decorations that use the definition.
-- source:
--   Kleinberg, Wei, Characterizing Local Breadth in Language Generation, STOC 2027 submission (manuscript sha256 f924cbfc309339291b1a61b8504342f4050ece6e4e903dd18b2bf541446f1064), Definition 7.4, p.54

import Mathlib
import Definitions.Def_LocalBreadth_Supplement_deltaH
import Definitions.Def_LocalBreadth_Supplement_StoppingGame

namespace LocalBreadth.Supplement

/-- The central cube `Q_a = [-a, a]^d ∩ ℤ^d` (Definition 7.4, p.54). -/
def cubeQ (d : ℕ) (a : ℝ) : Set (Fin d → ℤ) := {p | ∀ i, |((p i : ℤ) : ℝ)| ≤ a}

/-- **Geometric feasibility** (Definition 7.4). Kleinberg, Wei, STOC 2027 submission (manuscript sha256
f924cbfc…), p.54: the chain `L 0, …, L r` is geometrically feasible at the cutoffs `c 0, …, c r` outside
`Q_a` if every finite rectangle packet `(R_0, …, R_r)` is feasible whenever each `R ∈ R_i` is a
(nonempty) rectangle disjoint from `Q_a` with `m_{L_i}(R) ≥ c_i h(V(R))`.

**Formalization Note.** The quota is given per level (`qt i`): for Definition 7.4 it is `q(L_i)`, for
Definition 7.14 the copy quota. The cutoffs' bound `c_i ≥ 1` is imposed by the trees and decorations
that use this definition. Packet families `R_i` with `i > r` play no role. -/
def IsGeomFeasible {d : ℕ} (h : ℕ → ℝ) (L : ℕ → Set (Fin d → ℤ)) (qt c : ℕ → ℝ) (r : ℕ)
    (a : ℝ) : Prop :=
  ∀ Rs : ℕ → Finset ((Fin d → ℤ) × (Fin d → ℤ)),
    (∀ i ≤ r, ∀ R ∈ Rs i, R.1 ≤ R.2 ∧ Disjoint (rect R) (cubeQ d a) ∧
      c i * h (vol R) ≤ (mass (L i) R : ℝ)) →
    IsFeasiblePacket L qt r Rs

end LocalBreadth.Supplement


