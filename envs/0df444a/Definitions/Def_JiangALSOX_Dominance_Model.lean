-- Prove2me | Definitions.Def_JiangALSOX_Dominance_Model
-- name    : JiangALSOX_Dominance_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T01:04:51.237615+00:00
-- url     : https://prove2.me/theorems/92161e88-97c7-4f52-a875-db9ccd160d56
-- title:
--   Chance-constraint data and Assumptions A1–A2
-- statement:
--   The data comprise arbitrary finite dimensions, a set $\Xi\subseteq\mathbb R^m$, a probability law $P$ on $\Xi$, a positive finite family of real functions $g_i(x,\xi)$, a decision set $X\subseteq\mathbb R^n$, a convex cone $C$, a cost vector $c$, and a risk level $\varepsilon$. Define $g(x,\xi)=\max_i g_i(x,\xi)$.
--
--   The assumptions require $0<\varepsilon<1$, measurability of every random section $g_i(x,\cdot)$, and, on a single set of full probability, convexity and lower semicontinuity of every $g_i(\cdot,\xi)$. The set $X$ is nonempty, closed and convex, contained in $C$; the cone is closed and pointed. No moment condition, Slater point, unique solution, finite-support restriction or optimality certificate is part of these assumptions. In particular A3 is not included.
--
--   **Formalization Note.** Euclidean coordinates are finite real functions, and the positive number of constraints is encoded as $I+1$. The law of the source random vector replaces its underlying probability space; all subsequent random decisions remain functions of $\xi$, as in the source. The cone uses Mathlib's `ConvexCone` rather than reimplementing its algebra. The common almost-sure set is expressed before the universal constraint index.
-- source:
--   Nan Jiang and Weijun Xie, ALSO-X and ALSO-X+: Better Convex Approximations for Chance Constrained Programs, arXiv:2012.04763v4 (14 October 2021), https://arxiv.org/abs/2012.04763v4, pp. 1–2, (1), A1–A2; p. 12, section 3 opening

import Mathlib

open MeasureTheory

namespace JiangALSOX.Dominance

structure Model (n m I : ℕ) where
  Ξ : Set (Fin m → ℝ)
  P : Measure Ξ
  gi : Fin (I + 1) → (Fin n → ℝ) → Ξ → ℝ
  X : Set (Fin n → ℝ)
  C : ConvexCone ℝ (Fin n → ℝ)
  c : Fin n → ℝ
  ε : ℝ

noncomputable def loss {n m I : ℕ} (D : Model n m I) (x : Fin n → ℝ) (ξ : D.Ξ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => D.gi i x ξ)

def Assumptions {n m I : ℕ} (D : Model n m I) : Prop :=
  IsProbabilityMeasure D.P ∧ 0 < D.ε ∧ D.ε < 1 ∧
  (∀ i x, Measurable (D.gi i x)) ∧
  (∀ᵐ ξ ∂D.P, ∀ i, ConvexOn ℝ Set.univ (fun x => D.gi i x ξ) ∧
    LowerSemicontinuous (fun x => D.gi i x ξ)) ∧
  D.X.Nonempty ∧ IsClosed D.X ∧ Convex ℝ D.X ∧ D.X ⊆ D.C ∧
  IsClosed (D.C : Set (Fin n → ℝ)) ∧
  (∀ x : Fin n → ℝ, x ∈ D.C → -x ∈ D.C → x = 0)

end JiangALSOX.Dominance


