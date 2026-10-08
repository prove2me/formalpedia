-- Prove2me | Definitions.Def_ReflectedBSDE_Obstacle_Data
-- name    : ReflectedBSDE_Obstacle_Data
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:11:53.647507+00:00
-- url     : https://prove2.me/theorems/aec71785-9a97-468c-bb46-8db2a2acd5b0
-- title:
--   Section 8 obstacle-problem data
-- statement:
--   Fix a positive horizon $T$ and a positive spatial dimension $d$. The data consist of a drift $b(t,x)$, diffusion matrix $\sigma(t,x)$, generator $f(t,x,y,z)$, terminal value $g(x)$, and obstacle $h(t,x)$ on $[0,T]\times\mathbb R^d$. The coefficients are continuous; $b$ and $\sigma$ are uniformly Lipschitz in $x$. The function $g$ has polynomial growth. For some $K>0$ and integer $p$, the generator and obstacle satisfy the paper's conditions (20)–(22):
--
--   $$
--   |f(t,x,0,0)|\le K(1+|x|^p),\quad |f(t,x,y,z)-f(t,x,y',z')|\le K(|y-y'|+|z-z'|),\quad h(t,x)\le K(1+|x|^p).
--   $$
--
--   The compatibility condition is $h(T,x)\le g(x)$ for every $x$. These assumptions are shared by the viscosity definitions and uniqueness theorem.
--
--   **Formalization Note** The finite-dimensional sup norm appears in existential growth and Lipschitz bounds; equivalence of norms permits a change in their existential constants.
-- source:
--   El Karoui, Kapoudjian, Pardoux, Peng & Quenez, Reflected solutions of backward SDE's, and related obstacle problems for PDE's, Ann. Probab. 25(2) (1997), pp. 726–727, §8, assumptions preceding (20)–(23)

import Mathlib

open MeasureTheory Filter Topology
open scoped NNReal

namespace ReflectedBSDE.Obstacle

/-- The continuous coefficients and standing growth and Lipschitz assumptions of §8.
The finite-dimensional sup norm is used in bounds; its equivalence to the Euclidean
norm leaves the paper's existential constants unchanged. -/
structure Data (d : ℕ) where
  T : ℝ≥0
  T_pos : 0 < T
  b : ℝ≥0 → (Fin d → ℝ) → (Fin d → ℝ)
  sigma : ℝ≥0 → (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ
  f : ℝ≥0 → (Fin d → ℝ) → ℝ → (Fin d → ℝ) → ℝ
  g : (Fin d → ℝ) → ℝ
  h : ℝ≥0 → (Fin d → ℝ) → ℝ
  b_cont : ContinuousOn (fun z : ℝ≥0 × (Fin d → ℝ) => b z.1 z.2)
    (Set.Icc 0 T ×ˢ Set.univ)
  sigma_cont : ContinuousOn (fun z : ℝ≥0 × (Fin d → ℝ) => sigma z.1 z.2)
    (Set.Icc 0 T ×ˢ Set.univ)
  f_cont : ContinuousOn
    (fun z : ℝ≥0 × ((Fin d → ℝ) × (ℝ × (Fin d → ℝ))) =>
      f z.1 z.2.1 z.2.2.1 z.2.2.2)
    (Set.Icc 0 T ×ˢ Set.univ)
  g_cont : Continuous g
  h_cont : ContinuousOn (fun z : ℝ≥0 × (Fin d → ℝ) => h z.1 z.2)
    (Set.Icc 0 T ×ˢ Set.univ)
  g_growth : ∃ C : ℝ, 0 ≤ C ∧ ∃ k : ℕ,
    ∀ x, |g x| ≤ C * (1 + ‖x‖ ^ k)
  coeff_bounds : ∃ K : ℝ, 0 < K ∧ ∃ p : ℕ,
    (∀ t ≤ T, ∀ x y : Fin d → ℝ,
      ‖b t x - b t y‖ ≤ K * ‖x - y‖ ∧
      (∀ i j, |sigma t x i j - sigma t y i j| ≤ K * ‖x - y‖)) ∧
    (∀ t ≤ T, ∀ x : Fin d → ℝ, |f t x 0 0| ≤ K * (1 + ‖x‖ ^ p)) ∧
    (∀ t ≤ T, ∀ x : Fin d → ℝ, ∀ y y' : ℝ, ∀ z z' : Fin d → ℝ,
      |f t x y z - f t x y' z'| ≤ K * (|y - y'| + ‖z - z'‖)) ∧
    (∀ t ≤ T, ∀ x : Fin d → ℝ, h t x ≤ K * (1 + ‖x‖ ^ p))
  terminal : ∀ x, h T x ≤ g x

end ReflectedBSDE.Obstacle


