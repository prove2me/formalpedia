-- Prove2me | Definitions.Def_UnitCircleCyclicAngleData
-- name    : UnitCircleCyclicAngleData
-- status  : Definition
-- author  : @moona3k
-- created : 2026-10-04T17:28:39.826979+00:00
-- url     : https://prove2.me/theorems/bec15e4b-d7af-456f-9d03-8f4efbd4dad6
-- title:
--   Unit Circle Cyclic Angle Data
-- statement:
--   For a point $p\in\mathbb R^2$ and a finite set
--   $S\subset\mathbb R^2$, $\operatorname{UnitCircleCyclicAngleData}(p,S)$
--   is the following cyclic angular data on the points of $S$.  It consists of a
--   successor map $\sigma:S\to S$, a starting angle $\theta_x\in\mathbb R$ and
--   a lifted terminal angle $\Theta_x\in\mathbb R$ for every $x\in S$, such
--   that:
--   $$
--     \sigma \text{ is bijective},\qquad x\ne\sigma(x)\quad (x\in S),
--   $$
--   and the unordered endpoint pair determines the starting point,
--   $$
--     \{x,\sigma(x)\}=\{y,\sigma(y)\}\Longrightarrow x=y .
--   $$
--   Every starting angle lies in the fundamental interval,
--   $$
--     0\le \theta_x<2\pi,
--   $$
--   and the start and terminal endpoint are represented by the corresponding
--   unit-circle coordinates about $p$:
--   $$
--     x=p+(\cos\theta_x,\sin\theta_x),\qquad
--     \sigma(x)=p+(\cos\Theta_x,\sin\Theta_x).
--   $$
--   The terminal lift is compatible with the successor's fundamental angle,
--   $$
--     \Theta_x=\theta_{\sigma(x)}
--     \quad\text{or}\quad
--     \Theta_x=\theta_{\sigma(x)}+2\pi,
--   $$
--   and the lifted gap is positive and shorter than a full turn,
--   $$
--     \theta_x<\Theta_x<\theta_x+2\pi .
--   $$
--   Finally, the open lifted gaps encode cyclic consecutiveness: for every
--   $x,y\in S$ and $0<t<1$,
--   $$
--     y\ne p+\bigl(\cos((1-t)\theta_x+t\Theta_x),
--                  \sin((1-t)\theta_x+t\Theta_x)\bigr),
--   $$
--   and for distinct $x,y\in S$ and $0<s,t<1$, the two open-gap points
--   $$
--     p+\bigl(\cos((1-s)\theta_x+s\Theta_x),
--             \sin((1-s)\theta_x+s\Theta_x)\bigr)
--     \quad\text{and}\quad
--     p+\bigl(\cos((1-t)\theta_y+t\Theta_y),
--             \sin((1-t)\theta_y+t\Theta_y)\bigr)
--   $$
--   are distinct.
--
--   **Formalization Note** This node is ported from the Trellis formalization of the crossing lemma and its consequences ([wpegden/crossing-consequences](https://github.com/wpegden/crossing-consequences), commit `8769d142`, W. Pegden, Apache-2.0); the statement is the Trellis node `UnitCircleCyclicAngleData`.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/UnitCircleCyclicAngleData.lean#L1-L74

import Definitions.Def_UnitCircle

open Classical
noncomputable section

-- [TABLET NODE: UnitCircleCyclicAngleData]
structure UnitCircleCyclicAngleData
    (p : EuclideanSpace ℝ (Fin 2))
    (S : Finset (EuclideanSpace ℝ (Fin 2))) where
-- BODY
  succ :
    {x : EuclideanSpace ℝ (Fin 2) // x ∈ S} →
      {x : EuclideanSpace ℝ (Fin 2) // x ∈ S}
  startAngle : {x : EuclideanSpace ℝ (Fin 2) // x ∈ S} → ℝ
  endAngle : {x : EuclideanSpace ℝ (Fin 2) // x ∈ S} → ℝ
  succ_bijective : Function.Bijective succ
  succ_ne :
    ∀ x : {x : EuclideanSpace ℝ (Fin 2) // x ∈ S}, x.1 ≠ (succ x).1
  endpoint_unique :
    ∀ x y : {x : EuclideanSpace ℝ (Fin 2) // x ∈ S},
      (Sym2.mk x.1 (succ x).1 :
          Sym2 (EuclideanSpace ℝ (Fin 2))) =
        Sym2.mk y.1 (succ y).1 →
      x = y
  start_mem_fundamental :
    ∀ x : {x : EuclideanSpace ℝ (Fin 2) // x ∈ S},
      0 ≤ startAngle x ∧ startAngle x < 2 * Real.pi
  start_point :
    ∀ x : {x : EuclideanSpace ℝ (Fin 2) // x ∈ S},
      x.1 =
        p + WithLp.toLp 2
          (fun i : Fin 2 =>
            if i = 0 then Real.cos (startAngle x) else Real.sin (startAngle x))
  end_point :
    ∀ x : {x : EuclideanSpace ℝ (Fin 2) // x ∈ S},
      (succ x).1 =
        p + WithLp.toLp 2
          (fun i : Fin 2 =>
            if i = 0 then Real.cos (endAngle x) else Real.sin (endAngle x))
  end_lift :
    ∀ x : {x : EuclideanSpace ℝ (Fin 2) // x ∈ S},
      endAngle x = startAngle (succ x) ∨
        endAngle x = startAngle (succ x) + 2 * Real.pi
  gap_pos :
    ∀ x : {x : EuclideanSpace ℝ (Fin 2) // x ∈ S},
      startAngle x < endAngle x
  gap_short :
    ∀ x : {x : EuclideanSpace ℝ (Fin 2) // x ∈ S},
      endAngle x < startAngle x + 2 * Real.pi
  no_S_in_open_gap :
    ∀ (x y : {x : EuclideanSpace ℝ (Fin 2) // x ∈ S}) (t : ℝ),
      0 < t → t < 1 →
        y.1 ≠
          p + WithLp.toLp 2
            (fun i : Fin 2 =>
              if i = 0 then
                Real.cos ((1 - t) * startAngle x + t * endAngle x)
              else
                Real.sin ((1 - t) * startAngle x + t * endAngle x))
  open_gaps_disjoint :
    ∀ (x y : {x : EuclideanSpace ℝ (Fin 2) // x ∈ S}) (s t : ℝ),
      x ≠ y → 0 < s → s < 1 → 0 < t → t < 1 →
        p + WithLp.toLp 2
            (fun i : Fin 2 =>
              if i = 0 then
                Real.cos ((1 - s) * startAngle x + s * endAngle x)
              else
                Real.sin ((1 - s) * startAngle x + s * endAngle x)) ≠
          p + WithLp.toLp 2
            (fun i : Fin 2 =>
              if i = 0 then
                Real.cos ((1 - t) * startAngle y + t * endAngle y)
              else
                Real.sin ((1 - t) * startAngle y + t * endAngle y))


