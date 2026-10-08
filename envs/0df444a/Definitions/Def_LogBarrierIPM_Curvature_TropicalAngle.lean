-- Prove2me | Definitions.Def_LogBarrierIPM_Curvature_TropicalAngle
-- name    : LogBarrierIPM_Curvature_TropicalAngle
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T01:12:15.513102+00:00
-- url     : https://prove2.me/theorems/b45ed05e-9202-4928-9744-f469902b75bd
-- title:
--   Tropical maximum and arg max on $\mathbb T^d$, the conditions of Lemma 23, and the weak tropical angle $\angle^*UVW$
-- statement:
--   Let $\mathbb T=\mathbb R\cup\{-\infty\}$ and $d\ge0$. For $U\in\mathbb T^d$ write $\max_{i\in[d]}U_i\in\mathbb T$ for its largest coordinate ($-\infty$ when $d=0$) and $\arg\max_{i\in[d]}U_i$ for the set of coordinates attaining it.
--
--   Three points $U,V,W\in\mathbb T^d$ **satisfy the conditions of Lemma 23** when
--   $$\max_{i\in[d]}U_i<\max_{i\in[d]}V_i<\max_{i\in[d]}W_i\quad\text{and}\quad \arg\max_{i\in[d]}V_i\cap\arg\max_{i\in[d]}W_i=\emptyset .$$
--   The **(weak) tropical angle** is
--   $$\angle^*UVW=\begin{cases}\pi/2&\text{if }U,V,W\text{ satisfy the conditions of Lemma 23},\\ 0&\text{otherwise.}\end{cases}$$
--
--   By Lemma 23, $\angle^*$ is a lower estimate of the limiting turning angle of three points over $\mathbb K$ whose valuations are $U,V,W$; summed along the tropical central path it bounds the total curvature of the classical central paths from below.
--
--   **Formalization Note** $\mathbb T$ is `WithBot ℝ`; the maximum is `Finset.univ.sup` and the arg max a `Set (Fin d)`.
-- source:
--   Allamigeon, Benchimol, Gaubert, Joswig, Log-Barrier Interior Point Methods Are Not Strongly Polynomial, arXiv:1708.01544v2, p. 22 (Lemma 23 hypotheses; weak tropical angle ∠*UVW)

import Mathlib

namespace LogBarrierIPM.Curvature

/-- `max_{i ∈ [d]} U_i` for a tropical vector `U ∈ 𝕋^d`, `𝕋 = ℝ ∪ {−∞}` (`−∞` for `d = 0`). -/
noncomputable def tmax {d : ℕ} (U : Fin d → WithBot ℝ) : WithBot ℝ :=
  Finset.univ.sup U

/-- `arg max_{i ∈ [d]} U_i`: the set of coordinates attaining the maximum. -/
def targmax {d : ℕ} (U : Fin d → WithBot ℝ) : Set (Fin d) :=
  {i | U i = tmax U}

/-- The conditions of Lemma 23 (p. 22) on `U, V, W ∈ 𝕋^d`:
`max_i U_i < max_i V_i < max_i W_i`, and `arg max_i V_i`, `arg max_i W_i` are disjoint. -/
def Lemma23Condition {d : ℕ} (U V W : Fin d → WithBot ℝ) : Prop :=
  tmax U < tmax V ∧ tmax V < tmax W ∧ Disjoint (targmax V) (targmax W)

/-- The (weak) tropical angle (p. 22): `∠*UVW = π/2` if `U, V, W` satisfy the conditions of
Lemma 23, and `0` otherwise. -/
noncomputable def weakTropicalAngle {d : ℕ} (U V W : Fin d → WithBot ℝ) : ℝ :=
  open Classical in
  if Lemma23Condition U V W then Real.pi / 2 else 0

end LogBarrierIPM.Curvature


