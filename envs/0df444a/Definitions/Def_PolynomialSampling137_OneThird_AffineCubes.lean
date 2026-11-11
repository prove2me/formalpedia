-- Prove2me | Definitions.Def_PolynomialSampling137_OneThird_AffineCubes
-- name    : PolynomialSampling137_OneThird_AffineCubes
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T10:26:29.107293+00:00
-- url     : https://prove2.me/theorems/69565882-68ce-4dd7-b759-965596521a23
-- title:
--   Labeled affine cubes and coordinate means
-- statement:
--   For a base point $x\in\mathbb F_2^s$, directions $h_1,\ldots,h_t\in\mathbb F_2^s$, and label $v\in\mathbb F_2^t$, put $X_v=x+\sum_jv_jh_j$. Define
--
--   $$C_t(f)=\mathbb E_{x,h_1,\ldots,h_t}\prod_{v\in\mathbb F_2^t}f(X_v),\qquad A_{x,h}(q)=2^{-t}\sum_vq(X_v).$$
--
--   The parameters are independent uniform words. Directions can vanish or be dependent, and repeated image points occur once per label in the product. The cube-gap predicate requires $|A_{x,h}(Q_i)-p|\ge\delta$ for every base point, every direction tuple, and every output coordinate. It imposes no polynomial degree condition. These definitions provide the exact cube conventions for Lemma 2 and Theorem 3.
-- source:
--   Yan Zhong, STOC 2027 submission #137 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/137.pdf, §2.4, printed p. 9 / PDF p. 11; §3.1 Lemma 2 and Theorem 3, printed p. 10 / PDF p. 12

import Definitions.Def_PolynomialSampling137_OneThird_BooleanSources

noncomputable section

namespace PolynomialSampling137.OneThird

/-- Labeled affine cube. Directions may be zero or linearly dependent. -/
def cubeVertex {s t : ℕ} (x : Word s) (h : Fin t → Word s) (v : Word t) : Word s :=
  fun k => x k + ∑ j, v j * h j k

/-- Average product over independent uniform base point and directions.
All labels are retained in the product even when they map to the same point. -/
def cubeAverage {s : ℕ} (t : ℕ) (f : Word s → ℝ) : ℝ :=
  uniformAverage (fun x : Word s =>
    uniformAverage (fun h : Fin t → Word s =>
      ∏ v : Word t, f (cubeVertex x h v)))

/-- Empirical mean over all labels of one cube. -/
def cubeMean {s t : ℕ} (q : Word s → ZMod 2) (x : Word s)
    (h : Fin t → Word s) : ℝ :=
  uniformAverage (fun v : Word t => bitReal (q (cubeVertex x h v)))

/-- Every coordinate of every labeled affine t-cube has the stated gap. -/
def CubeGap {s n : ℕ} (t : ℕ) (p δ : ℝ) (Q : Word s → Word n) : Prop :=
  ∀ (x : Word s) (h : Fin t → Word s) (i : Fin n),
    δ ≤ |cubeMean (fun z => Q z i) x h - p|

end PolynomialSampling137.OneThird


