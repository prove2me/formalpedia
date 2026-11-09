-- Prove2me | Definitions.Def_CondGeoVerif_projClass
-- name    : CondGeoVerif_projClass
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:14:50.446391+00:00
-- url     : https://prove2.me/theorems/e6c00753-62ac-44e4-8d80-e1727fb7a033
-- title:
--   Feature space $\mathbb R^n$, Gaussian law, matrix action, Frobenius and operator norms, projection classes $\mathcal H_{F,d}$
-- statement:
--   Features are vectors of $\mathbb R^n$ with the Euclidean norm, and $\gamma_n=N(0,I_n)$ denotes the standard Gaussian law on $\mathbb R^n$. A real matrix $W\in\mathbb R^{m\times n}$ acts on $\mathbb R^n$ by $x\mapsto Wx$. The **Frobenius norm** is $\|W\|_F=(\sum_{i,j}W_{ij}^2)^{1/2}$ and the **operator norm** is $\|M\|_{\mathrm{op}}=\sup_{\|v\|\le1}\|Mv\|$. The **coordinate frame** $[I_k;0]\in\mathbb R^{d\times k}$ has entries $1$ on the diagonal and $0$ elsewhere, so $[I_k;0]^\top x=(x_1,\dots,x_k)$.
--
--   A **rule** is a function $f:\mathbb R^k\to\{-1,1\}$. For an orthonormal $k$-frame $W\in\mathbb R^{d\times k}$ ($W^\top W=I_k$, $d\ge k$), the **projection predictor** is $h_W(x)=f(W^\top x)$. For a family $F$ of rules, the **projection class** in dimension $d$ is
--   $$\mathcal H_{F,d}=\bigcup_{f\in F}\{x\mapsto f(W^\top x):W\in\mathbb R^{d\times k},\ W^\top W=I_k\}.$$
--   A singleton $F=\{f\}$ gives the fixed-rule class $\mathcal H_{f,d}$.
--
--   These classes are the hypothesis classes of every verification problem in the mission.
--
--   **Formalization Note** Labels are Booleans, with `true` for $+1$. Frames are the published Stiefel set `ProjLikeRetr.Stiefel.stiefel`; it is empty for $d<k$, and every statement assumes $d\ge k$ as the paper does. Borel measurability of the rules is a separate hypothesis of each statement.
-- source:
--   T. Y. Chen, The Conditional Geometry of Statistical Verification, manuscript (October 2026, STOC 2027 submission, sha256 07a66d18…), §2 "Projection classes and basic identities", p.4 (PDF p.7)

import Mathlib
import Definitions.Def_ProjLikeRetr_Stiefel_stiefel

set_option autoImplicit false

namespace CondGeoVerif

open MeasureTheory ProbabilityTheory ProjLikeRetr.Stiefel
open scoped Matrix

/-- Feature vectors `ℝⁿ`, as the Euclidean space `EuclideanSpace ℝ (Fin n)` (T. Y. Chen, *The
Conditional Geometry of Statistical Verification*, manuscript, October 2026, sha256 07a66d18…,
§2, p.3 = PDF p.6). -/
abbrev Vec (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The standard Gaussian law `N(0, I_n)` on `ℝⁿ` (Chen, Oct. 2026, §2, p.4: "Sections 3 and 4
assume X ∼ N(0, I_d)"). -/
noncomputable abbrev gauss (n : ℕ) : Measure (Vec n) := stdGaussian (Vec n)

/-- A real `m × n` matrix acting on `ℝⁿ`: `x ↦ W x`. -/
noncomputable def matVec {m n : ℕ} (W : Matrix (Fin m) (Fin n) ℝ) (x : Vec n) : Vec m :=
  WithLp.toLp 2 (W *ᵥ WithLp.ofLp x)

/-- The Frobenius norm `‖W‖_F = (∑_{i,j} W_{ij}²)^{1/2}` (Chen, Oct. 2026, §2, p.4). -/
noncomputable def frob {m n : ℕ} (W : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  Real.sqrt (∑ i, ∑ j, W i j ^ 2)

/-- The operator norm `‖M‖_op = sup_{‖v‖ ≤ 1} ‖M v‖` for the Euclidean norms (Chen, Oct. 2026,
§2, p.4). The supremum is over a nonempty set bounded by the Frobenius norm. -/
noncomputable def opNorm {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  ⨆ v : {v : Vec n // ‖v‖ ≤ 1}, ‖matVec M v.1‖

/-- The coordinate frame `[I_k; 0] ∈ ℝ^{d×k}`: its `(i, j)` entry is `1` when `i = j` and `0`
otherwise. Then `(coordFrame d k)ᵀ x = (x₁, …, x_k)` are the first `k` coordinates. -/
def coordFrame (d k : ℕ) : Matrix (Fin d) (Fin k) ℝ :=
  fun i j => if (i : ℕ) = (j : ℕ) then 1 else 0

/-- The projection predictor `h_W(x) = f(Wᵀ x)` of a rule `f : ℝᵏ → {−1, 1}` and a frame
`W ∈ ℝ^{d×k}`; labels are `Bool`, with `true` for `+1`. -/
noncomputable def frameRule {d k : ℕ} (f : Vec k → Bool) (W : Matrix (Fin d) (Fin k) ℝ) :
    Vec d → Bool :=
  fun x => f (matVec Wᵀ x)

/-- **Projection classes** (Chen, *The Conditional Geometry of Statistical Verification*,
manuscript, October 2026, sha256 07a66d18…, §2 "Projection classes and basic identities", p.4 =
PDF p.7): for a family `F` of rules `ℝᵏ → {−1, 1}`,
`H_{F,d} = ⋃_{f ∈ F} {x ↦ f(Wᵀx) : W ∈ ℝ^{d×k}, WᵀW = I_k}`. A singleton `F = {f}` gives
`H_{f,d}`.

**Formalization Note** Labels are `Bool` (`true` ↔ `+1`). Frames are the published Stiefel set
`ProjLikeRetr.Stiefel.stiefel d k = {W | Wᵀ W = I_k}`; it is empty for `d < k`, and every
statement of the mission assumes `d ≥ k` as the paper does. Borel measurability of the rules is a
separate hypothesis of each statement. -/
def projClass {k : ℕ} (F : Set (Vec k → Bool)) (d : ℕ) : Set (Vec d → Bool) :=
  {h | ∃ f ∈ F, ∃ W ∈ stiefel d k, h = frameRule f W}

end CondGeoVerif


