-- Prove2me | Definitions.Def_FourierEntropyApprox_Supplement_avgdegCJ
-- name    : FourierEntropyApprox_Supplement_avgdegCJ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:05:14.535634+00:00
-- url     : https://prove2.me/theorems/b661bd91-ca5e-4b29-b132-b5b5a46c2397
-- title:
--   Conical juntas over affine subspaces and $\mathrm{avgdeg}^{\oplus}_{cj}(f)$
-- statement:
--   A **conical junta over affine subspaces** is a function
--
--   $$h=\sum_{i=1}^m w_i\,\mathbf 1_{C_i},\qquad w_i\ge 0,$$
--
--   with $C_1,\dots,C_m$ nonempty affine subspaces of $\{-1,1\}^n$ that may overlap. It **represents** $f:\{-1,1\}^n\to\{-1,1\}$ if $(1-f)/2=h$ at every point. Its **average conical junta degree** is
--
--   $$\mathrm{avgdeg}^{\oplus}_{cj}(h)=\sum_{i=1}^m w_i\,\operatorname{co-dim}(C_i)\,2^{-\operatorname{co-dim}(C_i)},$$
--
--   and the average conical junta degree of $f$ is the minimum of $\mathrm{avgdeg}^{\oplus}_{cj}(h)$ over all conical juntas $h$ representing $f$. Accordingly $\mathrm{avgdeg}^{\oplus}_{cj}(-f)$ minimizes over representations of $(1+f)/2$.
--
--   Conical juntas over subcubes (conjunctions of literals) are the special case of [GJ16]; an unambiguous certificate is a representation by disjoint cells with unit weights. The measure appears in Theorem 4.5.
--
--   **Formalization Note** Terms are indexed by `Fin m` with real weights. `avgdegCJ f` is the infimum in $\mathbb R$ over exact representations; for Boolean $f$ the set is nonempty (point indicators of $\{f=-1\}$) and bounded below by $0$, and the linear objective attains its infimum on the feasible cone, so this is the paper's minimum.
-- source:
--   Paraashar, Saurabh, Fourier Entropy Bounds via Approximations, arXiv:2611.06451 (held version, sha256 adc9c5fc…), §2, p.13 (Conical Juntas); §1, pp.4–5 (average conical junta degree)

import Mathlib
import Definitions.Def_FourierEntropyApprox_Supplement_cubeSet

set_option autoImplicit false

namespace FourierEntropyApprox

/-!
# Conical juntas over affine subspaces and the average conical junta degree `avgdeg⊕_cj(f)`

M. Paraashar, N. Saurabh, *Fourier Entropy Bounds via Approximations*, arXiv:2611.06451 (held version,
sha256 adc9c5fc…), §2, p.13 ("Let h = ∑ w_C C, a conical junta, be a weighted sum over conjunctions C of
literals with weights w_C ≥ 0. We say that a Boolean function f … is represented by a conical junta h if
g = (1 − f)/2 = h. More generally, we will consider (non-negative) weighted sum over affine subspaces. We
define the average conical junta degree of h, denoted avgdeg⊕_cj(h), equals ∑_C w_C co-dim(C)2^{−co-dim(C)}.
Then, the average conical junta degree of f is avgdeg⊕_cj(f) := min_{h a conical junta} avgdeg⊕_cj(h)"), and
§1, pp.4–5 ("(1 − f)/2 = h = ∑_C w_C 1_C, w_C ≥ 0").

**Formalization Note.**
* A conical junta is `h = ∑_{i<m} wᵢ 1_{Cᵢ}` with nonempty affine subspaces `Cᵢ` (`cubeSet`), indexed by
  `Fin m` (repetitions allowed, which changes neither the represented functions nor the minimum), and real
  weights `wᵢ ≥ 0`. Subcubes (conjunctions of literals) are the special case of the paper's first sentence.
* `h` represents `f` when `(1 − f(x))/2 = h(x)` at every point `x`; so `avgdegCJ (-f)` minimizes over
  representations of `(1 + f)/2`, the paper's `avgdeg⊕_cj(−f)`.
* `avgdegCJ f` is the infimum (`sInf` in `ℝ`) of `∑ᵢ wᵢ co-dim(Cᵢ) 2^{−co-dim(Cᵢ)}`. For Boolean `f` the set is
  nonempty (the point indicators of `{f = −1}`) and bounded below by `0`, and the infimum of this linear
  objective over the feasible cone is attained, so it is the paper's minimum.
-/

namespace Supplement

/-- A conical junta over affine subspaces representing `f` (p.13): nonnegative weights `w` on nonempty
affine subspaces `C` with `(1 − f)/2 = ∑ᵢ wᵢ 1_{Cᵢ}` pointwise. -/
structure ConicalJunta {n : ℕ} (f : Cube n → ℝ) where
  /-- number of terms -/
  m : ℕ
  /-- the affine subspaces, as affine subspaces of `𝔽₂ⁿ` -/
  cell : Fin m → AffineSubspace (ZMod 2) (Fin n → ZMod 2)
  /-- every affine subspace is nonempty -/
  nonempty : ∀ i, (cubeSet (cell i)).Nonempty
  /-- the weights -/
  w : Fin m → ℝ
  /-- the weights are nonnegative -/
  w_nonneg : ∀ i, 0 ≤ w i
  /-- exact representation `(1 − f)/2 = h` -/
  represents : ∀ x, (1 - f x) / 2 = ∑ i, w i * (cubeSet (cell i)).indicator (fun _ => (1 : ℝ)) x

/-- The average conical junta degree `avgdeg⊕_cj(h) = ∑_C w_C co-dim(C) 2^{−co-dim(C)}` (p.13). -/
noncomputable def ConicalJunta.avgdeg {n : ℕ} {f : Cube n → ℝ} (h : ConicalJunta f) : ℝ :=
  ∑ i, h.w i * (codim (h.cell i) : ℝ) * (2 : ℝ)⁻¹ ^ codim (h.cell i)

/-- The average conical junta degree of `f`, `avgdeg⊕_cj(f) = min_h avgdeg⊕_cj(h)` over the conical juntas
representing `f` (p.13). -/
noncomputable def avgdegCJ {n : ℕ} (f : Cube n → ℝ) : ℝ :=
  sInf {c : ℝ | ∃ h : ConicalJunta f, h.avgdeg = c}

end Supplement

end FourierEntropyApprox


