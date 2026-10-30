-- Prove2me | Definitions.Def_NestedLogitAssort_General_obj31
-- name    : NestedLogitAssort_General_obj31
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:47:19.510616+00:00
-- url     : https://prove2.me/theorems/1d59285e-7a59-4d35-a56e-c3affa9b448d
-- title:
--   Objective of problem (31)
-- statement:
--   For a nest $i$, a vector $z\in[0,1]^n$ and numbers $x$, $y$, $b$, this is
--
--   $$
--   \sum_{j\in N}r_{ij}v_{ij}z_j-b\,x\Bigl(v_{i0}+\sum_{j\in N}v_{ij}z_j\Bigr)-b\,y\Bigl(v_{i0}+\sum_{j\in N}v_{ij}z_j\Bigr)^{1-\gamma_i},
--   $$
--
--   the objective of problem (31) in Case 2 of the proof of Theorem 11, where $b=\beta$, $x=\hat x$ and $y=\hat y_i$. For the 0–1 vector of $S$ it is $V_i(S)^{1-\gamma_i}\bigl[V_i(S)^{\gamma_i}(R_i(S)-bx)-by\bigr]$.
--
--   **Formalization Note** Real power; the theorems using it assume $v_{i0}>0$, so the base is positive.
-- source:
--   Davis, Gallego & Topaloglu, Assortment Optimization under Variants of the Nested Logit Model, revised manuscript of June 18, 2013, proof of Theorem 11 (Appendix A.4), Case 2, eq. (31), p. 48

import Mathlib
import Definitions.Def_NestedLogitAssort_General_Instance

namespace NestedLogitAssort.General

/-- **The objective of problem (31).**
Davis, Gallego & Topaloglu, *Assortment Optimization under Variants of the Nested Logit Model*,
revised manuscript of June 18, 2013, proof of Theorem 11 (Appendix A.4), Case 2, eq. (31), p. 48:
`∑_{j ∈ N} r_{ij} v_{ij} z_{ij} − b x (v_{i0} + ∑_{j ∈ N} v_{ij} z_{ij}) − b y (v_{i0} + ∑_{j ∈ N} v_{ij} z_{ij})^{1−γ_i}`,
for `z_i ∈ [0, 1]^n`. The page has `b = β`, `x = x̂` and `y = ŷ_i`.

**Formalization Note.** `Real.rpow`; the theorems using `obj31` take `v_{i0} > 0`, so the base is
positive. -/
noncomputable def obj31 {M : Type*} {n : ℕ} (I : Instance M n) (i : M) (z : Fin n → ℝ)
    (x y b : ℝ) : ℝ :=
  ∑ j, I.r i j * I.v i j * z j - b * x * (I.w0 i + ∑ j, I.v i j * z j) -
    b * y * (I.w0 i + ∑ j, I.v i j * z j) ^ (1 - I.γ i)

end NestedLogitAssort.General


