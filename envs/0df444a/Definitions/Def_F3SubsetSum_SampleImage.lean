-- Prove2me | Definitions.Def_F3SubsetSum_SampleImage
-- name    : F3SubsetSum_SampleImage
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:29:38.938085+00:00
-- url     : https://prove2.me/theorems/54b9119c-a851-4076-9e30-271bb6a4db96
-- title:
--   The sample images $V_t$, missing dimensions $h_t$ and increments $X_t$ (eqs. (39)–(40))
-- statement:
--   For samples $a_1,\dots,a_t\in K^n$ with linear forms $L_i=\langle a_i,x\rangle$ and $D\ge2$, let
--
--   $$
--   V_t=\sum_{i=1}^tL_i^2R_{D-2}\subseteq R_D,\qquad h_t=\dim R_D-\dim V_t ,
--   $$
--
--   the image of $\Phi_{t,D}$ and its codimension. For a new sample $a_{t+1}$ the **increment** is $X_{t+1}=\dim V_{t+1}-\dim V_t=h_t-h_{t+1}$. $\Phi_{m,D}$ is surjective exactly when $h_m=0$; the martingale argument of Theorem 4.12 tracks $h_t$.
--
--   **Formalization Note** A history is `a : Fin t → Fin n → K`; the new sample is appended with `Fin.snoc`.
-- source:
--   Kothari, Metger, O'Donnell, Shutty, Wu, Exponential quantum speedup for F_3^n-Subset-Sum? Or, rigorous classical algorithms for Binary-Error LWE, arXiv:2609.40321v1, §4.4, eqs. (39)–(40), p.24

import Mathlib
import Definitions.Def_F3SubsetSum_TruncatedRing

namespace F3SubsetSum

variable {K : Type*} [Field K] {n : ℕ} (q : ℕ)

/-- **The image after `t` samples** `V_t = Σ_{i≤t} L_i² R_{D−2} ⊆ R_D` (Kothari, Metger,
O'Donnell, Shutty, Wu, arXiv:2609.40321v1, eq. (39), p.24), for the linear forms
`L_i = ⟨a_i, x⟩` of the first `t` samples `a : Fin t → Kⁿ`: the image of `Φ_{t,D}`. -/
noncomputable def sampleImage {t : ℕ} (a : Fin t → Fin n → K) (D : ℕ) :
    Submodule K (Rd K n q D) :=
  LinearMap.range (Phi K q a D)

/-- **The missing dimension** `h_t = dim(R_D) − dim(V_t)` (eq. (39), p.24). -/
noncomputable def missingDim {t : ℕ} (a : Fin t → Fin n → K) (D : ℕ) : ℕ :=
  Module.finrank K (Rd K n q D) - Module.finrank K (sampleImage q a D)

/-- **The increment of sample `t`** `X_t = dim(V_t) − dim(V_{t−1}) = h_{t−1} − h_t`
(eq. (40), p.24), for the history `a = (a_1, …, a_{t−1})` and the new sample `a' = a_t`. -/
noncomputable def increment {t : ℕ} (a : Fin t → Fin n → K) (a' : Fin n → K) (D : ℕ) : ℕ :=
  missingDim q a D - missingDim q (Fin.snoc a a') D

end F3SubsetSum


