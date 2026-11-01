-- Prove2me | Definitions.Def_ProphetBipartite_algorithm1Step
-- name    : ProphetBipartite_algorithm1Step
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:49:16.814322+00:00
-- url     : https://prove2.me/theorems/10298bf1-deb3-4790-9c79-fdefbf8b82fa
-- title:
--   One round of Algorithm 1 and the errors (18)
-- statement:
--   For real matrices $M,Q$ and real vectors $l,r$ the **approximation errors** of (18) are
--
--   $$
--   \delta_L[i]=l_i-\sum_{j}\big[M_{i,j}-Q_{i,j}(l_i+r_j)\big]^+,\qquad
--   \delta_R[j]=r_j-\sum_{i}\big[M_{i,j}-Q_{i,j}(l_i+r_j)\big]^+ ,
--   $$
--
--   and the combined error is $\|\delta_L\|_1+\|\delta_R\|_1$. One round of **Algorithm 1** corrects the vector with the larger error by half of its error vector:
--
--   $$
--   \text{if }\|\delta_L\|_1\ge\|\delta_R\|_1:\ l\leftarrow l-\tfrac12\delta_L,\qquad\text{else}:\ r\leftarrow r-\tfrac12\delta_R .
--   $$
--
--   Iterating the round drives the error to zero and produces a solution of (17).
--
--   **Formalization Note** Only the update (lines 2–8) is defined; the stopping rule with precision $\varepsilon$ is not. The module defines `deltaL`, `deltaR`, `error17` (the combined error) and `algorithm1Step`.
-- source:
--   Gravin, Wang, Prophet inequality for bipartite matching: merits of being simple and non adaptive, arXiv:1902.06243v1, (18) p.10, Algorithm 1 p.10

import Mathlib

namespace ProphetBipartite

/-- The error vector `δ_L` of (18), p.10: `δ_L[i] = l_i − ∑_{j=1}^{m} [M_{i,j} − Q_{i,j}(l_i + r_j)]⁺`. -/
noncomputable def deltaL {L R : Type*} [Fintype R] (M Q : L → R → ℝ) (l : L → ℝ) (r : R → ℝ)
    (i : L) : ℝ :=
  l i - ∑ j, max (M i j - Q i j * (l i + r j)) 0

/-- The error vector `δ_R` of (18), p.10: `δ_R[j] = r_j − ∑_{i=1}^{n} [M_{i,j} − Q_{i,j}(l_i + r_j)]⁺`. -/
noncomputable def deltaR {L R : Type*} [Fintype L] (M Q : L → R → ℝ) (l : L → ℝ) (r : R → ℝ)
    (j : R) : ℝ :=
  r j - ∑ i, max (M i j - Q i j * (l i + r j)) 0

/-- The combined error `‖δ_L‖₁ + ‖δ_R‖₁` of Algorithm 1 (p.10). -/
noncomputable def error17 {L R : Type*} [Fintype L] [Fintype R] (M Q : L → R → ℝ) (l : L → ℝ)
    (r : R → ℝ) : ℝ :=
  ∑ i, |deltaL M Q l r i| + ∑ j, |deltaR M Q l r j|

/-- **One round of Algorithm 1.** Gravin & Wang, arXiv:1902.06243v1, Algorithm 1, p.10: "we choose
one of `l` or `r` vectors with the larger `L₁`-norm error in (18) and then correct this vector by
subtracting half of its error vector": if `‖δ_L‖₁ ≥ ‖δ_R‖₁` then `l ← l − ½ δ_L`, else
`r ← r − ½ δ_R`.

**Formalization Note.** Only the update rule (lines 2–7) is defined; the stopping rule
`‖δ_L‖₁ + ‖δ_R‖₁ ≤ ε` (line 9) is not part of this definition. -/
noncomputable def algorithm1Step {L R : Type*} [Fintype L] [Fintype R] (M Q : L → R → ℝ)
    (lr : (L → ℝ) × (R → ℝ)) : (L → ℝ) × (R → ℝ) :=
  if ∑ j, |deltaR M Q lr.1 lr.2 j| ≤ ∑ i, |deltaL M Q lr.1 lr.2 i| then
    (fun i => lr.1 i - (1 / 2) * deltaL M Q lr.1 lr.2 i, lr.2)
  else
    (lr.1, fun j => lr.2 j - (1 / 2) * deltaR M Q lr.1 lr.2 j)

end ProphetBipartite


