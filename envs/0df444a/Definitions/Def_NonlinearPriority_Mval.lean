-- Prove2me | Definitions.Def_NonlinearPriority_Mval
-- name    : NonlinearPriority_Mval
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:22:37.42275+00:00
-- url     : https://prove2.me/theorems/a00db63d-875a-4d2f-9d25-a63b79ded1e9
-- title:
--   The ratio $M^\gamma_i$, (4)
-- statement:
--   For a type $i\in\{k,k+1\}$ and $\gamma\in\{\pi_k,\pi_{k+1}\}$,
--   $$M^\gamma_i\equiv\frac{\mathbb E[(W^{\bar\pi_k}_i)^2]-\mathbb E[(W^\gamma_i)^2]}{\mathbb E[W^{\bar\pi_k}_i]-\mathbb E[W^\gamma_i]}.\tag{4}$$
--   It is the change in the second moment of the steady-state waiting time of type $i$ per change in its mean when switching from $\gamma$ to $\bar\pi_k$; under quadratic costs $\delta^\gamma_i=c^{(2)}_iM^\gamma_i+c^{(1)}_i$.
--
--   **Formalization Note** The paper writes $W^{\bar\pi_k}$ without a type subscript because the laws of types $k$ and $k+1$ under $\bar\pi_k$ coincide; the type-$i$ law is used here. The value is junk if a second moment is infinite or the means coincide.
-- source:
--   Ouyang–Argon–Ziya, Assigning Priorities (or Not), Management Science (2021, Articles in Advance), doi:10.1287/mnsc.2020.3952, (4), p.5 (PDF 6)

import Mathlib
import Definitions.Def_NonlinearPriority_piBar

open MeasureTheory

namespace NonlinearPriority

variable {K : ℕ}

/-- **`M^γ_i`, (4)** (§5, p. 5, PDF 6). Ouyang, Argon and Ziya, Management Science (2021),
doi:10.1287/mnsc.2020.3952:

`M^γ_i ≡ (E[(W^{π̄k})²] − E[(W^γ_i)²]) / (E[W^{π̄k}] − E[W^γ_i])` for `i ∈ {k, k+1}`,
`γ ∈ {πk, πk+1}`.

**Formalization Note.** The paper drops the type subscript of `W^{π̄k}` "because W^{π̄k}_k and
W^{π̄k}_{k+1} are identical"; here the type-`i` law under `π̄_k` is used, which is the literal
`δ^{γ,π̄k}_i` of (3). Real division and Bochner integrals: the value is junk if a second moment is
infinite or the means coincide; statements using `Mval` assume finite moments. -/
noncomputable def Mval (w : (Fin K → ℕ) → Fin K → ProbabilityMeasure ℝ) (k : ℕ)
    (γ : Fin K → ℕ) (i : Fin K) : ℝ :=
  ((∫ x, x ^ 2 ∂(w (piBar k) i : Measure ℝ)) - ∫ x, x ^ 2 ∂(w γ i : Measure ℝ)) /
    ((∫ x, x ∂(w (piBar k) i : Measure ℝ)) - ∫ x, x ∂(w γ i : Measure ℝ))

end NonlinearPriority


