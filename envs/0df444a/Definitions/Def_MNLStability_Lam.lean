-- Prove2me | Definitions.Def_MNLStability_Lam
-- name    : MNLStability_Lam
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:30:00.346619+00:00
-- url     : https://prove2.me/theorems/f541b518-9caf-4c97-874b-038be8703687
-- title:
--   Intervals $I_\ell$, contributions $R_\ell$, $\ell_{\min}$ and $\Lambda$
-- statement:
--   Setting of §4.3: $U^{\mathrm{step}}$ stocks every product of $I$ at a level of $H$, and $H(1)>H(2)>\dots>H(L)=0$ are the levels, $L=|H|$.
--
--   1. The **interval** $I_\ell$ is the set of products of $I$ stocked at level $H(\ell)$.
--   2. Its **contribution** is $R_\ell=\sum_{i\in I_\ell}r_i\,\mathbb E[X_i^{U^{\mathrm{step}}}]$.
--   3. $\ell_{\min}=\min\{\ell: R_\ell>0\}$; since levels decrease with $\ell$, $I_{\ell_{\min}}$ is the interval of the largest level with positive contribution.
--   4. $\Lambda=\{\ell\in[L]: R_\ell\ge(\varepsilon/L)\,R_{\ell_{\min}}\}$, and $\ell_1<\ell_2<\dots<\ell_{|\Lambda|}$ lists $\Lambda$ by increasing index, i.e. by decreasing level.
--
--   **Formalization Note** Intervals are indexed by their level $h=H(\ell)$ rather than by $\ell$, so "$\ell_1<\ell_2$" reads "$H(\ell_1)>H(\ell_2)$". When no level has $R_\ell>0$, `hMin` is $0$; every statement that uses it assumes some $R_\ell>0$, as the paper's definition of $\ell_{\min}$ does.
-- source:
--   Aouad & Segev, The Stability of MNL-Based Demand under Dynamic Customer Substitution and its Algorithmic Implications, SSRN:3498325 (manuscript of 2019-12-04), §4.3, p.20; §4.4, p.22 (ℓ₁ < ℓ₂ < ⋯)

import Mathlib
import Definitions.Def_MNLStability_expX

namespace MNLStability

variable {n : ℕ}

/-- The interval `I_ℓ` of SSRN:3498325, §4.3, p.20, indexed by its inventory level `h = H(ℓ)`: the
products of `I` stocked at level `h` by `U^step`. -/
def lev (I : Finset (Fin n)) (Ustep : Fin n → ℕ) (h : ℕ) : Finset (Fin n) :=
  I.filter fun i => Ustep i = h

/-- `R_ℓ = Σ_{i ∈ I_ℓ} r_i · E[X_i^{U^step}]`, the contribution of the interval at level `h` to the
expected revenue of `U^step` (p.20). -/
noncomputable def Rlev (wts : Weights n) (r : Fin n → ℝ) (pM : ℕ →₀ ℝ) (I : Finset (Fin n))
    (Ustep : Fin n → ℕ) (h : ℕ) : ℝ :=
  ∑ i ∈ lev I Ustep h, r i * expX wts pM Ustep i

/-- The level `H(ℓ_min)` of the interval `I_{ℓ_min}`, `ℓ_min = min{ℓ ∈ [L] : R_ℓ > 0}` (p.20). Since
`H(1) > ⋯ > H(L)`, the least index is the largest level with `R > 0`.

**Formalization Note.** `0` when no level has `R > 0`; every statement that uses it assumes some
`R_ℓ > 0`, as the paper's definition of `ℓ_min` does. -/
noncomputable def hMin (wts : Weights n) (r : Fin n → ℝ) (pM : ℕ →₀ ℝ) (I : Finset (Fin n))
    (H : Finset ℕ) (Ustep : Fin n → ℕ) : ℕ :=
  (H.filter fun h => 0 < Rlev wts r pM I Ustep h).sup id

/-- `Λ = {ℓ ∈ [L] : R_ℓ ≥ (ε/L) · R_{ℓ_min}}` (p.20), as a set of levels, with `L = |H|`. -/
noncomputable def Lam (wts : Weights n) (r : Fin n → ℝ) (pM : ℕ →₀ ℝ) (I : Finset (Fin n))
    (H : Finset ℕ) (Ustep : Fin n → ℕ) (ε : ℝ) : Finset ℕ :=
  H.filter fun h =>
    ε / H.card * Rlev wts r pM I Ustep (hMin wts r pM I H Ustep) ≤ Rlev wts r pM I Ustep h

/-- The levels of `Λ` in the order `ℓ₁ < ℓ₂ < ⋯ < ℓ_{|Λ|}` of §4.4, p.22, i.e. by decreasing level. -/
noncomputable def lamList (wts : Weights n) (r : Fin n → ℝ) (pM : ℕ →₀ ℝ) (I : Finset (Fin n))
    (H : Finset ℕ) (Ustep : Fin n → ℕ) (ε : ℝ) : List ℕ :=
  ((Lam wts r pM I H Ustep ε).sort (· ≤ ·)).reverse

end MNLStability


