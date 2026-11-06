-- Prove2me | Definitions.Def_TemporalVoter_metaphaseIndex
-- name    : TemporalVoter_metaphaseIndex
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:11:45.630645+00:00
-- url     : https://prove2.me/theorems/aba14bdd-185a-4afc-8f8f-b2e14111ff73
-- title:
--   Phases $t_r$ and metaphase boundaries $R_\alpha$ in the proof of Theorem 1.3
-- statement:
--   In the proof of Theorem 1.3, fix $B>0$, interval lengths $\Delta_j\ge1$ and reals $\phi_j\in[0,1]$, and let $r_{\max}=\lfloor Bm/d_{\min}\rfloor$.
--
--   1. $\ell_r=\min\{\ell:\sum_{j=0}^{\ell-1}\phi_j\ge r\}$ (so $\ell_0=0$) and $t_r=I^-_{\ell_r}=\Delta_0+\dots+\Delta_{\ell_r-1}$; the $r$-th **phase** is $[t_r,t_{r+1}-1]$.
--   2. $\mathcal O(t)$ is the set of opinions present at time $t$, and $\kappa=|\mathcal O(0)|$ is the number of opinions present in the model.
--   3. $R_0=0$ and, for $\alpha\ge1$,
--   $$R_\alpha=\min\Bigl(\{r_{\max}\}\cup\bigl\{r:\ |\mathcal O(t_r)|\le(5/6)^\alpha\kappa\vee1\bigr\}\Bigr),$$
--   where $\vee$ is the maximum. The $\alpha$-th **metaphase** is $[t_{R_\alpha},t_{R_{\alpha+1}}-1]$.
--
--   Metaphases group phases until the number of surviving opinions has dropped by a further factor $5/6$; they are the random time scale on which the multi-opinion bound is reduced to the two-opinion bound.
--
--   **Formalization Note** $\ell_r$ is an infimum in $\mathbb N$; it is the stated minimum whenever the partial sums of $\phi$ reach $r$, which the statements using it assume for $r\le r_{\max}$. $R_\alpha$ is a function of the path; the minimum over $r$ is taken with `Nat.find` over $r\in\mathbb N$ and is at most $r_{\max}$.
-- source:
--   Rocha Avila, Dell, Lapinskas, Temporal Conductance and Bounds on the Voter Model for Dynamic Networks, arXiv:2606.13374 (2 Nov 2026), proof of Theorem 1.3, p.24

import Mathlib
import Definitions.Def_TemporalVoter_temporalConductance

open scoped Classical

namespace TemporalVoter

variable {V : Type} [Fintype V]

/-- The set `O(x)` of opinions present in the state `x` (proof of Theorem 1.3, p.24). -/
def opinionsPresent {k : ℕ} (x : V → Fin k) : Finset (Fin k) :=
  Finset.univ.image x

/-- `ℓ_r = min{ℓ : ∑_{j=0}^{ℓ−1} φ_j ≥ r}` (proof of Theorem 1.3, p.24); `ℓ_0 = 0`.

**Formalization Note** `sInf` in `ℕ`; it is the paper's minimum whenever the partial sums reach `r`,
which every statement using it assumes for `r ≤ r_max`. -/
noncomputable def phaseIndex (φ : ℕ → ℝ) (r : ℕ) : ℕ :=
  sInf {ℓ | (r : ℝ) ≤ ∑ j ∈ Finset.range ℓ, φ j}

/-- The start `t_r = I⁻_{ℓ_r} = Δ_0 + ⋯ + Δ_{ℓ_r − 1}` of the `r`-th phase (p.24); `t_0 = 0`. -/
noncomputable def phaseStart (Δ : ℕ → ℕ) (φ : ℕ → ℝ) (r : ℕ) : ℕ :=
  Iminus Δ (phaseIndex φ r)

/-- `r_max = ⌊B m / d_min⌋` (proof of Theorem 1.3, p.24). -/
noncomputable def rmax (T : TemporalGraph V) (B : ℝ) : ℕ :=
  ⌊B * T.m / T.dmin⌋₊

/-- The metaphase boundaries `R_α` of the proof of Theorem 1.3 (p.24), on a path `ω` of the
`k`-opinion voter model: `R_0 = 0` and, for `α ≥ 1`,
`R_α = min({r_max} ∪ {r : |O(t_r)| ≤ (5/6)^α κ ∨ 1})`, where `κ = |O(ω 0)|` is the number of
opinions present in the model and `∨` is the maximum.

**Formalization Note** The minimum is `Nat.find` over `r ∈ ℕ` of `r = r_max ∨ |O(t_r)| ≤ …`, which
is at most `r_max`. -/
noncomputable def metaphaseIndex (T : TemporalGraph V) (B : ℝ) (Δ : ℕ → ℕ) (φ : ℕ → ℝ)
    {k : ℕ} (α : ℕ) (ω : ℕ → V → Fin k) : ℕ :=
  if α = 0 then 0 else
    Nat.find (⟨rmax T B, Or.inl rfl⟩ : ∃ r, r = rmax T B ∨
      ((opinionsPresent (ω (phaseStart Δ φ r))).card : ℝ) ≤
        max ((5 / 6 : ℝ) ^ α * (opinionsPresent (ω 0)).card) 1)

end TemporalVoter


