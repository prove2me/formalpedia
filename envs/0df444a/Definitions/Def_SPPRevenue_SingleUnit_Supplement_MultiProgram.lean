-- Prove2me | Definitions.Def_SPPRevenue_SingleUnit_Supplement_MultiProgram
-- name    : SPPRevenue_SingleUnit_Supplement_MultiProgram
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T20:11:12.481388+00:00
-- url     : https://prove2.me/theorems/7f045aa5-7c78-4fe5-a3c3-e3156eef22c0
-- title:
--   Theorem 3 and Lemma 4, pp. 18–20 — f_H, the program (FR-Multi(H)) and the cutoff equation
-- statement:
--   Objects of Theorem 3 and Lemma 4.
--
--   1. **$f_H$.** For $H\ge1$,
--   $$f_H(x)=H-e^{-x}\sum_{i=0}^{H-1}(H-i)\frac{x^i}{i!}.$$
--   2. **(FR-Multi(H)).** A function $s$ on $[0,\infty)$ is feasible when it is weakly decreasing, $0\le s(\tau)\le\min(H,1/\tau)$ for all $\tau\ge0$, and $\int_0^\infty f_H(s(\tau))\,d\tau\le1$. $\mathrm{FR\text{-}Multi}(H)$ is the supremum of $\int_0^\infty s(\tau)\,d\tau$ over feasible $s$.
--   3. **Cutoff equation (Lemma 4).** A number $T$ satisfies
--   $$\int_{1/H}^{T}\Big(H-e^{-1/\tau}\sum_{i=0}^{H-1}\frac{H-i}{\tau^i\,i!}\Big)\,d\tau=\frac{H^H}{H!\,e^H}.$$
--
--   $1/\mathrm{FR\text{-}Multi}(H)$ is the approximation factor of SPP mechanisms with $H$ units.
--
--   **Formalization Note** The constraint $s\le\min(H,1/\tau)$ is written $s(\tau)\le H$ and $\tau s(\tau)\le1$ (same constraint, no division by $0$). The integral of $f_H(s)$ is a lower integral in $[0,\infty]$; the cutoff integral is an ordinary interval integral of a continuous function on $[1/H,T]$.
-- source:
--   Beyhaghi et al., Improved Revenue Bounds for Posted-Price and Second-Price Mechanisms, arXiv:1807.03435v4, pp. 18–20, Theorem 3, (FR-Multi(H)), Lemma 4

import Mathlib
import Definitions.Def_SPPRevenue_SingleUnit_Setting
import Definitions.Def_SPPRevenue_SingleUnit_Supplement_Programs

namespace SPPRevenue.SingleUnit.Supplement

open MeasureTheory
open scoped ENNReal

/-- `f_H(x) = H − e^{−x} Σ_{i=0}^{H−1} (H − i) x^i / i!` (Theorem 3, p. 19). -/
noncomputable def fH (H : ℕ) (x : ℝ) : ℝ :=
  H - Real.exp (-x) * ∑ i ∈ Finset.range H, ((H : ℝ) - i) * x ^ i / (i.factorial : ℝ)

/-- Feasibility for (FR-Multi(H)) (Theorem 3, pp. 18–19): `s` weakly decreasing on `τ ≥ 0`,
`0 ≤ s(τ) ≤ min(H, 1/τ)` (written `s τ ≤ H ∧ τ * s τ ≤ 1`, avoiding `1/0 = 0` at `τ = 0`), and
`∫_0^∞ f_H(s(τ)) dτ ≤ 1`. -/
def FRMultiFeasible (H : ℕ) (s : ℝ → ℝ) : Prop :=
  AntitoneOn s (Set.Ici 0) ∧
    (∀ τ, 0 ≤ τ → 0 ≤ s τ ∧ s τ ≤ H ∧ τ * s τ ≤ 1) ∧
    ∫⁻ τ in Set.Ici 0, ENNReal.ofReal (fH H (s τ)) ≤ 1

/-- The objective values `∫_0^∞ s(τ) dτ` of the feasible points of (FR-Multi(H)). -/
def frMultiValues (H : ℕ) : Set ℝ≥0∞ := frObj '' {s | FRMultiFeasible H s}

/-- `FR-Multi(H)`, the optimal value of (FR-Multi(H)). -/
noncomputable def frMulti (H : ℕ) : ℝ≥0∞ := sSup (frMultiValues H)

/-- The equation of Lemma 4 (p. 20) for the cutoff `T = τ⋆`:
`∫_{1/H}^{T} (H − e^{−1/τ} Σ_{i=0}^{H−1} (H − i)/(τ^i i!)) dτ = H^H / (H! e^H)`. -/
def multiRootEq (H : ℕ) (T : ℝ) : Prop :=
  ∫ τ in (1 / (H : ℝ))..T,
      ((H : ℝ) - Real.exp (-(1 / τ)) *
        ∑ i ∈ Finset.range H, ((H : ℝ) - i) / (τ ^ i * (i.factorial : ℝ))) =
    (H : ℝ) ^ H / ((H.factorial : ℝ) * Real.exp H)

end SPPRevenue.SingleUnit.Supplement


