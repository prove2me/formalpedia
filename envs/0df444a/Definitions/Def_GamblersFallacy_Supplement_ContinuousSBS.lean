-- Prove2me | Definitions.Def_GamblersFallacy_Supplement_ContinuousSBS
-- name    : GamblersFallacy_Supplement_ContinuousSBS
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T00:15:58.124419+00:00
-- url     : https://prove2.me/theorems/1fd77dc3-5280-49f8-b5c2-365a5486c08d
-- title:
--   Continuous demand sizes with densities $f_j$ and the corrected biased densities $\tilde p_j(n,\theta)$
-- statement:
--   Let the inter-arrival time have law $P(Z=j)=p_j$ on $[J]$. Given $Z=j\in[J]$, the demand size has a probability density $f_j$ on $(0,\infty)$. The cycles $(Z_t,Y_t)$, $t\ge1$, are i.i.d. with this law, so $P(Z=j,\ Y\in B)=p_j\int_B f_j(\theta)\,d\theta$.
--
--   In the notation of the CPUGS, the **biased density** is
--   $$
--   \tilde p_j(n,\theta)=\mathbb E\Bigg[\sum_{t\in[\tau]}\frac{\chi(Z_t=j)}{\big(\sum_{s\in[\tau]^+,s\ne t}Y_s+\theta\big)/\theta}+\chi\Big(\sum_{s=1}^{\tau}Z_s=n-j\Big)\chi(Z_{\tau+1}=j)\,\frac{\theta}{\sum_{s\in[\tau]}Y_s+\max\{1,\theta\}}\Bigg]f_j(\theta),
--   $$
--   with $[\tau]^+=[\tau]\cup\{n\}$ and $Y_n=\max\{1,X_n\}$. The first term is printed in Theorem 5. The second (last-cycle) term is corrected in two ways: the factor $\chi(Z_{\tau+1}=j)$ requires the next demand to arrive at $n$, and the CPUGS denominator counts that demand as $\max\{1,\theta\}$.
--
--   It replaces $p_jf_j(\theta)$ in the single-cycle cost when the CPUGS is evaluated over a finite horizon (Theorem 5, problem (6)).
--
--   **Formalization Note** The densities are $[0,\infty]$-valued, measurable, zero on $(-\infty,0]$ and of total mass $1$ for $j\in[J]$. The cycle law is $\sum_{j\in[J]}p_j\,(f_j\,d\theta)$ pushed to $\{j\}\times\mathbb R$. The expectation is a lower Lebesgue integral in $[0,\infty]$, and $\sum_{s=1}^\tau Z_s=n-j$ is written $Z_1+\dots+Z_\tau+j=n$.
-- source:
--   Bi–He–Teo, Taming the Long Tail, MSOM (2023), doi:10.1287/msom.2023.1217, §4.2.3, p.21 (density f_j given inter-arrival time j); Theorem 5, p.22 and EC.2.5, p.ec6 (p̃_j(n, θ), [τ]^+, Y_n = max{1, X_n})

import Mathlib
import Definitions.Def_GamblersFallacy_Supplement_RenewalLaw
import Definitions.Def_GamblersFallacy_Supplement_CPUGS

namespace GamblersFallacy.Supplement

open MeasureTheory

/-- **Continuous demand sizes** (§4.2.3, p.21).
S. Bi, L. He, C.-P. Teo, *Taming the Long Tail: The Gambler's Fallacy in Intermittent Demand
Management*, MSOM (2023), doi:10.1287/msom.2023.1217, p.21: "Let D denote the random demand size
with probability density function f_j(·) conditional on inter-arrival time j."

The inter-arrival time has law `p` on `{1, …, J}`, and given inter-arrival time `j ∈ [J]` the
(nonzero) demand size has the probability density `f_j` on `(0, ∞)`.

**Formalization Note.** Densities are `ℝ≥0∞`-valued, vanish on `(−∞, 0]` (demands are nonzero
sizes) and integrate to `1` for every `j ∈ [J]`. -/
structure ContinuousDemandModel where
  /-- the inter-arrival law `p_j = P(Z = j)` -/
  law : InterArrivalLaw
  /-- `f j` is the density of the demand size given inter-arrival time `j` -/
  f : ℕ → ℝ → ENNReal
  measurable_f : ∀ j, Measurable (f j)
  f_eq_zero : ∀ j θ, θ ≤ 0 → f j θ = 0
  lintegral_f : ∀ j ∈ Finset.Icc 1 law.J, ∫⁻ θ, f j θ = 1

/-- The law of one cycle `(Z_t, Y_t)` on `ℕ × ℝ`: `P(Z = j, Y ∈ B) = p_j ∫_B f_j`. -/
noncomputable def ContinuousDemandModel.cycleLaw (M : ContinuousDemandModel) : Measure (ℕ × ℝ) :=
  ∑ j ∈ Finset.Icc 1 M.law.J,
    ENNReal.ofReal (M.law.p j) • (volume.withDensity (M.f j)).map (fun θ : ℝ => (j, θ))

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The biased density `p̃_j(n, θ)`, corrected** (Theorem 5, p.22; EC.2.5, p.ec6).
Printed: `p̃_j(n, θ) := E( Σ_{t∈[τ]} χ(Z_t = j) / ((Σ_{s∈[τ]⁺, s≠t} Y_s + θ)/θ)
  + χ(Σ_{s=1}^τ Z_s = n − j) / ((Σ_{s∈[τ]} Y_s + θ)/θ) ) f_j(θ)`, `[τ]⁺ = [τ] ∪ {n}`,
`Y_n = max{1, X_n}`.

Here the first term is as printed, and the second (the last cycle closing at `n` with demand `θ`)
is corrected to `χ(Σ_{s=1}^τ Z_s = n − j) χ(Z_{τ+1} = j) · θ / (Σ_{s∈[τ]} Y_s + max{1, θ})`: the
`(τ + 1)`-th demand must arrive at `n` (factor `χ(Z_{τ+1} = j)`), and the CPUGS denominator counts
it as `max{1, X_n} = max{1, θ}`.

**Formalization Note.** `Σ_{s=1}^τ Z_s = n − j` is written `Z₁ + ⋯ + Z_τ + j = n`. The
expectation is a lower Lebesgue integral of the nonnegative integrand (for `θ > 0` and
nonnegative sizes). -/
noncomputable def biasedDensity (M : ContinuousDemandModel) (P : Measure Ω) (Z : ℕ → Ω → ℕ)
    (Y : ℕ → Ω → ℝ) (n j : ℕ) (θ : ℝ) : ENNReal :=
  (∫⁻ ω, ENNReal.ofReal
    ((∑ t ∈ Finset.Icc 1 (lastCycle Z n ω),
        (if Z t ω = j then (1 : ℝ) else 0) /
          (((∑ s ∈ (Finset.Icc 1 (lastCycle Z n ω)).erase t, Y s ω) +
              max 1 (demandAtHorizon Z Y n ω) + θ) / θ)) +
      (if arrivalTime Z (lastCycle Z n ω) ω + j = n ∧ Z (lastCycle Z n ω + 1) ω = j
          then (1 : ℝ) else 0) * θ /
        ((∑ s ∈ Finset.Icc 1 (lastCycle Z n ω), Y s ω) + max 1 θ)) ∂P) * M.f j θ

end GamblersFallacy.Supplement


