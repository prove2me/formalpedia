-- Prove2me | Definitions.Def_NearOptOWF_idealDist
-- name    : NearOptOWF_idealDist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:12:37.04568+00:00
-- url     : https://prove2.me/theorems/e39441f6-3521-4b4a-9238-6888a0869609
-- title:
--   Ideal pre-image distribution
-- statement:
--   For a circuit $g : \{0,1\}^N \to \{0,1\}^*$, a target $y \in \mathrm{Im}(g)$ and a failure probability $p_\perp$, the **ideal pre-image distribution** outputs $\perp$ with probability $p_\perp$ and otherwise a uniform element of $g^{-1}(y)$:
--   $$
--   \Pr[\perp] = p_\perp, \qquad \Pr[z] = \frac{1 - p_\perp}{|g^{-1}(y)|}\quad (z \in g^{-1}(y)).
--   $$
--   A perfect pre-image sampler (Definition 4.2) has exactly this output distribution; Claim 4.7 shows the sampler $A$ is close to it.
-- source:
--   Ilango–Lombardi–Tu, Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), Claim 4.7, p.15 (PDF p.17); Definition 4.2, p.13 (PDF p.15)

import Mathlib
import Definitions.Def_LaconicBarrier_MCircuit

namespace NearOptOWF

open LaconicBarrier

/-- The **ideal pre-image distribution** for `g` and `y` with failure probability `p⊥` (Ilango–Lombardi–Tu, *Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP*, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), Claim
4.7, p.15 (PDF p.17): "the distribution that outputs ⊥ with probability `Pr[A(g, y) = ⊥]` and
otherwise outputs a uniform pre-image from `g⁻¹(y)`"; Definition 4.2, p.13 (PDF p.15)): `none` (`⊥`)
has mass `p⊥`, and each `z ∈ g⁻¹(y) ⊆ {0,1}^N` has mass `(1 − p⊥)/|g⁻¹(y)|`.

**Formalization Note** It is used only for `y ∈ Im(g)`, where `g⁻¹(y)` is nonempty. -/
noncomputable def idealDist {N : ℕ} (g : MCircuit N) (y : List Bool) (pbot : ℝ) :
    Option (Fin N → Bool) → ℝ
  | none => pbot
  | some z => if g.eval (List.ofFn z) = y then
      (1 - pbot) / ((Finset.univ.filter fun z' : Fin N → Bool => g.eval (List.ofFn z') = y).card : ℝ)
    else 0

end NearOptOWF


