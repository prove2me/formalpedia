-- Prove2me | Definitions.Def_DistQuantumQuery_sfAdv
-- name    : DistQuantumQuery_sfAdv
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:17:19.931049+00:00
-- url     : https://prove2.me/theorems/91b2c1f9-2ebb-4c79-97a7-d24f45a8ea5c
-- title:
--   Shaltiel-free adversary measure $\mathrm{sfAdv}^{(\nu_0,\nu_1)}(g)$
-- statement:
--   Let $g:\Sigma\to\{0,1\}$ be a decision problem on $\Sigma\subseteq\{0,1\}^m$, let $\nu_0,\nu_1$ be distributions supported on $g^{-1}(0)$ and $g^{-1}(1)$, and $\nu=\tfrac12(\nu_0+\nu_1)$. The **Shaltiel-free adversary measure** of $g$ with respect to $(\nu_0,\nu_1)$ is
--   $$
--   \mathrm{sfAdv}^{(\nu_0,\nu_1)}(g):=\inf_{\delta\in[0,1)}\frac{\mathrm{rAdv}^\nu_\delta(g)}{1-\delta}.
--   $$
--   It measures the best trade-off between the cost of an inner computation and the bias it provides, and is the inner factor of the paper's composition theorem.
--
--   **Formalization Note** The value is in $[0,\infty]$; $\{0,1\}$ is `Bool`. The support conditions on $\nu_0,\nu_1$ are hypotheses of the theorems that use the measure.
-- source:
--   Ben-David, Ebtehaj, Distributional Quantum Query Complexity, arXiv:2610.06835 (held version, sha256 6334ffaf…), Definition 6.10 p.53

import Mathlib
import Definitions.Def_DistQuantumQuery_rAdv

open scoped Matrix ENNReal

namespace DistQuantumQuery

/-- The **Shaltiel-free adversary measure** (Ben-David, Ebtehaj, *Distributional Quantum Query
Complexity*, arXiv:2610.06835, held version, sha256 6334ffaf…, Definition 6.10, p.53): for a
decision problem `g : Σ → {0,1}` and distributions `ν₀, ν₁` supported on `g⁻¹(0)`, `g⁻¹(1)`,
with `ν = (ν₀ + ν₁)/2`,
`sfAdv^{(ν₀,ν₁)}(g) := inf_{δ ∈ [0,1)} rAdv^ν_δ(g) / (1 − δ)`.

**Formalization Note** Value in `ℝ≥0∞`; `{0,1}` is `Bool`. The support conditions on `ν₀, ν₁`
are hypotheses of the theorems that use this measure, not part of the definition. -/
noncomputable def sfAdv {κ : Type*} [Fintype κ] (S : Finset (κ → Bool)) (g : S → Bool)
    (ν₀ ν₁ : S → ℝ) : ℝ≥0∞ :=
  ⨅ (δ : ℝ) (_ : 0 ≤ δ ∧ δ < 1),
    rAdv S (fun x => (ν₀ x + ν₁ x) / 2) g δ / ENNReal.ofReal (1 - δ)

end DistQuantumQuery


