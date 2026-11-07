-- Prove2me | Definitions.Def_QPSpinParisi_BrownianNoise
-- name    : QPSpinParisi_BrownianNoise
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:02:23.320752+00:00
-- url     : https://prove2.me/theorems/278f3d7d-8023-4e87-9895-0302cf0a9cd6
-- title:
--   A Brownian motion in $\mathbb R^3$ with its integrals $\int\sqrt\zeta\,dB$
-- statement:
--   The noise of the control problems: a probability space, a standard Brownian motion $(B_t)_{0\le t\le1}$ in $\mathbb R^3$, and in each coordinate $a$ the Wiener integral
--   $$N^a_t=\int_0^t\sqrt{\zeta(r)}\,dB^a_r.$$
--
--   **Formalization Note** The source fixes one $B$ on an unnamed space. The integral is tied to $B$ by the published Itô integral relation, with the integrand cut off after time $1$.
-- source:
--   Bhattacharya, Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), §2.1, p.4 (PDF p.4)

import Mathlib
import Definitions.Def_QPSpinParisi_zeta
import Definitions.Def_QPSpinParisi_brownVecFiltration
import Definitions.Def_ABPOnline_IsBrownianVec
import Definitions.Def_EthierKurtz_HasBrownianItoIntegral

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal Matrix

namespace QPSpinParisi

/-- A standard Brownian motion `(B_t)_{0≤t≤1}` in `ℝ³` together with the Wiener integral `N^a_t = ∫₀ᵗ √ζ(r) dB^a_r` in each
coordinate (Bhattacharya, *Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians*, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), §2.1, p.4, PDF p.4).

**Formalization Note** The source fixes one `B` on an unnamed space. The statements of the mission hold for every such
object, and `exists_noise` says that one exists. The process `N` is tied to `B` by `EthierKurtz.HasBrownianItoIntegral`
with the deterministic integrand `√ζ`, cut off after time `1`, where `ζ` is not evaluated. -/
structure BrownianNoise (c : ℕ → ℝ) where
  /-- The probability space. -/
  Ω : Type
  /-- Its σ-algebra. -/
  [mΩ : MeasurableSpace Ω]
  /-- Its probability measure. -/
  P : Measure Ω
  /-- `P` has mass one. -/
  isProb : IsProbabilityMeasure P
  /-- The Brownian motion, by coordinates. -/
  B : Fin 3 → ℝ≥0 → Ω → ℝ
  /-- The coordinates are independent standard Brownian motions on `[0,1]`. -/
  isBrownian : ABPOnline.IsBrownianVec B P
  /-- The Wiener integrals `∫₀ᵗ √ζ dB^a`. -/
  N : Fin 3 → ℝ≥0 → Ω → ℝ
  /-- `N` is the integral of `√ζ` against `B`, in each coordinate. -/
  isWiener : ∀ a, EthierKurtz.HasBrownianItoIntegral P (brownVecFiltration P B) (B a)
    (fun t _ => if t ≤ 1 then Real.sqrt (zeta c t) else 0) (N a)

attribute [instance] BrownianNoise.mΩ BrownianNoise.isProb

end QPSpinParisi


