-- Prove2me | Definitions.Def_IntMul_OpenAI_R129
-- name    : IntMul_OpenAI_R129
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-20T13:11:19.714576+00:00
-- url     : https://prove2.me/theorems/5f3e1b50-55a9-401f-8b6e-611e52281cc0
-- title:
--   OpenAI construction at the same-network-129 constants: cost table and parameters
-- statement:
--   Constants, normalized cost table and parameter map of the OpenAI integer multiplication construction, with the constants of the `same-network-129` patch.
--
--   **Constants.** $\tau = 1-2^{-42}$, $\delta = 1/16$ (unchanged), $c = 2^{-43}$, $\lambda' = 1-2^{-85}$, $\varepsilon = 2^{-43}$, $\kappa = 2^{-129}$, and $e_s = 1 - 2\kappa$.
--
--   **Cost table.** For reals $p, d, K, \ell, \alpha$,
--   $$N(p,d,K,\ell,\alpha) = dK + pK^{\tau-1} + \ell d^{\lambda'} + d^2(1+\ell^{\tau}) + d\,p^{1/2+\delta}\alpha + d\,p^{\delta} + (\ell + \log_2 p) + p^{\delta} + 1,$$
--   the running time of the construction divided by the bit volume (Table 1 of the manuscript). Powers are real powers.
--
--   **Parameter map.** For an input length $n$, with $b = \max(\lceil\log_2 n\rceil, 1)$ and $L$ the least integer with $4n \le 2^L b$ (both from `IntMul.OpenAI.Glue`): $d = \lfloor b^{\varepsilon}\rfloor$, $K = \lfloor d^{c}\rfloor$, $\ell = \lceil L/d\rceil$ (as $(L+d-1)/d$ in natural numbers), and $\alpha = \lceil (12 d^2 b)^{1/4}\rceil$.
-- source:
--   OpenAI, Integer multiplication below n log n, preprint, 23 September 2026, https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026, §8 (Table 1, eq. (fixed-parameters), margin list (margin-list)); parameters from D. Colkitt et al., integer-mult-bounds, patch same-network-129, https://github.com/CrocSwap/integer-mult-bounds/blob/main/patches/same-network-129.patch

import Mathlib
import Definitions.Def_IntMul_Kappa_K_Defs9

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The OpenAI construction retuned to `κ = 2⁻¹²⁹` (`same-network-129` parameters)

The constants, the normalized cost table and the per-length parameter map of the OpenAI
construction (*Integer multiplication below n log n*, §8 and §9.2.1), with the conservative
constants of §8 replaced by those of the community patch `same-network-129`:

* `τ = 1 - 2⁻⁴²` (was `1 - 2⁻⁵⁰`; same swap networks, sharper estimate `log 10⁶ < 14` of the
  motif exponent) and `δ = 1/16` (unchanged);
* `c = 2⁻⁴³` (was `2⁻⁵⁶`), `λ' = 1 - 2⁻⁸⁵` (was `1 - 2⁻⁵⁴`), `ε = 2⁻⁴³` (was `2⁻⁷⁵`);
* `κ = 2⁻¹²⁹` (was `2⁻¹⁸²`).

`Ncost` is the same expression as `IntMul.OpenAI.RCost.Ncost` (Table 1 of the manuscript, all rows
divided by `T p`), read at the new constants. The parameter map reuses `b = lg n`, `L`, `T`, `p`
and the bit volume `V = T p` from `IntMul.OpenAI.Glue` (they do not depend on the constants) and
redefines the four parameters that do: `d = ⌊b^ε⌋`, `K = ⌊d^c⌋`, `ℓ = ⌈L/d⌉` and
`α = ⌈(12 d² b)^{1/4}⌉`.
-/

open Real

namespace IntMul.OpenAI.R129

noncomputable section

/-- The swap exponent `τ = 1 - 2⁻⁴²`. -/
def τ : ℝ := 1 - 1 / 2 ^ 42
/-- `δ = 1/16` (unchanged). -/
def δ : ℝ := 1 / 16
/-- `c = 2⁻⁴³`. -/
def c : ℝ := 1 / 2 ^ 43
/-- `λ' = 1 - 2⁻⁸⁵`. -/
def lam' : ℝ := 1 - 1 / 2 ^ 85
/-- `ε = 2⁻⁴³`. -/
def ε : ℝ := 1 / 2 ^ 43
/-- `κ = 2⁻¹²⁹`. -/
def κ : ℝ := 1 / 2 ^ 129
/-- The common exponent `1 - 2κ`. -/
def es : ℝ := 1 - 2 * κ

/-- Normalized Table 1 cost (all rows after division by `T p`), at the `same-network-129` constants. -/
def Ncost (p d K ℓ α : ℝ) : ℝ :=
  d * K + p * K ^ (τ - 1) + ℓ * d ^ lam' + d ^ 2 * (1 + ℓ ^ τ) + d * p ^ (1 / 2 + δ) * α +
    d * p ^ δ + (ℓ + Real.logb 2 p) + p ^ δ + 1

/-- `d = ⌊b^ε⌋` with `ε = 2⁻⁴³`. -/
def dP (n : ℕ) : ℕ := ⌊(IntMul.OpenAI.Glue.bP n : ℝ) ^ ε⌋₊
/-- `K = ⌊d^c⌋` with `c = 2⁻⁴³`. -/
def KP (n : ℕ) : ℕ := ⌊(dP n : ℝ) ^ c⌋₊
/-- `ℓ = ⌈L/d⌉`. -/
def ℓP (n : ℕ) : ℕ := IntMul.OpenAI.RP.ell (IntMul.OpenAI.Glue.LP n) (dP n)
/-- `α = ⌈(12 d² b)^{1/4}⌉`. -/
def αP (n : ℕ) : ℕ := ⌈(12 * (dP n : ℝ) ^ 2 * IntMul.OpenAI.Glue.bP n) ^ ((1 : ℝ) / 4)⌉₊

end

end IntMul.OpenAI.R129


