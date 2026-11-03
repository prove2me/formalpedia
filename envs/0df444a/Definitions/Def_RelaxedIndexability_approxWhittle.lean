-- Prove2me | Definitions.Def_RelaxedIndexability_approxWhittle
-- name    : RelaxedIndexability_approxWhittle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:20:06.427364+00:00
-- url     : https://prove2.me/theorems/89fb4668-2a2f-494f-900c-520247ac2b86
-- title:
--   The closed form (41) of the approximated Whittle index $\hat W(\omega)$
-- statement:
--   Fix an arm with transition matrix $\mathbf P$ (rows $p_0, \dots, p_{K-1}$), rewards $B$, a discount factor $\beta$, and a belief $\omega$ as a point in the threshold. With $L(\cdot) := L(\cdot, \omega)$ the first-crossing time (34), define
--   $$
--   f(x) = \frac{1-\beta^{L(x)}}{1-\beta}, \qquad g(x) = \beta^{L(x)}\,\mathcal T^{L(x)}(x) = \beta^{L(x)}\, x\mathbf P^{L(x)},
--   $$
--   with $\beta^{+\infty} = 0$ (so $f(x) = 1/(1-\beta)$ and $g(x) = 0$ when $L(x) = +\infty$). Let $F(\mathbf P)$ be the column vector $(f(p_0), \dots, f(p_{K-1}))'$, $G(\mathbf P)$ the $K\times K$ matrix whose $k$-th row is the row vector $g(p_k)$, and $H(\mathbf P) = (I_K - \beta G(\mathbf P))^{-1}$. The closed form (41) is
--   $$
--   \hat W(\omega) = \frac{\omega B' - \beta g(\omega\mathbf P)\big[I_K + \beta H(\mathbf P)G(\mathbf P)\big]B' + \beta\,\omega H(\mathbf P)G(\mathbf P)B'}{1 + \beta f(\omega\mathbf P) + \beta\big[\beta g(\omega\mathbf P) - \omega\big]H(\mathbf P)F(\mathbf P)}.
--   $$
--   The module also names the numerator, the denominator, $f$, $g$, $F$, $G$ and $H$ separately.
--
--   **Formalization Note** The matrix inverse and the real division return $0$ on a singular matrix and on a zero denominator. Neither occurs where the formula is used: $I_K - \beta G(\mathbf P)$ is invertible (Lemma 3), and the denominator is nonzero under relaxed indexability (Theorem 3).
-- source:
--   Liu, Relaxed Indexability and Index Policy for Partially Observable Restless Bandits, arXiv:2107.11939v4, (41), p.22, and the definitions of L, f, g, F, G, H, p.23

import Mathlib
import Definitions.Def_RelaxedIndexability_discPow
import Definitions.Def_RelaxedIndexability_crossTime

open Matrix

namespace RelaxedIndexability

variable {K : ℕ}

/-- `f(x) := (1 − β^{L(x)})/(1 − β)` with `L(x) := L(x, ω)` (Liu, arXiv:2107.11939v4, p.23);
`f(x) = 1/(1 − β)` when `L(x, ω) = +∞`. -/
noncomputable def fCoef (β : ℝ) (P : Matrix (Fin K) (Fin K) ℝ) (B ω x : Fin K → ℝ) : ℝ :=
  (1 - discPow β (crossTime P B ω x)) / (1 - β)

/-- `g(x) := β^{L(x)} T^{L(x)}(x) = β^{L(x)} x P^{L(x)}` (Liu, arXiv:2107.11939v4, p.23), a row
vector; `g(x) = 0` when `L(x, ω) = +∞` (since `β^{+∞} = 0`). -/
noncomputable def gVec (β : ℝ) (P : Matrix (Fin K) (Fin K) ℝ) (B ω x : Fin K → ℝ) : Fin K → ℝ :=
  discPow β (crossTime P B ω x) • (x ᵥ* P ^ (crossTime P B ω x).toNat)

/-- `F(P) := [f(p₀); …; f(p_{K−1})]`, a column vector (p.23). -/
noncomputable def FVec (β : ℝ) (P : Matrix (Fin K) (Fin K) ℝ) (B ω : Fin K → ℝ) : Fin K → ℝ :=
  fun k => fCoef β P B ω (P k)

/-- `G(P) := [g(p₀); …; g(p_{K−1})]`, the `K × K` matrix whose row `k` is `g(p_k)` (p.23). -/
noncomputable def GMat (β : ℝ) (P : Matrix (Fin K) (Fin K) ℝ) (B ω : Fin K → ℝ) :
    Matrix (Fin K) (Fin K) ℝ :=
  Matrix.of fun k j => gVec β P B ω (P k) j

/-- `H(P) := (I_K − βG(P))⁻¹` (p.23). -/
noncomputable def HMat (β : ℝ) (P : Matrix (Fin K) (Fin K) ℝ) (B ω : Fin K → ℝ) :
    Matrix (Fin K) (Fin K) ℝ :=
  (1 - β • GMat β P B ω)⁻¹

/-- The numerator of (41): `ωB′ − βg(ωP)[I_K + βH(P)G(P)]B′ + βωH(P)G(P)B′`. -/
noncomputable def whittleNumerator (β : ℝ) (P : Matrix (Fin K) (Fin K) ℝ) (B ω : Fin K → ℝ) : ℝ :=
  ω ⬝ᵥ B - β * (gVec β P B ω (ω ᵥ* P) ⬝ᵥ ((1 + β • (HMat β P B ω * GMat β P B ω)) *ᵥ B))
    + β * (ω ⬝ᵥ ((HMat β P B ω * GMat β P B ω) *ᵥ B))

/-- The denominator of (41): `1 + βf(ωP) + β[βg(ωP) − ω]H(P)F(P)`. -/
noncomputable def whittleDenominator (β : ℝ) (P : Matrix (Fin K) (Fin K) ℝ) (B ω : Fin K → ℝ) :
    ℝ :=
  1 + β * fCoef β P B ω (ω ᵥ* P)
    + β * ((β • gVec β P B ω (ω ᵥ* P) - ω) ⬝ᵥ (HMat β P B ω *ᵥ FVec β P B ω))

/-- **The approximated Whittle index `Ŵ(ω)`** (Liu, arXiv:2107.11939v4, (41), p.22, with the
definitions of `L, f, g, F, G, H` on p.23), all computed with `ω` fixed as a point in the threshold:

`Ŵ(ω) = (ωB′ − βg(ωP)[I_K + βH(P)G(P)]B′ + βωH(P)G(P)B′) / (1 + βf(ωP) + β[βg(ωP) − ω]H(P)F(P))`.

**Formalization Note.** Row vectors times matrices are `ᵥ*`, matrices times column vectors `*ᵥ`,
and the row-by-column products `⬝ᵥ`. `β^{L} = 0` and `g = 0` when `L = +∞` (`discPow`). The matrix
inverse `⁻¹` and the real division return `0` on a singular matrix and a zero denominator; under the
hypotheses of Theorem 3 neither happens (`I_K − βG(P)` is invertible, and the denominator is nonzero
under relaxed indexability). -/
noncomputable def approxWhittle (β : ℝ) (P : Matrix (Fin K) (Fin K) ℝ) (B ω : Fin K → ℝ) : ℝ :=
  whittleNumerator β P B ω / whittleDenominator β P B ω

end RelaxedIndexability


