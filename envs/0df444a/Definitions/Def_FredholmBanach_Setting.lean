-- Prove2me | Definitions.Def_FredholmBanach_Setting
-- name    : FredholmBanach_Setting
-- status  : Definition
-- author  : @Mazecto
-- created : 2026-10-09T15:37:41.949774+00:00
-- url     : https://prove2.me/theorems/578e5e7b-73f7-4910-b849-2c4d40b3dd37
-- title:
--   The index $\dim\operatorname{Ker}u-\dim\operatorname{Coker}u$ of a Fredholm operator
-- statement:
--   The index of a Fredholm operator between normed spaces, following N. Bourbaki, *Théories spectrales*, Chapitre III, § 3, n° 3 (TS III.43).
--
--   Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$, let $E$, $F$ be normed spaces over $\mathbb{K}$ and let $u:E\to F$ be a bounded linear map. Write $\operatorname{Ker}u\subset E$ for its kernel, $\operatorname{Im}u\subset F$ for its range and $\operatorname{Coker}u=F/\operatorname{Im}u$ for its cokernel (an algebraic quotient). The **index** of $u$ is the integer
--   $$\operatorname{ind}u=\dim\operatorname{Ker}u-\dim\operatorname{Coker}u .$$
--
--   Fredholm operators themselves are not defined here: they are Mathlib's `ContinuousLinearMap.IsFredholm` ($u$ is a strict map, $\operatorname{Ker}u$ is finite-dimensional and topologically complemented, and $\operatorname{Im}u$ is closed and of finite codimension). For a Fredholm operator both dimensions are finite.
--
--   **Formalization Note** `index u` is `Module.finrank 𝕜 u.ker - Module.finrank 𝕜 (F ⧸ u.range)` in `ℤ`. Since `Module.finrank` is $0$ on infinite-dimensional spaces, `index u` is meaningful only when `u.IsFredholm`; every theorem about it assumes this. Bourbaki (TS III.43, formula (1)) uses the opposite sign, $\dim\operatorname{Coker}u-\dim\operatorname{Ker}u$; the sign here is the usual one in analysis and geometry. The scalar field is any `RCLike` field.
-- source:
--   N. Bourbaki, Théories spectrales, Chapitres III à V, Springer (2023), https://doi.org/10.1007/978-3-031-19505-1, Chapitre III, § 3, n° 2-3, pp. TS III.40-III.43

import Mathlib.Analysis.Normed.Operator.Fredholm.Basic
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.RCLike.Basic

/-!
# The index of a Fredholm operator

N. Bourbaki, *Théories spectrales*, Chapitre III, § 3, n° 2–3 (pp. TS III.40–III.43).

Fredholm operators are Mathlib's `ContinuousLinearMap.IsFredholm`: `u : E →L[𝕜] F` is
Fredholm if it is a strict map with closed range of finite codimension whose kernel is
finite-dimensional and topologically complemented. For Banach spaces over `ℝ` or `ℂ` this
agrees with Bourbaki's Definition 1 (existence of a quasi-inverse modulo finite rank).

The index is `ind u = dim Ker u - dim Coker u`, with `Coker u = F ⧸ Im u`.
Bourbaki (TS III.43, formula (1)) uses the opposite sign, `dim Coker u - dim Ker u`.
-/

namespace FredholmBanach

noncomputable section

/-- The index `dim Ker u - dim (F ⧸ Im u)` of a continuous linear map. `Module.finrank` is `0`
on infinite-dimensional spaces, so the value is meaningful only for Fredholm `u`. -/
def index {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] (u : E →L[𝕜] F) : ℤ :=
  (Module.finrank 𝕜 u.ker : ℤ) - (Module.finrank 𝕜 (F ⧸ u.range) : ℤ)

end

end FredholmBanach


