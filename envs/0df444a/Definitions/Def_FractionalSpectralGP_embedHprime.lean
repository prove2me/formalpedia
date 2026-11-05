-- Prove2me | Definitions.Def_FractionalSpectralGP_embedHprime
-- name    : FractionalSpectralGP_embedHprime
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:25:22.712256+00:00
-- url     : https://prove2.me/theorems/a72943ec-7fff-4840-8055-8c65f13e51e1
-- title:
--   The Hilbert space $\mathcal H'_k$ realized in $\ell^2(\ell)$
-- statement:
--   The map
--
--   $$
--   f\longmapsto\big(f_\alpha\,(2\mathbb N)^{-k\alpha/2}\big)_{\alpha\in\ell}
--   $$
--
--   is an isometry of $\mathcal H'_k$ onto $\ell^2(\ell)$. Through it, $\|f\|_k$ is an $\ell^2$ norm, and integrals of $\mathcal H'_k$-valued functions (such as $\int_a^bY(t)\diamond W_\sigma(t)\,dt$) are Bochner integrals in a Hilbert space.
--
--   **Formalization Note** For $f\notin\mathcal H'_k$ the value is $0$; every statement using it asserts or assumes membership in $\mathcal H'_k$ first.
-- source:
--   Alpay, Jorgensen, Levanony, A class of Gaussian processes with fractional spectral measures, arXiv:1009.0233v1, (4.6), p.11

import Mathlib
import Definitions.Def_FractionalSpectralGP_kondWeight
import Definitions.Def_FractionalSpectralGP_MemHprime

open MeasureTheory Complex Filter Topology ProbabilityTheory
open scoped SchwartzMap ENNReal

namespace FractionalSpectralGP

/-- The Hilbert space `𝓗'_k` of (4.6) (Alpay, Jorgensen, Levanony, arXiv:1009.0233v1, p.11), realized inside `ℓ²(ℓ)`:
`f ↦ (f_α (2ℕ)^{−kα/2})_α` is an isometry of `𝓗'_k` onto `ℓ²(ℓ)`, so `‖f‖_k = ‖embedHprime k f‖`.

**Formalization Note.** For `f ∉ 𝓗'_k` the value is `0`; every statement that uses it asserts or
assumes membership (`MemHprime k f`) first. Integrals of `𝓗'_k`-valued functions are Bochner
integrals in this Hilbert space. -/
noncomputable def embedHprime (k : ℕ) (f : (ℕ →₀ ℕ) → ℂ) : lp (fun _ : ℕ →₀ ℕ => ℂ) 2 := by
  classical
  exact if hf : MemHprime k f then ⟨_, hf⟩ else 0

end FractionalSpectralGP


