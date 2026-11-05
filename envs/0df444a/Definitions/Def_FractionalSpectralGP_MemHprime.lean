-- Prove2me | Definitions.Def_FractionalSpectralGP_MemHprime
-- name    : FractionalSpectralGP_MemHprime
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:24:18.359799+00:00
-- url     : https://prove2.me/theorems/7f173369-cd79-45ed-8fd5-92dfeaeec668
-- title:
--   Membership in $\mathcal H'_k$: $\sum_\alpha|f_\alpha|^2(2\mathbb N)^{-k\alpha}<\infty$
-- statement:
--   A formal series $f=\sum_{\alpha\in\ell}f_\alpha H_\alpha$, identified with its coefficient family, belongs to the Hilbert space $\mathcal H'_k$ if
--
--   $$
--   \|f\|_k^2=\sum_{\alpha\in\ell}|f_\alpha|^2\,(2\mathbb N)^{-k\alpha}<\infty .
--   $$
--
--   The spaces increase with $k$, and $S_{-1}$ is their union (inductive limit). $k=0$ gives $\mathcal H'_0=\ell^2$.
-- source:
--   Alpay, Jorgensen, Levanony, A class of Gaussian processes with fractional spectral measures, arXiv:1009.0233v1, (4.6), p.11

import Mathlib
import Definitions.Def_FractionalSpectralGP_kondWeight

open MeasureTheory Complex Filter Topology ProbabilityTheory
open scoped SchwartzMap ENNReal

namespace FractionalSpectralGP

/-- Membership in the Hilbert space `𝓗'_k` of formal series `Σ f_α H_α` with
`‖f‖²_k = Σ_α |f_α|² (2ℕ)^{−kα} < ∞` (Alpay, Jorgensen, Levanony, arXiv:1009.0233v1, (4.6), p.11).

**Formalization Note.** A formal series is its coefficient family `f : ℓ → ℂ`. Membership is
square-summability of `f_α (2ℕ)^{−kα/2}`; `k = 0` gives `𝓗'_0 = ℓ²`. -/
def MemHprime (k : ℕ) (f : (ℕ →₀ ℕ) → ℂ) : Prop :=
  Memℓp (fun α => f α * (((Real.sqrt (kondWeight α)) ^ k)⁻¹ : ℝ)) 2

end FractionalSpectralGP


