-- Prove2me | Definitions.Def_RandTreeUniv_kStar
-- name    : RandTreeUniv_kStar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:10:17.899478+00:00
-- url     : https://prove2.me/theorems/3bbf2475-f0c1-4f76-9ae8-042096fcb807
-- title:
--   Constants $C_0$, $C^*$ of (3) and the depth $k^*(n,\psi)$
-- statement:
--   Display (3) fixes the constants $C_0=10^5$ and $C^*=2(1+\varepsilon)$ with $\varepsilon=10^{-100}$. For $n$ and a value $\psi\ge1$, the optimal depth is
--
--   $$
--   k^*(n,\psi)=\Big\lceil \frac{C^*\ln n}{\psi\ln\ln n}\Big\rceil .
--   $$
--
--   Path systems and linking systems of depth $k\ge k^*$ (resp. $k\ge4e\,k^*$) exist whp in $G(n,C_0(\ln n)^\psi/n)$ (resp. $G(\delta n,(2C_0/\delta)(\ln n)^\psi/n)$) by Theorem 3.3 and Lemma 3.4; up to the constant this depth is optimal by a first-moment argument.
--
--   **Formalization Note** $\ln$ is the natural logarithm; the ceiling of a nonpositive number is $0$, which occurs only for small $n$, where no admissible $\psi$ exists.
-- source:
--   A. Cohen Antonir, L. Lichev, M. Zhukovskii, Universality in random graphs via optimal linking systems: trees and beyond, arXiv:2608.06358 (held revision, sha256 33e85b21…69a55921), display (3) and §3.1, p.14 (PDF 15)

import Mathlib

set_option autoImplicit false

open scoped Classical

namespace RandTreeUniv

/-- The constant `C₀ = 10⁵` of display (3), Cohen Antonir, Lichev, Zhukovskii, *Universality in random graphs via optimal linking systems: trees and beyond*, arXiv:2608.06358 (held revision, sha256 33e85b21…), p.14 (PDF 15). -/
noncomputable def C0 : ℝ := 10 ^ 5

/-- The constant `C∗ = 2(1 + ε)` with `ε = 10⁻¹⁰⁰` of display (3), p.14 (PDF 15). -/
noncomputable def Cstar : ℝ := 2 * (1 + (10 : ℝ) ^ (-(100 : ℤ)))

/-- The optimal depth `k∗ = k∗(n, ψ) := ⌈C∗ ln n / (ψ ln ln n)⌉` (Cohen Antonir, Lichev, Zhukovskii, *Universality in random graphs via optimal linking systems: trees and beyond*, arXiv:2608.06358 (held revision, sha256 33e85b21…), §3.1, p.14 (PDF 15)).

**Formalization Note** `ln` is `Real.log`; the ceiling is `Nat.ceil` (`0` for a nonpositive
argument, which happens only for small `n`, where `ψ ∈ [1, ln n/(4 ln ln n)]` is impossible). -/
noncomputable def kStar (n : ℕ) (ψ : ℝ) : ℕ :=
  ⌈Cstar * Real.log n / (ψ * Real.log (Real.log n))⌉₊

end RandTreeUniv


