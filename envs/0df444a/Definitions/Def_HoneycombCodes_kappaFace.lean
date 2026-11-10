-- Prove2me | Definitions.Def_HoneycombCodes_kappaFace
-- name    : HoneycombCodes_kappaFace
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:27:34.225967+00:00
-- url     : https://prove2.me/theorems/d36b722c-5543-44ce-a737-55c801b57e67
-- title:
--   One-sided face exponent $\kappa_{face}(\delta)$
-- statement:
--   Write $s_\delta=1-2\delta$. For $0<x\le 1/2$ and $0\le\rho<1/2$ define
--
--   $$
--   P_{face}=\frac{\dfrac{s_\delta}{2\sqrt{x(1-x)}}-\sqrt\rho}{\sqrt{1-\rho}-\sqrt\rho},\qquad
--   E_{face}=\sqrt{(1-2x+2x\rho)^2+4x(1-x)(1-2\rho)P_{face}},\qquad z_{face}=\frac{1-E_{face}}{2}.
--   $$
--
--   Let $D_{face}(\delta)$ be the pairs with $0<P_{face}<1$ and $0<E_{face}<1$. The **one-sided face exponent** is
--
--   $$
--   \kappa_{face}(\delta)=\inf_{(x,\rho)\in D_{face}(\delta)}\bigl\{H_2(x)+xH_2(\rho)-H_2(z_{face}(x,\rho;\delta))\bigr\}.
--   $$
--
--   It is the honeycomb exponent restricted to the face $\eta=0$ and to its spectral boundary $\Gamma_{HC}=s_\delta$.
--
--   **Formalization Note** A real `sInf` of the objective values over $D_{face}(\delta)$.
-- source:
--   W. Gay, F. Granha Jeronimo, L. Liu, The Honeycomb Framework for Code Bounds, arXiv:2608.20287v2 (sha256 f4b07e318538a352116042dc4da0d4e9d47cfd979cf302c7fce3324584a3cd51), eqs. (56)–(59), p.28 (PDF 30)

import Mathlib
import Definitions.Def_HoneycombCodes_H2

set_option autoImplicit false

namespace HoneycombCodes

/-- `P_face(x, ρ; δ) = (s_δ/(2√(x(1 − x))) − √ρ)/(√(1 − ρ) − √ρ)` with `s_δ = 1 − 2δ`,
Gay, Granha Jeronimo, Liu, *The Honeycomb Framework for Code Bounds*, arXiv:2608.20287v2
(sha256 f4b07e31…cd51), eq. (56), p.28 (PDF 30). -/
noncomputable def Pface (x ρ δ : ℝ) : ℝ :=
  ((1 - 2 * δ) / (2 * Real.sqrt (x * (1 - x))) - Real.sqrt ρ) /
    (Real.sqrt (1 - ρ) - Real.sqrt ρ)

/-- `E_face(x, ρ; δ) = √((1 − 2x + 2xρ)² + 4x(1 − x)(1 − 2ρ)P_face(x, ρ; δ))`,
arXiv:2608.20287v2, eq. (57), p.28 (PDF 30).

**Formalization Note.** `Real.sqrt` of a negative number is `0`; on `D_face(δ)` the radicand is
positive because `P_face > 0`. -/
noncomputable def Eface (x ρ δ : ℝ) : ℝ :=
  Real.sqrt ((1 - 2 * x + 2 * x * ρ) ^ 2 + 4 * x * (1 - x) * (1 - 2 * ρ) * Pface x ρ δ)

/-- `z_face(x, ρ; δ) = (1 − E_face(x, ρ; δ))/2`, arXiv:2608.20287v2, eq. (58), p.28 (PDF 30). -/
noncomputable def zface (x ρ δ : ℝ) : ℝ :=
  (1 - Eface x ρ δ) / 2

/-- The **one-sided face exponent** (59),
`κ_face(δ) = inf_{(x, ρ) ∈ D_face(δ)} {H₂(x) + xH₂(ρ) − H₂(z_face(x, ρ; δ))}`, where `D_face(δ)`
is the set of pairs with `0 < x ≤ 1/2`, `0 ≤ ρ < 1/2`, `0 < P_face < 1` and `0 < E_face < 1`,
arXiv:2608.20287v2, §6.1, p.28 (PDF 30).

**Formalization Note.** A real `sInf` of the set of objective values over `D_face(δ)`. -/
noncomputable def kappaFace (δ : ℝ) : ℝ :=
  sInf {r : ℝ | ∃ x ρ : ℝ, 0 < x ∧ x ≤ 1 / 2 ∧ 0 ≤ ρ ∧ ρ < 1 / 2 ∧
    0 < Pface x ρ δ ∧ Pface x ρ δ < 1 ∧ 0 < Eface x ρ δ ∧ Eface x ρ δ < 1 ∧
    r = H2 x + x * H2 ρ - H2 (zface x ρ δ)}

end HoneycombCodes


