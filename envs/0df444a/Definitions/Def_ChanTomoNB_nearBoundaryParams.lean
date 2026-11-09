-- Prove2me | Definitions.Def_ChanTomoNB_nearBoundaryParams
-- name    : ChanTomoNB_nearBoundaryParams
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T11:27:20.261087+00:00
-- url     : https://prove2.me/theorems/bbe55e6a-ba19-4fdd-86f9-23ea0b667595
-- title:
--   Near-boundary parameters $d'=\lfloor d_1/2\rfloor$, $\alpha$, $\chi$, $\lambda_0$, $C_0=450$, $\kappa$
-- statement:
--   In the near-boundary regime $d_1<rd_2<2d_1$:
--   $$
--   d'=\lfloor d_1/2\rfloor,\quad \alpha=rd_2-d_1,\quad \chi=\min\{\alpha d_1,\alpha^2d_2^2\},\quad \lambda_0=\frac{d_1-d'}{2r},\quad C_0=450,\quad \kappa=C_0\Big(\frac\alpha r+\frac1{d_2}\Big).
--   $$
--
--   These constants govern the packing size and separations of the hard family.
--
--   **Formalization Note** $\alpha$ is a natural-number difference; every statement using it assumes $d_1<rd_2$, so it equals the paper's $\alpha\ge1$. $\chi,\lambda_0,\kappa$ are real.
-- source:
--   Chen, Oufkir, Quantum channel tomography: optimal bounds in the near-boundary regime, arXiv:2611.03639v1, §5, p.24; §5.1, p.25; Lemma 5.1, p.25; Eq. (52), p.26

import Mathlib

namespace ChanTomoNB

/-- `d′ = ⌊d1/2⌋`, the signal input dimension. Chen, Oufkir, *Quantum channel tomography: optimal
bounds in the near-boundary regime*, arXiv:2611.03639v1, §5.1, p.25. -/
def dp (d1 : ℕ) : ℕ := d1 / 2

/-- `α = r d2 − d1` (arXiv:2611.03639v1, §5, p.24).

**Formalization Note.** Natural-number subtraction; every statement using it assumes
`d1 < r d2`, so the value is the paper's `α ≥ 1`. -/
def alpha (d1 d2 r : ℕ) : ℕ := r * d2 - d1

/-- `χ = min{α d1, α² d2²}` (arXiv:2611.03639v1, §5, p.24, and Theorem 6.1, p.33), in `ℝ`. -/
noncomputable def chi (d1 d2 r : ℕ) : ℝ :=
  min ((alpha d1 d2 r : ℝ) * d1) ((alpha d1 d2 r : ℝ) ^ 2 * (d2 : ℝ) ^ 2)

/-- `λ₀ = (d − d′)/(2r)` with `d = d1`, `d′ = ⌊d1/2⌋` (arXiv:2611.03639v1, Lemma 5.1, p.25), in `ℝ`. -/
noncomputable def lam0 (d1 r : ℕ) : ℝ := ((d1 : ℝ) - (dp d1 : ℝ)) / (2 * r)

/-- The constant `C₀ = 450` (arXiv:2611.03639v1, Eq. (52), p.26). -/
noncomputable def C0 : ℝ := 450

/-- `κ = C₀ (α/r + 1/d2)` (arXiv:2611.03639v1, Eq. (52), p.26), in `ℝ`. -/
noncomputable def kappa (d1 d2 r : ℕ) : ℝ := C0 * ((alpha d1 d2 r : ℝ) / r + 1 / (d2 : ℝ))

end ChanTomoNB


