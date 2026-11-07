-- Prove2me | Definitions.Def_OnlineShadow_LogRate_energy
-- name    : OnlineShadow_LogRate_energy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T04:09:51.523791+00:00
-- url     : https://prove2.me/theorems/ec2c353e-2fef-4e2f-a761-ea39bad7eb6e
-- title:
--   Energy $\mathcal E[\tau]=\frac1n\mathrm{Tr}(\mathsf N\tau)$
-- statement:
--   The **energy** of a (sub-normalized) state $\tau$ on $(\mathcal H\otimes\mathcal R)^{\otimes n}$ is
--   $$\mathcal E[\tau]=\frac1n\,\mathrm{Tr}(\mathsf N\tau),$$
--   the expected fraction of excited copies, relative to the purification $|\psi\rangle$. The untouched state $(|\psi\rangle\langle\psi|)^{\otimes n}$ has energy $0$. The energy quantifies the damage that measurements have done to the copies.
--
--
--   **Formalization Note** The real part of the trace is taken. At $n=0$ the value is $0$; every statement using it assumes $n\ge1$.
-- source:
--   Chen, O'Donnell, Pelecanos, Wright, Online Shadow Tomography Matching the Classical Bounds, STOC 2027 submission (manuscript of November 2, 2026, sha256 90993723…dc3a9), Definition 3.1, p. 8

import Mathlib
import Definitions.Def_OnlineShadow_LogRate_numberOp

namespace OnlineShadow.LogRate

/-- The **energy** `E[τ] ≜ (1/n) Tr(N τ)` of a (sub-normalized) state `τ` on `(H ⊗ R)^{⊗n}`
(Chen, O'Donnell, Pelecanos, Wright, *Online Shadow Tomography Matching the Classical Bounds*, STOC 2027 submission (manuscript of November 2, 2026, sha256 90993723…dc3a9), Definition 3.1, p.8), relative to the purification `ψ`.

**Formalization Note** The real part of the trace is taken (`Tr(Nτ)` is real for Hermitian `τ`).
At `n = 0` the value is `0`; every statement using it assumes `n ≥ 1`. -/
noncomputable def energy {d r : ℕ} (ψ : Fin d × Fin r → ℂ) (n : ℕ)
    (τ : Matrix (Fin n → Fin d × Fin r) (Fin n → Fin d × Fin r) ℂ) : ℝ :=
  (1 / (n : ℝ)) * (numberOp ψ n * τ).trace.re

end OnlineShadow.LogRate


