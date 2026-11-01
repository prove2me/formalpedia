-- Prove2me | Definitions.Def_ProjFPOracle_Hn
-- name    : ProjFPOracle_Hn
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:31:39.597821+00:00
-- url     : https://prove2.me/theorems/dcdbfd1a-5238-4b96-8bf6-943a62047b04
-- title:
--   The higher-order term $\mathcal H_n(\sigma_L,\sigma_b,\bar v)$
-- statement:
--   With $\kappa=\kappa(M)<1$, dimension $d$ and sample size $n$,
--   $$
--   \mathcal H_n(\sigma_L,\sigma_b,\bar v):=\frac{\sigma_L}{(1-\kappa)^3}\Big(\frac dn\Big)^{3/2}\big(\|\bar v\|^2\sigma_L^2+\sigma_b^2\big).
--   $$
--   It decays as $n^{-3/2}$ and is the higher-order part of the estimation error in Theorem 1.
--
--   **Formalization Note** $\kappa$ and $d$ are explicit arguments (the paper leaves them implicit), and $(d/n)^{3/2}$ is the real power of the positive real $d/n$.
-- source:
--   Mou, Pananjady & Wainwright, Optimal Oracle Inequalities for Projected Fixed-Point Equations, arXiv:2012.05299v1, §3.1.1, p.12, Eq. (27b)

import Mathlib

namespace ProjFPOracle

/-- **The higher-order term `𝓗_n(σ_L, σ_b, v̄)`** (Mou, Pananjady & Wainwright, *Optimal Oracle
Inequalities for Projected Fixed-Point Equations*, arXiv:2012.05299v1, Eq. (27b), p.12):
`𝓗_n(σ_L, σ_b, v̄) := (σ_L/(1 − κ)³) (d/n)^{3/2} (‖v̄‖² σ_L² + σ_b²)`.

**Formalization Note** `κ = κ(M)` and the dimension `d` enter as explicit arguments (the paper
leaves them implicit); `(d/n)^{3/2}` is the real power of the positive real `d/n`, and every
statement has `κ < 1`, `1 ≤ d` and `n ≥ 2`. -/
noncomputable def Hn {X : Type*} [NormedAddCommGroup X] (κ σL σb : ℝ) (v : X) (d n : ℕ) : ℝ :=
  σL / (1 - κ) ^ 3 * ((d : ℝ) / n) ^ (3 / 2 : ℝ) * (‖v‖ ^ 2 * σL ^ 2 + σb ^ 2)

end ProjFPOracle


