-- Prove2me | Definitions.Def_MarkdownReadjust_fluidValue
-- name    : MarkdownReadjust_fluidValue
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:13:40.164051+00:00
-- url     : https://prove2.me/theorems/b681f9fe-69f8-48d1-950d-a2777c8c50e4
-- title:
--   Fluid value $\bar J(x_0,T)=\lambda T R(\rho^d)$
-- statement:
--   The optimal value of the fluid revenue maximization problem (1) is
--
--   $$
--   \bar J(x_0,T)=\lambda T\,R(\rho^d).
--   $$
--
--   It upper-bounds the expected revenue of every non-anticipating policy (Theorem 1 of the paper) and is the benchmark against which revenue losses are measured.
-- source:
--   Chen, Jasin, Simple monotonic readjustment policies with applications to markdown pricing and pricing in the presence of strategic customers, SSRN 3740871 (2023-10-09), §4, p.8

import Mathlib
import Definitions.Def_MarkdownReadjust_Model
import Definitions.Def_MarkdownReadjust_rhoD

namespace MarkdownReadjust

/-- The optimal value of the fluid problem (1), `J̄(x₀, T) = λ T R(ρᵈ)` (Chen–Jasin, SSRN
3740871, §4, p.8), for initial inventory `x` and horizon `τ`. -/
noncomputable def fluidValue (M : Model) (x : ℕ) (τ : ℝ) : ℝ :=
  M.lam * τ * M.R (rhoD M x τ)

end MarkdownReadjust


