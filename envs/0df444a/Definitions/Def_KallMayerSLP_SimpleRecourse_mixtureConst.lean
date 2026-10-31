-- Prove2me | Definitions.Def_KallMayerSLP_SimpleRecourse_mixtureConst
-- name    : KallMayerSLP_SimpleRecourse_mixtureConst
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:12:30.642599+00:00
-- url     : https://prove2.me/theorems/76f1a3fc-4701-4fd3-b00a-b18add5b7e26
-- title:
--   The constant $C$ of (2.63)
-- statement:
--   $$
--   C = \frac{\Bigl(\sum_{k=0}^{K-1}\alpha_k\Bigr)\sum_{k=0}^{K-1}\beta_k l_k + \Bigl(\sum_{k=0}^{K-1}\beta_k\Bigr)\sum_{k=0}^{K-1}\alpha_k u_k}{\sum_{k=0}^{K-1}(\alpha_k+\beta_k)} .
--   $$
--
--   This is the constant by which the expected SRT function with distribution $G$ must be shifted to coincide with the expected MSRT function.
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 3, (2.63), p.242 (PDF 251)

import Mathlib

namespace KallMayerSLP.SimpleRecourse

/-- **The constant `C`, (2.63).**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 3, (2.63), p.242 (PDF 251)
(derived on p.241, PDF 250):
`C = [(Σ_{k=0}^{K−1} α_k)(Σ_{k=0}^{K−1} β_k l_k) + (Σ_{k=0}^{K−1} β_k)(Σ_{k=0}^{K−1} α_k u_k)] / Σ_{k=0}^{K−1} (α_k + β_k)`. -/
noncomputable def mixtureConst {K : ℕ} (α β u l : Fin K → ℝ) : ℝ :=
  ((∑ k, α k) * (∑ k, β k * l k) + (∑ k, β k) * (∑ k, α k * u k)) / ∑ k, (α k + β k)

end KallMayerSLP.SimpleRecourse


