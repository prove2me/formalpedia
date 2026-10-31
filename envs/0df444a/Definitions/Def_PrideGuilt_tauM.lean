-- Prove2me | Definitions.Def_PrideGuilt_tauM
-- name    : PrideGuilt_tauM
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:55:38.936985+00:00
-- url     : https://prove2.me/theorems/0c8d2d89-312c-40ec-9890-bc73b52833fc
-- title:
--   Indifference rate $\tau_m(f)$
-- statement:
--   For a reward $f$, the **indifference rate** is
--
--   $$
--   \tau_m(f) \equiv \frac{f-c_r+\gamma_P}{\gamma_P-\gamma_G},
--   $$
--
--   the recycling rate at which a recycler and a non-recycler have equal expected utility, $U_R(f,\tau_m(f))=U_N(\tau_m(f))$.
--
--   **Formalization Note** Lean's division returns $0$ when $\gamma_P=\gamma_G$, a case the paper excludes; the equilibrium map only evaluates $\tau_m$ strictly between $c_r-\max(\gamma_P,\gamma_G)$ and $c_r-\min(\gamma_P,\gamma_G)$, an interval that is empty when $\gamma_P=\gamma_G$.
-- source:
--   W. Huang, J. Nguyen, C.-L. Tseng, W. Chen, S. N. Kirshner, Pride or Guilt? Impacts of Consumers' Socially Influenced Recycling Behaviors on Closed-Loop Supply Chains, Manufacturing & Service Operations Management 26(6) (2024), doi:10.1287/msom.2023.0721 (accepted manuscript, printed page = PDF page - 1), Lemma 1, p.9

import Mathlib
import Definitions.Def_PrideGuilt_cr

namespace PrideGuilt

/-- **The indifference rate `τ_m(f) ≡ (f − c_r + γ_P)/(γ_P − γ_G)`.**
Huang–Nguyen–Tseng–Chen–Kirshner, *Pride or Guilt?*, M&SOM 26(6) (2024), doi:10.1287/msom.2023.0721, Lemma 1, p.9 (PDF 10).

**Formalization Note.** Lean's division gives `0` when `γ_P = γ_G`; the paper excludes that
case, and `tauStar` evaluates `τ_m` only strictly between `c_r − max(γ_P, γ_G)` and
`c_r − min(γ_P, γ_G)`, which is empty when `γ_P = γ_G`. -/
noncomputable def tauM (P : Params) (γP γG f : ℝ) : ℝ := (f - cr P + γP) / (γP - γG)

end PrideGuilt


