-- Prove2me | Definitions.Def_ProcessingNetworks_EntropyIneq_traffic
-- name    : ProcessingNetworks_EntropyIneq_traffic
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:28:00.663854+00:00
-- url     : https://prove2.me/theorems/a743df4a-98f0-4d04-9f4b-33a14b3fccca
-- title:
--   §B.4, p.269 — total arrival rates $\alpha=(I-P')^{-1}\lambda$ (traffic equations (B.16))
-- statement:
--   Given external arrival rates $\lambda\in\mathbb R^I$ and a routing matrix $P$, the vector of **total arrival rates** is
--
--   $$
--   \alpha:=(I-P')^{-1}\lambda ,
--   $$
--
--   where $P'$ is the transpose of $P$ and $I$ the identity matrix. When $\rho(P)<1$, $I-P'$ is invertible (Theorem F.1) and $\alpha$ is the unique solution of the traffic equations $\alpha=\lambda+P'\alpha$ (B.16); $\alpha_i$ is the total rate into class $i$, external arrivals plus internal transitions.
--
--   **Formalization Note** The inverse is Lean's matrix inverse, which equals the true inverse whenever $I-P'$ is invertible; every statement of this mission assumes $\rho(P)<1$.
-- source:
--   Dai & Harrison, Processing Networks (pre-publication draft 2020-4-2, spnbook.org), Appendix B §B.4, Traffic equations, eq. (B.16), p.269 (PDF 285)

import Mathlib

open Matrix

namespace ProcessingNetworks.EntropyIneq

/-- **Total arrival rates `α`** (Dai & Harrison, *Processing Networks*, pre-publication draft
2020-4-2, spnbook.org, Appendix B §B.4, "Traffic equations", p.269 (PDF 285)):
`α := (I − P′)⁻¹ λ`, where `λ ∈ ℝ^I_+` is the vector of external arrival rates and `P` the routing
matrix; under the section's assumption that `P` has spectral radius `< 1`, `α` is the unique
solution of the traffic equations `α = λ + P′α` (B.16).

**Formalization Note** `P′` is the transpose `Pᵀ`, `I` the identity `1`, and `(I − P′)⁻¹` is
`Matrix.inv` (`⁻¹`), which is the true inverse whenever `I − P′` is invertible; every statement of
this mission assumes `ρ(P) < 1`, under which it is (Theorem F.1). -/
noncomputable def traffic {I : ℕ} (lam : Fin I → ℝ) (P : Matrix (Fin I) (Fin I) ℝ) : Fin I → ℝ :=
  (1 - Pᵀ)⁻¹ *ᵥ lam

end ProcessingNetworks.EntropyIneq


