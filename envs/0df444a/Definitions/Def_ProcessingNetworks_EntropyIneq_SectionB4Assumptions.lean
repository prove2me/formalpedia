-- Prove2me | Definitions.Def_ProcessingNetworks_EntropyIneq_SectionB4Assumptions
-- name    : ProcessingNetworks_EntropyIneq_SectionB4Assumptions
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:28:53.734624+00:00
-- url     : https://prove2.me/theorems/72fc4430-3dc0-418d-b594-6b92fc0410a4
-- title:
--   §B.4, pp.268–269 — standing assumptions: $\lambda\ge0$, $P\ge0$, $\rho(P)<1$, $\alpha>0$
-- statement:
--   The standing assumptions of Section B.4 on the data $(\lambda,P)$:
--
--   1. $I\ge1$ is a positive integer;
--   2. $\lambda\in\mathbb R^I_+$, i.e. $\lambda_i\ge0$ for every class $i$;
--   3. $P$ is a non-negative $I\times I$ matrix, $P_{ij}\ge0$;
--   4. $P$ has spectral radius $\rho(P)<1$;
--   5. the total arrival rates $\alpha=(I-P')^{-1}\lambda$ are strictly positive, $\alpha_i>0$ for every $i$ (B.17).
--
--   These are the hypotheses of Lemmas B.9, B.10 and B.13, under which every class is reached by external traffic and the entropy-like inequalities of the section hold.
--
--   **Formalization Note** This is the section's hypothesis exactly as printed. It does not require $P$ to be substochastic (row sums at most $1$); Lemma B.13 needs that in addition and states it as its own hypothesis. The convention $\alpha_0=1$ is applied in the statements by writing the class-$0$ terms explicitly.
-- source:
--   Dai & Harrison, Processing Networks (pre-publication draft 2020-4-2, spnbook.org), Appendix B §B.4, pp.268–269 (PDF 284–285), eqs. (B.13)–(B.17)

import Mathlib
import Definitions.Def_RobustToDynamics_specRadius
import Definitions.Def_ProcessingNetworks_EntropyIneq_traffic

namespace ProcessingNetworks.EntropyIneq

/-- **Standing assumptions of Section B.4** (Dai & Harrison, *Processing Networks*,
pre-publication draft 2020-4-2, spnbook.org, Appendix B §B.4, pp.268–269 (PDF 284–285), eqs.
(B.13)–(B.17)): "We take as given a positive integer `I`, a vector `λ ∈ ℝ^I_+`, and an `I × I`
non-negative matrix `P`. We assume that `P` has spectral radius less than 1. … Throughout this
section we define `α₀ := 1` and assume `λ` and `P` to be such that `α > 0`", where
`α = (I − P′)⁻¹λ`.

Fields: `I ≥ 1`; `λᵢ ≥ 0`; `P_{ij} ≥ 0`; `ρ(P) < 1`; `αᵢ > 0` for every class `i`.

**Formalization Note** This is the section's hypothesis exactly as printed: it does **not** require
`P` to be substochastic (row sums `≤ 1`). Lemma B.13 needs that in addition and states it
separately. The convention `α₀ = 1` is not a field: it is applied where the book uses it, by writing
the class-0 term explicitly. -/
structure SectionB4Assumptions {I : ℕ} (lam : Fin I → ℝ) (P : Matrix (Fin I) (Fin I) ℝ) :
    Prop where
  pos_I : 0 < I
  lam_nonneg : ∀ i, 0 ≤ lam i
  P_nonneg : ∀ i j, 0 ≤ P i j
  specRadius_lt_one : RobustToDynamics.specRadius P < 1
  traffic_pos : ∀ i, 0 < traffic lam P i

end ProcessingNetworks.EntropyIneq


