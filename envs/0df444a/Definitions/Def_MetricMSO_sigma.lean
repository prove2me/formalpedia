-- Prove2me | Definitions.Def_MetricMSO_sigma
-- name    : MetricMSO_sigma
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:44:43.332213+00:00
-- url     : https://prove2.me/theorems/8118ab60-6afe-4b90-9d34-ffc4a13d6592
-- title:
--   The translation $\sigma_M$ from $\mathrm{CMSO}_2[\mathsf{SP},\mathsf{EqGC}]$ to $\mathrm{CMSO}_2$
-- statement:
--   The translation $\sigma_M(\varphi)$ replaces each $\mathsf{SP}$ atom by a fresh copy of $\mathsf{CertSP}_M$ and each $\mathsf{EqGC}$ atom by a fresh copy of $\mathsf{CertEqGC}_M$. It leaves all ordinary atoms unchanged, including modulo-counting atoms and unary input predicates, and it recurses through Boolean connectives and quantifiers.
--
--   **Formalization Note** `sigma M φ dV dS` reads $\varphi$ in a context of `dV` vertex and `dS` vertex-set variables, and writes each certificate for the context at its atom; fresh copies are fresh de Bruijn levels. The auxiliary variables are vertex and vertex-set variables, so edge and edge-set quantifiers do not change the levels used.
-- source:
--   Chakraborty, Ordyniak, Siebertz, Model Checking for Metric Extensions of MSO (arXiv:2610.41974, sha256 ad3c586330b037548a2b4a977081284996698f39c1b55c17b91cb81a536d3dd9), §4.3, p.28 (PDF 30)

import Mathlib
import Definitions.Def_MetricMSO_certEqGC

namespace MetricMSO

/-- **The translation `σ_M`** from CMSO2[SP, EqGC] to CMSO2.

Chakraborty, Ordyniak, Siebertz (arXiv:2610.41974, sha256 prefix ad3c5863), §4.3, p.28 (PDF 30):
"For φ ∈ CMSO1[SP, EqGC], we obtain σM(φ) ∈ CMSO1 by replacing each SP atom by a fresh copy of
CertSPM and each EqGC atom by a fresh copy of CertEqGCM. We leave all ordinary atoms, including
modulo-counting atoms and unary input predicates, unchanged, and we apply the translation
recursively through Boolean connectives and quantifiers." "For incidence structures, we again
restrict the auxiliary element variables to vertices and the auxiliary set variables to subsets
of V(G)."

`sigma M φ dV dS` translates `φ` read in a context with `dV` vertex variables and `dS` vertex-set
variables: every atom `sp P s t` becomes `certSP M P s t` and every atom `eqgc C x y u v` becomes
`certEqGC M C x y u v`, each written for the numbers of vertex and vertex-set variables in scope at
that atom; everything else is kept.

**Formalization Note** "Fresh copies" are the fresh de Bruijn levels above the variables in scope.
The auxiliary variables of the certificates are vertex and vertex-set variables, so edge and
edge-set quantifiers do not change the levels they use. -/
def sigma (M : ℕ) : Formula → ℕ → ℕ → Formula
  | .sp P s t, dV, dS => certSP M P s t dV dS
  | .eqgc C x y u v, dV, dS => certEqGC M C x y u v dV dS
  | .neg φ, dV, dS => .neg (sigma M φ dV dS)
  | .and φ ψ, dV, dS => .and (sigma M φ dV dS) (sigma M ψ dV dS)
  | .exV φ, dV, dS => .exV (sigma M φ (dV + 1) dS)
  | .exE φ, dV, dS => .exE (sigma M φ dV dS)
  | .exVS φ, dV, dS => .exVS (sigma M φ dV (dS + 1))
  | .exES φ, dV, dS => .exES (sigma M φ dV dS)
  | φ, _, _ => φ

end MetricMSO


