-- Prove2me | Definitions.Def_AlgoTransparency_Params
-- name    : AlgoTransparency_Params
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:48:22.64117+00:00
-- url     : https://prove2.me/theorems/ecc0a3e2-cff0-4b3c-bc29-9bb0fff1bde7
-- title:
--   Model parameters $\theta,\lambda,R,\alpha,\beta$
-- statement:
--   The hiring model of §3 has five real parameters:
--
--   1. $\theta$, the share of high-talent (type H) agents in a population of mass 1;
--   2. $\lambda$, the strength of the correlational feature: a share $\lambda$ of H agents and a share $1-\lambda$ of L agents have value 1 on it;
--   3. $R$, the reward (wage) the firm pays to every hired agent;
--   4. $\alpha$, the productivity premium of being type H;
--   5. $\beta$, the productivity premium of education, so that an agent's productivity is $W(T,\mathrm{Education})=\alpha\,\mathbf 1(T=H)+\beta\,\mathbf 1(\mathrm{Education}=1)$ (eq. (1)).
--
--   The agents' education costs $C_H$ and $C_L$ are kept outside this record, because the paper states its results over the $(C_H,C_L)$ plane.
--
--   **Formalization Note** $\lambda$ is a reserved word in Lean, so the field is called `lam`. The standing assumptions are the separate predicate `Standing`.
-- source:
--   Wang, Huang, Jasin & Singh, Algorithmic Transparency with Strategic Users, arXiv:2008.09283v1, §3 and §3.1, pp.11–14 (PDF 12–15), eq. (1)

import Mathlib

namespace AlgoTransparency

/-- **Model parameters** of Wang, Huang, Jasin & Singh, *Algorithmic Transparency with Strategic
Users*, arXiv:2008.09283v1, §3 and §3.1, pp.11–14 (PDF 12–15).

* `θ` — the share of high-talent (type H) agents; the mass of agents is normalized to 1;
* `lam` — the paper's `λ`: a `λ` share of H agents and a `1 − λ` share of L agents have value 1
  on the firm's correlational feature (p.12, PDF 13);
* `R` — the reward (wage) the firm pays to a hired agent (p.14, PDF 15);
* `α` — the marginal productivity effect of being type H, eq. (1) (p.13, PDF 14);
* `β` — the marginal productivity effect of education, eq. (1) (p.13, PDF 14).

The agents' education costs `C_H`, `C_L` are not part of this structure: every statement of the
mission takes them as two separate real arguments, since the paper's results are stated over the
`(C_H, C_L)` plane.

**Formalization Note.** `λ` is a reserved word in Lean, so the field is called `lam`. All five
parameters are real numbers; their standing assumptions are the separate predicate
`AlgoTransparency.Standing`. -/
structure Params where
  /-- share of type-H agents -/
  θ : ℝ
  /-- the paper's `λ` (correlation of the correlational feature with type H) -/
  lam : ℝ
  /-- reward (wage) paid to a hired agent -/
  R : ℝ
  /-- productivity premium of type H -/
  α : ℝ
  /-- productivity premium of education -/
  β : ℝ

end AlgoTransparency


