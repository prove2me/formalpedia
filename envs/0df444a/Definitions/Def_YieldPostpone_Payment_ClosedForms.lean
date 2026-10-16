-- Prove2me | Definitions.Def_YieldPostpone_Payment_ClosedForms
-- name    : YieldPostpone_Payment_ClosedForms
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T21:24:26.510731+00:00
-- url     : https://prove2.me/theorems/a9405dcc-1c1f-4d43-b1de-c0699d502eed
-- title:
--   Appendix B equilibrium outcome formulas
-- statement:
--   For each of OA, OR, DA, and DR, this file records the Appendix B equilibrium outcome triples: retailer profit, supplier profit, and expected consumer surplus. The functions $F^{OA}_1,F^{OA}_2,F^{OA}_3$, $F^{OR}_1,F^{OR}_2$, $F^{DA}_1,F^{DA}_2$, and $F^{DR}_1,F^{DR}_2,F^{DR}_3$ evaluate the corresponding displayed formulas at parameters $(a,b,\alpha,\theta,c)$.
--
--   $$F^k_j(a,b,\alpha,\theta,c)=(\pi_R^k,\pi_S^k,CS^k)\quad\text{on the }j\text{th cost interval of scenario }k.$$
--
--   These are formula definitions, not the definition of equilibrium: the model computes actual profit and surplus from strategies. The lemmas assert that these formulas agree with equilibrium outcomes.
--
--   **Formalization Note** The OA positive part $[x]^+$ is read as $\max\{0,x\}$, as in Lemma 1. The middle DR surplus has one fewer factor of $\alpha^2(1-\theta)+\theta$ in the denominator than the printed B.4 value, making it consistent with the equilibrium production tie convention. The equality $F^{DR}_3=F^{OR}_2$ is the displayed equality of their third and second formulas.
-- source:
--   Geng, Guo, Xiao, Yang, Supply Risk Mitigation in a Decentralized Supply Chain: Pricing Postponement or Payment Postponement?, SSRN 3546872 (author version), App. B.1–B.4, PDF pp. 35–37 (appendix pp. 3–5), equilibrium summaries

import Definitions.Def_YieldPostpone_Payment_Setting

noncomputable section

namespace YieldPostpone.Payment

def OA1 (P : Params) (c : ℝ) : ℝ × ℝ × ℝ :=
  ((P.a * P.α - P.b * c) ^ 2 / (16 * P.b * P.α ^ 2),
   (P.a * P.α - P.b * c) ^ 2 / (8 * P.b * P.α ^ 2),
   (P.a * P.α - P.b * c) ^ 2 / (32 * P.b * P.α ^ 2))

def OA2 (P : Params) (c : ℝ) : ℝ × ℝ × ℝ :=
  ((P.a * P.α - P.b * what P) ^ 2 / (4 * P.b * P.α ^ 2),
   (P.a * P.α - P.b * what P) * (what P - c) / (2 * P.α ^ 2),
   (P.a * P.α - P.b * what P) ^ 2 / (8 * P.b * P.α ^ 3))

def OA3 (P : Params) (c : ℝ) : ℝ × ℝ × ℝ :=
  ((P.a * P.μ - P.b * c) ^ 2 / (16 * P.b * P.μ),
   (P.a * P.μ - P.b * c) ^ 2 / (8 * P.b * P.μ),
   (P.a * P.μ - P.b * c) ^ 2 *
      (P.α * (2 - P.α) * (1 - P.θ) + P.θ) / (32 * P.b * P.μ ^ 2))

def OR1 (P : Params) (c : ℝ) : ℝ × ℝ × ℝ :=
  ((P.a * P.α * (1 - P.θ) - P.b * c) ^ 2 /
      (16 * P.b * P.α ^ 2 * (1 - P.θ)) + P.a ^ 2 * P.θ / (4 * P.b),
   (P.a * P.α * (1 - P.θ) - P.b * c) ^ 2 /
      (8 * P.b * P.α ^ 2 * (1 - P.θ)),
   (P.a * P.α * (1 - P.θ) - P.b * c) ^ 2 /
      (32 * P.b * P.α ^ 2 * (1 - P.θ)) + P.a ^ 2 * P.θ / (8 * P.b))

def OR2 (P : Params) (c : ℝ) : ℝ × ℝ × ℝ :=
  ((P.a * P.μ - P.b * c) ^ 2 /
      (16 * P.b * (P.α ^ 2 * (1 - P.θ) + P.θ)),
   (P.a * P.μ - P.b * c) ^ 2 /
      (8 * P.b * (P.α ^ 2 * (1 - P.θ) + P.θ)),
   (P.a * P.μ - P.b * c) ^ 2 /
      (32 * P.b * (P.α ^ 2 * (1 - P.θ) + P.θ)))

def DA1 (P : Params) (c : ℝ) : ℝ × ℝ × ℝ :=
  ((P.b * c - P.a * P.α) ^ 2 / (16 * P.b * P.α ^ 2),
   (P.b * c - P.a * P.α) ^ 2 / (8 * P.b * P.α ^ 2),
   (P.b * c - P.a * P.α) ^ 2 / (32 * P.b * P.α ^ 2))

def DA2 (P : Params) (c : ℝ) : ℝ × ℝ × ℝ :=
  ((P.b * c - P.a * P.μ) ^ 2 / (16 * P.b * P.μ),
   (P.b * c - P.a * P.μ) ^ 2 / (8 * P.b * P.μ),
   (P.b * c - P.a * P.μ) ^ 2 *
      (P.α * (2 - P.α) * (1 - P.θ) + P.θ) / (32 * P.b * P.μ ^ 2))

def DR1 (P : Params) (c : ℝ) : ℝ × ℝ × ℝ :=
  ((P.b * c - P.a * P.α) ^ 2 / (16 * P.b * P.α ^ 2),
   (P.a * P.α - P.b * c) ^ 2 / (8 * P.b * P.α ^ 2),
   (P.b * c - P.a * P.α) ^ 2 / (32 * P.b * P.α ^ 2))

def DR2 (P : Params) (c : ℝ) : ℝ × ℝ × ℝ :=
  (P.μ ^ 2 * (P.a * P.α * (1 - P.θ) - P.b * c) ^ 2 /
      (4 * P.b * P.α ^ 2 * (1 - P.θ) ^ 2 *
        (P.α ^ 2 * (1 - P.θ) + P.θ)),
   P.μ * P.θ * c * (P.a * P.α * (1 - P.θ) - P.b * c) /
      (2 * P.α ^ 2 * (1 - P.θ) ^ 2 *
        (P.α ^ 2 * (1 - P.θ) + P.θ)),
   P.μ ^ 2 * (P.a * P.α * (1 - P.θ) - P.b * c) ^ 2 /
      (8 * P.b * P.α ^ 2 * (1 - P.θ) ^ 2 *
        (P.α ^ 2 * (1 - P.θ) + P.θ)))

def DR3 (P : Params) (c : ℝ) : ℝ × ℝ × ℝ := OR2 P c

end YieldPostpone.Payment


