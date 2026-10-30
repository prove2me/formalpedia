-- Prove2me | Definitions.Def_AcquihiringAudit_Bargaining_vUpperExtended
-- name    : AcquihiringAudit_Bargaining_vUpperExtended
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T14:31:07.87558+00:00
-- url     : https://prove2.me/theorems/71948a92-6c78-4801-bfc4-72a18734409d
-- title:
--   Extended upper hiring threshold, including parameter endpoints
-- statement:
--   For real productive values $v_a,v_s$, startup benefit $b$ and wage floor $\underline w$, write $P=(v_a,v_s,b,\underline w)$. For real bargaining power $\alpha$ and post-failure poaching probability $\delta$, define
--
--   $$U(P,\alpha,\delta)=\begin{cases}v_s+b+\dfrac{\alpha}{(1-\alpha)(1-\delta)}[\delta(v_s-\underline w)+b]&\alpha<1\text{ and }\delta<1,\\+\infty&\text{otherwise}.\end{cases}$$
--
--   On the model's parameter square $[0,1]^2$, the second branch means $\alpha=1$ or $\delta=1$. It corrects the undefined endpoint quotient in Proposition 2 while leaving its interior formula unchanged. Outside that square the same branch rule makes this a total definition, with no economic claim. The result uses only the square with $0<\alpha\delta<1$.
--
--   This threshold is shared by all three hiring-region comparisons of the full-domain proposition. It reuses the published model and its finite upper-threshold formula; it adds no assumption on wages or productive values.
--
--   **Formalization Note** The codomain is the extended real line. Interior arithmetic is entirely real; the result is then embedded into the extended reals. At the endpoints the value is explicitly $+\infty$, with no use of a default real quotient at zero.
-- source:
--   Bar-Isaac, Johnson and Nocke, Acquihiring for Monopsony Power, CRC TR 224 Discussion Paper No. 500, January 22, 2024, Proposition 2, printed p. 9 / PDF p. 10; https://www.crctr224.de/research/discussion-papers/archive/dp500; PDF SHA-256 1d145f10d566016d690609bf85c10e38505da5adf94960de74e182b3ad469cd9. Endpoint limits: Corollaries 1–2, printed pp. 9–10 / PDF pp. 10–11.

import Mathlib
import Definitions.Def_AcquihiringMonopsony_Bargaining_NashSplit

namespace AcquihiringAudit.Bargaining

/-- Proposition 2, printed p. 9 / PDF 10, with its undefined endpoint quotient corrected.
On `α, δ ∈ [0,1]`, this is the printed real threshold if both are below one, and
`+∞` if either equals one. Outside that parameter square the same total branch rule
is used, but no economic interpretation is asserted. Only finite real arithmetic
is used in the interior branch; no extended-real addition or subtraction is needed. -/
noncomputable def vUpperExtended (P : AcquihiringMonopsony.Baseline.Params)
    (α δ : ℝ) : EReal :=
  if α < 1 ∧ δ < 1 then
    (AcquihiringMonopsony.Bargaining.vUpper P α δ : EReal)
  else ⊤

end AcquihiringAudit.Bargaining


