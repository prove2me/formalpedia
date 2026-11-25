-- Prove2me | Definitions.Def_erdos_dyadic_rho
-- name    : erdos_dyadic_rho
-- status  : Definition
-- author  : @Jhon Lenin Acuna
-- created : 2026-11-25T04:14:13.244864+00:00
-- url     : https://prove2.me/theorems/2ce7b937-f85e-4078-9f3a-bf004459786b
-- title:
--   Density $\rho(H)=m(H\cap[0,1])$ in one period
-- statement:
--   For $H\subseteq\mathbb R$, the **density in one period** is
--   $$\rho(H)=m\bigl(H\cap[0,1]\bigr)\in[0,\infty],$$
--   where $m$ is Lebesgue measure on $\mathbb R$. For a measurable 1-periodic set this is the normalized Lebesgue measure of its image in $\mathbb T$.
--
--   **Formalization Note** Lean defines $\rho$ for every set (using the outer measure) with values in $[0,\infty]$; the statements that use it assume measurability or openness where the paper does.
-- source:
--   OpenAI, The dyadic case of the Erdős similarity conjecture, Sept 25, 2026, https://github.com/openai/math/tree/main/preprints/The-dyadic-case-of-the-Erdos-similarity-conjecture-September-25-2026, Section 2, p. 3 (definition of ρ(A))

import Mathlib

open MeasureTheory Set

namespace ErdosDyadic

/-- Density of a 1-periodic set in one period: ρ(H) = m(H ∩ [0,1]). -/
noncomputable def rho (H : Set ℝ) : ENNReal := volume (H ∩ Icc 0 1)

end ErdosDyadic


