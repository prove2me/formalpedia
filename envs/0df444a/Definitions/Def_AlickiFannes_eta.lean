-- Prove2me | Definitions.Def_AlickiFannes_eta
-- name    : AlickiFannes_eta
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:21:01.616481+00:00
-- url     : https://prove2.me/theorems/54ac1cae-ffd9-4e6b-a3cb-157ff2a92702
-- title:
--   The entropy function $\eta(x) = -x\log x$
-- statement:
--   For a real number $x$ put
--
--   $$
--   \eta(x) = -x \log_2 x, \qquad \eta(0) = 0 .
--   $$
--
--   The von Neumann entropy of a state $\rho$ is $S(\rho) = \operatorname{Tr}\eta(\rho)$, and the terms $\eta(1-\epsilon) + \eta(\epsilon)$, the binary entropy of $\epsilon$, measure the entropy that mixing two states with weights $1-\epsilon$ and $\epsilon$ can create. The paper evaluates $\eta$ only on $[0,1]$.
--
--   **Formalization Note** The logarithm is to base 2, the base of the published von Neumann entropy `QAlgorithms.vnEntropy` used throughout this mission; the paper leaves the base unstated. Lean's `Real.logb 2 0 = 0` gives $\eta(0) = 0$ as on the page. The function is defined on all of $\mathbb R$; every statement of the mission applies it to points of $[0,1]$.
-- source:
--   Alicki–Fannes, Continuity of quantum conditional information, arXiv:quant-ph/0312081v2, p.1 (definition of η)

import Mathlib

namespace AlickiFannes

/-- Alicki–Fannes, *Continuity of quantum conditional information*, arXiv:quant-ph/0312081v2,
p.1: "η(x) := −x log x for 0 < x ≤ 1 and η(0) = 0", the function whose trace gives the von
Neumann entropy, `S(ρ) = Tr η(ρ)`.

**Formalization Note.** The logarithm is to base 2 (`Real.logb 2`), the base of the published
`QAlgorithms.vnEntropy` this mission uses for `S`; the paper leaves the base unstated and every
term of its bounds is one multiple of `log`, so any fixed base gives the same statements. The
function is total on `ℝ`; `Real.logb 2 0 = 0` gives `η(0) = 0` exactly as on the page. The
paper only evaluates `η` on `[0, 1]`, and so do all statements of this mission. -/
noncomputable def eta (x : ℝ) : ℝ := -(x * Real.logb 2 x)

end AlickiFannes


