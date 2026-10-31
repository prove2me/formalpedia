-- Prove2me | Definitions.Def_AlgoTransparency_massHO
-- name    : AlgoTransparency_massHO
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:49:11.720393+00:00
-- url     : https://prove2.me/theorems/b5f18891-c968-4997-9e78-6bfad6e06b51
-- title:
--   Mass $n^H_S$ of H agents in each opaque state
-- statement:
--   If every type-H agent improves education with probability $q_H\in[0,1]$, the (expected) mass of H agents in each opaque state is
--
--   $$
--   n^H_A=\theta\lambda(1-q_H),\quad n^H_B=\theta\lambda q_H,\quad n^H_C=\theta(1-\lambda)(1-q_H),\quad n^H_D=\theta(1-\lambda)q_H .
--   $$
--
--   **Formalization Note** Agents of the same type use the same strategy (p.14); improving "with some probability" (p.17) is read as a common mixed strategy $q_H$, and masses are expected masses, as in App. A.1.
-- source:
--   Wang, Huang, Jasin & Singh, Algorithmic Transparency with Strategic Users, arXiv:2008.09283v1, §3.1 and §4, pp.14, 16–17 (PDF 15, 17–18); App. A.1, pp.41–44

import Mathlib
import Definitions.Def_AlgoTransparency_Params
import Definitions.Def_AlgoTransparency_OState

namespace AlgoTransparency

/-- **Mass of type-H agents in each opaque state**, `n^H_S`, Wang, Huang, Jasin & Singh,
arXiv:2008.09283v1, §3.1 and §4, pp.14, 16–17 (PDF 15, 17–18), when every H agent improves
education with probability `qH`:

* `n^H_A = θλ(1 − qH)`, `n^H_B = θλ qH`,
* `n^H_C = θ(1 − λ)(1 − qH)`, `n^H_D = θ(1 − λ) qH`.

**Formalization Note.** "Agents of the same type use the same strategy" (p.14); a type that
improves "with some probability" (p.17) is read as a common mixed strategy `qH ∈ [0, 1]`, and
`n^H_S` is the expected mass, as in the paper's own case computations (App. A.1, pp.42–44).
A share `λ` of H agents is high on the correlational feature (p.12). -/
def massHO (p : Params) (qH : ℝ) : OState → ℝ
  | .A => p.θ * p.lam * (1 - qH)
  | .B => p.θ * p.lam * qH
  | .C => p.θ * (1 - p.lam) * (1 - qH)
  | .D => p.θ * (1 - p.lam) * qH

end AlgoTransparency


