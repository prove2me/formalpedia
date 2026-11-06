-- Prove2me | Definitions.Def_AutoQMem_Lindblad_IsQuantumMemoryUpTo
-- name    : AutoQMem_Lindblad_IsQuantumMemoryUpTo
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T21:00:21.918037+00:00
-- url     : https://prove2.me/theorems/63fe1e8a-f26e-4342-a1bd-43505520547d
-- title:
--   Quantum $\epsilon$-memory and classical $q$-remembering up to time $t$
-- statement:
--   For a family of physical channels $\mathcal W_{*,a}$ indexed by the readout time $a$, the encoded system is a **quantum $\epsilon$-memory up to time $t$** if
--   $$\inf_{a\in[0,t]}F_{\min}[\mathcal W_{*,a}]\ge1-\epsilon .$$
--   A classical process $(\xi_a)$ **$q$-remembers** $b$ up to time $t$ if
--   $$\sup_{a\in[0,t]}\Pr[b(\xi_a)\neq b(\xi_0)]\le q .$$
--
--   **Formalization Note** Both are written as pointwise bounds for every $a\in[0,t]$, which is equivalent. The classical notion takes the function $a\mapsto\Pr[b(\xi_a)\ne b(\xi_0)]$ as input.
-- source:
--   Drechsler, Oreg, Aharonov, Autonomous Quantum Memories from Classical Stochastic Processes, arXiv:2610.05589 (PDF of 2026-11-03), Definition 2.20, eq. (28), p. 19 (PDF p. 21); Definition 2.21, eq. (29), p. 19

import Mathlib
import Definitions.Def_AutoQMem_Lindblad_LogicalQubit_Fmin
open Matrix

namespace AutoQMem.Lindblad

variable {n' mX mZ : ℕ} {C : CSSCode (n' + 1) mX mZ}

/-- **Quantum ε-memory up to time t.** Drechsler, Oreg, Aharonov, *Autonomous Quantum Memories from Classical Stochastic Processes*,
arXiv:2610.05589 (PDF of 2026-11-03), Definition 2.20, eq. (28), p. 19 (PDF 21): "The encoded
system is a quantum ϵ_mem-memory on I if inf_{a∈I} F_min[W_{*,a}] ≥ 1 − ϵ_mem. For continuous-time
dynamics up to time t, we take I = [0, t]."

**Formalization Note.** The infimum condition is written as the equivalent pointwise bound
`∀ a ∈ [0, t], 1 - ε ≤ F_min[W(a)]`. `W a` is the physical channel at readout time `a`. -/
def IsQuantumMemoryUpTo (Q : LogicalQubit C) (DX : Decoder C.HX) (DZ : Decoder C.HZ)
    (W : ℝ → Op (n' + 1) → Op (n' + 1)) (t ε : ℝ) : Prop :=
  ∀ a ∈ Set.Icc (0 : ℝ) t, 1 - ε ≤ Q.Fmin DX DZ (W a)

/-- **q-remembering up to time t.** Drechsler, Oreg, Aharonov, *Autonomous Quantum Memories from Classical Stochastic Processes*,
arXiv:2610.05589 (PDF of 2026-11-03), Definition 2.21, eq. (29), p. 19 (PDF 21): "the process
q-remembers b : Ω → S on I if sup_{a∈I} Pr[b(ξ_a) ≠ b(ξ_{a_0})] ≤ q … We refer to the case I = [0, t]
… as remembering up to time t."

**Formalization Note.** `pr a` is the probability `Pr[b(ξ_a) ≠ b(ξ_0)]`; the supremum condition
is written as the equivalent pointwise bound `∀ a ∈ [0, t], pr a ≤ q`. -/
def RemembersUpTo (pr : ℝ → ℝ) (t q : ℝ) : Prop :=
  ∀ a ∈ Set.Icc (0 : ℝ) t, pr a ≤ q

end AutoQMem.Lindblad


