-- Prove2me | Definitions.Def_BoundEntPPT_IsDistillable
-- name    : BoundEntPPT_IsDistillable
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T16:01:11.364498+00:00
-- url     : https://prove2.me/theorems/442cca45-864a-4dd8-bd37-6007e4d33c91
-- title:
--   Distillability: outputs of local operations on $\varrho^{\otimes N}$ approach the singlet $\Psi_-$ with positive success probability
-- statement:
--   Let $\varrho$ be an operator on $\mathcal H_A\otimes\mathcal H_B$ and let $\Psi_-=\tfrac1{\sqrt2}(|{\uparrow\downarrow}\rangle-|{\downarrow\uparrow}\rangle)$ be the singlet of Eq. (1). Call $\varrho$ **distillable** if for every $\varepsilon>0$ there are $N\ge0$ and finitely many operators $A_i:\mathcal H_A^{\otimes N}\to\mathbb C^2$, $B_i:\mathcal H_B^{\otimes N}\to\mathbb C^2$ such that the unnormalized two-qubit output $\sigma=\sum_i(A_i\otimes B_i)\varrho^{\otimes N}(A_i\otimes B_i)^\dagger$ of Eq. (5) satisfies
--
--   $$
--   \operatorname{Tr}\sigma>0
--   \qquad\text{and}\qquad
--   \langle\Psi_-|\sigma|\Psi_-\rangle\;\ge\;(1-\varepsilon)\operatorname{Tr}\sigma .
--   $$
--
--   That is, with positive success probability $M=\operatorname{Tr}\sigma$ the normalized output $\sigma/M$ of Eq. (4) has singlet fidelity at least $1-\varepsilon$. This is the paper's notion: Alice and Bob "are able to obtain pure singlet two-qubit pairs for $N$ tending to infinity" (p.2), and "they need not succeed every time, but at least they know when they have been successful" (p.1).
--
--   **Formalization Note** $|\Psi_-\rangle\langle\Psi_-|$ is the published `Dependency50.P42.singletState` on `Fin 2 × Fin 2` ($\uparrow=0$, $\downarrow=1$), and $\langle\Psi_-|\sigma|\Psi_-\rangle=\operatorname{Re}\operatorname{Tr}(|\Psi_-\rangle\langle\Psi_-|\sigma)$. A single output pair is required; a protocol producing several pairs gives one by discarding the rest, which is again an operation of form (4). The operation class is all finite families of Eq. (4) with no completeness constraint, which contains LOCC. The condition $\operatorname{Tr}\sigma>0$ is essential: without it the empty family ($\sigma=0$) would make every operator distillable.
-- source:
--   M. Horodecki, P. Horodecki, R. Horodecki, Mixed-state entanglement and distillation: is there a "bound" entanglement in nature?, arXiv:quant-ph/9801069v1, pp.1–2, Eqs. (1), (4)–(5)

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P42
import Definitions.Def_BoundEntPPT_localOutput
open scoped Matrix ComplexOrder

namespace BoundEntPPT

/-- M. Horodecki, P. Horodecki, R. Horodecki, *Mixed-state entanglement and distillation: is there
a "bound" entanglement in nature?*, arXiv:quant-ph/9801069v1, pp.1–2, Eqs. (1), (4): `ϱ` is
*distillable*: "Alice and Bob are able to obtain pure singlet two-qubit pairs for N tending to
infinity" (p.2), where "They need not succeed every time, but at least they know when they have
been successful" (p.1), and the operations are those of Eq. (4), "the most general operation
producing a two-qubit pair". Formally: for every `ε > 0` there are `N` and a finite family
`(A_i, B_i)` of operators into `C²` whose unnormalized output `σ` (Eq. (5)) has positive trace
(the success probability) and singlet fidelity `⟨Ψ⁻|σ|Ψ⁻⟩ ≥ (1 − ε) Tr σ`.

**Formalization Note.** `Ψ⁻ = (|↑↓⟩ − |↓↑⟩)/√2` of Eq. (1) is the published
`Dependency50.P42.singletState` (`|Ψ⁻⟩⟨Ψ⁻|` on `Fin 2 × Fin 2`, `↑ = 0`, `↓ = 1`), and
`⟨Ψ⁻|σ|Ψ⁻⟩ = Tr(|Ψ⁻⟩⟨Ψ⁻| σ)`. The condition "the normalized output `σ / Tr σ` has singlet fidelity
at least `1 − ε`" is multiplied through by `Tr σ > 0`. Reading: one output pair suffices (a
protocol producing several pairs followed by discarding all but one is again of the form (4)),
and the operation class is all of Eq. (4), with no trace-non-increasing constraint; this class
contains every LOCC protocol. Positivity of `Tr σ` is essential: without it the empty family
(`σ = 0`) would make every matrix distillable. -/
def IsDistillable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (ρ : Matrix (I × J) (I × J) ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N m : ℕ, ∃ A : Fin m → Matrix (Fin 2) (Fin N → I) ℂ,
    ∃ B : Fin m → Matrix (Fin 2) (Fin N → J) ℂ,
      0 < (localOutput ρ N A B).trace.re ∧
      (1 - ε) * (localOutput ρ N A B).trace.re ≤
        (QAlgorithms.Papers.Independent.Dependency50.P42.singletState *
          localOutput ρ N A B).trace.re

end BoundEntPPT


