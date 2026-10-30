-- Prove2me | Definitions.Def_AKNMixed_FQP_subroutineGate
-- name    : AKNMixed_FQP_subroutineGate
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:15:48.147387+00:00
-- url     : https://prove2.me/theorems/537db34c-b32b-4465-bea7-02f800baa9d2
-- title:
--   Subroutine gate $g_f\circ\rho=\sum_d \Pr(d)\,U_d\rho U_d^\dagger$ (Definition 5)
-- statement:
--   Let $f$ be a probabilistic function from $m$ to $p$ bits. The **subroutine gate** $g_f$ is the super-operator on $m+p$ qubits (input register first)
--
--   $$g_f\circ\rho=\sum_{d}\Pr(d)\,U_d\,\rho\,U_d^{\dagger},\qquad \Pr(d)=\prod_{i\in\{0,1\}^m} f_{i,d(i)},$$
--
--   where the sum runs over all deterministic functions $d:\{0,1\}^m\to\{0,1\}^p$ and $U_d$ is the permutation $|i,x\rangle\mapsto|i,x\oplus d(i)\rangle$. Each deterministic function is applied with the probability induced by $f$.
--
--   **Formalization Note** $U_d$ is the exclusive-or completion `detPerm d` of the paper's $U_d|i,0\rangle=|i,d(i)\rangle$. The real weights are cast to $\mathbb C$.
-- source:
--   Aharonov, Kitaev, Nisan, Quantum Circuits with Mixed States, arXiv:quant-ph/9806029v1, Definition 5, p. 10

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_AKNMixed_FQP_ProbFun
import Definitions.Def_AKNMixed_FQP_detPerm

namespace AKNMixed.FQP

open QAlgorithms Matrix

/-- **The subroutine gate `g_f ∘ ρ = Σ_d Pr(d) U_d ρ U_d†`.**
Aharonov, Kitaev, Nisan, *Quantum Circuits with Mixed States*, arXiv:quant-ph/9806029v1,
Definition 5, p. 10: "g_f ∘ ρ = Σ_d Pr(d) U_d ρ U_d† Where the sum is over all deterministic
functions d : {0,1}^m ⟼ {0,1}^p, U_d is defined by U_d|i, 0⟩ = |i, d(i)⟩ and the induced
probability for d is: Pr(d) = Π_i Prob(i ↦ d(i)) = Π_i f_{i,d(i)}."

For a probabilistic function `f : {0,1}^m → distributions on {0,1}^p`, `subroutineGate f` is the
super-operator on `m + p` qubits (input register first) that applies every deterministic
`d : {0,1}^m → {0,1}^p` with weight `∏ᵢ f_{i,d(i)}`.

**Formalization Note.** `U_d` is `detPerm d`, the exclusive-or completion
`|i, x⟩ ↦ |i, x ⊕ d(i)⟩` of the paper's `U_d|i, 0⟩ = |i, d(i)⟩`. The real weights are cast to
`ℂ`. -/
noncomputable def subroutineGate {m p : ℕ} (f : ProbFun m p) :
    Superop (Qubits m × Qubits p) (Qubits m × Qubits p) :=
  fun ρ => ∑ d : Qubits m → Qubits p,
    ((∏ i, f.prob i (d i) : ℝ) : ℂ) • (detPerm d * ρ * (detPerm d)ᴴ)

end AKNMixed.FQP


