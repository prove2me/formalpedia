-- Prove2me | Definitions.Def_WildeQIT_EntManip_IsManipProtocol
-- name    : WildeQIT_EntManip_IsManipProtocol
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T18:38:08.267508+00:00
-- url     : https://prove2.me/theorems/07ab067c-bf85-4ea3-a76d-89a15d938618
-- title:
--   $(n, m/n, \varepsilon)$ entanglement manipulation protocol
-- statement:
--   Let $|\psi\rangle_{AB},|\varphi\rangle_{AB}\in\mathcal H_A\otimes\mathcal H_B$, let $n,m\in\mathbb N$ and $\varepsilon\in\mathbb R$. An **$(n,m/n,\varepsilon)$ entanglement manipulation protocol** for $\psi\to\varphi$ is an LOCC channel $\Lambda^{(n)}_{A^nB^n\to A^mB^m}$ such that the state $\omega_{A^mB^m}\equiv\Lambda^{(n)}(\psi_{AB}^{\otimes n})$ satisfies
--
--   $$
--   \frac12\left\|\omega_{A^mB^m}-\varphi_{AB}^{\otimes m}\right\|_1\le\varepsilon .
--   $$
--
--   Its rate of entanglement conversion is $m/n$.
--
--   **Formalization Note** The predicate asserts that such an LOCC channel exists. $A^n$, $B^n$ are indexed by `Fin n → a`, `Fin n → b`; $\|\cdot\|_1$ is the published `WildeQIT.traceNorm`, and $|\psi\rangle\langle\psi|$ the published `ObliviousRSP.pureState`.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, §19.3, (19.45)–(19.46), p. 540

import Mathlib
import Definitions.Def_WildeQIT_traceNorm
import Definitions.Def_WildeQIT_EntManip_IsLOCC
import Definitions.Def_ObliviousRSP_pureState
import Definitions.Def_WildeQIT_EntManip_tensorPowVec

namespace WildeQIT.EntManip

/-- **`(n, m/n, ε)` entanglement manipulation protocol** (Wilde, *From Classical to Quantum
Shannon Theory*, arXiv:1106.1445v8, §19.3, p. 540): Alice and Bob begin with `n` copies of
`|ψ⟩_{AB}` and perform an LOCC channel `Λ^{(n)}_{AⁿBⁿ→AᵐBᵐ}` to convert `(|ψ⟩_{AB})^{⊗n}` to `m`
copies of `|φ⟩_{AB}`; with `ω_{AᵐBᵐ} ≡ Λ^{(n)}(ψ^{⊗n}_{AB})` (19.45), the protocol has `ε` error if
`(1/2)‖ω_{AᵐBᵐ} − φ^{⊗m}_{AB}‖₁ ≤ ε` (19.46). The rate of entanglement conversion is `m/n`.

`IsManipProtocol ψ φ n m ε` says that such an LOCC channel exists.

**Formalization Note** `Aⁿ` is indexed by `Fin n → a`, `Bⁿ` by `Fin n → b` (`tensorPowVec`);
`‖·‖₁` is the published `WildeQIT.traceNorm`; `|ψ⟩⟨ψ|` is the published
`ObliviousRSP.pureState` (`vecMulVec ψ (star ψ)`); `IsLOCC` is §19.2's LOCC class. -/
def IsManipProtocol {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (ψ φ : a × b → ℂ) (n m : ℕ) (ε : ℝ) : Prop :=
  ∃ Λ : Matrix ((Fin n → a) × (Fin n → b)) ((Fin n → a) × (Fin n → b)) ℂ →
      Matrix ((Fin m → a) × (Fin m → b)) ((Fin m → a) × (Fin m → b)) ℂ,
    IsLOCC Λ ∧
      (1 / 2 : ℝ) * WildeQIT.traceNorm
        (Λ (ObliviousRSP.pureState (tensorPowVec ψ n))
          - ObliviousRSP.pureState (tensorPowVec φ m)) ≤ ε

end WildeQIT.EntManip


