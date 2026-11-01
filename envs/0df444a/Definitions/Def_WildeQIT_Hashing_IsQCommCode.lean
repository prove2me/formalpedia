-- Prove2me | Definitions.Def_WildeQIT_Hashing_IsQCommCode
-- name    : WildeQIT_Hashing_IsQCommCode
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:20:55.585489+00:00
-- url     : https://prove2.me/theorems/442af47b-75cb-499f-a691-3abffb76c3ea
-- title:
--   $(n,Q,\varepsilon)$ quantum communication code: $\tfrac12\|\varphi_{RA_1}-\omega_{RB_1}\|_1\le\varepsilon$ for all $\varphi$
-- statement:
--   Let $\mathcal E_{A_1\to A'^n}$ be an encoding channel, $\mathcal N_{A'^n\to B^n}$ the $n$ channel uses and $\mathcal D_{B^n\to B_1}$ a decoding channel, where $B_1$ has the dimension of $A_1$. They form a **quantum communication code with error $\varepsilon$** (entanglement transmission) when $\mathcal E$ and $\mathcal D$ are quantum channels and, for every pure state $|\varphi\rangle_{RA_1}$ with a reference $R$ of the dimension of $A_1$,
--
--   $$
--   \tfrac12\bigl\|\varphi_{RA_1}-\omega_{RB_1}\bigr\|_1\le\varepsilon,\qquad
--   \omega_{RB_1}=(\mathrm{id}_R\otimes\mathcal D\circ\mathcal N\circ\mathcal E)(\varphi_{RA_1}).
--   $$
--
--   The rate of the code is $Q=\frac1n\log\dim\mathcal H_{A_1}$. Preserving entanglement with an arbitrary reference is the strongest of the usual quantum-communication criteria; it covers the transmission of arbitrary pure and mixed states.
--
--   **Formalization Note** $A_1=B_1$ is a finite type `a`; channels are `QAlgorithms.Superop` maps, encoder and decoder satisfy the published `IsChannel` (a finite normalized Kraus family); the reference is the first tensor factor (`idTensorSuperop`); $\|\cdot\|_1$ is the published `WildeQIT.traceNorm`.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, §24.1, pp. 658–659, (24.1)–(24.3)

import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_WildeQIT_traceNorm

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, §24.1, pp. 658–659,
(24.1)–(24.2) (an `(n, Q, ε)` quantum communication code, entanglement transmission).
-/

namespace WildeQIT.Hashing

open QAlgorithms

/-- **Quantum communication code with error `ε`** (Wilde, *From Classical to Quantum Shannon
Theory*, arXiv:1106.1445v8, §24.1, pp. 658–659, (24.1)–(24.2)): an encoding channel
`E_{A₁→A′ⁿ}`, the `n` channel uses `N_{A′ⁿ→Bⁿ}` and a decoding channel `D_{Bⁿ→B₁}` (with `B₁`
of the dimension of `A₁`) such that for **every** pure state `|φ⟩_{RA₁}`, with the reference `R`
of the dimension of `A₁`,
`½ ‖φ_{RA₁} − ω_{RB₁}‖₁ ≤ ε`, where `ω_{RB₁} = (id_R ⊗ D ∘ N ∘ E)(φ_{RA₁})`.

**Formalization Note.** `A₁ = B₁` is the finite type `a`, the channel input `A′ⁿ` is `x` and
its output `Bⁿ` is `y`. Encoder and decoder are quantum channels in the published sense
`IsChannel` (a finite normalized Kraus family); the channel `Nn` is given as a map. The reference
is the first factor of `a × a` (published `idTensorSuperop`), `φ_{RA₁} = |φ⟩⟨φ|` with `‖φ‖ = 1`,
and `‖·‖₁` is the published `WildeQIT.traceNorm`. The rate `(1/n) log dim ℋ_{A₁}` of (24.3) is
recorded by the statements that use this predicate. -/
def IsQCommCode {a x y : Type} [Fintype a] [DecidableEq a] [Fintype x] [DecidableEq x]
    [Fintype y] [DecidableEq y] (Enc : Superop a x) (Nn : Superop x y) (Dec : Superop y a)
    (ε : ℝ) : Prop :=
  IsChannel Enc ∧ IsChannel Dec ∧
    ∀ φ : EuclideanSpace ℂ (a × a), ‖φ‖ = 1 →
      (1 / 2 : ℝ) * WildeQIT.traceNorm
        (pureDensity φ - idTensorSuperop (R := a) (Dec ∘ Nn ∘ Enc) (pureDensity φ)) ≤ ε

end WildeQIT.Hashing


