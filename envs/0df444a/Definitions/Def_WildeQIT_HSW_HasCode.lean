-- Prove2me | Definitions.Def_WildeQIT_HSW_HasCode
-- name    : WildeQIT_HSW_HasCode
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T19:12:45.948729+00:00
-- url     : https://prove2.me/theorems/00aec34c-46d9-417b-9235-ad0edeaa4595
-- title:
--   Code for classical communication with $n$ channel uses, $|\mathcal M|$ messages and maximal error $\le\varepsilon$
-- statement:
--   Let $\mathcal N_{A'\to B}$ be a quantum channel, $n\ge 0$ a number of channel uses, $|\mathcal M|$ a number of messages and $\varepsilon$ a real number. The channel has a code with these parameters if there exist
--
--   1. for every message $m\in\mathcal M = \{1,\dots,|\mathcal M|\}$ a density operator $\rho^m_{A'^n}$ on $\mathcal H_{A'}^{\otimes n}$ (possibly entangled across the $n$ channel inputs), and
--   2. a POVM $\{\Lambda_m\}_{m\in\mathcal M}$ on $\mathcal H_B^{\otimes n}$,
--
--   such that the error probability of every message is at most $\varepsilon$:
--
--   $$
--   p_e(m) = \mathrm{Tr}\{(I-\Lambda_m)\,\mathcal N^{\otimes n}(\rho^m_{A'^n})\} \le \varepsilon \qquad\text{for all } m\in\mathcal M,
--   $$
--
--   that is, the maximal probability of error $p^*_e \equiv \max_m p_e(m)$ is at most $\varepsilon$. The rate of such an $(n, C, \varepsilon)$ code is $C = \frac1n\log_2|\mathcal M|$.
--
--   This is the most general protocol for sending classical messages over $n$ uses of a quantum channel without assistance.
--
--   **Formalization Note** The message set is $\{0,\dots,|\mathcal M|-1\}$; $\mathcal N^{\otimes n}$ is `WildeQIT.HSW.tensorPowMap`; the trace is real for these operators and its real part is taken.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, §20.2.1, (20.10)–(20.15), p. 562

import Mathlib
import Definitions.Def_WildeQIT_QChannel
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_WildeQIT_QMemory_IsPOVM
import Definitions.Def_WildeQIT_HSW_tensorPowMap

namespace WildeQIT.HSW

/-- Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, §20.2.1, (20.10)–(20.14),
p. 562: the channel `N` has a **code for classical communication** with `n` channel uses, `M`
messages and maximal error probability at most `ε`: Alice encodes message `m` into a state
`ρ^m_{A′ⁿ}` (possibly entangled across the `n` channel inputs), Bob decodes with a POVM `{Λ_m}`
on `Bⁿ`, and `p_e(m) = Tr{(I − Λ_m) N^⊗n(ρ^m_{A′ⁿ})} ≤ ε` for every message `m`, i.e.
`p*_e ≡ max_m p_e(m) ≤ ε` (20.14). The rate of such an `(n, C, ε)` code is `C = (1/n) log |M|`
(20.15).

**Formalization Note.** The message set `{1, …, |M|}` is `Fin M`; states are
`WildeQIT.IsDensityOperator` on `Fin n → A`, the POVM is `WildeQIT.QMemory.IsPOVM` on `Fin n → B`,
and `N^⊗n` is `WildeQIT.HSW.tensorPowMap N n`. The trace of `(I − Λ_m)ρ` is real for these
operators; its real part is taken. -/
def HasCode {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (N : WildeQIT.QChannel A B) (n M : ℕ) (ε : ℝ) : Prop :=
  ∃ (ρ : Fin M → Matrix (Fin n → A) (Fin n → A) ℂ)
    (Λ : Fin M → Matrix (Fin n → B) (Fin n → B) ℂ),
    (∀ m, WildeQIT.IsDensityOperator (ρ m)) ∧ WildeQIT.QMemory.IsPOVM Λ ∧
    ∀ m, (Matrix.trace ((1 - Λ m) * tensorPowMap N n (ρ m))).re ≤ ε

end WildeQIT.HSW


