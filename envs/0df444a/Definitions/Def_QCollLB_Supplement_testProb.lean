-- Prove2me | Definitions.Def_QCollLB_Supplement_testProb
-- name    : QCollLB_Supplement_testProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:10:09.943066+00:00
-- url     : https://prove2.me/theorems/8767642b-ad52-4b95-92ff-8478e19d325e
-- title:
--   Output-bit probability of a one-round algorithm for $k$-to-one Testing
-- statement:
--   Let $\mathbb Z_q=\{0,\dots,q-1\}$ and let $x\in\mathbb Z_q^n$ be an input string. A **one-round $t$-query algorithm** with workspace $W=\mathbb C^w$ applies an input-independent unitary $U_0$ to an input-independent unit start state on $A=I^{\otimes t}\otimes C^{\otimes t}\otimes W$, then one layer of $t$ parallel phase queries to the same input $x$, $O_x^{\otimes t}|i_1,\dots,i_t,c_1,\dots,c_t\rangle=\prod_j\omega_q^{c_jx_{i_j}}|i_1,\dots,i_t,c_1,\dots,c_t\rangle$ with $\omega_q=e^{2\pi\imath/q}$, and then an input-independent unitary $U_1$. It measures $A$ and outputs a bit $\rho\in\{0,1\}$, where $0$ declares that the input is one-to-one and $1$ declares that it is $k$-to-one.
--
--   For a bit $\rho$, the **output probability**
--
--   $$
--   \Pr_x[\rho]=\sum_{z\,:\,\mathrm{out}(z)=\rho}\bigl|\langle z\,|\,U_1(O_x^{\otimes t}\otimes I_W)U_0\,\psi_{\mathrm{start}}\rangle\bigr|^2
--   $$
--
--   is the probability that the algorithm, run on $x$, outputs $\rho$.
--
--   This is the success measure of $k$-to-one Testing (Definition 2.1): an algorithm succeeds with probability at least $1/2+\varepsilon$ on every promised input when $\Pr_x[0]\ge 1/2+\varepsilon$ for every one-to-one $x$ and $\Pr_x[1]\ge 1/2+\varepsilon$ for every $k$-to-one $x$.
--
--   **Formalization Note** The algorithm and the oracle are the published `QCollLB.OneRoundAlg` and `QCollLB.parPhaseOracle`. The final measurement is a computational-basis measurement of the whole register followed by an arbitrary output map `out` to `Fin 2`; with an arbitrary $U_1$ and workspace this is the same class as an arbitrary two-outcome projective measurement.
-- source:
--   Peng–Wu, Quantum Lower Bounds for Collision Problems, arXiv:2611.01767 (PDF sha256 4e5aba34…d9fc), Definition 2.1 p.15, Eq. (6) p.15, proof of Theorem 1.3 p.63 (output bit convention)

import Mathlib
import Definitions.Def_QCollLB_OneRound

set_option autoImplicit false

namespace QCollLB.Supplement

open QAlgorithms

/-- The probability that the one-round `t`-query algorithm `A`, run on the input `x ∈ Z_q^n` with the
`t`-fold phase oracle on one shared input, outputs the bit `ρ` (Peng–Wu, *Quantum Lower Bounds for
Collision Problems*, arXiv:2611.01767 (PDF sha256 4e5aba34…d9fc), Definition 2.1, p.15 (`k`-to-one
Testing); Eq. (6), p.15 (one-round algorithms); proof of Theorem 1.3, p.63: "Write `ρ ∈ {0, 1}` for its
output, with 0 declaring that the input is injective and 1 declaring that it is exactly `k`-to-one").

**Formalization Note.** The algorithm is the published `QCollLB.OneRoundAlg` run with
`QCollLB.parPhaseOracle x`. The final measurement is a computational-basis measurement of the whole
register `A = I^{⊗t} ⊗ C^{⊗t} ⊗ W` followed by an arbitrary input-independent output map
`out : basis state → Fin 2`; with an arbitrary `U_1` and workspace this is the same class as an
arbitrary two-outcome PVM `{Π_0, Π_1}`. The bit `0 : Fin 2` means "one-to-one", `1 : Fin 2` means
"`k`-to-one". -/
noncomputable def testProb {n q t w : ℕ} [NeZero q] (A : OneRoundAlg n q t w)
    (out : ((Fin t → Fin n) × (Fin t → ZMod q)) × Fin w → Fin 2) (ρ : Fin 2)
    (x : Fin n → ZMod q) : ℝ :=
  probEvent (A.finalState (parPhaseOracle x)) fun z => out z = ρ

end QCollLB.Supplement


