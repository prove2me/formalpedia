-- Prove2me | Definitions.Def_QNoiseStab_phaseQuery
-- name    : QNoiseStab_phaseQuery
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:20:36.319707+00:00
-- url     : https://prove2.me/theorems/253754dd-e8f2-42a8-935b-b62d8c451ffb
-- title:
--   Phase oracle $O\,|i,p\rangle=\omega^{p x_i}|i,p\rangle$ on the query and phase registers
-- statement:
--   Let $n,d\ge1$, let $\omega\in\mathbb C$ and let $y\in\mathbb Z_d^{\,n}$ be an input. The **phase query** to $y$ acts on the query register $Q$ (indices $i\in[n]$) and the phase register $P$ (phases $p\in\mathbb Z_d$) as the diagonal operator
--
--   $$
--   O_y\,|i,p\rangle=\omega^{\,p\,y_i}\,|i,p\rangle .
--   $$
--
--   On the full algorithm state it acts as $O_y\otimes I_W$ on the workspace $W$, which gives the paper's oracle $O|i,p,w\rangle|x\rangle=\omega_d^{p x_i}|i,p,w\rangle|x\rangle$ once the input register is purified.
--
--   This is the only input-dependent operation of a query algorithm; every success-probability and Fourier-degree statement of the mission is about algorithms that use it.
--
--   **Formalization Note** The exponent is the residue of $p\,y_i$ in $\{0,\dots,d-1\}$; when $\omega^d=1$ (assumed by every theorem that uses the oracle) this is $\omega^{p y_i}$ for the integer representatives. Query indices are $0$-based.
-- source:
--   Beame–Holman–Kornerup, A Noise Operator Approach to Quantum Query Complexity and Time-Space Tradeoff Lower Bounds, arXiv:2609.40334 (version of 2026-11-02, sha256 814fe20e…), §2.1, p.6 (definition of the input oracle O)

import Mathlib

namespace QNoiseStab

/-- The phase query on the query and phase registers `(Q, P)` (Beame–Holman–Kornerup, *A Noise Operator Approach to Quantum Query Complexity and Time-Space Tradeoff Lower Bounds*, arXiv:2609.40334 (version of 2026-11-02, sha256 814fe20e…), §2.1, p.6: "We define input
oracle O that maps each basis state O |i, p, w⟩|x⟩ = ω_d^{p x_i} |i, p, w⟩|x⟩ … ω_d is some fixed
d'th root of unity"). For an input `y : Fin n → ZMod d` the oracle is the diagonal matrix with
entry `ω ^ (p * y i).val` at the basis state `|i, p⟩`; the identity on the workspace register is
added by `QAlgorithms.QueryAlg.stateAt`.

**Formalization Note** The query register `Q` is `Fin n` (index `i` is the paper's `i + 1`),
the phase register `P` is `ZMod d` (the paper's `p ∈ Z_m`, p.8), and the input symbol is
already encoded in `ZMod d`. The product `p * y i` is taken in `ZMod d` and read in
`{0, …, d − 1}`; when `ω ^ d = 1` (the hypothesis of every theorem using it) this equals
`ω ^ (p.val * (y i).val)`, the paper's `ω_d^{p x_i}`. -/
noncomputable def phaseQuery {n d : ℕ} (ω : ℂ) (y : Fin n → ZMod d) :
    Matrix (Fin n × ZMod d) (Fin n × ZMod d) ℂ :=
  Matrix.diagonal fun q => ω ^ (q.2 * y q.1).val

end QNoiseStab


