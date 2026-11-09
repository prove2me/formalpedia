-- Prove2me | Definitions.Def_DepthOneQExp_maxEnt
-- name    : DepthOneQExp_maxEnt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:44:24.53268+00:00
-- url     : https://prove2.me/theorems/30eec0c9-ab70-4150-ad26-8c5a34d5c6e9
-- title:
--   Maximally entangled vector $|a_1\rangle = \sum_i |i\rangle|i\rangle$
-- statement:
--   On two copies of an $n$-qubit register, with $N=2^n$,
--   $$
--   |a_1\rangle = \sum_{i\in[N]} |i\rangle|i\rangle \qquad\text{(Eq. (2.40))},
--   $$
--   the unnormalized maximally entangled vector: the amplitude of $|x\rangle|y\rangle$ is $1$ if $x=y$ and $0$ otherwise. Its squared norm is $N$, and the Haar average satisfies $\mathbb E_{U\sim\mu(U(2^n))}U\otimes\overline U = |a_1\rangle\langle a_1|/N$ (Eq. (2.41)).
-- source:
--   Anshu–Balasubramanian–Haferkamp–Harrow–Tan, Depth-1 expanders on the unitary group and applications, arXiv:2609.01605 (held version, sha256 3c3f8513…aebfd87), Eq. (2.40), p.13

import Mathlib
import Definitions.Def_MITMSynthesis_Gate

namespace DepthOneQExp

/-- The unnormalized maximally entangled vector `|a_1⟩ = Σ_{i ∈ [N]} |i⟩|i⟩` on two copies of an
`n`-qubit register, `N = 2ⁿ` (Anshu–Balasubramanian–Haferkamp–Harrow–Tan, *Depth-1 expanders on the
unitary group and applications*, arXiv:2609.01605, held version sha256 3c3f8513…aebfd87, Eq. (2.40),
p.13): the amplitude of `|x⟩|y⟩` is `1` if `x = y` and `0` otherwise. Its squared norm is `N`, and
`E_{U∼Haar} U ⊗ Ū = |a_1⟩⟨a_1| / N` (Eq. (2.41)). -/
def maxEnt (n : ℕ) : MITMSynthesis.Q n × MITMSynthesis.Q n → ℂ :=
  fun p => if p.1 = p.2 then 1 else 0

end DepthOneQExp


