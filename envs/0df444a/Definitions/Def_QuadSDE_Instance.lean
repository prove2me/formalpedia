-- Prove2me | Definitions.Def_QuadSDE_Instance
-- name    : QuadSDE_Instance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:15:22.597543+00:00
-- url     : https://prove2.me/theorems/b37978f1-9329-41c3-9d88-ad0b26f22631
-- title:
--   Classical part of an APX-SDE instance and its binary encoding
-- statement:
--   An instance of APX-SDE in the oracle-based model has a classical part
--   $$x=(N,\,a_V,\,a_P,\,r,\,J,\,p,\,q,\,T,\,\varepsilon,\,\|Y\|^2,\,u_0)$$
--   with $r\ge1$, $J>0$, $0<p,q\le1$, $T\ge0$, $\varepsilon>0$, $\|Y\|^2>0$ and $u_0\in\mathcal O$; $a_V$ and $a_P$ are the ancilla sizes of the value and position oracles. The coefficient tensor $c$ and the vector $Y$ are not part of it: the algorithm accesses them only through the oracles. The instance is written as a bit string: the integers in self-delimiting binary, the real parameters as rationals (signed numerator, then denominator), then the observable (a tag and its indices).
--
--   The **expansion scale** of $x$ is the input length plus $\lceil e^{2\|Y\|^2/p}\rceil$, $\lceil T\rceil$, $\lceil J\rceil$, $r$, $\lceil1/\varepsilon\rceil$, $\lceil1/p\rceil$, $\lceil1/q\rceil$, $a_V$, $a_P$ and $N$. It is the budget of the classical constructor that writes out the quantum program; the program's own gate, query and qubit counts are bounded separately.
--
--   **Formalization Note** p. 13 supplies $N$, $r$, $J$, $p$, $q$, $T$, $\varepsilon$ explicitly in binary, and p. 15 supplies $\|Y\|$ classically. Here the real parameters are arbitrary rationals, which contain the dyadic (binary) numbers; the norm is supplied as $\|Y\|^2$, as the succinct model's prefix-sum circuit does (p. 16), which covers every rational $\|Y\|$. The encodings reuse `QAlgorithms.LocalHamiltonian.encBin` and `encRat`.
-- source:
--   Bravyi, Byrne, Zayats, Zhuk, Zlokapa, Quantum algorithms for stochastic nonlinear differential equations, arXiv:2606.08349 (sha256 29bd9b01…94cdf), §1 Problem 2, p. 2; §3, pp. 13–15

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalBinaryEncoding
import Definitions.Def_QAlgorithms_ClassicalRationalEncoding
import Definitions.Def_QuadSDE_Observable

open QAlgorithms.Complexity QAlgorithms.LocalHamiltonian

noncomputable section

namespace QuadSDE

/-- Bravyi–Byrne–Zayats–Zhuk–Zlokapa, arXiv:2606.08349 (sha256 29bd9b01…), Problem 2 (p. 2) in the
oracle-based input model of §3 (pp. 13–15): the classical part of an APX-SDE instance. It holds the
dimension `N`, the ancilla sizes `a_V, a_P` of the value and position oracles, the number of drift
channels `r ≥ 1`, the strength `J > 0`, the noise rates `0 < p, q ≤ 1`, the final time `T ≥ 0`,
the error tolerance `ε > 0`, the squared norm `‖Y‖² > 0` of the noise-free initial condition, and the
observable `u₀ ∈ 𝒪`. The coefficient tensor `c` and the vector `Y` are not part of it: the
algorithm sees them only through the oracles.

**Formalization Note.** p. 13: "The dimension `N`, drift parameters `s, r, J`, noise rates `p, q`,
final time `T`, and error tolerance `ε` are supplied explicitly in binary"; p. 15: `‖Y‖` is
"supplied classically". The real parameters are rational numbers (numerator and denominator in
binary); a number written in binary is the special case of a dyadic rational. The norm is supplied
as its square `‖Y‖²` (as the succinct model's `InitPrefix(N)` does, p. 16); every rational `‖Y‖`
is covered. `‖Y‖² > 0` encodes the paper's `Y ≠ 0` (p. 15); `J, r > 0` is p. 13's "We assume
`J, r, s > 0`". -/
structure Instance where
  N : ℕ
  aV : ℕ
  aP : ℕ
  r : ℕ
  J : ℚ
  p : ℚ
  q : ℚ
  T : ℚ
  ε : ℚ
  normYsq : ℚ
  obs : Observable N
  r_pos : 1 ≤ r
  J_pos : 0 < J
  p_pos : 0 < p
  p_le : p ≤ 1
  q_pos : 0 < q
  q_le : q ≤ 1
  T_nonneg : 0 ≤ T
  ε_pos : 0 < ε
  normYsq_pos : 0 < normYsq

/-- The binary encoding of an observable: a tag bit, then its indices in self-delimiting binary. -/
def encodeObservable {N : ℕ} : Observable N → Str
  | .lin i => [false] ++ encBin i.val
  | .quad i j => [true] ++ encBin i.val ++ encBin j.val

/-- The input string of an instance: `N, a_V, a_P, r` in self-delimiting binary, then
`J, p, q, T, ε, ‖Y‖²` as rationals (`encRat`: signed numerator, then denominator, in binary), then the
observable. -/
def encodeInstance (x : Instance) : Str :=
  encBin x.N ++ encBin x.aV ++ encBin x.aP ++ encBin x.r ++
    encRat x.J ++ encRat x.p ++ encRat x.q ++ encRat x.T ++ encRat x.ε ++ encRat x.normYsq ++
    encodeObservable x.obs

/-- The constructor's time and space budget parameter: the input length, plus
`⌈exp(2‖Y‖²/p)⌉`, `⌈T⌉`, `⌈J⌉`, `r`, `⌈1/ε⌉`, `⌈1/p⌉`, `⌈1/q⌉`, `a_V`, `a_P` and `N`.

**Formalization Note.** This bounds only the classical constructor that writes out the quantum
program (`QAlgorithms.OPI.UniformResourceFamily.bound` is evaluated at it). The program's own gate,
query and qubit counts are bounded separately in Theorem 2, without the input length and with the
factor `exp(2‖Y‖²/p)` entering linearly. The constructor must at least read its input and write a
program of that size. -/
def expansionScale (x : Instance) : ℕ :=
  (encodeInstance x).length + ⌈Real.exp (2 * (x.normYsq : ℝ) / x.p)⌉₊ + ⌈(x.T : ℝ)⌉₊ +
    ⌈(x.J : ℝ)⌉₊ + x.r + ⌈1 / (x.ε : ℝ)⌉₊ + ⌈1 / (x.p : ℝ)⌉₊ + ⌈1 / (x.q : ℝ)⌉₊ + x.aV + x.aP + x.N

end QuadSDE


