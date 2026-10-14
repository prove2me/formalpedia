-- Prove2me | Definitions.Def_QAlgorithms_Defs_AmplitudeEstimation
-- name    : QAlgorithms_Defs_AmplitudeEstimation
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-13T17:42:44.506892+00:00
-- url     : https://prove2.me/theorems/46160c78-9b07-487d-a3fc-866653c5e8a3
-- title:
--   Phase precision on the circle, iterative phase estimation, amplitude estimation,
-- statement:
--   Phase precision on the circle, iterative phase estimation, amplitude estimation,
--
--   ### QAlgorithms.circDist
--
--   For real numbers $x, y$, this is the real number
--   $$
--   \operatorname{circDist}(x,y) \;=\; \bigl|\,(x-y) - \operatorname{round}(x-y)\,\bigr|,
--   $$
--   where $\operatorname{round}(t) = \lfloor t + \tfrac12 \rfloor$ is the nearest integer to $t$, with halves rounded up. This is the distance from $x-y$ to the nearest integer, a value in $[0, \tfrac12]$. It is symmetric in $x$ and $y$ and unchanged by integer shifts of either argument.
--
--   ### QAlgorithms.ipeInitIndex
--
--   Inputs are a natural number $h$ and a real sequence $\omega = (\omega_0, \omega_1, \dots)$. The result is the natural number
--   $$
--   I(h,\omega) \;=\; \operatorname{round}(8\,\omega_h) \bmod 8 \;\in\; \{0,1,\dots,7\}.
--   $$
--   Here $\operatorname{round}(t) = \lfloor t+\tfrac12\rfloor$ is an integer, and $\bmod 8$ is the nonnegative remainder, so negative integers are also sent into $\{0,\dots,7\}$. The resulting integer is then read as a natural number.
--
--   Only the single entry $\omega_h$ of the sequence is used.
--
--   ### QAlgorithms.ipeLowPair
--
--   Inputs are a natural number $h$ and a real sequence $\omega$. Write $I = I(h,\omega) \in \{0,\dots,7\}$ for the index of the previous definition: $\operatorname{round}(8\omega_h) \bmod 8$. Write $\operatorname{bit}_k(I) \in \{0,1\}$ for the $k$-th binary digit of $I$, with $k=0$ the least significant.
--
--   The definition gives a sequence of pairs of bits $(a_d, b_d)$ for $d = 0, 1, 2, \dots$, by recursion on $d$.
--
--   - **Base case:**
--   $$(a_0, b_0) = \bigl(\operatorname{bit}_2(I),\ \operatorname{bit}_1(I)\bigr).$$
--   - **Step from $d$ to $d+1$:**
--   $$
--   a_{d+1} = \begin{cases} 0 & \text{if } \operatorname{circDist}\!\left(\tfrac{a_d}{4} + \tfrac{b_d}{8},\ \omega_{h-d-1}\right) < \tfrac14,\\[2pt] 1 & \text{otherwise,}\end{cases}
--   \qquad b_{d+1} = a_d .
--   $$
--
--   Here $\operatorname{circDist}(x,y)$ is the distance from $x-y$ to the nearest integer. The index $h-d-1$ is natural-number subtraction truncated at $0$. So for every $d \ge h-1$ the step compares against $\omega_0$.
--
--   ### QAlgorithms.ipeDigits
--
--   Inputs are a natural number $h$ and a real sequence $\omega$. The output is a bit $x_j \in \{\text{false},\text{true}\}$ for every natural number $j$.
--
--   Let $I = \operatorname{round}(8\omega_h) \bmod 8 \in \{0,\dots,7\}$, with $\operatorname{bit}_k$ its binary digits ($k=0$ least significant). Let $(a_d, b_d)_{d\ge 0}$ be the pair sequence of the previous definition. Then
--   $$
--   x_j = \begin{cases}
--   \operatorname{bit}_0(I) & \text{if } j = h+2,\\
--   \operatorname{bit}_1(I) & \text{if } j = h+1,\\
--   a_{h-j} & \text{if } 1 \le j \le h,\\
--   \text{false} & \text{otherwise, i.e. } j = 0 \text{ or } j > h+2 .
--   \end{cases}
--   $$
--
--   In particular, $x_h = a_0 = \operatorname{bit}_2(I)$ when $h \ge 1$.
--
--   When $h = 0$, the middle range is empty. Only $x_1 = \operatorname{bit}_1(I)$ and $x_2 = \operatorname{bit}_0(I)$ are then taken from $I$, and $\operatorname{bit}_2(I)$ does not appear among the outputs.
--
--   ### QAlgorithms.binFracFrom
--
--   Inputs are a bit sequence $p : \mathbb N \to \{\text{false},\text{true}\}$ and natural numbers $j$ and $\ell$ (the argument named `last`). The result is the real number
--   $$
--   \operatorname{binFrac}(p; j, \ell) = \sum_{i=j}^{\ell} [p_i]\, 2^{-(i-j+1)},
--   $$
--   where $[p_i]$ is $1$ if $p_i$ is true and $0$ otherwise. This is the binary fraction $0.p_j p_{j+1}\cdots p_\ell$.
--
--   When $\ell < j$ the sum is empty and the value is $0$.
--
--   ### QAlgorithms.ampGoodState
--
--   Inputs are a finite index set $\iota$, an arbitrary vector $\alpha \in \mathbb C^\iota$, and a finite subset $M \subseteq \iota$. The vector $\alpha$ is not assumed to have unit norm.
--
--   Let
--   $$
--   P = \sum_{j \in M} |\alpha_j|^2 .
--   $$
--   This is the "probability of measuring an outcome in $M$", computed as $\sum_{j\in M}|\langle j|\alpha\rangle|^2$. The definition returns the vector with coordinates
--   $$
--   \bigl(\text{good}(\alpha,M)\bigr)_j = \frac{1}{\sqrt{P}}\cdot\begin{cases}\alpha_j & j\in M,\\ 0 & j\notin M,\end{cases}
--   $$
--   that is, the restriction of $\alpha$ to $M$ rescaled by $P^{-1/2}$.
--
--   Degenerate case: if $P = 0$, the convention $0^{-1} = 0$ applies and the result is the zero vector. In that case the restriction is zero anyway.
--
--   ### QAlgorithms.ampBadState
--
--   Inputs are a finite index set $\iota$, an arbitrary vector $\alpha \in \mathbb C^\iota$ (not assumed to have unit norm), and a finite subset $M \subseteq \iota$. Let $P = \sum_{j\in M}|\alpha_j|^2$. The definition returns the vector with coordinates
--   $$
--   \bigl(\text{bad}(\alpha,M)\bigr)_j = \frac{1}{\sqrt{1-P}}\cdot\begin{cases}0 & j\in M,\\ \alpha_j & j\notin M,\end{cases}
--   $$
--   that is, the restriction of $\alpha$ to the complement of $M$, scaled by $(1-P)^{-1/2}$.
--
--   The normalizing factor uses $1-P$, not the actual mass $\sum_{j\notin M}|\alpha_j|^2$ outside $M$. These agree only when $\|\alpha\| = 1$.
--
--   Degenerate case: if $P \ge 1$, the real square root of the nonpositive number $1-P$ is $0$. Its inverse is then taken to be $0$, and the result is the zero vector.
--
--   ### QAlgorithms.aeState
--
--   Inputs are natural numbers $n$ and $m$, and arbitrary complex $2^n\times 2^n$ matrices $S$ and $R$ indexed by $n$-bit strings. Neither $S$ nor $R$ is assumed unitary. The output is a vector on the two-register space $\mathbb C^{\{0,1\}^m}\otimes\mathbb C^{\{0,1\}^n}$.
--
--   For an $m$-bit string $b$, write $\operatorname{val}(b) = \sum_i b_i 2^{m-1-i}$ for its integer value, with the first bit most significant.
--
--   **The iterate $G$.** Define
--   $$
--   G = S\, R_0\, S^\dagger\, R .
--   $$
--   Here $S^\dagger$ is the conjugate transpose of $S$, and $R_0$ is the diagonal matrix with entry $+1$ at the all-zero string $0^n$ and $-1$ at every other string.
--
--   **The state.** The output is
--   $$
--   \operatorname{aeState}_m(S,R) = (F_m^\dagger \otimes \mathbb 1)\; C_m(G)\; (F_m\otimes \mathbb 1)\;\bigl(|0^m\rangle \otimes S|0^n\rangle\bigr).
--   $$
--   The rightmost operator is applied first. The pieces are:
--
--   - $|0^m\rangle$ is the all-zero basis vector of the first register.
--   - $F_m$ is the $2^m\times 2^m$ Fourier matrix, with entries
--     $$(F_m)_{b,b'} = \frac{e^{2\pi i\,\operatorname{val}(b)\operatorname{val}(b')/2^m}}{\sqrt{2^m}},$$
--     and $F_m^\dagger$ is its conjugate transpose.
--   - $C_m(G)$ is the controlled-power operator. It is block diagonal, acting as
--     $$|b\rangle\otimes v \;\mapsto\; |b\rangle\otimes G^{\operatorname{val}(b)} v,$$
--     with $G^0 = \mathbb 1$.
--
--   ### QAlgorithms.aeAngle
--
--   Input is an $m$-bit string $b$, with integer value $\operatorname{val}(b) = \sum_i b_i 2^{m-1-i}$ (first bit most significant). The result is the real number
--   $$
--   \operatorname{aeAngle}(b) = \begin{cases}
--   \pi\left(1 - \dfrac{\operatorname{val}(b)}{2^m}\right) & \text{if } m\ge 1 \text{ and } \operatorname{val}(b) \ge 2^{m-1},\\[8pt]
--   \pi\,\dfrac{\operatorname{val}(b)}{2^m} & \text{otherwise.}
--   \end{cases}
--   $$
--
--   The value always lies in $[0, \pi/2]$.
--
--   When $m = 0$, the only string is empty, its value is $0$, and the angle is $0$.
--
--   ### QAlgorithms.aeVartheta
--
--   Inputs are a natural number $m$ and a real number $\theta$. The result is the vector in $\mathbb C^{\{0,1\}^m}$
--   $$
--   \operatorname{aeVartheta}_m(\theta) = F_m^\dagger\, v_\theta,
--   \qquad (v_\theta)_k = \frac{e^{2 i\theta\,\operatorname{val}(k)}}{\sqrt{2^m}} \quad (k\in\{0,1\}^m).
--   $$
--   The notation is:
--
--   - $\operatorname{val}(k)$ is the most-significant-first integer value of the bit string $k$.
--   - $F_m$ is the Fourier matrix with entries $(F_m)_{b,b'} = e^{2\pi i\operatorname{val}(b)\operatorname{val}(b')/2^m}/\sqrt{2^m}$, and $F_m^\dagger$ is its conjugate transpose.
--
--   The exponent in $v_\theta$ is $2i\theta\operatorname{val}(k)$, with no factor of $\pi$.
--
--   ### QAlgorithms.searchAlg1Enum
--
--   Inputs are:
--
--   - a natural number $n$;
--   - a function $f : \{0,1\}^n \to \{\text{false},\text{true}\}$ (the "marked" strings are those with $f(j) = \text{true}$);
--   - a natural number $c$;
--   - a pair $oc = (o, k)$, where $o$ is either a string or the symbol "none", and $k$ is a natural number.
--
--   The output is an extended nonnegative real in $[0,\infty]$, in fact always $0$ or $1$. Write $\operatorname{val}(j)$ for the most-significant-first integer value of $j$.
--
--   - **Some string is marked.** Let $j^*$ be the marked string with the smallest value $\operatorname{val}(j^*)$. It is unique because $\operatorname{val}$ is injective. The output is $1$ if $oc = (j^*,\ c + \operatorname{val}(j^*) + 1)$, and $0$ otherwise.
--   - **No string is marked.** The output is $1$ if $oc = (\text{none},\ c + 2^n)$, and $0$ otherwise.
--
--   So, as a function of $oc$, this is the indicator of a single point.
--
--   ### QAlgorithms.searchAlg1Rounds
--
--   Inputs are a natural number $n$, a function $f:\{0,1\}^n\to\{\text{false},\text{true}\}$, a finite list $(m_1, \dots, m_r)$ of natural numbers, a natural number $c$, and a pair $oc$ (an optional $n$-bit string together with a natural number). The output is a value in $[0,\infty]$, defined by recursion on the list.
--
--   **Empty list.** The value is the previous definition, $\operatorname{Enum}_f(c, oc)$. This is $1$ exactly when:
--
--   - some string is marked and $oc$ equals ($j^*$, $c+\operatorname{val}(j^*)+1$), where $j^*$ is the marked string of least value; or
--   - nothing is marked and $oc$ equals (none, $c+2^n$).
--
--   Otherwise it is $0$.
--
--   **Nonempty list $m :: \text{rest}$.** The value is
--   $$
--   \operatorname{Rounds}_f(m{::}\text{rest}, c, oc) = \sum_{j\in\{0,1\}^n} p_m(j)\cdot
--   \begin{cases}
--   [\,oc = (j,\ c+2^m)\,] & \text{if } f(j)=\text{true},\\
--   \operatorname{Rounds}_f(\text{rest},\ c+2^m,\ oc) & \text{if } f(j)=\text{false}.
--   \end{cases}
--   $$
--   The increment is written in the code as $(2^m-1)+1$, which equals $2^m$.
--
--   **The weight $p_m(j)$.** It is the second-register marginal
--   $$
--   p_m(j) = \sum_{b\in\{0,1\}^m} \bigl|\psi_{(b,j)}\bigr|^2,
--   \qquad \psi = \operatorname{aeState}_m\bigl(H^{\otimes n}, O_f\bigr).
--   $$
--   The ingredients are:
--
--   - $H^{\otimes n}$ has entries $(H^{\otimes n})_{j,i} = (-1)^{i\cdot j}\,2^{-n/2}$, where $i\cdot j$ is the parity of the bitwise AND of $i$ and $j$.
--   - $O_f$ is the diagonal phase oracle $|i\rangle\mapsto(-1)^{f(i)}|i\rangle$.
--   - $\psi$ is the result of applying, in order, $F_m\otimes\mathbb 1$, then the controlled power $|b\rangle\otimes v\mapsto|b\rangle\otimes G^{\operatorname{val}(b)}v$, then $F_m^\dagger\otimes\mathbb 1$, to the vector $|0^m\rangle\otimes H^{\otimes n}|0^n\rangle$.
--   - The iterate is
--     $$G = H^{\otimes n} R_0 (H^{\otimes n})^\dagger O_f,$$
--     where $R_0$ is the diagonal matrix that is $+1$ at $0^n$ and $-1$ elsewhere, and $F_m$ is the $2^m$-point Fourier matrix (MSB-first indexing).
--   - The real number $p_m(j)$ is used as an element of $[0,\infty]$; it is already nonnegative.
--
--   ### QAlgorithms.searchAlg1Weight
--
--   This definition fixes $n \in \mathbb{N}$ and a Boolean function $f : \{0,1\}^n \to \{\text{true},\text{false}\}$ on $n$-bit strings. It produces a weight function
--   $$w_f : \bigl(\{0,1\}^n \cup \{\bot\}\bigr) \times \mathbb{N} \to [0,\infty].$$
--   A pair $(o,c)$ consists of an optional string $o$ ($\bot$ meaning "none") and a natural number $c$.
--
--   **The schedule.** Let $L$ be the list
--   $$L = [1,1,2,2,3,3,\dots,n-1,n-1],$$
--   in which each of $1,\dots,n-1$ appears twice, in this order. When $n \le 1$, $L$ is empty, using truncated subtraction $n-1 = 0$. Then
--   $$w_f(o,c) = R_f(L, 0, (o,c)),$$
--   where the recursion $R_f(\ell, c_0, (o,c))$ is defined below. Throughout, $N(b) = \sum_i b_i\,2^{\,n-1-i}$ is the number whose most-significant-first binary expansion is $b$.
--
--   **Empty list.** $R_f([\,], c_0, (o,c))$ is defined by cases.
--
--   - If some $j$ has $f(j)=\text{true}$, let $j^\ast$ be the marked string with the smallest value $N(j^\ast)$. The weight is $1$ if $(o,c) = (j^\ast,\ c_0 + N(j^\ast) + 1)$, and $0$ otherwise.
--   - If no string is marked, the weight is $1$ if $(o,c) = (\bot,\ c_0 + 2^n)$, and $0$ otherwise.
--
--   **Non-empty list.** For a list with head $m$ and tail $\ell'$:
--   $$R_f(m :: \ell', c_0, (o,c)) = \sum_{j \in \{0,1\}^n} p_m(j)\cdot \begin{cases} [\,(o,c) = (j,\ c_0 + 2^m)\,] & f(j) = \text{true},\\ R_f(\ell',\ c_0 + 2^m,\ (o,c)) & f(j) = \text{false}.\end{cases}$$
--   Here $[\cdot]$ is $1$ or $0$. The count is literally written $(2^m-1)+1$, which equals $2^m$.
--
--   **The weight $p_m(j)$.** It is the real number
--   $$p_m(j) = \sum_{b \in \{0,1\}^m} \bigl|\Phi_m(b,j)\bigr|^2,$$
--   viewed as an element of $[0,\infty]$. It is the probability that the second register shows $j$ when both registers of $\Phi_m$ are measured in the computational basis. The state $\Phi_m$ lives on $m$ "phase" qubits tensored with $n$ "search" qubits:
--   $$\Phi_m = (F_m^\dagger \otimes I)\; C_m(G)\; (F_m \otimes I)\,\bigl(|0^m\rangle \otimes H^{\otimes n}|0^n\rangle\bigr).$$
--   Its ingredients are as follows.
--
--   - $H^{\otimes n}$ has entries $H^{\otimes n}_{j,i} = (-1)^{i\cdot j}\,2^{-n/2}$, where $i\cdot j$ is the parity of the bitwise AND.
--   - $G = H^{\otimes n}\, R_0\, (H^{\otimes n})^\dagger\, O_f$ is the Grover iterate.
--     - $R_0$ is diagonal with entry $+1$ at $0^n$ and $-1$ elsewhere.
--     - $O_f$ is diagonal with entry $-1$ where $f$ is true and $+1$ elsewhere.
--   - $F_m$ is the $2^m$-dimensional Fourier transform, with entries $e^{2\pi i N(y)N(z)/2^m}/\sqrt{2^m}$, indexed via $N$.
--   - $C_m(G)$ maps $|b\rangle|v\rangle \mapsto |b\rangle\, G^{N(b)}|v\rangle$.
--
--   ### QAlgorithms.searchAlg1ExpectedCost
--
--   This definition fixes $n \in \mathbb{N}$ and $f : \{0,1\}^n \to \{\text{true},\text{false}\}$. It defines the extended non-negative number
--   $$\mathrm{Cost}(f) = \sum_{(o,c)\,\in\, (\{0,1\}^n\cup\{\bot\})\times\mathbb{N}} c \cdot w_f(o,c) \;\in [0,\infty].$$
--   The sum is an unconditional sum over all pairs, possibly infinite. Here $w_f$ is the weight function of `searchAlg1Weight`:
--
--   - It applies the schedule $[1,1,2,2,\dots,n-1,n-1]$, adding $2^m$ to the counter per round with head $m$.
--   - In each round, a string $j$ is drawn with weight equal to the second-register marginal of the phase-estimation-of-Grover state.
--   - The process stops at a marked $j$. Otherwise it continues.
--   - After the schedule, a deterministic leaf adds $N(j^\ast)+1$ for the least marked $j^\ast$, or adds $2^n$ with output $\bot$ if nothing is marked.
--
--   The definition does not require the weights $w_f$ to sum to $1$.
-- source:
--   https://github.com/shiy1022/lean-quantum-complexity/blob/main/algorithms/QAlgorithms/Defs/AmplitudeEstimation.lean . Exact primary-source page locators are preserved in the declaration docstrings.

import Definitions.Def_QAlgorithms_Defs_Measurement
/-!
# Phase precision on the circle, iterative phase estimation, amplitude estimation,
search with an unknown number of marked items (shared definition layer)

G. Nannicini, *Quantum algorithms for optimizers* (arXiv:2408.07086v5), cited "Nannicini p.N"
(PDF pages), Chapters 3–4. Phases are measured in full turns (`φ ∈ [0, 1)` stands for
`e^{2πiφ}`), the QFT is the frozen `qftQubits` (sign `+`, normalization `1/√2^m`, Def. 3.1), and
the first qubit is the most significant bit.
-/

namespace QAlgorithms

open scoped ENNReal

/-- Nannicini p.62 (Thm. 3.9), p.64 and p.66 (§3.3): the distance on the circle `ℝ/ℤ` of two
phases measured in full turns, `|(x − y) − round(x − y)|`. For `x, y ∈ [0, 1)` this is the
source's `min{|x − y|, 1 − |x − y|}`. The distance of angles `a, b` modulo `2π` is
`2π · circDist (a / 2π) (b / 2π)`. -/
noncomputable def circDist (x y : ℝ) : ℝ :=
  |(x - y) - (round (x - y) : ℝ)|

/-- Nannicini p.66, §3.3.2 (initialization step of iterative phase estimation): the integer
`k ∈ {0, …, 7}` obtained by rounding the estimate `ω_h` (in full turns) to the closest multiple of
`1/8`, modulo `1`, written as `8 · (ω_h rounded)`. Ties round up (Mathlib's `round`). Its 3-bit
binary expansion (most significant first) is `p_h p_{h+1} p_{h+2}`. -/
noncomputable def ipeInitIndex (h : ℕ) (ω : ℕ → ℝ) : ℕ :=
  Int.toNat (round (8 * ω h) % 8)

/-- Nannicini p.66, §3.3.2: the pair of digits `(p_{h−d}, p_{h−d+1})` after `d` steps of iterative
phase estimation, for `d ≤ h − 1`. Step `d = 0` is the initialization (`p_h, p_{h+1}` from
`ipeInitIndex`). The iteration step for `j = h − d − 1` sets `p_j := 0` if
`|0.0 p_{j+1} p_{j+2} − ω_j| < 1/4` (distance on the circle) and `p_j := 1` otherwise (the source's
second test `|0.1 p_{j+1} p_{j+2} − ω_j| < 1/4` is taken as the else branch). -/
noncomputable def ipeLowPair (h : ℕ) (ω : ℕ → ℝ) : ℕ → Bool × Bool
  | 0 => ((ipeInitIndex h ω).testBit 2, (ipeInitIndex h ω).testBit 1)
  | d + 1 =>
      let a := (ipeLowPair h ω d).1
      let b := (ipeLowPair h ω d).2
      (if circDist ((if a then 1 else 0) * 4⁻¹ + (if b then 1 else 0) * 8⁻¹) (ω (h - d - 1)) < 4⁻¹
        then false else true, a)

/-- Nannicini p.66, §3.3.2: the digits `p_1, …, p_{h+2}` (`true` = digit 1) computed by iterative
phase estimation from the angle estimates `ω_j` of `2^{j−1} φ` in full turns (`ω_h` is used by the
initialization, `ω_j` for `j = h − 1, …, 1` by the iteration step). `p_h p_{h+1} p_{h+2}` is the
binary expansion of `ipeInitIndex h ω`; `p_j` for `1 ≤ j < h` comes from `ipeLowPair`. Indices
outside `1, …, h + 2` return `false`. Meaningful for `h ≥ 1` (statements assume it). -/
noncomputable def ipeDigits (h : ℕ) (ω : ℕ → ℝ) : ℕ → Bool := fun j =>
  if j = h + 2 then (ipeInitIndex h ω).testBit 0
  else if j = h + 1 then (ipeInitIndex h ω).testBit 1
  else if 1 ≤ j ∧ j ≤ h then (ipeLowPair h ω (h - j)).1
  else false

/-- Nannicini p.66, §3.3.2: the binary fraction `0.p_j p_{j+1} … p_last =
Σ_{i=j}^{last} p_i 2^{−(i−j+1)}` (used with `last = h + 2`). -/
noncomputable def binFracFrom (p : ℕ → Bool) (j last : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc j last, (if p i then 1 else 0) * ((2 : ℝ) ^ (i - j + 1))⁻¹

/-- Nannicini p.78, Thm. 4.6: the good component `|ψ_G⟩ = (1/√p) Σ_{j∈M} α_j |j⟩` of
`α = S|0⟩`, with `p = Σ_{j∈M} |α_j|²`. Junk value `0` when `p = 0`; Thm. 4.6's setting has
`0 < p < 1`, a hypothesis of the statement. -/
noncomputable def ampGoodState {ι : Type*} [Fintype ι] [DecidableEq ι] (α : EuclideanSpace ℂ ι)
    (M : Finset ι) : EuclideanSpace ℂ ι :=
  ((Real.sqrt (probEvent α fun j => j ∈ M))⁻¹ : ℂ) •
    WithLp.toLp 2 fun j => if j ∈ M then α j else 0

/-- Nannicini p.78, Thm. 4.6: the bad component `|ψ_B⟩ = (1/√(1 − p)) Σ_{j∉M} α_j |j⟩` of
`α = S|0⟩`, `p` as in `ampGoodState`. Junk value `0` when `p = 1`. -/
noncomputable def ampBadState {ι : Type*} [Fintype ι] [DecidableEq ι] (α : EuclideanSpace ℂ ι)
    (M : Finset ι) : EuclideanSpace ℂ ι :=
  ((Real.sqrt (1 - probEvent α fun j => j ∈ M))⁻¹ : ℂ) •
    WithLp.toLp 2 fun j => if j ∈ M then 0 else α j

/-- Nannicini pp.86–87, §4.3.3 and Fig. 4.9: the state before measurement of the amplitude
estimation circuit with `m` qubits of precision: `|0⟩_m|0⟩_n`, then `S` on the second register,
then phase estimation (frozen `phaseEstimationState`) of the Grover operator
`G = S F S† R` with `F = 2|0⟩⟨0| − I` (frozen `ampAmpIterate S R 0`). The controlled powers
`G^{2^{m−k}}` are controlled by qubit `k` (first qubit most significant), as in Fig. 4.9. -/
noncomputable def aeState {n : ℕ} (m : ℕ) (S R : Matrix (Qubits n) (Qubits n) ℂ) :
    EuclideanSpace ℂ (Qubits m × Qubits n) :=
  phaseEstimationState m (ampAmpIterate S R 0) (act S (zeroKet n))

/-- Nannicini p.86, §4.3.3 (last step of amplitude estimation): the angle returned from the
measured `m`-bit string `b`: with `0.b = bitsToNat b / 2^m`, it is `π(1 − 0.b)` if the first bit
`b_1` is `1` (i.e. `2^{m−1} ≤ bitsToNat b`) and `π · 0.b` otherwise. The amplitude estimate is
`sin²` of it. At `m = 0` it is `0`. -/
noncomputable def aeAngle {m : ℕ} (b : Qubits m) : ℝ :=
  if 1 ≤ m ∧ 2 ^ (m - 1) ≤ bitsToNat b then
    Real.pi * (1 - (bitsToNat b : ℝ) * ((2 : ℝ) ^ m)⁻¹)
  else Real.pi * ((bitsToNat b : ℝ) * ((2 : ℝ) ^ m)⁻¹)

/-- Nannicini p.92, Eq. (4.11) and the proof of Lem. 4.28: the first-register state
`|ϑ_+⟩ = Q_m† (2^{−m/2} Σ_k e^{2iθk} |k⟩)` produced by the amplitude estimation circuit on the
eigenstate with eigenvalue `e^{2iθ}`; `|ϑ_−⟩` is `aeVartheta m (−θ)`. -/
noncomputable def aeVartheta (m : ℕ) (θ : ℝ) : EuclideanSpace ℂ (Qubits m) :=
  act (star (qftQubits m)) (WithLp.toLp 2 fun k =>
    Complex.exp (2 * Complex.I * (θ : ℂ) * (bitsToNat k : ℂ)) * ((Real.sqrt ((2 : ℝ) ^ m))⁻¹ : ℂ))

/-- Nannicini p.94, Alg. 1, lines 13–18 (the enumeration fallback): the strings of `{0,1}^n` are
tested in increasing `bitsToNat` order, one application of `U_f` each, starting from cost `c`.
If a marked string exists, the first one `j` is returned at cost `c + bitsToNat j + 1`; otherwise
"no solution" (`none`) at cost `c + 2^n`. A point mass on `(output, cost)`. -/
noncomputable def searchAlg1Enum {n : ℕ} (f : Qubits n → Bool) (c : ℕ)
    (oc : Option (Qubits n) × ℕ) : ℝ≥0∞ :=
  open Classical in
  if ∃ j, f j = true then
    (if ∃ j, f j = true ∧ (∀ j', f j' = true → bitsToNat j ≤ bitsToNat j') ∧
        oc = (some j, c + bitsToNat j + 1) then 1 else 0)
  else (if oc = (none, c + 2 ^ n) then 1 else 0)

/-- Nannicini p.94, Alg. 1, lines 3–12: the weight of ending with `oc = (output, cost)` when the
remaining rounds use the precisions listed in `rounds`, starting from cost `c`. In a round with
precision `m`, the string `j` is read on the second register of the amplitude estimation circuit
(`aeState m H^{⊗n} R`, `R|j⟩ = (−1)^{f(j)}|j⟩` the frozen `phaseOracle f`) with its marginal
probability (Postulate 3); the round costs `(2^m − 1) + 1` applications of `U_f` (the `2^m − 1`
Grover iterates of phase estimation, one `U_f` each, plus the evaluation of `f(j)`); the run
stops with output `j` if `f(j) = 1`, else goes on. After the last round, `searchAlg1Enum`. -/
noncomputable def searchAlg1Rounds {n : ℕ} (f : Qubits n → Bool) :
    List ℕ → ℕ → Option (Qubits n) × ℕ → ℝ≥0∞
  | [], c, oc => searchAlg1Enum f c oc
  | m :: rest, c, oc =>
      ∑ j : Qubits n,
        ENNReal.ofReal (∑ b : Qubits m, prob (aeState m (hadamardN n) (phaseOracle f)) (b, j)) *
          (if f j = true then (if oc = (some j, c + ((2 ^ m - 1) + 1)) then 1 else 0)
          else searchAlg1Rounds f rest (c + ((2 ^ m - 1) + 1)) oc)

/-- Nannicini p.94, Alg. 1: the probability that the quantum search algorithm without knowledge of
the number of marked items ends with output `oc.1` (`none` = "no solution") after `oc.2`
applications of `U_f`. The rounds are `(m, i)` for `m = 1, …, n − 1` and `i = 1, 2`, in this order,
then the enumeration. A weight function (its total mass is `1`, a fact, not an obligation of the
definition). "Alg. 1 returns `o`" is stated as: every `oc` of nonzero weight has `oc.1 = o`. -/
noncomputable def searchAlg1Weight {n : ℕ} (f : Qubits n → Bool) :
    Option (Qubits n) × ℕ → ℝ≥0∞ :=
  searchAlg1Rounds f ((List.range (n - 1)).flatMap fun i => [i + 1, i + 1]) 0

/-- Nannicini p.94, Thm. 4.29: the expected number of applications of `U_f` made by Alg. 1. -/
noncomputable def searchAlg1ExpectedCost {n : ℕ} (f : Qubits n → Bool) : ℝ≥0∞ :=
  ∑' oc : Option (Qubits n) × ℕ, (oc.2 : ℝ≥0∞) * searchAlg1Weight f oc

/-! ### Sanity tests -/

example (x : ℝ) : circDist x (x + 1) = 0 := by
  rw [circDist, show x - (x + 1) = ((-1 : ℤ) : ℝ) by push_cast; ring, round_intCast]
  simp

example : circDist (9 / 10) (1 / 10) = 1 / 5 := by
  have h : round ((9 / 10 : ℝ) - 1 / 10) = 1 := by
    rw [round_eq, Int.floor_eq_iff]; norm_num
  rw [circDist, h]
  norm_num [abs_of_neg]

example (h : ℕ) (ω : ℕ → ℝ) : ipeDigits h ω 0 = false := by
  simp [ipeDigits]

/-- `h = 1`, `ω_1 = 5/8`: the three digits are `101`, most significant first (`0.101 = 5/8`). -/
example : ipeDigits 1 (fun _ => 5 / 8) 1 = true ∧ ipeDigits 1 (fun _ => 5 / 8) 2 = false ∧
    ipeDigits 1 (fun _ => 5 / 8) 3 = true := by
  have hk : ipeInitIndex 1 (fun _ => 5 / 8) = 5 := by
    rw [ipeInitIndex, show (8 : ℝ) * (5 / 8) = ((5 : ℤ) : ℝ) by norm_num, round_intCast]
    rfl
  refine ⟨?_, ?_, ?_⟩ <;> simp [ipeDigits, ipeLowPair, hk] <;> decide

example (p : ℕ → Bool) (j : ℕ) : binFracFrom p j j = if p j then 2⁻¹ else 0 := by
  simp [binFracFrom]

example {ι : Type*} [Fintype ι] [DecidableEq ι] (α : EuclideanSpace ℂ ι) :
    ampGoodState α ∅ = 0 := by
  ext j; simp [ampGoodState]

example {ι : Type*} [Fintype ι] [DecidableEq ι] (α : EuclideanSpace ℂ ι) :
    ampBadState α ∅ = α := by
  ext j; simp [ampBadState, probEvent]

example : aeAngle (![true] : Qubits 1) = Real.pi / 2 := by
  simp [aeAngle, bitsToNat]
  ring

example {n : ℕ} (c : ℕ) :
    searchAlg1Enum (fun _ : Qubits n => false) c (none, c + 2 ^ n) = 1 := by
  simp [searchAlg1Enum]

example {n : ℕ} (f : Qubits n → Bool) (c : ℕ) : searchAlg1Rounds f [] c = searchAlg1Enum f c := by
  funext oc; rfl

end QAlgorithms


