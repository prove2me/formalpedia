-- Prove2me | Definitions.Def_KadatchJenkinsCrc
-- name    : KadatchJenkinsCrc
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-21T21:57:23.089117+00:00
-- url     : https://prove2.me/theorems/ec96c870-1fa9-4a06-8354-1e8eb55bc49e
-- title:
--   CRC as polynomial arithmetic over GF(2) (Kadatch–Jenkins 2010)
-- statement:
--   The objects of Kadatch–Jenkins' paper. All polynomials have coefficients in $\mathrm{GF}(2)$ (`ZMod 2`), and $a \bmod P$ is the remainder of polynomial division (`%`).
--
--   **Messages (§1, p. 2).** “A message $M = m_0 \dots m_{N-1}$ comprised of $N = |M|$ bits ($m_k \in \{0, 1\}$) may be viewed […] as a polynomial of a single variable of degree $(N - 1)$ $$M(x) = \sum_{k=0}^{N-1}m_kx^{N-1-k}$$ where $m_k \in GF(2) = \{0, 1\}$ and all arithmetic operations on coefficients are performed modulo 2.”
--   - `Message` is a list of bits; `Message.poly` gives $M(x)$, and the list length is $|M|$. Leading zero bits are allowed, so $M(x)$ has degree at most $N - 1$ (exactly $N - 1$ only when $m_0 = 1$), and $|M|$ is carried by the message, not read off $M(x)$.
--   - Concatenation of messages is list concatenation; its polynomial is $M_1(x)x^{|M_2|} + M_2(x)$, the paper's usage (§3.1, p. 4).
--   - `Message.ofPoly n p` is the $n$-bit message whose bits are the coefficients of $x^{n-1}, \dots, x^0$ of $p$: a $D$-bit value such as a CRC stored after a message (§3.5, p. 6).
--
--   **The CRC (eq. (1), pp. 2–3).** “In practice, a more complex formula is used: $$\mathrm{CRC}_u\big(M(x), v(x)\big) = \Big(\big(v(x) - u(x)\big) \cdot x^{|M|} + M(x) \cdot x^D + u(x)\Big) \bmod P(x), \qquad (1)$$ where polynomial $P(x)$ of degree $D$ and polynomial $u(x)$ of degree less than $D$ are fixed.” This is `crc P u M v`, with $D$ the degree of $P$ (`Polynomial.natDegree`). The definition takes any $P$ and $u$; the statements assume $\deg P \ge 1$ and $\deg u < D$.
--   - The sentence just before (1) on p. 2, “For a given polynomial $P(x)$ of degree $D = \deg\big(P(x)\big)$, $\mathrm{CRC}_u\big(M(x), v(x)\big)$ is the reminder from division of $\big(M(x) \cdot x^D\big)$ by $P(x)$”, is the plain CRC with $u = v = 0$; the paper then says it uses the "more complex formula" (1), which is what is defined.
--   - “Typically, $$u(x) = \sum_{k=0}^{D-1}x^k. \qquad (2)$$” This is `stdU D`.
--
--   **The simplified CRC (eq. (7), p. 9).** “It is sufficient to be able to compute $$\mathrm{CRC}_0\big(M(x), v(x)\big) = \Big(v(x) \cdot x^{|M|} + M(x) \cdot x^D\Big) \bmod P(x), \qquad (7)$$”. This is `crc0 P M v`.
--
--   **Powers of $x$ (eq. (6), p. 8).** $x^N$ “may be computed using no more than $(\lfloor\log_2(N)\rfloor + 1)$ multiplications of polynomials of degree less than $D$ provided known values of $$Pow2k(k) = x^{2^k} \bmod P(x). \qquad (6)$$” This is `pow2k P k`.
--
--   **MulByXpowD (eq. (10), p. 10).** “where $$\mathrm{MulByXpowD}\big(a(x)\big) = \big(a(x) \cdot x^D\big) \bmod P(x). \qquad (10)$$” This is `mulByXpowD P a`.
--
--   **CrcWordN (§4.11.3, p. 19).** “Given $v(x)$, $\deg\big(v(x)\big) < D$ and $m(x)$, $\deg\big(m(x)\big) < W$, $\mathrm{CrcWordN}\big(m(x), v(x)\big) = \Big(v(x) \cdot x^W + m(x) \cdot x^D\Big) \cdot x^{(N-1)W} \bmod P(x)$ may be implemented efficiently utilizing the techniques described in sections 4.6, 4.8, and 4.9.” This is `crcWordN P W N m v`, for a word width $W$ and $N$ stripes. It is defined for all $v$ and $m$; the statements that need the degree bounds assume them. For $N = 0$ the exponent $(N - 1)W$ is $0$ (natural-number subtraction); the paper has $N \ge 1$.
--
--   **The stripe CRCs (§4.11, pp. 16–18).** The message is $K$ groups of $N$ $W$-bit words $m_{k,n}$ (p. 16), given as a function `m k n`. The stripe values: “Once $v_{K,n}(x) = \mathrm{CRC}_0\big(M_n'(x), v_{0,n}(x)\big)$ are computed starting with $$v_{0,0} = v(x), \qquad v_{0,n} = 0, n \ge 1,$$” (p. 18) and follow (16)–(17): $v_{k+1,n}(x) = \dots = \mathrm{CrcWordN}\big(m_{k,n}(x), v_{k,n}(x)\big)$. `stripeCrc P W N m v k n` is $v_{k,n}$, defined by exactly this recurrence; that it equals $\mathrm{CRC}_0(M_n', v_{0,n})$ is a milestone, not part of the definition. It is defined for every $n$; only $n < N$ is used.
--
--   **Bytes and registers (§4.1, p. 7).** “For little-endian machines (assumed from now on), the result of loading of a $D$-bit word from memory into hardware register matches the expectations: the 0-th bit of the 0-th byte becomes the 0-th (least significant) bit of the word corresponding to $x^{(D-1)}$.”
--   - `Message.ofBytes bs` is the message of a byte string: bit $i$ of byte $j$ (bit $0$ least significant) is message bit $m_{8j+i}$.
--   - `regPoly r` is the polynomial held by a $D$-bit register $r$: bit $i$ is the coefficient of $x^{D-1-i}$. A $D$-bit word loaded from bytes $b_0, \dots$ thus holds `regPoly` = the polynomial of their message.
--   - The paper's example, “the 32-bit sequence of 4 bytes 0x01, 0x02, 0x03, 0x04 (0x04030201 when loaded into a 32-bit hardware register) corresponds to the polynomial $\big(x^{31} + x^{22} + x^{15} + x^{14} + x^5\big)$”, holds for both: the message of these four bytes and the register $\mathtt{0x04030201}$ both give that polynomial.
-- source:
--   Kadatch, A. and Jenkins, B., Everything we know about CRC but afraid to forget, September 3, 2010 (self-published white paper, distributed as doc/crc-doc.1.0.pdf with zlib 1.2.12 and later, and with Google's crcutil library; no DOI), pp. 2–19, messages and their polynomials (§1, p. 2), CRC_u (eq. (1), p. 3), the usual u(x) (eq. (2), p. 3), the little-endian bit mapping (§4.1, p. 7), Pow2k (eq. (6), p. 8), CRC₀ (eq. (7), p. 9), MulByXpowD (eq. (10), p. 10), the stripe CRCs v_{k,n} (eqs. (16)–(17), pp. 17–18) and CrcWordN (§4.11.3, p. 19)

import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Field.ZMod

/-!
# CRC as polynomial arithmetic over GF(2)

Definitions from A. Kadatch and B. Jenkins, *Everything we know about CRC but afraid to forget*
(2010): messages as bit strings and polynomials (§1), the CRC with pre- and post-conditioning
(eq. (1)), the usual conditioning polynomial (eq. (2)), `Pow2k` (eq. (6)), the simplified CRC
(eq. (7)), `MulByXpowD` (eq. (10)), the interleaved word step `CrcWordN` and the stripe CRCs
`v_{k,n}` (§4.11), and the little-endian mapping of bytes and registers to polynomials (§4.1).
-/

open Polynomial

namespace KadatchJenkins

/-- A message `M = m₀ … m_{N-1}`: a finite string of bits in `GF(2)` (§1). Its length is `|M|`. -/
abbrev Message := List (ZMod 2)

/-- The polynomial of a message, `M(x) = ∑_{k=0}^{N-1} m_k x^{N-1-k}` (§1). -/
noncomputable def Message.poly (M : Message) : (ZMod 2)[X] :=
  ∑ k : Fin M.length, C (M.get k) * X ^ (M.length - 1 - (k : ℕ))

/-- `CRC_u(M(x), v(x)) = ((v(x) - u(x)) · x^{|M|} + M(x) · x^D + u(x)) mod P(x)`, eq. (1),
where `D = deg P`. -/
noncomputable def crc (P u : (ZMod 2)[X]) (M : Message) (v : (ZMod 2)[X]) : (ZMod 2)[X] :=
  ((v - u) * X ^ M.length + M.poly * X ^ P.natDegree + u) % P

/-- The usual conditioning polynomial `u(x) = ∑_{k=0}^{D-1} x^k`, eq. (2). -/
noncomputable def stdU (D : ℕ) : (ZMod 2)[X] :=
  ∑ k ∈ Finset.range D, X ^ k

/-- The simplified CRC `CRC₀(M(x), v(x)) = (v(x) · x^{|M|} + M(x) · x^D) mod P(x)`, eq. (7). -/
noncomputable def crc0 (P : (ZMod 2)[X]) (M : Message) (v : (ZMod 2)[X]) : (ZMod 2)[X] :=
  (v * X ^ M.length + M.poly * X ^ P.natDegree) % P

/-- `CrcWordN(m(x), v(x)) = (v(x) · x^W + m(x) · x^D) · x^{(N-1)W} mod P(x)` (§4.11.3). -/
noncomputable def crcWordN (P : (ZMod 2)[X]) (W N : ℕ) (m v : (ZMod 2)[X]) : (ZMod 2)[X] :=
  ((v * X ^ W + m * X ^ P.natDegree) * X ^ ((N - 1) * W)) % P

/-- The `n`-bit message of a polynomial `p` of degree less than `n`, as when a `D`-bit CRC value is
stored after a message (§3.5): bit `m_k` is the coefficient of `x^{n-1-k}`. -/
noncomputable def Message.ofPoly (n : ℕ) (p : (ZMod 2)[X]) : Message :=
  List.ofFn fun k : Fin n => p.coeff (n - 1 - (k : ℕ))

/-- `MulByXpowD(a(x)) = (a(x) · x^D) mod P(x)`, eq. (10). -/
noncomputable def mulByXpowD (P a : (ZMod 2)[X]) : (ZMod 2)[X] :=
  (a * X ^ P.natDegree) % P

/-- `Pow2k(k) = x^{2^k} mod P(x)`, eq. (6). -/
noncomputable def pow2k (P : (ZMod 2)[X]) (k : ℕ) : (ZMod 2)[X] :=
  X ^ (2 ^ k) % P

/-- The stripe CRCs `v_{k,n}` of the interleaved computation (§4.11, eqs. (16)–(17)), for a
message whose `k`-th group consists of the `W`-bit words `m k 0, …, m k (N-1)`: starting from
`v_{0,0} = v(x)` and `v_{0,n} = 0` for `n ≥ 1` (§4.11.2),
`v_{k+1,n} = CrcWordN(m_{k,n}(x), v_{k,n}(x))`. -/
noncomputable def stripeCrc (P : (ZMod 2)[X]) (W N : ℕ) (m : ℕ → ℕ → Message) (v : (ZMod 2)[X]) :
    ℕ → ℕ → (ZMod 2)[X]
  | 0, n => if n = 0 then v else 0
  | k + 1, n => crcWordN P W N (m k n).poly (stripeCrc P W N m v k n)

/-- The message of a byte string on a little-endian machine (§4.1): bit `i` of byte `j` is
message bit `m_{8j+i}`. -/
def Message.ofBytes (bs : List (BitVec 8)) : Message :=
  bs.flatMap fun b => List.ofFn fun i : Fin 8 => if b.getLsbD i then 1 else 0

/-- The polynomial held by a `D`-bit register in `D`-normalized form (§4.1): bit `i` (bit `0`
least significant) is the coefficient of `x^{D-1-i}`. -/
noncomputable def regPoly {D : ℕ} (r : BitVec D) : (ZMod 2)[X] :=
  ∑ i : Fin D, if r.getLsbD i then X ^ (D - 1 - (i : ℕ)) else 0

end KadatchJenkins


