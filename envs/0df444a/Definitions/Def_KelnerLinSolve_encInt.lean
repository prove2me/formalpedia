-- Prove2me | Definitions.Def_KelnerLinSolve_encInt
-- name    : KelnerLinSolve_encInt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:54:46.261373+00:00
-- url     : https://prove2.me/theorems/f7b2faaa-d2ab-4836-994a-503df0673355
-- title:
--   Signed binary length $\mathrm{bits}(w)$, $\mathrm{len}(u)$, and the binary encodings of integers and rational vectors
-- statement:
--   For an integer $w$, the **signed binary length** is
--
--   $$
--   \mathrm{bits}(w) = 1 + \lceil \log_2(|w|+1) \rceil ,
--   $$
--
--   one sign bit followed by the binary digits of $|w|$. For a nonzero integer $u$, $\mathrm{len}(u) = \lfloor \log_2 |u| \rfloor + 1$ is the number of binary digits of $|u|$.
--
--   Machine words are over the alphabet $\{0,1,\#\}$. A natural number $k$ is written by its binary digits, most significant first, with no leading zeros (the empty word for $k=0$). An integer $w$ is written as a sign bit ($1$ for $w<0$) followed by the digits of $|w|$, so the word has exactly $\mathrm{bits}(w)$ symbols. A rational vector $z \in \mathbb Q^n$ is written as $a_1 \# d_1 \# \cdots \# a_n \# d_n$, where $z_i = a_i/d_i$ in lowest terms with $d_i \ge 1$.
--
--   These are the encodings of all inputs and outputs of the machines in this mission: the paper stores floating-point significands and exponents "in binary" and measures them by $\mathrm{bits}(\cdot)$.
--
--   **Formalization Note** $\mathrm{bits}(w)$ is `1 + Nat.size |w|`, since `Nat.size k` $=\lceil\log_2(k+1)\rceil$; $\mathrm{len}(u)$ is `Nat.size |u|`. Separators are `IntMul.joinSep`.
-- source:
--   Kelner, Solving Linear Systems in Õ(mn log(κ/ε)) Bit Operations, STOC 2027 submission (sha256 d1af55cb…), §1.1, p.3 (bits); §4.1, p.12 (len); Corollary 2.4, p.7 and Theorem 3.3, p.10 (reduced outputs)

import Mathlib
import Definitions.Def_IntMul_MultitapeWords

namespace KelnerLinSolve

/-- **Signed binary length** `bits(w) = 1 + ⌈log₂(|w| + 1)⌉` of an integer `w`.
Kelner, *Solving Linear Systems in Õ(mn log(κ/ε)) Bit Operations*, STOC 2027 submission
(sha256 d1af55cb…), §1.1, p.3.

**Formalization Note.** `Nat.size k` is the number of binary digits of `k`, which equals
`⌈log₂(k + 1)⌉` for every `k : ℕ` (and is `0` at `k = 0`), so `bitsInt w = 1 + Nat.size |w|` is the
page's formula exactly; `bitsInt 0 = 1`. -/
def bitsInt (w : ℤ) : ℕ := 1 + Nat.size w.natAbs

/-- `len(u) = ⌊log₂ |u|⌋ + 1`, the number of binary digits of a nonzero integer `u`
(Kelner, sha256 d1af55cb…, §4.1, p.12).

**Formalization Note.** Defined as `Nat.size |u|`, which equals `⌊log₂ |u|⌋ + 1` for `u ≠ 0`;
the page uses `len` only for nonzero `u` (the value `0` at `u = 0` is never used). -/
def lenInt (u : ℤ) : ℕ := Nat.size u.natAbs

/-- The binary word of a natural number `k` over `{0, 1, #}`: its `Nat.size k` binary digits, most
significant first, with no leading zeros (the empty word for `k = 0`). Encoding convention for the
inputs and outputs of the machines of this mission (Kelner, sha256 d1af55cb…, §1.1, p.3:
"stored in binary"). -/
def encNat (k : ℕ) : List (Option Bool) :=
  (List.range (Nat.size k)).reverse.map fun i => some (k.testBit i)

/-- The signed binary word of an integer `w`: one sign bit (`1` for `w < 0`) followed by
`encNat |w|`. Its length is exactly `bitsInt w` (Kelner, sha256 d1af55cb…, §1.1, p.3, "the signed
binary length of an integer"). -/
def encInt (w : ℤ) : List (Option Bool) :=
  some (decide (w < 0)) :: encNat w.natAbs

/-- The word `a₁ # d₁ # a₂ # d₂ # ⋯ # aₙ # dₙ` of a rational vector `z`, where `aᵢ / dᵢ` is `zᵢ`
in lowest terms with `dᵢ ≥ 1` (`aᵢ` signed, `dᵢ` unsigned). Output convention for the exact solvers
of Kelner (sha256 d1af55cb…), Corollary 2.4, p.7 and Theorem 3.3, p.10 ("each reduced output
numerator and denominator").

**Formalization Note.** A Lean `ℚ` is stored in lowest terms with a positive denominator, so
`(z i).num`, `(z i).den` are the reduced numerator and denominator. -/
def encRatVec {n : ℕ} (z : Fin n → ℚ) : List (Option Bool) :=
  IntMul.joinSep ((List.finRange n).flatMap fun i => [encInt (z i).num, encNat (z i).den])

end KelnerLinSolve


