-- Prove2me | Definitions.Def_QuantumKtSoI_pair
-- name    : QuantumKtSoI_pair
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:32:29.327878+00:00
-- url     : https://prove2.me/theorems/398da483-6d65-4608-8d59-8d3db9cd0d79
-- title:
--   Binary expansions, self-delimiting codes, the pairing $\langle x,y\rangle$ and the marker padding
-- statement:
--   String conventions of §2.1 and §5.2. For an integer $i\ge 0$, $\mathrm b(i)$ is its binary expansion, most significant bit first, with $\mathrm b(0)=0$; for a string $d$ write $\mathrm b(d)=\mathrm b(|d|)$. The **self-delimiting code** of $d$ is
--   $$\bar d = 1^{|\mathrm b(d)|}\,0\,\mathrm b(d)\,d ,$$
--   and for an integer $m\ge 0$, $\bar m$ is the code of $\mathrm b(m)$. The **pairing** of two strings is
--   $$\langle x,y\rangle=\begin{cases} xy & |x|=|y|,\\ \bar x y & |x|\ne|y|,\ |\bar xy| \text{ odd},\\ 0\bar x y & |x|\ne |y|,\ |\bar x y|\text{ even}.\end{cases}$$
--   For $\lambda>|v|$ the **marker padding** is $\mathrm{pad}_\lambda(v)=v\,1\,0^{\lambda-|v|-1}$, a string of length $\lambda$. The module also fixes $1^n$, the finite set of strings of length at most $n$, and the value of a binary numeral (most significant bit first).
--
--   These are the encodings with which descriptions, the inputs of the universal machine, and the padded pairs of the symmetry arguments are built.
--
--   **Formalization Note** Bits are Booleans (`true` is $1$). `pad` uses truncated subtraction; every statement that uses it assumes $\lambda>|v|$, as the paper does.
-- source:
--   Myrisiotis, Failure of Symmetry of Information for Quantum Computations, STOC 2027 submission (held version, sha256 6616571c…), §2.1, p.14; p.60 (pad)

import Mathlib

namespace QuantumKtSoI

/-- The binary expansion `b(i)` of a natural number, most significant bit first, with
`b(0) = 0` (Myrisiotis, *Failure of Symmetry of Information for Quantum Computations*, STOC 2027
submission, held version sha256 6616571c…, §2.1, p.14). `true` is the bit `1`. -/
def bin (i : ℕ) : List Bool :=
  if i = 0 then [false] else (Nat.bits i).reverse

/-- The self-delimiting code `d̄ = 1^{|b(d)|} 0 b(d) d` of a binary string `d`, where
`b(d) = b(|d|)` (§2.1, p.14). -/
def sd (d : List Bool) : List Bool :=
  List.replicate (bin d.length).length true ++ false :: (bin d.length ++ d)

/-- The code `m̄` of a natural number `m`, the self-delimiting code of its binary expansion
`b(m)` (§2.1, p.14: "For an integer m ≥ 0 we write m̄ for the code of b(m)"). -/
def sdNat (m : ℕ) : List Bool := sd (bin m)

/-- The pairing `⟨x, y⟩` of two binary strings (§2.1, p.14): `⟨x,y⟩ = xy` when `|x| = |y|`;
otherwise it is `x̄y` when `x̄y` has odd length and `0x̄y` when `x̄y` has even length, so that
the paired string then has odd length. -/
def pair (x y : List Bool) : List Bool :=
  if x.length = y.length then x ++ y
  else if (sd x ++ y).length % 2 = 1 then sd x ++ y
  else false :: (sd x ++ y)

/-- The marker padding `pad_λ(v) = v 1 0^{λ−|v|−1}` (p.60), a string of length `λ` when
`λ > |v|`.

**Formalization Note** Natural-number subtraction truncates; every statement that uses `pad`
assumes `λ > |v|`, exactly as the paper does. -/
def pad (lam : ℕ) (v : List Bool) : List Bool :=
  v ++ true :: List.replicate (lam - v.length - 1) false

/-- The unary string `1ⁿ`. -/
def ones (n : ℕ) : List Bool := List.replicate n true

/-- The finite set of binary strings of length at most `n`. -/
def stringsUpTo (n : ℕ) : Finset (List Bool) :=
  (Finset.range (n + 1)).biUnion fun k => Finset.univ.image fun f : Fin k → Bool => List.ofFn f

/-- The value of a binary string read as a numeral, most significant bit first (§2.1, p.14). -/
def binVal (w : List Bool) : ℕ :=
  w.foldl (fun a b => 2 * a + if b then 1 else 0) 0

end QuantumKtSoI


