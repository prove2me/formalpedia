-- Prove2me | Definitions.Def_PPADSIS_SubexpSIS_SISPuzzle
-- name    : PPADSIS_SubexpSIS_SISPuzzle
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T14:49:19.920538+00:00
-- url     : https://prove2.me/theorems/e71a4469-2e89-4a18-b111-4ac328f12532
-- title:
--   The SIS puzzle (F_sis, D_sis) of §7.3: n̂, m̂ = n̂ log q̂ + 1, q̂ = 2^{2⌈n̂^e⌉}, ternary addresses
-- statement:
--   Fix a real constant $e$. For a dimension $\hat n$ put
--   $$\hat q:=2^{2\lceil\hat n^e\rceil},\qquad \hat m:=\hat n\log\hat q+1 ,$$
--   and let $\hat n(\lambda)$ be the largest positive integer with $2\hat m\le\lambda$, or $\hat n:=1$ for the finitely many $\lambda$ for which no such integer exists. An address $a\in\{0,1\}^p$ **encodes** a vector $\mathbf u\in\{-1,0,1\}^{\hat m}$ if its first $\min(p,2\hat m)$ bits, padded with zeros to length $2\hat m$, encode the entries of $\mathbf u$ by $01,00,10$ for $-1,0,1$, and its remaining bits are zero. With $p:=\lfloor\log t\rfloor$:
--
--   - $D_{\mathrm{sis}}(t,1^\lambda)$ samples a uniform matrix $\hat{\mathbf A}\leftarrow\mathbb Z_{\hat q}^{\hat n\times\hat m}$ (at $\hat n=\hat n(\lambda)$) and outputs it;
--   - $F_{\mathrm{sis}}(t,\hat{\mathbf A})$ is the output of the exhaustive search $C_\varphi$ of Lemma 3.9 for the predicate $\varphi:\{0,1\}^p\to\{0,1\}$ that accepts $a$ if it encodes a vector $\mathbf u\ne0$ with $\hat{\mathbf A}\mathbf u=0\bmod\hat q$: it is $(1,a)$ for the first such $a$, or $(0,0^p)$ if no such address exists.
--
--   This is the hard computation of the SIS-only route: a smaller SIS instance, just small enough to be solved by exhaustive search over at most $2^\lambda$ addresses.
--
--   **Formalization Note** $\log$ is base 2 ($\log\hat q=2\lceil\hat n^e\rceil$ exactly). The matrix is output with the SIS code (`encMat`: dimensions, modulus, fixed-width entries); $F_{\mathrm{sis}}$ reads $\hat n,\hat m,\hat q$ from it, and on a string that is not a matrix code $\varphi$ accepts nothing, so $F_{\mathrm{sis}}=(0,0^p)$. $D_{\mathrm{sis}}$ is implemented with $(|\mathrm{input}|+2)^3$ coins, taking the entries from consecutive blocks of $\log\hat q$ coins; since $\hat q$ is a power of two and $\hat n\hat m\log\hat q\le(\lambda+2)^3$, its output is exactly uniform at every input.
-- source:
--   Choudhuri, PPAD Hardness from SIS, STOC 2027 submission (manuscript sha256 17abad73…), p. 58, §7.3 ('Formally, let n̂ be the largest positive integer ...')

import Mathlib
import Definitions.Def_PPADSIS_SubexpSIS_SIS
import Definitions.Def_PPADSIS_SubexpSIS_TreePuzzle

set_option autoImplicit false

namespace PPADSIS.SubexpSIS

open Polynomial

/-- The puzzle modulus `q̂ := 2^{2⌈n̂^e⌉}` at dimension `n̂` (Choudhuri, *PPAD Hardness from SIS*,
STOC 2027 submission (manuscript sha256 17abad73…), §7.3, p. 58). -/
noncomputable def qHat (e : ℝ) (n : ℕ) : ℕ := 2 ^ (2 * ⌈(n : ℝ) ^ e⌉₊)

/-- The puzzle width `m̂ := n̂ log q̂ + 1` at dimension `n̂` (p. 58; `log` is base 2, and
`log q̂ = 2⌈n̂^e⌉` exactly). -/
noncomputable def mHat (e : ℝ) (n : ℕ) : ℕ := n * Nat.log 2 (qHat e n) + 1

open Classical in
/-- The puzzle dimension `n̂(λ)` (p. 58): the largest positive integer `n̂` with `2m̂ ≤ λ`, and
`n̂ := 1` for the finitely many `λ` for which no such integer exists. (An admissible `n̂` is below
`λ`, since `m̂ > n̂`.) -/
noncomputable def nHat (e : ℝ) (lam : ℕ) : ℕ :=
  if ∃ n, 0 < n ∧ 2 * mHat e n ≤ lam then
    Nat.findGreatest (fun n => 0 < n ∧ 2 * mHat e n ≤ lam) lam
  else 1

/-- The two-bit code of an entry `−1, 0, 1` in an address: `01`, `00`, `10`. -/
def encTrit (z : ℤ) : List Bool :=
  if z = -1 then [false, true] else if z = 1 then [true, false] else [false, false]

/-- An address `a ∈ {0,1}^p` **encodes** `u ∈ {−1,0,1}^m` (p. 58): its first `min(p, 2m)` bits,
padded with zeros to length `2m`, encode the entries of `u` by `01, 00, 10` for `−1, 0, 1`, and its
remaining bits are zero. -/
def AddrEncodes (m : ℕ) (a : List Bool) (u : Fin m → ℤ) : Prop :=
  (∀ j, u j = -1 ∨ u j = 0 ∨ u j = 1) ∧
  a.take (2 * m) ++ List.replicate (2 * m - min a.length (2 * m)) false =
    (List.ofFn u).flatMap encTrit ∧
  ∀ b ∈ a.drop (2 * m), b = false

/-- The witness predicate `φ` of the SIS puzzle on the input string `x` (p. 58): `φ(a)` holds iff
`x` is the code of a matrix `Â ∈ ℤ_q̂^{n̂×m̂}` and `a` encodes a vector `u ≠ 0` with `Âu = 0 mod q̂`.
On a string that is not a matrix code, `φ` accepts nothing. -/
def sisWitness (x : List Bool) (a : List Bool) : Prop :=
  ∃ (n m q : ℕ) (A : Fin n → Fin m → Fin q), x = encMat A ∧
    ∃ u : Fin m → ℤ, AddrEncodes m a u ∧ u ≠ 0 ∧ ∀ i, (q : ℤ) ∣ ∑ j, ((A i j).val : ℤ) * u j

/-- `F_sis(t, Â)` (p. 58): with `p := ⌊log t⌋`, the output of the exhaustive search `C_φ` of
Lemma 3.9 for the predicate `φ` above, i.e. `(1, a)` for the lexicographically first address `a`
with `φ(a)`, or `(0, 0^p)` if no such address exists (`searchOutput`). -/
noncomputable def Fsis (t : ℕ) (x : List Bool) : List Bool :=
  searchOutput (Nat.log 2 t) (sisWitness x)

/-- The matrix read from a coin string: entry `(i, j)` is the big-endian value of the coin block
number `i·m + j` of width `w`, reduced mod `q`. -/
def matOfCoins (n m q w : ℕ) (hq : 0 < q) (c : List Bool) : Fin n → Fin m → Fin q :=
  fun i j => ⟨valBE ((c.drop ((i.val * m + j.val) * w)).take w) % q, Nat.mod_lt _ hq⟩

/-- `D_sis(t, 1^λ)` (p. 58): samples a uniform matrix `Â ← ℤ_q̂^{n̂×m̂}` (with `n̂ = n̂(λ)`,
`m̂ = m̂(n̂)`, `q̂ = q̂(n̂)`) and outputs its code. It reads `(|input| + 2)^3` coins and takes `Â`'s
entries from consecutive blocks of `log q̂` coins; since `q̂` is a power of two and
`n̂ · m̂ · log q̂ ≤ (λ + 2)^3` (it is `6` when `n̂ = 1`), the output law is exactly uniform at every
input. -/
noncomputable def Dsis (e : ℝ) : CoinAlg puzzleCode where
  coins := (X + 2) ^ 3
  run := fun tl c =>
    encMat (matOfCoins (nHat e tl.2) (mHat e (nHat e tl.2)) (qHat e (nHat e tl.2))
      (Nat.log 2 (qHat e (nHat e tl.2))) (by unfold qHat; positivity) c)

/-- **The SIS puzzle** `(F_sis, D_sis)` of §7.3 (p. 58) for the constant `e`. -/
noncomputable def sisPuzzle (e : ℝ) : TreePuzzle := ⟨Fsis, Dsis e⟩

end PPADSIS.SubexpSIS


