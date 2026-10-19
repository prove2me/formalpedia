-- Prove2me | Definitions.Def_DusartCertCore
-- name    : DusartCertCore
-- status  : Definition
-- author  : @@bwdaugherty
-- created : 2026-10-16T20:32:14.166675+00:00
-- url     : https://prove2.me/theorems/1bec2929-578b-42fe-a43a-b8644b20d219
-- title:
--   Kernel certificate checker for prime sums and logarithms
-- statement:
--   Integer-valued functions that the Lean kernel evaluates to certify bounds for prime sums on a finite range. Fix $Q=2^{64}$.
--
--   1. **Wheel walk.** `step` runs through the integers coprime to $210$ from a given start, reading one code per candidate: code $0$ keeps the candidate $n$ and adds $\lceil Q/n\rceil$ and an upper bound for $Q\,(-\log(1-1/n)-1/n)$ to two accumulators; a code $d$ must satisfy $1<d<n$ and $d\mid n$. Every prime above $7$ is therefore kept, and the accumulators bound $Q\sum 1/p$ and $Q\sum(-\log(1-1/p)-1/p)$ from above.
--   2. **Logarithms.** `logLo`, `logHi` give $\lfloor\cdot\rfloor$/$\lceil\cdot\rceil$ fixed-point bounds for $Q\log(a/b)$ from the series $\log y=\sum_j 2z^{2j+1}/(2j+1)$, $z=(y-1)/(y+1)$, with a range reduction by powers of $2$ and a geometric remainder.
--   3. **Cells.** `cellOK` checks one mesh cell $[a,b)$ of the inequality $\sum_{p<b}1/p-B\le\log\log a+\frac1{10\log^2b}+\frac4{15\log^3b}$ in fixed point; `run` chains wheel blocks and cell checks; `bOK` checks a lower bound for Mertens' constant $B$ (from $H_{1024}$, $\log 2$ and the accumulated prime sums).
--
--   **Formalization Note** All functions are on `Nat`; the soundness statements relating them to real numbers are proved in the theorems that use them.
-- source:
--   P. Dusart, Estimates of some functions over primes without R.H., arXiv:1002.0442 (2010), Theorem 6.10 (upper bound for x ≥ 10372) and Theorem 5.2 (k = 2, η = 0.2, x ≥ 3 594 641); the proof of Theorem 6.10 closes the range below 3 594 641 by a computer check.

/-! Kernel-evaluable certificate checker for the finite range of Dusart's Theorem 6.10 (wheel mod 210,
fixed-point prime sums, fixed-point logarithms, mesh-cell checks). -/

/-! Kernel-checked wheel certificate checker (mod 210) for prime sums. -/

namespace DusartCert

/-- Residues coprime to 210, in increasing order. -/
def res : List Nat := [1, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 121, 127, 131, 137, 139, 143, 149, 151, 157, 163, 167, 169, 173, 179, 181, 187, 191, 193, 197, 199, 209]

/-- Gaps between consecutive residues coprime to 210 (the last wraps from 209 to 211). -/
def gaps : List Nat := [10, 2, 4, 2, 4, 6, 2, 6, 4, 2, 4, 6, 6, 2, 6, 4, 2, 6, 4, 6, 8, 4, 2, 4, 2, 4, 8, 6, 4, 6, 2, 4, 6, 2, 6, 6, 4, 2, 4, 6, 2, 6, 4, 2, 4, 2, 10, 2]

/-- Ceiling division. -/
def cdiv (a b : Nat) : Nat := (a + b - 1) / b

/-- `∑_{k=2}^{m} ⌈Q/(k n^k)⌉`. -/
def gpart (Q n : Nat) : Nat → Nat
  | 0 => 0
  | 1 => 0
  | k + 2 => gpart Q n (k + 1) + cdiv Q ((k + 2) * n ^ (k + 2))

/-- Truncation order of the series for `-log(1 - 1/n) - 1/n`. -/
def gord (n : Nat) : Nat := if n < 100 then 24 else 4

/-- Fixed-point upper bound for `-log(1 - 1/n) - 1/n`:
`∑_{k=2}^{m} ⌈Q/(k n^k)⌉ + ⌈Q/((m+1) n^m (n-1))⌉`. -/
def wG (Q n : Nat) : Nat := gpart Q n (gord n) + cdiv Q ((gord n + 1) * n ^ gord n * (n - 1))

/-- Walk the wheel candidates from `n` (at wheel index `i`) with codes: `0` keeps `n`, adding `⌈Q/n⌉` to `a` and
`wG Q n` to `b`; a code `d` must satisfy `1 < d < n`, `n % d = 0`. Returns `(a, b, end)`, or `none`. -/
def step (Q : Nat) : List Nat → Nat → Nat → Nat → Nat → Option (Nat × Nat × Nat)
  | [], _, n, a, b => some (a, b, n)
  | c :: cs, i, n, a, b =>
    let g := gaps.getD i 0
    let i' := (i + 1) % 48
    if c == 0 then step Q cs i' (n + g) (a + cdiv Q n) (b + wG Q n)
    else if 1 < c && c < n && n % c == 0 then step Q cs i' (n + g) a b else none

end DusartCert


/-! Kernel-evaluable fixed-point bounds for `log`, by the series `log y = ∑ 2 z^(2j+1)/(2j+1)`, `z = (y-1)/(y+1)`. -/

namespace DusartCert

/-- `⌊Q · 2 a^(2j+1) / ((2j+1) b^(2j+1))⌋`. -/
def ltermLo (Q a b j : Nat) : Nat := 2 * Q * a ^ (2 * j + 1) / ((2 * j + 1) * b ^ (2 * j + 1))

/-- `⌈Q · 2 a^(2j+1) / ((2j+1) b^(2j+1))⌉`. -/
def ltermHi (Q a b j : Nat) : Nat := cdiv (2 * Q * a ^ (2 * j + 1)) ((2 * j + 1) * b ^ (2 * j + 1))

def lsumLo (Q a b : Nat) : Nat → Nat
  | 0 => 0
  | K + 1 => lsumLo Q a b K + ltermLo Q a b K

def lsumHi (Q a b : Nat) : Nat → Nat
  | 0 => 0
  | K + 1 => lsumHi Q a b K + ltermHi Q a b K

/-- Remainder `⌈Q · 2 a^(2K+1) b² / ((2K+1) b^(2K+1) (b² - a²))⌉`. -/
def lrem (Q a b K : Nat) : Nat := cdiv (2 * Q * a ^ (2 * K + 1) * b ^ 2) ((2 * K + 1) * b ^ (2 * K + 1) * (b ^ 2 - a ^ 2))

/-- Number of series terms. -/
def nterms : Nat := 16

/-- Lower / upper fixed-point bounds for `Q log(num/den)`, `den ≤ num`. -/
def logRedLo (Q num den : Nat) : Nat := lsumLo Q (num - den) (num + den) nterms
def logRedHi (Q num den : Nat) : Nat :=
  lsumHi Q (num - den) (num + den) nterms + lrem Q (num - den) (num + den) nterms

/-- Bounds for `Q log(num/den)` with range reduction `den 2^k ≤ num ≤ 2 den 2^k`. -/
def logLo (Q num den k : Nat) : Nat := k * logRedLo Q 2 1 + logRedLo Q num (den * 2 ^ k)
def logHi (Q num den k : Nat) : Nat := k * logRedHi Q 2 1 + logRedHi Q num (den * 2 ^ k)

/-- The range-reduction condition. -/
def redOK (num den k : Nat) : Bool := den * 2 ^ k ≤ num && num ≤ 2 * (den * 2 ^ k) && 0 < den

end DusartCert


namespace DusartCert

/-- `∑_{k=1}^n ⌊Q/k⌋`. -/
def hsum (Q : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => hsum Q n + Q / (n + 1)

end DusartCert


namespace DusartCert

/-- `⌈Q/2⌉ + ⌈Q/3⌉ + ⌈Q/5⌉ + ⌈Q/7⌉`. -/
def smallQ (Q : Nat) : Nat := cdiv Q 2 + cdiv Q 3 + cdiv Q 5 + cdiv Q 7

/-- Cell check on `[a, b)`: `Shi ≤ ⌊Q log log a⌋ + ⌊Q r(b)⌋ + Blo`, with `r(L) = 1/(10L²) + 4/(15L³)`. -/
def cellOK (Q Blo a b Shi k1a k1b k2 : Nat) : Bool :=
  decide (a ≤ b) && redOK a 1 k1a && redOK b 1 k1b && redOK (logLo Q a 1 k1a) Q k2 &&
    decide (Shi ≤ logLo Q (logLo Q a 1 k1a) Q k2 +
      (Q ^ 3 / (10 * logHi Q b 1 k1b ^ 2) + 4 * Q ^ 4 / (15 * logHi Q b 1 k1b ^ 3)) + Blo)

/-- Run a list of chunks from state `(n, i, A, G, lb)`; a chunk may carry a cell check `[lb, end)`. -/
def run (Q Blo : Nat) : List (List Nat × Option (Nat × Nat × Nat)) →
    Nat × Nat × Nat × Nat × Nat → Option (Nat × Nat × Nat × Nat × Nat)
  | [], s => some s
  | (codes, chk) :: rest, (n, i, A, G, lb) =>
    match step Q codes i n 0 0 with
    | none => none
    | some (a', g', n') =>
      match chk with
      | none => run Q Blo rest (n', (i + codes.length) % 48, A + a', G + g', lb)
      | some (k1a, k1b, k2) =>
        if cellOK Q Blo lb n' (smallQ Q + (A + a')) k1a k1b k2 then
          run Q Blo rest (n', (i + codes.length) % 48, A + a', G + g', n')
        else none

/-- Final arithmetic check for the Mertens-constant lower bound `Blo` (see `B_lower`, `gamma_lower`). -/
def bOK (Q Blo E G : Nat) : Bool :=
  decide (12 ≤ E) &&
  decide (4096 * (E - 1) * (Blo + 10 * logRedHi Q 2 1 + (wG Q 2 + wG Q 3 + wG Q 5 + wG Q 7) + G) +
      2 * (E - 1) * Q + 2048 * Q ≤ 4096 * (E - 1) * hsum Q 1024)

end DusartCert


