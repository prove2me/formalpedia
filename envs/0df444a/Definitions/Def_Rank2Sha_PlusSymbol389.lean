-- Prove2me | Definitions.Def_Rank2Sha_PlusSymbol389
-- name    : Rank2Sha_PlusSymbol389
-- status  : Definition
-- author  : @barindersbanwait
-- created : 2026-11-25T22:34:26.898252+00:00
-- url     : https://prove2.me/theorems/d0901d46-e5d1-4633-85be-0fad30531d32
-- title:
--   The plus modular symbol of the elliptic curve 389a1
-- statement:
--   Let $E$ be the elliptic curve $y^2 + y = x^3 + x^2 - 2x$ over $\mathbb{Q}$ (LMFDB 389.a1), $f$ its newform of weight $2$ on $\Gamma_0(389)$, $\omega$ the invariant differential of this minimal model, and $\Omega^+ = \int_{E(\mathbb{R})} |\omega|$. Since $E(\mathbb{R})$ has two components, $\Omega^+ = 2\omega_1$ with $\omega_1$ the least positive real period. For cusps $\alpha, \beta$ put
--
--   $$
--   [\alpha, \beta]^+ = \frac{1}{\Omega^+}\, \mathrm{Re}\Big( 2\pi i \int_{\alpha}^{\beta} f(z)\, dz \Big), \qquad [r]^+ = [\infty, r]^+ \quad (r \in \mathbb{Q}).
--   $$
--
--   This file defines $[r]^+$ without modular forms, by Manin's method.
--
--   1. For $g = \begin{pmatrix} a & b \\ c & d \end{pmatrix} \in \mathrm{SL}_2(\mathbb{Z})$ the number $2\,[g\cdot 0, g\cdot\infty]^+ = 2\,[b/d, a/c]^+$ depends only on the point $(c : d)$ of $\mathbb{P}^1(\mathbb{Z}/389\mathbb{Z})$. The definition contains the table of these $390$ numbers; they are integers between $-2$ and $2$.
--   2. Let $r = a/n$ in lowest terms, with continued fraction convergents $p_k/q_k$ for $k = 0, \dots, m$ and $p_{-1}/q_{-1} = 1/0$. Then
--
--   $$
--   [r]^+ = \sum_{k=0}^{m} \big[ p_{k-1}/q_{k-1},\ p_k/q_k \big]^+ ,
--   $$
--
--   and the $k$-th path is $g_k \cdot \{0, \infty\}$ for $g_k = \begin{pmatrix} p_k & (-1)^{k-1}p_{k-1} \\ q_k & (-1)^{k-1}q_{k-1} \end{pmatrix} \in \mathrm{SL}_2(\mathbb{Z})$, so its value is half the table entry at $(q_k : (-1)^{k-1}q_{k-1})$.
--
--   `plusModularSymbol389 r` is $[r]^+$, and `twicePlusSymbol389 r` is the integer $2[r]^+$.
--
--   **Formalization Note** The table was computed with PARI/GP 2.17.2 (`msfromell`), whose modular symbol is normalised by $\omega_1 = \Omega^+/2$; its values are therefore the numbers $2[g\cdot 0, g\cdot\infty]^+$. The equality of `plusModularSymbol389 r` with the integral above is not proved in Lean: it rests on the Manin relations and on the table. The definition agrees with PARI's `mseval` at $3000$ rational numbers with denominators up to $10^{12}$. The point $(c : d)$ with $389 \nmid d$ has index $c\,d^{-1} \bmod 389$ in the table, and $(1 : 0)$ has index $389$.
-- source:
--   Y. I. Manin, Parabolic points and zeta functions of modular curves, Izv. Akad. Nauk SSSR Ser. Mat. 36 (1972) (Manin symbols; continued fractions) ; J. E. Cremona, Algorithms for Modular Elliptic Curves, 2nd ed., Cambridge University Press 1997, Chapter II ; C.-H. Kim, The structure of Selmer groups and the Iwasawa main conjecture for elliptic curves, Amer. J. Math. 148 (2026), arXiv:2203.12159v6, Section 1.4.1 (the normalisation by Omega^+) ; https://www.lmfdb.org/EllipticCurve/Q/389/a/1

import Mathlib.Data.Rat.Defs

/-!
# The plus modular symbol of the elliptic curve 389a1

Let `E` be the elliptic curve `y² + y = x³ + x² - 2x` over `ℚ` (LMFDB 389.a1), `f` its
newform of weight 2 on `Γ₀(389)`, `ω` the invariant differential of this global minimal
model and `Ω⁺ = ∫_{E(ℝ)} |ω|`. Since `E(ℝ)` has two components, `Ω⁺ = 2 ω₁`, where `ω₁`
is the least positive real period. For cusps `α, β` write

    [α, β]⁺ = Re(2πi ∫_α^β f(z) dz) / Ω⁺,      [r]⁺ = [∞, r]⁺  (r ∈ ℚ).

This file defines `[r]⁺` without modular forms, by Manin's method.

1. For `g = (a b; c d) ∈ SL₂(ℤ)` the value `2 [g·0, g·∞]⁺ = 2 [b/d, a/c]⁺` depends only on
   the point `(c : d)` of `ℙ¹(ℤ/389ℤ)`. `maninTable389` lists these 390 values; they are
   integers. The point `(c : d)` with `389 ∤ d` has index `c d⁻¹ mod 389 ∈ {0, …, 388}`,
   and `(1 : 0)` has index `389`.
2. Let `r = a/n` in lowest terms, `n ≥ 1`, with continued fraction convergents
   `p_k/q_k`, `k = 0, …, m`, and `p_{-1}/q_{-1} = 1/0`. Then
   `[∞, r]⁺ = ∑_{k=0}^{m} [p_{k-1}/q_{k-1}, p_k/q_k]⁺`, and the `k`-th path is `g_k·{0, ∞}`
   for `g_k = (p_k, (-1)^{k-1} p_{k-1}; q_k, (-1)^{k-1} q_{k-1}) ∈ SL₂(ℤ)`, whose bottom row
   is `(q_k, (-1)^{k-1} q_{k-1})`. Only the denominators `q_k` enter.

So `twicePlusSymbol389 r = 2 [r]⁺ ∈ ℤ` and `plusModularSymbol389 r = [r]⁺ ∈ (1/2)ℤ`.

The table was computed with PARI/GP 2.17.2 (`msfromell(E, 1)`, then `mseval` on the path
`{b/d, a/c}` for one `g` in each class; script `compute/gp/f3_table.gp` of the
rank2_finite_sha project). PARI's symbol is normalised by `ω₁ = Ω⁺/2`, so its values are
the values `2 [g·0, g·∞]⁺` recorded here.

**Formalization Note** The identity `plusModularSymbol389 r = Re(2πi ∫_{i∞}^r f(z) dz) / Ω⁺`
is not proved in Lean. It rests on the Manin relations and on the table. The definition was
checked against PARI's `mseval(M, xpm, [oo, r])` at 3000 values of `r` with denominators up
to `10¹²`, and is invariant under `r ↦ -r` and `r ↦ r + 1` on those values.
-/

namespace Rank2Sha

/-- The values `2 [g·0, g·∞]⁺` for `g ∈ SL₂(ℤ)` with bottom row `(c, d)`, indexed by the point
`(c : d)` of `ℙ¹(ℤ/389ℤ)`: index `c d⁻¹ mod 389` when `389 ∤ d`, index `389` for `(1 : 0)`. -/
def maninTable389 : Array ℤ := #[
  0, 0, 0, 0, 0, 2, 0, 1, 0, -1, 0, 1, 0, 0, -1, 0, 1, 0, 1, 0,
  -1, 0, 0, 0, 1, -1, 0, 1, 1, 0, 0, -1, -2, -2, -1, -1, 0, 0, -1, 0,
  1, 0, -1, 1, -1, 0, -1, -2, -2, 0, 0, 0, 0, 0, 0, -1, -1, -1, -1, -2,
  0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, -1, -1, -1, 0, 0, -2, -2, -2,
  -2, -1, -1, 0, 0, -1, -2, 0, 0, -1, -1, -2, -1, 1, 1, 2, 2, 0, 0, 1,
  1, 0, -1, 1, 0, -1, -1, -1, -1, -1, -1, -1, -1, -1, 1, 0, 1, 0, 1, 1,
  -1, 0, -1, 0, -1, -1, 0, 0, -2, 0, 0, 0, 1, 0, 1, -1, 0, -1, 1, 1,
  1, 2, 0, 0, 0, 1, 0, -1, 1, 2, 0, 0, 0, 0, 2, 2, 2, 0, 2, 1,
  1, 0, 0, 1, 1, 2, 0, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 1,
  0, 0, 1, 0, 1, 1, 0, 0, 0, -2, -1, -2, -2, 0, 0, 0, 0, -2, -2, -1,
  -2, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1,
  1, 1, 2, 0, 2, 1, 1, 0, 0, 1, 1, 2, 0, 2, 2, 2, 0, 0, 0, 0,
  2, 1, -1, 0, 1, 0, 0, 0, 2, 1, 1, 1, -1, 0, -1, 1, 0, 1, 0, 0,
  0, -2, 0, 0, -1, -1, 0, -1, 0, -1, 1, 1, 0, 1, 0, 1, -1, -1, -1, -1,
  -1, -1, -1, -1, -1, 0, 1, -1, 0, 1, 1, 0, 0, 2, 2, 1, 1, -1, -2, -1,
  -1, 0, 0, -2, -1, 0, 0, -1, -1, -2, -2, -2, -2, 0, 0, -1, -1, -1, 0, 0,
  0, 0, 0, 1, 0, 2, 0, 0, 0, 0, -2, -1, -1, -1, -1, 0, 0, 0, 0, 0,
  0, -2, -2, -1, 0, -1, 1, -1, 0, 1, 0, -1, 0, 0, -1, -1, -2, -2, -1, 0,
  0, 1, 1, 0, -1, 1, 0, 0, 0, -1, 0, 1, 0, 1, 0, -1, 0, 0, 1, 0,
  -1, 0, 1, 0, 2, 0, 0, 0, 0, 0]

/-- The inverse of `d` modulo `389` when `389 ∤ d`, as `d ^ 387 mod 389` (Fermat). -/
def inverseMod389 (d : ℤ) : ℤ := (d % 389) ^ 387 % 389

/-- The index in `{0, …, 389}` of the point `(c : d)` of `ℙ¹(ℤ/389ℤ)`, for coprime `c, d`. -/
def p1Index389 (c d : ℤ) : ℕ :=
  if d % 389 = 0 then 389 else (c * inverseMod389 d % 389).toNat

/-- The Manin symbol `2 [g·0, g·∞]⁺` of any `g ∈ SL₂(ℤ)` with bottom row `(c, d)`. -/
def maninSymbol389 (c d : ℤ) : ℤ := maninTable389.getD (p1Index389 c d) 0

/-- The sum of the Manin symbols along the Euclidean algorithm. Given the step of the
continued fraction of `u/v` that produces the convergent `k`, with `q₀ = q_{k-2}`,
`q₁ = q_{k-1}` and `s = (-1)^{k-1}`, it adds `maninSymbol389 q_k (s q_{k-1})` for this and
every later convergent. `fuel` bounds the number of steps; `fuel ≥ v + 1` suffices. -/
def maninSum389 : ℕ → ℕ → ℕ → ℤ → ℤ → ℤ → ℤ
  | 0, _, _, _, _, _ => 0
  | fuel + 1, u, v, q₀, q₁, s =>
    if v = 0 then 0 else
      let q₂ := ((u / v : ℕ) : ℤ) * q₁ + q₀
      maninSymbol389 q₂ (s * q₁) + maninSum389 fuel v (u % v) q₁ q₂ (-s)

/-- `2 [r]⁺` for the curve 389a1: the term `k = 0` (the path `{∞, ⌊r⌋}`, bottom row `(1, 0)`)
plus the terms `k ≥ 1` from the continued fraction of `n / (a mod n)`, `r = a/n`. -/
def twicePlusSymbol389 (r : ℚ) : ℤ :=
  maninSymbol389 1 0 + maninSum389 r.den r.den (r.num % r.den).toNat 0 1 1

/-- The plus modular symbol `[r]⁺ = Re(2πi ∫_{i∞}^r f(z) dz) / Ω⁺` of the curve 389a1,
`Ω⁺ = ∫_{E(ℝ)} |ω|`, computed by Manin's method from `maninTable389`. -/
def plusModularSymbol389 (r : ℚ) : ℚ := (twicePlusSymbol389 r : ℚ) / 2

end Rank2Sha


