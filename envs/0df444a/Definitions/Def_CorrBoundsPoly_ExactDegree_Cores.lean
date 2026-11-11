-- Prove2me | Definitions.Def_CorrBoundsPoly_ExactDegree_Cores
-- name    : CorrBoundsPoly_ExactDegree_Cores
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T15:58:44.121202+00:00
-- url     : https://prove2.me/theorems/4777799e-acdb-4180-a5c0-7a7fdefc11e4
-- title:
--   Eq. (4.6) — the recursive exact-degree cores $F_s$ on $M(s)$ variables and the hard polynomials $H_{n,d}$
-- statement:
--   For dyadic $a\ge2$ let $E_a=\sigma_{a,3a^2}$. The **cores** $F_s$ ($s\ge1$), polynomials over $\mathbb F_2$ on $M(s)$ variables, are defined by recursion on $s$:
--
--   1. $F_1=x_1$, $M(1)=1$;
--   2. if $s\ge2$ is dyadic, $F_s=E_s$ and $M(s)=3s^2$;
--   3. otherwise write $s=a+t$ with $a$ the largest power of two below $s$ and $1\le t<a$, and on fresh disjoint variables
--   $$F_s=\bigoplus_{j=1}^{3}E_a(X^{(j)})\,F_t(Y^{(j)}),\qquad M(s)=3\big(3a^2+M(t)\big).$$
--
--   For $d\ge1$ and $n\ge M(d+1)$, $H_{n,d}$ is the sum of $\lfloor n/M(d+1)\rfloor$ copies of $F_{d+1}$ on disjoint blocks of $n$ variables, the remaining variables unused.
--
--   These are the explicit polynomials of the main theorem (Theorem 4.1): $F_s$ has degree exactly $s$ and $H_{n,d}$ degree exactly $d+1$.
--
--   **Formalization Note** `coreSig s : Σ m, MvPolynomial (Fin m) (ZMod 2)` is defined by strong recursion; `M s` is its first component and `F s : MvPolynomial (Fin (M s)) (ZMod 2)` its second, so $M(s)$ is the actual number of variables by construction. Dyadicity is decided by the test `2 ^ Nat.log 2 s = s`, and `a = 2 ^ Nat.log 2 s`, `t = s − a`. Variables are 0-based and laid out as follows: copy `j ∈ {0,1,2}` of the non-dyadic recursion occupies `j(3a² + M(t)), …, (j+1)(3a² + M(t)) − 1`, first the `3a²` variables $X^{(j)}$ of $E_a$ and then the `M(t)` variables $Y^{(j)}$ of $F_t$ (Mathlib's `finProdFinEquiv`, `Fin.castAdd`, `Fin.natAdd`). Copy `j < ⌊n/M(d+1)⌋` of `H n d` occupies variables `j·M(d+1), …, (j+1)·M(d+1) − 1` of `Fin n`; the last `n − ⌊n/M(d+1)⌋·M(d+1)` variables are unused. `F 0` is a placeholder (`0` on no variables); every statement takes `s ≥ 1`.
-- source:
--   Xin Li, More on Correlation Bounds for Polynomials, STOC 2027 submission (manuscript sha256 aa4ef6f7…), §4: Theorem 4.1, pp. 30–31 (PDF 32–33); proof of Lemma 4.3 and Eq. (4.6), pp. 31–32 (PDF 33–34)

import Mathlib
import Definitions.Def_CorrBoundsPoly_ExactDegree_ElemSym

namespace CorrBoundsPoly.ExactDegree

/-! Xin Li, *More on Correlation Bounds for Polynomials*, STOC 2027 submission (manuscript sha256
aa4ef6f7…), §4, pp. 30–32 (PDF 32–34): Lemma 4.3 and its proof (Eq. (4.6)), Theorem 4.1.

The recursive exact-degree cores `F_s` on `M(s)` variables and the hard polynomials `H_{n,d}`.

* `F_1 = x_1`, `M(1) = 1`.
* `s ≥ 2` dyadic: `F_s = E_s = σ_{s,3s²}`, `M(s) = 3s²`.
* `s ≥ 2` not dyadic: `s = a + t` with `a = 2^{⌊log₂ s⌋}` the largest power of two below `s` and
  `1 ≤ t < a`; `F_s = ⨁_{j=1}^{3} E_a(X^{(j)}) F_t(Y^{(j)})` on fresh disjoint variables,
  `M(s) = 3(3a² + M(t))`. Copy `j ∈ {0,1,2}` occupies the variables
  `j(3a² + M(t)), …, (j+1)(3a² + M(t)) − 1`: first the `3a²` variables `X^{(j)}` of `E_a`, then
  the `M(t)` variables `Y^{(j)}` of `F_t`.

`F_0` is a placeholder (`0` on no variables); every statement takes `s ≥ 1`. -/

/-- The pair `⟨M(s), F_s⟩`, by strong recursion on `s` (the test `2^{⌊log₂ s⌋} = s` decides
whether `s` is dyadic). -/
noncomputable def coreSig : ℕ → Σ m : ℕ, MvPolynomial (Fin m) (ZMod 2)
  | 0 => ⟨0, 0⟩
  | 1 => ⟨1, MvPolynomial.X 0⟩
  | s + 2 =>
    if 2 ^ Nat.log 2 (s + 2) = s + 2 then
      ⟨3 * (s + 2) ^ 2, sigma (s + 2) (3 * (s + 2) ^ 2)⟩
    else
      let c := coreSig (s + 2 - 2 ^ Nat.log 2 (s + 2))
      ⟨3 * (3 * (2 ^ Nat.log 2 (s + 2)) ^ 2 + c.1),
        ∑ j : Fin 3,
          MvPolynomial.rename
              (fun i : Fin (3 * (2 ^ Nat.log 2 (s + 2)) ^ 2) =>
                finProdFinEquiv (j, Fin.castAdd c.1 i))
              (sigma (2 ^ Nat.log 2 (s + 2)) (3 * (2 ^ Nat.log 2 (s + 2)) ^ 2)) *
            MvPolynomial.rename
              (fun i : Fin c.1 =>
                finProdFinEquiv (j, Fin.natAdd (3 * (2 ^ Nat.log 2 (s + 2)) ^ 2) i))
              c.2⟩
termination_by s => s
decreasing_by
  have := Nat.one_le_two_pow (n := Nat.log 2 (s + 2))
  omega

/-- `M(s)`, the number of variables of the core `F_s`. -/
noncomputable def M (s : ℕ) : ℕ := (coreSig s).1

/-- The core `F_s`, a polynomial over `F₂` in the variables `x_0, …, x_{M(s)−1}`. -/
noncomputable def F (s : ℕ) : MvPolynomial (Fin (M s)) (ZMod 2) := (coreSig s).2

/-- `H_{n,d}`: the sum (XOR) of `b = ⌊n/M(d+1)⌋` copies of `F_{d+1}` on disjoint blocks of `n`
variables, copy `j < b` on variables `j·M(d+1), …, (j+1)·M(d+1) − 1`; the last
`n − b·M(d+1)` variables are unused. -/
noncomputable def H (n d : ℕ) : MvPolynomial (Fin n) (ZMod 2) :=
  ∑ j : Fin (n / M (d + 1)),
    MvPolynomial.rename
      (fun i : Fin (M (d + 1)) =>
        Fin.castLE (Nat.div_mul_le_self n (M (d + 1))) (finProdFinEquiv (j, i)))
      (F (d + 1))

end CorrBoundsPoly.ExactDegree


