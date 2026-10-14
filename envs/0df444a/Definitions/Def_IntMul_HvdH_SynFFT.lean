-- Prove2me | Definitions.Def_IntMul_HvdH_SynFFT
-- name    : IntMul_HvdH_SynFFT
-- status  : Definition
-- author  : @xuanji
-- created : 2026-10-12T01:27:01.598674+00:00
-- url     : https://prove2.me/theorems/4981c90a-33e6-44ce-9e41-2cae5e6a9830
-- title:
--   Synthetic FFT over C[y]/(y^r+1) and its fixed-point version (Harvey–van der Hoeven §3.2)
-- statement:
--   The radix-2 synthetic FFT of Harvey–van der Hoeven §3.2 (Lemma 3.2), over $R=\mathbb C[y]/(y^r+1)$. A vector of $R^t$ with $t=2^e$ is an array $u:\mathbb N\times\mathbb N\to\mathbb C$, where $u(k,c)$ is the coefficient of $y^c$ in entry $k$.
--
--   * `yShift r m a` is the coefficient array of $y^m a$ in $R$, for $m\in\mathbb Z$.
--   * `synG r e` is the normalised transform $\tfrac1t\hat u$, computed by the Cooley–Tukey recursion. Each level halves the sums $(u_k+u_{k+t/2})/2$ for even outputs, and halves the differences multiplied by $y^{-2rk/t}$ for odd outputs.
--   * `halfZ` halves a Gaussian integer, rounding each part towards zero.
--   * `synGa r e` is the same recursion on fixed-point integer arrays `ℤ × ℤ`, using `halfZ` in place of division by 2.
-- source:
--   Harvey, van der Hoeven, Integer multiplication in time O(n log n), Annals of Math. 193 (2021), https://hal.science/hal-02070778, §3.2, Lemma 3.2

import Definitions.Def_IntMul_HvdH_FPApprox

/-! The synthetic FFT over `R = ℂ[y]/(y^r + 1)` and its fixed-point approximation
(Harvey–van der Hoeven Lemma 3.2). A vector in `R^t` is stored as an array `u : ℕ × ℕ → ℂ`,
where `u (k, c)` is the coefficient of `y^c` in the `k`-th entry; integer arrays
`U : ℕ × ℕ → ℤ × ℤ` stand for `2^{-p} U` as usual. -/

namespace IntMul.HvdH

/-- Coefficient `c` of `y^m a` in `ℂ[y]/(y^r + 1)` (for any `m : ℤ`), where `a c'` is the
coefficient of `y^{c'}`: writing `c - m = qr + i` with `0 ≤ i < r`, it is `(-1)^q a_i`. -/
def yShift {β : Type*} [Neg β] (r : ℕ) (m : ℤ) (a : ℕ → β) (c : ℕ) : β :=
  if ((c - m) / r) % 2 = 0 then a ((c - m) % r).toNat else -a ((c - m) % r).toNat

/-- The exact radix-2 synthetic transform `G_{2^e}` defined by the Cooley–Tukey recursion:
`(G_t u)_{2ℓ} = (G_{t/2} v)_ℓ` and `(G_t u)_{2ℓ+1} = (G_{t/2} w)_ℓ`, with
`v_k = (u_k + u_{k+t/2})/2` and `w_k = y^{-2rk/t} (u_k - u_{k+t/2})/2`. -/
noncomputable def synG (r : ℕ) : ℕ → ((ℕ × ℕ) → ℂ) → ((ℕ × ℕ) → ℂ)
  | 0 => id
  | e + 1 => fun u kc =>
    if kc.1 % 2 = 0 then
      synG r e (fun kc' => (u kc' + u (kc'.1 + 2 ^ e, kc'.2)) / 2) (kc.1 / 2, kc.2)
    else
      synG r e (fun kc' => yShift r (-((2 * r / 2 ^ (e + 1) * kc'.1 : ℕ) : ℤ))
        (fun c => (u (kc'.1, c) - u (kc'.1 + 2 ^ e, c)) / 2) kc'.2) (kc.1 / 2, kc.2)

/-- Halving a Gaussian integer, rounding each component towards zero. -/
def halfZ (z : ℤ × ℤ) : ℤ × ℤ := (z.1.tdiv 2, z.2.tdiv 2)

/-- Lemma 3.2: the fixed-point synthetic FFT `G̃_{2^e}`, following the same recursion with the
butterflies rounded by `halfZ` (the twiddle multiplications by powers of `y` are exact). -/
def synGa (r : ℕ) : ℕ → ((ℕ × ℕ) → ℤ × ℤ) → ((ℕ × ℕ) → ℤ × ℤ)
  | 0 => id
  | e + 1 => fun U kc =>
    if kc.1 % 2 = 0 then
      synGa r e (fun kc' => halfZ (U kc' + U (kc'.1 + 2 ^ e, kc'.2))) (kc.1 / 2, kc.2)
    else
      synGa r e (fun kc' => yShift r (-((2 * r / 2 ^ (e + 1) * kc'.1 : ℕ) : ℤ))
        (fun c => halfZ (U (kc'.1, c) - U (kc'.1 + 2 ^ e, c))) kc'.2) (kc.1 / 2, kc.2)

end IntMul.HvdH


