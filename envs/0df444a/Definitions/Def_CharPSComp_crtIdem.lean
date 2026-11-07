-- Prove2me | Definitions.Def_CharPSComp_crtIdem
-- name    : CharPSComp_crtIdem
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:07:30.087201+00:00
-- url     : https://prove2.me/theorems/39291067-a16f-475b-ab37-d1a2ae1b7058
-- title:
--   Prime-power parts $c_p=p^{v_p(c)}$ and the Chinese-remainder idempotents $\epsilon_i=(d_iu_i)\cdot1_R$
-- statement:
--   Factor $c=\prod_ic_i$ into pairwise coprime prime powers. Here the component of a prime $p\mid c$ has $c_p\triangleq p^{v_p(c)}$ (`ppart c p`). For $d_i\triangleq c/c_i$ and a chosen integer $u_i$ with $d_iu_i\equiv1\pmod{c_i}$, the **idempotent** is $\epsilon_i\triangleq(d_iu_i)\cdot1_R$ (`crtIdem R c p u`).
--
--   These elements split a ring of characteristic $c$ into the components $\epsilon_iR$ of prime-power characteristic on which Algorithm 3 runs.
-- source:
--   Zhu, Faster Power Series Composition in Fixed Positive Characteristic, STOC 2027 submission (manuscript sha256 e63e0527228218d0d0b04691cbfb8b92cc1c9c7abddec6972d71bbab231c6361), §3.6.3, p.17 (PDF p.18)

import Mathlib

namespace CharPSComp

/-- The prime-power part `c_p = p^{v_p(c)}` of `c` (Zhu, *Faster Power Series Composition in Fixed
Positive Characteristic*, STOC 2027 submission (manuscript sha256 e63e0527…), §3.6.3, p.17,
PDF p.18: "Factor `c = Π_{i=1}^r c_i` into pairwise coprime prime powers"). -/
def ppart (c p : ℕ) : ℕ := p ^ c.factorization p

/-- The Chinese-remainder idempotent of ibid., §3.6.3, p.17 (PDF p.18): for `d_i ≜ c/c_i` and an
integer `u_i` with `d_i u_i ≡ 1 (mod c_i)`, `ϵ_i ≜ (d_i u_i) · 1_R`. Here `c_i = ppart c p` for a
prime `p ∣ c`, and `u` is the chosen integer `u_i`. -/
def crtIdem (R : Type*) [Ring R] (c p : ℕ) (u : ℤ) : R :=
  (((c / ppart c p : ℕ) : ℤ) * u : ℤ)

end CharPSComp


