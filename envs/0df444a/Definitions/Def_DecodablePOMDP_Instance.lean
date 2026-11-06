-- Prove2me | Definitions.Def_DecodablePOMDP_Instance
-- name    : DecodablePOMDP_Instance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:23:49.684193+00:00
-- url     : https://prove2.me/theorems/78b67e89-1b8b-427e-bd35-b7a4728353a8
-- title:
--   Rational POMDP instances (the input of Theorem 1)
-- statement:
--   An **instance** is the data $(H,S,A,O,\mu_1,T,K,r,\varepsilon)$ with natural numbers $H,S,A,O$, rational entries $\mu_1(s)$, $T_h(s'\mid s,a)$ for $h\in[1:H-1]$, $K_h(y\mid s)$ and $r_h(y)$ for $h\in[2:H]$, and a rational accuracy $\varepsilon$. It is **valid** when $H,S,A,O\ge1$, $\mu_1$, every $T_h(\cdot\mid s,a)$ and every $K_h(\cdot\mid s)$ is a probability vector, every $r_h(y)\in[0,1]$, and $\varepsilon>0$.
--
--   Its POMDP has state space $[S]$, action space $[A]$, observation space $[O]$ and the given kernels (zero outside the printed index ranges, which are never read).
--
--   This is the input of the algorithm of Theorem 1: an algorithm in the bit model reads finitely many rational numbers.
-- source:
--   Dobson, Jog, Shiu, Quasipolynomial-Time Planning for Decodable POMDPs (preprint, sha256 c1256cbe…3584b), §2, p.6; Theorem 1, p.4

import Mathlib
import Definitions.Def_DecodablePOMDP_POMDP

namespace DecodablePOMDP

/-- **Rational POMDP instance** (the input of Theorem 1): `H, S, A, O ∈ ℕ`, rational
`μ₁ ∈ ℚ^S`, transition tables `T_h(s' | s, a)` for `h ∈ [1 : H−1]` (index `h − 1`), observation
tables `K_h(y | s)` and rewards `r_h(y)` for `h ∈ [2 : H]` (index `h − 2`), and the accuracy `ε`.

Dobson, Jog, Shiu (preprint, sha256 c1256cbe…3584b), §2, p.6: "The POMDP P with all its
parameters is thus P = (H, S, A, O, µ1, T, K, r)", and Theorem 1, p.4 ("let ε > 0").

**Formalization Note.** A bit-model algorithm reads finite data, so the entries are rational
(paper.md reading R2). -/
structure Instance where
  H : ℕ
  S : ℕ
  A : ℕ
  O : ℕ
  μ₁ : Fin S → ℚ
  T : Fin (H - 1) → Fin S → Fin A → Fin S → ℚ
  K : Fin (H - 1) → Fin S → Fin O → ℚ
  r : Fin (H - 1) → Fin O → ℚ
  ε : ℚ

/-- **Valid instance**: `H, S, A, O ≥ 1`; `μ₁`, every `T_h(· | s, a)` and every `K_h(· | s)` a
probability vector; every `r_h(y) ∈ [0, 1]`; and `ε > 0`.

Dobson, Jog, Shiu (preprint, sha256 c1256cbe…3584b), §2, pp.5–6 and Theorem 1, p.4. -/
def Instance.IsValid (I : Instance) : Prop :=
  1 ≤ I.H ∧ 1 ≤ I.S ∧ 1 ≤ I.A ∧ 1 ≤ I.O ∧
  (∀ s, 0 ≤ I.μ₁ s) ∧ ∑ s, I.μ₁ s = 1 ∧
  (∀ i s a, (∀ s', 0 ≤ I.T i s a s') ∧ ∑ s', I.T i s a s' = 1) ∧
  (∀ i s, (∀ y, 0 ≤ I.K i s y) ∧ ∑ y, I.K i s y = 1) ∧
  (∀ i y, 0 ≤ I.r i y ∧ I.r i y ≤ 1) ∧
  0 < I.ε

/-- **The POMDP of an instance**, over `Fin S`, `Fin A`, `Fin O`: `T_h` is table `h − 1` for
`h ∈ [1 : H−1]`, `K_h` and `r_h` are table `h − 2` for `h ∈ [2 : H]`, and every kernel is `0` out of
range (never read).

Dobson, Jog, Shiu (preprint, sha256 c1256cbe…3584b), §2, pp.5–6. -/
def Instance.toPOMDP (I : Instance) : POMDP (Fin I.S) (Fin I.A) (Fin I.O) where
  H := I.H
  μ₁ s := (I.μ₁ s : ℝ)
  T h s a s' := if hh : 1 ≤ h ∧ h - 1 < I.H - 1 then (I.T ⟨h - 1, hh.2⟩ s a s' : ℝ) else 0
  K h s y := if hh : 2 ≤ h ∧ h - 2 < I.H - 1 then (I.K ⟨h - 2, hh.2⟩ s y : ℝ) else 0
  r h y := if hh : 2 ≤ h ∧ h - 2 < I.H - 1 then (I.r ⟨h - 2, hh.2⟩ y : ℝ) else 0

end DecodablePOMDP


