-- Prove2me | Definitions.Def_KelnerLinSolve_trialY
-- name    : KelnerLinSolve_trialY
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:55:48.387481+00:00
-- url     : https://prove2.me/theorems/419936c4-7bef-4278-96a1-b5aa604e538a
-- title:
--   Rounding to nearest and the scaled perturbed solution $y$ of one precision trial
-- statement:
--   A map $\mathrm{round}:\mathbb R\to\mathbb Z$ **rounds to nearest** if $|\mathrm{round}(x)-x|\le 1/2$ for every $x$. At a tie it picks one of the two nearest integers, and that choice is its tie rule. It maps $0$ to $0$, so it preserves zero entries.
--
--   For $A_0\in\mathbb R^{n\times n}$, $b_0\in\mathbb R^n$ and a precision $h$, put $\ell = \lceil\log_2 n\rceil$, $S = 2^h$, $C = \mathrm{round}(SA_0)$, $d = \mathrm{round}(Sb_0)$ entrywise, $R = 2^{h+\ell+1}$, and
--
--   $$
--   y = R\,(I + RC)^{-1} d .
--   $$
--
--   **Formalization Note** The inverse is over $\mathbb R$ on the integer matrix $I+RC$, whose determinant is an integer $\equiv 1 \pmod R$, so it is the true inverse also when $C$ is singular. $\ell$ is `Nat.clog 2 n`.
-- source:
--   Kelner, Solving Linear Systems in Õ(mn log(κ/ε)) Bit Operations, STOC 2027 submission (sha256 d1af55cb…), Lemma 3.4, p.11; §4.1–4.2, (10)–(11), pp.12–13

import Mathlib
import Definitions.Def_KelnerLinSolve_kappa2

open Matrix

namespace KelnerLinSolve

/-- **Rounding to nearest.** `rnd : ℝ → ℤ` returns an integer nearest to its argument:
`|rnd x − x| ≤ 1/2` for every `x`. At a tie `x ∈ ℤ + 1/2` the function picks one of the two
nearest integers, and that choice is its tie rule. Such a function maps `0` to `0`, so it preserves
zero entries. Kelner, *Solving Linear Systems in Õ(mn log(κ/ε)) Bit Operations*, STOC 2027
submission (sha256 d1af55cb…), Lemma 3.4, p.11: "Round entries to nearest with a fixed tie rule,
preserving zero entries". -/
def IsNearestRounding (rnd : ℝ → ℤ) : Prop := ∀ x : ℝ, |(rnd x : ℝ) - x| ≤ 1 / 2

/-- **The scaled perturbed solution `y` of one precision trial** (Kelner, sha256 d1af55cb…,
Lemma 3.4, p.11; §4.2, (10)–(11), pp.12–13): for precision `h`, with `ℓ = ⌈log₂ n⌉`, `S = 2^h`,
`C = round(S A₀)`, `d = round(S b₀)`, `R = 2^{h+ℓ+1}`,
`y = R (I + R C)⁻¹ d`.

**Formalization Note.** `ℓ = Nat.clog 2 n` is `⌈log₂ n⌉` for `n ≥ 1`. The inverse is taken over `ℝ`
on the integer-valued matrix `I + R C`, whose determinant is an integer `≡ 1 (mod R)`, hence nonzero:
`⁻¹` is the true inverse, also when `C` is singular. -/
noncomputable def trialY {n : ℕ} (rnd : ℝ → ℤ) (A₀ : Matrix (Fin n) (Fin n) ℝ) (b₀ : Fin n → ℝ)
    (h : ℕ) : Fin n → ℝ :=
  let S : ℝ := 2 ^ h
  let R : ℝ := 2 ^ (h + Nat.clog 2 n + 1)
  let C : Matrix (Fin n) (Fin n) ℝ := fun i j => (rnd (S * A₀ i j) : ℝ)
  let d : Fin n → ℝ := fun i => (rnd (S * b₀ i) : ℝ)
  R • ((1 + R • C)⁻¹ *ᵥ d)

end KelnerLinSolve


