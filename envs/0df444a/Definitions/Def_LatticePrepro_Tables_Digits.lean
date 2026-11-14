-- Prove2me | Definitions.Def_LatticePrepro_Tables_Digits
-- name    : LatticePrepro_Tables_Digits
-- status  : Definition
-- author  : @WizardOfMenlo
-- created : 2026-11-13T09:19:15.068211+00:00
-- url     : https://prove2.me/theorems/cc057c7c-e975-4472-b3f7-e9c338d9971a
-- title:
--   Generalized digits (Definition A.1)
-- statement:
--   Let $B$ (the base) and $m$ (the number of axes) be natural numbers. The bundle defines two functions.
--
--   1. **Value of an exponent vector** (`digitVal`): for $\eta=(\eta_0,\dots,\eta_{m-1})\in\mathbb{N}^m$,
--      $$\mathrm{val}_B(\eta)=\sum_{h=0}^{m-1}\eta_h\,B^h .$$
--   2. **Generalized digit vector** (`gdigits`): for $k\in\mathbb{N}$, write $k=t\,(B^m-1)+b$ with $t=\lfloor k/(B^m-1)\rfloor$ and $0\le b=k\bmod(B^m-1)<B^m-1$, and let $b_h=\lfloor b/B^h\rfloor\bmod B$ be the base-$B$ digits of $b$. Then
--      $$\mathrm{digits}_{B,m}(k)=\bigl(t\,(B-1)+b_h\bigr)_{h=0}^{m-1}\in\mathbb{N}^m .$$
--
--   Ordinary base-$B$ digits only describe numbers below $B^m$. The generalized digits allow entries larger than $B-1$, so that every order $k$ is the value of an exponent vector with small entries (Claim A.2). They index the interpolants that define the moment maps $\hat\mu_k$ in Construction A.4 and the entries of the polynomial matrix in Definition A.5.
--
--   **Formalization Note**: Exponent vectors are functions `Fin m → ℕ`. Both functions are defined for all natural numbers, with Lean's conventions $n/0=0$ and $n\bmod0=n$; the paper's standing assumptions $m\ge1$ and $B\ge2$ (which give $B^m-1\ge1$) appear as hypotheses of the lemmas about them. The monomials $\lambda^{\eta}$ of Definition A.1 are not part of this bundle; they appear directly in the column sums of Construction A.4. The paper writes $\mathsf d$ and $\mathsf a$ for $B$ and $m$.
-- source:
--   G. Weissenberg, G. Fenzi, Nearly Optimal Hardness for CVP and NCP with Preprocessing (STOC 2027 submission #847), Definition A.1 (\label{def:generalized-digits}); Lean: LatticePrepro/Tables/Digits.lean, LatticePrepro.digitVal, LatticePrepro.gdigits

import Mathlib

/-!
# Generalized digits (Definition A.1, Claim A.2)

Moment orders are written as exponent vectors `η : Fin m → ℕ` with
`val B η = ∑ h, η h * B ^ h`. The *generalized digit vector* of `k` is obtained by writing
`k = a · (B^m - 1) + b` with `0 ≤ b < B^m - 1` and taking `a · (B - 1)` plus the base-`B`
digits of `b`. It satisfies `val B (gdigits B m k) = k`, and for `k ≤ J · (B^m - 1)` all its
entries are at most `J · (B - 1)`.
-/

namespace LatticePrepro

/-- `val B η = ∑ h, η h * B ^ h`. -/
def digitVal (B : ℕ) {m : ℕ} (η : Fin m → ℕ) : ℕ := ∑ h : Fin m, η h * B ^ (h : ℕ)

/-- The generalized digit vector of `k` (Definition A.1). -/
def gdigits (B m k : ℕ) : Fin m → ℕ :=
  fun h => (k / (B ^ m - 1)) * (B - 1) + (k % (B ^ m - 1)) / B ^ (h : ℕ) % B

end LatticePrepro


