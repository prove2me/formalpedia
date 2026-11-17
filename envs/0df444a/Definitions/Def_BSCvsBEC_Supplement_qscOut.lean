-- Prove2me | Definitions.Def_BSCvsBEC_Supplement_qscOut
-- name    : BSCvsBEC_Supplement_qscOut
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:33:32.816486+00:00
-- url     : https://prove2.me/theorems/d485c6b9-dd40-4319-96a7-64ca7bfa1b14
-- title:
--   The $q$-ary symmetric channel $\mathrm{qSC}_p$, its output pmf, and classical Rényi entropy
-- statement:
--   Let $\Omega$ be a finite alphabet with $|\Omega|=q$. Throughout the paper the crossover probability is tied to a correlation parameter $\rho$ by the standing convention
--   $$p=\frac{q-1}{q}(1-\rho)\qquad\text{(eq. (15))},$$
--   so $p=(1-\rho)/2$ for $q=2$.
--
--   The **$q$-ary symmetric channel** $\mathrm{qSC}_p$ sends a symbol $x\in\Omega$ to $y\in\Omega$ with probability $W(x\mid x)=1-p$ and $W(y\mid x)=p/(q-1)$ for $y\neq x$. On a word $x\in\Omega^n$ it acts on each coordinate independently, so a random $X\in\Omega^n$ with pmf $P$ produces the output pmf
--   $$P_Y(y)=\sum_{x\in\Omega^n}P(x)\prod_{i=1}^nW(y_i\mid x_i).$$
--   The output pmf of one fixed input symbol is $(1-p,\tfrac{p}{q-1},\dots,\tfrac{p}{q-1})$; its Rényi entropy is the quantity $H_\alpha(\mathrm{qSC}_p)$ of Theorem 2.7. For $q=2$ it is $\mathrm{Ber}(p)$.
--
--   The **Rényi entropy** of a pmf $P$, in bits, is $H_\alpha(P)=\frac1{1-\alpha}\log_2\sum_xP(x)^\alpha$ for $0<\alpha<\infty$, $\alpha\ne1$; $H_1$ is the Shannon entropy and $H_\infty(P)=\log_2\min_x(1/P(x))$ is the min-entropy.
--
--   **Formalization Note** The fixed input symbol is $0\in\{0,\dots,q-1\}$ (every input gives the same multiset of probabilities). The classical Rényi entropy is the published quantum Rényi entropy `BSCvsBEC.renyi` of the diagonal matrix $\mathrm{diag}(P)$, with $\alpha\in[0,\infty]$ an extended nonnegative real.
-- source:
--   J. Hązła, R. O'Donnell, BSC vs. BEC vs. PSC, manuscript of November 3, 2026 (STOC 2027 submission, preprint basis, sha256 a44ed9262ff4e01c0cbd7e204728d4ad8bf4cfda8dbf126b96022d4c84b56186), §2.1, eq. (15), p.5 (qSC_p, standing convention); pp.5–6 (Rényi entropies); Theorem 2.7, p.10 (H_α(qSC_p))

import Mathlib
import Definitions.Def_BSCvsBEC_renyi

namespace BSCvsBEC.Supplement

/-- The crossover probability of the standing convention (15): `p := ((q − 1)/q)(1 − ρ)`.
Hązła–O'Donnell, *BSC vs. BEC vs. PSC*, manuscript of November 3, 2026 (STOC 2027 submission,
sha256 a44ed926…), eq. (15), p.5 ("we take it as a standing notational convention throughout the
paper"); for `q = 2` it is `p = (1 − ρ)/2`.

**Formalization Note.** `q` is the alphabet size as a natural number, cast to `ℝ`. -/
noncomputable def qscP (q : ℕ) (ρ : ℝ) : ℝ :=
  ((q : ℝ) - 1) / q * (1 - ρ)

/-- The `q`-ary symmetric channel `qSC_p` on one symbol of a finite alphabet `Ω`, `|Ω| = q`:
`W(x|x) = 1 − p` and `W(y|x) = p/(q − 1)` for `y ≠ x`.
Hązła–O'Donnell, manuscript of November 3, 2026 (sha256 a44ed926…), §2.1, p.5.

**Formalization Note.** `qscKernel p x y = W(y | x)`. The alphabet is any finite type; the theorems
that use it assume `|Ω| ≥ 2`. -/
noncomputable def qscKernel {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (p : ℝ) (x y : Ω) : ℝ :=
  if y = x then 1 - p else p / ((Fintype.card Ω : ℝ) - 1)

/-- The output pmf of `qSC_p` applied coordinatewise to a random `X ∈ Ωⁿ` with pmf `P`:
`P_Y(y) = ∑ₓ P(x) ∏ᵢ W(yᵢ | xᵢ)`.
Hązła–O'Donnell, manuscript of November 3, 2026 (sha256 a44ed926…), §2.1, p.5 ("When sending
`x = (x₁, …, xₙ) ∈ Ωⁿ`, a given channel is applied to each coordinate independently"). -/
noncomputable def qscOut {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {n : ℕ} (p : ℝ)
    (P : (Fin n → Ω) → ℝ) : (Fin n → Ω) → ℝ :=
  fun y => ∑ x, P x * ∏ i, qscKernel p (x i) (y i)

/-- The output pmf of `qSC_p` for one fixed input symbol, on the alphabet `Fin q` with input `0`:
`(1 − p, p/(q − 1), …, p/(q − 1))`. Its Rényi entropy is the quantity `H_α(qSC_p)` of Theorem 2.7
("the output entropy of passing any fixed input symbol through the `q`-ary symmetric channel"),
Hązła–O'Donnell, manuscript of November 3, 2026 (sha256 a44ed926…), p.10.

**Formalization Note.** The input symbol is `0 : Fin q`; by symmetry every fixed input gives the
same multiset of output probabilities. For `q = 2` this is `Ber(p)` written as `(1 − p, p)`. -/
noncomputable def qscRow (q : ℕ) (p : ℝ) : Fin q → ℝ :=
  fun y => if y.val = 0 then 1 - p else p / ((q : ℝ) - 1)

/-- The classical Rényi entropy `H_α(P)` (bits) of a pmf `P`, `0 < α ≤ ∞`: the published quantum
`BSCvsBEC.renyi` of the diagonal density matrix `diag(P)`, i.e. `(1/(1 − α)) log₂ ∑ₓ P(x)^α` for
`α ≠ 1, ∞`, the Shannon entropy for `α = 1` and the min-entropy `log₂ (minₓ 1/P(x))` for `α = ∞`.
Hązła–O'Donnell, manuscript of November 3, 2026 (sha256 a44ed926…), §2.1, pp.5–6.

**Formalization Note.** `α : ℝ≥0∞` with `α = ⊤` the min-entropy, as in `BSCvsBEC.renyi`; the
spectrum of `diag(P)` is the multiset of values of `P`. -/
noncomputable def renyiP {ι : Type} [Fintype ι] [DecidableEq ι] (α : ENNReal) (P : ι → ℝ) : ℝ :=
  BSCvsBEC.renyi α (Matrix.diagonal (fun x => ((P x : ℝ) : ℂ)))

end BSCvsBEC.Supplement


