-- Prove2me | Definitions.Def_BSCvsBEC_Supplement_lamStarB
-- name    : BSCvsBEC_Supplement_lamStarB
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:35:30.929963+00:00
-- url     : https://prove2.me/theorems/a68d82a6-1497-4080-be29-7a57690fda7f
-- title:
--   $\|\cdot\|_\alpha$, $E_S$, $T_\rho$ on $\Omega^n$, the Samorodnitsky constants $\lambda^*$, and $\tau_\alpha(\theta)$, $\tau_\alpha(q,\theta)$
-- statement:
--   Let $|\Omega|=q$ and let $U$ be uniform on $\Omega^n$. For $g:\Omega^n\to\mathbb R$ and $\alpha>0$,
--   $$\|g\|_\alpha=\big(\mathbb E_U|g(U)|^\alpha\big)^{1/\alpha}$$
--   (a norm iff $\alpha\ge1$). For $S\subseteq[n]$, the **conditional expectation** $E_Sf(y)=\mathbb E[f(U)\mid U_S=y_S]$ averages $f$ over the $q^{n-|S|}$ words that agree with $y$ on $S$. For $\rho\in[0,1]$ the **noise operator** is $T_\rho f(y)=\mathbb E[f(U)\mid Y=y]$ with $Y=\mathrm{qSC}_p(U)$, $p=\frac{q-1}q(1-\rho)$; explicitly $T_\rho f(y)=\sum_x\prod_iW(y_i\mid x_i)f(x)$.
--
--   The **Samorodnitsky constants** of Theorem 2.7 are:
--
--   1. for $2\le\alpha\le\infty$: $\lambda^*(\alpha,q,\rho)=1-H_\alpha(\mathrm{qSC}_p)/\log q$;
--   2. for $q=2$, $1<\alpha<2$: $\lambda^*(\alpha,2,\rho)$ is the optimal $n=1$ constant, the infimum of the $\lambda\in[0,1]$ such that for every $g:\mathbb F_2\to\mathbb R_{\ge0}$
--   $$\log\|T_\rho g\|_\alpha\le\lambda\log\|g\|_\alpha+(1-\lambda)\log\|\mathbb E g\|_\alpha .$$
--
--   Finally $\tau_\alpha(\theta)=1-\lambda^*(\alpha,2,\cos\theta)$ for $1<\alpha<\infty$ (case 1 for $\alpha\ge2$, case 2 for $\alpha<2$), and $\tau_\alpha(q,\theta)=H_\alpha(\mathrm{qSC}_p)/\log q$ with $p=\frac{q-1}q(1-\cos\theta)$.
--
--   **Formalization Note** The $n=1$ inequality is written with the published random-subset expectation at $n=1$ ($S=\{1\}$ with probability $\lambda$, $S=\emptyset$ otherwise) and natural logarithms (the inequality is base-invariant). The infimum ranges over a set that contains $\lambda=1$ and lies in $[0,1]$. Entropies and $\log q$ are in bits.
-- source:
--   J. Hązła, R. O'Donnell, BSC vs. BEC vs. PSC, manuscript of November 3, 2026 (STOC 2027 submission, preprint basis, sha256 a44ed9262ff4e01c0cbd7e204728d4ad8bf4cfda8dbf126b96022d4c84b56186), eqs. (18)–(21), p.6; Theorem 2.7, eq. (51), p.10; §4.3, p.22 (τ_α(θ)); §5, p.23 (τ_α(q, θ))

import Mathlib
import Definitions.Def_BSCvsBEC_expectSubset
import Definitions.Def_BSCvsBEC_Supplement_qscOut

namespace BSCvsBEC.Supplement

/-- The (quasi-)norm `‖g‖_α := E_U[|g(U)|^α]^{1/α}` of eq. (18), `U` uniform on `Ωⁿ`, `α > 0`.
Hązła–O'Donnell, *BSC vs. BEC vs. PSC*, manuscript of November 3, 2026 (STOC 2027 submission,
sha256 a44ed926…), eq. (18), p.6 ("this is a norm iff `α ≥ 1`").

**Formalization Note.** `E_U` is `(1/|Ωⁿ|) ∑ₓ`; powers are real powers of nonnegative reals. For
`α = 1/2`, `‖g‖_{1/2} = (E √|g|)²`. -/
noncomputable def unifNorm {Ω : Type*} [Fintype Ω] {n : ℕ} (α : ℝ) (g : (Fin n → Ω) → ℝ) : ℝ :=
  ((∑ x, |g x| ^ α) / (Fintype.card (Fin n → Ω) : ℝ)) ^ (1 / α)

/-- The conditional expectation operator `E_S f(y) = E[f(U) | U_S = y_S]` of eq. (19), `U` uniform on
`Ωⁿ`: the average of `f` over the `q^{n − |S|}` words agreeing with `y` on `S`.
Hązła–O'Donnell, manuscript of November 3, 2026 (sha256 a44ed926…), eq. (19), p.6. -/
noncomputable def condExpS {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {n : ℕ} (S : Finset (Fin n))
    (f : (Fin n → Ω) → ℝ) : (Fin n → Ω) → ℝ :=
  fun y => (∑ x, if (∀ i ∈ S, x i = y i) then f x else 0) /
    (Fintype.card Ω : ℝ) ^ (n - S.card)

/-- The noise operator `T_ρ f(y) = E[f(U) | Y = y]`, `Y = qSC_p(U)`, `p = ((q − 1)/q)(1 − ρ)`, of
eq. (21); since `U` is uniform and `qSC_p` is doubly stochastic, `T_ρ f(y) = ∑ₓ ∏ᵢ W(yᵢ|xᵢ) f(x)`
(for `q = 2`: `∑ₓ p^{|x+y|}(1 − p)^{n−|x+y|} f(x)`).
Hązła–O'Donnell, manuscript of November 3, 2026 (sha256 a44ed926…), eq. (21), p.6, for `ρ ∈ [0, 1]`.

**Formalization Note.** Written through the explicit kernel (the conditional law of `U` given `Y`). -/
noncomputable def noiseN {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {n : ℕ} (ρ : ℝ)
    (f : (Fin n → Ω) → ℝ) : (Fin n → Ω) → ℝ :=
  fun y => ∑ x, (∏ i, qscKernel (qscP (Fintype.card Ω) ρ) (x i) (y i)) * f x

/-- `λ*(α, q, ρ) := 1 − H_α(qSC_p)/log q` (eq. (51), for `|Ω| = q` and `2 ≤ α ≤ ∞`), with
`H_α(qSC_p)` the Rényi entropy of the output of one fixed input symbol and `p = ((q − 1)/q)(1 − ρ)`.
Hązła–O'Donnell, manuscript of November 3, 2026 (sha256 a44ed926…), Theorem 2.7, eq. (51), p.10.

**Formalization Note.** Entropies and `log q` are both in bits (the ratio does not depend on the
base). `α : ℝ≥0∞`, `α = ⊤` the min-entropy. -/
noncomputable def lamStarA (α : ENNReal) (q : ℕ) (ρ : ℝ) : ℝ :=
  1 - renyiP α (qscRow q (qscP q ρ)) / Real.logb 2 q

/-- `λ*(α, 2, ρ)` for `1 < α < 2`: "the optimal `n = 1` constant" of Theorem 2.7, i.e. the infimum
of the `λ ∈ [0, 1]` such that the `n = 1` case of (51),
`log ‖T_ρ g‖_α ≤ E_{S∼λ} log ‖E_S g‖_α = λ log ‖g‖_α + (1 − λ) log ‖E g‖_α`, holds for every
`g : F₂ → ℝ≥0`.
Hązła–O'Donnell, manuscript of November 3, 2026 (sha256 a44ed926…), Theorem 2.7, p.10 ("For `q = 2`
and `1 < α < 2`, the above holds with `λ*(α, 2, ρ)` being the optimal `n = 1` constant").

**Formalization Note.** `F₂ = Fin 2`, one coordinate (`Fin 1 → Fin 2`), the published
`BSCvsBEC.expectSubset` with `n = 1` (`S = {1}` with probability `λ`, `S = ∅` otherwise). Natural
logarithm (the inequality is base-invariant); for `g = 0` both sides are `0` in Lean, as the
inequality is trivially true there. The set contains `λ = 1` (`T_ρ` is an `α`-norm contraction) and
is bounded below by `0`, so `sInf` is the true infimum. -/
noncomputable def lamStarB (α ρ : ℝ) : ℝ :=
  sInf {lam : ℝ | 0 ≤ lam ∧ lam ≤ 1 ∧
    ∀ g : (Fin 1 → Fin 2) → ℝ, (∀ x, 0 ≤ g x) →
      Real.log (unifNorm α (noiseN ρ g)) ≤
        BSCvsBEC.expectSubset lam 1 (fun S => Real.log (unifNorm α (condExpS S g)))}

/-- `τ_α(θ) := 1 − λ*(α, 2, cos θ)` for `1 < α < ∞`, with `λ*` the sharp scalar constant of
Theorem 2.7: `lamStarA` for `α ≥ 2`, `lamStarB` for `1 < α < 2`.
Hązła–O'Donnell, manuscript of November 3, 2026 (sha256 a44ed926…), §4.3, p.22 ("For `1 < α < ∞`,
define `τ_α(θ) := 1 − λ*(α, 2, cos θ)`").

**Formalization Note.** `α` is real; the Rényi order passed to `lamStarA` is `ENNReal.ofReal α`. -/
noncomputable def tauBin (α θ : ℝ) : ℝ :=
  1 - (if 2 ≤ α then lamStarA (ENNReal.ofReal α) 2 (Real.cos θ) else lamStarB α (Real.cos θ))

/-- `τ_α(q, θ) := H_α(qSC_p)/log q` with `p = ((q − 1)/q)(1 − cos θ)`, for `2 ≤ α ≤ ∞`.
Hązła–O'Donnell, manuscript of November 3, 2026 (sha256 a44ed926…), §5, p.23 ("Write `ρ = cos θ` and
`p = ((q−1)/q)(1 − ρ)`, and define `τ_α(q, θ) := H_α(qSC_p)/log q`").

**Formalization Note.** Entropy and `log q` in bits; `α : ℝ≥0∞`, `α = ⊤` the min-entropy. -/
noncomputable def tauQ (α : ENNReal) (q : ℕ) (θ : ℝ) : ℝ :=
  renyiP α (qscRow q (qscP q (Real.cos θ))) / Real.logb 2 q

end BSCvsBEC.Supplement


