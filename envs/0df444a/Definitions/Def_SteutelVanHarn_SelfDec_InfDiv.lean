-- Prove2me | Definitions.Def_SteutelVanHarn_SelfDec_InfDiv
-- name    : SteutelVanHarn_SelfDec_InfDiv
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T06:49:24.902402+00:00
-- url     : https://prove2.me/theorems/df7c42fa-6909-4a4b-98bd-b506d09d52ca
-- title:
--   Infinite divisibility on $\mathbb N_0$, the canonical sequence $r_n$ of (1.5), and the forms (1.3), (1.4)
-- statement:
--   Let $(p_n)$ be a distribution on $\mathbb N_0$ with p.g.f. $P$.
--
--   1. $(p_n)$ is **infinitely divisible** if for every integer $n\ge1$ there is a distribution on $\mathbb N_0$ whose p.g.f. $P_n$ satisfies $P_n(z)^n=P(z)$.
--   2. If $p_0>0$, the **canonical sequence** $(r_n)_{n\ge0}$ of $(p_n)$ is the unique real sequence with
--   $$
--   (n+1)\,p_{n+1}=\sum_{k=0}^{n}p_k\,r_{n-k}\qquad(n\in\mathbb N_0),\tag{1.5}
--   $$
--   that is, $r_n=\big((n+1)p_{n+1}-\sum_{k=1}^{n}p_k r_{n-k}\big)/p_0$. The paper calls it the canonical measure of $P$.
--   3. $P$ has the **form (1.3)** with parameters $\lambda$ and $(g_n)$ if $\lambda>0$, $(g_n)$ is a distribution on $\mathbb N_0$ with $g_0=0$, and
--   $$
--   P(z)=\exp\{\lambda(G(z)-1)\}\qquad(0\le z\le 1).
--   $$
--   4. $P$ has the **form (1.4)** with the sequence $(r_n)$ if $r_n\ge0$ for all $n$, the series $R(u)=\sum_{n\ge0}r_nu^n$ converges for $0\le u<1$, and for every $0\le z<1$ the integral $\int_z^1R(u)\,du$ is finite and
--   $$
--   P(z)=\exp\Big\{-\int_z^1R(u)\,du\Big\}.
--   $$
--
--   Lemma 1.2 of the paper says that, for $0<p_0<1$, infinite divisibility is equivalent to each of the forms (1.3) and (1.4), and to the nonnegativity of the canonical sequence.
--
--   **Formalization Note** Infinite divisibility follows Feller (vol. 1, XII.2); the paper uses it without defining it. The identity $P_n^n=P$ is required for real $z\in[0,1]$, which suffices because p.g.f.'s agreeing on $[0,1]$ have equal coefficients. The canonical sequence is defined by the recursion and only meaningful for $p_0\neq0$ (Lean's division by zero makes it $0$ when $p_0=0$); every statement using it assumes $p_0>0$. In (1.4) the convergence of $R$ and the integrability of $R$ on $(z,1)$ are stated explicitly, because Lean's `tsum` and integral return $0$ on divergent input.
-- source:
--   Steutel & van Harn, Discrete analogues of self-decomposability and stability, Memorandum COSOR 78-07, TH Eindhoven (1978), p. 1, §1 (inf div, refs [1], [6]); p. 2, Lemma 1.2, (1.3), (1.4), (1.5)

import Definitions.Def_SteutelVanHarn_SelfDec_PGF

namespace SteutelVanHarn.SelfDec

/-- Infinite divisibility of a distribution on `ℕ₀` (used in §1, p. 1, with reference to Feller,
vol. 1, XII.2): for every `n ≥ 1` there is a distribution `q` on `ℕ₀` whose p.g.f. `Q` satisfies
`Q ^ n = P`.

Formalization Note: the identity of p.g.f.'s is required on the real interval `[0, 1]`; two
p.g.f.'s that agree there are analytic in the open unit disc and agree on `|z| ≤ 1`. -/
def IsInfDiv (p : ℕ → ℝ) : Prop :=
  IsDistribution p ∧
    ∀ n : ℕ, 0 < n → ∃ q : ℕ → ℝ, IsDistribution q ∧
      ∀ z ∈ Set.Icc (0 : ℝ) 1, pgf q z ^ n = pgf p z

/-- The canonical sequence `r_n` of `p` (Lemma 1.2, (1.5), p. 2): the unique solution of
`(n + 1) p_{n+1} = ∑_{k=0}^{n} p_k r_{n-k}` (`n ∈ ℕ₀`), computed by the recursion
`r_n = ((n + 1) p_{n+1} - ∑_{k=1}^{n} p_k r_{n-k}) / p_0`.

Formalization Note: meaningful only when `p 0 ≠ 0`; every statement using it assumes `0 < p 0`
(at `p 0 = 0` Lean's division by zero makes it `0`). In the sum, `k : Fin n` stands for the
paper's index `k + 1 ∈ {1, …, n}`. -/
noncomputable def canonicalSeq (p : ℕ → ℝ) : ℕ → ℝ
  | n => ((n + 1 : ℝ) * p (n + 1) -
      ∑ k : Fin n, p (k + 1) * canonicalSeq p (n - 1 - k)) / p 0
decreasing_by have := k.isLt; omega

/-- The compound-Poisson form (1.3) of Lemma 1.2 (p. 2): `λ > 0`, `g` is a distribution on `ℕ₀`
with `g 0 = 0`, and `P(z) = exp{λ (G(z) - 1)}` for `z ∈ [0, 1]`. -/
def HasForm13 (p : ℕ → ℝ) (lam : ℝ) (g : ℕ → ℝ) : Prop :=
  0 < lam ∧ IsDistribution g ∧ g 0 = 0 ∧
    ∀ z ∈ Set.Icc (0 : ℝ) 1, pgf p z = Real.exp (lam * (pgf g z - 1))

/-- The form (1.4) of Lemma 1.2 (p. 2): `r n ≥ 0`, `R(u) = ∑ r n u ^ n` converges on `[0, 1)`,
and `P(z) = exp{-∫_z^1 R(u) du}` for `z ∈ [0, 1)`, the integral being finite.

Formalization Note: the convergence of `R` and the integrability of `R` on `(z, 1)` are stated
explicitly, because Lean's `tsum` and integral return `0` on divergent input. -/
def HasForm14 (p : ℕ → ℝ) (r : ℕ → ℝ) : Prop :=
  (∀ n, 0 ≤ r n) ∧
    (∀ u ∈ Set.Ico (0 : ℝ) 1, Summable (fun n => r n * u ^ n)) ∧
    ∀ z ∈ Set.Ico (0 : ℝ) 1,
      MeasureTheory.IntegrableOn (fun u => ∑' n, r n * u ^ n) (Set.Ioo z 1) ∧
      pgf p z = Real.exp (-∫ u in z..1, ∑' n, r n * u ^ n)

end SteutelVanHarn.SelfDec


