-- Prove2me | Definitions.Def_BSCvsBEC_expectSubset
-- name    : BSCvsBEC_expectSubset
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T08:29:35.280197+00:00
-- url     : https://prove2.me/theorems/95c92a4c-6688-48b2-9361-6fd6f89d3f8c
-- title:
--   Random-subset expectation $\mathbb E_{R\sim\lambda}$ and the marginal $P_{X_R}$
-- statement:
--   Fix $n$ and $\lambda\in[0,1]$. For a random subset $R\subseteq[n]$ that contains each coordinate independently with probability $\lambda$ ("$R\sim\lambda$"), the expectation of a function $F$ of subsets is
--   $$\mathbb E_{R\sim\lambda}F(R)=\sum_{R\subseteq[n]}\lambda^{|R|}(1-\lambda)^{n-|R|}F(R).$$
--
--   For a random variable $X\in\Omega^n$ with pmf $P$ and a set $R\subseteq[n]$ of coordinates, the **restriction** $X_R\in\Omega^R$ has pmf
--   $$P_{X_R}(u)=\sum_{x\,:\,x|_R=u}P(x),\qquad u\in\Omega^R.$$
--
--   These appear in the paper's tensorization lemma (Lemma 2.3) and in the entropy comparisons of §4, e.g. $\mathbb E_{R\sim\sin^2\theta}H(X_R)$.
--
--   **Formalization Note** Coordinates are `Fin n`; $\Omega^R$ is the type of functions on the elements of $R$. The weights use $0^0=1$, so $\lambda=0$ (resp. $1$) puts all mass on $R=\emptyset$ (resp. $R=[n]$).
-- source:
--   J. Hązła, R. O'Donnell, BSC vs. BEC vs. PSC, manuscript of November 3, 2026 (STOC 2027 submission, preprint basis, sha256 a44ed9262ff4e01c0cbd7e204728d4ad8bf4cfda8dbf126b96022d4c84b56186), §2.5, p.10 (notation S ∼ λ); §4, p.18 and Lemma 2.3, p.8 (X_R)

import Mathlib

namespace BSCvsBEC

/-- The expectation `E_{R∼λ} F(R)` over a random subset `R ⊆ [n]` that contains each coordinate
independently with probability `λ`:
`∑_{R ⊆ [n]} λ^{|R|} (1 − λ)^{n − |R|} F(R)`.
Hązła–O'Donnell, manuscript of November 3, 2026 (sha256 a44ed926…), §2.5, p.10: "for `0 ≤ λ ≤ 1`,
the notation `S ∼ λ` means that each coordinate is included in `S` independently with probability `λ`."

**Formalization Note.** Coordinates are `Fin n`; the weight uses `0⁰ = 1`, so `λ = 0` puts mass
`1` on `R = ∅` and `λ = 1` puts mass `1` on `R = [n]`. The natural-number subtraction
`n − |R|` is exact because `|R| ≤ n`. -/
noncomputable def expectSubset (lam : ℝ) (n : ℕ) (F : Finset (Fin n) → ℝ) : ℝ :=
  ∑ R : Finset (Fin n), lam ^ R.card * (1 - lam) ^ (n - R.card) * F R

/-- The marginal pmf of the restriction `X_R` of a random `X ∈ Ωⁿ` to the coordinates in `R`:
`P_{X_R}(u) = ∑_{x : x|_R = u} P_X(x)`.
Hązła–O'Donnell, manuscript of November 3, 2026 (sha256 a44ed926…), §4, p.18 (`H(X_R)`) and
Lemma 2.3, p.8.

**Formalization Note.** `X_R` takes values in `↥R → Ω` (functions on the coordinates of `R`). -/
noncomputable def margR {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {n : ℕ} (R : Finset (Fin n))
    (P : (Fin n → Ω) → ℝ) : (↥R → Ω) → ℝ :=
  fun u => ∑ x : Fin n → Ω, if (fun i : ↥R => x i) = u then P x else 0

end BSCvsBEC


