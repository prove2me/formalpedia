-- Prove2me | Definitions.Def_LowAccLTC_IsOneSidedLocalSpectral
-- name    : LowAccLTC_IsOneSidedLocalSpectral
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:37:20.010434+00:00
-- url     : https://prove2.me/theorems/3f6a6d52-dc10-4bd5-94bb-19c83d18feca
-- title:
--   $\lambda$-one-sided (local) spectral HDX, partite version
-- statement:
--   A weighted $r$-partite complex $(X,\mu)$ is a **$\lambda$-one-sided spectral HDX** if for every $0\le k\le r-2$ and every face $s\in X\langle k\rangle$ the underlying graph of the link $X_s$ — vertices of the top faces containing $s$ outside $s$, edges the pairs of such vertices in a common top face, with the measure induced by $\mu_s$ — is a $\lambda$-one-sided spectral expander: the second eigenvalue of its random-walk operator is at most $\lambda$.
--
--   This is assumption 1 of Theorem 4.1 (with $\lambda=r^{-2}$) and the conclusion of Fact 2.38 for KMS complexes.
--
--   **Formalization Note** $\lambda_2\le\lambda$ is written variationally: for every function $g$ with mean $0$ under the link's vertex law, $\mathbb E_{(u,v)}[g(u)g(v)]\le\lambda\,\mathbb E[g^2]$, the edge being an ordered pair of distinct vertices of $t\setminus s$ for $t\sim\mu_s$. This is equivalent to $\lambda_2\le\lambda$ because the operator is self-adjoint. The condition $\lambda\in[0,1]$ is not bundled.
-- source:
--   Ben Yaacov, Dikstein, Liu, Randomness-Efficient Robust LTCs in the Low-Acceptance Regime from HDXs (manuscript, sha256 04242e17…), Definition 2.7 p.15 (PDF p.18), Definition 2.16 p.17 (PDF p.20)

import Definitions.Def_LowAccLTC_PartiteComplex

namespace LowAccLTC

/-! Ben Yaacov, Dikstein, Liu, *Randomness-Efficient Robust LTCs in the Low-Acceptance Regime from HDXs*,
unpublished manuscript (sha256 04242e17…); page references are printed pages (PDF page − 3). -/

namespace PartiteComplex

variable {r : ℕ} {V T : Type*} [Fintype T] (X : PartiteComplex r V T)

/-- `X` is a `λ`-one-sided (local) spectral HDX (Definition 2.16, p.17, with Definition 2.7,
p.15): for every face `s` of size `k ≤ r - 2`, the underlying graph of the link `X_s`, with the
measure induced by `μ`, is a `λ`-one-sided spectral expander, i.e. `λ₂` of its random-walk
operator is at most `λ`.

The link's vertex law samples `t ∼ μ` conditioned on `s ⊆ t` and a uniformly random vertex of
`t ∖ s`; its (ordered) edge law samples `t` the same way and a uniformly random ordered pair of
distinct vertices of `t ∖ s`.

**Formalization Note.** `λ₂ ≤ λ` is written in its variational form: for every `g` with mean `0`
under the vertex law, `E_{(u,v)} g(u) g(v) ≤ λ · E_v g(v)²`. By self-adjointness of the random
walk operator in `ℓ²(vertex law)` and the Courant–Fischer theorem this is equivalent to
`λ₂ ≤ λ`. The condition `λ ∈ [0,1]` of Definition 2.16 is not bundled. -/
def IsOneSidedLocalSpectral (lam : ℝ) : Prop :=
  ∀ s, X.IsFace s → s.card + 2 ≤ r → ∀ g : V → ℝ,
    X.Estar s (fun t => avg (X.freeColors s t) (fun i => g (X.vert t i))) = 0 →
    X.Estar s (fun t => avg (X.freePairs s t) (fun ij => g (X.vert t ij.1) * g (X.vert t ij.2)))
      ≤ lam * X.Estar s (fun t => avg (X.freeColors s t) (fun i => g (X.vert t i) ^ 2))

end PartiteComplex

end LowAccLTC


