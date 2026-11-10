-- Prove2me | Definitions.Def_KnownFidelity_Rank_Lmat
-- name    : KnownFidelity_Rank_Lmat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:45:51.070827+00:00
-- url     : https://prove2.me/theorems/54ef2fe0-e6bc-40f0-a9ce-07c196fc0832
-- title:
--   The contraction $L=\sqrt\ell\,\sigma_J^{-1/2}$ of §4.1
-- statement:
--   Let $\sigma=U\,\mathrm{diag}(\lambda)\,U^*$ be the reference, let $J$ be a set of $j$ eigenvectors (the columns $Ue_{J(i)}$) and let $\ell=\min_i\lambda_{J(i)}>0$. Identifying $\mathbb C^j$ with the span of $J$, $\sigma_J=P_J\sigma P_J=\mathrm{diag}(\lambda_{J(i)})$ and
--
--   $$L=\sqrt\ell\,\sigma_J^{-1/2}=\mathrm{diag}\Big(\frac{\sqrt\ell}{\sqrt{\lambda_{J(i)}}}\Big),$$
--
--   with the inverse taken on $J$. Since every $\lambda_{J(i)}\ge\ell$, $L^*L\preceq I_J$.
--
--   **Formalization Note** $\ell$ is a parameter; the statements that use $L$ assume it is the least $\lambda_{J(i)}$ and positive.
-- source:
--   Lee, Jo, Fidelity Estimation to a Known Quantum State Is Nearly Quadratic in the Smaller Rank, arXiv:2608.01770, §4.1 (unnumbered), p. 8 (PDF p. 10)

import Mathlib

namespace KnownFidelity.Rank

/-- **The contraction `L = √ℓ σ_J^{−1/2}` of §4.1.**
Lee, Jo, *Fidelity Estimation to a Known Quantum State Is Nearly Quadratic in the Smaller Rank*,
arXiv:2608.01770, §4.1 (unnumbered), printed p. 8 (PDF p. 10): "Let J be a set of j eigenvectors
of σ, let P_J be its projector, and put σ_J = P_J σ P_J and ℓ = λ_min(σ_J) > 0. … Identify C^j
with J and set L = √ℓ σ_J^{−1/2} … The inverse is taken on J."

The reference is `σ = U diag(λ) U*`; `J : Fin j ↪ Fin d` selects `j` eigenvectors (the columns
`U e_{J i}`), and in that basis of `ℂ^j`, `σ_J = diag(λ_{J i})`. Hence
`Lmat lam J ℓ = diag(√ℓ / √λ_{J i})`.

**Formalization Note.** `ℓ` is a parameter; the statements that use `Lmat` assume that `ℓ` is the
least of the `λ_{J i}` and is positive, so every `λ_{J i} > 0` and `L* L ⪯ I`. -/
noncomputable def Lmat {d j : ℕ} (lam : Fin d → ℝ) (J : Fin j ↪ Fin d) (ℓ : ℝ) :
    Matrix (Fin j) (Fin j) ℂ :=
  Matrix.diagonal fun i => ((Real.sqrt ℓ / Real.sqrt (lam (J i)) : ℝ) : ℂ)

end KnownFidelity.Rank


