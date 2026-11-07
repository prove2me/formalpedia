-- Prove2me | Definitions.Def_BetheKS_outlierSpace
-- name    : BetheKS_outlierSpace
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:35:03.142434+00:00
-- url     : https://prove2.me/theorems/874e4d11-9e2d-4ffd-8c97-f08a0d02893d
-- title:
--   Planted spaces, outlier subspaces $E_{\mu,n}$ and their sum $E_n$
-- statement:
--   Let $\sigma:[n]\to[r]$ be the labels and $X_i(u)=\phi_i(\sigma(u))$. For an eigenvalue $\mu$ of $Q$, the **planted space** is
--   $$
--   \operatorname{span}\{X_i:\mu_i=\mu\}=\{\phi\circ\sigma:\ Q\phi=\mu\phi\}\subseteq\mathbb R^n .
--   $$
--   Given increasing orthonormal eigenbases $(v^+_j)$ of $H(\sqrt d,G)$ and $(v^-_j)$ of $H(-\sqrt d,G)$, the **outlier subspace** of a distinct informative eigenvalue $\mu$ is
--   $$
--   E_{\mu,n}=\begin{cases}\operatorname{span}\{v^+_i:\ i\in[r_+],\ \mu^+_i=\mu\}, & \mu>0,\\ \operatorname{span}\{v^-_j:\ j\in[r_-],\ \mu^-_j=\mu\}, & \mu<0,\end{cases}
--   $$
--   and $E_n$ is the sum of all of them, the span of the first $r_+$ eigenvectors of $H(\sqrt d,G)$ and the first $r_-$ of $H(-\sqrt d,G)$. For a simple informative $\mu$, its **unit outlier eigenvector** is the basis vector at the position of $\mu$. The file also defines the all-ones vector $\mathbf 1$.
--
--   **Formalization Note** The planted space is written basis-free, so no choice of eigenfunctions enters.
-- source:
--   Dong, McKenzie, Bethe Hessian Recovery through the Kesten–Stigum Regime, arXiv:2610.41802 (held version, sha256 4da41e16…), Theorem 2.2, p.5; App. F, p.26

import Mathlib
import Definitions.Def_BetheKS_SBMParams
import Definitions.Def_BetheKS_betheHessian

set_option autoImplicit false

namespace BetheKS

variable {r : ℕ}

/-- The planted space `span{Xᵢ : µᵢ = µ}` (Theorem 2.2, p.5), `Xᵢ(u) = ϕᵢ(σ(u))` (§2.3, p.4), in the
basis-free form `{ϕ ∘ σ : Q ϕ = µ ϕ}`.

**Formalization Note.** The `ϕᵢ` with `µᵢ = µ` form a basis of the eigenspace `ker(Q − µ)`, so their
pull-backs span exactly the vectors `ϕ ∘ σ` with `Q ϕ = µ ϕ`; no choice of eigenfunctions enters. -/
noncomputable def plantedSpace (p : SBMParams r) {n : ℕ} (σ : Fin n → Fin r) (μ : ℝ) :
    Submodule ℝ (EuclideanSpace ℝ (Fin n)) :=
  Submodule.span ℝ {x | ∃ ϕ : Fin r → ℝ, (signal p).mulVec ϕ = μ • ϕ ∧ x = WithLp.toLp 2 (ϕ ∘ σ)}

/-- **The outlier subspace `E_{µ,n}`** — Dong, McKenzie, arXiv:2610.41802 (held version, sha256
4da41e16…), Theorem 2.2, p.5: for a distinct informative eigenvalue `µ`, the span of the outlier
eigenvectors with indices `{i ∈ [r₊] : µᵢ⁺ = µ}` of `H(√d, Gₙ)` when `µ > 0`, or `{j ∈ [r₋] : µⱼ⁻ = µ}`
of `H(−√d, Gₙ)` when `µ < 0`, eigenvalues being ordered increasingly.

**Formalization Note.** `Bp`, `Bm` are increasing orthonormal eigenbases of `H(√d, G)` and
`H(−√d, G)`; index `j` (0-based) is the paper's `j + 1`. -/
noncomputable def outlierSpace (p : SBMParams r) {n : ℕ} {G : SimpleGraph (Fin n)}
    (Bp : IncEigenbasis (bh (Real.sqrt p.d) G)) (Bm : IncEigenbasis (bh (-Real.sqrt p.d) G))
    (μ : ℝ) : Submodule ℝ (EuclideanSpace ℝ (Fin n)) :=
  if 0 < μ then
    Submodule.span ℝ {x | ∃ j : Fin n, j.val < rplus p ∧ (posInf p).getD j.val 0 = μ ∧ x = Bp.vec j}
  else
    Submodule.span ℝ {x | ∃ j : Fin n, j.val < rminus p ∧ (negInf p).getD j.val 0 = μ ∧ x = Bm.vec j}

/-- `Eₙ`, the sum of all informative outlier subspaces of `H(√d, Gₙ)` and `H(−√d, Gₙ)`
(App. F, p.26): the span of the first `r₊` eigenvectors of `H(√d, Gₙ)` and the first `r₋`
eigenvectors of `H(−√d, Gₙ)`. -/
noncomputable def allOutliers (p : SBMParams r) {n : ℕ} {G : SimpleGraph (Fin n)}
    (Bp : IncEigenbasis (bh (Real.sqrt p.d) G)) (Bm : IncEigenbasis (bh (-Real.sqrt p.d) G)) :
    Submodule ℝ (EuclideanSpace ℝ (Fin n)) :=
  Submodule.span ℝ {x | ∃ j : Fin n, j.val < rplus p ∧ x = Bp.vec j} ⊔
    Submodule.span ℝ {x | ∃ j : Fin n, j.val < rminus p ∧ x = Bm.vec j}

/-- The all-ones vector `1 ∈ ℝⁿ`. -/
noncomputable def onesVec (n : ℕ) : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun _ => (1 : ℝ))

/-- The unit outlier eigenvector `v_{i,n}` of a simple informative eigenvalue `µ` (Theorem 2.2,
p.5): the eigenvector of `H(√d, G)` (if `µ > 0`) or `H(−√d, G)` (if `µ < 0`) at the position of `µ`
in the list `µ⁺` (resp. `µ⁻`). It is `0` if that position is not `< n`. -/
noncomputable def outlierVec (p : SBMParams r) {n : ℕ} {G : SimpleGraph (Fin n)}
    (Bp : IncEigenbasis (bh (Real.sqrt p.d) G)) (Bm : IncEigenbasis (bh (-Real.sqrt p.d) G))
    (μ : ℝ) : EuclideanSpace ℝ (Fin n) :=
  if 0 < μ then
    (if h : (posInf p).idxOf μ < n then Bp.vec ⟨(posInf p).idxOf μ, h⟩ else 0)
  else
    (if h : (negInf p).idxOf μ < n then Bm.vec ⟨(negInf p).idxOf μ, h⟩ else 0)

end BetheKS


