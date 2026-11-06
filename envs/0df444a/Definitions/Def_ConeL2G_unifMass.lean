-- Prove2me | Definitions.Def_ConeL2G_unifMass
-- name    : ConeL2G_unifMass
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:40:43.234741+00:00
-- url     : https://prove2.me/theorems/1a1a67cb-41cf-491c-9796-11d27e112b41
-- title:
--   The uniform distribution $\mu_H$ on proper list colorings
-- statement:
--   The uniform distribution $\mu_H=\mathrm{Unif}(\Omega_H)$ on proper list colorings, written as a mass function on all assignments:
--   $$\mu_H(x)=\begin{cases}1/|\Omega_H|,& x\in\Omega_H,\\ 0,&\text{otherwise.}\end{cases}$$
--
--   With $\mu=\mu_H$ the paper's inner product $\langle f,g\rangle_\mu=\mathbb E_{X\sim\mu}[f(X)g(X)]$ is `MarkovMixing.innerPi μ f g`; the single-site averaging operator $P_i f(x)=\mathbb E_\mu[f(X)\mid X_j=x_j\ \forall j\ne i]$, the single-site Laplacian $D_i=I-P_i$ and $D=\sum_i D_i$ are the reused operators `SpinGirth5.heatBath μ i`, `SpinGirth5.singleLap μ i` and `SpinGirth5.lapSum μ univ`.
--
--   **Formalization Note** $L^2(\mu)$ is realized as all real functions on assignments with $\mu$-weighted forms; values off $\Omega_H$ never enter a $\mu$-weighted sum. If $\Omega_H=\emptyset$ the mass is identically $0$.
-- source:
--   Li–Oveis Gharan, Local-to-Global Theorems Based on Cones with Applications to Graph Coloring, arXiv:2610.37721, Section 1, pp.1–2 and Section 2.1, p.7

import Mathlib
import Definitions.Def_ConeL2G_properColorings

namespace ConeL2G

/-- **The uniform distribution** `μ_H = Unif(Ω_H)` on proper list colorings, as a mass function
on all assignments `V → Fin K` (zero off `Ω_H`). Li–Oveis Gharan, arXiv:2610.37721, Section 1,
p.1 ("Let µ be the uniform distribution over all proper colorings") and Section 2.1, p.7
("`µ_H = Unif(Ω_H)`").

With `μ = unifMass H L`, the paper's inner product `⟨f, g⟩_µ = E_{X∼µ}[f(X)g(X)]` (p.2) is
`MarkovMixing.innerPi μ f g`, and `Pᵢ`, `Dᵢ = I − Pᵢ`, `D = Σᵢ Dᵢ` (p.2) are
`SpinGirth5.heatBath μ i`, `SpinGirth5.singleLap μ i`, `SpinGirth5.lapSum μ univ`.

**Formalization Note.** `L²(µ)` is realized as all real functions on `V → Fin K` with the
`μ`-weighted forms; values off `Ω_H` never enter a `μ`-weighted sum. If `Ω_H = ∅` the mass is
identically `0` (Lean's `1/0 = 0` is never reached, since the `if` fails). -/
noncomputable def unifMass {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] {K : ℕ} (L : V → Finset (Fin K)) (x : V → Fin K) : ℝ :=
  if x ∈ properColorings H L then 1 / ((properColorings H L).card : ℝ) else 0

end ConeL2G


