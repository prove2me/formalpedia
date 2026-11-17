-- Prove2me | Definitions.Def_ArgmaxDeFinetti_Supplement_marginal
-- name    : ArgmaxDeFinetti_Supplement_marginal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:38:51.200506+00:00
-- url     : https://prove2.me/theorems/b884b273-62c1-4cdd-ab91-251595559bb3
-- title:
--   The $t$-site marginal $\rho^{(t)}_N=\mathrm{Tr}_{t+1,\dots,N}\,\rho_N$
-- statement:
--   For a finite site space $\mathbb C^\iota$ and an operator $\rho_N$ on $(\mathbb C^\iota)^{\otimes N}$, the **marginal on the first $t$ sites** is the partial trace over sites $t+1,\dots,N$:
--
--   $$
--   \rho^{(t)}_N=\mathrm{Tr}_{t+1,\dots,N}\,\rho_N,\qquad \rho^{(t)}_N(a,b)=\sum_{c}\rho_N\big((a,c),(b,c)\big),
--   $$
--
--   where $a,b$ range over the indices of the first $t$ sites and $c$ over the indices of the remaining $N-t$ sites.
--
--   This is the reduced state that every $t$-site de Finetti theorem of the paper compares with a separable family; for $t=2$ and $\iota=\{1,\dots,d\}$ it is the base mission's two-site marginal.
--
--   **Formalization Note** Operators are matrices indexed by tensor indices $\mathrm{Fin}\,N\to\iota$. The definition is used only for $t\le N$, where it is the partial trace. The site type $\iota$ is general so that a composite site $\mathbb C^r\otimes\mathbb C^r$ can be used (Appendix B).
-- source:
--   Jeronimo, Wu, Xu, Optimal Quantum de Finetti Theorems via Argmax Rounding, arXiv:2608.02590 (held version, sha256 fb339472…), §2.1 "Bosonic states", p.19

import Mathlib

open Matrix

namespace ArgmaxDeFinetti

namespace Supplement

/-- The tensor index of `N` sites obtained by putting the indices `a` of the first `t` sites before the
indices `c` of the remaining `N − t` sites: site `k < t` reads `a k`, site `k ≥ t` reads `c (k − t)`.

**Formalization Note** Helper for the partial trace `marginal`; for `t ≤ N` the map `(a, c) ↦ joinIdx a c` is a
bijection `(Fin t → ι) × (Fin (N − t) → ι) ≃ (Fin N → ι)`. -/
def joinIdx {ι : Type} {N t : ℕ} (a : Fin t → ι) (c : Fin (N - t) → ι) : Fin N → ι :=
  fun k => if h : (k : ℕ) < t then a ⟨k, h⟩ else c ⟨(k : ℕ) - t, by have := k.2; omega⟩

/-- The marginal on the first `t` sites, `ρ^{(t)}_N = Tr_{t+1,…,N} ρ_N`, of an operator on `N` sites with site
space `ℂ^ι`, Jeronimo, Wu, Xu, *Optimal Quantum de Finetti Theorems via Argmax Rounding*, arXiv:2608.02590 (held version, sha256 fb339472…), §2.1 "Bosonic states", p.19 ("Its marginal on the first t sites is
ρ^{(t)}_N := Tr_{t+1,...,N} ρ_N").

**Formalization Note** Operators on `(ℂ^ι)^{⊗N}` are matrices indexed by tensor indices `Fin N → ι`; the
partial trace sums the diagonal over the indices of sites `t+1, …, N` (0-based: `t, …, N − 1`). The paper uses it
only for `t ≤ N`; every statement of the mission assumes `t ≤ N`, where this is the partial trace. For `t = 2`
and `ι = Fin d` it is the base mission's `marginal2`. The site type `ι` is general so that a composite site
`ℂ^r ⊗ ℂ^r` can be `ι = Fin r × Fin r` (Appendix B). -/
def marginal {ι : Type} [Fintype ι] {N : ℕ} (t : ℕ) (ρ : Matrix (Fin N → ι) (Fin N → ι) ℂ) :
    Matrix (Fin t → ι) (Fin t → ι) ℂ :=
  fun a b => ∑ c : Fin (N - t) → ι, ρ (joinIdx a c) (joinIdx b c)

end Supplement

end ArgmaxDeFinetti


