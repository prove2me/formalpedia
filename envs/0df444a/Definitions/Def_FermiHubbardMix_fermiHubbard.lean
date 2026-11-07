-- Prove2me | Definitions.Def_FermiHubbardMix_fermiHubbard
-- name    : FermiHubbardMix_fermiHubbard
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:34:20.588351+00:00
-- url     : https://prove2.me/theorems/79d8d882-467b-4d58-9f8b-ebc179c91165
-- title:
--   Spin-$\tfrac12$ Fermi–Hubbard Hamiltonian $H_{\mathrm{FH}}$ and $t_{\max}$
-- statement:
--   Take $m=2$ modes per site, labeled $\uparrow,\downarrow$, with $n_{i,\sigma}=c^\dagger_{i,\sigma}c_{i,\sigma}$. Let $E$ be the edge set of a simple graph on $\Lambda$, with real hopping amplitudes $t_{ij}$, onsite interactions $U_i$ and chemical potentials $\mu_i$. The **spin-$\tfrac12$ Fermi–Hubbard Hamiltonian** $H_{\mathrm{FH}}=V+W$ (Example 11.8) has
--   $$
--   v_i=U_i\,n_{i,\uparrow}n_{i,\downarrow}+\mu_i\,(n_{i,\uparrow}+n_{i,\downarrow}),\qquad
--   w_{\{i,j\}}=-\sum_{\sigma\in\{\uparrow,\downarrow\}}t_{ij}\bigl(c^\dagger_{i,\sigma}c_{j,\sigma}+c^\dagger_{j,\sigma}c_{i,\sigma}\bigr)\quad(\{i,j\}\in E),
--   $$
--   and $w_Z=0$ for all other $Z$. Its largest hopping amplitude is $t_{\max}=\max_{\{i,j\}\in E}|t_{ij}|$.
--
--   This is the model of the mission's goal (Corollary 15.2).
--
--   **Formalization Note** Spin $\uparrow$ is mode $0$ and $\downarrow$ mode $1$ of each site. The amplitudes are one real number per unordered pair (only edges are used, and $t_{ij}=0$ is allowed); $t_{\max}$ is a supremum over the edges ($0$ without edges). The hopping operator $\sum_\sigma(c^\dagger_{i,\sigma}c_{j,\sigma}+c^\dagger_{j,\sigma}c_{i,\sigma})$ is also named (`hopOp`).
-- source:
--   Bakshi, Moitra, Tan, Algorithmic Aspects of the Fermi–Hubbard Model, arXiv:2604.08408 (held version, sha256 055b8f8f…), Example 11.8, p.52; Corollary 15.2, p.68

import Mathlib
import Definitions.Def_FermiHubbardMix_HamData
open scoped BigOperators
open Matrix
noncomputable section

namespace FermiHubbardMix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- The hopping operator `∑_{σ ∈ {↑,↓}} (c†_{i,σ} c_{j,σ} + c†_{j,σ} c_{i,σ})` between sites `i` and `j`
(arXiv:2604.08408, held version sha256 055b8f8f…, Example 11.8, p.52).

**Formalization Note** Spin `↑` is mode `0` and spin `↓` is mode `1` of `Fin 2`. -/
def hopOp (ord : Λ × Fin 2 ≃ Fin N) (i j : Λ) : Op N :=
  ∑ σ : Fin 2, ((GaussTesting.annihilator N (ord (i, σ)))ᴴ * GaussTesting.annihilator N (ord (j, σ)) +
    (GaussTesting.annihilator N (ord (j, σ)))ᴴ * GaussTesting.annihilator N (ord (i, σ)))

open scoped Classical in
/-- **Example 11.8 (Spin-1/2 Fermi–Hubbard Hamiltonian)** (arXiv:2604.08408, held version sha256
055b8f8f…, p.52): `v_i = U_i n_{i,↑} n_{i,↓} + µ_i (n_{i,↑} + n_{i,↓})`,
`w_{{i,j}} = -t_{ij} ∑_σ (c†_{i,σ} c_{j,σ} + c†_{j,σ} c_{i,σ})` for `{i,j} ∈ E`, and `w_Z = 0` otherwise.

**Formalization Note** The edge set `E` is a simple graph `G` on `Λ`; the hopping amplitudes are one
real number `t e` per unordered pair `e : Sym2 Λ` (only edges are used; `t_{ij} = t_{ji}` because
`w_{{i,j}}` is symmetric in `i, j`), and `t e = 0` is allowed. Spin `↑` is mode `0`, `↓` is mode `1`.
For a two-element set `Z = {i, j}` that is an edge, the sum over ordered pairs of distinct elements
of `Z` is `t_{ij} (c†_{i,σ} c_{j,σ} + c†_{j,σ} c_{i,σ})`; every other `Z` gets `w_Z = 0`. -/
def fhHam (ord : Λ × Fin 2 ≃ Fin N) (G : SimpleGraph Λ) [DecidableRel G.Adj] (t : Sym2 Λ → ℝ)
    (U μ : Λ → ℝ) : HamData Λ N where
  v i := (U i : ℂ) • (numOp N (ord (i, 0)) * numOp N (ord (i, 1))) +
    (μ i : ℂ) • (numOp N (ord (i, 0)) + numOp N (ord (i, 1)))
  w Z := if Z.card = 2 ∧ ∀ i ∈ Z, ∀ j ∈ Z, i ≠ j → G.Adj i j then
      -∑ σ : Fin 2, ∑ i ∈ Z, ∑ j ∈ Z,
        if i ≠ j then (t s(i, j) : ℂ) • ((GaussTesting.annihilator N (ord (i, σ)))ᴴ * GaussTesting.annihilator N (ord (j, σ))) else 0
    else 0

/-- `t_max = max_{{i,j} ∈ E} |t_{ij}|` (arXiv:2604.08408, held version sha256 055b8f8f…,
Corollary 15.2, p.68).

**Formalization Note** The maximum over the finite edge set is a supremum (it is `0` when `G` has
no edges; Corollary 15.2 assumes `t_max > 0`). -/
def tmax (G : SimpleGraph Λ) [DecidableRel G.Adj] (t : Sym2 Λ → ℝ) : ℝ :=
  ⨆ e : G.edgeFinset, |t e|

end FermiHubbardMix


