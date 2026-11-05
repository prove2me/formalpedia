-- Prove2me | Definitions.Def_RouzeFranca_LearnGibbs_lipBox
-- name    : RouzeFranca_LearnGibbs_lipBox
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:46:36.996322+00:00
-- url     : https://prove2.me/theorems/f46a62bb-07ac-40f9-b081-5eb9d56ebc02
-- title:
--   The quantum Hamming Lipschitz constant $\|O\|_{\mathrm{Lip},\square}$
-- statement:
--   For an observable $O$ on $n$ qubits,
--   $$
--   \|O\|_{\mathrm{Lip},\square}=\sqrt n\,\max_{1\le i\le n}\ \max_{\substack{\rho,\sigma\in\mathcal D_{2^n}\\ \operatorname{tr}_i[\rho]=\operatorname{tr}_i[\sigma]}}\operatorname{tr}[O(\rho-\sigma)],
--   $$
--   where $\mathcal D_{2^n}$ is the set of states and $\operatorname{tr}_i$ is the partial trace over qubit $i$. It measures how much the expectation value of $O$ can change between two states that agree away from one site.
--
--   It is one of the two Lipschitz constants for which the main theorem is stated; it satisfies the nonnegativity and absolute homogeneity used there.
--
--   **Formalization Note** The partial trace is represented by the matrix $x,y\mapsto\sum_{b}\rho_{x[i\mapsto b],\,y[i\mapsto b]}$, which equals $\operatorname{tr}_i[\rho]\otimes I_i$ up to the order of tensor factors. The inner maximum is a real supremum over a set that is nonempty and bounded by $2\|O\|_\infty$; the outer maximum is a real supremum over the $n$ sites (it is $0$ when $n=0$, a case the paper does not consider). Traces are recorded by their real parts.
-- source:
--   Rouzé, Stilck França, Learning quantum many-body systems from a few copies, arXiv:2107.03333v4, Eq. (34), p. 21

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_RouzeFranca_LearnGibbs_gibbs

open Matrix

namespace RouzeFranca.LearnGibbs

/-- The partial trace over qubit `i`, padded back to an `n`-qubit operator:
`(ptraceSite i ρ) x y = ∑_{b} ρ (x[i ↦ b]) (y[i ↦ b])`. It equals `tr_i[ρ] ⊗ I_i` up to the
ordering of tensor factors, so `ptraceSite i ρ = ptraceSite i σ` iff `tr_i[ρ] = tr_i[σ]`.

Rouzé, Stilck França, arXiv:2107.03333v4, Eq. (34), p. 21 (`tr_i[ρ] = tr_i[σ]`). -/
def ptraceSite {n : ℕ} (i : Fin n) (ρ : Mat n) : Mat n :=
  fun x y => ∑ b : Bool, ρ (Function.update x i b) (Function.update y i b)

/-- The quantum Hamming Lipschitz constant
`‖O‖_Lip,□ = √n max_{1≤i≤n} max_{ρ,σ ∈ D_{2^n}, tr_i[ρ]=tr_i[σ]} tr[O(ρ − σ)]`.

Rouzé, Stilck França, arXiv:2107.03333v4, Eq. (34), p. 21.

**Formalization Note.** The inner maximum is a real `sSup` over a set that is nonempty (`ρ = σ`
gives `0`) and bounded above by `2‖O‖∞`, so it is the paper's maximum; the outer maximum over the
`n` sites is a real `⨆` over `Fin n` (it is `0` for `n = 0`, a case the paper does not consider).
The trace is recorded by its real part. The mission's theorems are stated for every Lipschitz
constant satisfying `IsLipSeminorm`, which this one does. -/
noncomputable def lipBox {n : ℕ} (O : Mat n) : ℝ :=
  Real.sqrt n * ⨆ i : Fin n, sSup {t : ℝ | ∃ ρ σ : Mat n, WildeQIT.IsDensityOperator ρ ∧
    WildeQIT.IsDensityOperator σ ∧ ptraceSite i ρ = ptraceSite i σ ∧
    t = (trace (O * (ρ - σ))).re}

end RouzeFranca.LearnGibbs


