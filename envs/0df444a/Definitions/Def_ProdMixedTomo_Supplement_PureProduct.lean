-- Prove2me | Definitions.Def_ProdMixedTomo_Supplement_PureProduct
-- name    : ProdMixedTomo_Supplement_PureProduct
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T22:30:03.301211+00:00
-- url     : https://prove2.me/theorems/d8f5246c-2a83-4af2-84fd-ec35f8d33be7
-- title:
--   Pure product states $\Pi_n$ and the benchmark $\mathrm{opt}(\Pi_n)$
-- statement:
--   A one-qubit pure state $|\pi_j\rangle$ has density matrix $|\pi_j\rangle\langle\pi_j|=\tfrac12(I+c_j\cdot\sigma)$ with a Bloch vector $c_j\in\mathbb R^3$ of unit length, $\|c_j\|=1$, where $c\cdot\sigma=c_0X+c_1Y+c_2Z$. The set of **pure product states** on $n$ qubits is
--   $$
--   \Pi_n=\Bigl\{\,|\pi\rangle\langle\pi|=\bigotimes_{j=1}^n\tfrac12(I+c_j\cdot\sigma)\ :\ \|c_j\|=1\text{ for every }j\Bigr\},
--   $$
--   and the agnostic benchmark of an $n$-qubit density matrix $\rho$ with respect to it is
--   $$
--   \mathrm{opt}(\Pi_n)(\rho)=\inf_{|\pi\rangle\in\Pi_n} d_{\mathrm{tr}}\bigl(|\pi\rangle\langle\pi|,\rho\bigr).
--   $$
--   Since $\Pi_n\subseteq\mathcal M_n$, this is at least the benchmark $\mathrm{opt}(\rho)$ over product mixed states.
--
--   These are the hypothesis class and the error benchmark of the pure-state tomography result, Theorem 3.6.
--
--   **Formalization Note** The tensor product is the entrywise product `prodMat` of the base mission, and $\|c_j\|=1$ is written $c_{j,0}^2+c_{j,1}^2+c_{j,2}^2=1$. The infimum is taken over a nonempty set of reals bounded below by $0$.
-- source:
--   Arulandu, Diakonikolas, Kane, Li, Agnostic Product Mixed State Tomography via Robust Statistics, arXiv:2510.08472 (manuscript of Nov. 3, 2026, sha256 6c87a7ba…), §3.3 and Theorem 3.6, p.19 (PDF p.21)

import Mathlib
import Definitions.Def_ProdMixedTomo_States
import Definitions.Def_ProdMixedTomo_TraceDistance

namespace ProdMixedTomo.Supplement

/-- `Π_n`, the pure product states on `n` qubits: the matrices `|π⟩⟨π|` with
`|π⟩ = |π₁⟩ ⊗ ⋯ ⊗ |πₙ⟩`, i.e. `⨂ⱼ ½(I + cⱼ·σ)` with every Bloch vector `cⱼ ∈ ℝ³` of unit length.

Arulandu, Diakonikolas, Kane, Li, *Agnostic Product Mixed State Tomography via Robust Statistics*,
arXiv:2510.08472 (manuscript of Nov. 3, 2026, sha256 6c87a7ba…), §3.3 and Theorem 3.6, p.19 (PDF p.21): "Recall we let Π_n denote the set of pure product
states"; proof of Theorem 3.6: "|π_j⟩⟨π_j| = ½(I_j + c_j·σ_j) … Since |π_j⟩ is a pure state,
‖c_j‖ = 1".

**Formalization Note.** A one-qubit rank-one projector is exactly `½(I + c·σ)` with `‖c‖ = 1`
(`qubitOf c` of the base `ProdMixedTomo.States`); the tensor product is the base `prodMat`.
The unit-length condition is written `c₀² + c₁² + c₂² = 1`. -/
def PureProduct (n : ℕ) : Set (QMat n) :=
  {σ | ∃ c : Fin n → Fin 3 → ℝ, (∀ j, ∑ k, c j k ^ 2 = 1) ∧ σ = prodMat fun j => qubitOf (c j)}

/-- `opt(Π_n)(ρ) = inf_{|π⟩ ∈ Π_n} d_tr(|π⟩⟨π|, ρ)`, the trace distance from `ρ` to the nearest
pure product state (Theorem 3.6, p.19, PDF p.21).

**Formalization Note.** The infimum of a nonempty set of reals bounded below by `0`. It is at least
the base `optM ρ` (the infimum over the larger set `M_n`). -/
noncomputable def optPure {n : ℕ} (ρ : QMat n) : ℝ :=
  sInf ((fun σ => dtr σ ρ) '' PureProduct n)

end ProdMixedTomo.Supplement


