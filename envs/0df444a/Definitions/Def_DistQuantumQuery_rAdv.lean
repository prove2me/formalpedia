-- Prove2me | Definitions.Def_DistQuantumQuery_rAdv
-- name    : DistQuantumQuery_rAdv
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:15:57.049224+00:00
-- url     : https://prove2.me/theorems/ecd53960-4dba-4357-891d-135f06ba13d5
-- title:
--   Relaxed targets $\mathcal R^\mu_\delta(f)$ and relaxed adversary measure $\mathrm{rAdv}^\mu_\delta(f)$
-- statement:
--   Let $\Sigma\subseteq\{0,1\}^n$, $f:\Sigma\to\Omega$ a functional problem, $\mu$ a distribution and $\delta\in[0,1]$. The set of **relaxed targets** is
--   $$
--   \mathcal R^\mu_\delta(f):=\{\Psi\in\mathrm{Herm}(\Sigma):\ \Psi\circ A_f=A_f,\ \|\Psi\circ\Delta_f\circ|\mu\rangle\langle\mu|\|_{\mathrm{tr}}\le\delta\},
--   $$
--   and the **relaxed adversary measure** is
--   $$
--   \mathrm{rAdv}^\mu_\delta(f):=\min_{\Psi\in\mathcal R^\mu_\delta(f)}\bar\gamma^\mu_2(J-\Psi\mid\{\Delta_i\}).
--   $$
--   Relaxed targets need not be positive semidefinite; only their disagreement part, measured in trace norm, is constrained. The measure bounds distributional query complexity up to a quadratic loss in the error and underlies the Shaltiel-free measure.
--
--   **Formalization Note** The value is an infimum in $[0,\infty]$ (the set contains $A_f$; the paper's Lemma 6.2 shows the minimum is attained). The filters are the query filters of $\Sigma$.
-- source:
--   Ben-David, Ebtehaj, Distributional Quantum Query Complexity, arXiv:2610.06835 (held version, sha256 6334ffaf…), Definition 6.1 p.47

import Mathlib
import Definitions.Def_DistQuantumQuery_gammaBar

open scoped Matrix ENNReal

namespace DistQuantumQuery

/-- The set of **relaxed targets** `R^μ_δ(f) := {Ψ ∈ Herm(Σ) : Ψ ∘ A_f = A_f,
‖Ψ ∘ Δ_f ∘ |μ⟩⟨μ|‖_tr ≤ δ}` of a functional problem `f : Σ → Ω`
(Ben-David, Ebtehaj, *Distributional Quantum Query Complexity*, arXiv:2610.06835, held version,
sha256 6334ffaf…, Definition 6.1, p.47). -/
def relaxedTargets {X Ω : Type*} [Fintype X] [DecidableEq X] [DecidableEq Ω]
    (μ : X → ℝ) (f : X → Ω) (δ : ℝ) : Set (Matrix X X ℂ) :=
  {Ψ | Ψ.IsHermitian ∧ Ψ ⊙ agree f = agree f ∧ traceNorm (Ψ ⊙ disagree f ⊙ muMat μ) ≤ δ}

/-- The **relaxed adversary measure** (arXiv:2610.06835, held version, sha256 6334ffaf…,
Definition 6.1, p.47): for `Σ ⊆ {0,1}^n`, a functional problem `f : Σ → Ω`, a distribution `μ`
and `δ ∈ [0,1]`, `rAdv^μ_δ(f) := min_{Ψ ∈ R^μ_δ(f)} γ̄^μ₂(J − Ψ | {Δ_i})`.

**Formalization Note** Value in `ℝ≥0∞`, written as an infimum (the set contains `A_f`, so it is
never empty; Lemma 6.2 shows the minimum is attained). The filters are the query filters
`Δ_i` of the input set `Σ` (`qfilters`). -/
noncomputable def rAdv {ι Ω : Type*} [Fintype ι] [DecidableEq Ω]
    (S : Finset (ι → Bool)) (μ : S → ℝ) (f : S → Ω) (δ : ℝ) : ℝ≥0∞ :=
  ⨅ (Ψ : Matrix S S ℂ) (_ : Ψ ∈ relaxedTargets μ f δ), gammaBar μ (allOnes S - Ψ) (qfilters S)

end DistQuantumQuery


