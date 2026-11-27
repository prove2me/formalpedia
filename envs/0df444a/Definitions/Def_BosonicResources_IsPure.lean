-- Prove2me | Definitions.Def_BosonicResources_IsPure
-- name    : BosonicResources_IsPure
-- status  : Definition
-- author  : @Senrui Chen
-- created : 2026-11-27T05:17:04.684886+00:00
-- url     : https://prove2.me/theorems/bb51c0b1-942b-46a1-a89f-ea4e7f0e0d69
-- title:
--   Pure states (rank-one density operators)
-- statement:
--   A density operator $\rho$ on the Hilbert space $\ell^2(I)$ with orthonormal basis indexed by a set $I$ is called *pure* if it is a rank-one projector, that is, if there is a unit vector $\psi\in\ell^2(I)$ such that
--
--   $$
--   \rho=\lvert\psi\rangle\langle\psi\rvert ,\qquad\text{i.e.}\qquad \rho_{ij}=\psi_i\,\overline{\psi_j}\quad\text{for all }i,j\in I .
--   $$
--
--   For an $n$-mode bosonic system the index set is $I=\mathbb N^n$ (the Fock basis), and $\rho_{uv}=\langle u\rvert\rho\lvert v\rangle$ are the Fock matrix elements of $\rho$.
--
--   This is the purity promise of the paper: the hypothesis "even if $\rho$ is promised to be pure" of Theorem 3, "given the promise that $\rho$ is pure" of Theorem 5, and the purity assumption in Lemma 1, Lemma A.1 and Lemma B.3. For Gaussian states the paper also characterizes purity through the covariance matrix, $\det\Sigma=4^{-n}$.
--
--   **Formalization Note** This is the standard operator definition of purity: literally the predicate of the published subtype `Dependency50.P33.PureState` and the purity clause of the published set `OptGaussTomo.bosePure` (pure Gaussian states), so results stated with either transfer by unfolding. The paper's covariance criterion ($\det\Sigma=4^{-n}$ for a Gaussian state) is a theorem about Gaussian states, stated separately as `pure_iff_det`; it is not part of this definition.
-- source:
--   Chen, Mele, Fanizza, Li, Mann, Huang, Chen, Preskill, What resources are needed for optimal learning of bosonic Gaussian states?, https://arxiv.org/abs/2603.18136, Sec. 2 (pure Gaussian states); Sec. 3.2, Theorem 3; Sec. 3.3, Theorem 5

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33

open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsDensity traceSize rankOne)

namespace BosonicResources

/-- **Pure states.**
Chen, Mele, Fanizza, Li, Mann, Huang, Chen, Preskill, *What resources are needed for optimal learning of bosonic
Gaussian states?*, arXiv:2603.18136, §2 ("it corresponds to a pure Gaussian state if det Σ = 4^{-n}"), Theorem 3
("even if ρ is promised to be pure"), Theorem 5 ("given the promise that ρ is pure").

`IsPure ρ` says the density operator `ρ` on `ℓ²(I)` is a rank-one projector: `ρ = |ψ⟩⟨ψ|` for some unit vector
`ψ ∈ ℓ²(I)`, i.e. `ρ_{ij} = ψ_i · conj(ψ_j)`.

**Formalization Note.** This is the standard operator definition of purity: literally the predicate of the published
subtype `Dependency50.P33.PureState` and the purity clause of the published set `OptGaussTomo.bosePure` (pure
Gaussian states), so results stated with either transfer by unfolding. The paper's covariance criterion (`det Σ = 4^{-n}` for a Gaussian state) is a theorem
about Gaussian states, stated separately as `pure_iff_det`; it is not part of this definition. -/
def IsPure {I : Type} (ρ : State I) : Prop :=
  ∃ ψ : Hilbert I, ‖ψ‖ = 1 ∧ ρ.coefficients = rankOne ψ

end BosonicResources


