-- Prove2me | Definitions.Def_SchmidtKPos_IsKPositive
-- name    : SchmidtKPos_IsKPositive
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:50:33.000345+00:00
-- url     : https://prove2.me/theorems/53c53200-41db-4540-87cb-84cdf5c48680
-- title:
--   $k$-positive linear map in the sense of Definition 2
-- statement:
--   A linear map $\Lambda:\mathcal M_n(\mathbb C)\to\mathcal M_m(\mathbb C)$ is **$k$-positive** if it preserves Hermiticity and
--
--   $$
--   (\mathbf 1\otimes\Lambda)(|\psi\rangle\langle\psi|)\ge 0
--   \qquad\text{for all } |\psi\rangle\langle\psi|\in S_k .
--   $$
--
--   Here $\mathbf 1$ is the identity on the first factor $\mathcal M_n(\mathbb C)$. This is the class of maps that witnesses the Schmidt number, in the same way that positive maps witness entanglement.
--
--   **Formalization Note** This is Definition 2 of the paper, not the textbook positivity of $\mathrm{id}_{M_k}\otimes\Lambda$: Hermiticity preservation is part of the definition and the identity acts on $\mathcal H_n$. Membership of $|\psi\rangle\langle\psi|$ in $S_k$ forces $\|\psi\|=1$. At $k=0$ the set $S_0$ is empty and the condition reduces to Hermiticity preservation.
-- source:
--   B. M. Terhal, P. Horodecki, A Schmidt number for density matrices, arXiv:quant-ph/9911117v4, Definition 2, Eq. (2), p. 2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_SchmidtKPos_schmidtClass
open scoped Matrix ComplexConjugate ComplexOrder

namespace SchmidtKPos

open QAlgorithms.Papers.Independent.Dependency50.P50 (PreservesHermiticity)

/-- B. M. Terhal, P. Horodecki, *A Schmidt number for density matrices*,
arXiv:quant-ph/9911117v4, Definition 2, Eq. (2), p.2: the linear Hermiticity-preserving map `Λ` is
`k`-positive iff `(1 ⊗ Λ)(|ψ⟩⟨ψ|) ≥ 0` for all `|ψ⟩⟨ψ| ∈ S_k`.

**Formalization Note.** This is Definition 2 itself, not the textbook positivity of
`id_{M_k} ⊗ Λ`: Hermiticity preservation is part of the definition, and the identity acts on
`H_n`, the dimension of `Λ`'s input (the space on which `S_k` lives). `Λ : M_n → M_m` may change the
dimension, as on p.2 ("`Λ_n : M_n(C) → M_m(C)`"). The membership `|ψ⟩⟨ψ| ∈ S_k` forces `‖ψ‖ = 1`. At
`k = 0`, `S_0 = ∅` and the condition is Hermiticity preservation alone.
`QAlgorithms.idTensorSuperop` puts the identity on the first tensor factor. -/
def IsKPositive (k : ℕ) {n m : ℕ}
    (Λ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ) : Prop :=
  PreservesHermiticity Λ ∧
    ∀ ψ : EuclideanSpace ℂ (Fin n × Fin n), QAlgorithms.pureDensity ψ ∈ schmidtClass n k →
      (QAlgorithms.idTensorSuperop (R := Fin n) (⇑Λ) (QAlgorithms.pureDensity ψ)).PosSemidef

end SchmidtKPos


