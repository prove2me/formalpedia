-- Prove2me | Definitions.Def_DattaDiscord_dilated
-- name    : DattaDiscord_dilated
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:21:01.501626+00:00
-- url     : https://prove2.me/theorems/5859ee22-cfe4-4c8a-b61e-f2f099ebaf06
-- title:
--   The dilated state $\rho'_{ABC}$ of Eq. (3)
-- statement:
--   Let $\{|e_j\rangle\}$ be an orthonormal basis of $\mathcal H_B$, and let $C$ be a copy of $B$ with standard basis $\{|f_j\rangle\}$. Measuring $B$ in $\{|e_j\rangle\}$ through a unitary interaction with $C$, $U|e_j\rangle\otimes|0\rangle=|e_j\rangle\otimes|f_j\rangle$, turns $\rho_{AB}$ into
--
--   $$
--   \rho'_{ABC}=\sum_{j,k}\langle e_j|\rho_{AB}|e_k\rangle\otimes|e_j\rangle\langle e_k|\otimes|f_j\rangle\langle f_k|,
--   $$
--
--   Eq. (3), where $\langle e_j|\rho_{AB}|e_k\rangle$ is the operator on $\mathcal H_A$ with matrix entries $\sum_{b,b'}\overline{e_j(b)}\,\rho_{AB}\big((a,b),(a',b')\big)\,e_k(b')$.
--
--   The paper's proof of Theorems 1 and 2 applies strong subadditivity to this state.
--
--   **Formalization Note** $C$ is indexed by $B$, $|f_j\rangle\langle f_k|$ is `Matrix.single j k 1`, and $\mathcal H_A\otimes\mathcal H_B\otimes\mathcal H_C$ is indexed by `(A × B) × B`, so that $\rho'_{AB}$ is `QAlgorithms.traceRight` of $\rho'_{ABC}$.
-- source:
--   Datta, A Condition for the Nullity of Quantum Discord, arXiv:1003.5256v2, Eq. (3), p.1

import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Defs_Ensemble

open scoped ComplexConjugate

namespace DattaDiscord

/-- **The dilated state** `ρ′_ABC` of Eq. (3), Datta, *A Condition for the Nullity of Quantum Discord*, arXiv:1003.5256v2, p.1: for an orthonormal basis `{e_j}` of
`B`, a system `C` (a copy of `B` with standard basis `{f_j}`) interacts with `B` so that
`U|e_j⟩ ⊗ |0⟩ = |e_j⟩ ⊗ |f_j⟩`, leaving
`ρ′_ABC = ∑_{j,k} ⟨e_j|ρ_AB|e_k⟩ ⊗ |e_j⟩⟨e_k| ⊗ |f_j⟩⟨f_k|`,
where `⟨e_j|ρ_AB|e_k⟩` is the operator on `A` with entries
`∑_{b,b'} conj(e_j(b)) ρ_AB((a,b),(a',b')) e_k(b')`.

**Formalization Note** `C` is indexed by `B` (so `f_j` is the standard basis vector of index `j`,
and `|f_j⟩⟨f_k|` is `Matrix.single j k 1`); `A ⊗ B ⊗ C` is indexed by `(A × B) × B`, so that
`ρ′_AB` is `QAlgorithms.traceRight ρ′_ABC`. -/
noncomputable def dilated {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    (e : OrthonormalBasis B ℂ (EuclideanSpace ℂ B)) (ρ : Matrix (A × B) (A × B) ℂ) :
    Matrix ((A × B) × B) ((A × B) × B) ℂ :=
  ∑ j, ∑ k, Matrix.kronecker
    (Matrix.kronecker
      (Matrix.of fun a a' => ∑ b, ∑ b', conj (e j b) * ρ (a, b) (a', b') * e k b')
      (Matrix.of fun b b' => e j b * conj (e k b')))
    (Matrix.single j k (1 : ℂ))

end DattaDiscord


