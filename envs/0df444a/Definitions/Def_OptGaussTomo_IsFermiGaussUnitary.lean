-- Prove2me | Definitions.Def_OptGaussTomo_IsFermiGaussUnitary
-- name    : OptGaussTomo_IsFermiGaussUnitary
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:05:45.163196+00:00
-- url     : https://prove2.me/theorems/4884bc6c-f9d3-4d1a-b933-228a14d17a21
-- title:
--   Fermionic Gaussian unitaries $U_R$, $R\in SO(2m)$
-- statement:
--   A unitary $U$ on $m$ qubits is a **fermionic Gaussian unitary** if there is a real matrix $R\in SO(2m)$ with
--
--   $$
--   U c_j U^\dagger=\sum_{k=1}^{2m}R_{kj}\,c_k\qquad (j=1,\dots,2m), \tag{C.1}
--   $$
--
--   where $c_1,\dots,c_{2m}$ are the Jordan–Wigner Majorana operators. $U$ is determined by $R$ up to a phase, and $R\mapsto U_R$ is a projective representation of $SO(2m)$.
--
--   **Formalization Note** The Majorana operators are the published `FermiCap.Gaussian.majorana` (0-based: index $2(j-1)$ is $c_{2j-1}$, index $2j-1$ is $c_{2j}$).
-- source:
--   Chen, Fanizza, Girardi, Lami, Mele, Walter, Witteveen, Optimal tomography of bosonic and fermionic Gaussian states, arXiv:2607.11847 (held version, sha256 0f7548a2a5cfd55079e5d7f1787c97c8561a818a53d7e29824715104bad416ed), §C.1 p.33 (pdf p.33), eq. (C.1)

import Mathlib
import Definitions.Def_FermiCap_Gaussian_Majorana

open FermiCap.Gaussian (Qubits Op majorana)
open scoped Matrix

namespace OptGaussTomo

/-!
# Fermionic Gaussian unitaries

Chen, Fanizza, Girardi, Lami, Mele, Walter, Witteveen, *Optimal tomography of bosonic and
fermionic Gaussian states*, arXiv:2607.11847 (held version, sha256 0f7548a2…), §C.1, p.33:
"For each `R ∈ SO(2m)`, there exists a unitary `U_R` satisfying
`U_R c_j U_R† = ∑_{k=1}^{2m} R_kj c_k`. (C.1) … We call any unitary satisfying (C.1) a Gaussian
unitary."

**Formalization Note.** The Majorana operators are the published Jordan–Wigner operators
`FermiCap.Gaussian.majorana m p` on `m` qubits (`p = 0, …, 2m−1`, 0-based: `p = 2(j−1)` is the
source's `c_{2j−1} = Z₁⋯Z_{j−1}X_j` and `p = 2j − 1` is `c_{2j} = Z₁⋯Z_{j−1}Y_j`). `R` ranges over
real special orthogonal matrices. A Gaussian unitary is determined by `R` up to a phase.
-/

/-- `U` is a fermionic Gaussian unitary: unitary, and `U c_j U† = ∑_k R_kj c_k` for some
`R ∈ SO(2m)` (C.1). -/
def IsFermiGaussUnitary {m : ℕ} (U : Op m) : Prop :=
  U ∈ Matrix.unitaryGroup (Qubits m) ℂ ∧
  ∃ R : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ,
    R ∈ Matrix.specialOrthogonalGroup (Fin (2 * m)) ℝ ∧
    ∀ j : Fin (2 * m), U * majorana m j * Uᴴ = ∑ k : Fin (2 * m), ((R k j : ℝ) : ℂ) • majorana m k

end OptGaussTomo


