-- Prove2me | Definitions.Def_CompNonlocal_Supplement_UCN
-- name    : CompNonlocal_Supplement_UCN
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:08:43.862631+00:00
-- url     : https://prove2.me/theorems/972eea32-14ac-456a-9307-358392dfa0fb
-- title:
--   The universal computational nonlocality assumption (Assumption 2)
-- statement:
--   **Universal computational nonlocality (UCN):** every entangled state (a density matrix that is not separable; the published `UnitalMIP.IsEntangled`) on every bipartite qubit register $(\mathbb C^2)^{\otimes n_A}\otimes(\mathbb C^2)^{\otimes n_B}$ is computationally nonlocal in the sense of Definition 10.
--
--   This is the hypothesis of Theorem 9.
--
--   **Formalization Note** The paper's assumption ranges over all finite-dimensional spaces $H_A,H_B$; requiring it only on qubit registers asks less, so a theorem assuming this version implies the paper's.
-- source:
--   Głuch, Morimae, From Computational Nonlocality to Public-Key Encryption and Commitments, manuscript (STOC 2027 submission, sha256 e245edd7b7dd5f4c52119a37e0ee1d00eaf20185262775b8ab7d3067a9f2fcae), Assumption 2, p.26

import Mathlib
import Definitions.Def_CompNonlocal_Supplement_IsCompNonlocal
import Definitions.Def_UnitalMIP_HasMaxMixedMarginals

set_option autoImplicit false

namespace CompNonlocal.Supplement

open QAlgorithms.Complexity

/-- The universal computational nonlocality (UCN) assumption. Głuch, Morimae, *From Computational Nonlocality to Public-Key Encryption and Commitments*, manuscript (STOC 2027 submission, sha256 e245edd7…), Assumption 2, p.26: "For all
finite-dimensional Hilbert spaces H_A, H_B, every entangled state ω_AB ∈ S(H_A ⊗ H_B) is
computationally nonlocal in the sense of Definition 10."

**Formalization Note** The local spaces range over qubit registers `(C²)^{⊗n_A}`, `(C²)^{⊗n_B}`, for
all `n_A, n_B`. This asks less than the paper's assumption (every finite-dimensional space embeds
into a qubit register, but the assumption is only required of states on qubit registers), so a
theorem with `UCN` as hypothesis is at least as strong as the paper's. -/
def UCN : Prop :=
  ∀ (nA nB : ℕ) (ω : Matrix (Bits nA × Bits nB) (Bits nA × Bits nB) ℂ),
    UnitalMIP.IsEntangled ω → IsCompNonlocal ω

end CompNonlocal.Supplement


