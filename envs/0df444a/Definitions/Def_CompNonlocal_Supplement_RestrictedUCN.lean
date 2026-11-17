-- Prove2me | Definitions.Def_CompNonlocal_Supplement_RestrictedUCN
-- name    : CompNonlocal_Supplement_RestrictedUCN
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:10:57.900348+00:00
-- url     : https://prove2.me/theorems/c60ff485-603d-40eb-925f-e69c45b3a93f
-- title:
--   UCN restricted to public verification and independent questions
-- statement:
--   **Restricted UCN:** every entangled state on every bipartite qubit register has a certificate (Definition 10, polynomially many independent rounds, inverse-polynomial gap) with public verification and independent questions.
--
--   Theorem 11 shows that this restricted form is false.
-- source:
--   Głuch, Morimae, From Computational Nonlocality to Public-Key Encryption and Commitments, manuscript (STOC 2027 submission, sha256 e245edd7b7dd5f4c52119a37e0ee1d00eaf20185262775b8ab7d3067a9f2fcae), Theorem 11, p.69; Theorem 5, p.6

import Mathlib
import Definitions.Def_CompNonlocal_Supplement_IsCertificateK
import Definitions.Def_UnitalMIP_HasMaxMixedMarginals
import Definitions.Def_CompNonlocal_Supplement_Game_IsPublic
import Definitions.Def_CompNonlocal_Supplement_Game_IndepQuestions

set_option autoImplicit false

namespace CompNonlocal.Supplement

open QAlgorithms.Complexity

/-- UCN restricted to public verification and independent questions. Głuch, Morimae, *From Computational Nonlocality to Public-Key Encryption and Commitments*, manuscript (STOC 2027 submission, sha256 e245edd7…), Theorem 11, p.69
("Consequently, UCN cannot hold under these restrictions") and Theorem 5, p.6 ("UCN with independent
questions and public verification"): every entangled state on qubit registers has a certificate
(Definition 10, any polynomial number of independent rounds, inverse-polynomial gap) whose verifier
retains no private register and whose questions are independent.

**Formalization Note** As in `UCN`, the local spaces are qubit registers of every size. -/
def RestrictedUCN : Prop :=
  ∀ (nA nB : ℕ) (ω : Matrix (Bits nA × Bits nB) (Bits nA × Bits nB) ℂ), UnitalMIP.IsEntangled ω →
    ∃ (G : Game) (cc s : ℕ → ℝ), G.IsPublic ∧ G.IndepQuestions ∧ IsCertificateK G ω cc s

end CompNonlocal.Supplement


