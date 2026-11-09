-- Prove2me | Definitions.Def_RestrictedDec_INDCCA2
-- name    : RestrictedDec_INDCCA2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:55:35.277144+00:00
-- url     : https://prove2.me/theorems/2b9fbdec-56f1-427d-83a8-57d3f0ed1907
-- title:
--   IND-CCA1 and IND-CCA2 as $\mathrm{Sec}^{na}(\mathcal F_{\mathrm{id}})$, $\mathrm{Sec}^{ad}(\mathcal F_{\mathrm{id}})$
-- statement:
--   A scheme over $\{0,1\}^{n(\lambda)}$ is **IND-CCA1 secure** if it belongs to $\mathrm{Sec}^{na}(\mathcal F_{\mathrm{id}})$ and **IND-CCA2 secure** if it belongs to $\mathrm{Sec}^{ad}(\mathcal F_{\mathrm{id}})$: the pre-challenge and the adaptive game with full decryption, with ordinary correctness.
--
--   The paper shows (§2.2) that these coincide with the classical CCA1 and CCA2 requirements: a CCA2 reduction computes the public common answer at the exact challenge without decrypting, and the functional oracle answers every admissible CCA2 query with the identity function; the simulations are exact.
--
--   **Formalization Note** The classical games are not restated; Corollary 2's hypothesis "IND-CCA2-secure public-key encryption exists" is stated with `INDCCA2`.
-- source:
--   Nguyen–Susilo, Between CPA and CCA: Security Hierarchies for Restricted Decryption, STOC 2027 submission (manuscript sha256 6aeac40c…), §2.2, p.14

import Mathlib
import Definitions.Def_RestrictedDec_famId
import Definitions.Def_RestrictedDec_Sec
open QAlgorithms.Complexity
set_option autoImplicit false

namespace RestrictedDec

/-- **IND-CCA1** security: `Sec^na(𝓕_id)`, the pre-challenge game with full decryption.
Nguyen–Susilo, STOC 2027 submission (manuscript sha256 6aeac40c…), §2.2, p.14 ("If the identity
function idM⊥ is permitted, the pre-challenge and adaptive games recover IND-CCA1 and IND-CCA2,
respectively. … Thus the security requirements coincide, including ordinary correctness."). -/
def INDCCA1 (n : ℕ → ℕ) (P : PKE) : Prop := Sec .na n famId P

/-- **IND-CCA2** security: `Sec^ad(𝓕_id)`, the adaptive game with full decryption (the exact
challenge may be queried only when `id(m₀) = id(m₁)`).
Nguyen–Susilo, STOC 2027 submission (manuscript sha256 6aeac40c…), §2.2, p.14.

**Formalization Note.** p.14 shows that these games coincide with the classical CCA1/CCA2 games
(exact simulations both ways); the classical games are not restated. -/
def INDCCA2 (n : ℕ → ℕ) (P : PKE) : Prop := Sec .ad n famId P

end RestrictedDec


