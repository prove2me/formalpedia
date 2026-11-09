-- Prove2me | Definitions.Def_RestrictedDec_famId
-- name    : RestrictedDec_famId
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:53:19.212862+00:00
-- url     : https://prove2.me/theorems/96abd8b0-7ab4-47ae-84a5-4fc6be2e3c2c
-- title:
--   Full-decryption family $\mathcal F_{\mathrm{id}}=\{\mathrm{id}_{\mathcal M_\perp}\}$
-- statement:
--   The **full-decryption family** $\mathcal F_{\mathrm{id}}=\{\mathrm{id}_{\mathcal M_\perp}\}$ has a single admissible description, whose function returns the decryption output itself. With it the functional decryption oracle is full decryption, and the pre-challenge and adaptive games of Definition 1 are IND-CCA1 and IND-CCA2.
--
--   **Formalization Note** The admissible description is the empty string, and $x\in\mathcal M_\perp$ is returned in the code `encOpt`.
-- source:
--   Nguyen–Susilo, Between CPA and CCA: Security Hierarchies for Restricted Decryption, STOC 2027 submission (manuscript sha256 6aeac40c…), §2.1, p.13; §2.2, p.14

import Mathlib
import Definitions.Def_RestrictedDec_Family
open QAlgorithms.Complexity
set_option autoImplicit false

namespace RestrictedDec

/-- The **full-decryption family** `𝓕_id = {id_{M_⊥}}`: one admissible description (the empty
string), whose function returns the decryption output itself.
Nguyen–Susilo, STOC 2027 submission (manuscript sha256 6aeac40c…), §2.1, p.13 ("The identity
function gives full decryption"); §2.2, p.14 ("If the identity function idM⊥ is permitted, the
pre-challenge and adaptive games recover IND-CCA1 and IND-CCA2").

**Formalization Note.** The value `x ∈ M_⊥` is returned as the string `encOpt x`. -/
def famId : Family where
  admissible := fun _ d => decide (d = [])
  eval := fun _ _ x => encOpt x

end RestrictedDec


