-- Prove2me | Definitions.Def_WildeQIT_Compression_Supplement_privateCapacity
-- name    : WildeQIT_Compression_Supplement_privateCapacity
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T04:01:34.756787+00:00
-- url     : https://prove2.me/theorems/5e91a290-3e6b-5b7d-884d-5220a19fad6e
-- title:
--   Private classical capacity $C_P(\mathcal N)$
-- statement:
--   The **private classical capacity** of a quantum channel $\mathcal N$ is the supremum of all achievable rates for private classical communication:
--
--   $$
--   C_P(\mathcal N)=\sup\{P : P\text{ is an achievable private rate for }\mathcal N\}.
--   $$
--
--   The Devetak–Cai–Winter–Yeung theorem (Theorem 23.2.1) identifies it with the regularized private information.
--
--   **Formalization Note** The supremum is taken in the extended reals, as for the published quantum capacity `WildeQIT.QErasure.quantumCapacity`, so it is the true least upper bound in every case.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, §23.1, p. 641

import Mathlib
import Definitions.Def_WildeQIT_Compression_Supplement_IsAchievablePrivateRate

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, §23.1, p. 641
(the private classical capacity `C_P(N)`).
-/

namespace WildeQIT.Compression.Supplement

/-- **Private classical capacity `C_P(N)`** (Wilde, *From Classical to Quantum Shannon Theory*,
arXiv:1106.1445v8, §23.1, p. 641): "The private classical capacity `C_P(N)` of a channel `N_{A′→B}`
is equal to the supremum of all achievable rates for private classical communication."

**Formalization Note.** The supremum is taken in the extended reals `EReal`, as for the published
quantum capacity `WildeQIT.QErasure.quantumCapacity`, so it is the true least upper bound in every
case (an empty set gives `⊥`, an unbounded one `⊤`), never a junk real value. -/
noncomputable def privateCapacity {a b : Type} [Fintype a] [Fintype b] [DecidableEq a]
    [DecidableEq b] (N : QChannel a b) : EReal :=
  sSup ((fun P : ℝ => (P : EReal)) '' {P | IsAchievablePrivateRate N P})

end WildeQIT.Compression.Supplement


