-- Prove2me | Definitions.Def_RestrictedDec_Supplement_FamilyValidM
-- name    : RestrictedDec_Supplement_FamilyValidM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:21:45.234196+00:00
-- url     : https://prove2.me/theorems/3edc5483-8b20-4048-bc35-2d12a0efb4d5
-- title:
--   Valid family of permitted functions over $M$
-- statement:
--   A family $\mathcal F$ of permitted functions $F:M_\perp\to\{0,1\}^*$, given by public descriptions, is **valid over $M$** if admissibility of a description is decided, and the function of an admissible description is evaluated at every $x\in M_\perp=M_\lambda\cup\{\bot\}$, by polynomial-time machines uniform in $\lambda$.
--
--   This is the paper's requirement that a family have a uniform evaluation algorithm and an effective syntax for admissible descriptions.
--
--   **Formalization Note** The published `RestrictedDec.Family.Valid` with $\{0,1\}^{n(\lambda)}$ replaced by $M_\lambda$.
-- source:
--   Nguyen–Susilo, Between CPA and CCA: Security Hierarchies for Restricted Decryption, STOC 2027 submission (manuscript sha256 6aeac40c…), §2.1, pp.12–13

import Mathlib
import Definitions.Def_BeyondDS_tup
import Definitions.Def_RestrictedDec_encOpt
import Definitions.Def_RestrictedDec_Family
open QAlgorithms.Complexity
set_option autoImplicit false

namespace RestrictedDec

namespace Supplement

/-- A family `𝓕` of permitted functions is **valid for the message space `M`**: admissibility of a
description is decided, and the function of an admissible description is evaluated on every
`x ∈ M_⊥ = M_λ ∪ {⊥}`, by polynomial-time machines uniform in `λ`.
Nguyen–Susilo, STOC 2027 submission (manuscript sha256 6aeac40c…), §2.1, p.12 ("The family must
have a uniform evaluation algorithm and an effective syntax for admissible descriptions"); p.13
("Function descriptions and their validator are uniform in λ").

**Formalization Note.** The published `RestrictedDec.Family.Valid` with `m.length = n λ` replaced by
`M λ m`. -/
def FamilyValidM (M : ℕ → Str → Prop) (F : Family) : Prop :=
  (∃ f : Str → Str, PolyTimeComputable f ∧ ∀ lam d,
    f (BeyondDS.tup [encNat lam, d]) = BeyondDS.encBool (F.admissible lam d)) ∧
  (∃ f : Str → Str, PolyTimeComputable f ∧ ∀ lam d (x : Option Str),
    F.admissible lam d = true → (∀ m, x = some m → M lam m) →
    f (BeyondDS.tup [encNat lam, d, encOpt x]) = F.eval lam d x)

end Supplement

end RestrictedDec


