-- Prove2me | Definitions.Def_RestrictedDec_Supplement_SecSubsetneq
-- name    : RestrictedDec_Supplement_SecSubsetneq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:24:23.649773+00:00
-- url     : https://prove2.me/theorems/cdc325c2-5588-416d-9d56-1d91233f5f8e
-- title:
--   Strict asymptotic inclusion $\mathrm{Sec}^t(\mathcal G)\subsetneq\mathrm{Sec}^t(\mathcal F)$
-- statement:
--   For families $\mathcal G,\mathcal F$ and a timing $t$, $\mathrm{Sec}^t(\mathcal G)\subsetneq\mathrm{Sec}^t(\mathcal F)$ over $M$ means:
--
--   1. every efficient scheme over $M$ (polynomial-time, decrypting into $M_\lambda\cup\{\bot\}$, App. A.1) in $\mathrm{Sec}^t(\mathcal G)$ is in $\mathrm{Sec}^t(\mathcal F)$; and
--   2. one efficient scheme lies in $\mathrm{Sec}^t(\mathcal F)$ but not in $\mathrm{Sec}^t(\mathcal G)$.
--
--   This is the paper's asymptotic notion of strictness: a single uniformly constructible scheme satisfies the weaker notion while a single PPT attack breaks the stronger one, possibly only on infinitely many security parameters.
-- source:
--   Nguyen–Susilo, Between CPA and CCA: Security Hierarchies for Restricted Decryption, STOC 2027 submission (manuscript sha256 6aeac40c…), §2.3, p.15

import Mathlib
import Definitions.Def_RestrictedDec_Supplement_IsSchemeM
import Definitions.Def_RestrictedDec_Supplement_SecM
open QAlgorithms.Complexity
set_option autoImplicit false

namespace RestrictedDec

namespace Supplement

/-- **Strict asymptotic inclusion** `Sec^t(𝓖) ⊊ Sec^t(𝓕)` over the message space `M`: every
(efficient) scheme over `M` in `Sec^t(𝓖)` is in `Sec^t(𝓕)`, and one efficient scheme is in `Sec^t(𝓕)` but not in `Sec^t(𝓖)`.
Nguyen–Susilo, STOC 2027 submission (manuscript sha256 6aeac40c…), §2.3, p.15 ("An inclusion is
strict in the asymptotic sense only when a single uniformly constructible encryption scheme
satisfies the weaker notion and a single PPT attack has nonnegligible advantage for the stronger one
(possibly on an infinite subsequence of security parameters)").

**Formalization Note.** "Not in `Sec^t(𝓖)`" is the negation of `SecM`; for a correct scheme it says
that some uniform PPT adversary has non-negligible advantage. The inclusion ranges over the schemes
of the paper, those with message space `M` (`IsSchemeM`: polynomial-time, and `Dec` outputs in
`M_λ ∪ {⊥}`, App. A.1, p.29). Over arbitrary `PKE` values it would be false: a decryption output
outside `M_λ` is not covered by the simulation `𝓕 ⪯ 𝓖` of §3.1, which is stated on `M_⊥` only. -/
def SecSubsetneq (t : Timing) (M : ℕ → Str → Prop) (G F : Family) : Prop :=
  (∀ P : PKE, IsSchemeM M P → SecM t M G P → SecM t M F P) ∧
    ∃ P : PKE, IsSchemeM M P ∧ SecM t M F P ∧ ¬ SecM t M G P

end Supplement

end RestrictedDec


