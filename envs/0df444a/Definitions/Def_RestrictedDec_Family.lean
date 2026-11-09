-- Prove2me | Definitions.Def_RestrictedDec_Family
-- name    : RestrictedDec_Family
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:52:08.089194+00:00
-- url     : https://prove2.me/theorems/c9e25d38-41fc-4379-a21c-04d41864987b
-- title:
--   Family of permitted functions $\mathcal F$
-- statement:
--   A **family of permitted functions** $\mathcal F$ is a public family of maps $F:\mathcal M_\perp\to\{0,1\}^*$, each specified by a public description $d$. It consists of
--
--   1. an effective syntax: a test whether a description $d$ is admissible at security parameter $\lambda$, and
--   2. a uniform evaluation algorithm: $(\lambda,d,x)\mapsto F_d(x)$.
--
--   The family is **valid** for the message space $\{0,1\}^{n(\lambda)}$ if both are computed by polynomial-time machines uniform in $\lambda$ (evaluation on admissible descriptions and on every $x\in\mathcal M_\perp$). Public parameters chosen separately in each query, such as the candidate in a plaintext-equality test, are part of the description.
--
--   The experiment uses the syntax to decide which queries are permitted.
-- source:
--   Nguyen–Susilo, Between CPA and CCA: Security Hierarchies for Restricted Decryption, STOC 2027 submission (manuscript sha256 6aeac40c…), §2.1, pp.12–13

import Mathlib
import Definitions.Def_BeyondDS_tup
import Definitions.Def_RestrictedDec_encOpt
open QAlgorithms.Complexity
set_option autoImplicit false

namespace RestrictedDec

/-- A **family of permitted functions** `𝓕` of maps `F : M_⊥ → {0,1}*`, given by public
descriptions: `admissible λ d` is the effective syntax of admissible descriptions, and
`eval λ d x = F_d(x)` is the uniform evaluation algorithm.
Nguyen–Susilo, STOC 2027 submission (manuscript sha256 6aeac40c…), §2.1, p.12 ("The permitted
functions form a public family F of efficiently computable maps F : M⊥ −→ {0, 1}∗. The adversary
specifies a function by a public description of polynomial length. The family must have a uniform
evaluation algorithm and an effective syntax for admissible descriptions").

**Formalization Note.** Public parameters chosen per query (p.12) are part of the description. -/
structure Family where
  admissible : ℕ → Str → Bool
  eval : ℕ → Str → Option Str → Str

/-- A family is **valid** for the message space `{0,1}^{n(λ)}`: admissibility is decided, and the
function of an admissible description is evaluated on every `x ∈ M_⊥`, by polynomial-time
machines uniform in `λ` (p.12; p.13: "Function descriptions and their validator are uniform in
λ"). -/
def Family.Valid (n : ℕ → ℕ) (F : Family) : Prop :=
  (∃ f : Str → Str, PolyTimeComputable f ∧ ∀ lam d,
    f (BeyondDS.tup [encNat lam, d]) = BeyondDS.encBool (F.admissible lam d)) ∧
  (∃ f : Str → Str, PolyTimeComputable f ∧ ∀ lam d (x : Option Str),
    F.admissible lam d = true → (∀ m, x = some m → m.length = n lam) →
    f (BeyondDS.tup [encNat lam, d, encOpt x]) = F.eval lam d x)

end RestrictedDec


