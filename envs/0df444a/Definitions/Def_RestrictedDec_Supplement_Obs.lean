-- Prove2me | Definitions.Def_RestrictedDec_Supplement_Obs
-- name    : RestrictedDec_Supplement_Obs
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:26:22.856821+00:00
-- url     : https://prove2.me/theorems/9bb658a7-48bd-4f06-b728-e43b741acf98
-- title:
--   Public observations $q$, $\mathrm{Valid}_q$, $\mathrm{Rep}_q$, $q=T\circ r$, and $\mathrm{Norm}_q$ (4.1)
-- statement:
--   1. A **uniformly efficient map** $r:M_\perp\to\{0,1\}^*$ is computed from $(1^\lambda,x)$ by one polynomial-time machine; a **public observation** is such a map whose values on $M_\perp$ all have one polynomially bounded length $\ell(\lambda)$.
--   2. An observation $q$ **has the public algorithms of §2.3** if $\mathrm{Valid}_q(1^\lambda,y)$ decides exactly whether $y\in Y_q=q_\lambda(M_\lambda)$, and the deterministic $\mathrm{Rep}_q(1^\lambda,y)$ returns, for $y\in Y_q$, a valid $m$ with $q(m)=y$; both are polynomial-time and use no secret key. $q(\bot)$ is unconstrained.
--   3. $q$ is **efficiently recoverable from $r$** if $q(x)=T(1^\lambda,r(x))$ on $M_\perp$ for a polynomial-time $T$.
--   4. The **normalizer** (4.1) is
--   $$\mathrm{Norm}_q(y,z)=\begin{cases}z,& z\in M_\lambda\text{ and }q(z)=y,\\ \mathrm{Rep}_q(1^\lambda,y),&\text{otherwise},\end{cases}$$
--   so that $q(\mathrm{Norm}_q(y,z))=y$ for every valid label $y$ and every $z\in M_\perp$ (4.2), as checked in the sanity file.
-- source:
--   Nguyen–Susilo, Between CPA and CCA: Security Hierarchies for Restricted Decryption, STOC 2027 submission (manuscript sha256 6aeac40c…), §2.3, p.14; (4.1)–(4.2), p.23; App. B.3, p.39

import Mathlib
import Definitions.Def_BeyondDS_tup
import Definitions.Def_NoisyOWMPC_Negligible
import Definitions.Def_RestrictedDec_encOpt
open QAlgorithms.Complexity
set_option autoImplicit false

namespace RestrictedDec

namespace Supplement

/-- `r = r_λ : M_⊥ → {0,1}*` is a **uniformly efficient map on decryption outputs**: one
polynomial-time machine computes `r_λ(x)` from `(1^λ, x)` for every `x ∈ M_⊥`.
Nguyen–Susilo, STOC 2027 submission (manuscript sha256 6aeac40c…), Theorem 11, p.43 ("let r be any
uniformly efficient map on decryption outputs"). -/
def IsEffMap (M : ℕ → Str → Prop) (r : ℕ → Option Str → Str) : Prop :=
  ∃ f : Str → Str, PolyTimeComputable f ∧ ∀ lam (x : Option Str), (∀ m, x = some m → M lam m) →
    f (BeyondDS.tup [encNat lam, encOpt x]) = r lam x

/-- `q = q_λ : M_⊥ → {0,1}^{ℓ(λ)}` is a **public observation**: a uniformly polynomial-time map
whose values on `M_⊥` all have one length `ℓ(λ)`, `ℓ` polynomially bounded.
Nguyen–Susilo, STOC 2027 submission (manuscript sha256 6aeac40c…), §2.3, p.14 ("For any uniformly
polynomial-time map q = qλ : M⊥ −→ {0, 1}ℓ(λ), where ℓ is polynomially bounded"). -/
def IsObsMap (M : ℕ → Str → Prop) (q : ℕ → Option Str → Str) : Prop :=
  IsEffMap M q ∧ ∃ ℓ : ℕ → ℕ, NoisyOWMPC.PolyBounded ℓ ∧
    ∀ lam (x : Option Str), (∀ m, x = some m → M lam m) → (q lam x).length = ℓ lam

/-- A public observation `q` **with its public algorithms** `Valid_q` and `Rep_q`. -/
structure Obs where
  q : ℕ → Option Str → Str
  valid : ℕ → Str → Bool
  rep : ℕ → Str → Str

/-- The observation `o` **has the public algorithms of Section 2.3** over `M`: `q` is a public
observation (`IsObsMap`), and
1. `Valid_q(1^λ, y)` decides exactly whether `y ∈ Y_q = q_λ(M_λ)`;
2. the deterministic `Rep_q(1^λ, y)` returns, for `y ∈ Y_q`, a valid message `m ∈ M_λ` with
   `q(m) = y`;
both computed by polynomial-time machines, uniformly in `λ`, using no secret key.
Nguyen–Susilo, STOC 2027 submission (manuscript sha256 6aeac40c…), §2.3, p.14 ("Write Yq = qλ(Mλ)
for the values attained on valid plaintexts. We require the following polynomial-time algorithms:
(i) Validq(1λ, y), which decides exactly whether y ∈ Yq; (ii) Repq(1λ, y), which, for y ∈ Yq,
returns a valid message m with q(m) = y. We take Repq to be deterministic").

**Formalization Note.** `q(⊥)` is unconstrained: it may coincide with a valid label (p.14). -/
def Obs.IsPublic (M : ℕ → Str → Prop) (o : Obs) : Prop :=
  IsObsMap M o.q ∧
  (∀ lam y, o.valid lam y = true ↔ ∃ m, M lam m ∧ o.q lam (some m) = y) ∧
  (∀ lam y, o.valid lam y = true → M lam (o.rep lam y) ∧ o.q lam (some (o.rep lam y)) = y) ∧
  (∃ f : Str → Str, PolyTimeComputable f ∧ ∀ lam y,
    f (BeyondDS.tup [encNat lam, y]) = BeyondDS.encBool (o.valid lam y)) ∧
  (∃ f : Str → Str, PolyTimeComputable f ∧ ∀ lam y, o.valid lam y = true →
    f (BeyondDS.tup [encNat lam, y]) = o.rep lam y)

/-- `q` is **efficiently recoverable from `r`** (`q = T ∘ r` for an efficient public map `T`) on
`M_⊥`. Nguyen–Susilo, STOC 2027 submission (manuscript sha256 6aeac40c…), §2.3, p.14 ("If
q(x) = T(r(x)) for a polynomial-time T, the value returned by q can be computed from the value
returned by r"); Theorem 7, p.27; Theorem 9, p.38.

**Formalization Note.** `T` also reads `1^λ`. -/
def Recoverable (M : ℕ → Str → Prop) (q r : ℕ → Option Str → Str) : Prop :=
  ∃ T : Str → Str, PolyTimeComputable T ∧ ∀ lam (x : Option Str), (∀ m, x = some m → M lam m) →
    q lam x = T (BeyondDS.tup [encNat lam, r lam x])

open Classical in
/-- The **normalizer** `Norm_q(y, z)` (4.1): `z` if `z ∈ M_λ` and `q(z) = y`, `Rep_q(1^λ, y)`
otherwise (in particular for `z = ⊥`). The same rule is `Norm_{q,y}(z)` of (B.2) and App. B.3.
Nguyen–Susilo, STOC 2027 submission (manuscript sha256 6aeac40c…), (4.1), p.23; (B.2), p.36;
App. B.3, p.39. -/
noncomputable def norm (M : ℕ → Str → Prop) (o : Obs) (lam : ℕ) (y : Str) :
    Option Str → Option Str
  | some z => if M lam z ∧ o.q lam (some z) = y then some z else some (o.rep lam y)
  | none => some (o.rep lam y)

end Supplement

end RestrictedDec


