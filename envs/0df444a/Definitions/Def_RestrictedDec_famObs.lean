-- Prove2me | Definitions.Def_RestrictedDec_famObs
-- name    : RestrictedDec_famObs
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:53:05.361688+00:00
-- url     : https://prove2.me/theorems/5525f592-1428-46f8-9f35-c6a6ebaf33a0
-- title:
--   Observation class $\mathcal F_q=\{g\circ q\}$
-- statement:
--   For an observation $q=q_\lambda:\mathcal M_\perp\to\{0,1\}^{\ell(\lambda)}$, the **observation class** is
--
--   $$\mathcal F_q=\{\,g\circ q:\ g\text{ supplied as an admissible polynomial-size circuit}\,\}.$$
--
--   Its admissible descriptions are circuit descriptions, and the description of $g$ denotes $x\mapsto g(q_\lambda(x))$. One writes $\mathrm{Sec}^t(q)$ for $\mathrm{Sec}^t(\mathcal F_q)$. On an ordinary query the single answer $q(\mathrm{Dec}(c))$ determines every allowed reply; at the exact adaptive challenge, admissibility is decided by the particular $g\circ q$ chosen.
--
--   **Formalization Note** The circuit reads the string $q_\lambda(x)$ as its input wires.
-- source:
--   Nguyen–Susilo, Between CPA and CCA: Security Hierarchies for Restricted Decryption, STOC 2027 submission (manuscript sha256 6aeac40c…), §2.3, p.14

import Mathlib
import Definitions.Def_RestrictedDec_Family
import Definitions.Def_RestrictedDec_Circuit
open QAlgorithms.Complexity
set_option autoImplicit false

namespace RestrictedDec

/-- The **public observation class** `𝓕_q = {g ∘ q : g an admissible polynomial-size circuit}` of
an observation `q = q_λ : M_⊥ → {0,1}^{ℓ(λ)}`: the admissible descriptions are circuit codes, and
the description of `g` denotes `x ↦ g(q_λ(x))`. `Sec^t(q)` is `Sec^t(𝓕_q)`.
Nguyen–Susilo, STOC 2027 submission (manuscript sha256 6aeac40c…), §2.3, p.14 ("For any uniformly
polynomial-time map q = qλ : M⊥ −→ {0, 1}ℓ(λ), where ℓ is polynomially bounded, we can consider the
class Fq = {g ◦ q : g is supplied as an admissible polynomial-size circuit}. Write Sect(q) for
Sect(Fq).").

**Formalization Note.** The circuit reads the string `q λ x` as its input wires, whatever its
length (no padding or truncation). Admissibility at the exact challenge is decided by the
circuit's outputs on `m₀` and `m₁` (descriptions, not semantic equality, p.13). -/
def famObs (q : ℕ → Option Str → Str) : Family where
  admissible := fun _ d => (decCircuit d).isSome
  eval := fun lam d x =>
    match decCircuit d with
    | some C => C.eval (q lam x)
    | none => []

end RestrictedDec


