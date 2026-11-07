-- Prove2me | Definitions.Def_QMAPlusGap_IsEntrywiseNonneg
-- name    : QMAPlusGap_IsEntrywiseNonneg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T04:05:17.6045+00:00
-- url     : https://prove2.me/theorems/d165a6c3-20e8-4170-9897-d8776a6074af
-- title:
--   Entrywise nonnegative operators
-- statement:
--   An operator $\rho$ on $\mathbb C^{\kappa}$ is **entrywise nonnegative** (in the fixed computational basis) if every matrix entry is a nonnegative real number:
--   $$
--   \langle a|\rho|b\rangle\in\mathbb R_{\ge0}\qquad\text{for all }a,b\in\kappa .
--   $$
--
--   This is a condition on matrix entries, not positive semidefiniteness. Post-measurement states of nonnegative proofs and all their reductions have this property, and Lemma 10 and Proposition 9 use it.
-- source:
--   Miyamoto, Near-Optimal Gap Amplification for Nonnegative Unentangled Quantum Proofs, arXiv:2608.07986 (held version, sha256 4667925f…), Lemma 10, p.17; §4.3, p.17

import Mathlib

set_option autoImplicit false

namespace QMAPlusGap

/-- **Entrywise nonnegative operator**, Miyamoto, *Near-Optimal Gap Amplification for Nonnegative Unentangled Quantum Proofs*, arXiv:2608.07986 (held version, sha256 4667925f…), §4.3, p.17 and Lemma 10, p.17 ("entrywise nonnegative in the fixed
computational basis"): every matrix entry `⟨a|ρ|b⟩` in the computational basis is a nonnegative real number.

**Formalization Note** This is a condition on matrix entries, not positive semidefiniteness. Operators on
`ℂ^κ` are matrices indexed by the basis `κ`. -/
def IsEntrywiseNonneg {κ : Type} (ρ : Matrix κ κ ℂ) : Prop :=
  ∀ a b : κ, (ρ a b).im = 0 ∧ 0 ≤ (ρ a b).re

end QMAPlusGap


