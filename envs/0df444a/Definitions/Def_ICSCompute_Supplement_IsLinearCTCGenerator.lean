-- Prove2me | Definitions.Def_ICSCompute_Supplement_IsLinearCTCGenerator
-- name    : ICSCompute_Supplement_IsLinearCTCGenerator
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T15:03:43.027851+00:00
-- url     : https://prove2.me/theorems/2690b1ee-8eaa-42d6-9dea-b6fca3346bbf
-- title:
--   Generators and linear closed-timelike-curve generators
-- statement:
--   A **generator** $A$ assigns to every well-formed circuit description $(m,C)$, where $C$ is an $(m+r)$-to-$(m+\ell)$ quantum circuit and $m,r,\ell\ge0$, an $r$-to-$\ell$ qubit quantum channel $A(m,C)$. A generator **agrees on** a class of descriptions if $A(m,C)=\mathrm{PMO}_{(m,C)}$, the generated channel, for every description in the class; on other descriptions it may return any quantum channel of the prescribed dimensions.
--
--   A generator is a **linear CTC generator** (Definition 4.11) if
--
--   $$A(m,C)=\mathrm{PMO}_{(m,C)}\qquad\text{whenever }(m,C)\text{ is a PMG}.$$
--
--   Generators are the oracles of the complexity classes of Definition 4.12; the algorithm must be correct for every generator of the class, so it gains nothing from queries that are not valid PMGs.
--
--   **Formalization Note** Descriptions are the published normal-form circuits `Desc m r ℓ` of the base mission. A generator is an arbitrary function (it need not be computable, p.22). The obligation is a parameter (`ValidityPredicate`): `pmgValid` gives Definition 4.11, and the weaker obligation of Theorem 1.1 is a different predicate.
-- source:
--   Shmueli, What Can Be Computed with Indefinite Causal Structure?, arXiv:2610.40573 (version of 2026-11-03, sha256 d3e36399…b606), Definition 4.11 and Remark 4.4, p.22 (PDF p.24)

import Mathlib
import Definitions.Def_ICSCompute_IsQuantumChannel
import Definitions.Def_ICSCompute_IsPurePMG

namespace ICSCompute.Supplement

open QAlgorithms

/-- A **generator**: a function assigning to every well-formed description `(m, C)`, with `C`
an `(m + r)`-to-`(m + ℓ)` circuit and `m, r, ℓ ∈ ℕ ∪ {0}`, an `r`-to-`ℓ` qubit quantum channel
(Shmueli, arXiv:2610.40573, Definition 4.11, p.22 (PDF p.24), first sentence). -/
structure Generator where
  /-- The channel returned for the description `D = (m, C)`. -/
  A : (m r ℓ : ℕ) → Desc m r ℓ →
    (Matrix (Qubits r) (Qubits r) ℂ →ₗ[ℂ] Matrix (Qubits ℓ) (Qubits ℓ) ℂ)
  /-- Every returned map is a quantum channel (Definition 3.13). -/
  channel : ∀ (m r ℓ : ℕ) (D : Desc m r ℓ), IsQuantumChannel (A m r ℓ D)

/-- A predicate on descriptions saying on which descriptions a generator is obliged to return
the generated channel. -/
abbrev ValidityPredicate := (m r ℓ : ℕ) → Desc m r ℓ → Prop

/-- The generator returns the generated channel `PMO_D` on every description satisfying
`Valid`, and is unconstrained (beyond being a channel) elsewhere. -/
def Generator.AgreesOn (G : Generator) (Valid : ValidityPredicate) : Prop :=
  ∀ (m r ℓ : ℕ) (D : Desc m r ℓ), Valid m r ℓ D → G.A m r ℓ D = pmoD D

/-- The validity predicate of Definition 4.11: `D` is a PMG. -/
def pmgValid : ValidityPredicate := fun _ _ _ D => IsPMG D

/-- **Linear closed timelike curve generator** (Shmueli, *What Can Be Computed with Indefinite
Causal Structure?*, arXiv:2610.40573, version of 2026-11-03, sha256 d3e36399…b606,
Definition 4.11, p.22 (PDF p.24)): "Let `A` be a function that maps every well-formed
description `(m, C)`, where `C` is an `(m + r)`-to-`(m + ℓ)` quantum circuit and
`m, r, ℓ ∈ ℕ ∪ {0}`, to an `r`-to-`ℓ` qubit quantum channel. We say that `A` is a linear CTC
generator if `A(m, C) = PMO_{(m,C)}` whenever `(m, C)` is a PMG. On descriptions that are not
PMGs, `A` may return any quantum channel of the prescribed dimensions."

**Formalization Note** Descriptions are the base mission's `Desc m r ℓ` (normal-form circuits);
the generator is an arbitrary (not necessarily computable) function, as on p.22 ("The generator
of channels is assumed and does not need to be efficiently computable"). Channels are
`IsQuantumChannel` (CP with every qubit reference register, TP on every matrix). -/
def IsLinearCTCGenerator (G : Generator) : Prop :=
  G.AgreesOn pmgValid

end ICSCompute.Supplement


