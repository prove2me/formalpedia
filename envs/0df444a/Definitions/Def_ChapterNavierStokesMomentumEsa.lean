-- Prove2me | Definitions.Def_ChapterNavierStokesMomentumEsa
-- name    : ChapterNavierStokesMomentumEsa
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T06:23:02.888174+00:00
-- url     : https://prove2.me/theorems/c475227f-7ad1-435a-bee9-ef240f48c6b5
-- title:
--   Chapter NavierStokesMomentumEsa
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterNavierStokesMomentumEsa.lean`): generated def bundle for ChapterNavierStokesMomentumEsa. See BookProof/ChapterNavierStokesMomentumEsa.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesMomentumEsa.lean

import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesFarisLavineLift
import Mathlib


/-!
# Essential self-adjointness of the Navier–Stokes Hamiltonian, momentum representation

`BookProof.ChapterNavierStokesIkebeKato` proved, for an arbitrary index set, the
three analytic facts that the Faris–Lavine route needs about the comparison
operator: positivity, surjectivity of `N + 1` on the maximal domain, and the
fact that the finite-mode states are an operator core.  Here those facts are
specialised twice.

**1. One particle.**  In the fiber momentum representation the comparison
operator `n = ∑ᵢ πᵢ² + ∑ᵢ Vᵢ² + I` is multiplication by the symbol
`σ(k) = ∑ᵢ pᵢ(k)² + ∑ᵢ qᵢ(k)² + 1 ≥ 1` (`nsSymbol`), which is exactly the operator
`ComparisonData.comparison` of `BookProof.ChapterNavierStokesFarisLavineLift`
(`nsComparison_restrict_eq`).  Consequently:

* `nsComparison_ikebeKato` — the comparison operator is essentially self-adjoint on
  the finite-mode core, now *via* Faris–Lavine and the maximal-domain analysis,
  and `nsComparison_selfAdjoint_maxDom` on its maximal domain;
* `ns_hamiltonian_essentiallySelfAdjointOn_core` — **the Navier–Stokes Hamiltonian
  of the fiber is essentially self-adjoint on the finite-mode core** as soon as it
  obeys the two Faris–Lavine inequalities relative to `n`.  Nothing else is
  assumed: the Faris–Lavine criterion is the theorem
  `BookProof.FarisLavine.essentiallySelfAdjointOn_core_of_farisLavine` and the
  Ikebe–Kato-type input is proved.

**2. The Fock space.**  In the momentum representation the bosonic Fock space over
the fiber is `ℓ²` over the set `Config = ℕ →₀ ℕ` of occupation-number
configurations, and the second quantization `N̂ = dΓ(n) + I` is again a
*multiplication* operator, by the total-energy symbol
`Σ(α) = ∑ₖ α(k) n(k) + 1` (`fockSymbol`).  Hence the whole analysis applies
verbatim with `ι = Config`:

* `fockSymbol_add` — `dΓ` is additive over particles, `fockSymbol_ge_one` — `N̂ ≥ I`;
* `fockComparison_ikebeKato` — the Fock comparison operator is essentially
  self-adjoint on the finite-configuration core;
* `fock_ns_hamiltonian_essentiallySelfAdjointOn_core` and its deficiency-predicate
  form `fock_ns_hamiltonian_hasZeroDeficiencyOn` — **the second-quantized
  Navier–Stokes Hamiltonian is essentially self-adjoint** on that core, given the
  two Faris–Lavine inequalities.

## What is and is not claimed

The two Faris–Lavine inequalities (`hrel`, `hcomm`) remain hypotheses on the
Hamiltonian: they are the statements that the Navier–Stokes Hamiltonian is
`N`-bounded and that its form commutator with `N` is `N`-dominated, and they are
not verified here for any continuum operator.  Everything else on the route —
the criterion itself and the Ikebe–Kato-type input — is proved.  Global existence
for the Navier–Stokes equation is not claimed anywhere.

Note also that the *earlier* rendering of the criterion in
`BookProof.ChapterNavierStokesFlow` (relative bound plus commutator bound, with no
positivity and no surjectivity of `N + 1`) is refutable —
`BookProof.FarisLavine.not_farisLavine_criterion_of_relative_bound` — which is
precisely why the theorems below are stated with the maximal domain of a
non-negative symbol.
-/

namespace BookProof.NavierStokesFlow

namespace MomentumEsa

open LpNat FarisLavine IkebeKato FarisLavineLift DiagonalEsa

/-! ## Transfer to the deficiency predicate of the Navier–Stokes chapters -/

variable {ι : Type*}



/-! ## One particle: the Navier–Stokes comparison symbol -/

/-- The classical symbol of the one-particle comparison operator
`n = ∑ᵢ πᵢ² + ∑ᵢ Vᵢ² + I` in the momentum representation: `πᵢ` is multiplication
by the momentum symbol `pᵢ`, `Vᵢ` multiplication by the advection symbol `qᵢ`. -/
def nsSymbol (d : ℕ) (p q : Fin d → ℕ → ℝ) : ℕ → ℝ :=
  fun k => (∑ i, p i k ^ 2) + (∑ i, q i k ^ 2) + 1















/-! ## The Fock space in the occupation-number representation -/

/-- An occupation-number configuration of the fiber momentum modes: finitely many
modes are occupied, each by finitely many particles.  `ℓ²(Config)` is the bosonic
Fock space over the fiber `ℓ²(ℕ)` in the momentum representation. -/
abbrev Config := ℕ →₀ ℕ

/-- **The second quantization `N̂ = dΓ(n) + I` is a multiplication operator** in
the occupation-number representation, by the total-energy symbol
`Σ(α) = ∑ₖ α(k) n(k) + 1`. -/
def fockSymbol (n : ℕ → ℝ) : Config → ℝ := fun a => (a.sum fun k m => (m : ℝ) * n k) + 1





















/-- The Navier–Stokes instance of the Fock symbol: the second quantization of the
fiber comparison operator `n = ∑ᵢ πᵢ² + ∑ᵢ Vᵢ² + I`. -/
noncomputable def nsFockSymbol (d : ℕ) (p q : Fin d → ℕ → ℝ) : Config → ℝ :=
  fockSymbol (nsSymbol d p q)





end MomentumEsa

end BookProof.NavierStokesFlow


