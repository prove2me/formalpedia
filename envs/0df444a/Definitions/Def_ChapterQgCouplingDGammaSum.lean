-- Prove2me | Definitions.Def_ChapterQgCouplingDGammaSum
-- name    : ChapterQgCouplingDGammaSum
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-15T20:18:34.258992+00:00
-- url     : https://prove2.me/theorems/4a92d4de-b051-423d-aa64-9b373c9c3315
-- title:
--   Chapter ChapterQgCouplingDGammaSum
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.QgCouplingDGammaSum`, source chapter `BookProof/ChapterQgCouplingDGammaSum.lean`): Chapter ChapterQgCouplingDGammaSum
--
--   Generated def bundle for ChapterQgCouplingDGammaSum. See BookProof/ChapterQgCouplingDGammaSum.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgCouplingDGammaSum.lean

import Definitions.Def_ChapterFockSecondQuantization
import Mathlib
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterYangMillsFriedrichs


/-!
# QG-3.2 operator track — a sum of second quantizations in *differing* bases

`DESIGN_QG32_FARISLAVINE_DIFFERING_BASES.md` (plan item **QG-3.2-exec (i)** of
`CONSOLIDATED_PLAN.md`) asks for the essential self-adjointness of the lifted
coupling

```text
H_coup = Σ_ℓ dΓ(h_ℓ),
```

where the one-particle operators `h_ℓ` are positive and self-adjoint but each
diagonalizable **in its own basis**.  The design's worry is that a naive
common-alphabet rendering has to sum the pulled-back matrices
`Σ_ℓ (U_ℓ† h_ℓ U_ℓ)(p,q)` and then postulate a weighted-`ℓ¹` gate on the
resulting dense matrix — a gate that can fail precisely because the bases
differ.

This module removes that gate.  The four structural facts it proves are

* `dGamma_finsetSum_col` / `dGammaOp_finsetSum_col` — **second quantization is
  linear in the one-particle datum**: `Σ_ℓ dΓ(h_ℓ) = dΓ(Σ_ℓ h_ℓ)` on the
  finite-occupation core.  So the coupling sum is *one* second-quantized
  operator, and no common-alphabet summability gate is involved;
* `isHermCol_finsetSum`, `isPosCol_finsetSum`, `coupling_friedrichs` — the
  summed one-particle datum is again Hermitian and positive semidefinite, so
  the coupling has a positive self-adjoint (Friedrichs) extension
  unconditionally (the comparison operator of stage 2 of the design);
* `comparisonCol`, `comparison_friedrichs`, `coupling_quadForm_le`,
  `coupling_quadForm_le_comparison` — the Faris–Lavine comparison operator
  `N = Σ_ℓ dΓ(h_ℓ) + 𝒩` is positive self-adjoint (Friedrichs) and dominates
  every summand in the form sense (the relative form bound, stage 3), and
  `commForm_finsetSum` — the commutator form of a sum is the sum of the
  commutator forms (stage 4);
* `numberOp_essentiallySelfAdjoint` — the number operator `𝒩 = dΓ(1)` is
  essentially self-adjoint on the finite-occupation core;
* `coupling_esa_dGamma` — the **headline** (stage 6): if the *total*
  one-particle operator is diagonal in the working basis with non-negative
  eigenvalues `lam` (equivalently: the sum, not the individual summands, is
  diagonalized by the alphabet), then `Σ_ℓ dΓ(h_ℓ)` is essentially
  self-adjoint on the finite-occupation core.  The individual `h_ℓ` are never
  required to share a basis, and no `ℓ¹` gate on cross-basis matrix elements
  is assumed.

The bridge to the diagonal case is `dGammaOp_diagCol_eq`: over a basis
diagonalizing the total one-particle operator, `dΓ` is multiplication by the
occupation energy `occEnergy lam α = Σ_k lam k · α k` on `ℓ²(Conf)`, whose
essential self-adjointness on the finite-occupation core is
`BookProof.NavierStokesFlow.IkebeKato.ikebeKato_momentum`.

## Honest boundary

The diagonalizability of the *total* one-particle operator is a genuine
hypothesis: a positive symmetric one-particle operator need not have an
orthonormal eigenbasis, and `dΓ` of an arbitrary positive Hermitian matrix need
not be essentially self-adjoint on the finite-occupation core (only the
Friedrichs extension, `coupling_friedrichs`, is unconditional).  What is
removed here is the *differing-bases* obstruction: nothing is assumed about the
individual summands or about cross-basis matrix elements.

Everything in this module is `sorry`-free and `axiom`-free.
-/

namespace BookProof.QgCouplingDGammaSum

open BookProof.FockSecondQuantization
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.FriedrichsExtension BookProof.YangMillsFriedrichs

noncomputable section

variable {ι : Type*}

/-! ## 1. Second quantization is linear in the one-particle datum -/















/-! ## 2. Hermiticity and positivity are preserved by the sum -/







/-! ## 3. The relative form bound and the additivity of the commutator form -/







/-! ## 4. The diagonal total: `dΓ` is multiplication by the occupation energy -/

/-- The one-particle matrix of an operator diagonal in the working basis, with
eigenvalues `lam`. -/
def diagCol (lam : ℕ → ℝ) : ℕ → (ℕ →₀ ℂ) := fun k => Finsupp.single k (lam k : ℂ)

/-- The occupation energy of a configuration: `Σ_k lam k · α k`. -/
def occEnergy (lam : ℕ → ℝ) (α : Conf) : ℝ := ∑ k ∈ α.support, lam k * (α k : ℝ)













/-! ## 5. The comparison operator `N = Σ_ℓ dΓ(h_ℓ) + 𝒩` -/





/-- The one-particle datum of the **number operator** `𝒩 = dΓ(1)`. -/
def numberCol : ℕ → (ℕ →₀ ℂ) := diagCol (fun _ => 1)







/-- The one-particle datum of the Faris–Lavine comparison operator
`N = Σ_ℓ h_ℓ + 1` of the design (second quantized: `Σ_ℓ dΓ(h_ℓ) + 𝒩`). -/
def comparisonCol (s : Finset ι) (cols : ι → ℕ → (ℕ →₀ ℂ)) : ℕ → (ℕ →₀ ℂ) :=
  fun k => (∑ i ∈ s, cols i k) + numberCol k











/-! ## 6. The headline: ESA of the coupling sum, bases never reconciled -/





/-! ## 7. Axiom audit

The audit of the eight headline theorems (`dGammaOp_finsetSum_col_eq`, `coupling_friedrichs`,
`coupling_quadForm_le`, `commForm_finsetSum`, `coupling_esa_dGamma`, `comparison_friedrichs`,
`coupling_quadForm_le_comparison`, `numberOp_essentiallySelfAdjoint`) belongs to their own
`Theorems` nodes. Those declarations are not part of this *definition* bundle, and a `#print`
of a name the module does not declare is a hard elaboration error on the platform
(`Unknown constant`), not a warning -- so the commands are not carried over here. -/

end

end BookProof.QgCouplingDGammaSum


