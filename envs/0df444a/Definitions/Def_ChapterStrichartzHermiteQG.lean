-- Prove2me | Definitions.Def_ChapterStrichartzHermiteQG
-- name    : ChapterStrichartzHermiteQG
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-04T17:08:51.302057+00:00
-- url     : https://prove2.me/theorems/4b4216ff-fd3d-45a4-8eaf-00206495387d
-- title:
--   The Lean 4 theorem `hermiteLp_mem_hermiteDiagDomain` in the `?` chapter of the timepiece formalization
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterStrichartzHermiteQG.lean`): generated def bundle for ChapterStrichartzHermiteQG. See BookProof/ChapterStrichartzHermiteQG.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterStrichartzHermiteQG.lean

import Theorems.Thm_BookProof_HermiteCore_hermiteBasis_apply


import Definitions.Def_ChapterHermiteFunctions
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterQuantumGravityDensitized
import Mathlib


/-!
# The Hermite core, and a Strichartz-type theorem on it

This chapter joins the two strands of the project.

`BookProof.ChapterHermiteFunctions` builds the genuine Hermite orthonormal basis
`hermiteBasis` of `L²(ℝ)` (orthogonality, completeness via Fourier uniqueness,
and the harmonic-oscillator eigenvalue equation).  This chapter defines the
**Hermite core**

`hermiteCore = span_ℂ { ψ₀, ψ₁, ψ₂, … } ⊆ L²(ℝ)`,

the finite linear combinations of Hermite functions — i.e. the polynomials times
the Gaussian `e^{-x²/4}` — and proves that a **diagonal operator** in the Hermite
basis, with an arbitrary real symbol `lam : ℕ → ℝ`, is

* symmetric on the core (`hermiteCoreOp_symmetric`),
* has **trivial deficiency at every non-real `z`** (`hermiteCoreOp_deficiencyTrivialAt`),
  which is precisely the Strichartz "finite speed / unique continuation" input, and
* is therefore **essentially self-adjoint on the core**
  (`hermiteCoreOp_essentiallySelfAdjoint`), via the *proved* route
  `BookProof.QuantumGravityDensitized.strichartz_esa_of_finiteSpeed`.

The core is dense (`hermiteCore_dense`), so this is a genuine essential
self-adjointness statement, and the operator is genuinely unbounded whenever the
symbol is (`hermiteCoreOp_not_bounded`).

Finally the result is instantiated with the **3D gauge-fixed quantum-gravity mode
symbol**: after gauge fixing and densitization, the principal symbol of the
gravity Hamiltonian is the hyperbolic form
`qgSymbol ξ ξ_y = (1/16) Σ_{a<3} ξ_a² − (1/24) ξ_y²`
of `BookProof.ChapterQuantumGravityDensitized`, and mode by mode one gets
`qg3DModeSymbol`.  The conclusion is
`qg3D_essentiallySelfAdjoint_on_hermiteCore`: the 3D gauge-fixed quantum-gravity
mode Hamiltonian is essentially self-adjoint on the Hermite core of `L²(ℝ)`.
-/

namespace BookProof.HermiteStrichartzQG

open MeasureTheory BookProof.HermiteCore BookProof.FarisLavine
open BookProof.QuantumGravityDensitized

/-- `L²(ℝ)` with the Lebesgue measure. -/
noncomputable abbrev L2R := Lp ℂ 2 (volume : Measure ℝ)

/-- The unitary `L²(ℝ) ≃ ℓ²(ℕ)` given by the Hermite basis. -/
noncomputable def hermiteRepr : L2R ≃ₗᵢ[ℂ] L2Nat := hermiteBasis.repr

@[simp] theorem hermiteRepr_hermiteLp (n : ℕ) :
    hermiteRepr (hermiteLp n) = lp.single 2 n (1 : ℂ) := by
  rw [hermiteRepr, ← hermiteBasis_apply, HilbertBasis.repr_self]

@[simp] theorem hermiteRepr_symm_single (n : ℕ) :
    hermiteRepr.symm (lp.single 2 n (1 : ℂ)) = hermiteLp n := by
  rw [hermiteRepr, HilbertBasis.repr_symm_single, hermiteBasis_apply]



/-! ## The Hermite core -/

/-- **The Hermite core**: the finite linear combinations of Hermite functions,
i.e. the polynomials times the Gaussian `e^{-x²/4}`, as a submodule of `L²(ℝ)`. -/
noncomputable def hermiteCore : Submodule ℂ L2R := Submodule.span ℂ (Set.range hermiteLp)





/-! ## Diagonal operators in the Hermite basis -/

/-- The maximal domain of the diagonal operator with symbol `lam`: the `L²`
functions whose Hermite coefficients stay square-summable after multiplication
by `lam`. -/
noncomputable def hermiteDiagDomain (lam : ℕ → ℝ) : Submodule ℂ L2R :=
  Submodule.comap (hermiteRepr.toLinearEquiv.toLinearMap) (mulSymbolDomain lam)

/-- The restriction of the unitary to the two domains. -/
noncomputable def hermiteDiagRestrict (lam : ℕ → ℝ) :
    hermiteDiagDomain lam →ₗ[ℂ] mulSymbolDomain lam where
  toFun f := ⟨hermiteRepr (f : L2R), f.2⟩
  map_add' f g := by ext n; simp
  map_smul' c f := by ext n; simp

/-- **The diagonal operator with real symbol `lam` in the Hermite basis**,
on its maximal domain: it multiplies the `n`-th Hermite coefficient by `lam n`. -/
noncomputable def hermiteDiagOp (lam : ℕ → ℝ) : hermiteDiagDomain lam →ₗ[ℂ] L2R :=
  hermiteRepr.symm.toLinearEquiv.toLinearMap ∘ₗ
    ((mulHamiltonian lam) ∘ₗ hermiteDiagRestrict lam)

theorem hermiteLp_mem_hermiteDiagDomain (lam : ℕ → ℝ) (n : ℕ) :
    hermiteLp n ∈ hermiteDiagDomain lam := by
  have h : (hermiteRepr.toLinearEquiv.toLinearMap (hermiteLp n) : L2Nat)
      = ((mulBasis lam n : mulSymbolDomain lam) : L2Nat) := by
    simp [mulBasis]
  rw [hermiteDiagDomain, Submodule.mem_comap, h]
  exact (mulBasis lam n).2

theorem hermiteCore_le_hermiteDiagDomain (lam : ℕ → ℝ) :
    hermiteCore ≤ hermiteDiagDomain lam := by
  rw [hermiteCore, Submodule.span_le]
  rintro _ ⟨n, rfl⟩
  exact hermiteLp_mem_hermiteDiagDomain lam n

/-- **The diagonal operator restricted to the Hermite core.** -/
noncomputable def hermiteCoreOp (lam : ℕ → ℝ) : hermiteCore →ₗ[ℂ] L2R :=
  (hermiteDiagOp lam) ∘ₗ Submodule.inclusion (hermiteCore_le_hermiteDiagDomain lam)



/-! ## Symmetry, deficiency, essential self-adjointness -/











/-! ## The harmonic oscillator on the Hermite core -/

/-- The harmonic-oscillator symbol `n + 1/2`. -/
noncomputable def oscillatorSymbol (n : ℕ) : ℝ := (n : ℝ) + 1 / 2







/-! ## The 3D gauge-fixed quantum-gravity Hamiltonian -/

/-- The **3D gauge-fixed quantum-gravity mode symbol**: mode by mode, the
hyperbolic principal symbol `qgSymbol` of the densitized, gauge-fixed gravity
Hamiltonian in three spatial dimensions, plus a real potential. -/
noncomputable def qg3DModeSymbol (xi : ℕ → Fin 3 → ℝ) (xiY V : ℕ → ℝ) (k : ℕ) : ℝ :=
  qgSymbol (xi k) (xiY k) + V k

/-- The 3D gauge-fixed quantum-gravity Hamiltonian on the Hermite core of
`L²(ℝ)`. -/
noncomputable def qg3DHermiteHamiltonian (xi : ℕ → Fin 3 → ℝ) (xiY V : ℕ → ℝ) :
    hermiteCore →ₗ[ℂ] L2R :=
  hermiteCoreOp (qg3DModeSymbol xi xiY V)











end BookProof.HermiteStrichartzQG


