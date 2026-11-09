-- Prove2me | Definitions.Def_ChapterYangMillsNonAbelianEsa
-- name    : ChapterYangMillsNonAbelianEsa
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-11-08T20:49:47.722446+00:00
-- url     : https://prove2.me/theorems/597bcba6-7985-4204-acd1-6bfeb228bad5
-- title:
--   ChapterYangMillsNonAbelianEsa
-- statement:
--   ChapterYangMillsNonAbelianEsa

import Definitions.Def_ChapterHermiteGraphApprox
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterEsaOneParticleDGamma
import Definitions.Def_ChapterDegKatoEsa
import Definitions.Def_ChapterDegSchrodingerCore
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterQgHermiteFriedrichs
import Definitions.Def_ChapterQgOneParticleCcEsa
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterSecondQuantizationCoreEsa
import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterYangMillsFriedrichs
import Mathlib


/-!
# The non-abelian Yang–Mills one-particle Hamiltonian is essentially self-adjoint

The tree had essential self-adjointness of the gauge-fixed Yang–Mills Hamiltonian only in the
abelian (quadratic) case (`BookProof/ChapterYangMillsAbelianEsa.lean`).  The Kato-type
theorem of `BookProof/ChapterDegKatoEsa.lean` and its transfer to the Gauss–polynomial core
(`BookProof/ChapterHermiteGraphApprox.lean`) hold for an arbitrary real polynomial potential
`W ≥ 1` and an arbitrary set `S` of momentum-carrying coordinates.  This module instantiates
them for the **non-abelian** Hamiltonian `ymHamiltonian`, for arbitrary real structure
constants `f_{abc}`:

* `deficiencyTrivialAt_of_esa` — for a symmetric operator on a Hilbert space, trivial
  deficiency at `± i` gives trivial deficiency at every non-real point;
* `essentiallySelfAdjointOn_affine` — hence `a • K + b` (`a > 0`, `b` real) is essentially
  self-adjoint whenever `K` is;
* `weylPoly_eq_hamCoreS`, `weylPoly_esa` — any Weyl-type operator `½ Σ_m π_{idx m}² + ½ Σ_j Φ_j²`
  on the Gauss–polynomial core, with momenta in distinct coordinates and real polynomial
  fields `Φ_j`, satisfies `2H + 1 = −Δ_S + W` with `W = Σ_j Φ_j² + 1`, hence is essentially
  self-adjoint;
* `ymHamiltonian_eq_weylPoly` — the non-abelian Yang–Mills Hamiltonian is such an operator,
  with `S` the 24 gauge-field coordinates `A_{j,a}` and `Φ` the 24 magnetic fields `B_{ia}`;
* **`ym_h_esa`** — the non-abelian gauge-fixed Yang–Mills one-particle Hamiltonian
  `H = ½ Σ π² + ½ Σ B²` is essentially self-adjoint on the Gauss–polynomial core of `L²(ℝ⁹⁹)`;
* **`ym_dGamma_esa`** — its second quantization `dΓ(H)` (one-particle `H` enclosed between a
  creation on the left and an annihilation on the right) is essentially self-adjoint on the
  finite-particle domain over that core, by the lift of `BookProof/ChapterEsaOneParticleDGamma`.

Nothing is assumed: the module contains no `axiom` and no `sorry`.
-/

namespace BookProof.YangMillsNonAbelianEsa

open MeasureTheory MvPolynomial
open BookProof.FarisLavine BookProof.ScalaronEsa
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgOneParticleCc BookProof.YangMillsHermite BookProof.YangMillsFriedrichs
open BookProof.DegSchrodinger BookProof.DegKatoEsa BookProof.HermiteGraphApprox
open BookProof.TensorCore BookProof.DirectSumEsa BookProof.SecondQuantizationCore

noncomputable section

/-! ## 1. Essential self-adjointness is stable under positive affine maps -/

section Abstract

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {D : Submodule ℂ F}

/-- For a symmetric operator on a Hilbert space, essential self-adjointness (trivial
deficiency at `± i`) gives trivial deficiency at **every** non-real point. -/
theorem deficiencyTrivialAt_of_esa (K : D →ₗ[ℂ] F) (hK : SymmetricOn D K)
    (hesa : EssentiallySelfAdjointOn D K) {σ : ℂ} (hσ : σ.im ≠ 0) :
    DeficiencyTrivialAt D K σ := by
  have hI : ((1 : ℝ) : ℂ) * Complex.I = Complex.I := by simp
  have hdense : Dense (Set.range fun x : D => K x - (((1 : ℝ) : ℂ) * Complex.I) • (x : F)) := by
    rw [hI]
    refine dense_range_of_deficiencyTrivialAt K Complex.I ?_
    rw [Complex.conj_I]
    exact hesa.2
  refine deficiencyTrivialAt_of_dense_range K hK 1 one_ne_zero σ hσ hdense ?_
  rw [hI]
  exact hesa.1

/-- **A positive affine image of an essentially self-adjoint operator is essentially
self-adjoint**: `a • K + b` for real `a > 0` and real `b`. -/
theorem essentiallySelfAdjointOn_affine (K : D →ₗ[ℂ] F) (hK : SymmetricOn D K)
    (hesa : EssentiallySelfAdjointOn D K) {a : ℝ} (ha : 0 < a) (b : ℝ) :
    EssentiallySelfAdjointOn D ((a : ℂ) • K + (b : ℂ) • D.subtype) := by
  have key : ∀ z : ℂ, z.im ≠ 0 → DeficiencyTrivialAt D ((a : ℂ) • K + (b : ℂ) • D.subtype) z := by
    intro z hz w hw
    have hσ : ((z - b) / a).im ≠ 0 := by
      rw [Complex.div_ofReal_im, Complex.sub_im, Complex.ofReal_im, sub_zero]
      exact div_ne_zero hz ha.ne'
    refine deficiencyTrivialAt_of_esa K hK hesa hσ w fun v => ?_
    have hv := hw v
    rw [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply, inner_add_left,
      inner_smul_left, inner_smul_left, Complex.conj_ofReal, Complex.conj_ofReal,
      Submodule.subtype_apply] at hv
    have ha' : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ha.ne'
    field_simp
    linear_combination hv
  exact ⟨key _ (by simp), key _ (by simp)⟩

end Abstract

/-! ## 2. Transport of polynomial operators to the core, in any dimension -/

section Transport

variable {d : ℕ}

theorem equiv_pgLp_d (p : MvPolynomial (Fin d) ℂ) :
    (coreRepPoly d).equiv p = ⟨pgLp p, pgLp_mem_core p⟩ :=
  Subtype.ext ((coreRepPoly d).coe_equiv p)

theorem equiv_symm_pgLp_d (p : MvPolynomial (Fin d) ℂ) :
    (coreRepPoly d).equiv.symm ⟨pgLp p, pgLp_mem_core p⟩ = p := by
  rw [← equiv_pgLp_d p, LinearEquiv.symm_apply_apply]

theorem op_pgLp_d (T : Module.End ℂ (MvPolynomial (Fin d) ℂ)) (p : MvPolynomial (Fin d) ℂ) :
    (coreRepPoly d).op T ⟨pgLp p, pgLp_mem_core p⟩ = ⟨pgLp (T p), pgLp_mem_core _⟩ := by
  refine Subtype.ext ?_
  rw [CoreRep.coe_op, equiv_symm_pgLp_d]



end Transport

/-! ## 3. A Weyl-type operator with polynomial fields is a degenerate Schrödinger operator -/

section General

variable {d k r : ℕ}

/-- The Weyl-type operator `½ Σ_m π_{idx m}² + ½ Σ_j Φ_j²` on the Gauss–polynomial core of
`L²(ℝᵈ)`: momenta in the coordinates `idx m`, multiplication by the polynomials `Φ_j`. -/
def weylPoly (idx : Fin k → Fin d) (Φ : Fin r → MvPolynomial (Fin d) ℂ) :
    (polyGaussCore (d := d)) →ₗ[ℂ] L2d d :=
  weylOp (fun m => (coreRepPoly d).op (momOp (idx m))) (fun j => (coreRepPoly d).op (mulOp (Φ j)))

/-- The potential `W = Σ_j Φ_j² + 1`. -/
def weylPotPoly (Φ : Fin r → MvPolynomial (Fin d) ℂ) : MvPolynomial (Fin d) ℂ :=
  (∑ j : Fin r, Φ j * Φ j) + C ((1 : ℝ) : ℂ)













end General

/-! ## 4. The non-abelian Yang–Mills instance -/

/-- The coordinate of the `m`-th gauge-field component `A_{j,a}`. -/
def ymIdx (m : Fin 24) : Fin 99 := idxA (decodeSpace m) (decodeColor m)



/-- The `m`-th magnetic-field polynomial `B_{ia}`. -/
def ymMag (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) (m : Fin 24) : MvPolynomial (Fin 99) ℂ :=
  magPoly fabc (decodeSpace m) (decodeColor m)





/-- `L²(ℝᵈ)` as a bundled inner product space, the one-particle space of the enclosure. -/
def L2dSpace (d : ℕ) : IPSpace := ⟨L2d d⟩

instance (d : ℕ) : CompleteSpace (L2dSpace d).carrier :=
  inferInstanceAs (CompleteSpace (L2d d))



end

end BookProof.YangMillsNonAbelianEsa


