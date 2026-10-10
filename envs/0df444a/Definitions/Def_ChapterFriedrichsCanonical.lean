-- Prove2me | Definitions.Def_ChapterFriedrichsCanonical
-- name    : ChapterFriedrichsCanonical
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-10T07:16:30.060988+00:00
-- url     : https://prove2.me/theorems/2fa36ea6-cf03-474e-803d-81c3a5a77332
-- title:
--   The Lean 4 theorem `quadForm_shift` in the `?` chapter of the timepiece formalization
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterFriedrichsCanonical.lean`): generated def bundle for ChapterFriedrichsCanonical. See BookProof/ChapterFriedrichsCanonical.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterFriedrichsCanonical.lean

import Theorems.Thm_BookProof_QgHermiteFriedrichs_continuous_scalaronW

import Theorems.Thm_BookProof_QgHermiteFriedrichs_expBounded_scalaronW

import Theorems.Thm_BookProof_QgHermiteFriedrichs_hamCore_quadForm_nonneg

import Theorems.Thm_BookProof_QgHermiteFriedrichs_hamCore_symmetricOn

import Theorems.Thm_BookProof_QgHermiteFriedrichs_scalaronW_nonneg

import Theorems.Thm_BookProof_Starobinsky_starobinskyV_nonneg


import Theorems.Thm_BookProof_QgHermiteCore_continuous_scalaronSectorPotential

import Theorems.Thm_BookProof_QgHermiteCore_expBounded_scalaronSectorPotential

import Theorems.Thm_BookProof_QgHermiteFriedrichs_hamCore_quadForm_ge






import Theorems.Thm_BookProof_HashimotoShiftInvert_ell2Example_isPositiveSelfAdjointExtension

import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterQgHermiteFriedrichs
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Mathlib


/-!
# The Friedrichs extension is **canonical**

`BookProof.ChapterFriedrichsExtension` proves the *existence* half of the
Friedrichs theorem: a densely defined positive symmetric operator `H` on a
complex Hilbert space has a positive self-adjoint extension, constructed as
`A_F = S⁻¹ − 1` for the form resolvent `S = (H + 1)⁻¹`
(`friedrichs_extension_exists`).  What that statement does *not* say is *which*
extension it is — and a symmetric operator generally has many.

This module supplies the missing half, the one that makes the Friedrichs
extension **the canonical self-adjoint realization**:

* the construction is packaged as a *named* operator rather than an existential:
  `friedrichsDomain P`, `friedrichsOp P hdense`, with
  `friedrichsOp_isPositiveSelfAdjointExtension` re-proving the existence
  statement for it;
* `formDomain P` — the range of the embedding of the form completion, i.e. the
  *form domain* `Q(H)` — contains the domain of `H` (`dom_le_formDomain`) and the
  Friedrichs domain (`friedrichsDomain_le_formDomain`);
* **`friedrichs_canonical`**: *every* symmetric extension of `H` whose domain is
  contained in the form domain is a restriction of `A_F`.  So `A_F` is the
  largest such extension;
* **`friedrichs_unique_selfAdjoint`**: consequently `A_F` is the **unique**
  self-adjoint extension of `H` with domain inside the form domain — the
  classical characterization of the Friedrichs extension (Reed–Simon Vol. II,
  Thm X.23; Kato, Thm VI.2.11).  Both the domain and the action are pinned down.

The named instance is the one `CONSOLIDATED_PLAN.md` §10.6.1 asks about: the
quantum-gravity one-particle scalaron Hamiltonian `−Δ + V(φ)` on the
Gauss–polynomial (Hermite) core of `L²(ℝ)` has a *canonical* self-adjoint
realization (`qgOneParticleHermite_friedrichs_canonical`,
`qgOneParticleHermite_friedrichs_unique`).

**Honest boundary.**  Uniqueness *among extensions with domain in the form
domain* is not essential self-adjointness: an operator that is not essentially
self-adjoint still has other self-adjoint extensions, whose domains necessarily
leave `Q(H)`.  Nothing here claims otherwise.
-/

namespace BookProof.FriedrichsCanonical

open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.HashimotoShiftInvert
open BookProof.FriedrichsExtension BookProof.FriedrichsExtension.FormDom

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-! ## The form domain and the Friedrichs operator, as named objects -/

/-- **The form domain `Q(H)`**: the image in `F` of the completion of `dom H` in
the form norm `‖x‖₁² = ‖x‖² + ⟪x, Hx⟫`.  The embedding is injective
(`formExt_injective`), so this really is a copy of the form completion inside
`F`. -/
def formDomain (P : PosSymOp F) : Submodule ℂ F :=
  LinearMap.range (formExt P : FormSpace P →ₗ[ℂ] F)







/-- **The domain of the Friedrichs extension**: the range of the form resolvent
`S = (H + 1)⁻¹`. -/
def friedrichsDomain (P : PosSymOp F) : Submodule ℂ F :=
  LinearMap.range (friedrichsResolvent P : F →ₗ[ℂ] F)





/-- **The Friedrichs extension of `P`**, as a named operator: `A_F = S⁻¹ − 1`. -/
def friedrichsOp (P : PosSymOp F) (hdense : Dense (P.dom : Set F)) :
    friedrichsDomain P →ₗ[ℂ] F :=
  invShiftOperator (friedrichsResolvent P) (friedrichsResolvent_injective P hdense) 1









/-! ## The vanishing criterion in the form space -/



/-! ## Canonicity -/





/-! ## The classical (merely semibounded) statement -/

section Semibounded

variable {D : Submodule ℂ F}

omit [CompleteSpace F] in
/-- Shifting an operator by a real constant shifts its quadratic form. -/
theorem quadForm_shift (H : D →ₗ[ℂ] F) (c : ℝ) (x : D) :
    quadForm (H + (c : ℂ) • D.subtype) x = quadForm H x + c * ‖(x : F)‖ ^ 2 := by
  simp only [quadForm, LinearMap.add_apply, LinearMap.smul_apply, Submodule.subtype_apply,
    inner_add_right, inner_smul_right, Complex.add_re]
  congr 1
  rw [inner_self_eq_norm_sq_to_K]
  simp [← Complex.ofReal_pow]

omit [CompleteSpace F] in
theorem symmetricOn_shift {H : D →ₗ[ℂ] F} (hsym : SymmetricOn D H) (c : ℝ) :
    SymmetricOn D (H + (c : ℂ) • D.subtype) := by
  intro x y
  simp only [LinearMap.add_apply, LinearMap.smul_apply, Submodule.subtype_apply,
    inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
  rw [hsym x y]

/-- **The shift `H + c` of a symmetric operator bounded below by `−c`**, as a
positive symmetric operator: the object the Friedrichs machinery consumes. -/
def shiftedPosSymOp (H : D →ₗ[ℂ] F) (hsym : SymmetricOn D H) (c : ℝ)
    (hbelow : ∀ x : D, -c * ‖(x : F)‖ ^ 2 ≤ quadForm H x) : PosSymOp F where
  dom := D
  op := H + (c : ℂ) • D.subtype
  sym := symmetricOn_shift hsym c
  pos := by
    intro x
    rw [quadForm_shift]
    linarith [hbelow x]





/-- **The Friedrichs extension of a merely semibounded symmetric operator**:
`A_F − c`, for the Friedrichs extension of the positive shift `H + c`. -/
def semiboundedFriedrichsOp (H : D →ₗ[ℂ] F) (hsym : SymmetricOn D H) (c : ℝ)
    (hbelow : ∀ x : D, -c * ‖(x : F)‖ ^ 2 ≤ quadForm H x) (hdense : Dense (D : Set F)) :
    friedrichsDomain (shiftedPosSymOp H hsym c hbelow) →ₗ[ℂ] F :=
  friedrichsOp (shiftedPosSymOp H hsym c hbelow) hdense
    - (c : ℂ) • (friedrichsDomain (shiftedPosSymOp H hsym c hbelow)).subtype





end Semibounded

end

/-! ## The quantum-gravity instance -/

section QG

open BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs BookProof.HermiteProductCore

noncomputable section

/-- The scalaron Hamiltonian on the Gauss–polynomial (Hermite) core, bundled as a
positive symmetric operator. -/
def qgScalaronPosSymOp (M alpha : ℝ) (hM : 0 < M) (halpha : 0 < alpha) :
    PosSymOp (L2d 1) where
  dom := polyGaussCore
  op := hamCore (scalaronW M alpha) (continuous_scalaronW M alpha) (expBounded_scalaronW M alpha hM)
  sym := hamCore_symmetricOn _ _ _
  pos := hamCore_quadForm_nonneg _ _ _ (scalaronW_nonneg halpha)







/-! ### The reduced two-variable sector `(R_c, φ)` -/

/-- The lower bound of the reduced-sector potential: the conformal-mode
polynomial supplies `−c` and the scalaron part is nonnegative. -/
theorem scalaronSectorPotential_lower (M alpha : ℝ) (halpha : 0 < alpha) (V3 : Polynomial ℝ)
    (c : ℝ) (hV3 : ∀ t : ℝ, -c ≤ V3.eval t) (x : Vd 2) :
    -c ≤ scalaronSectorPotential M alpha V3 x := by
  have h1 := hV3 (x 0)
  have h2 := BookProof.Starobinsky.starobinskyV_nonneg (M := M) halpha (x 1)
  simp only [scalaronSectorPotential]
  linarith

/-- The reduced `(R_c, φ)` sector Hamiltonian on the Hermite core, shifted by its
lower bound so as to be positive. -/
def qgSectorShiftedPosSymOp (M alpha : ℝ) (hM : 0 < M) (halpha : 0 < alpha)
    (V3 : Polynomial ℝ) (c : ℝ) (hV3 : ∀ t : ℝ, -c ≤ V3.eval t) : PosSymOp (L2d 2) :=
  shiftedPosSymOp
    (hamCore (scalaronSectorPotential M alpha V3) (continuous_scalaronSectorPotential M alpha V3)
      (expBounded_scalaronSectorPotential M alpha hM V3))
    (hamCore_symmetricOn _ _ _) c
    (hamCore_quadForm_ge _ _ _ c (scalaronSectorPotential_lower M alpha halpha V3 c hV3))

/-- The Friedrichs realization of the reduced-sector Hamiltonian. -/
def qgSectorFriedrichsOp (M alpha : ℝ) (hM : 0 < M) (halpha : 0 < alpha)
    (V3 : Polynomial ℝ) (c : ℝ) (hV3 : ∀ t : ℝ, -c ≤ V3.eval t) :
    friedrichsDomain (qgSectorShiftedPosSymOp M alpha hM halpha V3 c hV3) →ₗ[ℂ] L2d 2 :=
  semiboundedFriedrichsOp
    (hamCore (scalaronSectorPotential M alpha V3) (continuous_scalaronSectorPotential M alpha V3)
      (expBounded_scalaronSectorPotential M alpha hM V3))
    (hamCore_symmetricOn _ _ _) c
    (hamCore_quadForm_ge _ _ _ c (scalaronSectorPotential_lower M alpha halpha V3 c hV3))
    polyGaussCore_dense





end

end QG

/-! ## The canonicity theorem is not vacuous -/

noncomputable section Example

open BookProof.HermiteGalerkin
open scoped lp

/-- The genuinely unbounded diagonal operator `A eₙ = n eₙ` on `ℓ²(ℕ, ℂ)`, on the
finite-mode domain, as a positive symmetric operator. -/
def ell2ExamplePosSymOp : PosSymOp (ℓ²(ℕ, ℂ)) where
  dom := finiteModeDomain ell2Basis
  op := ell2ExampleMatrix
  sym := by
    obtain ⟨-, hsym, -, -⟩ := ell2Example_isPositiveSelfAdjointExtension
    intro x y
    exact hsym ⟨(x : ℓ²(ℕ, ℂ)), finiteModeDomain_le_range x.2⟩
      ⟨(y : ℓ²(ℕ, ℂ)), finiteModeDomain_le_range y.2⟩
  pos := by
    obtain ⟨-, -, hpos, -⟩ := ell2Example_isPositiveSelfAdjointExtension
    intro x
    exact hpos ⟨(x : ℓ²(ℕ, ℂ)), finiteModeDomain_le_range x.2⟩



end Example

end BookProof.FriedrichsCanonical


