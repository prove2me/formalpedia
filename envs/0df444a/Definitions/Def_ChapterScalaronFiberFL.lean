-- Prove2me | Definitions.Def_ChapterScalaronFiberFL
-- name    : ChapterScalaronFiberFL
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-05T13:10:49.486249+00:00
-- url     : https://prove2.me/theorems/cefe5e2e-c765-4a51-bbfd-f990166e3b2a
-- title:
--   The Lean 4 theorem `pot_smooth` in the `?` chapter of the timepiece formalization
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.ScalaronFiberFL`, source chapter `BookProof/ChapterScalaronFiberFL.lean`): The scalaron fibre: the exponential wall as a Faris–Lavine comparison operator What is proved
--
--   This module prepares the *one-dimensional* input of the quantum-gravity Faris–Lavine programme in the form the outer-Fock lift needs: the scalaron degree of freedom, carrying the **full exponential** Einstein-frame potential (no Taylor expansion), realised as a family of Faris–Lavine comparison operators
--
--   `h_s = −d²/dφ² + φ²/4 + V(φ) + s`, `s ≥ 0`,
--
--   on `L²(ℝ)`, together with the estimates that make the fibre usable inside a lifted Hamiltonian: everything is uniform in the shift `s`.
--
--   * `isGraphCore_of_esa` — an abstract and reusable step: if a symmetric operator `P` on a subspace `C₀` is essentially self-adjoint there, then `C₀` is a **graph core** for *every* comparison operator extending `P`. (Density of the range of `P − i` is exactly the deficiency triviality, and `‖Nu − iu‖² = ‖Nu‖² + ‖u‖²` converts one approximation into a graph approximation.) This is what lets the Friedrichs extension of a positive one-particle operator be used with the core-extension machinery of `BookProof.QgOuterFockCoreFL`. * `integral_weight_re_secondDeriv` — the weighted integration-by-parts identity `∫ P·Re(conj u · u'') = −∫ P|u'|² + ½∫ P''|u|²` for compactly supported smooth `u`. * `wallEnergy_identity` — the resulting energy identity `‖−u'' + P u‖² = ‖u''‖² + ‖P u‖² + 2∫P|u'|² − ∫P''|u|²`. * `WallPot` — the data of an admissible wall: a smooth non-negative potential with `V'' ≤ C(V+1)`. `starobinskyWall` is the Einstein-frame scalaron potential, which satisfies it (`starobinskyV_hess_le`). * `fibHam`, `fibHam_symmetricOn`, `fibHam_quadForm`, `fibHam_pos`, `fibHam_esa` — the fibre Hamiltonian on the compactly supported smooth core, its quadratic form, positivity and essential self-adjointness. * `fibHam_norm_bounds` (`norm_deriv2_le`, `norm_pot_mul_le`, `norm_coord_mul_le`, `norm_deriv_le`, `norm_le_shift`) — the relative bounds of the second derivative, of the potential, of `φ` and of `d/dφ` against `‖(h_s+1)u‖`, **with constants independent of the shift `s`**. * `fibComparison` — the Friedrichs extension of `h_s` as a Faris–Lavine comparison operator, and `fibComparison_isGraphCore`, `fibComparison_core_apply`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterScalaronFiberFL.lean

import Theorems.Thm_BookProof_ScalaronEsa_ccDomain_dense

import Theorems.Thm_BookProof_ScalaronWallEsa_wallHam_symmetricOn

import Theorems.Thm_BookProof_WallEsaSemibounded_kinCcR_quadratic_form

import Theorems.Thm_BookProof_WallEsaSemibounded_opCc_quadratic_form

import Theorems.Thm_BookProof_ScalaronEsa_contDiff_starobinskyV

import Theorems.Thm_BookProof_Starobinsky_starobinskyV_nonneg

import Definitions.Def_ChapterWallEsaBddBelow
import Definitions.Def_ChapterWallEsaSemibounded
import Definitions.Def_ChapterSchrodingerCutoffEsa
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterScalaronWallEsa
import Definitions.Def_ChapterStrichartzWave
import Mathlib


/-!
# The scalaron fibre: the exponential wall as a Faris–Lavine comparison operator

This module prepares the *one-dimensional* input of the quantum-gravity Faris–Lavine
programme in the form the outer-Fock lift needs: the scalaron degree of freedom, carrying
the **full exponential** Einstein-frame potential (no Taylor expansion), realised as a
family of Faris–Lavine comparison operators

`h_s = −d²/dφ² + φ²/4 + V(φ) + s`,  `s ≥ 0`,

on `L²(ℝ)`, together with the estimates that make the fibre usable inside a lifted
Hamiltonian: everything is uniform in the shift `s`.

## What is proved

* `isGraphCore_of_esa` — an abstract and reusable step: if a symmetric operator `P` on a
  subspace `C₀` is essentially self-adjoint there, then `C₀` is a **graph core** for *every*
  comparison operator extending `P`.  (Density of the range of `P − i` is exactly the
  deficiency triviality, and `‖Nu − iu‖² = ‖Nu‖² + ‖u‖²` converts one approximation into a
  graph approximation.)  This is what lets the Friedrichs extension of a positive
  one-particle operator be used with the core-extension machinery of
  `BookProof.QgOuterFockCoreFL`.
* `integral_weight_re_secondDeriv` — the weighted integration-by-parts identity
  `∫ P·Re(conj u · u'') = −∫ P|u'|² + ½∫ P''|u|²` for compactly supported smooth `u`.
* `wallEnergy_identity` — the resulting energy identity
  `‖−u'' + P u‖² = ‖u''‖² + ‖P u‖² + 2∫P|u'|² − ∫P''|u|²`.
* `WallPot` — the data of an admissible wall: a smooth non-negative potential with
  `V'' ≤ C(V+1)`.  `starobinskyWall` is the Einstein-frame scalaron potential, which
  satisfies it (`starobinskyV_hess_le`).
* `fibHam`, `fibHam_symmetricOn`, `fibHam_quadForm`, `fibHam_pos`, `fibHam_esa` — the fibre
  Hamiltonian on the compactly supported smooth core, its quadratic form, positivity and
  essential self-adjointness.
* `fibHam_norm_bounds` (`norm_deriv2_le`, `norm_pot_mul_le`, `norm_coord_mul_le`,
  `norm_deriv_le`, `norm_le_shift`) — the relative bounds of the second derivative, of the
  potential, of `φ` and of `d/dφ` against `‖(h_s+1)u‖`, **with constants independent of the
  shift `s`**.
* `fibComparison` — the Friedrichs extension of `h_s` as a Faris–Lavine comparison
  operator, and `fibComparison_isGraphCore`, `fibComparison_core_apply`.
-/

namespace BookProof.ScalaronFiberFL

open MeasureTheory SchwartzMap
open BookProof.StrichartzWave
open BookProof.FarisLavine BookProof.ScalaronEsa BookProof.ScalaronWallEsa
open BookProof.WallEsaSemibounded BookProof.WallEsaBddBelow
open BookProof.QgOuterFockFL BookProof.QgOuterFockCoreFL
open BookProof.SchrodingerCutoff BookProof.FriedrichsExtension

noncomputable section

/-! ## 1. A graph core from essential self-adjointness -/

section Abstract

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]





end Abstract

/-! ## 2. Integration by parts: the Wronskian identity on the line -/

section Wronskian



end Wronskian

/-! ## 3. The scalaron fibre operator -/

section Fibre

/-- The `L²` space of the scalaron fibre. -/
abbrev L2R := Lp ℂ 2 (volume : Measure ℝ)

/-- An **admissible wall**: a smooth non-negative potential on the line.  The Einstein-frame
scalaron potential of Starobinsky inflation, with the exponential kept in full and no
Taylor expansion, is one — see `starobinskyWall`. -/
structure WallPot where
  /-- The potential. -/
  V : ℝ → ℝ
  /-- It is smooth. -/
  smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V
  /-- It is non-negative. -/
  nonneg : ∀ x, 0 ≤ V x

/-- **The scalaron wall**: the Einstein-frame Starobinsky potential
`M⁴/(16α)·(1 − exp(−√(2/3)·φ/M))²`, with the exponential in full. -/
def starobinskyWall (M alpha : ℝ) (halpha : 0 < alpha) : WallPot where
  V := BookProof.Starobinsky.starobinskyV M alpha
  smooth := BookProof.ScalaronEsa.contDiff_starobinskyV M alpha
  nonneg := fun phi => BookProof.Starobinsky.starobinskyV_nonneg halpha phi

namespace WallPot

variable (W : WallPot) (s : ℝ)

/-- The fibre potential `φ²/4 + V(φ) + s`. -/
def pot : ℝ → ℝ := fun x => x ^ 2 / 4 + (W.V x + s)

theorem pot_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (W.pot s) :=
  ((contDiff_id.pow 2).div_const 4).add (W.smooth.add contDiff_const)

theorem pot_nonneg (hs : 0 ≤ s) (x : ℝ) : 0 ≤ W.pot s x := by
  have h1 : (0 : ℝ) ≤ x ^ 2 / 4 := by positivity
  have h2 := W.nonneg x
  simp only [pot]
  linarith





/-- **The scalaron fibre Hamiltonian** `h_s = −d²/dφ² + φ²/4 + V(φ) + s`, on the compactly
supported smooth core of `L²(ℝ)`. -/
def ham : ccDomain ℝ →ₗ[ℂ] L2R := wallHam (W.pot s) (W.pot_smooth s)

theorem ham_symmetricOn : SymmetricOn (ccDomain ℝ) (W.ham s) :=
  wallHam_symmetricOn _ _



end WallPot

/-! ### The fibre operator on a core element, as a Schwartz function -/

/-- The fibre Hamiltonian, as a map of the compactly supported smooth core into Schwartz
space. -/
def hamS (W : WallPot) (s : ℝ) (f : ccSchwartz ℝ) : 𝓢(ℝ, ℂ) :=
  kinOpR (f : 𝓢(ℝ, ℂ)) + mulCc (W.pot s) (W.pot_smooth s) f





/-- Multiplication by the scalaron field `φ`, on the core. -/
def xCc : ccDomain ℝ →ₗ[ℂ] L2R := opCc (fun x : ℝ => x) contDiff_id



/-- The derivative of a core element, as an element of `L²(ℝ)`. -/
def derivL2 (f : ccSchwartz ℝ) : L2R :=
  (SchwartzMap.derivCLM ℂ ℂ (f : 𝓢(ℝ, ℂ))).toLp 2 (volume : Measure ℝ)

/-! ### Integrals -/







/-! ### The quadratic form of the fibre Hamiltonian, and the uniform estimates -/



theorem ham_inner_self (W : WallPot) (s : ℝ) (f : ccSchwartz ℝ) :
    (inner ℂ (W.ham s (ccEquiv ℝ f)) ((ccEquiv ℝ f : ccDomain ℝ) : L2R) : ℂ)
      = (((∫ x, ‖deriv ((f : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x‖ ^ 2)
          + ∫ x, W.pot s x * ‖(f : 𝓢(ℝ, ℂ)) x‖ ^ 2 : ℝ) : ℂ) := by
  have hk := kinCcR_quadratic_form f
  have hp := opCc_quadratic_form (W.pot s) (W.pot_smooth s) f
  change (inner ℂ ((kinCcR + opCc (W.pot s) (W.pot_smooth s)) (ccEquiv ℝ f))
    ((ccEquiv ℝ f : ccDomain ℝ) : L2R) : ℂ) = _
  rw [LinearMap.add_apply, inner_add_left, hk, hp]
  push_cast
  ring

/-- The quadratic form of `h_s` is the Dirichlet energy plus the potential energy. -/
theorem ham_quadForm (W : WallPot) (s : ℝ) (f : ccSchwartz ℝ) :
    quadForm (W.ham s) (ccEquiv ℝ f)
      = (∫ x, ‖deriv ((f : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x‖ ^ 2)
        + ∫ x, W.pot s x * ‖(f : 𝓢(ℝ, ℂ)) x‖ ^ 2 := by
  have h := ham_inner_self W s f
  have hc : (inner ℂ ((ccEquiv ℝ f : ccDomain ℝ) : L2R) (W.ham s (ccEquiv ℝ f)) : ℂ)
      = (starRingEnd ℂ)
        (inner ℂ (W.ham s (ccEquiv ℝ f)) ((ccEquiv ℝ f : ccDomain ℝ) : L2R) : ℂ) :=
    (inner_conj_symm _ _).symm
  rw [quadForm, hc, h]
  simp

theorem integral_deriv_nonneg (f : ccSchwartz ℝ) :
    (0 : ℝ) ≤ ∫ x, ‖deriv ((f : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x‖ ^ 2 :=
  integral_nonneg fun x => by positivity

/-- **The fibre Hamiltonian is positive** for `s ≥ 0`. -/
theorem ham_quadForm_nonneg (W : WallPot) (s : ℝ) (hs : 0 ≤ s) (u : ccDomain ℝ) :
    0 ≤ quadForm (W.ham s) u := by
  obtain ⟨f, rfl⟩ := (ccEquiv ℝ).surjective u
  rw [ham_quadForm]
  have h2 : (0 : ℝ) ≤ ∫ x, W.pot s x * ‖(f : 𝓢(ℝ, ℂ)) x‖ ^ 2 :=
    integral_nonneg fun x => mul_nonneg (W.pot_nonneg s hs x) (by positivity)
  have h1 := integral_deriv_nonneg f
  linarith













/-! ### The commutator of the fibre Hamiltonian with the scalaron field -/







/-! ### The fibre comparison operator -/

namespace WallPot

variable (W : WallPot) (s : ℝ) (hs : 0 ≤ s)

/-- The fibre Hamiltonian as a densely defined positive symmetric operator. -/
def posSym : PosSymOp L2R where
  dom := ccDomain ℝ
  op := W.ham s
  sym := W.ham_symmetricOn s
  pos := ham_quadForm_nonneg W s hs

/-- **The fibre comparison operator**: the Friedrichs extension of
`h_s = −d²/dφ² + φ²/4 + V(φ) + s`, a positive self-adjoint operator whose shift by one is
onto `L²(ℝ)`. -/
def comparison : Comparison L2R :=
  friedrichsComparison (W.posSym s hs) ccDomain_dense







end WallPot

end Fibre

end

end BookProof.ScalaronFiberFL


