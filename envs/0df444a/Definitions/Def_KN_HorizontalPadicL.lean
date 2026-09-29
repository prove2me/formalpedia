-- Prove2me | Definitions.Def_KN_HorizontalPadicL
-- name    : KN_HorizontalPadicL
-- status  : Definition
-- author  : @davidloeffler
-- created : 2026-09-17T06:41:45.397016+00:00
-- url     : https://prove2.me/theorems/832da5cd-8f60-4e94-9142-723299694d2b
-- title:
--   Twisted critical values of a modular elliptic curve
-- statement:
--   Defines modularity for one rational elliptic curve and counts primitive algebraic Dirichlet characters for which the MTT Mellin-integral critical value is nonzero. The count uses MTT.criticalLValue directly and never constructs the twist as a modular form.
-- source:
--   Kriz–Nordentoft, Horizontal p-adic L-functions, https://arxiv.org/pdf/2310.20678, Sections 2.1–2.5 and 5.1.

import Definitions.Def_MTT_Arithmetic
import Mathlib.AlgebraicGeometry.EllipticCurve.LFunction
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false

namespace HorizontalPadicL

/-- Quantitative lower-bound notation used in Theorem 1.1. -/
def HasLogPowerLowerBound (count : ℝ → ℕ) (α : ℝ) : Prop :=
  ∃ c X₀ : ℝ, 0 < c ∧ 1 ≤ X₀ ∧
    ∀ X : ℝ, X₀ ≤ X → c * X / (Real.log X) ^ (1 - α) ≤ count X

/-- An algebraic Dirichlet character together with its level. -/
abbrev DirichletCharacterWithLevel :=
  Σ N : {N : ℕ // 0 < N}, DirichletCharacter MTT.Qbar N.1

/-- Weight-two cusp forms for `Γ₀(N)`, with positivity supplied explicitly. -/
abbrev CuspFormAtLevel (N : ℕ) (hN : 0 < N) :=
  let _ : NeZero N := ⟨Nat.ne_of_gt hN⟩
  CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2

/-- A weight-two cusp form of level `N` whose q-expansion coefficients are the
arithmetic L-series coefficients of `E`. -/
structure ModularFormAtLevel (E : WeierstrassCurve ℚ) (N : ℕ) where
  level_pos : 0 < N
  form : CuspFormAtLevel N level_pos
  coeff_eq : ∀ n : ℕ, (E.LFunction n : ℂ) =
    (UpperHalfPlane.qExpansion 1 form).coeff n

/-- A rational elliptic curve is modular if it has an associated weight-two cusp form
at some positive level. -/
def IsModular (E : WeierstrassCurve ℚ) : Prop :=
  ∃ N : ℕ, Nonempty (ModularFormAtLevel E N)

/-- The least level of a modular form associated with `E`. -/
noncomputable def modularConductor (E : WeierstrassCurve ℚ) (hE : IsModular E) : ℕ := by
  classical
  exact Nat.find hE

/-- A chosen modular form associated with `E` at its least level. -/
noncomputable def modularFormAtConductor (E : WeierstrassCurve ℚ) (hE : IsModular E) :
    ModularFormAtLevel E (modularConductor E hE) := by
  classical
  exact Classical.choice (Nat.find_spec hE)

lemma modularConductor_pos (E : WeierstrassCurve ℚ) (hE : IsModular E) :
    0 < modularConductor E hE :=
  (modularFormAtConductor E hE).level_pos

/-- Number of primitive exact-order characters of conductor at most `X`, coprime to
`N(E)`, for which the twisted critical value defined by the MTT Mellin integral is
nonzero. No twisted modular form is constructed or chosen. -/
noncomputable def nonvanishingCount (ι : MTT.Qbar →+* ℂ)
    (E : WeierstrassCurve ℚ) (hE : IsModular E) (d : ℕ) (X : ℝ) : ℕ :=
  let P := modularFormAtConductor E hE
  Set.ncard {χ : DirichletCharacterWithLevel |
    χ.2.IsPrimitive ∧ orderOf χ.2 = d ∧ (χ.2.conductor : ℝ) ≤ X ∧
    Nat.Coprime (modularConductor E hE) χ.1.1 ∧
    @MTT.criticalLValue ι P.form χ.1.1 ⟨Nat.ne_of_gt χ.1.2⟩ χ.2 0 ≠ 0}

end HorizontalPadicL


