-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:01:36.496335+00:00
-- url     : https://prove2.me/theorems/5af96d2d-3f66-4f6a-b255-00ecf7c0aa0a
-- title:
--   Is Closed Kset
-- statement:
--   Definitions and structural lemmas for Is Closed Kset, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/IsClosedKset.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PsiExistsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder
namespace ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
def IsMu (lam : Fin n → ℝ) (μ : Fin n → ℤ) : Prop := ∀ a, (μ a : ℝ) = lam a + rho n a
def muNext (μ : Fin n → ℤ) (i : Fin n) : ℤ := if h : (i : ℕ) + 1 < n then μ ⟨(i : ℕ) + 1, h⟩ else 0
def lead (i : ℕ) (z : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  if h : i ≤ n then (z.submatrix (Fin.castLE h) (Fin.castLE h)).det else 0
def PhiM (μ : Fin n → ℤ) (z : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  ∏ i : Fin n, lead ((i : ℕ) + 1) z ^ (-(μ i - muNext μ i))
def OmegaSet (n : ℕ) : Set (Matrix (Fin n) (Fin n) ℂ) := {z | ∀ i : Fin n, lead ((i : ℕ) + 1) z ≠ 0}
lemma isClosed_Kset (ε : Fin n → Bool) : IsClosed (Kset ε) := by
  have h1 : IsClosed {g : Matrix (Fin n) (Fin n) ℂ | star g * g = 1 ∧ g * star g = 1} :=
    (isClosed_eq (continuous_star.mul continuous_id) continuous_const).inter
      (isClosed_eq (continuous_id.mul continuous_star) continuous_const)
  have h2 : IsClosed {g : Matrix (Fin n) (Fin n) ℂ | g * Jm ε = Jm ε * g} :=
    isClosed_eq (continuous_id.mul continuous_const) (continuous_const.mul continuous_id)
  convert h1.inter h2 using 1
  ext g
  simp only [Kset, Set.mem_setOf_eq, Set.mem_inter_iff, Matrix.unitaryGroup]
  exact Iff.rfl
lemma isClosed_KG (ε : Fin n → Bool) : IsClosed ((KG ε : Set (UJ ε))) := by
  show IsClosed {g : UJ ε | toM g ∈ Kset ε}
  exact (isClosed_Kset ε).preimage (by first
    | fun_prop
    | continuity
    | exact continuous_subtype_val
    | exact Units.continuous_val.comp continuous_subtype_val)
instance (ε : Fin n → Bool) : LocallyCompactSpace (KG ε) := (isClosed_KG ε).locallyCompactSpace
instance (ε : Fin n → Bool) : MeasurableSpace (KG ε) := borel _
instance (ε : Fin n → Bool) : BorelSpace (KG ε) := ⟨rfl⟩
def muK (ε : Fin n → Bool) : Measure (KG ε) := Measure.haar
def projW {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) : T.V →L[ℂ] T.V :=
  (innerSL ℂ T.w).smulRight T.w
def psM {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (μ : Fin n → ℤ)
    (x : Matrix (Fin n) (Fin n) ℂ) : T.V →L[ℂ] T.V :=
  ((Module.finrank ℂ T.V : ℂ) / ((muK ε Set.univ).toReal : ℂ)) •
    ∫ k, PhiM μ (toMK k⁻¹ * x * toMK k) • (T.op k * projW T * T.op k⁻¹) ∂(muK ε)
open Classical in

def PsiM {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (μ : Fin n → ℤ)
    (g : Matrix (Fin n) (Fin n) ℂ) : T.V →L[ℂ] T.V :=
  if h : ∃ (k : KG ε) (X : Matrix (Fin n) (Fin n) ℂ), inP ε X ∧ g = toMK k * NormedSpace.exp X then
    T.op h.choose * psM T μ (NormedSpace.exp h.choose_spec.choose)
  else 0
section Calc
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
def IsLowerTri (c : Matrix (Fin n) (Fin n) ℂ) : Prop := ∀ a b : Fin n, a < b → c a b = 0
def IsUpperTri (c : Matrix (Fin n) (Fin n) ℂ) : Prop := ∀ a b : Fin n, b < a → c a b = 0
def IsBlock (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) : Prop := ∀ a b : Fin n, ε a ≠ ε b → X a b = 0
def lowMinusUp (B : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun a b => if b < a then B a b else if a < b then -B a b else 0
def posSet (n : ℕ) : Set (Matrix (Fin n) (Fin n) ℂ) := {x | x.PosDef}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
def Lhol (X : Matrix (Fin n) (Fin n) ℂ) (F : Matrix (Fin n) (Fin n) ℂ → E) :
    Matrix (Fin n) (Fin n) ℂ → E :=
  fun z => fderiv ℂ F z (X * z)
def Rhol (X : Matrix (Fin n) (Fin n) ℂ) (F : Matrix (Fin n) (Fin n) ℂ → E) :
    Matrix (Fin n) (Fin n) ℂ → E :=
  fun z => fderiv ℂ F z (z * X)
def casL (F : Matrix (Fin n) (Fin n) ℂ → E) : Matrix (Fin n) (Fin n) ℂ → E :=
  fun z => ∑ a, ∑ b, Lhol (Matrix.single a b 1) (Lhol (Matrix.single b a 1) F) z
end Calc
def Gint {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (μ : Fin n → ℤ)
    (x : Matrix (Fin n) (Fin n) ℂ) (k : KG ε) : T.V →L[ℂ] T.V :=
  PhiM μ (toMK k⁻¹ * x * toMK k) • (T.op k * projW T * T.op k⁻¹)
end ReciprocityTheory.ChartRestriction.DS.S7


