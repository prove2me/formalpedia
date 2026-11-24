-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsSelfDualE
-- name    : Development_AbelianVarietyTheory_Definitions_Foundations_IsSelfDualE
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T08:42:14.497643+00:00
-- url     : https://prove2.me/theorems/63f4b5bc-0595-46d6-a79c-c76cc49b881b
-- title:
--   Is Self Dual E
-- statement:
--   Definitions and structural lemmas for Is Self Dual E, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsSelfDualE.lean

import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefMod
import Definitions.Def_Formalism_QuotientMetricDivisors_RatHermLcvTwist
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open Formalism.BasicNotions Formalism.L2.DIV
open scoped Matrix ComplexOrder
noncomputable section
namespace GlobalTheory.TestLat
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {n N : ℕ} {C : Type}
def valAt (lam : ι → DomWeight n) (e : Fin N ≃ C × VVIdx lam) (c : C) : (Fin N → K) →ₗ[K] VV K lam :=
  ((bVV K lam).equivFun.symm : (VVIdx lam → K) →ₗ[K] VV K lam) ∘ₗ LinearMap.funLeft K K fun i => e.symm (c, i)
def sumLat (lam : ι → DomWeight n) (e : Fin N ≃ C × VVIdx lam) (T : C → Submodule (𝓞 K) (VV K lam)) :
    Submodule (𝓞 K) (Fin N → K) :=
  ⨅ c, (T c).comap ((valAt lam e c).restrictScalars (𝓞 K))
open Classical in

def sumGram [StarRing K] (lam : ι → DomWeight n) (e : Fin N ≃ C × VVIdx lam) (G : ι → Matrix (Fin n) (Fin n) K) :
    Matrix (Fin N) (Fin N) K :=
  Matrix.of fun a b => if (e a).1 = (e b).1 then pairK lam G (bVV K lam (e a).2) (bVV K lam (e b).2) else 0
def IsMetric (H : Matrix (Fin N) (Fin N) K) (X : InfinitePlace K → Matrix (Fin N) (Fin N) ℂ) : Prop :=
  ∀ v : InfinitePlace K, IsUnit (X v).det ∧ ((X v)⁻¹)ᴴ * (X v)⁻¹ = H.map v.embedding
def SpreadLe (lam : ι → DomWeight n) (R : ℝ) : Prop := ∀ τ i j, (((lam τ).w i - (lam τ).w j : ℤ) : ℝ) ≤ R
def IsDefGram [StarRing K] (G : Matrix (Fin n) (Fin n) K) : Prop :=
  Gᴴ = G ∧ (∀ a b, G a b ∈ Formalism.DivisionValues.cmMax K) ∧ ∀ φ : K →+* ℂ, (G.map φ).PosDef
def IsSelfDualK [StarRing K] (G : Matrix (Fin n) (Fin n) K) (M : Submodule (𝓞 K) (Fin n → K)) : Prop :=
  Submodule.IsLattice K M ∧ hdualFr G M = M
def IsSelfDualE {E : Type} [Field E] [NumberField E] (cE : E →+* E) (J : Matrix (Fin n) (Fin n) E)
    (L : Submodule (𝓞 E) (Fin n → E)) : Prop :=
  Submodule.IsLattice E L ∧ ∀ y, y ∈ L ↔ ∀ x ∈ L, Formalism.UG.hform cE J x y ∈ (algebraMap (𝓞 E) E).range
def bound (f ν : ℕ) (R : ℝ) : ℝ := 4 * (f : ℝ) * ν * R * Real.log (ν * R)
end GlobalTheory.TestLat


