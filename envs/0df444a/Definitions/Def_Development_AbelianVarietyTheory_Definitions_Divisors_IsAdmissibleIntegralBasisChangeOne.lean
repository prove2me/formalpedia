-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
-- name    : Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T00:45:11.138546+00:00
-- url     : https://prove2.me/theorems/d38529df-05a1-4bf2-8822-835f8412c3c8
-- title:
--   Is Admissible Integral Basis Change One
-- statement:
--   Definitions and structural lemmas for Is Admissible Integral Basis Change One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IsAdmissibleIntegralBasisChangeOne.lean

import Mathlib
import Definitions.Def_GroundTheory_FunctionField_PlaceBridge
import Theorems.Thm_GroundTheory_FunctionField_Place_ordHom_apply
import Theorems.Thm_GroundTheory_FunctionField_Place_valuation_le_one_iff
import Theorems.Thm_GroundTheory_FunctionField_Place_valuation_surjective
import Theorems.Thm_GroundTheory_FunctionField_valuation_eq_of_isEquiv
import Theorems.Thm_P2M_GroundTheory_FunctionField_Place_valuation_algebraMap__1215bcdcaa8c
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.FunctionField.Place.ordHom_apply


set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped IntermediateField Polynomial
namespace GlobalTheory.Nef
def IsFF (k F : Type) [Field k] [Field F] [Algebra k F] : Prop :=
  ∃ t : F, Transcendental k t ∧ FiniteDimensional k⟮t⟯ F
def Place (k F : Type) [Field k] [Field F] [Algebra k F] : Type :=
  {v : Valuation F (WithZero (Multiplicative ℤ)) //
    Function.Surjective v ∧ ∀ c : k, c ≠ 0 → v (algebraMap k F c) = 1}
variable {k F : Type} [Field k] [Field F] [Algebra k F]
abbrev Place.O (v : Place k F) : ValuationSubring F := v.1.valuationSubring
def ord (v : Place k F) (x : F) : ℤ := -WithZero.log (v.1 x)
def nrm {n : ℕ} (v : Place k F) (x : Fin n → F) : WithZero (Multiplicative ℤ) :=
  Finset.univ.sup fun i => v.1 (x i)
def ordVec {n : ℕ} (v : Place k F) (x : Fin n → F) : ℤ := -WithZero.log (nrm v x)
def Unimod {n : ℕ} (v : Place k F) (g : Matrix (Fin n) (Fin n) F) : Prop :=
  (∀ i j, v.1 (g i j) ≤ 1) ∧ v.1 g.det = 1
def admitted {n : ℕ} (g : Place k F → Matrix (Fin n) (Fin n) F) : Prop :=
  (∀ v, (g v).det ≠ 0) ∧ {v | ¬ Unimod v (g v)}.Finite
def deg [IsAlgClosed k] {n : ℕ} (g : Place k F → Matrix (Fin n) (Fin n) F) : ℤ := ∑ᶠ v, ord v (g v).det
def degLine [IsAlgClosed k] {n : ℕ} (g : Place k F → Matrix (Fin n) (Fin n) F) (w : Fin n → F) : ℤ :=
  ∑ᶠ v, ordVec v ((g v).mulVec w)
def IsRes {E : Type} [Field E] [Algebra k E] [Algebra F E] (ρ : Place k E → Place k F) : Prop :=
  ∀ p x, p.1 (algebraMap F E x) ≤ 1 ↔ (ρ p).1 x ≤ 1
def pullAd {n : ℕ} {E : Type} [Field E] [Algebra k E] [Algebra F E] (ρ : Place k E → Place k F)
    (g : Place k F → Matrix (Fin n) (Fin n) F) : Place k E → Matrix (Fin n) (Fin n) E :=
  fun p => (g (ρ p)).map (algebraMap F E)
def LinesLE [IsAlgClosed k] {n : ℕ} (g : Place k F → Matrix (Fin n) (Fin n) F) (b : ℝ) : Prop :=
  ∀ (E : Type) [Field E] [Algebra k E] [Algebra F E] [IsScalarTower k F E] [FiniteDimensional F E]
    (ρ : Place k E → Place k F), IsRes ρ → ∀ w : Fin n → E, w ≠ 0 →
      (degLine (pullAd ρ g) w : ℝ) ≤ b * Module.finrank F E
def IsRat (φ : PowerSeries F) : Prop :=
  ∃ p q : F[X], q ≠ 0 ∧ (q : PowerSeries F) * φ = (p : PowerSeries F)
def hankel (c : ℕ → F) (n : ℕ) : F := (Matrix.of fun i j : Fin (n + 1) => c (i + j)).det
def sc (v : Place k F) (u : F) : PowerSeries v.O →+* PowerSeries F :=
  (PowerSeries.rescale u).comp (PowerSeries.map v.O.subtype)
namespace Lib
open scoped WithZero
open IsDedekindDomain GroundTheory.FunctionField
def toRing (v : Nef.Place k F) : GroundTheory.FunctionField.Place k F where
  ring := v.1.valuationSubring
  ne_top h := by
    obtain ⟨x, hx⟩ := v.2.1 (WithZero.exp 1)
    have hm : x ∈ v.1.valuationSubring := h ▸ ValuationSubring.mem_top _
    rw [Valuation.mem_valuationSubring_iff, hx, ← WithZero.exp_zero, WithZero.exp_le_exp] at hm
    omega
  algebraMap_mem c := by
    rw [Valuation.mem_valuationSubring_iff]
    by_cases hc : c = 0
    · simp [hc]
    · exact (v.2.2 c hc).le
theorem valuation_toRing [IsFunctionField k F] (v : Nef.Place k F) : (toRing v).valuation = v.1 :=
  valuation_eq_of_isEquiv (Valuation.isEquiv_iff_val_le_one.2 fun {x} => (toRing v).valuation_le_one_iff x)
    (toRing v).valuation_surjective v.2.1
def placeEquiv [IsFunctionField k F] : Nef.Place k F ≃ GroundTheory.FunctionField.Place k F where
  toFun := toRing
  invFun w := ⟨w.valuation, w.valuation_surjective, fun _ hc => w.valuation_algebraMap' hc⟩
  left_inv v := Subtype.ext (valuation_toRing v)
  right_inv w := GroundTheory.FunctionField.Place.ext (by
    ext x
    exact w.valuation_le_one_iff x)
open scoped Classical in

def atPlace {n : ℕ} (v : Nef.Place k F) (d : Fin n → F) : Nef.Place k F → Matrix (Fin n) (Fin n) F :=
  fun u => if u = v then Matrix.diagonal d else 1
section Line
variable (k)
open scoped Classical in

def atInf : Nef.Place k (RatFunc k) :=
  ⟨RatFunc.inftyValuation k, fun y => by
    rcases eq_or_ne y 0 with rfl | hy
    · exact ⟨0, map_zero _⟩
    · exact ⟨RatFunc.X ^ WithZero.log y, by rw [RatFunc.inftyValuation.X_zpow, WithZero.exp_log hy]⟩,
    fun c hc => RatFunc.inftyValuation.C k hc⟩
variable {k}
def atPrime (u : HeightOneSpectrum k[X]) : Nef.Place k (RatFunc k) :=
  ⟨u.valuation (RatFunc k), u.valuation_surjective _, fun c hc => by
    rw [IsScalarTower.algebraMap_apply k k[X] (RatFunc k)]
    exact (u.valuation_of_algebraMap _).trans (HeightOneSpectrum.intValuation_eq_one_iff.2 fun hm =>
      u.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hm ((IsUnit.mk0 c hc).map _)))⟩
def primeOf {f : k[X]} (hf : Irreducible f) : HeightOneSpectrum k[X] where
  asIdeal := Ideal.span {f}
  isPrime := (Ideal.span_singleton_prime hf.ne_zero).2 hf.prime
  ne_bot := by simpa using hf.ne_zero
def placeX (k : Type) [Field k] : Nef.Place k (RatFunc k) := atPrime (primeOf (Polynomial.irreducible_X (R := k)))
end Line
section Product
end Product
end Lib
end GlobalTheory.Nef


