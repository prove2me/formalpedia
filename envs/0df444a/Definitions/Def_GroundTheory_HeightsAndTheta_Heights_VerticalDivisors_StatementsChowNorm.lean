-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsChowNorm
-- name    : GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsChowNorm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:40:47.033909+00:00
-- url     : https://prove2.me/theorems/ecad7835-910d-41a4-9e69-01fae35d2a0d
-- title:
--   Statements Chow Norm
-- statement:
--   Definitions and structural lemmas for Statements Chow Norm, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/StatementsChowNorm.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_Inhabitants
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial
noncomputable section
section Generic
variable (k : Type*) [Field k] (e n : ℕ)
abbrev GenParField : Type _ := FractionRing (MvPolynomial (Par e n) k)
def genPar : Par e n → GenParField k e n :=
  fun p => algebraMap (MvPolynomial (Par e n) k) (GenParField k e n) (X p)
abbrev GenSec {n : ℕ} (Q : Ideal (MvPolynomial (Fin n) k)) : Type _ :=
  SecAlg (Q.map (MvPolynomial.map (algebraMap k (GenParField k e n)))) (genPar k e n)
end Generic
def ChowNormFormGeneric.Statement : Prop :=
  ∀ (k : Type) [Field k] [PerfectField k] (n e : ℕ) (Q : Ideal (MvPolynomial (Fin n) k))
    (g : MvPolynomial (Fin (e + 1) × Fin n) k), IsProjPrime Q → IsChowForm Q (e + 1) g →
      Module.Finite (GenParField k e n) (GenSec k e Q) ∧
        ∃ c : GenParField k e n, c ≠ 0 ∧
          specRest (algebraMap k (GenParField k e n)) g (genPar k e n) =
            C c * normForm (GenSec k e Q)
              (secCoord (Q.map (MvPolynomial.map (algebraMap k (GenParField k e n)))) (genPar k e n))
def SecAlgFieldChange.Statement : Prop :=
  ∀ (E₀ E : Type) [Field E₀] [Field E] (φ : E₀ →+* E) (n e : ℕ)
    (Q₀ : Ideal (MvPolynomial (Fin n) E₀)) (y₀ : Par e n → E₀), Module.Finite E₀ (SecAlg Q₀ y₀) →
      Module.Finite E (SecAlg (Q₀.map (MvPolynomial.map φ)) (φ ∘ y₀)) ∧
        (normForm (SecAlg Q₀ y₀) (secCoord Q₀ y₀)).map φ =
          normForm (SecAlg (Q₀.map (MvPolynomial.map φ)) (φ ∘ y₀))
            (secCoord (Q₀.map (MvPolynomial.map φ)) (φ ∘ y₀))
def SecAlgFinite.Statement : Prop :=
  ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (n e : ℕ)
    (Q : Ideal (MvPolynomial (Fin n) k)) (g : MvPolynomial (Fin (e + 1) × Fin n) k)
    (y : Par e n → E), AlgebraicIndependent k y → IsProjPrime Q → IsChowForm Q (e + 1) g →
      Module.Finite E (SecAlg (Q.map (MvPolynomial.map (algebraMap k E))) y)
def GenSecDomain.Statement : Prop :=
  ∀ (k : Type) [Field k] (n e : ℕ) (Q : Ideal (MvPolynomial (Fin n) k))
    (g : MvPolynomial (Fin (e + 1) × Fin n) k), IsProjPrime Q → IsChowForm Q (e + 1) g →
      IsDomain (GenSec k e Q)
def GenSecSeparable.Statement : Prop :=
  ∀ (k : Type) [Field k] [PerfectField k] (n e : ℕ) (Q : Ideal (MvPolynomial (Fin n) k))
    (g : MvPolynomial (Fin (e + 1) × Fin n) k), IsProjPrime Q → IsChowForm Q (e + 1) g →
      Algebra.IsSeparable (GenParField k e n) (GenSec k e Q)
def ChowSecDvd.Statement : Prop :=
  ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (n e : ℕ)
    (Q : Ideal (MvPolynomial (Fin n) k)) (g : MvPolynomial (Fin (e + 1) × Fin n) k)
    (y : Par e n → E), IsProjPrime Q → IsChowForm Q (e + 1) g →
      ∃ m : ℕ, 0 < m ∧
        (∑ j, X j * C (secCoord (Q.map (MvPolynomial.map (algebraMap k E))) y j)) ∣
          ((specRest (algebraMap k E) g y).map
            (algebraMap E (SecAlg (Q.map (MvPolynomial.map (algebraMap k E))) y))) ^ m
def NormFormIrreducible.Statement : Prop :=
  ∀ (E L : Type) [Field E] [CommRing L] [IsDomain L] [Algebra E L] [Module.Finite E L]
    [Algebra.IsSeparable E L] (n : ℕ) (x : Fin n → L) (t : Fin n → E),
    Algebra.adjoin E (Set.range x) = ⊤ → ∑ j, algebraMap E L (t j) * x j = 1 →
      Irreducible (normForm (R := E) L x)
def GenChowIrreducible.Statement : Prop :=
  ∀ (k : Type) [Field k] (n e : ℕ) (Q : Ideal (MvPolynomial (Fin n) k))
    (g : MvPolynomial (Fin (e + 1) × Fin n) k), IsProjPrime Q → IsChowForm Q (e + 1) g →
      Irreducible (specRest (algebraMap k (GenParField k e n)) g (genPar k e n))
def NormFormDvd.Statement : Prop :=
  ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra R A] [Module.Free R A] [Module.Finite R A]
    (n : ℕ) (x : Fin n → A) (p : MvPolynomial (Fin n) R),
      (∑ j, X j * C (x j) : MvPolynomial (Fin n) A) ∣ p.map (algebraMap R A) →
        normForm A x ∣ p ^ Module.finrank R A
section Inhabitants
def complexGens : Fin 2 → ℂ := ![1, Complex.I]
end Inhabitants
end
end GroundTheory.Heights₂.Heights.Vertical


