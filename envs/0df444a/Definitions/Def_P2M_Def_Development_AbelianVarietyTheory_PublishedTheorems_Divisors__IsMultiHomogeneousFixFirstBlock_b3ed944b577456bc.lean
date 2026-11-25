-- Prove2me | Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__IsMultiHomogeneousFixFirstBlock_b3ed944b577456bc
-- name    : P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__IsMultiHomogeneousFixFirstBlock_b3ed944b577456bc
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T15:59:06.251704+00:00
-- url     : https://prove2.me/theorems/bb2097de-fd68-4b58-ba38-5ff1bc7e32b0
-- title:
--   Is Multi Homogeneous Fix First Block
-- statement:
--   Definitions and structural lemmas for Is Multi Homogeneous Fix First Block, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/IsMultiHomogeneousFixFirstBlock.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IrreducibleOfIrreducibleMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ForallAevalLineVanishingIdealIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ProjPointIdealMemProjComponentsOfIsProjPureDim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
namespace GlobalTheory.ChowHt
section Mult
variable {R : Type} [CommRing R]
def localLength (J Q : Ideal R) [Q.IsPrime] : ℕ∞ :=
  Module.length (Localization.AtPrime Q)
    (Localization.AtPrime Q ⧸ J.map (algebraMap R (Localization.AtPrime Q)))
end Mult
variable {k : Type} [Field k] {N : ℕ}
open Classical in

def projCycle (J : Ideal (MvPolynomial (Fin N) k)) : Ideal (MvPolynomial (Fin N) k) →₀ ℕ :=
  Finsupp.ofSupportFinite
    (fun Q => if h : Q ∈ projComponents J then
      (haveI : Q.IsPrime := h.1.1.1; localLength J Q).toNat else 0)
    ((finite_projComponents J).subset fun Q hQ => by
      by_contra h
      exact hQ (dif_neg h))
def hyperplaneForm (u : Fin N → k) : MvPolynomial (Fin N) k := ∑ j, C (u j) * X j
def hyperplaneSection (P : Ideal (MvPolynomial (Fin N) k)) (u : Fin N → k) :
    Ideal (MvPolynomial (Fin N) k) →₀ ℕ :=
  projCycle (P ⊔ Ideal.span {hyperplaneForm u})
def fixFirstBlock {B : ℕ} (u : Fin N → k) (f : MvPolynomial (Fin (B + 1) × Fin N) k) :
    MvPolynomial (Fin B × Fin N) k :=
  aeval (fun p : Fin (B + 1) × Fin N =>
    (Fin.cons (fun j => C (u j)) (fun b j => X (b, j)) :
      Fin (B + 1) → Fin N → MvPolynomial (Fin B × Fin N) k) p.1 p.2) f
end GlobalTheory.ChowHt
namespace GlobalTheory.Published
open GlobalTheory.ChowHt
def ChowFormExists : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (N D : ℕ) (I : Ideal (MvPolynomial (Fin N) k)),
    I.IsHomogeneous (homogeneousSubmodule (Fin N) k) →
    (I.map (MvPolynomial.map (algebraMap k (AlgebraicClosure k)) :
      MvPolynomial (Fin N) k →+* MvPolynomial (Fin N) (AlgebraicClosure k))).IsPrime →
    ringKrullDim (MvPolynomial (Fin N) k ⧸ I) = (D + 1 : ℕ) →
    ∃ f : MvPolynomial (Fin (D + 1) × Fin N) k, IsChowForm I D (hilbertDegree I) f ∧
      ∀ g : MvPolynomial (Fin (D + 1) × Fin N) k, IsChowForm I D (hilbertDegree I) g →
        ∃ c : k, c ≠ 0 ∧ g = C c * f
def ChowFormIntExists : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (N e : ℕ) (P : Ideal (MvPolynomial (Fin N) k)),
    P.IsHomogeneous (homogeneousSubmodule (Fin N) k) → P.IsPrime →
    ringKrullDim (MvPolynomial (Fin N) k ⧸ P) = (e + 1 : ℕ) →
    ∃ f : MvPolynomial (Fin (e + 1) × Fin N) k, IsChowFormInt P e (hilbertDegree P) f ∧
      ∀ g : MvPolynomial (Fin (e + 1) × Fin N) k, IsChowFormInt P e (hilbertDegree P) g →
        ∃ c : k, c ≠ 0 ∧ g = C c * f
def ChowFormHyperplaneSection : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (N e : ℕ) (P : Ideal (MvPolynomial (Fin N) k)),
    P.IsHomogeneous (homogeneousSubmodule (Fin N) k) → P.IsPrime →
    ringKrullDim (MvPolynomial (Fin N) k ⧸ P) = (e + 1 + 1 : ℕ) →
    ∀ u : Fin N → k, hyperplaneForm u ∉ P →
    ∀ (dl : ℕ) (f : MvPolynomial (Fin (e + 1 + 1) × Fin N) k), IsChowFormInt P (e + 1) dl f →
    ∀ (d : Ideal (MvPolynomial (Fin N) k) → ℕ)
      (g : Ideal (MvPolynomial (Fin N) k) → MvPolynomial (Fin (e + 1) × Fin N) k),
      (∀ Q ∈ (hyperplaneSection P u).support, IsChowFormInt Q e (d Q) (g Q)) →
      ∃ c : k, c ≠ 0 ∧
        fixFirstBlock u f = C c * (hyperplaneSection P u).prod (fun Q m => g Q ^ m)
end GlobalTheory.Published


