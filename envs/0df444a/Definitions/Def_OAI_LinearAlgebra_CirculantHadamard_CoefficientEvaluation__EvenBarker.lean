-- Prove2me | Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CoefficientEvaluation__EvenBarker
-- name    : OAI_LinearAlgebra_CirculantHadamard_CoefficientEvaluation__EvenBarker
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T15:09:17.505782+00:00
-- url     : https://prove2.me/theorems/93386626-824e-45f2-b6a9-2e4d76b7868b
-- title:
--   Changing coefficients in a cyclic group ring
-- statement:
--   These notions belong to a formal proof that a real circulant Hadamard matrix of positive order $n$ exists only for $n=1$ and $n=4$. Such a matrix has entries $\pm1$, satisfies $HH^{\mathsf T}=nI$, and has the form $H_{ij}=h(j-i)$ with indices in $\mathbb Z/n$. Its first row becomes an element $f$ of the integer group ring $\mathbb Z[\mathbb Z/n]$ with $f f^{*}=n$, where $f^{*}$ reverses the indices. Two-adic descent reduces every order $n>1$ to $n=4u^2$ with $u$ odd; for $u>1$, evaluation at characters with values in cyclotomic rings and a local argument at a prime above $2$ give a contradiction. Write $R[\mathbb Z/n]$ for the cyclic group ring (finitely supported coefficient functions on $\mathbb Z/n$ with convolution), $e_a$ for its basis element at $a$, and $f^{*}(a)=\overline{f(-a)}$ for its involution, which reverses indices and applies the coefficient star.
--
--   1. **Coefficient map.** For a ring homomorphism $\varphi:R\to S$, the ring homomorphism $R[\mathbb Z/n]\to S[\mathbb Z/n]$ that applies $\varphi$ to every coefficient and keeps the index:
--   $$
--   r\,e_a\longmapsto\varphi(r)\,e_a .
--   $$
--   It sends scalars to scalars, and it is natural for character evaluation: evaluating the image at $(\psi,\chi)$ equals evaluating the original at $(\psi\circ\varphi,\chi)$. It also commutes with augmentation, $\varepsilon(\varphi_*F)=\varphi(\varepsilon(F))$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/LinearAlgebra/CirculantHadamard/CoefficientEvaluation.lean

-- Generated from openai/math@1581d4c lean/OAI/LinearAlgebra/CirculantHadamard/CoefficientEvaluation.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the EvenBarker mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Model
import Definitions.Def_OAI_LinearAlgebra_Barker_Model
import Definitions.Def_OAI_LinearAlgebra_Barker_PeriodicModFour
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Basic__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Witnesses__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_MatrixBridge__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicRing__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicNorm__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicProjection__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_LocalDVR__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_IntegerTwoLocal__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicEvaluation__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicPolynomial__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_RamifiedConjugation__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicIntegerEvaluation__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_DyadicRemainder__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_RamifiedEisenstein__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_RamifiedLocal__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_OrderHalving__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryBlocks__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryCoefficients__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicRings__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_PrimeComponents__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_PrimeCharacterEvaluations__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryEvaluation__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_LocalizationMaps__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryLocalization__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryLocalRing__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_AlternatingProducts__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryProductTransport__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_FirstOrderResidue__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryResidue__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryLocalFamily__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_ResidueOneAssociation__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicLocalBase__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicAwayLocal__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicProjectionPolynomial__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicEvaluationAt__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicProjection__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_LocalComparison__EvenBarker

namespace OAI

universe uR uS uT

/-!
# Changing coefficients in an actual cyclic group ring

The group coordinate is retained unchanged. Character evaluation and augmentation
commute with this coefficient map, including localization of the away ring.
-/

noncomputable section

namespace CirculantHadamard.CyclicRing

open PrimeCharacterEvaluations

variable {R : Type uR} {S : Type uS} {T : Type uT} [Semiring R] [CommSemiring S] [CommSemiring T]

/-- Map coefficients and retain the same cyclic basis. -/
def coefficientMap (φ : R →+* S) (n : ℕ) : Elem R n →+* Elem S n :=
  weightedProjection φ (AddMonoidHom.id (ZMod n)) 1

@[simp] theorem coefficientMap_single (φ : R →+* S) (n : ℕ)
    (a : ZMod n) (r : R) :
    coefficientMap φ n (AddMonoidAlgebra.single a r) =
      AddMonoidAlgebra.single a (φ r) := by
  simp [coefficientMap, weightedProjection_single]

@[simp] theorem coefficientMap_scalar (φ : R →+* S) (n : ℕ) (r : R) :
    coefficientMap φ n (scalar n r) = scalar n (φ r) :=
  weightedProjection_scalar φ (AddMonoidHom.id (ZMod n)) 1 r

/-- Bundled naturality; no root-of-unity or nonzero-modulus premise is needed. -/
theorem evaluate_coefficientMap_hom (φ : R →+* S) (ψ : S →+* T) (n : ℕ)
    (χ : Multiplicative (ZMod n) →* T) :
    (evaluate ψ χ).comp (coefficientMap φ n) = evaluate (ψ.comp φ) χ := by
  apply AddMonoidAlgebra.ringHom_ext
  · intro r
    simp only [RingHom.comp_apply, coefficientMap_single, evaluate_single]
  · intro a
    simp only [RingHom.comp_apply, coefficientMap_single, evaluate_single]

theorem evaluate_coefficientMap (φ : R →+* S) (ψ : S →+* T) {n : ℕ}
    (χ : Multiplicative (ZMod n) →* T) (F : Elem R n) :
    evaluate ψ χ (coefficientMap φ n F) = evaluate (ψ.comp φ) χ F :=
  congrArg (fun f : Elem R n →+* T => f F) (evaluate_coefficientMap_hom φ ψ n χ)

@[simp] theorem augmentation_coefficientMap (φ : R →+* S) (n : ℕ) [NeZero n]
    (F : Elem R n) :
    augmentation n (coefficientMap φ n F) = φ (augmentation n F) := by
  calc
    augmentation n (coefficientMap φ n F) =
        evaluate (RingHom.id S) (1 : Multiplicative (ZMod n) →* S)
          (coefficientMap φ n F) := by
            simpa only [RingHom.id_apply] using
              (evaluate_trivial_eq_augmentation (R := S) (S := S) (n := n)
                (RingHom.id S) (coefficientMap φ n F)).symm
    _ = evaluate ((RingHom.id S).comp φ) (1 : Multiplicative (ZMod n) →* S) F :=
      evaluate_coefficientMap φ (RingHom.id S) 1 F
    _ = φ (augmentation n F) := by
      simpa only [RingHom.id_comp] using evaluate_trivial_eq_augmentation φ F

end CirculantHadamard.CyclicRing

end

end OAI


