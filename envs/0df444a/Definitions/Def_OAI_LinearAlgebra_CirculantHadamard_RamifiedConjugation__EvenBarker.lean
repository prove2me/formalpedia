-- Prove2me | Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_RamifiedConjugation__EvenBarker
-- name    : OAI_LinearAlgebra_CirculantHadamard_RamifiedConjugation__EvenBarker
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T13:56:40.213996+00:00
-- url     : https://prove2.me/theorems/69d5c595-f532-4956-b486-39631af6efbc
-- title:
--   Root-inverting conjugation of a cyclotomic quotient
-- statement:
--   These notions belong to a formal proof that a real circulant Hadamard matrix of positive order $n$ exists only for $n=1$ and $n=4$. Such a matrix has entries $\pm1$, satisfies $HH^{\mathsf T}=nI$, and has the form $H_{ij}=h(j-i)$ with indices in $\mathbb Z/n$. Its first row becomes an element $f$ of the integer group ring $\mathbb Z[\mathbb Z/n]$ with $f f^{*}=n$, where $f^{*}$ reverses the indices. Two-adic descent reduces every order $n>1$ to $n=4u^2$ with $u$ odd; for $u>1$, evaluation at characters with values in cyclotomic rings and a local argument at a prime above $2$ give a contradiction.
--
--   1. **Valuation invariance.** Every ring automorphism of a discrete valuation ring preserves its additive valuation.
--   2. **Cyclotomic quotient.** For a commutative ring $A$, the ring $A[X]/(\Phi_n(X))$ with root $\zeta$ the class of $X$; then $\zeta^n=1$, and $\zeta$ is a primitive $n$th root of unity once the quotient is a domain of characteristic zero.
--   3. **Conjugation.** For $n>0$ and such a quotient, the $A$-algebra automorphism
--   $$
--   \sigma(\zeta)=\zeta^{n-1}=\zeta^{-1},
--   $$
--   which is an involution fixing $A$. When the quotient is a DVR, $\sigma$ preserves its valuation, which is used to show that a norm $x\,\sigma(x)$ equal to a unit times an even power of a prime forces half that power to divide $x$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/LinearAlgebra/CirculantHadamard/RamifiedConjugation.lean

-- Generated from openai/math@1581d4c lean/OAI/LinearAlgebra/CirculantHadamard/RamifiedConjugation.lean by skeleton subtraction
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

namespace OAI

universe uR uA

/-!
# Cyclotomic conjugation and norm divisibility in a DVR

The conjugation fixes the coefficient ring and sends the actual
adjoined root to its multiplicative inverse. In a DVR every ring
automorphism preserves the canonical additive valuation, because it sends
units to units and uniformizers to uniformizers. Consequently a norm equal
to a unit times an even scalar power forces the corresponding half-power
to divide the element.
-/

noncomputable section

namespace CirculantHadamard.RamifiedConjugation

open Polynomial IsDiscreteValuationRing

section Valuation

variable {R : Type uR} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- Ring automorphisms of a DVR preserve its integer-valued order. -/
theorem addVal_ringEquiv (e : R ≃+* R) (x : R) :
    addVal R (e x) = addVal R x := by
  by_cases hx : x = 0
  · simp only [hx, map_zero]
  obtain ⟨π, hπ⟩ := exists_irreducible R
  obtain ⟨m, u, hu⟩ := eq_unit_mul_pow_irreducible hx hπ
  have heπ : Irreducible (e π) := (MulEquiv.irreducible_iff e).mpr hπ
  have heu : e x = (Units.map e.toMonoidHom u : R) * (e π) ^ m := by
    simpa only [map_mul, map_pow, Units.coe_map,
      show e.toMonoidHom (u : R) = e (u : R) from rfl] using congrArg e hu
  rw [addVal_def x u hπ m hu,
    addVal_def (e x) (Units.map e.toMonoidHom u) heπ m heu]

end Valuation

section Cyclotomic

variable (A : Type uA) [CommRing A] (n : ℕ)

/-- The actual cyclotomic quotient used by the ramified construction. -/
abbrev CyclotomicRing := AdjoinRoot (cyclotomic n A)

/-- The adjoined root satisfies the stated order relation even before
domainhood or characteristic zero has been established. -/
theorem root_pow_order : AdjoinRoot.root (cyclotomic n A) ^ n = 1 := by
  have h : AdjoinRoot.mk (cyclotomic n A) (X ^ n - 1) = 0 :=
    AdjoinRoot.mk_eq_zero.mpr (cyclotomic.dvd_X_pow_sub_one n A)
  simpa only [map_sub, map_pow, map_one, AdjoinRoot.mk_X, sub_eq_zero] using h

variable (hn : 0 < n)
variable [domain : IsDomain (CyclotomicRing A n)] [charZero : CharZero (CyclotomicRing A n)]

include hn

/-- The quotient root is a primitive root of the exact specified order. -/
theorem root_isPrimitiveRoot :
    IsPrimitiveRoot (AdjoinRoot.root (cyclotomic n A)) n := by
  apply (isRoot_cyclotomic_iff_charZero hn).mp
  simpa only [map_cyclotomic] using AdjoinRoot.isRoot_root (cyclotomic n A)

omit domain charZero in
theorem root_pow_pred_mul_root [IsDomain (CyclotomicRing A n)]
    [CharZero (CyclotomicRing A n)] :
    AdjoinRoot.root (cyclotomic n A) ^ (n - 1) *
      AdjoinRoot.root (cyclotomic n A) = 1 := by
  rw [← pow_succ, Nat.sub_add_cancel hn, root_pow_order]

 theorem inverse_root_aeval :
    aeval (AdjoinRoot.root (cyclotomic n A) ^ (n - 1)) (cyclotomic n A) = 0 := by
  have hcoprime : (n - 1).Coprime n :=
    (Nat.coprime_self_sub_left hn).mpr (Nat.coprime_one_left n)
  have hroot :=
    ((root_isPrimitiveRoot A n hn).pow_of_coprime (n - 1) hcoprime).isRoot_cyclotomic hn
  rw [aeval_def, ← eval_map, map_cyclotomic]
  exact hroot

/-- The root-inverting endomorphism fixes the coefficient algebra. -/
def conjugationHom : CyclotomicRing A n →ₐ[A] CyclotomicRing A n :=
  AdjoinRoot.liftAlgHom (cyclotomic n A)
    (Algebra.ofId A (CyclotomicRing A n))
    (AdjoinRoot.root (cyclotomic n A) ^ (n - 1)) (inverse_root_aeval A n hn)

@[simp] theorem conjugationHom_root :
    conjugationHom A n hn (AdjoinRoot.root (cyclotomic n A)) =
      AdjoinRoot.root (cyclotomic n A) ^ (n - 1) := by
  exact AdjoinRoot.liftAlgHom_root (cyclotomic n A)
    (Algebra.ofId A (CyclotomicRing A n))
    (AdjoinRoot.root (cyclotomic n A) ^ (n - 1)) (inverse_root_aeval A n hn)

theorem conjugationHom_comp_self :
    (conjugationHom A n hn).comp (conjugationHom A n hn) =
      AlgHom.id A (CyclotomicRing A n) := by
  apply AdjoinRoot.algHom_ext
  change conjugationHom A n hn
    (conjugationHom A n hn (AdjoinRoot.root (cyclotomic n A))) =
      AdjoinRoot.root (cyclotomic n A)
  rw [conjugationHom_root]
  have hzero : AdjoinRoot.root (cyclotomic n A) ≠ 0 :=
    ((root_isPrimitiveRoot A n hn).isUnit (ne_of_gt hn)).ne_zero
  apply mul_right_cancel₀ (pow_ne_zero (n - 1) hzero)
  calc
    conjugationHom A n hn (AdjoinRoot.root (cyclotomic n A) ^ (n - 1)) *
        AdjoinRoot.root (cyclotomic n A) ^ (n - 1) =
      conjugationHom A n hn (AdjoinRoot.root (cyclotomic n A) ^ (n - 1) *
        AdjoinRoot.root (cyclotomic n A)) := by rw [map_mul, conjugationHom_root]
    _ = 1 := by rw [root_pow_pred_mul_root A n hn, map_one]
    _ = AdjoinRoot.root (cyclotomic n A) *
        AdjoinRoot.root (cyclotomic n A) ^ (n - 1) := by
      simpa only [mul_comm] using (root_pow_pred_mul_root A n hn).symm

/-- The actual involutive algebra automorphism inverting the cyclotomic root. -/
def cyclotomicConjugation : CyclotomicRing A n ≃ₐ[A] CyclotomicRing A n :=
  AlgEquiv.ofAlgHom (conjugationHom A n hn) (conjugationHom A n hn)
    (conjugationHom_comp_self A n hn) (conjugationHom_comp_self A n hn)

@[simp] theorem cyclotomicConjugation_root :
    cyclotomicConjugation A n hn (AdjoinRoot.root (cyclotomic n A)) =
      AdjoinRoot.root (cyclotomic n A) ^ (n - 1) :=
  conjugationHom_root A n hn

variable [IsDiscreteValuationRing (CyclotomicRing A n)]

@[simp] theorem cyclotomicConjugation_addVal (x : CyclotomicRing A n) :
    addVal (CyclotomicRing A n) (cyclotomicConjugation A n hn x) =
      addVal (CyclotomicRing A n) x :=
  addVal_ringEquiv (cyclotomicConjugation A n hn).toRingEquiv x

end Cyclotomic

end CirculantHadamard.RamifiedConjugation

end

end OAI


