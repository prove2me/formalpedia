-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_IntegralExtensions
-- name    : liuyao_ca_fd889115_k1_Analysis_IntegralExtensions
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T17:53:44.962034+00:00
-- url     : https://prove2.me/theorems/680c902a-3072-441b-98a3-d23b30c2dc27
-- title:
--   Computable analysis · IntegralExtensions · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/IntegralExtensions.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_IntegralSpecification

set_option autoImplicit true

/-!
# Complex and exhaustion integrals use the same specification

A complex path is integrated through its supplied real and imaginary
pullbacks on a rational parameter interval. The path, differential, and
pullback agreement must be justified by the caller; a box-valued program alone
does not certify a path integral.

An improper integral additionally specifies a family of compact intervals and
convergence of their certified integrals. Its uniqueness does not construct
any new integral. Different exhaustions require a separate comparison proof.
-/
namespace ComputableAnalysis
namespace Integral

/-- Orientation changes the sign of the value, while the semantic test always
certifies the entire ordered segment. Rational endpoints may coincide. -/
inductive HasOrientedIntegral (F : FunctionOnInterval) (a b : Rat) (I : RealCompute) : Prop
  | forward (ha : F.lower ≤ a) (hab : a ≤ b) (hb : b ≤ F.upper)
      (integral : HasIntegral (F.restrict a b ha hab hb) I) :
      HasOrientedIntegral F a b I
  | reverse (hb : F.lower ≤ b) (hba : b < a) (ha : a ≤ F.upper)
      (valid : I.Valid)
      (integral : HasIntegral (F.restrict b a hb (Rat.le_of_lt hba) ha) (-I)) :
      HasOrientedIntegral F a b I

theorem HasOrientedIntegral.unique {F : FunctionOnInterval} {a b : Rat} {I J : RealCompute}
    (hI : HasOrientedIntegral F a b I) (hJ : HasOrientedIntegral F a b J) :
    I.Equiv J := by
  cases hI with
  | forward ha hab hb hI =>
    cases hJ with
    | forward _ _ _ hJ => exact hI.unique hJ
    | reverse _ hba _ _ _ => exact False.elim (by grind)
  | reverse hb hba ha hv hI =>
    cases hJ with
    | forward _ hab _ _ => exact False.elim (by grind)
    | reverse _ _ _ _ hJ =>
      have h := hI.unique hJ
      intro n
      have ho := (RealCompute.compareAt_overlap_iff (-I) (-J) n n).1 (h n)
      apply (RealCompute.compareAt_overlap_iff I J n n).2
      change -(I.compute n).hi ≤ -(J.compute n).lo ∧
        -(J.compute n).hi ≤ -(I.compute n).lo at ho
      constructor <;> grind

structure HasComplexIntegral (re im : FunctionOnInterval) (I : ComplexCompute) : Prop where
  same_lower : re.lower = im.lower
  same_upper : re.upper = im.upper
  valid : I.Valid
  real : HasIntegral re I.realPart
  imag : HasIntegral im I.imagPart

theorem HasComplexIntegral.unique {re im : FunctionOnInterval} {I J : ComplexCompute}
    (hI : HasComplexIntegral re im I) (hJ : HasComplexIntegral re im J) :
    I.Equiv J := by
  intro n
  have hr := (RealCompute.compareAt_overlap_iff I.realPart J.realPart n n).1
    (hI.real.unique hJ.real n)
  have hi := (RealCompute.compareAt_overlap_iff I.imagPart J.imagPart n n).1
    (hI.imag.unique hJ.imag n)
  apply (ComplexCompute.compareAt_overlap_iff I J n n).2
  exact ⟨⟨hr.1, hi.1⟩, ⟨hr.2, hi.2⟩⟩

/-- Exact closeness expressed through all rational approximations. -/
def Within (I J : RealCompute) (eps : Rat) : Prop :=
  ∀ n m, (I.compute n).lo ≤ (J.compute m).hi + eps ∧
    (J.compute m).lo ≤ (I.compute n).hi + eps

/-- A limit of actual compact integrals along a supplied exhaustion.
The compact-witness field prevents a vacuous convergence condition when none
of the finite integrals have been constructed. Domain coverage and any
substitution identifying an improper integral belong to the exhaustion proof. -/
structure HasIntegralLimit (F : Nat → FunctionOnInterval) (I : RealCompute) : Prop where
  valid : I.Valid
  compact : ∀ n, ∃ J, HasIntegral (F n) J
  converges : ∀ eps : QPos, ∃ N, ∀ n, N ≤ n →
    ∀ J, HasIntegral (F n) J → Within I J eps.val

theorem HasIntegralLimit.unique {F : Nat → FunctionOnInterval} {I J : RealCompute}
    (hI : HasIntegralLimit F I) (hJ : HasIntegralLimit F J) : I.Equiv J := by
  have hle : ∀ (X Y : RealCompute), HasIntegralLimit F X →
      HasIntegralLimit F Y → X.Le Y := by
    intro X Y hX hY n m
    by_cases h : (X.compute n).lo ≤ (Y.compute m).hi
    · exact h
    exfalso
    let gap := (X.compute n).lo - (Y.compute m).hi
    have hg : 0 < gap / 4 := by dsimp [gap]; grind
    let eps : QPos := ⟨gap/4, hg⟩
    obtain ⟨Nx, hx⟩ := hX.converges eps
    obtain ⟨Ny, hy⟩ := hY.converges eps
    obtain ⟨K, hK⟩ := hX.compact (max Nx Ny)
    obtain ⟨s, hs⟩ := hK.valid.2.2 eps
    have hw := hs s (Nat.le_refl _)
    have hxk := (hx (max Nx Ny) (Nat.le_max_left _ _) K hK n s).1
    have hyk := (hy (max Nx Ny) (Nat.le_max_right _ _) K hK m s).2
    change (K.compute s).width ≤ gap/4 at hw
    change (X.compute n).lo ≤ (K.compute s).hi + gap/4 at hxk
    change (K.compute s).lo ≤ (Y.compute m).hi + gap/4 at hyk
    dsimp [gap] at hw hxk hyk
    grind [QInterval.width]
  exact RealCompute.equiv_of_le_of_ge (hle I J hI hJ) (hle J I hJ hI)

end Integral
end ComputableAnalysis


