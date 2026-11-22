-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HenselRootsBounded
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_HenselRootsBounded
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:36:46.024816+00:00
-- url     : https://prove2.me/theorems/538094b8-b6ae-4aab-8138-56cb5e0f6c54
-- title:
--   Hensel Roots Bounded
-- statement:
--   Definitions and structural lemmas for Hensel Roots Bounded, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HenselRootsBounded.lean

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
namespace Formalism.FourierDecayAlt.P.HenselRootsBounded
def Pk {K : Type} [CommRing K] (R : Subring K) (ϖ : Kˣ) (k : ℤ) : AddSubgroup K where
  carrier := {x | ((ϖ ^ (-k) : Kˣ) : K) * x ∈ R}
  zero_mem' := by
    show ((ϖ ^ (-k) : Kˣ) : K) * 0 ∈ R
    rw [mul_zero]; exact R.zero_mem
  add_mem' := by
    intro a b ha hb
    show ((ϖ ^ (-k) : Kˣ) : K) * (a + b) ∈ R
    rw [mul_add]; exact R.add_mem ha hb
  neg_mem' := by
    intro a ha
    show ((ϖ ^ (-k) : Kˣ) : K) * (-a) ∈ R
    rw [mul_neg]; exact R.neg_mem ha
section Alg
variable {K : Type} [CommRing K] {R : Subring K} {ϖ : Kˣ}
end Alg
structure Ctx (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
    (R : Subring K) (ϖ : Kˣ) : Prop where
  t2 : T2Space K
  isOpen : IsOpen (R : Set K)
  isCompact : IsCompact (R : Set K)
  mem : (ϖ : K) ∈ R
  ex : ∀ x : K, ∃ m : ℕ, (ϖ : K) ^ m * x ∈ R
  red : IsReduced K
  nat : ∀ n : ℕ, n ≠ 0 → IsUnit (n : K)
section Top
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
  {R : Subring K} {ϖ : Kˣ}
end Top
section Top2
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
  {R : Subring K} {ϖ : Kˣ}
end Top2
section Core
variable {K : Type} [CommRing K]
open Classical in

def TT (s : ℕ) (Cut : Set K) (τ : Kˣ) (F : Kˣ → ℂ) (c : Kˣ) : ℂ :=
  if (c : K) ∈ Cut then ∑ᶠ z : Kˣ, if z ^ s = τ * c then F z else 0 else 0
def mulQ (R : Subring K) (lam : Kˣ) (h1 : (lam : K) ∈ R) (h2 : ((lam⁻¹ : Kˣ) : K) ∈ R) :
    (K ⧸ R.toAddSubgroup) ≃ (K ⧸ R.toAddSubgroup) where
  toFun := QuotientAddGroup.map _ _ (AddMonoidHom.mulLeft (lam : K))
    (by intro r hr; exact R.mul_mem h1 hr)
  invFun := QuotientAddGroup.map _ _ (AddMonoidHom.mulLeft ((lam⁻¹ : Kˣ) : K))
    (by intro r hr; exact R.mul_mem h2 hr)
  left_inv := by
    intro x
    induction x using QuotientAddGroup.induction_on with
    | H x =>
      show (((((lam⁻¹ : Kˣ) : K) * ((lam : K) * x) : K)) : K ⧸ R.toAddSubgroup) = x
      rw [← mul_assoc, ← Units.val_mul]; simp
  right_inv := by
    intro x
    induction x using QuotientAddGroup.induction_on with
    | H x =>
      show ((((lam : K) * (((lam⁻¹ : Kˣ) : K) * x) : K)) : K ⧸ R.toAddSubgroup) = x
      rw [← mul_assoc, ← Units.val_mul]; simp
end Core
section Main
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
  {R : Subring K} {ϖ : Kˣ}
end Main
end Formalism.FourierDecayAlt.P.HenselRootsBounded


