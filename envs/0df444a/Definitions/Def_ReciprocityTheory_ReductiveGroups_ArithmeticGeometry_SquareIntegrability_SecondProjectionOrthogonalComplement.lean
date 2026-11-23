-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SecondProjectionOrthogonalComplement
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SecondProjectionOrthogonalComplement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:34:04.083179+00:00
-- url     : https://prove2.me/theorems/0b41109d-fb93-4506-818a-9b48c3afc1ed
-- title:
--   Second Projection Orthogonal Complement
-- statement:
--   Definitions and structural lemmas for Second Projection Orthogonal Complement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SecondProjectionOrthogonalComplement.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.I2
open Complex
open scoped InnerProductSpace
noncomputable section
namespace Col
variable {ι : Type} [Fintype ι]
variable (K : Submodule ℝ (EuclideanSpace ℂ ι))
abbrev dK : ℕ := Module.finrank ℝ K
def ob : OrthonormalBasis (Fin (dK K)) ℝ K := stdOrthonormalBasis ℝ K
def e (k : Fin (dK K)) : EuclideanSpace ℂ ι := (ob K k : EuclideanSpace ℂ ι)
def z (k : Fin (dK K)) (v : EuclideanSpace ℂ ι) : ℂ := Hf v (e K k)
def p1 (v : EuclideanSpace ℂ ι) : EuclideanSpace ℂ ι := ∑ k, z K k v • e K k
def p2 (v : EuclideanSpace ℂ ι) : EuclideanSpace ℂ ι := v - p1 K v
def uc (v : EuclideanSpace ℂ ι) : EuclideanSpace ℂ ι := ∑ k, (z K k v).im • e K k
def S (v : EuclideanSpace ℂ ι) : ℂ := ∑ k, z K k v ^ 2
section iso
variable {K}
variable (hK : ∀ a ∈ K, ∀ b ∈ K, (Hf a b).im = 0)
include hK
end iso
section V2
def span1 : Submodule ℂ (EuclideanSpace ℂ ι) := Submodule.span ℂ (Set.range (e K))
def V2 : Submodule ℂ (EuclideanSpace ℂ ι) := (span1 K)ᗮ
abbrev gB : ℕ := Module.finrank ℂ (V2 K)
def ob2 : OrthonormalBasis (Fin (gB K)) ℂ (V2 K) := stdOrthonormalBasis ℂ (V2 K)
def jj (t : EuclideanSpace ℂ (Fin (gB K))) : EuclideanSpace ℂ ι := ((ob2 K).repr.symm t : V2 K)
def wmap : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ (Fin (gB K)) :=
  (ob2 K).repr.toContinuousLinearEquiv.toContinuousLinearMap ∘L (V2 K).orthogonalProjectionOnto
variable {K}
variable (hK : ∀ a ∈ K, ∀ b ∈ K, (Hf a b).im = 0)
include hK
end V2
end Col
end
end ReciprocityTheory.ChartRestriction.G.I2


