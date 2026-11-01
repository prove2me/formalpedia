-- Prove2me | Definitions.Def_ContactTopology_CoreSeparation
-- name    : ContactTopology_CoreSeparation
-- status  : Definition
-- author  : @Johan Mercedes
-- created : 2026-10-31T06:01:49.9595+00:00
-- url     : https://prove2.me/theorems/a82dfa3d-45e3-4a68-a447-6f844d7a3ff4
-- title:
--   Standard cores, contact rotations and round neighborhoods
-- statement:
--   Write points of $\mathbb R^4$ as $(q,p)\in\mathbb R^2\times\mathbb R^2$. Define the standard real core $c(u)=(u,0)$ for $u\in S^1$, the normalization $a_s=(1+4s^2)^{-1/2}$, and the ambient linear maps
--   $$R_s(q,p)=a_s(q+2sp,p-2sq).$$
--   For a supplied equivariant sphere contactomorphism $F$, the notation $C_F$ denotes $F(c(S^1))$. The round sets used for its neighborhoods are
--   $$T_r=\{(q,p)\in S^3:|p|^2\le r^2|q|^2\}.$$
--   These are data definitions. Smoothness, invertibility, the contact identity, separation, and existence of a contact isotopy are proved in the associated theorem.
-- source:
--   Original coordinate auxiliary lemma for the standard contact sphere, proved in the accompanying Lean submission. The critical-value step uses Mathlib, Mathlib/MeasureTheory/Function/Jacobian.lean, MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero, at revision 0df444a360eaa60ab8c11dca51a86af692955474: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Function/Jacobian.lean . Context: Hyunki Min, The contact mapping class group and rational unknots in lens spaces, arXiv:2207.03590v2, https://arxiv.org/html/2207.03590v2, Proposition 3.5. This is a separately proved separation lemma, not a formalization of Proposition 3.5 or a claim of core classification.

import Definitions.Def_BirkhoffGlobalSection_SphereContact
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace ContactTopology.CoreSeparation
open BirkhoffGlobalSection Set Function
noncomputable section
def scale (s : ℝ) : ℝ := (Real.sqrt (1+4*s^2))⁻¹

def rotation (s : ℝ) (y : Phase) : Phase :=
  scale s • ![y 0+2*s*y 2,y 1+2*s*y 3,y 2-2*s*y 0,y 3-2*s*y 1]


def standardCore (u : Plane) : Phase := ![u 0,u 1,0,0]
def coreSet (F : EquivariantSphereContactomorphism) : Set Phase :=
  (F.toFun ∘ standardCore) '' unitCircle
def standardTube (r : ℝ) : Set Phase :=
  {y | y ∈ unitThreeSphere ∧ wNormSq y ≤ r^2*zNormSq y}


end
end ContactTopology.CoreSeparation


