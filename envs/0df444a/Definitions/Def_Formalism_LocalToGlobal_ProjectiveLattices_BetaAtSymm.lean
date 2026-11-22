-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_BetaAtSymm
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_BetaAtSymm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:27:55.794019+00:00
-- url     : https://prove2.me/theorems/478b3fa9-2802-4c36-a3d1-c37a81d16c97
-- title:
--   Beta At Symm
-- statement:
--   Definitions and structural lemmas for Beta At Symm, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/BetaAtSymm.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThickTransComp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open AlgebraicGeometry CategoryTheory
variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
def ordPsi (D : DegPre R) (χ : D.X) : ℕ∞ :=
  ⨆ (n : ℕ) (_ : D.PsiIn χ (IsLocalRing.maximalIdeal R ^ n)), (n : ℕ∞)
def betaZ (D : DegPre R) (a b : D.X) : ℤ :=
  ((ordPsi D (a + b)).toNat : ℤ) - ((ordPsi D a).toNat : ℤ) - ((ordPsi D b).toNat : ℤ)
def ordNat (R : Type) [CommRing R] [IsLocalRing R] (n : ℕ) : ℕ∞ :=
  ⨆ (k : ℕ) (_ : (n : R) ∈ IsLocalRing.maximalIdeal R ^ k), (k : ℕ∞)
def betaP (D : DegPre R) (p : ℕ) (a b : D.X) : ℝ :=
  (betaZ D a b : ℝ) / ((ordNat R p).toNat : ℝ)
section At
variable {R : Type} [CommRing R] [IsDomain R]
def PsiCoord (D : DegPre R) (χ : D.X) (r : R) : Prop :=
  ∃ (j : PUnit → D.P.L.ι) (_ : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ (D.c χ).left ⁻¹ᵁ D.P.L.U (j PUnit.unit))
    (h : jK R ⁻¹ᵁ ⊤ ≤ (LB.LinComb D.P.L (K := PUnit) (fun _ => D.xK χ) (fun _ => -1)).U j),
    ((jK R).app ⊤).hom (DegPre.toOpen (R := R) ⊤ r) = ((TK R).left.presheaf.map (homOfLE h).op).hom ((D.psi χ).s j).val
def vPsiAt (D : DegPre R) {C : Type} [NormedField C] (f : R →+* C) (p : ℕ) (χ : D.X) : ℝ :=
  open Classical in
  if h : ∃ r, PsiCoord D χ r then -Real.logb p ‖f h.choose‖ else 0
def betaAt (D : DegPre R) {C : Type} [NormedField C] (f : R →+* C) (p : ℕ) (a b : D.X) : ℝ :=
  vPsiAt D f p (a + b) - vPsiAt D f p a - vPsiAt D f p b
end At
end Formalism.L2.Pj


