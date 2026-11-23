-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_BlockDegOfScale
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_BlockDegOfScale
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:37:44.262802+00:00
-- url     : https://prove2.me/theorems/8a9633b8-7202-428e-a1a2-31d24aaa3bc8
-- title:
--   Block Deg Of Scale
-- statement:
--   Definitions and structural lemmas for Block Deg Of Scale, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/BlockDegOfScale.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ScaleMultiHomogeneous
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.T0
open MvPolynomial
section Gen
variable {K : Type} [Field K] {D N : ℕ}
end Gen
section Blocks
variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {D N : ℕ}
def IsBaseBlockVar (b : Fin (D + 1)) (v : SVar D N) : Prop :=
  Sum.elim (fun _ => b = 0) (fun w : Fin (D + 1) × Fin N => w.1 = b) v
instance (b : Fin (D + 1)) : DecidablePred (IsBaseBlockVar (D := D) (N := N) b) := by
  intro v
  cases v <;> simp only [IsBaseBlockVar, Sum.elim_inl, Sum.elim_inr] <;> infer_instance
noncomputable def tauPG (b : Fin (D + 1)) (u : Kˣ) :
    MvPolynomial (SVar D N) Ω ≃ₐ[Ω] MvPolynomial (SVar D N) Ω :=
  scaleEquiv (IsBaseBlockVar b) (Units.map (algebraMap K Ω).toMonoidHom u)
noncomputable def tauFG (b : Fin (D + 1)) (u : Kˣ) : OmS Ω D N ≃+* OmS Ω D N :=
  IsFractionRing.ringEquivOfRingEquiv (tauPG (Ω := Ω) (D := D) (N := N) b u).toRingEquiv
end Blocks
end ReciprocityTheory.ChartRestriction.G.T0


