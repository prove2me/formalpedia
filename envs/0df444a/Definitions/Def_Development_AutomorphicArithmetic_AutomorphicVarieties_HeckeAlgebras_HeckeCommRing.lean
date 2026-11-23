-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_HeckeAlgebras_HeckeCommRing
-- name    : Development_AutomorphicArithmetic_AutomorphicVarieties_HeckeAlgebras_HeckeCommRing
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:42:25.301948+00:00
-- url     : https://prove2.me/theorems/82713b02-5e1f-4c4b-a1df-17c44ecee6b0
-- title:
--   Hecke Comm Ring
-- statement:
--   Definitions and structural lemmas for Hecke Comm Ring, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/HeckeAlgebras/HeckeCommRing.lean

import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_HeckeAlgebras_ContinuousTorusCharacter
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_CommutativeAlgebra_ResMapBijective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsLocalRing
namespace UpperTheory.V.Hi
variable {A M ι : Type} [CommRing A] [AddCommGroup M] [Module A M]
instance heckeCommRing (Y : Submodule A M) (op : ι → Module.End A M) [h : Fact (CommOn Y op)] : CommRing (heckeAlg Y op) :=
  { (inferInstance : Ring (heckeAlg Y op)) with
    mul_comm := fun a b => by
      have key : ∀ s ∈ {t : Module.End A Y | ∃ i, Restr t (op i)}, ∀ t ∈ {t : Module.End A Y | ∃ i, Restr t (op i)},
          s * t = t * s := by
        rintro s ⟨i, hi⟩ t ⟨j, hj⟩
        refine LinearMap.ext fun y => Subtype.ext ?_
        change (s (t y) : M) = t (s y)
        rw [hi, hj, hj, hi]
        exact h.out.2 i j y y.2
      exact (Algebra.adjoinCommSemiringOfComm A key).mul_comm a b }
def heckeGen (Y : Submodule A M) (op : ι → Module.End A M) [h : Fact (CommOn Y op)] (i : ι) : heckeAlg Y op :=
  ⟨(op i).restrict (h.out.1 i), Algebra.subset_adjoin ⟨i, fun _ => rfl⟩⟩
end UpperTheory.V.Hi


