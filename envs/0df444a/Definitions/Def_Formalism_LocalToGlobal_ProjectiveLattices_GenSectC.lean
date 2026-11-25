-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenSectC
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_GenSectC
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T01:30:30.054681+00:00
-- url     : https://prove2.me/theorems/85899b16-a697-4e2b-9520-b86eaae10cb3
-- title:
--   Gen Sect C
-- statement:
--   Definitions and structural lemmas for Gen Sect C, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/GenSectC.lean

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenSectB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.Pj.GenSect
open MvPolynomial
open scoped TensorProduct
variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {D m : ℕ}
theorem psi_kt (x : Fin m → Ω) (j₀ : Fin m) (q : KT K D m) :
    psi x j₀ (ktToΩ K Ω D m q) = aeval (gs x j₀) q := by
  show aeval (gs x j₀) (MvPolynomial.map (algebraMap K Ω) q) = aeval (gs x j₀) q
  rw [MvPolynomial.aeval_map_algebraMap]
def Phi (x : Fin m → Ω) (j₀ : Fin m) (hinj : ∀ q : KT K D m, q ≠ 0 → aeval (gs x j₀) q ≠ 0) :
    RS K Ω D m →+* FractionRing (CT Ω D j₀) :=
  IsLocalization.lift (M := KTS K Ω D m)
    (g := (algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀))).comp (psi x j₀).toRingHom) (by
      rintro ⟨s, hs⟩
      obtain ⟨q, hq, rfl⟩ := hs
      refine isUnit_iff_ne_zero.mpr ?_
      show algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀)) (psi x j₀ (ktToΩ K Ω D m q)) ≠ 0
      rw [psi_kt]
      exact fun h => hinj q (nonZeroDivisors.ne_zero hq)
        ((IsFractionRing.injective (CT Ω D j₀) (FractionRing (CT Ω D j₀))) (h.trans (map_zero _).symm)))
end Formalism.L2.Pj.GenSect


