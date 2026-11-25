-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenSectT
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_GenSectT
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T01:44:53.892893+00:00
-- url     : https://prove2.me/theorems/9a7ace5d-c777-42f6-a647-6d32126ec9db
-- title:
--   Gen Sect T
-- statement:
--   Definitions and structural lemmas for Gen Sect T, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/GenSectT.lean

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenSect
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
variable (K Ω Kl K' : Type) [Field K] [Field Ω] [Algebra K Ω] [Field Kl] [Field K'] [Algebra K Kl]
  [Algebra Kl K'] [Algebra K K'] [IsScalarTower K Kl K']
abbrev TZ : Type := K' ⊗[Kl] (Kl ⊗[K] Ω)
variable {K Ω Kl K'} {D m : ℕ}
variable (K Kl) in

def tsec (t : Fin (D + 1) × Fin m → K') (v : Fin m → Ω) (i : Fin (D + 1)) : TZ K Ω Kl K' :=
  ∑ k, t (i, k) ⊗ₜ[Kl] ((1 : Kl) ⊗ₜ[K] v k)
variable (K Kl) in

def tJ (t : Fin (D + 1) × Fin m → K') (v : Fin m → Ω) : Ideal (Localization.Away (tsec K Kl t v 0)) :=
  Ideal.span (Set.range fun i : Fin D =>
    algebraMap (TZ K Ω Kl K') (Localization.Away (tsec K Kl t v 0)) (tsec K Kl t v i.succ) *
      IsLocalization.Away.invSelf (tsec K Kl t v 0))
end Formalism.L2.Pj.GenSect


