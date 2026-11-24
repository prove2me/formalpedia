-- Prove2me | Definitions.Def_Formalism_YangianSpanCharacter_StatementB
-- name    : Formalism_YangianSpanCharacter_StatementB
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T11:47:44.344807+00:00
-- url     : https://prove2.me/theorems/e94247c4-e608-4f1b-b4d5-6a6b1361fe8a
-- title:
--   Statement B
-- statement:
--   Definitions and structural lemmas for Statement B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/YangianSpanCharacter/StatementB.lean

import Definitions.Def_Formalism_FormalDegreeBessel_FinalWR
import Definitions.Def_Formalism_YangianSpanCharacter_ExchangeGen
import Definitions.Def_Formalism_YangianSpanCharacter_TJTrev
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.YangianSpanCharacter.B
open Matrix Formalism.YangianSpanCharacter.T Formalism.QuantumDeterminants
def TJTReal : Prop :=
  ∀ (m : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (l : Fin m) (Y : ℂ),
    (Tm (Y + 1) (pEnd (E := E) l) (cEnd l) (ciEnd l))ᵀ * Formalism.YangianSpanCharacter.T.J (Module.End ℂ (WSm m E)) *
        Tm Y (pEnd (E := E) l) (cEnd l) (ciEnd l) = Formalism.YangianSpanCharacter.T.J (Module.End ℂ (WSm m E))
def TvJTsReal : Prop :=
  ∀ (m : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (l : Fin m) (Y : ℂ),
    Tm (Y + 1) (-pbEnd (E := E) l) (cbEnd l) (cbiEnd l) * Formalism.YangianSpanCharacter.T.J (Module.End ℂ (WSm m E)) *
        (Tm Y (-pbEnd (E := E) l) (cbEnd l) (cbiEnd l))ᵀ = Formalism.YangianSpanCharacter.T.J (Module.End ℂ (WSm m E))
def RTTReal : Prop :=
  ∀ (m : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (l : Fin m) (Y Y' : ℂ),
    ((Y' - Y) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) (Module.End ℂ (WSm m E))) -
          Pf (Module.End ℂ (WSm m E))) * T1 Y' (pEnd (E := E) l) (cEnd l) (ciEnd l) *
        T2 Y (pEnd (E := E) l) (cEnd l) (ciEnd l) =
      T2 Y (pEnd (E := E) l) (cEnd l) (ciEnd l) * T1 Y' (pEnd (E := E) l) (cEnd l) (ciEnd l) *
        ((Y' - Y) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) (Module.End ℂ (WSm m E))) -
          Pf (Module.End ℂ (WSm m E)))
def ExchangeTReal : Prop :=
  ∀ (m : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (l : Fin m) (Y Yb : ℂ),
    Tbt Yb (pEnd (E := E) l) (cEnd l) (ciEnd l) *
        pt1 ((Yb - Y) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) (Module.End ℂ (WSm m E))) -
          Pf (Module.End ℂ (WSm m E))) * T1 Y (pEnd (E := E) l) (cEnd l) (ciEnd l) =
      T1 Y (pEnd (E := E) l) (cEnd l) (ciEnd l) *
        pt1 ((Yb - Y) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) (Module.End ℂ (WSm m E))) -
          Pf (Module.End ℂ (WSm m E))) * Tbt Yb (pEnd (E := E) l) (cEnd l) (ciEnd l)
end Formalism.YangianSpanCharacter.B


