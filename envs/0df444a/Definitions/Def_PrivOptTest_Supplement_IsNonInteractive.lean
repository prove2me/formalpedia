-- Prove2me | Definitions.Def_PrivOptTest_Supplement_IsNonInteractive
-- name    : PrivOptTest_Supplement_IsNonInteractive
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:33:17.181193+00:00
-- url     : https://prove2.me/theorems/8af550cc-1e08-4186-be75-6a76c88a113b
-- title:
--   Non-interactive two-party protocols
-- statement:
--   A two-party protocol is **non-interactive** when each party sends exactly one message, computed from its own dataset, its private coins and the public coins, and the common output is a function of the public coins and the two messages.
--
--   On the base mission's protocol model this means: Alice speaks in round $0$; Bob's round-$1$ message does not depend on Alice's round-$0$ message; the run does not stop before round $2$; and at round $2$ it stops with output $g(\omega_P,m_0,m_1)$ for a fixed map $g$ of the public coins $\omega_P$ and the two messages $m_0,m_1$. Public randomness is allowed.
--
--   This is the protocol class of Theorems 4.9 and 4.11, the testers for small datasets.
-- source:
--   M. Haghifam, K. K. Patel, A. Blum, G. Fanti, J. Ziani, Should We Combine Our Data? Algorithms and Limits for Privately Assessing Data Sharing, arXiv:2611.03599 (manuscript sha256 4ac94dcf…), Theorem 4.9, p.33; Theorem 4.11, p.34; proofs pp.51–53

import Mathlib
import Definitions.Def_PrivOptTest_Protocol

namespace PrivOptTest

namespace Supplement

/-- **A non-interactive protocol** (arXiv:2611.03599, manuscript sha256 4ac94dcf…, Theorems 4.9 and
4.11, pp.33–34): each party sends one message, computed from its own input, its private coins and the
public coins only, and the common output is a function of the public coins and the two messages.

On the base mission's `Protocol`: Alice speaks at round 0 (her message sees no earlier message); Bob's
round-1 message does not depend on Alice's round-0 message; the run does not stop before round 2; and
at round 2 it stops with the output `g ωP (h 0) (h 1)`.

**Formalization Note.** Public randomness is allowed (Algorithm 4 uses public random signs). -/
def IsNonInteractive {In Out : Type} (Pr : Protocol In Out) : Prop :=
  (∀ (s : In) (ωB : Pr.ΩB) (ωP : Pr.ΩP) (h h' : Fin 1 → Pr.Msg),
      Pr.nextB 1 s ωB ωP h = Pr.nextB 1 s ωB ωP h') ∧
    (∀ (ωP : Pr.ΩP) (h : Fin 0 → Pr.Msg), Pr.stop 0 ωP h = Sum.inr ()) ∧
    (∀ (ωP : Pr.ΩP) (h : Fin 1 → Pr.Msg), Pr.stop 1 ωP h = Sum.inr ()) ∧
    ∃ g : Pr.ΩP → Pr.Msg → Pr.Msg → Out,
      ∀ (ωP : Pr.ΩP) (h : Fin 2 → Pr.Msg), Pr.stop 2 ωP h = Sum.inl (g ωP (h 0) (h 1))

end Supplement

end PrivOptTest


