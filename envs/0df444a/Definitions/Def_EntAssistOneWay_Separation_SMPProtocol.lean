-- Prove2me | Definitions.Def_EntAssistOneWay_Separation_SMPProtocol
-- name    : EntAssistOneWay_Separation_SMPProtocol
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:44:18.223446+00:00
-- url     : https://prove2.me/theorems/fbf04b90-8aaf-4ae1-b70b-e9d370bb09ae
-- title:
--   Classical SMP with randomness shared only by the senders
-- statement:
--   Alice sends $c_A$ bits and Bob sends $c_B$ bits to a referee. Their shared randomness is a law $\nu$ on pairs of deterministic encoding tables $(u:X\to[2^{c_A}],v:Y\to[2^{c_B}])$. A single deterministic function $R$ of the two messages defines
--   $$a(x,y)=\sum_{u,v}\nu(u,v)\,1[R(u(x),v(y))=1].$$
--
--   The referee sees neither the random seed nor the input tables. The communication cost is $c_A+c_B$. This is exactly the senders-only shared randomness convention of §3.1, needed for the second clause of Theorem 4.3.
-- source:
--   Ryan Anselm, Srijita Kundu, Olivier Lalonde, Ashwin Nayak, STOC 2027 submission #228 (October 2026), p. 15, §3.1 SMP convention; p. 24, proof of Theorem 4.3

import Definitions.Def_EntAssistOneWay_Separation_Probability

open scoped BigOperators ComplexOrder
open Classical
set_option autoImplicit false

namespace EntAssistOneWay.Separation

noncomputable section

/-- Public randomness shared only by the senders. The deterministic referee sees
only the two messages, never the seed. -/
structure SMPProtocol (X Y : Type) [Fintype X] [Fintype Y] (cA cB : ℕ) where
  law : FiniteLaw ((X → Fin (2 ^ cA)) × (Y → Fin (2 ^ cB)))
  referee : Fin (2 ^ cA) → Fin (2 ^ cB) → Bool

def smpAccept {X Y : Type} [Fintype X] [Fintype Y] {cA cB : ℕ}
    (P : SMPProtocol X Y cA cB) (x : X) (y : Y) : ℝ :=
  ∑ t, P.law.mass t * if P.referee (t.1 x) (t.2 y) then 1 else 0

end

end EntAssistOneWay.Separation


