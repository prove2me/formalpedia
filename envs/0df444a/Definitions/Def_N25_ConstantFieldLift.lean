-- Prove2me | Definitions.Def_N25_ConstantFieldLift
-- name    : N25_ConstantFieldLift
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:10:38.315218+00:00
-- url     : https://prove2.me/theorems/ca2f2211-821b-4438-a97a-96f3538ff3bb
-- title:
--   Constant-field lifts of places
-- statement:
--   For a rational place $P$ of the level-$25$ function field and a geometric place $P'$ after extension to $\overline{ℚ}$, the file defines $P'$ to be a constant-field lift of $P$ when $$\mathcal O_{P'}\cap F_{ℚ}=\mathcal O_P\quad\text{and}\quad \operatorname{ord}_{P'}(f)=\operatorname{ord}_P(f)\ \text{for every }f∈F_{ℚ}.$$ This predicate records both valuation-ring descent and preservation of orders under constant-field extension.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_Endgame
set_option autoImplicit false
namespace N25.Endgame

def IsConstantFieldLift25 (P : QPlace) (P' : GPlace) : Prop :=
  P'.toValuationSubring.comap emb25.toRingHom = P.toValuationSubring ∧
    ∀ f : FQ, P'.ord (emb25 f) = P.ord f

end N25.Endgame


