-- Prove2me | Definitions.Def_NSWBetter_util
-- name    : NSWBetter_util
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:50:53.690305+00:00
-- url     : https://prove2.me/theorems/aaf90922-7066-4255-a00b-c38730c0788b
-- title:
--   Utility $v_i(X_i)$ of an agent under an allocation
-- statement:
--   For an allocation $X$, the **utility** of agent $i$ is $v_i(X_i)=\sum_{g\in X_i}v_i(g)$, the additive value of its bundle.
-- source:
--   Viswanathan, A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations, arXiv:2607.13340 (held version, sha256 08811cb468c2df39231dca4222c5af94163587c7c83e205e50bbf0b91fc1deb3), Section 2, p.8 (agent i receives utility vi(Xi))

import Mathlib
import Definitions.Def_NSWBetter_Inst
import Definitions.Def_NSWBetter_Alloc

namespace NSWBetter

/-- **Utility of an agent.**
Viswanathan, *A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations*, arXiv:2607.13340 (held version, sha256 08811cb4…), Section 2, p.8: "Each agent i is allocated the bundle Xi and receives utility vi(Xi)"; additivity, p.8.

`util I X i = Σ_(g : X g = some i) v i g = v_i(X_i)` (as a real number). -/
noncomputable def util (I : Inst) (X : Alloc I) (i : Fin I.n) : ℝ :=
  ∑ g ∈ Finset.univ.filter (fun g => X g = some i), ((I.v i g : ℚ) : ℝ)

end NSWBetter


