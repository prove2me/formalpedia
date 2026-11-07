-- Prove2me | Definitions.Def_NSWBetter_decodeCLP
-- name    : NSWBetter_decodeCLP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:52:31.053337+00:00
-- url     : https://prove2.me/theorems/189ccb9a-bb73-4c29-9406-36fc804ed243
-- title:
--   Reading a configuration LP solution from its entries
-- statement:
--   A list of entries $(i,S,q)$ is read as the vector $y$ with $y_{i,S}$ the total of the values $q$ listed for agent $i$ and bundle $S$ (entries naming a good index $\ge m$ are ignored); unlisted entries are $0$.
-- source:
--   Viswanathan, A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations, arXiv:2607.13340 (held version, sha256 08811cb468c2df39231dca4222c5af94163587c7c83e205e50bbf0b91fc1deb3), Theorem 2.5, p.10 ("represented using a list of the non-zero entries")

import Mathlib
import Definitions.Def_NSWBetter_Inst
import Definitions.Def_NSWBetter_Entry

namespace NSWBetter

open Classical in
/-- **A configuration LP vector from its entry list.**
Viswanathan, *A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations*, arXiv:2607.13340 (held version, sha256 08811cb4…), Theorem 2.5, p.10: "represented using a list of the non-zero entries".

`decodeCLP I l i S` is the sum of the values `q` of the entries `(i, S', q)` of `l` whose agent is `i`, whose goods are all `< m`, and whose set of goods is `S`; it is `0` if there is none.

**Formalization Note.** Every list is read as some vector `y`; entries with an out-of-range good are ignored and repeated entries add up. Validity of `y` is stated separately. -/
noncomputable def decodeCLP (I : Inst) (l : List Entry) : Fin I.n → Finset (Fin I.m) → ℝ :=
  fun i S => ((l.filter fun e => decide (e.1 = i.val ∧ (∀ g ∈ e.2.1, g < I.m) ∧
      Finset.univ.filter (fun g : Fin I.m => g.val ∈ e.2.1) = S)).map
        fun e => ((e.2.2 : ℚ) : ℝ)).sum

end NSWBetter


