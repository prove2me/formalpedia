-- Prove2me | Definitions.Def_CompNonlocal_TwoMsg_IsLocalPostprocessing
-- name    : CompNonlocal_TwoMsg_IsLocalPostprocessing
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:44:42.468683+00:00
-- url     : https://prove2.me/theorems/92df7bbc-28eb-453b-8d64-cf8e3887bf75
-- title:
--   Local postprocessing of a protocol's outputs
-- statement:
--   A protocol $\Pi$ is obtained from $P$ by **local postprocessing** if at every $\kappa$ there are finite-support probability kernels $K_R$, $K_S$ such that the honest law of $(\mathrm{msg}_S,\mathrm{msg}_R,\mathrm{out}_R,\mathrm{out}_S)$ under $\Pi$ is the law under $P$ with the receiver's output passed through $K_R$ and the sender's through $K_S$, independently: same messages, each new output computed from that party's own old output and fresh coins.
-- source:
--   Głuch, Morimae, From Computational Nonlocality to Public-Key Encryption and Commitments, manuscript (STOC 2027 submission, sha256 e245edd7…), Lemma 19, pp.45–46

import Mathlib
import Definitions.Def_CompNonlocal_TwoMsg

set_option autoImplicit false

namespace CompNonlocal

open QAlgorithms.Complexity

/-- `Π` is obtained from `P` by local postprocessing of the parties' outputs. Głuch, Morimae, *From
Computational Nonlocality to Public-Key Encryption and Commitments*, manuscript (STOC 2027
submission, sha256 e245edd7…), Lemma 19, p.45: "A protocol satisfying the hypothesis of Lemma 18 can
be modified by local postprocessing to obtain a protocol Π …"; the construction (p.46) keeps the
messages and has each party transform its own output with private coins.

**Formalization Note** The modified protocol `Π` is the argument `Q`. At every `κ` there are finite-support probability kernels `K_R` (from `P`'s
receiver output to `Π`'s) and `K_S` (from `P`'s sender output to `Π`'s) such that the honest law of
`(msg_S, msg_R, out_R, out_S)` under `Π` is the law under `P` with `out_R` passed through `K_R` and
`out_S` through `K_S`, independently: the transcript is unchanged and each new output depends only on
its own party's old output and fresh coins. Efficiency of `Π` is required separately. -/
def TwoMsg.IsLocalPostprocessing (P Q : TwoMsg) : Prop :=
  ∀ κ, ∃ KR KS : Str → List (Str × ℝ),
    (∀ s, ∀ w ∈ KR s, 0 ≤ w.2) ∧ (∀ s, ((KR s).map Prod.snd).sum = 1) ∧
    (∀ s, ∀ w ∈ KS s, 0 ≤ w.2) ∧ (∀ s, ((KS s).map Prod.snd).sum = 1) ∧
    ∀ f : Str → Str → Str → Str → ℝ,
      Q.expect κ f = P.expect κ (fun mS mR oR oS =>
        ((KR oR).map fun u => ((KS oS).map fun w => u.2 * w.2 * f mS mR u.1 w.1).sum).sum)

end CompNonlocal


