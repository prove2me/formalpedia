-- Prove2me | Definitions.Def_CompNonlocal_TwoMsg_PrivatePredictionAdvantage
-- name    : CompNonlocal_TwoMsg_PrivatePredictionAdvantage
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:44:45.636681+00:00
-- url     : https://prove2.me/theorems/c481d9ee-fd23-47ec-ae9e-2e46485c7f03
-- title:
--   Private prediction advantage (hypothesis of Lemma 18)
-- statement:
--   A sender-first two-message protocol with receiver bit $B_R\in\{-1,1\}$ and sender value $\hat B_S\in[-1,1]$ has a **private prediction advantage** if for some polynomial $q$ and every polynomial-size public predictor $\mathcal A$ reading the transcript $Z$, eventually
--   $$\mathbb E[(B_R-\mathcal A(Z))^2]\ge\mathbb E[(B_R-\hat B_S)^2]+\frac1{q(\kappa)} .$$
-- source:
--   Głuch, Morimae, From Computational Nonlocality to Public-Key Encryption and Commitments, manuscript (STOC 2027 submission, sha256 e245edd7…), Lemma 18, p.45

import Mathlib
import Definitions.Def_CompNonlocal_TwoMsg
import Definitions.Def_CompNonlocal_PolySize
import Definitions.Def_CompNonlocal_decDyadic
import Definitions.Def_CompNonlocal_clipUnit

set_option autoImplicit false

namespace CompNonlocal

open QAlgorithms.Complexity

/-- A private prediction advantage of the sender over every efficient public predictor, the
hypothesis of Lemma 18 of Głuch, Morimae, *From Computational Nonlocality to Public-Key Encryption
and Commitments*, manuscript (STOC 2027 submission, sha256 e245edd7…), p.45: "Suppose a sender-first
two-message QCCC protocol produces a transcript Z, a receiver bit B_R ∈ {−1, 1}, and a sender value
B̂_S ∈ [−1, 1]. If, for some polynomial q and every efficient public predictor A(Z) ∈ [−1, 1],
eventually E[(B_R − A(Z))²] ≥ E[(B_R − B̂_S)²] + 1/q(κ) …".

**Formalization Note** `Z = msg_S ++ msg_R`; `B_R = 1` if the receiver's private output starts with
`1` and `−1` otherwise; `B̂_S` is the sender's output read as a real (`decDyadic`) and clipped to
`[−1, 1]`; an efficient public predictor is a polynomial-size family reading `Z`, its output read the
same way. "1/q(κ)" is `1/(q(κ) + 1)` for `q : Polynomial ℕ`. -/
def TwoMsg.PrivatePredictionAdvantage (P : TwoMsg) : Prop :=
  ∃ q : Polynomial ℕ, ∀ A : Family, PolySize A → ∀ᶠ κ in Filter.atTop,
    P.expect κ (fun _ _ oR oS =>
        ((if oR.headD false then 1 else -1) - clipUnit (decDyadic oS).1) ^ 2) +
      1 / ((q.eval κ : ℕ) + 1 : ℝ) ≤
    P.expect κ (fun mS mR oR _ =>
      ∑ e : Bits (A κ).outC.length,
        ((A κ).effectOn 0 (mS ++ mR) (fun t => decide (t = List.ofFn e))).trace.re *
          ((if oR.headD false then 1 else -1) - clipUnit (decDyadic (List.ofFn e)).1) ^ 2)

end CompNonlocal


