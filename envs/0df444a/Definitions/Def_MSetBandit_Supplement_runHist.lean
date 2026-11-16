-- Prove2me | Definitions.Def_MSetBandit_Supplement_runHist
-- name    : MSetBandit_Supplement_runHist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T23:47:26.365855+00:00
-- url     : https://prove2.me/theorems/ca2d9b65-3d99-4e59-9463-1e26d3aa87ed
-- title:
--   History of the interaction of an algorithm with an adversary
-- statement:
--   Fix a randomized algorithm $(h_t)$, a deterministic adversary $(f_t)$ and a realization $\omega$ of the private randomness. The **interaction** is defined recursively by $H_0=\emptyset$ and, for each round $t$,
--   $$
--   X_t=h_t(H_{t-1},\omega),\qquad \ell_t=f_t(H_{t-1}),\qquad Y_t=X_t^\top\ell_t,\qquad H_t=(H_{t-1},X_t,Y_t).
--   $$
--   This definition returns the history $H_t$ for every $t$.
--
--   It is the protocol of Section 2 specialized to a deterministic adversary: the adversary chooses $\ell_t$ before seeing $X_t$, and the learner observes only $Y_t$.
--
--   **Formalization Note** Rounds are indexed from $0$: the history after $0$ rounds is empty and the history after $t+1$ rounds appends round $t$'s action and feedback.
-- source:
--   Bacchiocchi–Cesari–Colomboni, An Efficient Minimax-Optimal Algorithm for Adversarial m-Set Bandits, arXiv:2608.12231, Section 2, p.4; Appendix E, pp.40–41

import Mathlib
import Definitions.Def_MSetBandit_ind
import Definitions.Def_MSetBandit_Supplement_RandAlg
import Definitions.Def_MSetBandit_Supplement_DetAdversary
open Matrix

namespace MSetBandit.Supplement

/-- **The history of the interaction.** Bacchiocchi–Cesari–Colomboni, *An Efficient Minimax-Optimal Algorithm for Adversarial m-Set Bandits*, arXiv:2608.12231, Section 2, p.4, and Appendix E, pp.40–41: for a
realization `ω` of the algorithm's private randomness, `X_t = h_t(H_{t−1}, ω)`,
`ℓ_t = f_t(H_{t−1})`, `Y_t = X_t^⊤ℓ_t`, and `H_t = (H_{t−1}, X_t, Y_t)`, with `H_0 = ∅`.

`runHist alg adv ω t` is the history `H_t` of the first `t` rounds when algorithm `alg` plays
against adversary `adv` and the private randomness is `ω`.

**Formalization Note.** Rounds are 0-based: `runHist … 0` is the empty history and
`runHist … (t+1)` appends round `t`'s action and feedback. -/
def runHist {d m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (alg : RandAlg d m Ω)
    (adv : DetAdversary d m) (ω : Ω) : (t : ℕ) → History d m t
  | 0 => Fin.elim0
  | t + 1 =>
    let H := runHist alg adv ω t
    let x := alg.h t H ω
    Fin.snoc (α := fun _ => Action d m × ℝ) H (x, ind x ⬝ᵥ adv.f t H)

end MSetBandit.Supplement


