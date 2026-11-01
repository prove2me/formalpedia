-- Prove2me | Definitions.Def_WiretapFeedback_WiretapCode_law
-- name    : WiretapFeedback_WiretapCode_law
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T16:00:44.0894+00:00
-- url     : https://prove2.me/theorems/182d6f22-2f86-4698-aa92-7cee2e1c3ebf
-- title:
--   Induced law $P_{M\hat M Z^n\mathbf F}$ of a wiretap code
-- statement:
--   For a wiretap code, a message law $\mu$ on $\{1,\dots,N\}$ and a channel $W:\mathcal X\to\mathcal Y\times\mathcal Z$, this is the joint law
--   $$
--   P_{M\hat MZ^n\mathbf F}
--   $$
--   of the message $M\sim\mu$, its decoded value $\hat M=d(Y^n)$, the eavesdropper's observations $Z^n=(Z_1,\dots,Z_n)$ and the public feedback $\mathbf F=(F_0,\dots,F_{n-1})$ when the code is run over $W$.
--
--   With $W$ replaced by another channel $V$, the same construction gives the law $Q_{M\hat MZ^n\mathbf F}$ of Lemma 7 and of the proof of Theorem 6.
-- source:
--   Hayashi–Tyagi–Watanabe, Strong Converse for a Degraded Wiretap Channel via Active Hypothesis Testing, arXiv:1410.0443v1, §II, p.2; Lemma 7 and proof of Theorem 6, pp.3–4

import Mathlib
import Definitions.Def_WiretapFeedback_WiretapCode_toStrategy
import Definitions.Def_WiretapFeedback_FeedbackStrategy_runLaw

namespace WiretapFeedback

/-- The induced joint law `P_{M M̂ Zⁿ 𝐅}` of the message `M`, its decoded value `M̂ = d(Yⁿ)`, the
eavesdropper's observations `Zⁿ = (Z_0, …, Z_{n−1})` and the feedback `𝐅 = (F_0, …, F_{n−1})`,
when the wiretap code `c` is used with message law `M ∼ μ` over the channel `W : X → Y × Z`
(Hayashi–Tyagi–Watanabe, arXiv:1410.0443v1, §II, p. 2; with `W` replaced by `V` it is the law
`Q_{M M̂ Zⁿ 𝐅}` of Lemma 7 and of the proof of Theorem 6, pp. 3–4).

The value at `(m, m̂, z, f)` is the probability that `M = m`, `M̂ = m̂`, `Zⁿ = z` and `𝐅 = f`. -/
noncomputable def WiretapCode.law {X Y Z : Type} [Fintype Y] [Fintype Z] {N n : ℕ}
    (c : WiretapCode X Y N n) (μ : PMF (Fin N)) (W : WildeQIT.Channel X (Y × Z)) :
    PMF (Fin N × Fin N × (Fin n → Z) × (Fin n → c.Fb)) :=
  ((c.toStrategy Z μ).runLaw W).map fun r =>
    ((r.1 : Fin N × c.Ux).1,
     c.decoder (fun s => (r.2.2 s).1),
     (fun s => (r.2.2 s).2),
     fun s => c.feedback s (fun i => (r.2.2 ⟨i, lt_trans i.isLt s.isLt⟩).1) (r.2.1 : c.Uy))

end WiretapFeedback


