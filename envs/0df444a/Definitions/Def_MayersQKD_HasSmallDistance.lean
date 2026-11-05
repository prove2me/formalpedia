-- Prove2me | Definitions.Def_MayersQKD_HasSmallDistance
-- name    : MayersQKD_HasSmallDistance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:45:50.059013+00:00
-- url     : https://prove2.me/theorems/304581e7-484a-4e4e-9a40-fdc03559a4dc
-- title:
--   The $\epsilon n$-small distance property of $M_v$
-- statement:
--   Let $v$ be a view with transcript $t$ and final outcome $y$, and let $E=E_c$. The operation $M_v$ has the $\epsilon n$-small distance property if, for every $(b,w',\theta')$,
--
--   $$
--   M_v\,P_0\,|b,w',\theta'\rangle_{\mathcal C}|\psi_{w',\theta'}\rangle=0,\qquad P_0=P_0[E,\epsilon n].
--   $$
--
--   It is the hypothesis of Lemma 1. In words, what Bob finally observes has no component in the states that are far from $\hat w$ on $E$.
--
--   **Formalization Note** $M_v=2^{-(n+1)}P_{\mathcal C}|v\rangle\langle\phi_v|$. The classical projection $P_{\mathcal C}$ annihilates $|b,w',\theta'\rangle_{\mathcal C}$ exactly when those values do not give the transcript $t$, so the condition is required on the values giving $t$, and on them $M_v$ is a scalar times $K_y(t)M_{\hat w}$. The case of a rank-one $|v\rangle\langle\phi_v|$ is the case where that operator has rank one.
-- source:
--   Mayers, Quantum Key Distribution and String Oblivious Transfer in Noisy Channels, arXiv:quant-ph/9606003v1, §7, pp.9–10; §6, p.9

import Mathlib
import Definitions.Def_MayersBC_bb84State
import Definitions.Def_MayersQKD_Bits
import Definitions.Def_MayersQKD_Attack
import Definitions.Def_MayersQKD_transcript
import Definitions.Def_MayersQKD_Lsub

namespace MayersQKD

open MayersBC

variable {n r m : ℕ}

/-- Mayers, arXiv:quant-ph/9606003v1, §7, pp.9–10: the operation `M_v` of a view `v = (t, y)` has
the `εn`-small distance property: for every `(b, w′, θ′)`,
`M_v P₀ |b, w′, θ′⟩_C |ψ_{w′,θ′}⟩ = 0`, with `P₀ = P₀[E, εn]` and `E = E_c`.

**Formalization Note.** `M_v = 2^(−(n+1)) P_C |v⟩⟨φ_v|` (p.9). `P_C` kills `|b, w′, θ′⟩_C` exactly
when that value does not give the transcript `t`, so only such values remain; on them `M_v` acts
as the scalar times `K_y(t) M_ŵ`. A rank-one `|v⟩⟨φ_v|` is the case where `K_y(t) M_ŵ` has rank
one. -/
def HasSmallDistance (A : Attack n r m) (δ ε : ℝ) (s : A.Seed) (what : Bits n)
    (R : Finset (Fin n)) (f : HashMatrix r m (blockLen n)) (c : Bool) (E : Finset (Fin n))
    (t : Transcript A.Seed n r m) (y : A.Y) : Prop :=
  ∀ (b : Bits m) (w' : Bits n) (θ' : Bases n), transcript A δ b w' θ' R f c s what = t →
    A.K t y (A.M s what (proj false (A.commit s) what E (ε * n) (bb84State θ' w'))) = 0

end MayersQKD


