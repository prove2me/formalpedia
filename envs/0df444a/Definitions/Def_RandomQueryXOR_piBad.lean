-- Prove2me | Definitions.Def_RandomQueryXOR_piBad
-- name    : RandomQueryXOR_piBad
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T06:01:39.521193+00:00
-- url     : https://prove2.me/theorems/520fda28-dbdc-41ce-b43e-ff55bb242f15
-- title:
--   Truncated protocol $\pi_{\rm bad}$ and good prefixes
-- statement:
--   For a protocol $\pi$ of the two-bit parity game, a transcript prefix $\Pi_{<i}$ together with public randomness $R_{\rm pub}$ is a **good prefix** if
--   $$
--   \delta_{uv}:=\Pr\bigl[\alpha=u,\ \beta=v\ \big|\ \Pi_{<i},R_{\rm pub}\bigr]\ \ge\ 0.1\qquad\text{for all }u,v\in\{0,1\}.
--   $$
--   The protocol $\pi_{\rm bad}$ runs $\pi$ as long as the current prefix is good: player $Q_i$ sends its $\pi$-message if the prefix $\Pi_{<i}$ is good (and no earlier player stopped), and otherwise it and all later players send the null message $\bot$. Its transcript $\Pi_{\rm bad}$ is a function of $\Pi$ and $R_{\rm pub}$.
--
--   Claim 5.4 shows that $\pi_{\rm bad}$ still reveals $\Omega_\varepsilon(1)$ information about $(\alpha,\beta)$.
--
--   **Formalization Note** Messages of $\pi_{\rm bad}$ are `Option M` (`none` = $\bot$); same randomness as $\pi$; goodness is computed from $\pi$'s law. A prefix of probability $0$ counts as good (junk value of the conditioned law); it never occurs. The answer of $\pi_{\rm bad}$ is $\pi$'s on an untruncated board and $0$ otherwise (no statement uses it).
-- source:
--   Garg, Sundaresan, Velusamy, XOR-Functions and Beyond in the Random Query Model, arXiv:2611.04353, §5.2, p.38 (PDF p.40); δ_uv p.34 (PDF p.36)

import Mathlib
import Definitions.Def_RandomQueryXOR_TwoBitProtocol

set_option autoImplicit false
set_option synthInstance.maxSize 2048

namespace RandomQueryXOR

open WildeQIT GameSpace

namespace TwoBitProtocol

variable {k : ℕ} {M R Q : Type} [Fintype M] [DecidableEq M] [Fintype R] [DecidableEq R]
  [Fintype Q]

/-- A transcript prefix `Π_{<i} = p` with public randomness `R_pub = r` is *good* if
`δ_{uv} := Pr[α = u, β = v | Π_{<i} = p, R_pub = r] ≥ 0.1` for all `u, v ∈ {0, 1}`
(arXiv:2611.04353, p.34 = PDF p.36 for `δ_{uv}`, p.38 = PDF p.40 for good prefixes).

**Formalization Note** For a prefix of probability `0` the conditioned law is the junk value
(the unconditioned law, every `δ_{uv} = 1/4`), so such a prefix counts as good; it never
occurs. -/
def IsGoodPrefix (π : TwoBitProtocol k M R Q) (i : Fin k) (p : Fin i.val → M) (r : R) : Prop :=
  ∀ u v : Bool, (1 : ℝ) / 10 ≤
    probOf (condDist π.gameLaw fun ω => π.prefixT ω i = p ∧ pubR ω = r)
      (fun ω => alpha ω = u ∧ beta ω = v)

open Classical in
/-- The truncated protocol `π_bad` (Garg, Sundaresan, Velusamy, *XOR-Functions and Beyond in
the Random Query Model*, arXiv:2611.04353, p.38 = PDF p.40): "For any i ∈ [k], as long as the
current transcript prefix Π_{<i} is good, the players send the same messages as in π. If the
transcript prefix Π_{<i} is not good, all the remaining players starting from Q_i send ⊥ or the
null message containing no information."

**Formalization Note** Messages of `π_bad` are `Option M` (`none` = ⊥). Player `Q_i` sends
`some` of its `π`-message iff no earlier player sent ⊥ and the `π`-prefix it reads off the board
is good; same public and private randomness as `π`. Its answer is `π`'s answer on an untruncated
board and `0` otherwise (the paper's random bit is not needed: Claim 5.4 is about the transcript
only). Goodness is computed from `π`'s law, so `π_bad` is a protocol in the sense of
`TwoBitProtocol`. -/
noncomputable def piBad (π : TwoBitProtocol k M R Q) : TwoBitProtocol k (Option M) R Q where
  pub := π.pub
  priv := π.priv
  msg a r q inp prev :=
    if h : ∀ c, (prev c).isSome then
      if π.IsGoodPrefix a (fun c => (prev c).get (h c)) r then
        some (π.msg a r q inp fun c => (prev c).get (h c))
      else none
    else none
  out r board :=
    if h : ∀ c, (board c).isSome then π.out r fun c => (board c).get (h c) else false

end TwoBitProtocol

end RandomQueryXOR


