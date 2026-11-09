-- Prove2me | Definitions.Def_RandomQueryXOR_TwoBitProtocol
-- name    : RandomQueryXOR_TwoBitProtocol
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:57:49.607767+00:00
-- url     : https://prove2.me/theorems/25c383e5-c822-48ef-9dcd-bbaec4065c03
-- title:
--   Protocols for the two-bit parity game, their transcript and success probability
-- statement:
--   In the **two-bit parity game** with $k$ players $Q_1,\dots,Q_k$:
--
--   1. two bits $\alpha,\beta$ are drawn independently and uniformly;
--   2. for every player $a$, independently, $\rho_a$ is uniform on $\{\text{'}\alpha\text{'},\text{'}\beta\text{'}\}$ and $\theta_a$ is uniform on $\{0,1\}$;
--   3. player $Q_a$ receives $\rho_a$ and $\theta_a$, and if $\theta_a=1$ also $\alpha$ when $\rho_a=\text{'}\alpha\text{'}$ and $\beta$ when $\rho_a=\text{'}\beta\text{'}$;
--   4. the players write one message each on a blackboard in the order $Q_1,\dots,Q_k$, each after seeing its input, the public randomness $R_{\rm pub}$, its own private randomness and all preceding messages;
--   5. the answer must be $\alpha\oplus\beta$.
--
--   A **protocol** fixes the laws of the public randomness and of each player's private randomness (independent of everything else), the message functions and the answer. Its **transcript** is $\Pi=(\Pi_1,\dots,\Pi_k)$, $\Pi_{<i}$ is the prefix before $Q_i$, and its **success probability** is $\Pr[\text{answer}=\alpha\oplus\beta]$. The event $\mathcal E_{\rm eq}=\{\alpha=\beta\}$ is used throughout: on it the answer is fixed, so information the transcript carries about $\theta=(\theta_1,\dots,\theta_k)$ given $\mathcal E_{\rm eq}$ is information about who received a bit.
--
--   **Formalization Note** Messages, public and private randomness range over finite sets $M,R,Q$ (the paper's information theory is on finite sets); a common private alphabet with per-player laws covers player-specific alphabets by embedding. $\rho_a=$ `false` is 'α'. Players are 0-based. The answer is a function of $R_{\rm pub}$ and the whole board, which contains "the last player writes $\alpha\oplus\beta$" (decode the last message).
-- source:
--   Garg, Sundaresan, Velusamy, XOR-Functions and Beyond in the Random Query Model, arXiv:2611.04353, Definition 4.5 and the notation after it, p.18 (PDF p.20)

import Mathlib
import Definitions.Def_WildeQIT_FinDist
import Definitions.Def_ShallowShadows_ShadowNorm_uniformDist
import Definitions.Def_RandomQueryXOR_uniformOn
import Definitions.Def_RandomQueryXOR_cmi

set_option autoImplicit false
set_option synthInstance.maxSize 2048

namespace RandomQueryXOR

open WildeQIT
open ShallowShadows.ShadowNorm (uniformDist)

/-- The input `(ρ_a, θ_a, v_a)` of a player of the two-bit parity game: the side `ρ_a`
(`false` = 'α', `true` = 'β'), the bit `θ_a`, and the value `v_a` received (`some α` or
`some β` when `θ_a = 1`, `none` when `θ_a = 0`). -/
abbrev PlayerInput := Bool × Bool × Option Bool

/-- A protocol for the two-bit parity game with `k` players (Garg, Sundaresan, Velusamy,
*XOR-Functions and Beyond in the Random Query Model*, arXiv:2611.04353, Definition 4.5,
p.18 = PDF p.20): "There are k players Q_1, …, Q_k. … 4. The players communicate in the
blackboard model in the order Q_1, Q_2, …, Q_k. Each player writes one message on the blackboard
after observing its input and all preceding messages. 5. The last player Q_k must write α ⊕ β on
the blackboard." Player `Q_a` (0-based `a : Fin k`) writes `msg a r q inp prev`, a function of
the public randomness `r ∼ pub`, its own private randomness `q ∼ priv a`, its input `inp` and
the preceding messages `prev`; the protocol's answer is `out r Π`.

**Formalization Note** Messages, public and private randomness range over finite sets `M`, `R`,
`Q` (the paper's information theory is on finite sets, Appendix A); a common private alphabet `Q`
with per-player laws covers player-specific alphabets by embedding. Reading the answer as
`out r Π` from the public randomness and the whole board is more general than "the last player
writes α ⊕ β": a printed protocol is one whose `out` decodes the last message, and `Q_k` sees
`r` and the whole board. -/
structure TwoBitProtocol (k : ℕ) (M R Q : Type) [Fintype R] [Fintype Q] where
  /-- the law of the public randomness `R_pub` -/
  pub : FinDist R
  /-- the law of the private randomness of each player (independent across players) -/
  priv : Fin k → FinDist Q
  /-- the message of player `a` given public coins, own private coins, own input, prefix -/
  msg : (a : Fin k) → R → Q → PlayerInput → (Fin a.val → M) → M
  /-- the answer read off the public randomness and the blackboard -/
  out : R → (Fin k → M) → Bool

/-- The probability space of the two-bit parity game: `(α, β, ρ, θ, R_pub, private coins)`. -/
abbrev GameSpace (k : ℕ) (R Q : Type) :=
  Bool × Bool × (Fin k → Bool) × (Fin k → Bool) × R × (Fin k → Q)

namespace GameSpace

variable {k : ℕ} {R Q : Type}

/-- The input bit `α`. -/
def alpha (ω : GameSpace k R Q) : Bool := ω.1
/-- The input bit `β`. -/
def beta (ω : GameSpace k R Q) : Bool := ω.2.1
/-- The sides `ρ = (ρ_1, …, ρ_k)` (`false` = 'α', `true` = 'β'). -/
def rho (ω : GameSpace k R Q) : Fin k → Bool := ω.2.2.1
/-- The bits `θ = (θ_1, …, θ_k)`. -/
def theta (ω : GameSpace k R Q) : Fin k → Bool := ω.2.2.2.1
/-- The public randomness `R_pub`. -/
def pubR (ω : GameSpace k R Q) : R := ω.2.2.2.2.1
/-- The private randomness of the players. -/
def privQ (ω : GameSpace k R Q) : Fin k → Q := ω.2.2.2.2.2

/-- The input of player `Q_a` (Definition 4.5, step 3): `ρ_a`, `θ_a` and, if `θ_a = 1`, the bit
`α` when `ρ_a = 'α'` and `β` when `ρ_a = 'β'`. -/
def input (ω : GameSpace k R Q) (a : Fin k) : PlayerInput :=
  (rho ω a, theta ω a, if theta ω a then some (if rho ω a then beta ω else alpha ω) else none)

/-- The event `E_eq := {α = β}`. -/
def Eeq (ω : GameSpace k R Q) : Prop := alpha ω = beta ω

instance (ω : GameSpace k R Q) : Decidable (Eeq ω) := by
  unfold Eeq; infer_instance

end GameSpace

namespace TwoBitProtocol

variable {k : ℕ} {M R Q : Type} [Fintype R] [Fintype Q]

open GameSpace

/-- The law of the game (Definition 4.5, steps 1–2): `α, β` independent uniform bits; for
every player independently `ρ_a` uniform on {'α', 'β'} and `θ_a` uniform on `{0, 1}`; the public
randomness `R_pub ∼ pub` and the private coins `q_a ∼ priv a`, all independent. -/
noncomputable def gameLaw (π : TwoBitProtocol k M R Q) : FinDist (GameSpace k R Q) :=
  (uniformDist Bool).prod ((uniformDist Bool).prod ((uniformDist (Fin k → Bool)).prod
    ((uniformDist (Fin k → Bool)).prod (π.pub.prod (piDist π.priv)))))

/-- The transcript `Π = (Π_1, …, Π_k)`: player `a` writes its message after seeing all
preceding messages. -/
def transcript (π : TwoBitProtocol k M R Q) (ω : GameSpace k R Q) : Fin k → M
  | a => π.msg a (pubR ω) (privQ ω a) (input ω a) (fun c => π.transcript ω ⟨c.val, by omega⟩)
termination_by a => a.val
decreasing_by exact c.isLt

/-- The transcript prefix `Π_{<i}` (the messages of the players before `Q_i`). -/
def prefixT (π : TwoBitProtocol k M R Q) (ω : GameSpace k R Q) (i : Fin k) : Fin i.val → M :=
  fun c => π.transcript ω ⟨c.val, by omega⟩

/-- The probability of success `Pr[answer = α ⊕ β]` over the law of the game. -/
noncomputable def success (π : TwoBitProtocol k M R Q) : ℝ :=
  probOf π.gameLaw fun ω => π.out (pubR ω) (π.transcript ω) = xor (alpha ω) (beta ω)

end TwoBitProtocol

end RandomQueryXOR


