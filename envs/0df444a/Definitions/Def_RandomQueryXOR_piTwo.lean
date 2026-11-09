-- Prove2me | Definitions.Def_RandomQueryXOR_piTwo
-- name    : RandomQueryXOR_piTwo
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T06:03:07.085267+00:00
-- url     : https://prove2.me/theorems/62910077-1cf9-4f9c-8943-4e6ae0d15cea
-- title:
--   Protocol $\pi_{\rm two}$: solving the two-bit parity game with a branching program for $g_{f\oplus}$
-- statement:
--   Let $P$ be a randomized branching program of width $2^S$ and length $T$ in the gate-keeper model for inputs in $\{0,1\}^{2n}$. Protocol $\pi_{\rm two}$ for the two-bit parity game with $k$ players:
--
--   1. samples $L$ by $\pi_L$ and the input $y$ by $\pi_y$: $y'\sim\mathcal D_{f\oplus}$ publicly, $y(j)=y'(j)$ off the pair of $h$, $y(2h-1)=\alpha$, $y(2h)=\beta$; if $h$ occurs more than $k$ times among $(m_t)$, it declares FAIL and outputs $0$;
--   2. draws a deterministic program $R_{\rm pub}$ from $P$ with public randomness;
--   3. simulates $R_{\rm pub}$ on $y$ and $L$: the label $\hat P_0$ before the first occurrence of $h$ is public; the gate bit at the $a$-th occurrence of $h$ is $\theta_a$, the other gate bits of the $a$-th simulation block (up to the time before the next occurrence) are private bits of $Q_a$; each active player $Q_a$ (one whose occurrence exists) writes the $S$-bit label $\hat P_a$ at the end of its block, inactive players write $\bot$;
--   4. answers $P(y)\oplus f(x^\star)$, reading $P(y)$ off the last non-null state $P_T$.
--
--   Every player has what it needs: indices and input bits off the pair of $h$ are public, and at its occurrence $Q_a$ holds the index side $\rho_a$ and, if $\theta_a=1$, the bit read there.
--
--   **Formalization Note** Messages are `Option (Fin (2 ^ S))`; on FAIL all players write $\bot$ (FAIL is a function of the public $(h,(m_t))$). Step (iii)(a), "sample $\hat P_0$ using public randomness conditioned on $y$ and $L$", is implemented by drawing the gate bits before the first occurrence publicly and computing $\hat P_0$ from them: the joint law is the same, and given $\hat P_0$ the transcript and $\theta$ are independent of those bits. The public randomness $R^{\rm two}_{\rm pub}$ is $(h,(m_t),(c_t),u,R_{\rm pub},(b_t))$ with $y'$ built from $u$; each player's private randomness is $T$ fair bits, of which it uses those of its block. $x^\star$ is any input with a sensitive zero.
-- source:
--   Garg, Sundaresan, Velusamy, XOR-Functions and Beyond in the Random Query Model, arXiv:2611.04353, §4.2, protocols π_y (p.20, PDF p.22) and π_two (p.21, PDF p.23); R^two_pub p.22 (PDF p.24)

import Mathlib
import Definitions.Def_WildeQIT_FinDist
import Definitions.Def_ShallowShadows_ShadowNorm_uniformDist
import Definitions.Def_RandomQueryXOR_uniformOn
import Definitions.Def_RandomQueryXOR_sens
import Definitions.Def_RandomQueryXOR_xorLift
import Definitions.Def_RandomQueryXOR_DetBP
import Definitions.Def_RandomQueryXOR_gateSuccessProb
import Definitions.Def_RandomQueryXOR_hardDist
import Definitions.Def_RandomQueryXOR_TwoBitProtocol
import Definitions.Def_RandomQueryXOR_piL

set_option autoImplicit false
set_option synthInstance.maxSize 2048

namespace RandomQueryXOR

open WildeQIT
open ShallowShadows.ShadowNorm (uniformDist)

/-- The public randomness `R^two_pub` of the embedding protocols: the special index `h`, the
sequence `(m_t)`, the public coins `(c_t)` of π_L, the bits `u` of `y′ ∼ D_{f⊕}`, the
deterministic program `R_pub` drawn from `P`, and the gate bits `(b_t)` used before the first
occurrence of `h`. -/
abbrev TwoPub (n S T : ℕ) :=
  Fin n × (Fin T → Fin n) × (Fin T → Bool) × (Fin n → Bool) ×
    DetBP (2 ^ S) (GateSample (Fin (2 * n))) T × (Fin T → Bool)

namespace TwoPub

variable {n S T : ℕ}

instance instDecidableEq : DecidableEq (TwoPub n S T) :=
  inferInstanceAs (DecidableEq (Fin n × (Fin T → Fin n) × (Fin T → Bool) × (Fin n → Bool) ×
    DetBP (2 ^ S) (GateSample (Fin (2 * n))) T × (Fin T → Bool)))

instance instFintype : Fintype (TwoPub n S T) :=
  inferInstanceAs (Fintype (Fin n × (Fin T → Fin n) × (Fin T → Bool) × (Fin n → Bool) ×
    DetBP (2 ^ S) (GateSample (Fin (2 * n))) T × (Fin T → Bool)))

/-- The special index `h`. -/
def h (r : TwoPub n S T) : Fin n := r.1
/-- The sequence `M = (m_t)_{t ∈ [T]}`. -/
def m (r : TwoPub n S T) : Fin T → Fin n := r.2.1
/-- The public coins of π_L. -/
def c (r : TwoPub n S T) : Fin T → Bool := r.2.2.1
/-- The bits of `y′ ∼ D_{f⊕}` (`y′ = hardY f xs u`). -/
def u (r : TwoPub n S T) : Fin n → Bool := r.2.2.2.1
/-- The deterministic branching program `R_pub` sampled from `P`. -/
def prog (r : TwoPub n S T) : DetBP (2 ^ S) (GateSample (Fin (2 * n))) T := r.2.2.2.2.1
/-- The public gate bits. -/
def bpub (r : TwoPub n S T) : Fin T → Bool := r.2.2.2.2.2

/-- `t̂_{j+1} − 1` (0-based time of occurrence number `j` of `h`, counted from `0`), and `T`
(the paper's `t̂ = T + 1`) if `h` occurs at most `j` times: the number of times `s` such that
`h` occurs at most `j` times among `m_0, …, m_s`. -/
def occTime (r : TwoPub n S T) (j : ℕ) : ℕ :=
  (Finset.univ.filter fun s : Fin T =>
    (Finset.univ.filter fun s' : Fin T => s' ≤ s ∧ r.m s' = r.h).card ≤ j).card

/-- `h` occurs more than `k` times: protocol π_two declares FAIL. -/
def Fail (k : ℕ) (r : TwoPub n S T) : Prop := k < occCount r.h r.m

instance (k : ℕ) (r : TwoPub n S T) : Decidable (Fail k r) := by unfold Fail; infer_instance

end TwoPub

open TwoPub

variable {n S T : ℕ}

/-- The public samples `(ℓ_t, b_t, w(ℓ_t))` at times `t` with `m_t ≠ h`, using the public gate
bits: `ℓ_t` from the public coin and `w` read off `y′ = hardY f xs u` (which agrees with `y`
outside the pair of `h`). -/
def pubSample (f : (Fin n → Bool) → Bool) (xs : Fin n → Bool) (r : TwoPub n S T) :
    Fin T → GateSample (Fin (2 * n)) := fun s =>
  (pairIdx (r.m s) (r.c s), r.bpub s,
    if r.bpub s then some (hardY f xs r.u (pairIdx (r.m s) (r.c s))) else none)

/-- `P̂_0`, the state immediately before the first occurrence of `h` (`P_T` if `h` does not
occur), computed from the public randomness. -/
def hat0 (f : (Fin n → Bool) → Bool) (xs : Fin n → Bool) (r : TwoPub n S T) : Fin (2 ^ S) :=
  r.prog.runFrom (pubSample f xs r) 0 r.prog.start (r.occTime 0)

/-- The samples as seen by an active player with private bits `q` and input `inp = (ρ_a, θ_a,
v_a)`: at its occurrence of `h` the sample is `(ℓ, θ_a, v_a)` with `ℓ = 2h − 1` if
`ρ_a = 'α'` and `ℓ = 2h` if `ρ_a = 'β'`; at other times of its block the index is public, the
gate bit is its private bit, and `w` is read off `y′` (Observation 4.8, 4.10). -/
def localSample (f : (Fin n → Bool) → Bool) (xs : Fin n → Bool) (r : TwoPub n S T)
    (q : Fin T → Bool) (inp : PlayerInput) : Fin T → GateSample (Fin (2 * n)) := fun s =>
  if r.m s = r.h then (pairIdx r.h inp.1, inp.2.1, inp.2.2)
  else (pairIdx (r.m s) (r.c s), q s,
    if q s then some (hardY f xs r.u (pairIdx (r.m s) (r.c s))) else none)

/-- The state `P̂_a` at the end of the simulation block of player `Q_a` (0-based `a`): starting
from the previous player's message (`P̂_0` for the first player), run `R_pub` on the player's
samples from its occurrence of `h` up to the time before the next occurrence (or to `T`). -/
def blockEnd {k : ℕ} (f : (Fin n → Bool) → Bool) (xs : Fin n → Bool) (a : Fin k)
    (r : TwoPub n S T) (q : Fin T → Bool) (inp : PlayerInput)
    (prev : Fin a.val → Option (Fin (2 ^ S))) : Fin (2 ^ S) :=
  r.prog.runFrom (localSample f xs r q inp) (r.occTime a.val)
    (if ha : 0 < a.val then (prev ⟨a.val - 1, by omega⟩).getD (hat0 f xs r) else hat0 f xs r)
    (r.occTime (a.val + 1) - r.occTime a.val)

/-- The message of player `Q_a` in the embedding protocols: ⊥ (`none`) if `Q_a` is not active
(`h` occurs at most `a` times, 0-based) or, in π_two (`aux = false`), on FAIL; otherwise the
`S`-bit label `P̂_a` at the end of its block. -/
def embedMsg {k : ℕ} (f : (Fin n → Bool) → Bool) (xs : Fin n → Bool) (aux : Bool) (a : Fin k)
    (r : TwoPub n S T) (q : Fin T → Bool) (inp : PlayerInput)
    (prev : Fin a.val → Option (Fin (2 ^ S))) : Option (Fin (2 ^ S)) :=
  if (aux = false ∧ Fail k r) ∨ occCount r.h r.m ≤ a.val then none
  else some (blockEnd f xs a r q inp prev)

/-- The law of `R^two_pub`: `h` uniform on the sensitive zeros of `x⋆ = xs`, `(m_t)` uniform on
`[n]^T`, fair public coins, `u` uniform (so `y′ ∼ D_{f⊕}`), the program `R_pub ∼ μP`, and fair
public gate bits, all independent. -/
noncomputable def twoPubLaw (f : (Fin n → Bool) → Bool) (xs : Fin n → Bool)
    (hZ : (sensZeros f xs).Nonempty) (μP : FinDist (DetBP (2 ^ S) (GateSample (Fin (2 * n))) T)) :
    FinDist (TwoPub n S T) :=
  haveI : Nonempty (Fin n) := ⟨hZ.choose⟩
  (uniformOn (sensZeros f xs) hZ).prod ((uniformDist (Fin T → Fin n)).prod
    ((uniformDist (Fin T → Bool)).prod ((uniformDist (Fin n → Bool)).prod
      (μP.prod (uniformDist (Fin T → Bool))))))

/-- The state the answer is read from: the message of the last active player, or `P̂_0` if no
player is active (then `P̂_0 = P_T`). -/
def lastState {k : ℕ} (f : (Fin n → Bool) → Bool) (xs : Fin n → Bool) (r : TwoPub n S T)
    (board : Fin k → Option (Fin (2 ^ S))) : Fin (2 ^ S) :=
  if h0 : 0 < occCount r.h r.m ∧ occCount r.h r.m - 1 < k then
    (board ⟨occCount r.h r.m - 1, h0.2⟩).getD (hat0 f xs r)
  else hat0 f xs r

/-- Protocol π_two for the two-bit parity game built from a randomized gate-keeper branching
program `P` (law `μP`) for `g = f ∘ ⊕2` (Garg, Sundaresan, Velusamy, *XOR-Functions and Beyond
in the Random Query Model*, arXiv:2611.04353, p.21 = PDF p.23): "(i) Sample L using protocol
π_L and sample y using protocol π_y. If h occurs more than k times in (m_t)_{t∈[T]}, declare FAIL
and output 0. (ii) Use public randomness to sample a deterministic branching program from the
distribution associated with the randomized branching program P. (iii) The players simulate P
… (a) Sample the S-bit label P̂_0 using public randomness conditioned on y and L. (b) For every
active player Q_a with a ∈ [k], the value of b̂_a = b_{t̂_a} is set as θ_a. For every other time
step t in the simulation block of a, where t̂_a < t ≤ t̂_{a+1} − 1, b_t is sampled from {0, 1}
uniformly at random with private randomness of Q_a. (c) Active player Q_a then writes the S-bit
label corresponding P̂_a on the blackboard. (d) Players who are not active, with t̂_a = T + 1
write ⊥ on the board. (iv) The last player Q_k uses the last non-null state, which is P_T, to get
the output P(y), and fixes P(y) ⊕ f(x⋆_f) as the answer." Here π_y sets `y(j) = y′(j)` off the
pair of `h`, `y(2h − 1) = α`, `y(2h) = β` (p.20 = PDF p.22).

**Formalization Note** Messages are `Option (Fin (2 ^ S))` (`none` = ⊥); on FAIL every player
writes ⊥ and the answer is `0` (FAIL is a function of the public `(h, M)`). Step (iii)(a) is
implemented by drawing the gate bits before the first occurrence of `h` publicly and computing
`P̂_0` from them: this gives the same joint law, and given `P̂_0` the transcript and `θ` are
independent of those bits. The private coins of `Q_a` are `T` fair bits, of which it uses those
of its block. `x⋆ = xs` is any input with a sensitive zero. -/
noncomputable def piTwo (f : (Fin n → Bool) → Bool) (xs : Fin n → Bool) (k : ℕ)
    (hZ : (sensZeros f xs).Nonempty) (μP : FinDist (DetBP (2 ^ S) (GateSample (Fin (2 * n))) T)) :
    TwoBitProtocol k (Option (Fin (2 ^ S))) (TwoPub n S T) (Fin T → Bool) where
  pub := twoPubLaw f xs hZ μP
  priv := fun _ => uniformDist (Fin T → Bool)
  msg := embedMsg f xs false
  out r board :=
    if Fail k r then false else xor (r.prog.out (lastState f xs r board)) (f xs)

end RandomQueryXOR


