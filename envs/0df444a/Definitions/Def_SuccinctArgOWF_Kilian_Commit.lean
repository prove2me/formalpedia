-- Prove2me | Definitions.Def_SuccinctArgOWF_Kilian_Commit
-- name    : SuccinctArgOWF_Kilian_Commit
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T07:09:48.951198+00:00
-- url     : https://prove2.me/theorems/7db0bf3b-745b-42e8-bf18-a0af167cb6c2
-- title:
--   §3.3 and Definitions 3.4, 3.5, 5.1 — public-coin commitments, binding games, local verification
-- statement:
--   **Commitment schemes (§3.3).** An $\ell$-round public-coin commitment scheme $\mathrm{Com}=(S,R,\mathrm{Open},\mathrm{Ver})$ for $n$-bit messages consists of finite nonempty sets $R_1,\dots,R_\ell$, deterministic sender next-message functions $S_1,\dots,S_\ell$ and deterministic $\mathrm{Open},\mathrm{Ver}$. On $m\in\{0,1\}^n$ the sender starts from $\mathrm{state}_0=m$; in round $j$ the receiver sends $r_j\leftarrow R_j$ and the sender replies $y_j$, where $(y_j,\mathrm{state}_j)=S_j(\mathrm{state}_{j-1},r_j)$. With coins $\rho=(r_1,\dots,r_\ell)$ the sender transcript is $\tau=\mathrm{tr}(m,\rho)=(y_1,\dots,y_\ell)$. The opening sends $m$ and $\pi=\mathrm{Open}(\mathrm{state}_\ell)$, accepted if $\mathrm{Ver}(\rho,\tau,m,\pi)=1$. *Completeness*: the honest opening is accepted for every $m$ and all coins. The *canonical opening* has empty proofs and $\mathrm{Ver}(\rho,\tau,m,\pi)=1$ iff $\mathrm{tr}(m,\rho)=\tau$.
--
--   A scheme *with interval opening* for messages in $\{0,1\}^N$ opens an interval $I$ by $(m_I,\mathrm{Open}(\mathrm{state},I))$ and accepts if $\mathrm{Ver}(\rho,\tau,I,v,\pi)=1$; completeness is required for every interval.
--
--   **Binding games.** In the *binding game* (Definition 3.4) a stateful adversary plays the sender against the honest receiver and outputs $(m_0,\pi_0),(m_1,\pi_1)$ with $m_b\in\{0,1\}^n$; it wins if $m_0\neq m_1$ and both are accepted. $\mathrm{bind}_{\mathrm{Com}}(t)$ is the largest winning probability (over $\rho$ and the adversary's coins) of an adversary of running time at most $t$. In the *selective interval binding game* (Definition 3.5) the adversary first outputs $I\subseteq[N]$, then plays the commit phase, then outputs $(I,v_0,\pi_0),(I,v_1,\pi_1)$ with $v_b\in\{0,1\}^{|I|}$; it wins if both are accepted and $v_0\neq v_1$:
--
--   $$\mathrm{bind}^{\mathrm{int}}_{\mathrm{Com}}(t)=\sup\{\Pr[A\text{ wins}] : A\text{ of running time at most }t\}.$$
--
--   In the *adaptive* interval binding game the interval is output with the openings after the commit phase; restricting to $|I|=1$ gives the selective and adaptive *position binding* games.
--
--   **Local verification (Definition 5.1).** If the sender messages lie in $\{0,1\}^d$ and $J$ maps every interval $I\subseteq[N]$ to an interval $J(I)\subseteq[d]$, $\mathrm{Com}$ has local verification w.r.t. $J$ if $\mathrm{Ver}(\rho,\tau,I,v,\pi)$ depends on $\tau=(y_1,\dots,y_\ell)$ only through $\tau_{J(I)}=((y_1)_{J(I)},\dots,(y_\ell)_{J(I)})$.
--
--   These are the objects all binding statements of the mission are about.
--
--   **Formalization Note** Sender states have an arbitrary type initialised from the message. The adversary's phases are fixed per game (round phase and final phase; selective games add a first phase that outputs the interval); the adaptive final phase outputs $v_0,\pi_0,v_1,\pi_1$ before the interval. The supremum is the real supremum of a set of probabilities, which is bounded by $1$.
-- source:
--   Jesko Dujmovic, Daniel Wichs, STOC 2027 submission #650 (October 2026), §3.3, Definitions 3.4–3.5, pp. 8–9 (PDF pp. 10–11); Definition 5.1, p. 13 (PDF p. 15)

import Mathlib
import Definitions.Def_SuccinctArgOWF_Kilian_Machines

set_option autoImplicit false

namespace SuccinctArgOWF.Kilian

/-! # Public-coin commitment schemes and their binding games (§3.3, Definitions 3.4, 3.5, 5.1)

An `ℓ`-round public-coin commitment scheme: finite receiver message sets `R₁, …, R_ℓ`, deterministic
sender next-message functions `S_j`, a deterministic opening algorithm `Open` and verifier `Ver`.
The sender state is of an arbitrary type `σ`, initialised from the message (`state₀ = m`). -/

/-- The sender state after `j` rounds on message `m` and receiver coins `ρ`. -/
def senderState {σ : Type} {ℓ : ℕ} (init : Str → σ) (S : Fin ℓ → σ → Str → Str × σ) (m : Str)
    (ρ : Fin ℓ → Str) : ℕ → σ
  | 0 => init m
  | j + 1 =>
    if h : j < ℓ then (S ⟨j, h⟩ (senderState init S m ρ j) (ρ ⟨j, h⟩)).2
    else senderState init S m ρ j

/-- The honest sender transcript `tr(m, ρ) = (y₁, …, y_ℓ)`. -/
def transcript {σ : Type} {ℓ : ℕ} (init : Str → σ) (S : Fin ℓ → σ → Str → Str × σ) (m : Str)
    (ρ : Fin ℓ → Str) : Fin ℓ → Str :=
  fun j => (S j (senderState init S m ρ j.1) (ρ j)).1

/-! ## Plain commitments for `n`-bit messages -/

/-- An `ℓ`-round public-coin commitment scheme `Com = (S, R, Open, Ver)` for `n`-bit messages
(§3.3, p.8). `Ver ρ τ m π` is the receiver's decision on coins `ρ`, sender messages `τ`, message `m`
and proof `π`. -/
structure Commit where
  /-- message length -/
  n : ℕ
  /-- number of rounds -/
  ℓ : ℕ
  /-- the finite sets the receiver draws its messages from -/
  R : Fin ℓ → Finset Str
  R_ne : ∀ j, (R j).Nonempty
  /-- type of sender states -/
  σ : Type
  init : Str → σ
  /-- `S j state r = (y, state')` -/
  S : Fin ℓ → σ → Str → Str × σ
  Open : σ → Str
  Ver : (Fin ℓ → Str) → (Fin ℓ → Str) → Str → Str → Bool

/-- Receiver coins `ρ = (r₁, …, r_ℓ)`, `r_j ∈ R_j`, sampled uniformly. -/
abbrev Commit.Coins (C : Commit) := (j : Fin C.ℓ) → ↥(C.R j)

/-- The coins as strings. -/
def Commit.cs (C : Commit) (ρ : C.Coins) : Fin C.ℓ → Str := fun j => (ρ j).1

/-- `tr(m, ρ)`. -/
def Commit.tr (C : Commit) (m : Str) (ρ : Fin C.ℓ → Str) : Fin C.ℓ → Str :=
  transcript C.init C.S m ρ

/-- The final sender state. -/
def Commit.final (C : Commit) (m : Str) (ρ : Fin C.ℓ → Str) : C.σ :=
  senderState C.init C.S m ρ C.ℓ

/-- Completeness: for every `m ∈ {0,1}^n` and all coins the honest opening is accepted. -/
def Commit.Complete (C : Commit) : Prop :=
  ∀ m : Str, m.length = C.n → ∀ ρ : C.Coins,
    C.Ver (C.cs ρ) (C.tr m (C.cs ρ)) m (C.Open (C.final m (C.cs ρ))) = true

/-- The canonical opening: the proof is empty and `Ver(ρ, τ, m, π) = 1` iff `tr(m, ρ) = τ`. -/
def Commit.Canonical (C : Commit) : Prop :=
  (∀ st, C.Open st = []) ∧ ∀ ρ τ m π, C.Ver ρ τ m π = decide (C.tr m ρ = τ)

/-- Every sender message has exactly `d` bits (for every message `m ∈ {0,1}^n` and all coins). -/
def Commit.MsgLen (C : Commit) (d : ℕ) : Prop :=
  ∀ m : Str, m.length = C.n → ∀ ρ : C.Coins, ∀ j, (C.tr m (C.cs ρ) j).length = d

/-- The binding game's schedule: one invocation per round (phase `0`, incoming message `r_j`), then
the final invocation (phase `1`) that outputs the two openings `(m₀, π₀), (m₁, π₁)` as components
`1, 2, 3, 4`. -/
def Commit.bindSched (C : Commit) (ρ : C.Coins) : List (ℕ × Str) :=
  List.ofFn (fun j : Fin C.ℓ => ((0 : ℕ), (ρ j).1)) ++ [(1, [])]

/-- `A` wins the binding game (Definition 3.4) on random tape `ω` and receiver coins `ρ`. -/
noncomputable def Commit.bindWin (C : Commit) (A : Adv) (t : ℕ) (ω : Fin t → Bool) (ρ : C.Coins) :
    Prop :=
  let os := A.outs (List.ofFn ω) [] (C.bindSched ρ)
  let τ : Fin C.ℓ → Str := fun j => outC os j.1 1
  os.length = C.ℓ + 1 ∧ outC os C.ℓ 1 ≠ outC os C.ℓ 3 ∧
    (outC os C.ℓ 1).length = C.n ∧ (outC os C.ℓ 3).length = C.n ∧
    C.Ver (C.cs ρ) τ (outC os C.ℓ 1) (outC os C.ℓ 2) = true ∧
    C.Ver (C.cs ρ) τ (outC os C.ℓ 3) (outC os C.ℓ 4) = true

/-- The winning probability over the receiver coins and the coins of `A`. -/
noncomputable def Commit.bindProb (C : Commit) (A : Adv) (t : ℕ) : ℝ :=
  prob fun p : (Fin t → Bool) × C.Coins => C.bindWin A t p.1 p.2

/-- `bind_Com(t)`: the largest winning probability of an adversary of running time at most `t`. -/
noncomputable def Commit.bind (C : Commit) (t : ℕ) : ℝ :=
  sSup {x | ∃ A : Adv, A.RunsWithin t [] (Set.range C.bindSched) ∧ x = C.bindProb A t}

/-! ## Commitments with interval opening for messages in `{0,1}^N` -/

/-- An `ℓ`-round public-coin commitment scheme with interval opening for messages in `{0,1}^N`
(p.9): `Open state a b` opens the interval `I = {a, …, b}` and `Ver ρ τ a b v π` decides on the
claimed values `v ∈ {0,1}^{|I|}`. -/
structure ICommit where
  N : ℕ
  ℓ : ℕ
  R : Fin ℓ → Finset Str
  R_ne : ∀ j, (R j).Nonempty
  σ : Type
  init : Str → σ
  S : Fin ℓ → σ → Str → Str × σ
  Open : σ → ℕ → ℕ → Str
  Ver : (Fin ℓ → Str) → (Fin ℓ → Str) → ℕ → ℕ → Str → Str → Bool

abbrev ICommit.Coins (C : ICommit) := (j : Fin C.ℓ) → ↥(C.R j)

def ICommit.cs (C : ICommit) (ρ : C.Coins) : Fin C.ℓ → Str := fun j => (ρ j).1

def ICommit.tr (C : ICommit) (m : Str) (ρ : Fin C.ℓ → Str) : Fin C.ℓ → Str :=
  transcript C.init C.S m ρ

def ICommit.final (C : ICommit) (m : Str) (ρ : Fin C.ℓ → Str) : C.σ :=
  senderState C.init C.S m ρ C.ℓ

/-- Completeness: for every `m ∈ {0,1}^N`, all coins and every interval `I ⊆ [N]` the honest
opening `(m_I, Open(state, I))` is accepted. -/
def ICommit.Complete (C : ICommit) : Prop :=
  ∀ m : Str, m.length = C.N → ∀ ρ : C.Coins, ∀ a b, IsInterval C.N a b →
    C.Ver (C.cs ρ) (C.tr m (C.cs ρ)) a b (sub m a b) (C.Open (C.final m (C.cs ρ)) a b) = true

/-- Every sender message has exactly `d` bits ("the sender messages lie in `{0,1}^d`"). -/
def ICommit.MsgLen (C : ICommit) (d : ℕ) : Prop :=
  ∀ m : Str, m.length = C.N → ∀ ρ : C.Coins, ∀ j, (C.tr m (C.cs ρ) j).length = d

/-- The committer sends exactly `s` bits in total (`|τ| = s`) on every message and all coins. -/
def ICommit.SenderBits (C : ICommit) (s : ℕ) : Prop :=
  ∀ m : Str, m.length = C.N → ∀ ρ : C.Coins,
    (List.ofFn fun j => (C.tr m (C.cs ρ) j).length).sum = s

/-- Definition 5.1 (local verification): the sender messages lie in `{0,1}^d`, `J` maps every
interval `I ⊆ [N]` to an interval `J(I) ⊆ [d]`, and `Ver(ρ, τ, I, v, π)` depends on
`τ = (y₁, …, y_ℓ) ∈ ({0,1}^d)^ℓ` only through `τ_{J(I)} = ((y₁)_{J(I)}, …, (y_ℓ)_{J(I)})`. -/
def ICommit.LocalVer (C : ICommit) (d : ℕ) (J : ℕ → ℕ → ℕ × ℕ) : Prop :=
  C.MsgLen d ∧ (∀ a b, IsInterval C.N a b → IsInterval d (J a b).1 (J a b).2) ∧
    ∀ (ρ : C.Coins) (τ τ' : Fin C.ℓ → Str) (a b : ℕ) (v π : Str), IsInterval C.N a b →
      (∀ j, (τ j).length = d) → (∀ j, (τ' j).length = d) →
      (∀ j, sub (τ j) (J a b).1 (J a b).2 = sub (τ' j) (J a b).1 (J a b).2) →
      C.Ver (C.cs ρ) τ a b v π = C.Ver (C.cs ρ) τ' a b v π

/-- The string in `{0,1}^d` holding `u` at the positions `a, …, b` and zeros elsewhere; under local
verification `Ver(ρ, u, I, v, π)` is `Ver` on the messages `embed d a b u_j`. -/
def embed (d a b : ℕ) (u : Str) : Str :=
  List.replicate (a - 1) false ++ u ++ List.replicate (d - b) false

/-- Schedule of the selective interval binding game (Definition 3.5): phase `0` outputs the interval
`I = {a, …, b}` (components `1, 2`, in binary), then one invocation per round (phase `1`), then the
final invocation (phase `2`) outputs `v₀, π₀, v₁, π₁` (components `1, 2, 3, 4`). -/
def ICommit.selSched (C : ICommit) (ρ : C.Coins) : List (ℕ × Str) :=
  [((0 : ℕ), [])] ++ List.ofFn (fun j : Fin C.ℓ => ((1 : ℕ), (ρ j).1)) ++ [(2, [])]

/-- The interval output by the selective adversary (first invocation). -/
noncomputable def ICommit.selI (C : ICommit) (A : Adv) (t : ℕ) (ω : Fin t → Bool) (ρ : C.Coins) :
    ℕ × ℕ :=
  let os := A.outs (List.ofFn ω) [] (C.selSched ρ)
  (bitsVal (outC os 0 1), bitsVal (outC os 0 2))

/-- `A` wins the selective interval binding game (`pos = false`), or the selective position binding
game (`pos = true`: the interval must be a single position), on coins `ω, ρ`: both openings of the
interval chosen before the commit phase are accepted and contradict each other. -/
noncomputable def ICommit.selWin (C : ICommit) (pos : Bool) (A : Adv) (t : ℕ) (ω : Fin t → Bool)
    (ρ : C.Coins) : Prop :=
  let os := A.outs (List.ofFn ω) [] (C.selSched ρ)
  let a := bitsVal (outC os 0 1)
  let b := bitsVal (outC os 0 2)
  let τ : Fin C.ℓ → Str := fun j => outC os (j.1 + 1) 1
  let k := C.ℓ + 1
  os.length = C.ℓ + 2 ∧ IsInterval C.N a b ∧ (pos = true → a = b) ∧
    (outC os k 1).length = b + 1 - a ∧ (outC os k 3).length = b + 1 - a ∧
    outC os k 1 ≠ outC os k 3 ∧
    C.Ver (C.cs ρ) τ a b (outC os k 1) (outC os k 2) = true ∧
    C.Ver (C.cs ρ) τ a b (outC os k 3) (outC os k 4) = true

noncomputable def ICommit.selProb (C : ICommit) (pos : Bool) (A : Adv) (t : ℕ) : ℝ :=
  prob fun p : (Fin t → Bool) × C.Coins => C.selWin pos A t p.1 p.2

/-- `bind^int_Com(t)`: the largest probability with which an adversary of running time at most `t`
wins the selective interval binding game. -/
noncomputable def ICommit.bindInt (C : ICommit) (t : ℕ) : ℝ :=
  sSup {x | ∃ A : Adv, A.RunsWithin t [] (Set.range C.selSched) ∧ x = C.selProb false A t}

/-- Schedule of the adaptive games: one invocation per round (phase `0`), then the final invocation
(phase `1`) outputs `v₀, π₀, v₁, π₁` (components `1, 2, 3, 4`) and the interval `{a, …, b}`
(components `5, 6`, in binary) after the commit phase. -/
def ICommit.adaSched (C : ICommit) (ρ : C.Coins) : List (ℕ × Str) :=
  List.ofFn (fun j : Fin C.ℓ => ((0 : ℕ), (ρ j).1)) ++ [(1, [])]

/-- `A` wins the adaptive interval binding game (`pos = false`) or the adaptive position binding game
(`pos = true`). -/
noncomputable def ICommit.adaWin (C : ICommit) (pos : Bool) (A : Adv) (t : ℕ) (ω : Fin t → Bool)
    (ρ : C.Coins) : Prop :=
  let os := A.outs (List.ofFn ω) [] (C.adaSched ρ)
  let τ : Fin C.ℓ → Str := fun j => outC os j.1 1
  let k := C.ℓ
  let a := bitsVal (outC os k 5)
  let b := bitsVal (outC os k 6)
  os.length = C.ℓ + 1 ∧ IsInterval C.N a b ∧ (pos = true → a = b) ∧
    (outC os k 1).length = b + 1 - a ∧ (outC os k 3).length = b + 1 - a ∧
    outC os k 1 ≠ outC os k 3 ∧
    C.Ver (C.cs ρ) τ a b (outC os k 1) (outC os k 2) = true ∧
    C.Ver (C.cs ρ) τ a b (outC os k 3) (outC os k 4) = true

noncomputable def ICommit.adaProb (C : ICommit) (pos : Bool) (A : Adv) (t : ℕ) : ℝ :=
  prob fun p : (Fin t → Bool) × C.Coins => C.adaWin pos A t p.1 p.2

/-- The selective adversary `A` (random tape length `t`) always outputs an interval of size at most
`L` (whenever its first output is an interval of `[N]` at all). -/
noncomputable def ICommit.SelSizeLe (C : ICommit) (A : Adv) (t L : ℕ) : Prop :=
  ∀ (ω : Fin t → Bool) (ρ : C.Coins), IsInterval C.N (C.selI A t ω ρ).1 (C.selI A t ω ρ).2 →
    (C.selI A t ω ρ).2 + 1 - (C.selI A t ω ρ).1 ≤ L

end SuccinctArgOWF.Kilian


