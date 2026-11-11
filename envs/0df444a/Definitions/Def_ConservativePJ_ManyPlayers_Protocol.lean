-- Prove2me | Definitions.Def_ConservativePJ_ManyPlayers_Protocol
-- name    : ConservativePJ_ManyPlayers_Protocol
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T15:31:06.678552+00:00
-- url     : https://prove2.me/theorems/7aa27c69-68ad-4960-880d-541c88f8bdd7
-- title:
--   Definitions 2.1–2.2, Eq. (2), (5) — pointer jumping, conservative protocols, costs, ε-error protocols with coins, $B_\varepsilon$, $T_\varepsilon$, µ, µ_bool, γ
-- statement:
--   **Pointer jumping.** Fix $n\ge 1$ vertices per layer, write $[n]=\{1,\dots,n\}$, and fix $k\ge 2$ layers. An input of $\widehat{\mathrm{MPJ}}_k$ is a start vertex $a_1\in[n]$ and layers $f_i:[n]\to[n]$ for $2\le i\le k$; the path is $a_i=f_i(a_{i-1})$ and the correct output is $a_k$. In the Boolean version $\mathrm{MPJ}_k$ the layers $f_2,\dots,f_{k-1}$ map $[n]\to[n]$ and the last layer is $f_k:[n]\to\{0,1\}$; the output is the bit $a_k=f_k(a_{k-1})$. Player $1$ has $a_1$ on its forehead and Player $i$ has $f_i$ on its forehead for $i\ge 2$.
--
--   **Conservative protocols (Definition 2.1).** Players $1,\dots,k$ write one message each on a blackboard, in this order; the message of Player $k$ is the output. Player $i\le k-1$ writes a message in an alphabet $M_i$ fixed in advance (finite, nonempty). The protocol is *conservative*: Player $1$ sees only $f_2,\dots,f_k$ (not $a_1$); Player $i$, $2\le i\le k$, sees only the vertex $a_{i-1}$ reached so far, the layers $f_{i+1},\dots,f_k$ ahead of it, and the messages of Players $1,\dots,i-1$ (not $f_i$, not the layers behind it, not $a_1$). A deterministic protocol is *correct* on an input if its output equals $a_k$.
--
--   **Costs (Definition 2.2).** $\ell_i=\lceil\log_2|M_i|\rceil$ for $1\le i\le k-1$; the *maximum communication* is $\max_{1\le i\le k-1}\ell_i$ and the *total communication* is $\ell_1+\cdots+\ell_{k-1}$. The output of Player $k$ is not counted.
--
--   **Randomness and error.** A protocol with public and private coins induces, once all coins are fixed, a deterministic conservative protocol with the same alphabets; so it is a probability distribution, independent of the input, over finitely many deterministic conservative protocols with common alphabets. Its success probability on an input is the probability that the output is correct, its error probability the probability that it is wrong; it is an *ε-error protocol* if its error probability is at most $\varepsilon$ on every input. For $0\le\varepsilon<1$,
--   $$B_\varepsilon=\min\{\text{maximum communication of an }\varepsilon\text{-error protocol}\},\qquad T_\varepsilon=\min\{\text{total communication of an }\varepsilon\text{-error protocol}\},$$
--   for $\widehat{\mathrm{MPJ}}_k$ and for $\mathrm{MPJ}_k$ with $n$ vertices per layer.
--
--   **Hard distributions (Eq. (2)).** Under $\mu$, $A_1$ is uniform on $[n]$ and $\Pi_2,\dots,\Pi_k$ are uniform permutations of $[n]$, all independent. Under $\mu_{\mathrm{bool}}$, $A_1,\Pi_2,\dots,\Pi_{k-1}$ are as in $\mu$ and the last layer $F_k:[n]\to\{0,1\}$ is independent with independent uniform values. The success probability of a deterministic protocol under such a law is the probability that it is correct on a random input. We put $\theta=1/n$ for $\widehat{\mathrm{MPJ}}_k$ and $\theta=1/2$ for $\mathrm{MPJ}_k$.
--
--   **Section 4 notation.** For $1\le w\le n$, $d=\lceil n/w\rceil$; a partition of $[n]$ into $w$ parts of size at most $d$; the gain $\gamma(p)=\min\{p,1-p\}/(32\sqrt{1+dp})$ of Eq. (5); and the alphabets $(2^w,\,2|M_1|,\,|M_2|,\dots,|M_{m-1}|)$ of a protocol obtained by adding a player in front of a protocol with alphabets $M_1,\dots,M_{m-1}$ (one sign per part; one bit followed by a first message of the old protocol; then the old messages).
--
--   These are the objects of every statement in this mission; one definition per concept of the paper.
--
--   **Formalization Note.** Vertices are `Fin n`; an `Input n k pb` has `start` $=a_1$, `mid j` $=f_{j+2}$ for $j<k-2$, and `last` $=f_k$, with answer type `pb.Ans n` (`Fin n` for `.hat` = $\widehat{\mathrm{MPJ}}$, `Bool` for `.bool` = MPJ). `x.vertex t` $=a_{t+1}$. The message of Player $i+1$ is indexed by `i : Fin (k-1)`, has alphabet `Fin (M i)` with `M i ≥ 1`, and is `msg i x c` for the earlier messages `c`; `conservative` requires it to depend on `x` only through `SameView i`, which is exactly the view of Definition 2.1. Player $k$ is `out (a_{k-1}) (messages)`. `msgLength m = Nat.clog 2 m` $=\lceil\log_2 m\rceil$. A protocol with coins is a `RandProtocol`: deterministic protocols `det r`, `r : Fin N`, with real weights $\ge0$ summing to $1$ (arbitrary real, not only dyadic, weights). `Bε`, `Tε` are `sInf` over ℕ; their sets are nonempty for $n\ge1$, $k\ge2$, so the infimum is attained. `successMu`, `successMuBool` are normalized finite sums over $[n]\times S_n^{k-1}$, resp. $[n]\times S_n^{k-2}\times\{0,1\}^{[n]}$. The objects are used for $k\ge 2$; every statement assumes it (or a threshold implying it).
-- source:
--   Mantri, Tight Bounds for Conservative Pointer Jumping, STOC 2027 submission (manuscript sha256 5f73a9aa…), pp. 6–7 (PDF 8–9), §2: Notation, Pointer jumping, Definition 2.1, Randomness and error, Definition 2.2, The hard distribution (Eq. (2)); p. 9 (PDF 11), §4 standing assumptions and Eq. (5); p. 10 (PDF 12), Lemma 4.1 (message structure); p. 44 (PDF 46), θ and the hard distribution of a problem

import Mathlib

set_option autoImplicit false

namespace ConservativePJ.ManyPlayers

open Finset

/-! Mantri, *Tight Bounds for Conservative Pointer Jumping*, STOC 2027 submission (manuscript sha256
5f73a9aa…), §2 (pp. 6–7): pointer jumping `MPĴ_k` and `MPJ_k`, conservative one-way protocols
(Definition 2.1), their costs and `B_ε`, `T_ε` (Definition 2.2), the hard distributions `µ` and
`µ_bool` (Eq. (2)), and the gain `γ` of Eq. (5) (p. 9). -/

/-- The two problems: `hat` is `MPĴ_k` (the output is the end vertex `a_k ∈ [n]`), `bool` is
`MPJ_k` (the last layer maps into `{0,1}` and the output is a bit). -/
inductive Problem
  | hat
  | bool
  deriving DecidableEq

/-- The answer set of a problem with `n` vertices per layer: `[n]` (as `Fin n`) for `MPĴ_k`,
`{0,1}` (as `Bool`) for `MPJ_k`. -/
def Problem.Ans (n : ℕ) : Problem → Type
  | .hat => Fin n
  | .bool => Bool

instance Problem.instDecidableEqAns (n : ℕ) (pb : Problem) : DecidableEq (pb.Ans n) := by
  cases pb <;> unfold Problem.Ans <;> infer_instance

instance Problem.instFintypeAns (n : ℕ) (pb : Problem) : Fintype (pb.Ans n) := by
  cases pb <;> unfold Problem.Ans <;> infer_instance

/-- An input of the problem `pb` with `k` layers of `n` vertices (vertices `[n]` encoded as
`Fin n`): the start vertex `a_1 = start` (on Player 1's forehead), the middle layers
`f_2, …, f_{k-1} : [n] → [n]` (`mid j = f_{j+2}`, on the forehead of Player `j+2`), and the last
layer `f_k = last : [n] → Ans` (on Player `k`'s forehead). Used only for `k ≥ 2`. -/
structure Input (n k : ℕ) (pb : Problem) where
  start : Fin n
  mid : Fin (k - 2) → Fin n → Fin n
  last : Fin n → pb.Ans n

namespace Input

variable {n k : ℕ} {pb : Problem}

/-- `x.vertex t = a_{t+1}`: `a_1 = start` and `a_{t+2} = f_{t+2}(a_{t+1})` for `t < k - 2`
(the index is frozen past `k - 2`; only `t ≤ k - 2` is ever used). -/
def vertex (x : Input n k pb) : ℕ → Fin n
  | 0 => x.start
  | t + 1 => if h : t < k - 2 then x.mid ⟨t, h⟩ (x.vertex t) else x.vertex t

/-- The correct output `a_k = f_k(a_{k-1})`. -/
def answer (x : Input n k pb) : pb.Ans n :=
  x.last (x.vertex (k - 2))

/-- Two inputs look the same to the speaker with 0-based index `i` (Player `i + 1`), for
`i ≤ k - 2` (Definition 2.1): Player 1 (`i = 0`) sees the layers `f_2, …, f_k`; Player `i + 1`
with `i ≥ 1` sees the vertex `a_i` reached so far and the layers `f_{i+2}, …, f_k` ahead of it
(not `f_{i+1}` on its forehead, not the layers behind it, not `a_1`). -/
def SameView (i : ℕ) (x y : Input n k pb) : Prop :=
  if i = 0 then x.mid = y.mid ∧ x.last = y.last
  else x.vertex (i - 1) = y.vertex (i - 1) ∧
    (∀ j : Fin (k - 2), i ≤ j.val → x.mid j = y.mid j) ∧ x.last = y.last

end Input

/-- A deterministic conservative one-way protocol for `pb` with `k` players and message alphabets
`Fin (M i)`, `i = 0, …, k - 2` (the alphabet of Player `i + 1`, fixed in advance and nonempty).
Player `i + 1` (`i : Fin (k - 1)`) writes `msg i x c`, where `c` are the messages of the earlier
players; `conservative` says it depends on the input only through the view of Player `i + 1`
(Definition 2.1). Player `k` outputs `out a_{k-1} (all messages)`: it sees the vertex `a_{k-1}`
reached so far and the messages. -/
structure DetProtocol (n k : ℕ) (pb : Problem) (M : Fin (k - 1) → ℕ) where
  msg : (i : Fin (k - 1)) → Input n k pb → ((j : Fin (k - 1)) → j < i → Fin (M j)) → Fin (M i)
  out : Fin n → ((j : Fin (k - 1)) → Fin (M j)) → pb.Ans n
  conservative : ∀ (i : Fin (k - 1)) (x y : Input n k pb)
      (c : (j : Fin (k - 1)) → j < i → Fin (M j)),
      Input.SameView i.val x y → msg i x c = msg i y c
  alphabet_pos : ∀ i, 0 < M i

namespace DetProtocol

variable {n k : ℕ} {pb : Problem} {M : Fin (k - 1) → ℕ}

/-- The message actually written by Player `i + 1` on input `x` (players speak in order). -/
def message (P : DetProtocol n k pb M) (x : Input n k pb) (i : Fin (k - 1)) : Fin (M i) :=
  P.msg i x (fun j (_ : j < i) => P.message x j)
termination_by i.val
decreasing_by assumption

/-- The output of Player `k` on input `x`. -/
def run (P : DetProtocol n k pb M) (x : Input n k pb) : pb.Ans n :=
  P.out (x.vertex (k - 2)) (P.message x)

/-- `P` is correct on `x`: its output is `a_k`. -/
def Correct (P : DetProtocol n k pb M) (x : Input n k pb) : Prop :=
  P.run x = x.answer

instance (P : DetProtocol n k pb M) (x : Input n k pb) : Decidable (P.Correct x) := by
  unfold Correct; infer_instance

end DetProtocol

/-- Length `ℓ_i = ⌈log₂ |M_i|⌉` of a message with alphabet of size `m` (Definition 2.2). -/
def msgLength (m : ℕ) : ℕ := Nat.clog 2 m

/-- Maximum communication `max_{1 ≤ i ≤ k-1} ℓ_i` (Definition 2.2; the output is not counted). -/
def maxComm {k : ℕ} (M : Fin (k - 1) → ℕ) : ℕ :=
  Finset.univ.sup (fun i => msgLength (M i))

/-- Total communication `ℓ_1 + ⋯ + ℓ_{k-1}` (Definition 2.2; the output is not counted). -/
def totalComm {k : ℕ} (M : Fin (k - 1) → ℕ) : ℕ :=
  ∑ i, msgLength (M i)

/-- "The first message has at most `w` bits and the other messages before the output have at
most `w + 1` bits each" (§4). -/
def LengthShape {k : ℕ} (M : Fin (k - 1) → ℕ) (w : ℕ) : Prop :=
  ∀ i : Fin (k - 1), msgLength (M i) ≤ (if i.val = 0 then w else w + 1)

/-- A protocol with public and private coins, encoded by the distribution it induces on
deterministic conservative protocols with the common alphabets `M` (fixing all coins gives a
deterministic conservative protocol with the same alphabets): finitely many deterministic
protocols `det r` with real weights `weight r ≥ 0` summing to `1`, independent of the input. -/
structure RandProtocol (n k : ℕ) (pb : Problem) (M : Fin (k - 1) → ℕ) where
  N : ℕ
  weight : Fin N → ℝ
  weight_nonneg : ∀ r, 0 ≤ weight r
  weight_sum : ∑ r, weight r = 1
  det : Fin N → DetProtocol n k pb M

namespace RandProtocol

variable {n k : ℕ} {pb : Problem} {M : Fin (k - 1) → ℕ}

/-- Success probability on the input `x`: the probability that the output is correct. -/
noncomputable def successProb (R : RandProtocol n k pb M) (x : Input n k pb) : ℝ :=
  ∑ r, R.weight r * (if (R.det r).Correct x then 1 else 0)

/-- Error probability on the input `x`: the probability that the output is wrong. -/
noncomputable def errorProb (R : RandProtocol n k pb M) (x : Input n k pb) : ℝ :=
  ∑ r, R.weight r * (if (R.det r).Correct x then 0 else 1)

/-- `R` is an `ε`-error protocol: on every input its output is wrong with probability at most
`ε`. -/
def IsEpsError (R : RandProtocol n k pb M) (ε : ℝ) : Prop :=
  ∀ x, R.errorProb x ≤ ε

end RandProtocol

/-- `B_ε` of `pb` with `k` players and `n` vertices per layer (Definition 2.2): the least maximum
communication of an `ε`-error conservative protocol with public and private coins. -/
noncomputable def Bε (n k : ℕ) (pb : Problem) (ε : ℝ) : ℕ :=
  sInf {b : ℕ | ∃ (M : Fin (k - 1) → ℕ) (R : RandProtocol n k pb M),
    R.IsEpsError ε ∧ maxComm M = b}

/-- `T_ε` of `pb` with `k` players and `n` vertices per layer (Definition 2.2): the least total
communication of an `ε`-error conservative protocol with public and private coins. -/
noncomputable def Tε (n k : ℕ) (pb : Problem) (ε : ℝ) : ℕ :=
  sInf {t : ℕ | ∃ (M : Fin (k - 1) → ℕ) (R : RandProtocol n k pb M),
    R.IsEpsError ε ∧ totalComm M = t}

/-- Success probability under `µ` (Eq. (2)) of a deterministic protocol for `MPĴ_k`: `A_1`
uniform on `[n]` and `Π_2, …, Π_k` uniform on `S_n`, all independent; the normalized number of
correct tuples `(a_1, π_2, …, π_{k-1}, π_k)` (`π` lists `π_2, …, π_{k-1}`, `σ = π_k`). -/
noncomputable def successMu {n k : ℕ} {M : Fin (k - 1) → ℕ}
    (P : DetProtocol n k .hat M) : ℝ :=
  (∑ a : Fin n, ∑ π : Fin (k - 2) → Equiv.Perm (Fin n), ∑ σ : Equiv.Perm (Fin n),
      (if P.Correct ⟨a, fun j => ⇑(π j), ⇑σ⟩ then (1 : ℝ) else 0)) /
    (Fintype.card (Fin n × (Fin (k - 2) → Equiv.Perm (Fin n)) × Equiv.Perm (Fin n)) : ℝ)

/-- Success probability under `µ_bool` (§2) of a deterministic protocol for `MPJ_k`: `A_1` and
`Π_2, …, Π_{k-1}` as in (2), and the last layer `F_k : [n] → {0,1}` independent of them with
independent uniform values. -/
noncomputable def successMuBool {n k : ℕ} {M : Fin (k - 1) → ℕ}
    (P : DetProtocol n k .bool M) : ℝ :=
  (∑ a : Fin n, ∑ π : Fin (k - 2) → Equiv.Perm (Fin n), ∑ g : Fin n → Bool,
      (if P.Correct ⟨a, fun j => ⇑(π j), g⟩ then (1 : ℝ) else 0)) /
    (Fintype.card (Fin n × (Fin (k - 2) → Equiv.Perm (Fin n)) × (Fin n → Bool)) : ℝ)

/-- Success probability under the hard distribution of the problem: `µ` for `MPĴ_k`,
`µ_bool` for `MPJ_k` (Appendix A.4.8). -/
noncomputable def hardSuccess {n k : ℕ} {M : Fin (k - 1) → ℕ} :
    (pb : Problem) → DetProtocol n k pb M → ℝ
  | .hat, P => successMu P
  | .bool, P => successMuBool P

/-- `θ = 1/n` for `MPĴ_k` and `θ = 1/2` for `MPJ_k` (Appendix A.4.8, p. 44). -/
noncomputable def theta (n : ℕ) : Problem → ℝ
  | .hat => 1 / (n : ℝ)
  | .bool => 1 / 2

/-- `d = ⌈n/w⌉`, the bound on the part sizes in §4. -/
noncomputable def partBound (n w : ℕ) : ℕ := ⌈(n : ℝ) / (w : ℝ)⌉₊

/-- `G : [n] → [w]` is a partition of `[n]` into `w` (nonempty) parts `G⁻¹(l)` of size at most
`d`. -/
def IsPartition {n w : ℕ} (G : Fin n → Fin w) (d : ℕ) : Prop :=
  Function.Surjective G ∧ ∀ l : Fin w, (Finset.univ.filter (fun x => G x = l)).card ≤ d

/-- The gain `γ(p) = min{p, 1 − p} / (32 √(1 + d p))` of Eq. (5). -/
noncomputable def gain (d : ℕ) (p : ℝ) : ℝ :=
  min p (1 - p) / (32 * Real.sqrt (1 + (d : ℝ) * p))

/-- The alphabets of the protocol `P⁺` of Lemma 4.1 (and `P⁻` of Lemma A.3.1) for `m + 1`
players built from alphabets `M` of a protocol for `m` players: one sign per part (`2^w`
values), then one bit followed by the first message of `P` (`2 |M_1|` values), then the
alphabets `M_2, …, M_{m-1}` of `P`. -/
def addPlayerAlphabet {m : ℕ} (w : ℕ) (M : Fin (m - 1) → ℕ) : Fin (m + 1 - 1) → ℕ :=
  fun i => if i.val = 0 then 2 ^ w
    else if h : i.val - 1 < m - 1 then (if i.val = 1 then 2 else 1) * M ⟨i.val - 1, h⟩ else 1

end ConservativePJ.ManyPlayers


