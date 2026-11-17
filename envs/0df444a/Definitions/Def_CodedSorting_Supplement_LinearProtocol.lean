-- Prove2me | Definitions.Def_CodedSorting_Supplement_LinearProtocol
-- name    : CodedSorting_Supplement_LinearProtocol
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T11:50:03.166501+00:00
-- url     : https://prove2.me/theorems/b9734148-a25b-43a2-891e-504524e16856
-- title:
--   Finite-round binary linear protocols and their common rates ($R_{\mathrm{code}}$)
-- statement:
--   Fix a finite simple undirected graph $G$ on $\{0,\dots,n-1\}$ and $W$ sessions with sources $s_i$ and sinks $t_i$. Source $s_i$ holds a message $X_i\in\mathbb F_2^k$ of $k$ bits, which sink $t_i$ must recover.
--
--   A **finite-round binary linear protocol** with $T$ rounds is fixed in advance, independently of the input, and consists of:
--
--   1. a **schedule**: for every round $r<T$ and ordered pair $(u,v)$, whether $u$ sends one bit to $v$ in round $r$. Bits travel only along edges of $G$, and never in both directions of an edge in the same round, so each edge carries at most one bit in one direction per round;
--   2. **linear transmissions**: the bit sent from $u$ to $v$ in round $r$ is a sum over $\mathbb F_2$ (an XOR) of bits available at $u$ at the start of round $r$, namely the message bits $X_i(j)$ of the sessions with $s_i=u$ and the bits $u$ received in rounds $r'<r$. The coefficients are fixed in advance;
--   3. **decoders**: for every session $i$, an arbitrary function (local computation and storage are unrestricted) of what the sink $t_i$ holds after round $T-1$, namely its own source messages and every bit it received.
--
--   The protocol is **correct** (zero-error) if for every input $(X_1,\dots,X_W)\in(\mathbb F_2^k)^W$ every decoder $i$ outputs $X_i$. The independence of the messages is the requirement that every combination of inputs is decoded.
--
--   A correct protocol with $k\ge 1$ and $T\ge1$ has **common rate** $k/T$. The set of these rates is $\mathcal R_{\mathrm{code}}(G,s,t)$, and
--   $$R_{\mathrm{code}}=\sup\mathcal R_{\mathrm{code}}(G,s,t).$$
--
--   This is the coding side of Theorem 3.2.
--
--   **Formalization Note** The run is computed round by round: the bits of round $r$ are evaluated from the bits of rounds $<r$, and a pair with no scheduled transmission carries the constant $0$. A sink's own messages are presented as the vector of all messages with those of other nodes replaced by $0$. The supremum is not a `def`: theorems state it with `IsLUB`, because Lean's `sSup` is $0$ on an empty or unbounded set.
-- source:
--   B. Li, Z. Li, S. Liu, Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting, arXiv:2610.20079 (held version, sha256 6e149d97…8850b), §3.2, p.5 (PDF 6), the finite-round binary linear protocol and R_code

import Mathlib

set_option autoImplicit false

namespace CodedSorting

namespace Supplement

/-! # Finite-round binary linear protocols and `R_code`

B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory
Integer Sorting*, arXiv:2610.20079 (held version, sha256 6e149d97…8850b), §3.2, p.5 (PDF 6):
"every transmitted bit is an exclusive-or (XOR), or sum modulo two, of bits already available at
the transmitting node, and transmission times and directions are fixed in advance. In each round,
each edge carries at most one bit in one direction, computed only from initial messages or
information received in earlier rounds. Local computation and storage are unrestricted. If a
protocol delivers `k` bits from each source to its sink in `T` rounds, its common rate is `k/T`."
-/

/-- **A finite-round binary linear protocol** on the simple graph `G` (vertices `Fin n`) with
`W` sessions whose sources are `s i`, delivering `k` bits per session in `T` rounds (rounds
`0, …, T-1`). Everything is fixed in advance, before the input:
* `send r u v`: in round `r`, node `u` transmits one bit to `v`; only along edges of `G`
  (`send_adj`), and never in both directions of an edge in the same round (`send_one_dir`), so
  each edge carries at most one bit in one direction per round;
* the bit sent in round `r` from `u` to `v` is the sum over `𝔽₂` of the message bits
  `X i j` with coefficient `cMsg r u v i j` and of the bits received by `u` from `w` in round `r'`
  with coefficient `cRecv r u v r' w`; a message bit may enter only if it is held by `u`
  (`s i = u`, `cMsg_local`), and a received bit only if it was received by `u` in an earlier round
  (`r' < r` and `send r' w u`, `cRecv_causal`);
* `dec i`: the decoder of session `i`, an arbitrary function (local computation is unrestricted)
  of what the sink holds: its own source messages and every bit it received (see
  `LinearProtocol.ownView`, `LinearProtocol.recvView`). -/
structure LinearProtocol {n W : ℕ} (G : SimpleGraph (Fin n)) (s : Fin W → Fin n) (k T : ℕ) where
  send : Fin T → Fin n → Fin n → Bool
  send_adj : ∀ r u v, send r u v = true → G.Adj u v
  send_one_dir : ∀ r u v, send r u v = true → send r v u = false
  cMsg : Fin T → Fin n → Fin n → Fin W → Fin k → ZMod 2
  cMsg_local : ∀ r u v i j, cMsg r u v i j ≠ 0 → s i = u
  cRecv : Fin T → Fin n → Fin n → Fin T → Fin n → ZMod 2
  cRecv_causal : ∀ r u v r' w, cRecv r u v r' w ≠ 0 → r' < r ∧ send r' w u = true
  dec : Fin W → (Fin W → Fin k → ZMod 2) → (Fin T → Fin n → ZMod 2) → Fin k → ZMod 2

namespace LinearProtocol

variable {n W : ℕ} {G : SimpleGraph (Fin n)} {s : Fin W → Fin n} {k T : ℕ}

/-- `P.bitsBefore X m r u v`: on input `X` (`X i` is the `k`-bit message of session `i`), the bit
sent from `u` to `v` in round `r` if `r < m` and `send r u v`, and `0` otherwise. Round `m` is
computed from the bits of rounds `< m` only. -/
def bitsBefore (P : LinearProtocol G s k T) (X : Fin W → Fin k → ZMod 2) :
    ℕ → Fin T → Fin n → Fin n → ZMod 2
  | 0 => fun _ _ _ => 0
  | m + 1 => fun r u v =>
      if (r : ℕ) < m then P.bitsBefore X m r u v
      else if (r : ℕ) = m then
        (if P.send r u v then
          (∑ i, ∑ j, P.cMsg r u v i j * X i j) +
            ∑ r', ∑ w, P.cRecv r u v r' w * P.bitsBefore X m r' w u
        else 0)
      else 0

/-- The full transcript of the run on input `X`: `P.transcript X r u v` is the bit sent from `u`
to `v` in round `r`, and `0` when no bit is sent. -/
def transcript (P : LinearProtocol G s k T) (X : Fin W → Fin k → ZMod 2) :
    Fin T → Fin n → Fin n → ZMod 2 :=
  P.bitsBefore X T

/-- The source messages held by node `x` on input `X`: `X i` for the sessions with `s i = x`,
and `0` (no information) for the others. -/
def ownView (s : Fin W → Fin n) (X : Fin W → Fin k → ZMod 2) (x : Fin n) :
    Fin W → Fin k → ZMod 2 :=
  fun i j => if s i = x then X i j else 0

/-- The bits received by node `x` during the run on input `X`: `(r, w) ↦` the bit sent from `w` to
`x` in round `r` (`0` when none is sent). -/
def recvView (P : LinearProtocol G s k T) (X : Fin W → Fin k → ZMod 2) (x : Fin n) :
    Fin T → Fin n → ZMod 2 :=
  fun r w => P.transcript X r w x

/-- **Zero-error correctness**: for every input `X ∈ (𝔽₂^k)^W` (the source messages are
independent: every combination occurs) and every session `i`, the decoder of session `i`, applied
to what the sink `t i` holds after the last round, returns the message `X i`. -/
def IsCorrect (P : LinearProtocol G s k T) (t : Fin W → Fin n) : Prop :=
  ∀ (X : Fin W → Fin k → ZMod 2) (i : Fin W),
    P.dec i (ownView s X (t i)) (P.recvView X (t i)) = X i

end LinearProtocol

/-- **Common rates of binary linear protocols** on the network `(G, s, t)`: the rates `k/T` of the
correct finite-round binary linear protocols delivering `k ≥ 1` bits per session in `T ≥ 1`
rounds. `R_code` is the supremum of this set; it is stated through `IsLUB`, since Lean's `sSup`
is `0` on an unbounded or empty set. -/
def codeRates {n W : ℕ} (G : SimpleGraph (Fin n)) (s t : Fin W → Fin n) : Set ℝ :=
  {ρ | ∃ k T : ℕ, 1 ≤ k ∧ 1 ≤ T ∧ ρ = (k : ℝ) / (T : ℝ) ∧
    ∃ P : LinearProtocol G s k T, P.IsCorrect t}

end Supplement

end CodedSorting


