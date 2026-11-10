-- Prove2me | Definitions.Def_FreeReplExchange_m3RoundQ
-- name    : FreeReplExchange_m3RoundQ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:18:19.651812+00:00
-- url     : https://prove2.me/theorems/f8113f93-64ba-4f3c-b894-2eaf867c29f4
-- title:
--   Binary encoding of a round and M3's round rule on rational data
-- statement:
--   A **round input** consists of the numbers $n$ of agents (agents $0<1<\dots<n-1$) and $m$ of goods, the initial allocation $x^{(0)}$, rational utility matrices $U$ satisfying the sign conditions, the participating set $P$, the current allocation $x\ge x^{(0)}$ and the set $D$ of rejected exchanges. Its **binary code** writes $n$ and $m$ in self-delimiting binary, then $x^{(0)}$ ($nm$ bits), the $n^2m$ utility entries (each as a sign bit, the binary numerator and the binary denominator of its reduced form), $P$ ($n$ bits), $x$ ($nm$ bits) and the incidence vector of $D$ ($n^2m^2$ bits).
--
--   The **round rule** maps a round input to the incidence vector of the proposal set of M3 in that state: build $G_t$ (the edges of $G(x,P)$ not in $D$), propose nothing if it has no edge, and otherwise select the matching maximizing $\Phi$ for the lexicographic tie order by $(i,j,r,s)$, the example order of §4.2.
--
--   These objects state the per-round polynomial-time guarantee.
--
--   **Formalization Note** Every number is in binary and every block has a length fixed by $n$, $m$ or its own prefix, so the code determines the input; its length is at least $n^2m$ and polynomial in $n$, $m$ and the bit length of the utilities. The lexicographic order is the injective rank $((i\,n+j)\,m+r)\,m+s$.
-- source:
--   Yang–Kandasamy, Pairwise Exchanges of Freely Replicable Goods with Negative Externalities, arXiv:2603.12403 (held version, sha256 3ae07967…), §4.2, pp.32–33 (PDF pp.34–35), "Polynomial-time implementation"; §5.4.1, p.38 (PDF p.40)

import Mathlib
import Definitions.Def_FreeReplExchange_util
import Definitions.Def_FreeReplExchange_m3Select

namespace FreeReplExchange

/-- Self-delimiting binary code of a natural number: the bit length in unary (ones, then a zero),
then the binary digits (`Nat.bits`, least significant first). -/
def natCode (k : ℕ) : List Bool :=
  List.replicate (Nat.bits k).length true ++ [false] ++ Nat.bits k

/-- Binary code of a rational number (Yang–Kandasamy, arXiv:2603.12403, held version, sha256
3ae07967…, p.38: "rational utility parameters encoded in binary"): a sign bit (`true` for negative),
the binary code of the absolute value of the reduced numerator, then that of the denominator. -/
def ratCode (q : ℚ) : List Bool :=
  decide (q.num < 0) :: (natCode q.num.natAbs ++ natCode q.den)

/-- The input of one round of M3 with rational utilities: the numbers of agents `n` (agents are
`Fin n`, ordered by index) and goods `m`, the initial allocation `x^(0)`, the rational utility
matrices `U`, the participating set `P`, the current allocation `x` and the set `D` of rejected
exchanges (the state of §4.3, p.33, at the start of a round). -/
structure RoundInput where
  /-- the number of agents -/
  n : ℕ
  /-- the number of goods -/
  m : ℕ
  /-- the initial allocation -/
  x0 : Fin n → Fin m → Bool
  /-- the rational utility matrices, `U i j r = (U_i)_{j,r}` -/
  U : Fin n → Fin n → Fin m → ℚ
  /-- the participating set -/
  P : Finset (Fin n)
  /-- the current allocation -/
  x : Fin n → Fin m → Bool
  /-- the rejected exchanges -/
  D : Finset (Exchange (Fin n) m)

/-- The real utility matrices of a round input. -/
def RoundInput.realU (I : RoundInput) : Fin I.n → Fin I.n → Fin I.m → ℝ :=
  fun i j r => (I.U i j r : ℝ)

/-- The round inputs of the model: the utility matrices satisfy the sign conditions of §2.1 and
the current allocation dominates the initial one. -/
def ValidRoundInput : Type :=
  {I : RoundInput // SignCond I.realU ∧ Dominates I.x0 I.x}

/-- Bits of an allocation, row by row. -/
def gridCode {n m : ℕ} (f : Fin n → Fin m → Bool) : List Bool :=
  (List.finRange n).flatMap fun i => List.ofFn (f i)

/-- **Binary encoding of a round input.** `n` and `m` in self-delimiting binary, then `x^(0)`
(`nm` bits), the `n²m` utility entries `(U_i)_{j,r}` in binary (`ratCode`, in the order `i, j, r`),
the participating set (`n` bits), `x` (`nm` bits) and the incidence vector of `D` over all
quadruples `((i, r), (j, s))` (`n²m²` bits).

**Formalization Note.** Every number is in binary and every block has a length determined by
`n`, `m` or its own self-delimiting prefix, so the code determines the input and its length is at
least `n²m` (one bit per utility entry) and at most polynomial in `n`, `m` and the bit length of
the utility parameters. -/
def encRoundInput (I : ValidRoundInput) : List Bool :=
  natCode I.1.n ++ natCode I.1.m ++ gridCode I.1.x0 ++
    ((List.finRange I.1.n).flatMap fun i => (List.finRange I.1.n).flatMap fun j =>
      (List.finRange I.1.m).flatMap fun r => ratCode (I.1.U i j r)) ++
    List.ofFn (fun i => decide (i ∈ I.1.P)) ++ gridCode I.1.x ++
    ((List.finRange I.1.n).flatMap fun i => (List.finRange I.1.m).flatMap fun r =>
      (List.finRange I.1.n).flatMap fun j => (List.finRange I.1.m).map fun s =>
        decide (⟨i, r, j, s⟩ ∈ I.1.D))

/-- The global tie order of the paper's example, p.32: "order `((i, r), (j, s))` lexicographically
by `(i, j, r, s)`", as an injective rank on `Fin n` agents and `Fin m` goods. -/
def lexRank (n m : ℕ) (p : Exchange (Fin n) m) : ℕ :=
  ((p.i.val * n + p.j.val) * m + p.r.val) * m + p.s.val

open Classical in
/-- **One round of M3 on rational data**, §4.3, p.33: from the state `(x, D)` build `G_t` (the edges
of `G(x, P)` not in `D`), propose nothing if it has no edge, and otherwise select the matching
maximizing (18) for the lexicographic tie order `lexRank`. The output is the incidence vector of
the proposal set `P_t` over all quadruples `((i, r), (j, s))`, in the order `i, r, j, s`. -/
noncomputable def m3RoundQ (I : ValidRoundInput) : List Bool :=
  let E := edges I.1.x0 I.1.realU I.1.P I.1.x \ I.1.D
  let μ := if E = ∅ then ∅ else m3Select I.1.realU (lexRank I.1.n I.1.m) E
  (List.finRange I.1.n).flatMap fun i => (List.finRange I.1.m).flatMap fun r =>
    (List.finRange I.1.n).flatMap fun j => (List.finRange I.1.m).map fun s =>
      decide (⟨i, r, j, s⟩ ∈ μ)

end FreeReplExchange


