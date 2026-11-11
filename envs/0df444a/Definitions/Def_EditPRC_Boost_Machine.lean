-- Prove2me | Definitions.Def_EditPRC_Boost_Machine
-- name    : EditPRC_Boost_Machine
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T05:07:56.649285+00:00
-- url     : https://prove2.me/theorems/c24a2b32-40f3-4b9a-b569-1de52d92c703
-- title:
--   Bit encodings, polynomial-time machines and oracle algorithms with fresh-randomness oracles (model of Definition 2.1)
-- statement:
--   This file fixes the computational model behind "polynomial-time randomized algorithm" and "polynomial-time distinguisher with oracle access" in Definition 2.1.
--
--   **Bit strings.** A bit string $u$ is written self-delimited as $\mathrm{sd}(u)$: every bit $b$ becomes the pair $1b$ and the string ends with $00$. A tuple $(u_1,\dots,u_r)$ is written $\mathrm{sd}(u_1)\cdots\mathrm{sd}(u_r)$, and $1^\lambda$ is the unary string of length $\lambda$. A symbol $a$ of a finite alphabet $\alpha$ is written as the $w_\alpha$ low-order bits (least significant first) of its index under a fixed enumeration of $\alpha$, where $w_\alpha$ is the bit length of $|\alpha|$; a string over $\alpha$ is written symbol by symbol. Conversely, any bit string $q$ is read as a message in $\alpha^k$: its $j$-th block of $w_\alpha$ bits (missing bits are $0$) is read as a number and reduced modulo $|\alpha|$. Every message is read back from its own encoding, so reading queries this way lets a caller ask for any message.
--
--   **Polynomial-time functions.** A function $F$ on bit strings is polynomial-time if one multi-stack Turing machine (Mathlib's `Turing.FinTM2`) computes it within $p(|u|)$ steps on every input $u$, for a polynomial $p$. A randomized algorithm is a deterministic one that reads its coin string as an additional input.
--
--   **Oracle algorithms.** An oracle algorithm $D$ consists of a number of coins $\mathrm{coins}(\lambda)$, a number of rounds $\mathrm{rounds}(\lambda)$ and a next-move function. On input $1^\lambda$ with coins $c$ and an oracle $O$, it runs in rounds: in each round the next-move function is applied to the configuration $(1^\lambda, c, a_0, \dots, a_{i-1})$, where $a_0,\dots,a_{i-1}$ are the oracle answers received so far. A move $1b\cdots$ halts with output $b$; a move $0q$ queries the oracle, whose $i$-th call (counting from $0$) is answered by $O(i, q)$; any other move halts with output $0$. After $\mathrm{rounds}(\lambda)$ rounds the output is $0$. Because the oracle sees the call number, an oracle that answers with fresh, independent randomness on every call is modelled by drawing one independent random string per call.
--
--   **Running time.** $D$ runs within time $T$ against answers of at most $a(\lambda)$ bits if one Turing machine computes its next-move function and, for all sufficiently large $\lambda$,
--   $$\mathrm{coins}(\lambda) + \mathrm{rounds}(\lambda)\cdot \max_{L \le L_{\max}(\lambda)} t(L) \;\le\; T(\lambda),$$
--   where $t(L)$ bounds the machine's steps on inputs of length $L$ and $L_{\max}(\lambda) = (2\lambda+2) + (2\,\mathrm{coins}(\lambda)+2) + \mathrm{rounds}(\lambda)(2a(\lambda)+2)$ bounds the length of every configuration. $D$ is polynomial-time if this holds with $T$ a polynomial.
--
--   **Uniform probability.** For a finite set $\Omega$ and an event $E \subseteq \Omega$, $\Pr[E] = |E|/|\Omega|$.
--
--   These objects are the shared substrate for the pseudorandomness games of Definition 2.1 and for pseudorandom functions (§2.6).
--
--   **Formalization Note.** The configuration does not store past queries: the next-move function recomputes them, which costs at most a polynomial factor. Every time bound is eventual in $\lambda$, as in $O(\cdot)$ notation; finitely many small $\lambda$ are unconstrained.
-- source:
--   Gozon, Edit-Robust Pseudorandom Codes, Watermarks, and Steganography, STOC 2027 submission (manuscript sha256 73170029…6b60), p. 8 (notation, adversaries running in time 2^{O(s(λ))}), p. 9, Definition 2.1 (polynomial-time randomized algorithms; polynomial-time distinguisher; the uniformly random oracle 𝒰 that outputs a uniformly random string each time it is called)

import Mathlib

set_option autoImplicit false

namespace EditPRC.Boost

/-!
# Bit encodings, polynomial-time functions and oracle algorithms with fresh-randomness oracles

Gozon, *Edit-Robust Pseudorandom Codes, Watermarks, and Steganography*, STOC 2027 submission
(manuscript sha256 73170029…6b60), p. 8 (notation: adversaries running in time `2^{O(s(λ))}`),
p. 9, Definition 2.1 ("a tuple of polynomial-time randomized algorithms", "for any
polynomial-time distinguisher `Dist`", "`𝒰` is the uniformly random oracle that outputs a
uniformly random string each time it is called").

* Machines are Mathlib's multi-stack Turing machines (`Turing.FinTM2`) on bit strings; a
  randomized algorithm is a deterministic one that reads its coin string as an extra input.
* An oracle algorithm is given by its next-move function, which is run once per round on the
  configuration (the input `1^λ`, the coin string and all oracle answers received so far, each
  written self-delimited). A move `true :: b :: _` halts with output `b`; a move `false :: q`
  queries the oracle at `q`; any other move halts with output `false`. After `rounds λ` rounds
  the algorithm halts with output `false`.
* The oracle is a function of the call number and the query, so an oracle that answers with
  fresh randomness on every call is modelled by drawing one independent random string per call.
-/

/-- Self-delimiting encoding of a bit string: every bit `b` becomes `true, b`, and the string
ends with `false, false`. -/
def sd (u : List Bool) : List Bool := u.flatMap (fun b => [true, b]) ++ [false, false]

/-- A tuple of bit strings, each written self-delimited. -/
def tup (us : List (List Bool)) : List Bool := us.flatMap sd

/-- The unary string `1^λ`. -/
def unary (n : ℕ) : List Bool := List.replicate n true

/-- The number of bits used to write one symbol of a finite alphabet `α`. -/
noncomputable def symWidth (α : Type) [Fintype α] : ℕ := Nat.size (Fintype.card α)

/-- A symbol of a finite alphabet, written as the `symWidth α` low-order bits (least significant
first) of its index under the fixed enumeration `Fintype.equivFin α`. -/
noncomputable def symCode {α : Type} [Fintype α] (a : α) : List Bool :=
  (List.range (symWidth α)).map (fun i => Nat.testBit (Fintype.equivFin α a : ℕ) i)

/-- A string over a finite alphabet, written symbol by symbol with `symCode`. -/
noncomputable def strCode {α : Type} [Fintype α] (x : List α) : List Bool := x.flatMap symCode

/-- The number whose binary digits, least significant first, are `u`. -/
def bitsVal (u : List Bool) : ℕ := u.foldr (fun b acc => 2 * acc + if b then 1 else 0) 0

/-- Read a bit string as a symbol: the number it denotes, reduced modulo `|α|`. On `symCode a`
this returns `a`. -/
noncomputable def symParse {α : Type} [Fintype α] [Nonempty α] (u : List Bool) : α :=
  (Fintype.equivFin α).symm ⟨bitsVal u % Fintype.card α, Nat.mod_lt _ Fintype.card_pos⟩

/-- Read an arbitrary bit string `q` as a message in `α^k`: the `j`-th symbol is read from the
`j`-th block of `symWidth α` bits (missing bits count as `0`). Every message `m` is read from
`strCode m`, so an oracle that reads its queries this way lets the caller choose any message. -/
noncomputable def msgParse {α : Type} [Fintype α] [Nonempty α] (k : ℕ) (q : List Bool) :
    Fin k → α :=
  fun j => symParse ((q.drop (j.val * symWidth α)).take (symWidth α))

/-- `f` is bounded by a polynomial. -/
def PolyBounded (f : ℕ → ℕ) : Prop := ∃ p : Polynomial ℕ, ∀ n, f n ≤ p.eval n

/-- `F` is computed by one multi-stack Turing machine within a polynomial number of steps in the
length of its input (Mathlib's `Turing.TM2ComputableInPolyTime`, input and output alphabet
`Bool`). -/
def PolyTimeFn (F : List Bool → List Bool) : Prop :=
  Nonempty (Turing.TM2ComputableInPolyTime (id : List Bool → List Bool)
    (id : List Bool → List Bool) F)

/-- The uniform probability of the event `p` on the finite type `α`. -/
noncomputable def unifProb {α : Type} [Fintype α] (p : α → Prop) : ℝ := by
  classical
  exact ((Finset.univ.filter p).card : ℝ) / (Fintype.card α : ℝ)

/-- An **oracle algorithm**: the number of coins it reads and the number of rounds it may run
at security parameter `λ`, and its next-move function. -/
structure OracleAlg where
  /-- Number of fair coins read at security parameter `λ`. -/
  coins : ℕ → ℕ
  /-- Maximal number of rounds at security parameter `λ` (it halts with output `false` after). -/
  rounds : ℕ → ℕ
  /-- The next-move function, applied to the current configuration. -/
  next : List Bool → List Bool

/-- Run for at most `f` more rounds, with fixed input part `pre` (the input `1^λ` and the coins),
oracle `O` (call number, query ↦ answer) and the answers `ans` received so far. -/
def OracleAlg.exec (D : OracleAlg) (pre : List (List Bool)) (O : ℕ → List Bool → List Bool) :
    ℕ → List (List Bool) → Bool
  | 0, _ => false
  | f + 1, ans =>
    match D.next (tup (pre ++ ans)) with
    | true :: b :: _ => b
    | false :: q => D.exec pre O f (ans ++ [O ans.length q])
    | _ => false

/-- The output bit of `D^O(1^λ)` with coin string `c`. The `i`-th oracle call (from `0`) is
answered by `O i q`. -/
def OracleAlg.output (D : OracleAlg) (lam : ℕ) (c : Fin (D.coins lam) → Bool)
    (O : ℕ → List Bool → List Bool) : Bool :=
  D.exec [unary lam, List.ofFn c] O (D.rounds lam) []

/-- An upper bound on the length of every configuration of `D` at security parameter `λ` when
every oracle answer has at most `a λ` bits. -/
def OracleAlg.cfgBound (D : OracleAlg) (a : ℕ → ℕ) (lam : ℕ) : ℕ :=
  (2 * lam + 2) + (2 * D.coins lam + 2) + D.rounds lam * (2 * a lam + 2)

/-- `D` **runs within time `T`** against oracles whose answers have at most `a λ` bits: one
Turing machine computes its next-move function, and for all sufficiently large `λ` the number
of coins plus `rounds λ` times the largest number of machine steps on a configuration of
admissible length is at most `T λ`. -/
def OracleAlg.RunsWithin (D : OracleAlg) (a : ℕ → ℕ) (T : ℕ → ℝ) : Prop :=
  ∃ M : Turing.TM2ComputableInTime (id : List Bool → List Bool) (id : List Bool → List Bool)
      D.next,
    ∀ᶠ lam in Filter.atTop,
      (((D.coins lam + D.rounds lam * (Finset.range (D.cfgBound a lam + 1)).sup M.time : ℕ))
        : ℝ) ≤ T lam

/-- `D` is a **polynomial-time** oracle algorithm against answers of at most `a λ` bits. -/
def OracleAlg.PolyTime (D : OracleAlg) (a : ℕ → ℕ) : Prop :=
  ∃ p : Polynomial ℕ, D.RunsWithin a (fun lam => ((p.eval lam : ℕ) : ℝ))

end EditPRC.Boost


