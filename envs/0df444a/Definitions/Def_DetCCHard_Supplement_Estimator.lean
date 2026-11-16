-- Prove2me | Definitions.Def_DetCCHard_Supplement_Estimator
-- name    : DetCCHard_Supplement_Estimator
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:56:02.67061+00:00
-- url     : https://prove2.me/theorems/bf22327c-9dd7-43a3-97a7-8bcdf5ce6f5f
-- title:
--   Randomized machines, random tapes, sparse 3-SAT instances and additive estimators of communication cost
-- statement:
--   A **randomized algorithm** is a one-tape machine (the published Cook machine model) run on the input word followed by a separator and a **random tape**; the tape length is a function of the input only, and probabilities are fractions of the $2^\ell$ tapes of that length. A **sparse 3-SAT instance** is written as the number $N$ of variables in unary followed by the formula, over the variables $0, \dots, N-1$.
--
--   An **additive-$a(T)$ estimator** (Definition 4.1) reads the explicit encoding of a table $M$ with $T$ entries and outputs a value $\widehat D(M)$. On every square table of power-of-two side length it runs in time polynomial in $T$ on every tape, its output can be compared in polynomial time with any binary rational of bit length polynomial in $T$, and on every sufficiently large such table
--   $$
--   |\widehat D(M) - D(M)| \le a(T)
--   $$
--   holds on at least $2/3$ of the tapes (on every tape for a deterministic estimator, which uses no random bits).
--
--   These models express the randomized reduction (Theorem 9.6) and the tradeoff between approximation error and 3-SAT running time (Theorem 9.7).
--
--   **Formalization Note** The output's value is an arbitrary real-valued map accessed only through a deterministic comparator machine that decides whether $\widehat D < p/2^e$; binary rationals are written as a sign, $|p|$ in binary and $e$ in unary.
-- source:
--   Gaspers–He–Mackenzie, NP-Hardness and Additive Inapproximability of Deterministic Communication Complexity, arXiv:2508.05597 (held version, sha256 ad552d13…), Definition 4.1 and §4.1, p.13; §9.3, p.40

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_DetCCHard_CodeSym
import Definitions.Def_DetCCHard_SrcGraph
import Definitions.Def_DetCCHard_commCost

namespace DetCCHard.Supplement

open DetCCHard

/-- The **input of a randomized algorithm** (Gaspers–He–Mackenzie, arXiv:2508.05597, held version
sha256 ad552d13…a4a03, §4.1, p.13, and §9.3, p.40: "A random tape is the sequence of random bits
used by the algorithm"): the input word `x`, a separator, and the random tape, written over the
alphabet `Option (Sym ⊕ Bool)` (`none` is the separator).

**Formalization Note** A randomized algorithm is a published one-tape machine
(`CookPvsNP.TM`) run on this word; the tape length is a function of the input only, and
probabilities are uniform over the tapes of that length. -/
def randInput {Sym : Type} (x : List Sym) (tape : List Bool) : List (Option (Sym ⊕ Bool)) :=
  x.map (some ∘ Sum.inl) ++ none :: tape.map (some ∘ Sum.inr)

/-- The **probability over a uniform random tape** of length `ℓ` of an event `P`: the fraction of
the `2^ℓ` tapes in `P`. -/
noncomputable def tapeFrac (ℓ : ℕ) (P : (Fin ℓ → Bool) → Prop) : ℚ := by
  classical
  exact ((Finset.univ.filter P).card : ℚ) / 2 ^ ℓ

/-- A machine **decides within `T` steps** on input `x` with answer `b`: it halts within `T` steps,
and it is in its accepting state after `T` steps exactly when `b` holds. -/
def DecidesWithin {Sym Γ : Type} (M : CookPvsNP.TM Γ) (ι : Sym ↪ Γ) (x : List Sym) (T : ℕ)
    (b : Prop) : Prop :=
  M.HaltsWithin T (x.map ι) ∧ ((M.run T (M.init (x.map ι))).state = M.qaccept ↔ b)

/-- The **input of the randomized reduction** of Theorem 9.6 (p.41): the gap `k` and the source
graph `G`, as a block `[k]` followed by the blocks of the published `encodeGraph G` (all numbers in
binary). -/
def encodeRandRedInput (G : SrcGraph) (k : ℕ) : List CodeSym :=
  encodeBlocks ([k] :: [G.n] :: G.edges.map fun e => [(e.1 : ℕ), (e.2 : ℕ)])

/-- The **input of sparse 3-SAT** (§4.1, p.13: "the input has `N` variables and at most `c_s N`
clauses"): the number of variables `N` in unary, an `endClause` separator, and the published
`CookPvsNP.encodeCNF` of a formula over the variables `0, …, N − 1`. -/
def encodeSparseInstance (N : ℕ) (Φ : CookPvsNP.CNF) : List CookPvsNP.SatSym :=
  List.replicate N CookPvsNP.SatSym.one ++ CookPvsNP.SatSym.endClause :: CookPvsNP.encodeCNF Φ

/-- The **encoding of a binary rational** `p / 2^e` (Definition 4.1, p.13): a block with the sign
(`1` for negative) and `|p|` in binary, then a block of `e` ones. Its length is linear in the bit
length `⌈log₂(|p| + 1)⌉ + e`. -/
def encodeBinRat (p : ℤ) (e : ℕ) : List CodeSym :=
  encodeBlocks [[if p < 0 then 1 else 0, p.natAbs], List.replicate e 1]

/-- The **bit length** of the binary rational `p / 2^e`: the binary length of `|p|` plus `e`. -/
def binRatBitLen (p : ℤ) (e : ℕ) : ℕ := Nat.size p.natAbs + e

/-- An **estimator** of communication cost (Definition 4.1, p.13): a randomized machine `E` that
reads the explicit encoding of a table followed by a random tape of length `tapeLen` (a function of
the input), and writes an output word over `Out`, whose value is `val`; and a deterministic
**comparator** machine `Cmp` that reads an output word and a binary rational.

**Formalization Note** A deterministic estimator is one with `tapeLen ≡ 0`. The value map `val`
is arbitrary: the only access to an output is through the comparator, as in Definition 4.1 ("Its
output must be comparable in polynomial time with any binary rational"). -/
structure Estimator where
  /-- the estimator's tape alphabet -/
  Γ : Type
  [instFintype : Fintype Γ]
  /-- the input alphabet (table encoding, separator, random bits) inside the tape alphabet -/
  ι : Option (CodeSym ⊕ Bool) ↪ Γ
  /-- the output alphabet -/
  Out : Type
  /-- the output alphabet inside the tape alphabet -/
  ιo : Out ↪ Γ
  /-- the estimating machine -/
  E : CookPvsNP.TM Γ
  /-- the random-tape length, a function of the input -/
  tapeLen : List CodeSym → ℕ
  /-- the value `D̂` of an output word -/
  val : List Out → ℝ
  /-- the comparator's tape alphabet -/
  Γc : Type
  [instFintypec : Fintype Γc]
  /-- the comparator's input alphabet (an output word, a separator, a binary rational) -/
  ιc : Option (Out ⊕ CodeSym) ↪ Γc
  /-- the comparator -/
  Cmp : CookPvsNP.TM Γc

attribute [instance] Estimator.instFintype Estimator.instFintypec

namespace Estimator

variable (Est : Estimator)

/-- A **deterministic** estimator uses no random bits. -/
def IsDeterministic : Prop := ∀ x, Est.tapeLen x = 0

/-- The estimator, as Definition 4.1 (p.13) and the last sentence of Theorem 9.7 (p.42) require it
on **square tables whose side length is a power of two**, is a polynomial-time additive-`a(T)`
estimator, bounded-error if randomized:
1. on every such table `M` with `T` entries, the tape length is at most `T^c + c`, and on every tape
   the estimator halts within `T^c + c` steps;
2. for every polynomial bound `T^{c₁} + c₁` on bit lengths there is a polynomial `T^{c₂} + c₂` such
   that, for every output word on such a table and every binary rational `p/2^e` of bit length at
   most `T^{c₁} + c₁`, the comparator decides within `T^{c₂} + c₂` steps whether `val < p/2^e`;
3. on every such table with `T ≥ T₀` entries, the output satisfies `|D̂(M) − D(M)| ≤ a(T)` on at
   least `2/3` of the tapes (on every tape if the estimator is deterministic).

**Formalization Note** Comparison is the decision of `val < p/2^e`; the paper's "comparable" asks
for no less. `D` is the published `Dcost`. -/
def IsAdditive (a : ℕ → ℝ) : Prop :=
  ∃ c : ℕ, (∀ (j : ℕ) (M : Fin (2 ^ j) → Fin (2 ^ j) → Bool),
      Est.tapeLen (encodeTable M) ≤ (2 ^ j * 2 ^ j) ^ c + c ∧
      ∀ tape : Fin (Est.tapeLen (encodeTable M)) → Bool, ∃ o : List Est.Out,
        RunsWithin Est.E Est.ι Est.ιo (randInput (encodeTable M) (List.ofFn tape))
          ((2 ^ j * 2 ^ j) ^ c + c) o) ∧
    (∀ c₁ : ℕ, ∃ c₂ : ℕ, ∀ (j : ℕ) (M : Fin (2 ^ j) → Fin (2 ^ j) → Bool)
      (tape : Fin (Est.tapeLen (encodeTable M)) → Bool) (o : List Est.Out),
      RunsWithin Est.E Est.ι Est.ιo (randInput (encodeTable M) (List.ofFn tape))
        ((2 ^ j * 2 ^ j) ^ c + c) o →
      ∀ (p : ℤ) (e : ℕ), binRatBitLen p e ≤ (2 ^ j * 2 ^ j) ^ c₁ + c₁ →
        DecidesWithin Est.Cmp Est.ιc
          (o.map (some ∘ Sum.inl) ++ none :: (encodeBinRat p e).map (some ∘ Sum.inr))
          ((2 ^ j * 2 ^ j) ^ c₂ + c₂) (Est.val o < (p : ℝ) / 2 ^ e)) ∧
    ∃ T₀ : ℕ, ∀ (j : ℕ) (M : Fin (2 ^ j) → Fin (2 ^ j) → Bool), T₀ ≤ 2 ^ j * 2 ^ j →
      (2 / 3 : ℚ) ≤ tapeFrac (Est.tapeLen (encodeTable M)) (fun tape =>
        ∀ o : List Est.Out,
          RunsWithin Est.E Est.ι Est.ιo (randInput (encodeTable M) (List.ofFn tape))
            ((2 ^ j * 2 ^ j) ^ c + c) o →
          |Est.val o - (Dcost M : ℝ)| ≤ a (2 ^ j * 2 ^ j))

end Estimator

end DetCCHard.Supplement


