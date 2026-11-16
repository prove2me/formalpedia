-- Prove2me | Definitions.Def_RoundedPotentials_Main_Supplement_Verification
-- name    : RoundedPotentials_Main_Supplement_Verification
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T13:04:53.199567+00:00
-- url     : https://prove2.me/theorems/869d6d66-a407-44f7-9cfa-99fc7bc4c35d
-- title:
--   Word-RAM layouts, Merlin–Arthur messages, batched excess tests, nondeterminism and γ
-- statement:
--   All running times in Theorem 4.6, Lemma 4.8, Corollaries 4.9–4.10 and Theorem 1.5 are measured on the published randomized word RAM `DynConnWC.Program`, with the run notions of `MinKCutII_Main_Runs`. The machine performs unit-cost operations on $W$-bit words, reads its input once and in order, and takes its random words from a tape. The word size is `wordSize K x T`, computed from the **instance** words $x$ only. A Merlin message or a nondeterministic guess is read after (or interleaved with) the instance, and each of its words is reduced modulo $2^W$, so it cannot enlarge the words.
--
--   The file defines:
--   1. integers as a sign word and an absolute value;
--   2. `wordBits`, the number of bits of a word list;
--   3. queries $(s,t,\text{claim})$, and valid query lists with $1\le q\le n(n-1)$ and $s\ne t$;
--   4. the public words of an edge-list input and of a capacity-matrix input;
--   5. Merlin's message: a header of a constant number `hl` of words and one block of `bl` words per query. Arthur reads the header, the public graph words, $q$, and then each query's public words followed by Merlin's block for it;
--   6. `Accepts`: the run halts with output exactly $[1]$;
--   7. an excess-test **block** $(s,t,p,i_1,\dots,i_n)$ with grid indices $i_u=Q_0y_u$, where $Q_0=32n^2W$, and its promise $s\ne t$, $0\le p\le(n-1)W$, $0\le i_u\le(2n-1)Q_0$;
--   8. `ExcessPass`, the excess tests (7)/(12) $|\mathrm{ex}_g(v)-p(\mathbf 1[v=s]-\mathbf 1[v=t])|\le1/(8n)$ at every vertex, and `excessAnswers`, the list of pass bits;
--   9. the batched and all-pairs input layouts;
--   10. `MMProgram P K₀ T`: $P$ is a deterministic program that multiplies an $r\times d$ by a $d\times d$ natural matrix within $T(r,d)$ steps, the paper's $\mathrm{MM}_d(r)$, at every word size at least $K_0\lceil\log_2(\text{input magnitude})\rceil$;
--   11. the exponent
--   $$\gamma=\min_{0\le\beta\le1}\max\{\omega(3-\beta,1,1),\,3+\beta\}$$
--   as an infimum over $\beta\in[0,1]$, with $\omega(a,b,c)$ the published operational exponent `omega3`;
--   12. `NondetAPMF`, Definition 2.3 for the ordered-pair maximum-flow matrix: for every guess the run halts within $T$ and outputs either $[0]$ ("don't know") or $1$ followed by a matrix whose off-diagonal entries are the maximum-flow values, and some guess produces the matrix.
-- source:
--   Ohad Trabelsi, STOC 2027 submission #1650 (October 2026), pp. 11–12 (§2, Definition 2.3), pp. 17–18 (eqs. (11)–(18)), pp. 22–25 (§§4.3–4.4, Algorithm 1, Corollary 4.9)

import Mathlib
import Definitions.Def_RoundedPotentials_Main_Supplement_Graphs
import Definitions.Def_MultStretchAPASP_Weighted_OmegaExp

namespace RoundedPotentials.Main.Supplement

open RoundedPotentials.Main DynConnWC MinKCutII.Main MultStretchAPASP.Weighted

/-! # Word-RAM verification: input layouts, Merlin–Arthur acceptance, excess tests,
total-function nondeterminism, the exponent γ (§§2, 4.3, 4.4)

All running times are on the published randomized word RAM `DynConnWC.Program` with the run
notions of `MinKCutII_Main_Runs` (`HaltsWithin`, `finalOutput`, `touchedBetween`, `tapeLaw`,
`IsDeterministic`, `wordSize`): unit-cost operations on `W`-bit words, input words read once in
order, random words from the tape. The **instance** words `x` fix the word size
`wordSize K x T`; a proof or guess `g` supplied by Merlin or by the nondeterministic choice is
appended to the input (`x ++ g`) and is read word by word after the instance, each word reduced
modulo `2^W`, so that it cannot enlarge the machine's words. -/

/-- An integer as two input words: a sign word (`1` iff negative) and the absolute value. -/
def intWords (z : ℤ) : List ℕ := [if z < 0 then 1 else 0, z.natAbs]

/-- The number of bits of a list of words, `Σ (⌊log₂ x⌋ + 1)`. -/
def wordBits (ws : List ℕ) : ℕ := (ws.map (fun x => Nat.log 2 x + 1)).sum

/-- A query: an ordered terminal pair `(s, t)` and the claimed integer value of `MaxFlow(s, t)`. -/
abbrev Query (n : ℕ) := Fin n × Fin n × ℤ

/-- A public query list as Theorem 4.6 allows: `1 ≤ q ≤ n(n − 1)` pairs of distinct terminals. -/
def ValidQueries (n : ℕ) (Qs : List (Query n)) : Prop :=
  1 ≤ Qs.length ∧ Qs.length ≤ n * (n - 1) ∧ ∀ a ∈ Qs, a.1 ≠ a.2.1

/-- The public words of one query: `s, t` and the claim. -/
def oneQueryWords {n : ℕ} (a : Query n) : List ℕ := [a.1.val, a.2.1.val] ++ intWords a.2.2

/-- The words of a query list: `q`, then `s, t, claim` for every query. -/
def queryWords {n : ℕ} (Qs : List (Query n)) : List ℕ :=
  Qs.length :: Qs.flatMap oneQueryWords

/-- The public graph words of an edge-list input (Theorem 4.6): `n, W, m`, then the `m` edges
`u, v, c_uv`. -/
def edgeListWords {n W : ℕ} (I : Instance n W) : List ℕ :=
  [n, W, I.edges.length] ++ I.edges.flatMap (fun e => [e.1.val, e.2.1.val, e.2.2])

/-- The public graph words of a capacity-matrix input: `n, W`, then the `n²` capacities row by
row. -/
def matrixWords (n W : ℕ) (c : Fin n → Fin n → ℕ) : List ℕ :=
  [n, W] ++ natMatWords c

/-- Merlin's message in the layout of the protocols of Theorem 4.6: a header of exactly `hl`
words (`hl` a constant of the protocol) and, for each of the `q` queries, a block of exactly
`bl` words. -/
def MAMessage (hl bl q : ℕ) (header : List ℕ) (blocks : ℕ → List ℕ) : Prop :=
  header.length = hl ∧ ∀ k < q, (blocks k).length = bl

/-- The number of bits of Merlin's message. -/
def messageBits (q : ℕ) (header : List ℕ) (blocks : ℕ → List ℕ) : ℕ :=
  wordBits header + ∑ k ∈ Finset.range q, wordBits (blocks k)

/-- The words Arthur reads, in order: Merlin's header, the public graph words, `q`, then for
each query its public words immediately followed by Merlin's block for it. Merlin's message is
fixed before Arthur's coins; the fixed lengths of its parts make the layout unambiguous. -/
def maInput {n : ℕ} (graph : List ℕ) (Qs : List (Query n)) (header : List ℕ)
    (blocks : ℕ → List ℕ) : List ℕ :=
  header ++ graph ++ [Qs.length] ++ (Qs.mapIdx (fun k a => oneQueryWords a ++ blocks k)).flatten

/-- The run on input words `inp` accepts: it halts and its whole output is the single word `1`
(`finalOutput` is `[]` for a run that never halts). -/
def Accepts (W : ℕ) (P : Program) (inp : List ℕ) (ω : ℕ → Fin (2 ^ W)) : Prop :=
  finalOutput W P inp ω = [1]

/-- One block of the batched excess tests of §4.4: an ordered pair `(s, t)`, the claimed value
`p` and the `n` integer grid indices `i_u = Q₀ y_u` (denominator `Q₀ = 32 n² W`). -/
structure Block (n : ℕ) where
  s : Fin n
  t : Fin n
  p : ℕ
  idx : Fin n → ℕ

/-- The words of a block: `s, t, p, i_0, …, i_{n−1}`. -/
def blockWords {n : ℕ} (b : Block n) : List ℕ :=
  [b.s.val, b.t.val, b.p] ++ (List.finRange n).map b.idx

/-- The promise on a block when the excess tests run (Algorithm 1 tests only after its
step 1): distinct terminals, `0 ≤ p ≤ (n − 1)W`, indices in `[0, (2n − 1)Q₀]`. -/
def BlockPromise (n W : ℕ) (b : Block n) : Prop :=
  b.s ≠ b.t ∧ b.p ≤ (n - 1) * W ∧ IndexRange n W (fun u => (b.idx u : ℤ))

/-- The excess tests (7)/(12) of a block for the capacity matrix `c`: at every vertex `v`,
`|ex_g(v) − p(1[v = s] − 1[v = t])| ≤ 1/(8n)`, where `g` is the assignment induced by the grid
potentials `y_u = i_u / Q₀` (Algorithm 1, step 4). -/
def ExcessPass (n W : ℕ) (c : Fin n → Fin n → ℕ) (b : Block n) : Prop :=
  ∀ v, |excess (induced (matrixInstance n W c) (gridPotential n W (fun u => (b.idx u : ℤ)))) v -
    target b.s b.t (b.p : ℝ) v| ≤ epsilon n

open Classical in
/-- The correct answers of the excess tests: `1` for a block that passes, `0` otherwise. -/
noncomputable def excessAnswers (n W : ℕ) (c : Fin n → Fin n → ℕ) (bs : List (Block n)) :
    List ℕ :=
  bs.map (fun b => if ExcessPass n W c b then 1 else 0)

/-- Input of the batched excess tests (Lemma 4.8): `n, W, B, q`, the capacity matrix row by row,
then the `q` blocks. -/
def batchInput (n W B : ℕ) (c : Fin n → Fin n → ℕ) (bs : List (Block n)) : List ℕ :=
  [n, W, B, bs.length] ++ natMatWords c ++ bs.flatMap blockWords

/-- Input of the all-pairs excess tests (Corollary 4.9): `n, W`, the capacity matrix row by row,
then one block for every ordered pair of distinct vertices, in lexicographic order. -/
def allPairsInput (n W : ℕ) (c : Fin n → Fin n → ℕ) (bs : List (Block n)) : List ℕ :=
  [n, W] ++ natMatWords c ++ bs.flatMap blockWords

/-- A deterministic matrix-multiplication program with time bound `T r d` for an `r × d` by
`d × d` product (the paper's `MM_d(r)`): on the input `matMulInput X Y` of
`MultStretchAPASP_Weighted_OmegaExp` it halts within `T r d` steps with the entries of `X·Y` row
by row as output, at every word size at least `K₀ ⌈log₂(inputMag)⌉`. -/
def MMProgram (P : Program) (K₀ : ℕ) (T : ℕ → ℕ → ℝ) : Prop :=
  IsDeterministic P ∧
    ∀ r d : ℕ, 1 ≤ r → 1 ≤ d → ∀ (X : Fin r → Fin d → ℕ) (Y : Fin d → Fin d → ℕ) (W : ℕ),
      K₀ * Nat.clog 2 (inputMag (matMulInput X Y)) ≤ W → ∀ ω : ℕ → Fin (2 ^ W),
        HaltsWithin W P (matMulInput X Y) ω (T r d) ∧
          finalOutput W P (matMulInput X Y) ω = natMatWords (fun i k => ∑ j, X i j * Y j k)

/-- The exponent of Corollary 4.9, `γ = min_{0 ≤ β ≤ 1} max{ω(3 − β, 1, 1), 3 + β}`, as the
infimum over `β ∈ [0, 1]` (a nonempty set of reals bounded below by `3`), with `ω(a, b, c)` the
published operational exponent `omega3`. -/
noncomputable def gammaExp : ℝ :=
  sInf ((fun β : ℝ => max (omega3 (3 - β) 1 1) (3 + β)) '' Set.Icc 0 1)

/-- Input of All-Pairs Max-Flow (Algorithm 1): `n`, then the capacity matrix row by row. -/
def apmfInput (n : ℕ) (c : Fin n → Fin n → ℕ) : List ℕ :=
  n :: natMatWords c

/-- Definition 2.3 (nondeterministic algorithm for a total function) for the ordered-pair
maximum-flow matrix of the capacity matrix `c` (capacities at most `W`), on the word RAM with
word size `wordSize K x T`, `x` the instance: for every guess `g` the deterministic program `P`
on `x ++ g` halts within `T` steps and outputs either `[0]` ("don't know") or `1` followed by a
matrix `M` (row by row) with `M u v = MaxFlow(u, v)` for all `u ≠ v`; and for some guess it
outputs such a matrix. -/
def NondetAPMF (P : Program) (K : ℕ) (n W : ℕ) (c : Fin n → Fin n → ℕ) (T : ℝ) : Prop :=
  IsDeterministic P ∧
    let x := apmfInput n c
    let Wd := wordSize K x T
    let Solution : List ℕ → Prop := fun out =>
      ∃ M : Fin n → Fin n → ℕ, out = 1 :: natMatWords M ∧
        ∀ u v, u ≠ v → MatrixMaxValue n W c u v (M u v)
    (∀ (g : List ℕ) (ω : ℕ → Fin (2 ^ Wd)), HaltsWithin Wd P (x ++ g) ω T ∧
        (finalOutput Wd P (x ++ g) ω = [0] ∨ Solution (finalOutput Wd P (x ++ g) ω))) ∧
      ∃ g : List ℕ, ∀ ω : ℕ → Fin (2 ^ Wd), Solution (finalOutput Wd P (x ++ g) ω)

end RoundedPotentials.Main.Supplement


