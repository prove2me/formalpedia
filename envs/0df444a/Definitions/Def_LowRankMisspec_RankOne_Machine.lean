-- Prove2me | Definitions.Def_LowRankMisspec_RankOne_Machine
-- name    : LowRankMisspec_RankOne_Machine
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T23:15:58.908778+00:00
-- url     : https://prove2.me/theorems/dc4b3991-07f4-48d0-9c52-57c3e21785fe
-- title:
--   σ-ary CondSamp oracle, candidate-evaluation oracle, learner input and dyadic product codes
-- statement:
--   The machine is the published fair-coin log-cost RAM `PrefixMixLearn_Proper_Machine` (a reference item): one program for all inputs, fair coins as the only randomness, an oracle `query` instruction whose reply is fresh randomness, and a log-cost charge that includes every cell of every query and reply and of the output. `HaltsWithin`, `OutputsSatisfy`, `QueriesWithin` and `outProb` quantify over every run (every coin and every oracle reply).
--
--   **CondSamp (Definition 2.2).** $\mathrm{CondSamp}(P;h)$ returns a full continuation $f\in[\sigma]^{T-|h|}$ with probability $P[f\mid h]$, with fresh randomness at each call; for a history with $P^{(|h|)}[h]=0$ it returns $\bot$; $\mathrm{CondSamp}(P;\varepsilon)$ is $\mathrm{Samp}(P)$. As an oracle on lists of naturals: a query $h$ with $P^{(|h|)}[h]>0$ is answered $1::f$; every other query (zero-mass prefix, an entry $\ge\sigma$, $|h|>T$) is answered $\bot=[0]$, which is distinct from every continuation reply, including the empty continuation $[1]$ at $|h|=T$.
--
--   **Candidate evaluation (Corollary D.2).** For rational laws $H_1,\dots,H_M$, `valOracle P H` answers $0::h$ by CondSamp at $h$ and $1::j::x$ ($j<M$, $x$ a string) with the exact value $H_{j+1}[x]$ as `[numerator, denominator]`; anything else gets `[]`. `nullOracle` answers `[]` to everything.
--
--   **Encodings.** Learner input $[T,\sigma,\eta_{num},\eta_{den},\delta_{num},\delta_{den}]$. A **dyadic product code** has precision $b$ and numerators $n_{t,a}$, cells $[T,\sigma,b,n_{1,1},\dots,n_{T,\sigma}]$; it is **valid** when $\sum_a n_{t,a}=2^b$ for every $t$, and decodes to $H[x]=\prod_t n_{t,x_t}/2^b$. Sampler input $[T,\sigma,k,n]$, output: each string's symbols followed by `[num, den]` of its probability. Validator input $[T,\sigma,M,a_{num},a_{den},\delta_{num},\delta_{den}]$, output: each estimate as `[sign, |num|, den]`. `valBits H` is the largest bit length of a candidate value. `AllQueriesSatisfy` / `QueriesWhereWithin` bound, on every run, which queries are made and how many of a given kind.
-- source:
--   Hasrati, Risteski, Understanding Model Misspecification in Low-Rank Distributions: Tolerant Testing and Agnostic Learning, STOC 2027 submission (manuscript sha256 235f2a4f…), p. 3 (PDF 4), Definition 2.2; p. 8 (PDF 9), Theorem 5.1; p. 31–32 (PDF 32–33), Lemma D.1, Corollary D.2; p. 38–39 (PDF 39–40), Appendix E.2

import Mathlib
import Definitions.Def_PrefixMixLearn_Proper_Machine
import Definitions.Def_LowRankMisspec_RankOne_Laws

set_option autoImplicit false

open scoped Classical ENNReal

open PrefixMixLearn.Proper (Program Oracle runLaw ratCells bits)

noncomputable section

namespace LowRankMisspec.RankOne

/-!
# The σ-ary CondSamp oracle, the candidate-evaluation oracle, and the encodings

Hasrati, Risteski, *Understanding Model Misspecification in Low-Rank Distributions: Tolerant
Testing and Agnostic Learning*, STOC 2027 submission (manuscript sha256 235f2a4f…),
Definition 2.2, p. 3 (PDF 4); Theorem 5.1, p. 8 (PDF 9); Lemma D.1 and Corollary D.2, pp. 31–32
(PDF 32–33); Appendix E.2, pp. 38–39 (PDF 39–40).

The machine is the published fair-coin log-cost RAM `PrefixMixLearn.Proper` (`Program`, `runLaw`,
`HaltsWithin`, `QueriesWithin`, `OutputsSatisfy`, `outProb`, `encLen`, `ratCells`); its generic
`Oracle := List ℕ → PMF (List ℕ)` answers each `query` instruction with fresh randomness.

**CondSamp (Definition 2.2).** `condSamp P` answers a query `h` (a list of naturals, the history)
as follows. If `P^(|h|)[h] > 0` (which forces `|h| ≤ T` and every entry `< σ`), the reply is
`1 :: f`, where the continuation `f ∈ [σ]^{T−|h|}` has law `P[f | h]` (a string `x` is drawn from
`P` restricted to the strings beginning with `h`, normalized, and `f` is its last `T − |h|`
symbols). Every other query (a zero-mass prefix, an entry `≥ σ`, `|h| > T`) gets `⊥`, encoded as
the reply `[0]`, which differs from every continuation reply even when `|h| = T` (continuation `[1]`).
`h = []` is `Samp(P)`.

**Candidate evaluation (Corollary D.2).** `valOracle P H` with candidates `H_1, …, H_M`
(rational-valued, indexed `j = 0, …, M − 1`) answers `0 :: h` as `condSamp P h`, and
`1 :: j :: x` with `j < M` and `x` the symbol list of a string of `[σ]^T` with the exact value
`H_{j+1}[x]` as the two cells `[numerator, denominator]`; every other query gets `[]`.

`nullOracle` answers every query with `[]`: a program run with it makes no use of any oracle.

**Encodings.**
* `learnerInput T σ η δ = [T, σ, η.num, η.den, δ.num, δ.den]`.
* A dyadic product code `c : ProdCode σ T` has precision `b = c.prec` and numerators
  `n_{t,a} = c.num t a`; its cells are `encCode c = [T, σ, b, n_{1,1}, …, n_{1,σ}, …, n_{T,σ}]`; it
  is valid when every row sums to `2^b`; it decodes to the product law
  `lawOfCode c [x] = Π_t n_{t,x_t} / 2^b`.
* `treeInput T σ k n = [T, σ, k, n]`; `samplesCells xs ps` lists, for `i = 1, …, n`, the symbols of
  `X_i` followed by the two cells of the rational `p_i`.
* `valInput T σ M a δ = [T, σ, M, a.num, a.den, δ.num, δ.den]`; `estCells D` lists the estimates
  `D̂_1, …, D̂_M`, each as three cells `[sign, |numerator|, denominator]` (sign `1` iff negative).
* `valBits H` is the largest `bits(num) + bits(den)` over the candidate values `H_j[x]`.
* `AllQueriesSatisfy`: on every run every query made satisfies a predicate.
  `QueriesWhereWithin`: on every run at most `n` of the queries made satisfy a predicate.
-/

/-- The σ-ary conditional sampling oracle `CondSamp(P; ·)` of Definition 2.2; `⊥` is `[0]`, a
continuation `f` is `1 :: f`. -/
def condSamp {σ T : ℕ} (P : Str σ T → ℝ) : Oracle := fun h =>
  let w : Str σ T → ℝ≥0∞ := fun x => if IsPrefix h x then ENNReal.ofReal (P x) else 0
  if hw : (∑' x, w x) ≠ 0 ∧ (∑' x, w x) ≠ ⊤ then
    (PMF.normalize w hw.1 hw.2).map fun x => 1 :: (strCells x).drop h.length
  else PMF.pure [0]

/-- The oracle that answers every query with `[]`. -/
def nullOracle : Oracle := fun _ => PMF.pure []

/-- CondSamp access to `P` (queries `0 :: h`) together with exact evaluation of the candidates
`H_1, …, H_M` (queries `1 :: j :: x`, answered `[num, den]` of `H_{j+1}[x]`). -/
def valOracle {σ T M : ℕ} (P : Str σ T → ℝ) (H : Fin M → Str σ T → ℚ) : Oracle := fun q =>
  match q with
  | 0 :: h => condSamp P h
  | 1 :: j :: xs =>
    if hj : j < M ∧ ∃ x : Str σ T, strCells x = xs then
      PMF.pure (ratCells (H ⟨j, hj.1⟩ (Classical.choose hj.2)))
    else PMF.pure []
  | _ => PMF.pure []

/-- On every run, at every time, every oracle query made so far satisfies `good`. -/
def AllQueriesSatisfy (prog : Program) (Q : Oracle) (input : List ℕ) (good : List ℕ → Prop) :
    Prop :=
  ∀ t, ∀ s ∈ (runLaw prog Q input t).support, ∀ q ∈ s.queries, good q

/-- On every run, at every time, at most `n` of the oracle queries made so far satisfy `kind`. -/
def QueriesWhereWithin (prog : Program) (Q : Oracle) (input : List ℕ) (kind : List ℕ → Prop)
    (n : ℝ) : Prop :=
  ∀ t, ∀ s ∈ (runLaw prog Q input t).support,
    ((s.queries.filter fun q => decide (kind q)).length : ℝ) ≤ n

/-- The learner's input `[T, σ, η.num, η.den, δ.num, δ.den]`. -/
def learnerInput (T σ : ℕ) (η δ : ℚ) : List ℕ := [T, σ] ++ ratCells η ++ ratCells δ

/-- A dyadic product code: precision `b` and numerators `n_{t,a}`. -/
structure ProdCode (σ T : ℕ) where
  /-- The precision `b`. -/
  prec : ℕ
  /-- The numerators `n_{t,a}`. -/
  num : Fin T → Fin σ → ℕ

/-- The cells `[T, σ, b, n_{1,1}, …, n_{1,σ}, …, n_{T,1}, …, n_{T,σ}]` of a product code. -/
def encCode {σ T : ℕ} (c : ProdCode σ T) : List ℕ :=
  T :: σ :: c.prec :: (List.ofFn fun t => List.ofFn fun a => c.num t a).flatten

/-- A valid code: every row's numerators sum to `2^b`. -/
def ValidCode {σ T : ℕ} (c : ProdCode σ T) : Prop :=
  ∀ t, ∑ a, c.num t a = 2 ^ c.prec

/-- The product law of a code: `H[x] = Π_t n_{t,x_t} / 2^b`. -/
def lawOfCode {σ T : ℕ} (c : ProdCode σ T) : Str σ T → ℝ :=
  prodLaw fun t a => (c.num t a : ℝ) / 2 ^ c.prec

/-- The empirical-tree sampler's input `[T, σ, k, n]`. -/
def treeInput (T σ k n : ℕ) : List ℕ := [T, σ, k, n]

/-- The cells of `n` samples with their probabilities: for each `i`, the symbols of `X_i`, then
`[num, den]` of `p_i`. -/
def samplesCells {σ T n : ℕ} (xs : Fin n → Str σ T) (ps : Fin n → ℚ) : List ℕ :=
  (List.ofFn fun i => strCells (xs i) ++ ratCells (ps i)).flatten

/-- The validator's input `[T, σ, M, a.num, a.den, δ.num, δ.den]`. -/
def valInput (T σ M : ℕ) (a δ : ℚ) : List ℕ := [T, σ, M] ++ ratCells a ++ ratCells δ

/-- A rational as three cells `[sign, |numerator|, denominator]`, sign `1` iff negative. -/
def qCells (q : ℚ) : List ℕ := [if q < 0 then 1 else 0, q.num.natAbs, q.den]

/-- The cells of the estimates `D̂_1, …, D̂_M`. -/
def estCells {M : ℕ} (D : Fin M → ℚ) : List ℕ := (List.ofFn fun j => qCells (D j)).flatten

/-- The largest bit length `bits(num) + bits(den)` of a candidate value `H_j[x]`. -/
def valBits {σ T M : ℕ} (H : Fin M → Str σ T → ℚ) : ℕ :=
  Finset.univ.sup fun p : Fin M × Str σ T => bits (H p.1 p.2).num.toNat + bits (H p.1 p.2).den

end LowRankMisspec.RankOne


