-- Prove2me | Definitions.Def_TightPQRepetition_Main_Preprocess
-- name    : TightPQRepetition_Main_Preprocess
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T23:40:08.488849+00:00
-- url     : https://prove2.me/theorems/dd87eb7b-d61c-4c63-bccf-1b9d9f87765c
-- title:
--   The tail bounds of Lemma 3.7, the adversary $A_S$, and transformations with oracle access to $B$
-- statement:
--   For a prover $S$ against $\widehat V^{k',t'}$, write $\Pr[\sum_{j\ne1}V_j(\tau_j,r_j)\ge s\mid r_{{\rm Query},1}=r^*]$ for the conditional tail. **TailBounds** says that with probability at least $1-\nu/10k$ over $r^*$, both
--   $$\Pr\Big[\sum_{j\ne1}V_j\ge t'\,\Big|\,r^*\Big]\le B(k'-1,t',\varepsilon)+\frac{10(k'-1)+1}{10k}\nu,\qquad \Pr\Big[\sum_{j\ne1}V_j\ge t'-1\,\Big|\,r^*\Big]\le B(k'-1,t'-1,\varepsilon)+\frac{10(k'-1)+1}{10k}\nu$$
--   hold for the same $r^*$.
--
--   The adversary $A_S$ of Appendix A.1, for a set $S$ of coordinates and query coins $r^*_j$ for $j\notin S$, plays $\widehat V^{|S|,t'}$: it has the quantum core of $B$ and a controller that simulates the verifiers outside $S$ with query coins $r^*_j$ and fresh other coins, and passes the coordinates in $S$ to the external verifier. A **transformation** is a randomized classical algorithm that may ask for a fresh execution of $B$, on a fresh copy of its initial state, against $\widehat V^{k,t}$ with coins of its choice, and sees the answers; its output describes $S$, $t'$ and $r^*$.
--
--   **Formalization Note** The conditioning event $r_{{\rm Query},1}=r^*$ has probability exactly $2^{-|r_{\rm Query}|}$, so the conditional probability is written as $2^{|r_{\rm Query}|}$ times the joint probability, with no division. The circuits of a transformation are indexed by its discrete inputs $(\lambda,t,k,\lceil1/\nu\rceil)$ only; it reads the real inputs $\nu,\varepsilon$ through dyadic approximations $a_\nu,a_\varepsilon$ with $|x-\mathrm{val}(a_x)/2^P|\le2^{-P}$, written with $P+2$ bits at the head of its input, for a precision $P$ of its choice. Its precision, coins, number of executions of $B$ and circuit sizes are polynomial in $\lambda+k+\lceil1/\nu\rceil$ and the input length.
-- source:
--   Zvika Brakerski, Andrew Huang, Yael Tauman Kalai, Nicholas Spooner, STOC 2027 submission #158 (October 2026), SHA-256 269f233ccbc44af16ba1b9aceb41299c2242cca048f65729c5fd3451cb6cd0b8, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/158.pdf, Lemma 3.7 and Appendix A.1, printed pp. 12, 35–36 / PDF pp. 14, 37–38

import Mathlib
import Definitions.Def_TightPQRepetition_Main_Encryption

namespace TightPQRepetition.Main

/-!
Brakerski, Huang, Kalai, Spooner, STOC 2027 submission #158, Lemma 3.7 and Appendix A.1 (PDF pp. 14,
37–38): the conditional tail bounds shared by Lemma 3.7 and Theorem 5.1, the adversary `A_S` that
simulates the coordinates outside `S` around black-box `B`, and transformations `T` that run with
oracle access to `B`.
-/

open QAlgorithms

/-- The repeated encrypted verifier `V̂^{k,t}` for numbers `k`, `t`. -/
def hatPar (E : EncScheme) (V : Verifier) (k t : ℕ) : Verifier :=
  (hatV E V).parallel (fun _ => k) (fun _ => t)

/-- `Pr[∑_{j≠1} V_j(τ_j, r_j) ≥ s | r_Query,1 = r*]` over `(τ, r) ← (S, V̂^{k',t'})`. The coordinate
written `1` in the source is coordinate `0` here, and its `r_Query` is the prefix of the coins of
`V̂^{k',t'}`; the conditioning event has probability `2^{-|r_Query|}` exactly, so the conditional
probability is `2^{|r_Query|}` times the joint one. -/
noncomputable def tailGiven (E : EncScheme) (V : Verifier) (S : Strategy) (lam k' t' : ℕ)
    (rstar : Bits) (s : ℤ) : ℝ :=
  (2 : ℝ) ^ V.coins lam * S.eventProb (hatPar E V k' t') lam fun r τ =>
    hatQueryCoins V lam r = rstar ∧
      s ≤ ((hatV E V).acceptCount lam (List.range k').tail r τ : ℤ)

open Classical in
/-- The second part of the conclusion of Lemma 3.7 and hypothesis of Theorem 5.1: with probability
at least `1 - ν/10k` over `r*`, both conditional tails, at thresholds `t'` and `t' - 1`, are at most
the binomial tail plus `(10(k'-1)+1)/(10k) · ν`. -/
def TailBounds (E : EncScheme) (V : Verifier) (S : Strategy) (lam k k' t' : ℕ) (ν ε : ℝ) : Prop :=
  1 - ν / (10 * k) ≤ avgCoins (V.coins lam) fun rstar =>
    if tailGiven E V S lam k' t' rstar t' ≤
          binomTail (k' - 1) t' ε + (10 * ((k' : ℝ) - 1) + 1) / (10 * k) * ν ∧
        tailGiven E V S lam k' t' rstar ((t' : ℤ) - 1) ≤
          binomTail (k' - 1) ((t' : ℤ) - 1) ε + (10 * ((k' : ℝ) - 1) + 1) / (10 * k) * ν
    then 1 else 0

/-- What `T` outputs: the coordinates `S` kept, the threshold `t'`, and the fixed query coins
`r*_j` of the coordinates outside `S`. Then `k' = |S|`. -/
structure PreOutput where
  /-- The kept coordinates, in increasing order. -/
  S : List ℕ
  /-- The new threshold. -/
  t' : ℕ
  /-- The fixed query coins. -/
  rstar : ℕ → Bits

/-- Reading the output of `T` from a string: a bit mask of `S`, `t'` in unary, then the `r*_j`. -/
def decodeOutput (k : ℕ) (x : Bits) : PreOutput where
  S := (List.range k).filter fun j => ((unpack x).getD 0 []).getD j false
  t' := ((unpack x).getD 1 []).length
  rstar j := (unpack x).getD (2 + j) []

/-- The non-query coins of `V̂`, which `A_S` draws from its tape for each simulated coordinate. -/
def simChunk (E : EncScheme) (V : Verifier) (lam : ℕ) : ℕ := chainCoins E V lam

/-- All the coins of the simulated coordinate `j`: `r*_j` and a slice of `A_S`'s tape. -/
def simCoins (E : EncScheme) (V : Verifier) (lam : ℕ) (B : Strategy) (o : PreOutput) (j : ℕ)
    (u : Bits) : Bits :=
  o.rstar j ++ coordCoins (simChunk E V lam) j (u.drop B.tape)

/-- The joint message of `V̂^{k,t}` in round `i` that `A_S` gives to `B`: for `j ∈ S` the external
verifier's message for that coordinate, for `j ∉ S` the simulated `V̂`. -/
def simJoint (E : EncScheme) (V : Verifier) (lam k : ℕ) (B : Strategy) (o : PreOutput) (u : Bits)
    (i : ℕ) (qExt : Bits) (ans : List Bits) : Bits :=
  pack ((List.range k).map fun j =>
    if j ∈ o.S then coordMsg (o.S.idxOf j) qExt
    else (hatV E V).query lam (simCoins E V lam B o j u) i (coordAnswers j ans))

/-- `A_S`'s reconstruction of `B`'s run from the external messages and the core answers: the pairs
(message to `B`, core answer), and `B`'s answers. -/
def simReplay (E : EncScheme) (V : Verifier) (lam k : ℕ) (B : Strategy) (o : PreOutput) (u : Bits)
    (pairs : List (Bits × Bits)) : List (Bits × Bits) × List Bits :=
  pairs.foldl (fun st p =>
    let hist' := st.1 ++ [(simJoint E V lam k B o u st.1.length p.1 st.2, p.2)]
    (hist', st.2 ++ [B.toVerifier st.1.length (pack (controllerView (u.take B.tape) hist'))]))
    ([], [])

/-- The adversary `A_S` of Appendix A.1 (PDF p. 37). It has exactly the quantum core of `B`, hence
uses `B` as a black box and one copy of its initial state; its classical controller runs the
verifiers of the coordinates outside `S`, with query coins fixed to `r*`, and passes the coordinates
in `S` to and from the external verifier `V̂^{|S|,t'}`. -/
def simAdversary (E : EncScheme) (V : Verifier) (lam k : ℕ) (B : Strategy) (o : PreOutput) :
    Strategy where
  n := B.n
  init := B.init
  steps := B.steps
  tape := B.tape + k * simChunk E V lam
  toCore j v :=
    let u := (unpack v).headD []
    let rest := (unpack v).tail
    let st := simReplay E V lam k B o u (pairUp rest)
    B.toCore j (pack (controllerView (u.take B.tape) st.1 ++
      [simJoint E V lam k B o u j (rest.getLastD []) st.2]))
  toVerifier _ v :=
    let u := (unpack v).headD []
    let st := simReplay E V lam k B o u (pairUp (unpack v).tail)
    pack (o.S.map fun j => coordMsg j (st.2.getLastD []))

/-- The inputs of `T`: `(1^λ, t, k, ν, ε)`. -/
structure PreParams where
  /-- The security parameter. -/
  lam : ℕ
  /-- The threshold. -/
  t : ℕ
  /-- The number of repetitions. -/
  k : ℕ
  /-- The advantage. -/
  ν : ℝ
  /-- The target soundness. -/
  ε : ℝ

/-- The discrete inputs `(1^λ, t, k, 1^{⌈1/ν⌉})` of `T`, which index its circuits. The reals `ν`,
`ε` are not part of the index: `T` reads them only through dyadic approximations on its input. -/
structure PreIndex where
  /-- The security parameter. -/
  lam : ℕ
  /-- The threshold. -/
  t : ℕ
  /-- The number of repetitions. -/
  k : ℕ
  /-- `⌈1/ν⌉`, given in unary as in `poly(λ, k, ν⁻¹)`. -/
  N : ℕ

/-- The index of `T` at the parameters `p`. -/
noncomputable def PreParams.index (p : PreParams) : PreIndex := ⟨p.lam, p.t, p.k, ⌈1 / p.ν⌉₊⟩

/-- The cost parameter `λ + k + ⌈1/ν⌉` of `T`. -/
def PreIndex.cost (i : PreIndex) : ℕ := i.lam + i.k + i.N

/-- `a` is a dyadic approximation of `x` to precision `2^{-P}`, written with `P + 2` bits, least
significant first: `|x - val(a)/2^P| ≤ 2^{-P}`. For `x ∈ [0,1]` such a string exists. -/
def IsApprox (x : ℝ) (P : ℕ) (a : Bits) : Prop :=
  a.length = P + 2 ∧ |x - (bitsVal a : ℝ) / 2 ^ P| ≤ 1 / 2 ^ P

/-- A transformation `T`: a randomized classical algorithm that may repeatedly ask for a fresh
execution of `B` (on a fresh copy of its initial state) against `V̂^{k,t}` with coins of its choice,
and sees the transcript. It has no access to `B` otherwise. Its circuits are indexed by the discrete
inputs `(λ, t, k, ⌈1/ν⌉)`; the real inputs `ν`, `ε` reach it only as dyadic approximations, to a
precision `prec` of its choice, written at the head of every input. -/
structure Preprocessor where
  /-- The number of bits of precision at which `T` reads `ν` and `ε`. -/
  prec : PreIndex → ℕ
  /-- The number of random bits. -/
  seed : PreIndex → ℕ
  /-- The maximal number of executions of `B`. -/
  queries : PreIndex → ℕ
  /-- From `pack (aν :: aε :: seed :: history)`: `[]` to stop, or `true :: r` to run `B` with
  coins `r`. -/
  next : PreIndex → Bits → Bits
  /-- From `pack (aν :: aε :: seed :: history)`: the output, in the encoding of `decodeOutput`. -/
  out : PreIndex → Bits → Bits

/-- `T` runs in time `poly(λ, k, 1/ν)` given oracle access to `B`: its precision, its coins, its
number of executions of `B`, and its circuits on inputs of length `n` have size polynomial in
`λ + k + ⌈1/ν⌉` and `n`. -/
def Preprocessor.IsEfficient (T : Preprocessor) : Prop :=
  ∃ s : ℕ → ℕ, PolyBound s ∧ ∀ i : PreIndex, i.t ≤ i.k →
    T.prec i ≤ s i.cost ∧ T.seed i ≤ s i.cost ∧ T.queries i ≤ s i.cost ∧
    ∀ n, ComputedBySize (T.next i) n (s (i.cost + n)) ∧ ComputedBySize (T.out i) n (s (i.cost + n))

/-- The approximations and the history as an input of `T`. -/
def Preprocessor.input (aν aε seed : Bits) (hist : List (Bits × Bits)) : Bits :=
  pack (aν :: aε :: seed :: flattenPairs hist)

open Classical in
/-- The probability that `T`, given the approximations `aν`, `aε`, with the history so far and at
most `f` executions left, ends with an output satisfying `good`. Each execution of `B` has its own
tape and its own fresh core. -/
noncomputable def Preprocessor.prob (T : Preprocessor) (p : PreParams) (aν aε : Bits) (W : Verifier)
    (B : Strategy) (good : PreOutput → Prop) (seed : Bits) : ℕ → List (Bits × Bits) → ℝ
  | 0, hist =>
    if good (decodeOutput p.k (T.out p.index (Preprocessor.input aν aε seed hist))) then 1 else 0
  | f + 1, hist =>
    match T.next p.index (Preprocessor.input aν aε seed hist) with
    | [] =>
      if good (decodeOutput p.k (T.out p.index (Preprocessor.input aν aε seed hist))) then 1 else 0
    | _ :: r =>
      avgCoins B.tape fun u => ∑ o : B.Outcomes (W.rounds p.lam),
        ‖(B.runAgainst W p.lam r u (B.outcomeList o)).ket‖ ^ 2 *
          Preprocessor.prob T p aν aε W B good seed f
            (hist ++ [(r, pack (B.runAgainst W p.lam r u (B.outcomeList o)).answers)])

/-- The probability that the output of `T` satisfies `good`, for `T` run against `B` and given the
approximations `aν`, `aε` of `ν`, `ε`. -/
noncomputable def Preprocessor.outputProb (T : Preprocessor) (E : EncScheme) (V : Verifier)
    (p : PreParams) (aν aε : Bits) (B : Strategy) (good : PreOutput → Prop) : ℝ :=
  avgCoins (T.seed p.index) fun seed =>
    T.prob p aν aε (hatPar E V p.k p.t) B good seed (T.queries p.index) []

/-- The conclusion of part 2 of Lemma 3.7 for an output `o` of `T`, with `k' = |S|` and
`A = A_S`. -/
def PreOutput.IsGood (o : PreOutput) (E : EncScheme) (V : Verifier) (B : Strategy)
    (p : PreParams) : Prop :=
  binomTail o.S.length o.t' p.ε + (10 * (o.S.length : ℝ) - 1) / (10 * p.k) * p.ν ≤
      (simAdversary E V p.lam p.k B o).acceptProb (hatPar E V o.S.length o.t') p.lam ∧
    (o.S.length = 1 ∨
      TailBounds E V (simAdversary E V p.lam p.k B o) p.lam p.k o.S.length o.t' p.ν p.ε)

/-- `k' ∈ [k]` with `S ⊆ [k]` increasing, and `t' ≤ t`, with `t' ≥ 1` whenever `t ≥ 1`; for each
`j ∉ S`, `r*_j` has the length of `r_Query`. -/
def PreOutput.IsWellFormed (o : PreOutput) (V : Verifier) (p : PreParams) : Prop :=
  1 ≤ o.S.length ∧ o.S.length ≤ p.k ∧ o.S.Pairwise (· < ·) ∧ (∀ j ∈ o.S, j < p.k) ∧
    o.t' ≤ p.t ∧ (1 ≤ p.t → 1 ≤ o.t') ∧
    ∀ j, j < p.k → j ∉ o.S → (o.rstar j).length = V.coins p.lam

/-- Every controller function of `S` on inputs of length `n`, in round `j`, has circuits of size at
most `s (j + n)`. -/
def Strategy.ControllerCost (S : Strategy) (s : ℕ → ℕ) : Prop :=
  ∀ j n, ComputedBySize (S.toCore j) n (s (j + n)) ∧ ComputedBySize (S.toVerifier j) n (s (j + n))

end TightPQRepetition.Main


