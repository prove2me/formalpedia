-- Prove2me | Definitions.Def_ITPIRPreproc_MatchVec_Efficiency
-- name    : ITPIRPreproc_MatchVec_Efficiency
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T07:08:58.143472+00:00
-- url     : https://prove2.me/theorems/0eaf9f7e-a802-49fc-a6ef-7bf77bb504f9
-- title:
--   §4.1 — efficiency requirements of a One Compatible Hint PIR implementation
-- statement:
--   An **implementation** of a family of One Compatible Hint PIR primitives (one for each $m$, for databases of length $n=m^2$) consists of bit-string codes for keys, hints, private states and answers, and word-RAM programs, the same for every $m$ (they read $m$ from a header): samplers for $R\leftarrow\mathcal R$ and $R\leftarrow\mathcal R_i$, a compatibility test, the algorithms $\mathsf{Query}$, $\mathsf{Answer}$ (the server's, with random access to $D$ and the query only) and $\mathsf{Decode}$, and a deterministic **streaming hint computation**, given as an initialization step and a per-chunk step whose state is a bit string. The database is cut into $E=\lfloor m/8\rfloor$ consecutive chunks of $b=\lceil n/E\rceil$ bits (the last zero-padded). It may also carry a public precomputed table (for the matching-vector primitive, the vector tables the client retains), produced by a deterministic program and given to the client programs.
--
--   The implementation meets the **efficiency requirements of §4.1** at size $m$ with parameters $t_{\rm basic},t_{\rm stream},\mathrm{time}(\mathsf{Query}),\mathrm{time}(\mathsf{Decode}),\mathrm{time}(\mathsf{Answer})$ and message lengths $|Q|,|\mathsf{Answer}(D,Q)|$ if, in the worst case over all inputs and coins (every program halts within its bound):
--
--   1. the samplers output the code of a uniform key of $\mathcal R$, resp. of $\mathcal R_i$, and they and the test take work at most $t_{\rm basic}$;
--   2. $\mathsf{Query}$, $\mathsf{Answer}$, $\mathsf{Decode}$ compute the primitive's algorithms (the output law of $\mathsf{Query}$ is that of the primitive) within $\mathrm{time}(\cdot)$, which, as in the paper, includes processing their explicit inputs; codes of keys and answers have at most $|Q|$ and $|\mathsf{Answer}(D,Q)|$ bits;
--   3. for every $L\ge E$ and all keys $R_1,\dots,R_L$, the streaming computation started on the keys and fed the $E$ chunks ends with $(\mathsf{Hint}(D,R_1),\dots,\mathsf{Hint}(D,R_L))$, and its initialization time, its time per chunk and its storage (the input it holds, including keys and chunk, plus working bits) are at most $L\,t_{\rm stream}$;
--   4. the public table is computed within work and storage $E\,t_{\rm stream}$.
--
--   **Formalization Note** The public table is charged to the streaming budget with $L=E$, as the paper does when it counts the construction of the vector tables in the streaming initialization and their storage in the streaming storage (Claim 6.2.4). A primitive without precomputed data has the empty table.
-- source:
--   Jesko Dujmovic, Zhengnan Lai, Daniel Wichs, Nearly Optimal Information-Theoretic PIR with Client Preprocessing, STOC 2027 submission #572 (October 2026), §4.1 "Efficiency", printed p.12 (PDF p.14); §4.2 "Guarantees and costs", printed p.14 (PDF p.16); §6.2, printed p.20 (PDF p.22)

import Mathlib
import Definitions.Def_ITPIRPreproc_MatchVec_Machine
import Definitions.Def_ITPIRPreproc_MatchVec_OneCompatibleHint

open MeasureTheory
open scoped ENNReal

namespace ITPIRPreproc.MatchVec

open WordRAM

/-!
# Efficiency requirements of a One Compatible Hint PIR (§4.1, printed p.12; §4.2, p.14)

"Efficiency. We assume that the basic operations: sample R ← R, R ← R_i, and decide if
i ∈ S(R) are all efficient and can be computed in time t_basic(n). For streaming hint
computation, fix E = ⌊m/8⌋ = Θ(√n). For every integer L ≥ E, there is an efficient deterministic
streaming algorithm that starts with keys R_1, …, R_L, receives D as E consecutive equal-size
chunks, and after the last chunk outputs (Hint(D, R_1), …, Hint(D, R_L)). Its initialization
time, time to process each chunk, and total client storage are each at most L t_stream(n). The
storage bound includes the input keys, intermediate values, and temporary workspace."
(p.14: "For a primitive algorithm A, let time(A) denote its worst-case bit work, including input
and output processing. Message lengths below are also worst-case lengths of primitive queries and
answers.")

An *implementation* of a family of primitives `P m : OCHP (m·m)` consists of bit-string encodings
of keys, hints, private states and answers, and word-RAM programs, the same programs for every
`m` (they read `m` from the header `encNat m`):

* `sampleKey`, `sampleCompat`, `testCompat` — the basic operations;
* `query`, `answer`, `decode` — the primitive's retrieval algorithms; `answer` is the server's and
  receives only the query and random access to `D`;
* `streamInit`, `streamChunk` — the streaming hint computation, as an initialization step and a
  per-chunk step; the streaming state is a bit string, so the computation can be suspended
  between chunks; chunks are the `E` consecutive blocks of `b = ⌈n/E⌉` bits of `D` (the last
  padded with zeros);
* `tableProg` with output `table m` — public precomputed data (for the matching-vector primitive,
  the vector tables that "the client retains", §6.2 p.20). The client programs receive it as part
  of their input. Its computation time and size are charged at most `E · t_stream(n)`, i.e. to the
  streaming initialization budget with `L = E`, which is where the paper accounts for building the
  vector tables ("construct the vector tables", "Storage includes the input keys, vector tables,
  and temporary workspace", Claim 6.2.4). A primitive without precomputed data has `table m = []`.

Message lengths are worst-case: every key (hence every query) is encoded in at most `qLen` bits
and every answer in at most `aLen` bits; these are `|Q|` and `|Answer(D, Q)|`.
-/

/-- An implementation of a family of One Compatible Hint PIR primitives. -/
structure OCHPImpl (P : ∀ m : ℕ, OCHP (m * m)) where
  encKey : ∀ m, (P m).Key → List Bool
  encHint : ∀ m, (P m).HintVal → List Bool
  encSecret : ∀ m, (P m).Secret → List Bool
  encAns : ∀ m, (P m).AnsVal → List Bool
  table : ℕ → List Bool
  tableProg : Program
  sampleKey : Program
  sampleCompat : Program
  testCompat : Program
  query : Program
  answer : Program
  decode : Program
  streamInit : Program
  streamChunk : Program

/-- `E = ⌊m/8⌋`, the number of chunks. -/
def numChunks (m : ℕ) : ℕ :=
  m / 8

/-- The chunk length `b = ⌈n/E⌉` for `n = m²`. -/
def chunkLen (m : ℕ) : ℕ :=
  (m * m + numChunks m - 1) / numChunks m

/-- Chunk number `k` (from `0`) of the database: bits `k·b, …, k·b + b − 1`, zero-padded. -/
def chunk {m : ℕ} (D : Fin (m * m) → Bool) (k : ℕ) : List Bool :=
  List.ofFn fun t : Fin (chunkLen m) =>
    if h : k * chunkLen m + t.val < m * m then D ⟨k * chunkLen m + t.val, h⟩ else false

/-- Input of the per-chunk streaming step: header, the chunk, the streaming state. -/
def streamChunkInput (m : ℕ) (c st : List Bool) : List Bool :=
  encNat m ++ encBits c ++ st

namespace OCHPImpl

variable {P : ∀ m : ℕ, OCHP (m * m)} (I : OCHPImpl P)

/-- Input of the basic samplers `R ← R`. -/
def sampleKeyInput (m : ℕ) : List Bool :=
  encNat m ++ I.table m

/-- Input of `R ← R_i`. -/
def sampleCompatInput (m : ℕ) (i : Fin (m * m)) : List Bool :=
  encNat m ++ encNat i.val ++ I.table m

/-- The explicit arguments `(i, R)` of the compatibility test and of `Query(i, R)` (with the
header). -/
def keyArgs (m : ℕ) (i : Fin (m * m)) (R : (P m).Key) : List Bool :=
  encNat m ++ encNat i.val ++ encBits (I.encKey m R)

/-- Input of the compatibility test and of `Query(i, R)`: arguments, then the public table. -/
def keyInput (m : ℕ) (i : Fin (m * m)) (R : (P m).Key) : List Bool :=
  I.keyArgs m i R ++ I.table m

/-- The explicit argument of `Answer(D, Q)` other than the database (with the header). -/
def answerArgs (m : ℕ) (Q : (P m).Key) : List Bool :=
  encNat m ++ encBits (I.encKey m Q)

/-- Input of `Answer(D, Q)`: header, query, and the database (random access). -/
def answerInput (m : ℕ) (D : Fin (m * m) → Bool) (Q : (P m).Key) : List Bool :=
  I.answerArgs m Q ++ List.ofFn D

/-- The explicit arguments of `Decode(i, R, hint, Q, u, ans)` (with the header). -/
def decodeArgs (m : ℕ) (i : Fin (m * m)) (R : (P m).Key) (z : (P m).HintVal) (Q : (P m).Key)
    (u : (P m).Secret) (a : (P m).AnsVal) : List Bool :=
  encNat m ++ encNat i.val ++ encBits (I.encKey m R) ++ encBits (I.encHint m z) ++
    encBits (I.encKey m Q) ++ encBits (I.encSecret m u) ++ encBits (I.encAns m a)

/-- Input of `Decode`: its explicit arguments, then the public table. -/
def decodeInput (m : ℕ) (i : Fin (m * m)) (R : (P m).Key) (z : (P m).HintVal) (Q : (P m).Key)
    (u : (P m).Secret) (a : (P m).AnsVal) : List Bool :=
  I.decodeArgs m i R z Q u a ++ I.table m

/-- Input of the streaming initialization for the key list `keys` (`L = keys.length`). -/
def streamInitInput (m : ℕ) (keys : List (P m).Key) : List Bool :=
  encNat m ++ encNat keys.length ++ keys.flatMap (fun R => encBits (I.encKey m R)) ++ I.table m

/-- The streaming state after `k` chunks. -/
noncomputable def streamState (J : OCHPImpl P) (m : ℕ) (keys : List (P m).Key)
    (D : Fin (m * m) → Bool) : ℕ → List Bool
  | 0 => output J.streamInit (J.streamInitInput m keys) zeroTape
  | k + 1 => output J.streamChunk
      (streamChunkInput m (chunk D k) (streamState J m keys D k)) zeroTape

/-- The required final output `(Hint(D, R_1), …, Hint(D, R_L))`, each hint self-delimited. -/
def hintsCode (m : ℕ) (keys : List (P m).Key) (D : Fin (m * m) → Bool) : List Bool :=
  keys.flatMap fun R => encBits (I.encHint m ((P m).hint D R))

/-- The **efficiency requirements of §4.1** at size `m` (`n = m²`), with basic time `tB`
(`t_basic(n)`), per-component streaming factor `tS` (`t_stream(n)`), worst-case times `tQ`, `tD`,
`tA` of `Query`, `Decode`, `Answer`, and worst-case message lengths `qLen = |Q|`,
`aLen = |Answer(D, Q)|`. All bounds are worst-case: for every input and every coin outcome, the program halts within the
bound. As in §4.2 ("time(A) denote its worst-case bit work, including input and output
processing"), `tQ`, `tA`, `tD` are at least the lengths of the explicit arguments (outputs are
charged by the machine itself, one unit per output bit). -/
structure Efficient (m : ℕ) (tB tS tQ tD tA : ℝ) (qLen aLen : ℕ) : Prop where
  key_len : ∀ R : (P m).Key, (I.encKey m R).length ≤ qLen
  ans_len : ∀ (D : Fin (m * m) → Bool) (Q : (P m).Key),
    (I.encAns m ((P m).answer D Q)).length ≤ aLen
  /-- The public table: deterministic, computed within the streaming budget with `L = E`. -/
  table_det : Deterministic I.tableProg
  table_ok : Halts I.tableProg (encNat m) zeroTape ∧
    output I.tableProg (encNat m) zeroTape = I.table m ∧
    (cost I.tableProg (encNat m) zeroTape : ℝ) ≤ numChunks m * tS ∧
    (workingBits I.tableProg (encNat m) zeroTape : ℝ) ≤ numChunks m * tS
  /-- `R ← R` in time `t_basic`: the output is the code of a uniform key. -/
  sampleKey_ok :
    (∀ τ, Halts I.sampleKey (I.sampleKeyInput m) τ ∧
      (cost I.sampleKey (I.sampleKeyInput m) τ : ℝ) ≤ tB) ∧
    ∀ x : List Bool, coinTape {τ | output I.sampleKey (I.sampleKeyInput m) τ = x} =
      ((Finset.univ.filter fun R => I.encKey m R = x).card : ℝ≥0∞) /
        (Fintype.card (P m).Key : ℝ≥0∞)
  /-- `R ← R_i` in time `t_basic`: the output is the code of a uniform key of `R_i`. -/
  sampleCompat_ok : ∀ i : Fin (m * m),
    (∀ τ, Halts I.sampleCompat (I.sampleCompatInput m i) τ ∧
      (cost I.sampleCompat (I.sampleCompatInput m i) τ : ℝ) ≤ tB) ∧
    ∀ x : List Bool, coinTape {τ | output I.sampleCompat (I.sampleCompatInput m i) τ = x} =
      (((P m).compat i).filter fun R => I.encKey m R = x).card / (((P m).compat i).card : ℝ≥0∞)
  /-- Deciding `i ∈ S(R)` in time `t_basic`. -/
  test_det : Deterministic I.testCompat
  test_ok : ∀ (i : Fin (m * m)) (R : (P m).Key),
    Halts I.testCompat (I.keyInput m i R) zeroTape ∧
    output I.testCompat (I.keyInput m i R) zeroTape = [decide (i ∈ (P m).sel R)] ∧
    (cost I.testCompat (I.keyInput m i R) zeroTape : ℝ) ≤ tB
  /-- `Query(i, R)` for a compatible key, in time `time(Query)`: the output is
  `encBits (code of Q) ++ code of u`, distributed as `Query(i, R)`. -/
  query_ok : ∀ (i : Fin (m * m)), ∀ R ∈ (P m).compat i,
    (∀ τ, Halts I.query (I.keyInput m i R) τ ∧
      (cost I.query (I.keyInput m i R) τ : ℝ) ≤ tQ) ∧
    ∀ x : List Bool, coinTape {τ | output I.query (I.keyInput m i R) τ = x} =
      ((P m).query i R).toOuterMeasure
        {p | encBits (I.encKey m p.1) ++ I.encSecret m p.2 = x}
  /-- `time(A)` includes input processing: the explicit arguments of `Query`, `Answer` and
  `Decode` (everything except the public table and the database) fit in their time bounds. -/
  query_args : ∀ (i : Fin (m * m)) (R : (P m).Key), ((I.keyArgs m i R).length : ℝ) ≤ tQ
  answer_args : ∀ Q : (P m).Key, ((I.answerArgs m Q).length : ℝ) ≤ tA
  decode_args : ∀ (i : Fin (m * m)) (R : (P m).Key) (z : (P m).HintVal) (Q : (P m).Key)
      (u : (P m).Secret) (a : (P m).AnsVal), ((I.decodeArgs m i R z Q u a).length : ℝ) ≤ tD
  /-- `Answer(D, Q)` in time `time(Answer)`. -/
  answer_det : Deterministic I.answer
  answer_ok : ∀ (D : Fin (m * m) → Bool) (Q : (P m).Key),
    Halts I.answer (I.answerInput m D Q) zeroTape ∧
    output I.answer (I.answerInput m D Q) zeroTape = I.encAns m ((P m).answer D Q) ∧
    (cost I.answer (I.answerInput m D Q) zeroTape : ℝ) ≤ tA
  /-- `Decode` in time `time(Decode)`, on every input. -/
  decode_det : Deterministic I.decode
  decode_ok : ∀ (i : Fin (m * m)) (R : (P m).Key) (z : (P m).HintVal) (Q : (P m).Key)
      (u : (P m).Secret) (a : (P m).AnsVal),
    Halts I.decode (I.decodeInput m i R z Q u a) zeroTape ∧
    decodeBit (output I.decode (I.decodeInput m i R z Q u a) zeroTape) =
      (P m).decode i R z Q u a ∧
    (cost I.decode (I.decodeInput m i R z Q u a) zeroTape : ℝ) ≤ tD
  /-- The deterministic streaming hint computation, for every `L ≥ E` and all `L` keys:
  initialization time, time per chunk and storage (input held, including the keys and the chunk,
  plus working bits) at most `L · t_stream`, and after the `E`-th chunk the state is the list of
  hints. -/
  stream_det : Deterministic I.streamInit ∧ Deterministic I.streamChunk
  stream_ok : ∀ (keys : List (P m).Key), numChunks m ≤ keys.length →
    ∀ D : Fin (m * m) → Bool,
      (Halts I.streamInit (I.streamInitInput m keys) zeroTape ∧
        (cost I.streamInit (I.streamInitInput m keys) zeroTape : ℝ) ≤ keys.length * tS ∧
        (((I.streamInitInput m keys).length +
            workingBits I.streamInit (I.streamInitInput m keys) zeroTape : ℕ) : ℝ) ≤
          keys.length * tS) ∧
      (∀ k < numChunks m,
        let inp := streamChunkInput m (chunk D k) (I.streamState m keys D k)
        Halts I.streamChunk inp zeroTape ∧
        (cost I.streamChunk inp zeroTape : ℝ) ≤ keys.length * tS ∧
        ((inp.length + workingBits I.streamChunk inp zeroTape : ℕ) : ℝ) ≤ keys.length * tS) ∧
      I.streamState m keys D (numChunks m) = I.hintsCode m keys D

end OCHPImpl

end ITPIRPreproc.MatchVec


