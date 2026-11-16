-- Prove2me | Definitions.Def_AggregatedCodeTesting_Testing_Supplement_Computation
-- name    : AggregatedCodeTesting_Testing_Supplement_Computation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T11:29:01.16376+00:00
-- url     : https://prove2.me/theorems/e96e34af-0718-4619-9c55-5645bdc8803b
-- title:
--   Supplement — binary encodings, actual machine execution and recovery/order computation specifications
-- statement:
--   Use the published deterministic multi-tape binary Turing machine of `MetaSearch.Heyting`. Every transition reads and writes only the scanned symbols and moves each head by at most one cell. Cost is the number of transitions until halting. Input/output is tape 0, stored code-only tables are tape 1, and independent fair random bits are initially placed on tape 2. No arithmetic primitive, oracle, correctness property or assigned clock is part of the machine model.
--
--   Naturals are encoded by their bit length in unary, a separator and little-endian binary digits; integers add a sign, and rationals encode numerator and positive denominator. Matrices have binary dimensions and row-major bits. Observation input consists of $m,w,n,R$ and the $nR$ observation vectors in binary. A full-row-rank parity-check matrix $R$ defines $C=(\operatorname{rowspan}R)^\perp$; rank and structural conditions are predicates on this actual code.
--
--   Blocks are ordered by the first coordinate they contain; coset representatives and nonzero dual words are ordered by their binary numerical value. The stored table is the explicit sequence of characters, witness exponents and rational coefficients from Appendix B. Profile output contains each distinct block-coset count once. This serialization carries exactly the information in the published representative-indexed profile.
--
--   For block $D$, write $m_D=|D|$, $q_D=|C_D^\perp|$, $D_0=d_Dq_D/2$ and $M_D=\binom{m_D+D_0}{m_D}$. Universal positive coefficient $a$ and natural degree $d$ majorize all Appendix B preprocessing bounds by a polynomial in these parameters. The aggregate preprocessing allowance is
--
--   $$P(C)=a\left(1+m+\sum_{D\text{ informative}}(m_D+q_D+D_0+M_D)\right)^d.$$
--
--   The separate per-block specification uses $a(1+m_D+q_D+D_0+M_D)^d$. The $m$ term accommodates reading the full matrix and identifying blocks. A tagged matrix input requests either one block's witness table or the full stored table used by recovery. Realization means that the actual machine halts within the bound with exactly that table. These are conclusions required of the algorithms, not assumptions about them.
--
--   The online specification requires a single fixed-code program to output the exact defined moment decoder on every observation list and every random string. Its time is at most $Na_C(1+L)^{d_C}$, where $N=nR$ and $L=\lceil\log_2(w+1)\rceil+\lceil\log_2(N+1)\rceil$. Thus the composed preprocessing/online cost is $P(C)+Na_C(1+L)^{d_C}$.
--
--   For order computation, encode confidence by $b=\max(1,\lceil\log_2(1/\delta)\rceil)$ for any real $0<\delta<1$. One universal machine must halt on every random string within $a(1+m+2^r+b)^d$ steps. Under a uniform $T$-bit tape, success means that its one output contains every nonzero character, its correct detection order, and their maximum, simultaneously. Success probability is the number of successful $T$-bit tapes divided by $2^T$.
--
--   This interface separates fixed-code witness preprocessing from the code-uniform randomized scalar-order computation. In particular, the witness-table bound includes $M_D$ and can be exponential in block length at fixed dual dimension. All realization predicates describe executable output and time relations of the reused machine; they impose no efficiency or statistical assumption on the code.
-- source:
--   Jianxin Wang, Zixuan Wang, Chenxu Pang, Chaoen Xiao, Lei Zhang, Zaitian Fu, Conghui Zheng, Yiyang Zou, STOC 2027 submission #1555 (October 2026), §5 Theorem 11, printed pp.10–11 (PDF pp.11–12); §6.1 Theorem 12, printed p.11 (PDF p.12); Appendix B, printed pp.14–15 (PDF pp.15–16); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1555.pdf; pinned PDF SHA256 1f5fce093155b2721073a124d87a3c6947269ff7851c61301dfa6e81232f0b2c

import Definitions.Def_AggregatedCodeTesting_Testing_Supplement_Algebra
import Definitions.Def_MetaSearch_Heyting_Machine

set_option autoImplicit false
open Finset Classical
noncomputable section

namespace AggregatedCodeTesting.Testing.Supplement

/-- Self-delimiting binary naturals: unary bit length, separator, binary digits. -/
def natCode (n : ℕ) : List Bool := List.replicate n.bits.length true ++ [false] ++ n.bits

def intCode (n : ℤ) : List Bool := decide (n < 0) :: natCode n.natAbs

def rationalCode (x : ℚ) : List Bool := intCode x.num ++ natCode x.den

def listCode (xs : List ℕ) : List Bool := natCode xs.length ++ xs.flatMap natCode

def wordCode {m : ℕ} (x : Word m) : List Bool := List.ofFn (fun e => decide (x e = 1))

def indexCode {m : ℕ} (v : Fin m →₀ ℕ) : List Bool := (List.ofFn (fun e => v e)).flatMap natCode

/-- Matrix in row-major order with binary dimensions. -/
def matrixCode {m r : ℕ} (R : Matrix (Fin r) (Fin m) (ZMod 2)) : List Bool :=
  natCode m ++ natCode r ++ (List.finRange r).flatMap (fun i => wordCode (R i))

/-- The row span of the supplied parity-check matrix and its kernel code. -/
def rowSpace {m r : ℕ} (R : Matrix (Fin r) (Fin m) (ZMod 2)) : Submodule (ZMod 2) (Word m) :=
  Submodule.span (ZMod 2) (Set.range R)
def matrixCodeSpace {m r : ℕ} (R : Matrix (Fin r) (Fin m) (ZMod 2)) :
    Submodule (ZMod 2) (Word m) := orthogonal (rowSpace R)

/-- Full row rank; no assumption on an order or algorithmic guarantee is bundled here. -/
def FullRowRank {m r : ℕ} (R : Matrix (Fin r) (Fin m) (ZMod 2)) : Prop :=
  LinearIndependent (ZMod 2) R

/-- Canonical coordinate order of blocks, retaining the first occurrence of each block. -/
def orderedBlocks {m : ℕ} (C : Submodule (ZMod 2) (Word m)) : List (Finset (Fin m)) :=
  ((List.finRange m).map (blockOf C)).dedup

/-- Canonical increasing binary order of all words. -/
def orderedWords (m : ℕ) : List (Word m) :=
  (List.finRange (2 ^ m)).map (fun j e => (j.val / 2 ^ e.val % 2 : ℕ))

/-- Canonical increasing binary order of block coset representatives. -/
def orderedRepresentatives {m : ℕ} (C : Submodule (ZMod 2) (Word m))
    (D : Finset (Fin m)) : List (Word m) :=
  (orderedWords m).filter (fun x => decide (x ∈ representatives C D))

/-- Canonical increasing binary order of dual words. -/
def orderedDual {m : ℕ} (C : Submodule (ZMod 2) (Word m)) : List (Word m) :=
  (orderedWords m).filter (fun A => decide (A ∈ dualCode C ∧ A ≠ 0))

/-- Exact witness table, independent of width and confidence. Entries include A, its exponent
vector, and the rational leading coefficient, in increasing binary order. -/
def witnessTableCode {m : ℕ} (C : Submodule (ZMod 2) (Word m)) : List Bool :=
  ((orderedDual C).map fun A => wordCode A ++ indexCode (witnessIndex C univ A) ++
    rationalCode (witnessCoefficient C univ A)).flatten

/-- A step-counted run with input, optional stored table and independent random bits on separate
ordinary tapes. Tape 0 is input/output, tape 1 table, tape 2 random bits. -/
def runBits (M : MetaSearch.Heyting.Machine) (input table coins : List Bool) (steps : ℕ) :
    Option (List Bool) :=
  let c : MetaSearch.Heyting.Config := ⟨0,
    (List.range (M.numTapes + 1)).map (fun j =>
      MetaSearch.Heyting.Tape.ofString (([input, table, coins] : List (List Bool)).getD j []))⟩
  let c' := M.runFor steps c
  if (M.step c').isNone then some ((c'.tapes.headD MetaSearch.Heyting.Tape.blank).output) else none

/-- Natural polynomial majorant: coefficients and degree are quantified before the instances
on which a uniform bound is claimed. -/
def polyBound (a d : ℕ) (x : ℕ) : ℕ := a * (1 + x) ^ d

/-- ceil(log2(1/epsilon)); we use precision b with epsilon_b=2^-b. -/
def precisionError (b : ℕ) : ℝ := (2 : ℝ) ^ (-(b : ℤ))

/-- Appendix B's per-block dimension parameters; no truncation in m. -/
def preprocessingSize {m : ℕ} (C : Submodule (ZMod 2) (Word m)) (D : Finset (Fin m)) : ℕ :=
  let q := (blockDual C D).card
  let B := degreeBound C D
  D.card + q + B + (D.card + B).choose D.card

def preprocessingBudget {m : ℕ} (C : Submodule (ZMod 2) (Word m)) (a d : ℕ) : ℕ :=
  polyBound a d (m + ∑ D ∈ informativeBlocks C, preprocessingSize C D)

/-- Universal polynomial-time realization of the deterministic Appendix B table, for one block.
This is an output/time specification, to be concluded by Theorem 11, never a hypothesis. -/
def RealizesPreprocessing (M : MetaSearch.Heyting.Machine) (a d : ℕ) : Prop :=
  ∀ m r (R : Matrix (Fin r) (Fin m) (ZMod 2)), FullRowRank R →
    let C := matrixCodeSpace R
    HasNoZeroCoord C → IsIndecomposable C → IsInformative C univ →
    runBits M (natCode 0 ++ matrixCode R) [] [] (polyBound a d (preprocessingSize C univ)) =
      some (witnessTableCode C)

/-- Observations are binary coordinates, row-major, with w, batch size, batch count and m. -/
def recoveryInput {m w n R : ℕ} (xs : Fin (n * R) → (Fin m → Fin (w + 1))) : List Bool :=
  natCode m ++ natCode w ++ natCode n ++ natCode R ++
    (List.finRange (n * R)).flatMap (fun i => (List.ofFn (fun e => (xs i e).val)).flatMap natCode)

/-- Output only distinct coset counts per block. It carries precisely the same information as
`profile C l` with its repeated representative coordinates. -/
def profileCode {m : ℕ} (C : Submodule (ZMod 2) (Word m)) (t : Profile C) : List Bool :=
  ((orderedBlocks C).flatMap fun D =>
    if h : D ∈ blocks C then
      (orderedRepresentatives C D).map (fun x => t ⟨D,h⟩ x)
    else []).flatMap natCode

/-- Stored tables concatenated in the same code-only block order. -/
def allTablesCode {m : ℕ} (C : Submodule (ZMod 2) (Word m)) : List Bool :=
  (((orderedBlocks C).filter (fun D => decide (D ∈ informativeBlocks C))).map fun D =>
    ((orderedDual C).filter (fun A => decide (A ∈ blockDual C D))).flatMap fun A =>
      wordCode A ++ indexCode (witnessIndex C D A) ++ rationalCode (witnessCoefficient C D A)).flatten

/-- The actual all-block stored data is produced by a single uniform preprocessor. Its input
is the full binary parity-check matrix, tagged 1 (tag 0 requests one block's witness table).
The m term includes reading the matrix and block decomposition. -/
def RealizesAllPreprocessing (M : MetaSearch.Heyting.Machine) (a d : ℕ) : Prop :=
  ∀ m r (R : Matrix (Fin r) (Fin m) (ZMod 2)), FullRowRank R →
    let C := matrixCodeSpace R
    HasNoZeroCoord C → 0 < sStar C →
    runBits M (natCode 1 ++ matrixCode R) [] [] (preprocessingBudget C a d) =
      some (allTablesCode C)

/-- Online realization on every observation list and every coin string. The program computes the
specified moment decoder; observations are not restricted to the support of a true profile. -/
def RealizesRecovery {m : ℕ} (C : Submodule (ZMod 2) (Word m))
    (M : MetaSearch.Heyting.Machine) (a d : ℕ) : Prop :=
  ∀ w R : ℕ, 1 ≤ w → 1 ≤ R → Odd R →
    ∀ xs : Fin (batchSize C w * R) → (Fin m → Fin (w + 1)), ∀ coins : List Bool,
      runBits M (recoveryInput xs) (allTablesCode C) coins
        (polyBound a d (Nat.clog 2 (w + 1) + Nat.clog 2 (batchSize C w * R + 1)) *
          (batchSize C w * R)) = some (profileCode C (recovery C w R xs))

/-- Correct output containing every nonzero dual word, its order, and their maximum. Theorem 12
also concludes finiteness, so toNat loses no information. -/
def orderOutput {m : ℕ} (C : Submodule (ZMod 2) (Word m)) : List Bool :=
  natCode (sStar C).toNat ++ ((orderedDual C).flatMap fun A =>
    wordCode A ++ natCode (detOrder C univ A).toNat)

/-- Simultaneous success under uniform independent fair bits. Failure includes nonhalting. -/
def orderSuccess {m r : ℕ} (M : MetaSearch.Heyting.Machine)
    (R : Matrix (Fin r) (Fin m) (ZMod 2)) (b T : ℕ) : ℝ :=
  ((univ.filter fun coins : Fin T → Bool =>
    runBits M (matrixCode R ++ natCode b) [] (List.ofFn coins) T =
      some (orderOutput (matrixCodeSpace R))).card : ℝ) / (2 : ℝ) ^ T

/-- One universal order algorithm, worst-case step bound on all random strings. -/
def RealizesOrders (M : MetaSearch.Heyting.Machine) (a d : ℕ) : Prop :=
  ∀ m r (R : Matrix (Fin r) (Fin m) (ZMod 2)), FullRowRank R →
    let C := matrixCodeSpace R
    HasNoZeroCoord C → IsIndecomposable C → IsInformative C univ →
    ∀ delta : ℝ, 0 < delta → delta < 1 →
      let b := max 1 ⌈Real.log (1 / delta) / Real.log 2⌉₊
      ∃ T : ℕ, T ≤ polyBound a d (m + 2 ^ r + b) ∧
        (∀ coins : List Bool, (runBits M (matrixCode R ++ natCode b) [] coins T).isSome) ∧
        1 - delta ≤ orderSuccess M R b T

end AggregatedCodeTesting.Testing.Supplement


