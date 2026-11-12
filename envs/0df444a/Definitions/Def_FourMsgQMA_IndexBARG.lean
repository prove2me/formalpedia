-- Prove2me | Definitions.Def_FourMsgQMA_IndexBARG
-- name    : FourMsgQMA_IndexBARG
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:33:07.752958+00:00
-- url     : https://prove2.me/theorems/3039b697-66a7-4c86-806a-be3b01fd1125
-- title:
--   Somewhere-extractable batch arguments: vector interface (Defs. 3.20, 3.21) and index interface (Def. 3.22)
-- statement:
--   **Index interface** (§3.11.1). An index circuit $C:[k]\times\{0,1\}^m\to\{0,1\}$ of size at most $S$ is a NAND circuit on the binary representation of the index followed by the witness. The interface consists of $(crs,td)\leftarrow\mathrm{Setup}(1^\lambda,k,S,m,i^*)$, $\pi\leftarrow\mathrm{Prove}(crs,C,(w_j)_j)$, $\mathrm{Verify}(crs,C,\pi)$ and $w^*:=\mathrm{Extract}(td,C,\pi)$. Its properties:
--
--   1. **perfect completeness**: $\mathrm{Good}_I(crs)$ for every setup outcome. For all supported $C$, all witnesses with $C(j,w_j)=1$ for every $j$, and all prover tapes, the proof verifies;
--   2. **index hiding**, the first half of Definition 3.22;
--   3. **semi-adaptive extraction**, the second half of Definition 3.22: the adversary names $i^*$, receives $crs$ and outputs $(C,\pi)$, and
--   $$
--   \Pr[\mathrm{Verify}(crs,C,\pi)=1\wedge C(i^*,w^*)=0]\le\nu(\lambda);
--   $$
--   4. **efficiency**: CRS, trapdoor and proof lengths and the verification and extraction circuits are $\mathrm{poly}(\lambda,S,m,\log(k+1))$; setup and proving are polynomial time.
--
--   **Vector interface** (§3.11). For a bounded relation $R(u,w)$, a NAND circuit on $n+m$ inputs with $s_R=|R|+n+m$, the analogous algorithms take vectors $u,w$. The properties are perfect completeness ($\mathrm{Good}_B$), index hiding (Definition 3.20), semi-adaptive somewhere extraction with event $\mathrm{Verify}=1\wedge R(u_{i^*},w^*)=0$ (Definition 3.21), lengths $\mathrm{poly}(\lambda,s_R,\log(k+1))$ and polynomial-time algorithms.
--
--   **Formalization Note** Pinned-down version (operator request): an adversary's circuit description is parsed with the inverse of the circuit encoding (unparsable strings are rejected); invalid indices are read as $1$; adversaries are `IsQPT`.
-- source:
--   Goyal, Koppula, Four-Message Arguments for NP ∘ batchQMA and Six-Message Arguments for QMA from LWE, STOC 2027 submission (sha256 6c523d45…), §3.11, pp.19–20 (PDF 21–22): Definitions 3.20, 3.21; §3.11.1, pp.20–21 (PDF 22–23): Definition 3.22

import Mathlib
import Definitions.Def_FourMsgQMA_NandCircuit
import Definitions.Def_FourMsgQMA_SEC

namespace FourMsgQMA

/-!
Goyal, Koppula, STOC 2027 submission (sha256 6c523d45…), §3.11 and §3.11.1 (pp.19–21, PDF 21–23):
somewhere-extractable batch arguments for NP (the vector interface, Definitions 3.20–3.21) and the
index-language interface (Definition 3.22).

Pinned-down version (operator request): relations and index circuits are NAND circuits
(`NandCircuit`); an index `i ∈ [k]` enters an index circuit as its `⌈log₂(k+1)⌉`-bit binary
representation (least significant bit first) followed by the witness; an adversary's circuit
description is parsed with the inverse of `NandCircuit.encode` (an unparsable string is rejected);
adversaries are the published `TightPQRepetition.Main.IsQPT`; "time" is polynomial-time
computability and circuit size.
-/

open Classical QAlgorithms.Complexity TightPQRepetition.Main

/-- The circuit described by a string, if any. -/
noncomputable def decodeCircuit (b : Bits) : Option NandCircuit :=
  if h : ∃ C : NandCircuit, C.encode = b then some (Classical.choose h) else none

/-- The binary representation of an index `i` in `w` bits, least significant bit first. -/
def idxBits (w i : ℕ) : Bits := List.ofFn fun b : Fin w => i.testBit b

/-- `C(i, w)` for an index circuit on `[k] × {0,1}^m`. -/
def indexEval (k : ℕ) (C : NandCircuit) (i : ℕ) (w : Bits) : Bool :=
  C.eval (idxBits (clog2 (k + 1)) i ++ w)

/-- An index circuit `C : [k] × {0,1}^m → {0,1}` of size at most `S`. -/
def IndexCircuitOK (k S m : ℕ) (C : NandCircuit) : Prop :=
  C.WellFormed ∧ C.nIn = clog2 (k + 1) + m ∧ C.size ≤ S

/-- An index-language argument (§3.11.1, pp.20–21). -/
structure IndexBARG where
  /-- Coins of `Setup` at `(λ, k, S, m)`. -/
  setupCoins : ℕ → ℕ → ℕ → ℕ → ℕ
  /-- `(crs, td) ← Setup(1^λ, k, S, m, i*)`, with coins. -/
  setup : ℕ → ℕ → ℕ → ℕ → ℕ → Bits → Bits × Bits
  /-- The prover's tape length at `(λ, k, S, m)`. -/
  proveCoins : ℕ → ℕ → ℕ → ℕ → ℕ
  /-- `π ← Prove(crs, C, (w_j)_{j ∈ [k]})`, with tape. -/
  prove : Bits → NandCircuit → List Bits → Bits → Bits
  /-- `Verify(crs, C, π) ∈ {0,1}`, deterministic. -/
  verify : Bits → NandCircuit → Bits → Bool
  /-- `w* := Extract(td, C, π) ∈ {0,1}^m`, deterministic and total. -/
  extract : Bits → NandCircuit → Bits → Bits

/-- `Good_I(crs)` (p.21): for all supported `C`, all witness vectors with `C(j, w_j) = 1` for every
`j ∈ [k]` and all prover tapes, `Verify(crs, C, Prove(crs, C, (w_j)_j; ω)) = 1`. -/
def IndexBARG.Good (B : IndexBARG) (lam k S m : ℕ) (crs : Bits) : Prop :=
  ∀ C : NandCircuit, IndexCircuitOK k S m C → ∀ w : List Bits, w.length = k →
    (∀ b ∈ w, b.length = m) → (∀ j, 1 ≤ j → j ≤ k → indexEval k C j (w.getD (j - 1) []) = true) →
    ∀ ω : Bits, ω.length = B.proveCoins lam k S m → B.verify crs C (B.prove crs C w ω) = true

/-- Perfect completeness (p.21): `Good_I(crs)` for every setup outcome, every admissible
parameter choice and selected index. -/
def IndexBARG.PerfectlyComplete (B : IndexBARG) : Prop :=
  ∀ lam k S m i, 1 ≤ i → i ≤ k → ∀ r : Bits, r.length = B.setupCoins lam k S m →
    B.Good lam k S m (B.setup lam k S m i r).1

/-- The index-hiding experiment of Definition 3.22 (p.21) for parameters `(k, S, m)(λ)`. -/
def IndexBARG.hidingVerifier (B : IndexBARG) (k S m : ℕ → ℕ) : Verifier where
  rounds := fun _ => 2
  coins := fun lam => B.setupCoins lam (k lam) (S lam) (m lam) + 1
  qLen := fun _ _ => 0
  query := fun lam r j as =>
    let b := r.getD (B.setupCoins lam (k lam) (S lam) (m lam)) false
    let ii := unpack (as.headD [])
    let i := readIndex (k lam) (if b then ii.getD 1 [] else ii.getD 0 [])
    if j = 0 then [] else
      (B.setup lam (k lam) (S lam) (m lam) i (r.take (B.setupCoins lam (k lam) (S lam) (m lam)))).1
  verdict := fun lam r τ =>
    decide ((τ.getD 1 ([], [])).2.getD 0 false = r.getD (B.setupCoins lam (k lam) (S lam) (m lam)) false)

/-- The semi-adaptive extraction experiment of Definition 3.22 (p.21): the adversary names `i*`
(its first answer), receives `crs` for `(crs, td) ← Setup(1^λ, k, S, m, i*)`, and answers
`pack [C, π]`; it wins when `Verify(crs, C, π) = 1` and `C(i*, w*) = 0` for
`w* := Extract(td, C, π)`. -/
noncomputable def IndexBARG.extractVerifier (B : IndexBARG) (k S m : ℕ → ℕ) : Verifier where
  rounds := fun _ => 2
  coins := fun lam => B.setupCoins lam (k lam) (S lam) (m lam)
  qLen := fun _ _ => 0
  query := fun lam r j as =>
    if j = 0 then [] else
      (B.setup lam (k lam) (S lam) (m lam) (readIndex (k lam) (as.headD [])) r).1
  verdict := fun lam r τ =>
    let i := readIndex (k lam) (τ.getD 0 ([], [])).2
    let o := B.setup lam (k lam) (S lam) (m lam) i r
    let ans := unpack (τ.getD 1 ([], [])).2
    match decodeCircuit (ans.getD 0 []) with
    | none => false
    | some C => B.verify o.1 C (ans.getD 1 []) && !(indexEval (k lam) C i (B.extract o.2 C (ans.getD 1 [])))

/-- Definition 3.22 (p.21), both halves: index hiding (`Pr[b̂ = b] ≤ 1/2 + ν`) and semi-adaptive
extraction (`Pr[Verify = 1 ∧ C(i*, w*) = 0] ≤ ν`), for every polynomially bounded parameter
sequence and every QPT adversary. -/
def IndexBARG.Secure (B : IndexBARG) : Prop :=
  ∀ k S m : ℕ → ℕ, PolyBound k → PolyBound S → PolyBound m → ∀ Adv : ℕ → Strategy, IsQPT Adv →
    ∃ ν : ℕ → ℝ, Negligible ν ∧ ∀ lam,
      (Adv lam).acceptProb (B.hidingVerifier k S m) lam ≤ 1 / 2 + ν lam ∧
      (Adv lam).acceptProb (B.extractVerifier k S m) lam ≤ ν lam

/-- Efficiency of the index interface (p.21): setup, its coin length and proving are polynomial
time (so "Setup and proving take time poly(λ, k, S, m)"), and one polynomial `p` bounds, at
`P = p(λ, S, m, ⌈log₂(k+1)⌉)`, the lengths of `crs`, `td` and honest proofs, and the size of
circuits computing verification and extraction on the inputs that occur ("CRS, trapdoor, and proof
lengths and verification and extraction time are poly(λ, S, m, log(k + 1))"). -/
def IndexBARG.Efficient (B : IndexBARG) : Prop :=
  (∃ g : Str → Str, PolyTimeComputable g ∧ ∀ lam k S m,
      g (pack [unary lam, unary k, unary S, unary m]) =
        pack [unary (B.setupCoins lam k S m), unary (B.proveCoins lam k S m)]) ∧
  (∃ g : Str → Str, PolyTimeComputable g ∧ ∀ lam k S m i r,
      g (pack [unary lam, unary k, unary S, unary m, unary i, r]) =
        pack [(B.setup lam k S m i r).1, (B.setup lam k S m i r).2]) ∧
  (∃ g : Str → Str, PolyTimeComputable g ∧ ∀ crs C w ω,
      g (pack [crs, C.encode, pack w, ω]) = B.prove crs C w ω) ∧
  ∃ p : MvPolynomial (Fin 4) ℕ, ∀ lam k S m : ℕ,
    let P := eval4 p lam S m (clog2 (k + 1))
    (∀ i (r : Bits), 1 ≤ i → i ≤ k → r.length = B.setupCoins lam k S m →
      (B.setup lam k S m i r).1.length ≤ P ∧ (B.setup lam k S m i r).2.length ≤ P ∧
      ∀ C w (ω : Bits), IndexCircuitOK k S m C → ω.length = B.proveCoins lam k S m →
        (B.prove (B.setup lam k S m i r).1 C w ω).length ≤ P) ∧
    (∀ n, ComputedOn (fun x => let l := unpack x
        match decodeCircuit (l.getD 1 []) with
        | none => [false]
        | some C => [B.verify (l.getD 0 []) C (l.getD 2 [])])
      {x | ∃ (i : ℕ) (r π : Bits) (C : NandCircuit), 1 ≤ i ∧ i ≤ k ∧
        r.length = B.setupCoins lam k S m ∧ IndexCircuitOK k S m C ∧ π.length ≤ P ∧
        x = pack [(B.setup lam k S m i r).1, C.encode, π]} n P) ∧
    (∀ n, ComputedOn (fun x => let l := unpack x
        match decodeCircuit (l.getD 1 []) with
        | none => []
        | some C => B.extract (l.getD 0 []) C (l.getD 2 []))
      {x | ∃ (i : ℕ) (r π : Bits) (C : NandCircuit), 1 ≤ i ∧ i ≤ k ∧
        r.length = B.setupCoins lam k S m ∧ IndexCircuitOK k S m C ∧ π.length ≤ P ∧
        x = pack [(B.setup lam k S m i r).2, C.encode, π]} n P)

/-! ### The vector interface (§3.11, pp.19–20) -/

/-- A bounded NP relation `R = (R, n, m)`: a NAND circuit on `n + m` inputs, `R(u, w) = R(u ++ w)`. -/
def RelationOK (n m : ℕ) (R : NandCircuit) : Prop := R.WellFormed ∧ R.nIn = n + m

/-- `s_R = |R| + n + m`. -/
def relSize (n m : ℕ) (R : NandCircuit) : ℕ := R.size + n + m

/-- A somewhere-extractable batch argument for a bounded relation (§3.11, p.19). -/
structure VectorBARG where
  /-- Coins of `Setup` at `(λ, k, s_R)`. -/
  setupCoins : ℕ → ℕ → ℕ → ℕ
  /-- `(crs, td) ← Setup(1^λ, k, R, i*)`, with coins (`R` with its bounds `n, m`). -/
  setup : ℕ → ℕ → ℕ → ℕ → NandCircuit → ℕ → Bits → Bits × Bits
  /-- The prover's tape length at `(λ, k, s_R)`. -/
  proveCoins : ℕ → ℕ → ℕ → ℕ
  /-- `π ← Prove(crs, u, w)` for `u ∈ ({0,1}^n)^k`, `w ∈ ({0,1}^m)^k`, with tape. -/
  prove : Bits → List Bits → List Bits → Bits → Bits
  /-- `Verify(crs, u, π)`, deterministic. -/
  verify : Bits → List Bits → Bits → Bool
  /-- `w* := Extract(td, u, π) ∈ {0,1}^m`, deterministic and total. -/
  extract : Bits → List Bits → Bits → Bits

/-- `Good_B(crs)` (p.20): for all vectors `(u, w)` with `R(u_j, w_j) = 1` for every `j` and every
prover tape, `Verify(crs, u, Prove(crs, u, w; ω)) = 1`. -/
def VectorBARG.Good (B : VectorBARG) (lam k n m : ℕ) (R : NandCircuit) (crs : Bits) : Prop :=
  ∀ u w : List Bits, u.length = k → w.length = k → (∀ a ∈ u, a.length = n) →
    (∀ b ∈ w, b.length = m) → (∀ j : Fin k, R.eval (u.getD j [] ++ w.getD j []) = true) →
    ∀ ω : Bits, ω.length = B.proveCoins lam k (relSize n m R) →
      B.verify crs u (B.prove crs u w ω) = true

/-- Perfect completeness (p.20). -/
def VectorBARG.PerfectlyComplete (B : VectorBARG) : Prop :=
  ∀ lam k n m R i, RelationOK n m R → 1 ≤ i → i ≤ k →
    ∀ r : Bits, r.length = B.setupCoins lam k (relSize n m R) →
      B.Good lam k n m R (B.setup lam k n m R i r).1

/-- The index-hiding experiment of Definition 3.20 (p.20) for a fixed sequence `(k, R)`. -/
def VectorBARG.hidingVerifier (B : VectorBARG) (k n m : ℕ → ℕ) (R : ℕ → NandCircuit) : Verifier where
  rounds := fun _ => 2
  coins := fun lam => B.setupCoins lam (k lam) (relSize (n lam) (m lam) (R lam)) + 1
  qLen := fun _ _ => 0
  query := fun lam r j as =>
    let c := B.setupCoins lam (k lam) (relSize (n lam) (m lam) (R lam))
    let ii := unpack (as.headD [])
    let i := readIndex (k lam) (if r.getD c false then ii.getD 1 [] else ii.getD 0 [])
    if j = 0 then [] else (B.setup lam (k lam) (n lam) (m lam) (R lam) i (r.take c)).1
  verdict := fun lam r τ =>
    decide ((τ.getD 1 ([], [])).2.getD 0 false =
      r.getD (B.setupCoins lam (k lam) (relSize (n lam) (m lam) (R lam))) false)

/-- The semi-adaptive somewhere-extraction experiment of Definition 3.21 (p.20): the adversary
names `i*`, receives `crs`, answers `pack (π :: u)`; it wins when `Verify(crs, u, π) = 1` and
`R(u_{i*}, w*) = 0` for `w* := Extract(td, u, π)`. -/
def VectorBARG.extractVerifier (B : VectorBARG) (k n m : ℕ → ℕ) (R : ℕ → NandCircuit) :
    Verifier where
  rounds := fun _ => 2
  coins := fun lam => B.setupCoins lam (k lam) (relSize (n lam) (m lam) (R lam))
  qLen := fun _ _ => 0
  query := fun lam r j as =>
    if j = 0 then [] else
      (B.setup lam (k lam) (n lam) (m lam) (R lam) (readIndex (k lam) (as.headD [])) r).1
  verdict := fun lam r τ =>
    let i := readIndex (k lam) (τ.getD 0 ([], [])).2
    let o := B.setup lam (k lam) (n lam) (m lam) (R lam) i r
    let ans := unpack (τ.getD 1 ([], [])).2
    let u := ans.drop 1
    B.verify o.1 u (ans.getD 0 []) &&
      !((R lam).eval (u.getD (i - 1) [] ++ B.extract o.2 u (ans.getD 0 [])))

/-- Definitions 3.20 and 3.21 (p.20): index hiding and semi-adaptive somewhere extraction, for
every fixed polynomially bounded `(k, R)` and every QPT adversary. -/
def VectorBARG.Secure (B : VectorBARG) : Prop :=
  ∀ (k n m : ℕ → ℕ) (R : ℕ → NandCircuit), PolyBound k → PolyBound (fun lam => relSize (n lam) (m lam) (R lam)) →
    (∀ lam, RelationOK (n lam) (m lam) (R lam)) → ∀ Adv : ℕ → Strategy, IsQPT Adv →
    ∃ ν : ℕ → ℝ, Negligible ν ∧ ∀ lam,
      (Adv lam).acceptProb (B.hidingVerifier k n m R) lam ≤ 1 / 2 + ν lam ∧
      (Adv lam).acceptProb (B.extractVerifier k n m R) lam ≤ ν lam

/-- Succinctness of the vector interface (p.20): CRS, trapdoor and proof lengths are
`poly(λ, s_R, log(k + 1))`; setup, proving, verification and extraction run in time
`poly(λ, k, s_R)` (polynomial-time computability on the packed inputs, with `λ, k, n, m, i` in
unary and `R` encoded). -/
def VectorBARG.Efficient (B : VectorBARG) : Prop :=
  (∃ g : Str → Str, PolyTimeComputable g ∧ ∀ lam k s,
      g (pack [unary lam, unary k, unary s]) =
        pack [unary (B.setupCoins lam k s), unary (B.proveCoins lam k s)]) ∧
  (∃ g : Str → Str, PolyTimeComputable g ∧ ∀ lam k n m R i r,
      g (pack [unary lam, unary k, unary n, unary m, R.encode, unary i, r]) =
        pack [(B.setup lam k n m R i r).1, (B.setup lam k n m R i r).2]) ∧
  (∃ g : Str → Str, PolyTimeComputable g ∧ ∀ crs u w ω,
      g (pack [crs, pack u, pack w, ω]) = B.prove crs u w ω) ∧
  (∃ g : Str → Str, PolyTimeComputable g ∧ ∀ crs u π, g (pack [crs, pack u, π]) = [B.verify crs u π]) ∧
  (∃ g : Str → Str, PolyTimeComputable g ∧ ∀ td u π, g (pack [td, pack u, π]) = B.extract td u π) ∧
  ∃ p : MvPolynomial (Fin 4) ℕ, ∀ lam k n m R i (r : Bits), RelationOK n m R → 1 ≤ i → i ≤ k →
    r.length = B.setupCoins lam k (relSize n m R) →
    let P := eval4 p lam (relSize n m R) (clog2 (k + 1)) 0
    let o := B.setup lam k n m R i r
    o.1.length ≤ P ∧ o.2.length ≤ P ∧
      ∀ u w (ω : Bits), ω.length = B.proveCoins lam k (relSize n m R) → (B.prove o.1 u w ω).length ≤ P

end FourMsgQMA


