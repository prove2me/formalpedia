-- Prove2me | Definitions.Def_TightPQRepetition_Main_Reduction
-- name    : TightPQRepetition_Main_Reduction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T23:42:51.658291+00:00
-- url     : https://prove2.me/theorems/c89fd2ba-042a-477e-88d8-62d4b59a97ed
-- title:
--   Algorithm 1 and the hybrids $H_0,H_{1,1},H_{1,2},H_{1,3},H_{1,4},H_m$
-- statement:
--   Fix $\lambda$, a prover $B$ against $\widehat V^{k',t'}$ in the normal form of the proof of Theorem 5.1 (one unitary per round, a designated answer register $Z_\ell$ per round), and put $N=\lceil20k\lambda/\nu\rceil$, $\mu=\nu/10km$, $\delta=\mu^2/2N^2$, and rotation precision $2^{-\lambda}$.
--
--   The quantum state lives on $W\otimes R\otimes E\otimes O$: the wires of $B$, the coherent coins $R=R_1\cdots R_m$ of coordinate 1, its message registers $E=E_1\cdots E_m$, and an ancilla. $U_{{\rm Ver},\ell}$ applies the prover's unitary of round $\ell$, controlled on $E_\ell$ and the earlier answers; internal coordinates' messages come from $r_{\rm Ver}$ and those answers. $\Pi_{\rm Ver}$ projects onto exactly $t'-1$ accepting internal verifiers, and
--   $$\Pi_{{\rm Acc},{\rm rnd}}=U_{{\rm Ver},{\rm rnd}}^\dagger\cdots U_{{\rm Ver},m}^\dagger\,\Pi_{\rm Ver}\,U_{{\rm Ver},m}\cdots U_{{\rm Ver},{\rm rnd}}.$$
--   $|{\rm Enc}(q)_{\rm rnd}\rangle$ is the coherent state of the remaining rounds with $q$ encrypted in round rnd and zero plaintexts afterwards.
--
--   Algorithm 1 tries at most $N$ times to pass the measurement of $\Pi_{{\rm Acc},1}$ with a dummy $|{\rm Enc}(0)_1\rangle$, rotates back to the clean state and discards the registers; then in each round it appends $|{\rm Enc}(q)_{\rm rnd}\rangle$ for the real query, rotates, measures $\Pi_{{\rm Acc},{\rm rnd}}$, applies $U_{{\rm Ver},{\rm rnd}}$, measures the round's registers, rotates back to the dummy state of the next round, tests and discards it, and answers.
--
--   $H_0$ is a run of this algorithm against an external verifier, $H_{1,1}$ uses the real first query in the first step, $H_{1,2}$ keeps $R,E$ after a successful test, $H_{1,3}$ drops the test, and $H_{1,4}$ drops the two rotations of round 1. $H_m$ fixes $r_{{\rm Query},1}$, runs $B$ against $\widehat V^{k',t'}$ at most $N$ times, and takes the first transcript with exactly $t'-1$ other accepting coordinates, or aborts.
--
--   **Formalization Note** Each hybrid is a law on the classical output or $\bot$, computed by recursion over rounds on density matrices. The zero plaintext of each round has the length of the real query. A measured register is reset to $|0\rangle$ after its value is recorded. The source's $[k]$ in §5 are the $k'$ coordinates played by $B$; $k$ stays in $N$, $\mu$ and $\nu/10k$.
-- source:
--   Zvika Brakerski, Andrew Huang, Yael Tauman Kalai, Nicholas Spooner, STOC 2027 submission #158 (October 2026), SHA-256 269f233ccbc44af16ba1b9aceb41299c2242cca048f65729c5fd3451cb6cd0b8, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/158.pdf, Theorem 5.1 proof, Algorithms 1–5, printed pp. 20–32 / PDF pp. 22–34

import Mathlib
import Definitions.Def_TightPQRepetition_Main_Jordan
import Definitions.Def_TightPQRepetition_Main_Preprocess

namespace TightPQRepetition.Main

/-!
Brakerski, Huang, Kalai, Spooner, STOC 2027 submission #158, proof of Theorem 5.1 (PDF pp. 22–34):
Algorithm 1 run against the external verifier, the hybrids `H₀`, `H₁,₁`, `H₁,₂`, `H₁,₃`, `H₁,₄`, and
`H_m`, at one security parameter.

Rounds are numbered from `0` (the source's round `rnd` is round `rnd - 1` here) and so are the
coordinates (the source's coordinate `1`, embedded with the external verifier, is coordinate `0`).
The prover plays `V̂^{k',t'}`; `k` stays in `N`, `μ` and `ν/(10k)`.

Each hybrid is computed as an explicit law on its classical output. The quantum state of a run is
a density matrix on `W ⊗ R ⊗ E ⊗ O`: `W` the wires of `B`, `R = R₀ ⋯ R_{m-1}` the coherent coins of
coordinate `0`, `E = E₀ ⋯ E_{m-1}` the registers of its messages, and `O` the ancilla (the second
factor `Fin 2`). A measured register is reset to `0` after its value is recorded, and a discarded
register is traced out, so the unused `R_ℓ`, `E_ℓ` are always `|0⟩`.
-/

open QAlgorithms Matrix
open scoped ComplexConjugate Classical

/-- `B` in the form assumed in the proof of Theorem 5.1 (PDF p. 22): no tape, a trivial controller,
one round per protocol round, and a designated answer register `Z_j` per round, disjoint from the
others, that no other round reads or writes; `U_j(q̄)` then acts on `I` and `Z_j` only. -/
def Strategy.IsNormalForm (B : Strategy) (m : ℕ) : Prop :=
  B.tape = 0 ∧ B.steps.length = m ∧
    (∀ j v, B.toCore j v = (unpack v).getLastD []) ∧
    (∀ j v, B.toVerifier j v = (unpack v).getLastD []) ∧
    ∀ j j', j < m → j' < m → j ≠ j' → ∀ a ∈ (B.stepAt j').outW,
      a ∉ (B.stepAt j).outW ∧ a ∉ (B.stepAt j).inW ∧
        ∀ g ∈ (B.stepAt j).circ, ∀ i, g.wires i ≠ a

/-- The parameters of Algorithm 1 at one security parameter. -/
structure RedCtx where
  /-- The encryption scheme. -/
  E : EncScheme
  /-- The verifier of the underlying protocol. -/
  V : Verifier
  /-- The prover against `V̂^{k',t'}`. -/
  B : Strategy
  /-- The security parameter. -/
  lam : ℕ
  /-- The original number of repetitions. -/
  k : ℕ
  /-- The number of repetitions of the verifier played by `B`. -/
  k' : ℕ
  /-- The threshold of the verifier played by `B`. -/
  t' : ℕ
  /-- The advantage. -/
  ν : ℝ
  /-- The rotation circuits of Theorem 3.9. -/
  prog : ℝ → ℝ → RotationProgram

namespace RedCtx

variable (x : RedCtx)

/-- The number of rounds. -/
def m : ℕ := x.V.rounds x.lam

/-- The encrypted verifier. -/
def hat : Verifier := hatV x.E x.V

/-- `N = ⌈20kλ/ν⌉`, the number of attempts and of copies of `B`'s state. -/
noncomputable def N : ℕ := ⌈20 * (x.k : ℝ) * x.lam / x.ν⌉₊

/-- The precision `2^{-λ}` of the rotations, written `ε` in Algorithm 1. -/
noncomputable def epsQ : ℝ := (1 / 2) ^ x.lam

/-- `μ = ν/(10km)`. -/
noncomputable def mu : ℝ := x.ν / (10 * x.k * x.m)

/-- `δ = μ²/(2N²)`. -/
noncomputable def delta : ℝ := x.mu ^ 2 / (2 * (x.N : ℝ) ^ 2)

/-- The coins register `R_ℓ` has this many qubits. -/
def rLen (ℓ : ℕ) : ℕ := blockLen x.E x.V x.lam ℓ

/-- The message register `E_ℓ` has this many qubits. -/
def eLen (ℓ : ℕ) : ℕ := x.hat.qLen x.lam ℓ

/-- Basis labels of `W`. -/
abbrev Wq := Qubits x.B.n

/-- Basis labels of `R`. -/
abbrev Rr := (ℓ : Fin x.m) → Qubits (x.rLen ℓ)

/-- Basis labels of `E`. -/
abbrev Ee := (ℓ : Fin x.m) → Qubits (x.eLen ℓ)

/-- Measured answers. -/
abbrev Zs := (ℓ : Fin x.m) → Qubits (x.B.outLen ℓ)

/-- Basis labels of `R ⊗ E`. -/
abbrev RE := x.Rr × x.Ee

/-- Basis labels of `W ⊗ R ⊗ E`. -/
abbrev Sp := x.Wq × x.RE

/-- Basis labels of `W ⊗ R ⊗ E ⊗ O`. -/
abbrev Tp := x.Sp × Fin 2

/-- Basis labels of `W ⊗ O`. -/
abbrev WO := x.Wq × Fin 2

/-- The classical randomness `r_Ver` of the coordinates other than the first. -/
abbrev RVer := Fin (x.k' - 1) → Qubits (x.hat.coins x.lam)

/-- The classical output of a hybrid: `r_Query,1` of the external verifier, `r_Ver`, the measured
coins and messages of coordinate `0`, and the measured joint answers. Together these determine the
transcript `τ_m`. -/
abbrev Out := Qubits (x.V.coins x.lam) × x.RVer × x.Rr × x.Ee × x.Zs

/-- A subnormalized law on the output or `⊥` (`none`). -/
abbrev Law := Option x.Out → ℝ

/-- The joint answer of round `ℓ` held in `Z_ℓ`. -/
def zAt (w : x.Wq) (ℓ : ℕ) : Bits := (x.B.stepAt ℓ).outW.map w

/-- The message of the internal verifier of coordinate `i + 1` in round `ℓ`, given its coins and
the answers held in `Z_0 ⋯ Z_{ℓ-1}`. -/
def internalMsg (rv : x.RVer) (i : Fin (x.k' - 1)) (ℓ : ℕ) (w : x.Wq) : Bits :=
  x.hat.query x.lam (toBits (rv i)) ℓ ((List.range ℓ).map fun a => coordMsg (i + 1) (x.zAt w a))

/-- The joint query of round `ℓ`, with `e` the message of coordinate `0`. -/
def fullQuery (rv : x.RVer) (e : Bits) (ℓ : ℕ) (w : x.Wq) : Bits :=
  pack (e :: List.ofFn fun i => x.internalMsg rv i ℓ w)

/-- `U_{Ver,ℓ}`: controlled on `E_ℓ` and `Z_0 ⋯ Z_{ℓ-1}`, apply the prover's unitary of round `ℓ`
for the resulting joint query. -/
noncomputable def uVer (rv : x.RVer) (ℓ : Fin x.m) : Matrix x.Sp x.Sp ℂ :=
  Matrix.of fun s s' =>
    if s.2 = s'.2 then
      (x.B.stepAt ℓ).op (x.fullQuery rv (toBits (s'.2.2 ℓ)) ℓ s'.1) s.1 s'.1
    else 0

/-- The transcript of the internal verifier of coordinate `i + 1`, read from `Z`. -/
def internalTranscript (rv : x.RVer) (i : Fin (x.k' - 1)) (w : x.Wq) : List (Bits × Bits) :=
  (List.range x.m).map fun ℓ => (x.internalMsg rv i ℓ w, coordMsg (i + 1) (x.zAt w ℓ))

/-- `∑_{i≠1} V_i(τ_i, r_{Ver,i})`. -/
def otherAccepts (rv : x.RVer) (w : x.Wq) : ℕ :=
  (List.finRange (x.k' - 1)).countP fun i =>
    x.hat.verdict x.lam (toBits (rv i)) (x.internalTranscript rv i w)

/-- `Π_Ver`, the projection on `Z` values with exactly `t' - 1` accepting internal verifiers (no
value when `t' = 0`). -/
noncomputable def piVer (rv : x.RVer) : Matrix x.Sp x.Sp ℂ :=
  Matrix.diagonal fun s => if (x.otherAccepts rv s.1 : ℤ) = (x.t' : ℤ) - 1 then 1 else 0

/-- `U_{Ver,m} ⋯ U_{Ver,rnd}`. -/
noncomputable def uChain (rv : x.RVer) (rnd : ℕ) : Matrix x.Sp x.Sp ℂ :=
  (((List.finRange x.m).filter fun ℓ : Fin x.m => rnd ≤ (ℓ : ℕ)).map (x.uVer rv)).reverse.prod

/-- `Π_{Acc,rnd} = U_{Ver,rnd}† ⋯ U_{Ver,m}† Π_Ver U_{Ver,m} ⋯ U_{Ver,rnd}`. -/
noncomputable def piAcc (rv : x.RVer) (rnd : ℕ) : Matrix x.Sp x.Sp ℂ :=
  (x.uChain rv rnd)ᴴ * x.piVer rv * x.uChain rv rnd

/-- The secret key derived from the block `b`. -/
def skOf (b : Bits) : Bits := (x.E.gen x.lam (genPart x.E x.lam b)).2

/-- The message that `E_ℓ` holds in `|Enc(head)_rnd⟩` for the coins `r`: `head` in round `rnd` and
the zero plaintext later; the secret key encrypted in round `rnd` is `prev`, and in later rounds the
previous round's key, computed from `R`. -/
def msgAt (rnd : Fin x.m) (head prev : Bits) (r : x.Rr) (ℓ : Fin x.m) : Bits :=
  hatMessage x.E x.V x.lam ℓ (toBits (r ℓ))
    (if ℓ = rnd then head else zeros (x.V.qLen x.lam ℓ))
    (if ℓ = rnd then prev else
      if h : (ℓ : ℕ) - 1 < x.m then x.skOf (toBits (r ⟨(ℓ : ℕ) - 1, h⟩)) else [])

/-- The state `|Enc(head)_rnd⟩` on `R_rnd ⋯ R_m E_rnd ⋯ E_m` (steps 2(b), 3(b)), with the registers
of earlier rounds in `|0⟩`. -/
noncomputable def encState (rnd : Fin x.m) (head prev : Bits) : EuclideanSpace ℂ x.RE :=
  WithLp.toLp 2 fun p =>
    if (∀ ℓ : Fin x.m, ℓ < rnd → p.1 ℓ = (fun _ => false) ∧ p.2 ℓ = (fun _ => false)) ∧
        (∀ ℓ : Fin x.m, rnd ≤ ℓ → toBits (p.2 ℓ) = x.msgAt rnd head prev p.1 ℓ) then
      ((((Real.sqrt 2) ^ (∑ ℓ : Fin x.m, if rnd ≤ ℓ then x.rLen ℓ else 0))⁻¹ : ℝ) : ℂ)
    else 0

/-- The dummy `|Enc(0)_rnd⟩`, with the zero plaintext of the length of the real query. -/
noncomputable def encZero (rnd : Fin x.m) (prev : Bits) : EuclideanSpace ℂ x.RE :=
  x.encState rnd (zeros (x.V.qLen x.lam rnd)) prev

/-- `|φ⟩⟨φ|_{RE} ⊗ I_W`. -/
noncomputable def projRE (φ : EuclideanSpace ℂ x.RE) : Matrix x.Sp x.Sp ℂ :=
  Matrix.of fun s s' => if s.1 = s'.1 then φ s.2 * conj (φ s'.2) else 0

/-- An operator on `W R E`, tensored with the identity on `O`. -/
def lift (A : Matrix x.Sp x.Sp ℂ) : Matrix x.Tp x.Tp ℂ :=
  Matrix.of fun p q => if p.2 = q.2 then A p.1 q.1 else 0

/-- `C_{ε,δ}^{Π_B,Π_A}`, on `W R E O`. -/
noncomputable def rot (PB PA : Matrix x.Sp x.Sp ℂ) : Matrix x.Tp x.Tp ℂ :=
  Matrix.of fun p q => programOp PA PB (x.prog x.epsQ x.delta) p.2 q.2 p.1 q.1

/-- `ρ ↦ A ρ A†`. -/
noncomputable def conjOp {α : Type} [Fintype α] (A ρ : Matrix α α ℂ) : Matrix α α ℂ :=
  A * ρ * Aᴴ

/-- The total weight of a subnormalized density matrix. -/
noncomputable def weight {α : Type} [Fintype α] (ρ : Matrix α α ℂ) : ℝ := ρ.trace.re

/-- `σ ⊗ |φ⟩⟨φ|_{RE}`. -/
noncomputable def appendRE (σ : Matrix x.WO x.WO ℂ) (φ : EuclideanSpace ℂ x.RE) :
    Matrix x.Tp x.Tp ℂ :=
  Matrix.of fun p q => σ (p.1.1, p.2) (q.1.1, q.2) * φ p.1.2 * conj (φ q.1.2)

/-- Discarding `R` and `E`. -/
noncomputable def discardRE (ρ : Matrix x.Tp x.Tp ℂ) : Matrix x.WO x.WO ℂ :=
  Matrix.of fun a b => ∑ y : x.RE, ρ ((a.1, y), a.2) ((b.1, y), b.2)

/-- A fresh copy of `|ψ⟩`, with `O` in `|0⟩`. -/
noncomputable def freshCopy : Matrix x.WO x.WO ℂ :=
  Matrix.of fun a b =>
    if a.2 = 0 ∧ b.2 = 0 then x.B.init a.1 * conj (x.B.init b.1) else 0

/-- The measurement of `R_rnd`, `E_rnd` and `Z_rnd` with outcome `(a, b, c)`, after which `R_rnd`
and `E_rnd` are reset to `|0⟩`. -/
noncomputable def measOp (rnd : Fin x.m) (a : Qubits (x.rLen rnd)) (b : Qubits (x.eLen rnd))
    (c : Qubits (x.B.outLen rnd)) : Matrix x.Sp x.Sp ℂ :=
  Matrix.of fun s' s =>
    if s.2.1 rnd = a ∧ s.2.2 rnd = b ∧ x.zAt s.1 rnd = toBits c ∧
        s' = (s.1, (Function.update s.2.1 rnd (fun _ => false),
          Function.update s.2.2 rnd (fun _ => false))) then 1 else 0

/-- The output `⊥` with weight `w`. -/
noncomputable def abortLaw (w : ℝ) : x.Law := Pi.single none w

/-- The partial output: the measured coins, messages and answers so far. -/
abbrev Partial := x.Rr × x.Ee × x.Zs

/-- The empty partial output. -/
def noRecord : x.Partial := (fun _ _ => false, fun _ _ => false, fun _ _ => false)

/-- Steps 3(d)–(h) of round `rnd`, and all later rounds, from the state `ρ` just after 3(c). `rq` is
`r_Query,1`, `ans` the answers already sent to the external verifier, `f` a bound on the rounds left.
Step 3(d): measure `Π_{Acc,rnd}`, apply `U_{Ver,rnd}`, measure `R_rnd, E_rnd, Z_rnd`. Unless this is
the last round: 3(e) rotate towards `|Enc(0)_{rnd+1}⟩`, 3(f)–(g) test it and discard `R`, `E`,
aborting if the test fails. Step 3(h): decrypt the answer of coordinate `0` and send it. Then, in the
next round, 3(a) receive the query, 3(b) append `|Enc(q)_{rnd+1}⟩`, 3(c) rotate back. -/
noncomputable def tail (rq : Qubits (x.V.coins x.lam)) (rv : x.RVer) :
    ℕ → (rnd : Fin x.m) → x.Partial → List Bits → Matrix x.Tp x.Tp ℂ → x.Law
  | 0, _, _, _, _ => 0
  | f + 1, rnd, acc, ans, ρ =>
    x.abortLaw (weight (conjOp (1 - x.lift (x.piAcc rv rnd)) ρ)) +
    ∑ a : Qubits (x.rLen rnd), ∑ b : Qubits (x.eLen rnd), ∑ c : Qubits (x.B.outLen rnd),
      let ρc := conjOp (x.lift (x.measOp rnd a b c))
        (conjOp (x.lift (x.uVer rv rnd)) (conjOp (x.lift (x.piAcc rv rnd)) ρ))
      let acc' : x.Partial := (Function.update acc.1 rnd a, Function.update acc.2.1 rnd b,
        Function.update acc.2.2 rnd c)
      let sk := x.skOf (toBits a)
      let ans' := ans ++ [x.E.dec x.lam sk (coordMsg 0 (toBits c))]
      if h : (rnd : ℕ) + 1 < x.m then
        let nxt : Fin x.m := ⟨(rnd : ℕ) + 1, h⟩
        let ρd := conjOp (x.rot (x.projRE (x.encZero nxt sk)) (x.piAcc rv nxt)) ρc
        let Pl := x.lift (x.projRE (x.encZero nxt sk))
        let φ := x.encState nxt (x.V.query x.lam (toBits rq) nxt ans') sk
        x.abortLaw (weight (conjOp (1 - Pl) ρd)) +
          tail rq rv f nxt acc' ans'
            (conjOp (x.rot (x.projRE φ) (x.piAcc rv nxt))ᴴ (x.appendRE (x.discardRE (conjOp Pl ρd)) φ))
      else
        Pi.single (some (rq, rv, acc'.1, acc'.2.1, acc'.2.2)) (weight ρc)

/-- The hybrids of the first round. -/
inductive Stage
  | h0
  | h11
  | h12
  | h13
  | h14
  deriving DecidableEq

/-- Steps 2(d)–(f) and step 3(b)–(c) of the first round, once `Π_{Acc,1}` has accepted, in each
hybrid. In `H₀` the state used in step 2 is the dummy `|Enc(0)₁⟩`, in the others `|Enc(q₁)₁⟩`.
`H₁,₂` keeps `R`, `E` after a successful test, `H₁,₃` drops the test, `H₁,₄` drops the two rotations
as well. `ρ` is the state after the accepting measurement of step 2(c). -/
noncomputable def afterAccept (st : Stage) (r0 : Fin x.m) (rq : Qubits (x.V.coins x.lam))
    (rv : x.RVer) (ρ : Matrix x.Tp x.Tp ℂ) : x.Law :=
  let φq := x.encState r0 (x.V.query x.lam (toBits rq) r0 []) []
  let φp := if st = .h0 then x.encZero r0 [] else φq
  let PA := x.piAcc rv r0
  let rotP := x.rot (x.projRE φp) PA
  let rotQ := x.rot (x.projRE φq) PA
  let Pp := x.lift (x.projRE φp)
  let cont := x.tail rq rv x.m r0 x.noRecord []
  match st with
  | .h14 => cont ρ
  | .h13 => cont (conjOp rotQᴴ (conjOp rotQ ρ))
  | .h12 =>
    x.abortLaw (weight (conjOp (1 - Pp) (conjOp rotP ρ))) +
      cont (conjOp rotQᴴ (conjOp Pp (conjOp rotP ρ)))
  | _ =>
    x.abortLaw (weight (conjOp (1 - Pp) (conjOp rotP ρ))) +
      cont (conjOp rotQᴴ (x.appendRE (x.discardRE (conjOp Pp (conjOp rotP ρ))) φq))

/-- The expectation over `r_Ver`. -/
noncomputable def avgVer (g : x.RVer → x.Law) : x.Law :=
  ((Fintype.card x.RVer : ℝ))⁻¹ • ∑ rv : x.RVer, g rv

/-- Step 2, with `s` attempts left: sample `r_Ver`, append a fresh copy of `|ψ⟩` and `|Enc(·)₁⟩`,
measure `Π_{Acc,1}`; on outcome `0` go to the next attempt, and abort when no attempt is left. -/
noncomputable def attempts (st : Stage) (r0 : Fin x.m) (rq : Qubits (x.V.coins x.lam)) :
    ℕ → x.Law
  | 0 => x.abortLaw 1
  | s + 1 => x.avgVer fun rv =>
    let φ := if st = .h0 then x.encZero r0 []
      else x.encState r0 (x.V.query x.lam (toBits rq) r0 []) []
    let ρ₀ := x.appendRE x.freshCopy φ
    let P := x.lift (x.piAcc rv r0)
    weight (conjOp (1 - P) ρ₀) • attempts st r0 rq s + x.afterAccept st r0 rq rv (conjOp P ρ₀)

/-- The law of the output of a hybrid: `r_Query,1` is uniform, as sampled by the external verifier,
and `H₀` is a random execution of Algorithm 1 with it. Defined when there is at least one round. -/
noncomputable def hybrid (st : Stage) (r0 : Fin x.m) : x.Law :=
  ((2 : ℝ) ^ x.V.coins x.lam)⁻¹ • ∑ rq : Qubits (x.V.coins x.lam), x.attempts st r0 rq x.N

/-- The trace distance of two classical laws. -/
noncomputable def lawTD (p q : x.Law) : ℝ := (1 / 2) * ∑ o, |p o - q o|

/-- The verifier played by `B`. -/
def par : Verifier := hatPar x.E x.V x.k' x.t'

/-- In one run of `B` against `V̂^{k',t'}`, conditionally on `r_Query,1 = rq`: exactly `t' - 1` of the
other coordinates accept. -/
noncomputable def hitProb (rq : Bits) : ℝ :=
  (2 : ℝ) ^ x.V.coins x.lam * x.B.eventProb x.par x.lam fun r τ =>
    hatQueryCoins x.V x.lam r = rq ∧
      (x.hat.acceptCount x.lam (List.range x.k').tail r τ : ℤ) = (x.t' : ℤ) - 1

/-- The same, and moreover the first coordinate accepts. -/
noncomputable def winProb (rq : Bits) : ℝ :=
  (2 : ℝ) ^ x.V.coins x.lam * x.B.eventProb x.par x.lam fun r τ =>
    hatQueryCoins x.V x.lam r = rq ∧
      (x.hat.acceptCount x.lam (List.range x.k').tail r τ : ℤ) = (x.t' : ℤ) - 1 ∧
      x.hat.coordVerdict x.lam 0 r τ = true

/-- `H_m` (PDF p. 34), with `s` attempts left: run `B` against `V̂^{k',t'}` with `rq` hardwired as
the query randomness of the first subverifier; stop at the first transcript with exactly `t' - 1`
accepting other coordinates, otherwise try again. The value is the probability that a transcript
is output and the first subverifier accepts it. -/
noncomputable def hmSuccess (rq : Bits) : ℕ → ℝ
  | 0 => 0
  | s + 1 => x.winProb rq + (1 - x.hitProb rq) * hmSuccess rq s

/-- `Pr_{τ←H_m}[V(τ₁, r_{Ver,1}) = 1]`. -/
noncomputable def hmAccept : ℝ := avgCoins (x.V.coins x.lam) fun rq => x.hmSuccess rq x.N

/-- The standing setting of the hybrids at one security parameter (PDF pp. 22, 25): efficient
scheme and verifier, at least one round, `B` a valid strategy in the form of the proof of Theorem
5.1, `1 ≤ k' ≤ k`, `t' ≤ k'`, `0 < ν ≤ k`, and rotation circuits as in Theorem 3.9. -/
structure Standing (c : ℝ) : Prop where
  scheme : x.E.IsEfficient
  verifier : x.V.IsEfficient
  rounds : 0 < x.m
  valid : x.B.Valid
  normal : x.B.IsNormalForm x.m
  one_le : 1 ≤ x.k'
  le_k : x.k' ≤ x.k
  threshold : x.t' ≤ x.k'
  nu_pos : 0 < x.ν
  /-- The source success inequality with k′ > 1 implies this bound. -/
  nu_le : x.ν ≤ (x.k : ℝ)
  rotation : IsRotationFamily c x.prog

end RedCtx

/-- The context of Algorithm 1 at security parameter `lam`, for families of parameters. -/
def redCtx (E : EncScheme) (V : Verifier) (B : ℕ → Strategy) (k k' t' : ℕ → ℕ) (ν : ℕ → ℝ)
    (prog : ℝ → ℝ → RotationProgram) (lam : ℕ) : RedCtx :=
  ⟨E, V, B lam, lam, k lam, k' lam, t' lam, ν lam, prog⟩

/-- The setting of the hybrids as families: `B` is QPT, `k`, `k'`, `t'` are polynomially bounded,
`ν` is an inverse polynomial, and the setting holds at every security parameter. -/
def IsHybridFamily (E : EncScheme) (V : Verifier) (B : ℕ → Strategy) (k k' t' : ℕ → ℕ) (ν : ℕ → ℝ)
    (prog : ℝ → ℝ → RotationProgram) (c : ℝ) : Prop :=
  IsQPT B ∧ PolyBound k ∧ PolyBound k' ∧ PolyBound t' ∧ InversePoly ν ∧
    ∀ lam, (redCtx E V B k k' t' ν prog lam).Standing c

end TightPQRepetition.Main


