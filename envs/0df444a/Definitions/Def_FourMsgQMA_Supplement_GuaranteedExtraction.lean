-- Prove2me | Definitions.Def_FourMsgQMA_Supplement_GuaranteedExtraction
-- name    : FourMsgQMA_Supplement_GuaranteedExtraction
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:21:30.372207+00:00
-- url     : https://prove2.me/theorems/c96326e2-6868-4628-a721-d0d46951df34
-- title:
--   Guaranteed extraction for Kilian's argument (Def 3.25): coherent access and expected running time
-- statement:
--   **Guaranteed extraction** (Definition 3.25, following [LMS22, Definition 8.1]) is defined through the experiment $\mathrm{GE}_A$ for a cheating prover $A$:
--
--   1. sample $vk\leftarrow\mathrm{Setup}$ and run $A$'s first stage on $vk$ and its advice, obtaining classical $(u,\beta)$ and a residual state $\rho$;
--   2. prepare $2^{-r/2}\sum_q|q\rangle$, run $A$'s response circuit coherently, compute $B=\mathrm{Verify}(vk,u,\beta,q,a)$ and measure only $B$; let $\rho_B$ be the remaining state;
--   3. if $B=0$ output $(u,0,\perp)$; if $B=1$ run $w\leftarrow\mathrm{FindWitness}(vk,u,\beta;\rho_B)$ and output $(u,1,w)$.
--
--   The procedure has coherent access to the response circuit $U$ and its inverse $U^\dagger$ (measurement and coin registers retained) and works on the one residual state $\rho_B$. Guaranteed extraction requires a polynomial $P$ such that for every QPT $A$
--   $$
--   \Pr\big[B=1\wedge R(u,w)\ne1\big]\le\mathrm{negl}(\lambda),\qquad \mathbb E[\mathrm{Time}_{\mathrm{GE}}]\le P(\lambda,M,T_A),
--   $$
--   both over the whole experiment (key generation, the adaptive $(u,\beta)$, the measurement of $B$ and every internal outcome), not conditionally on $(vk,u,\beta)$ or on $B=1$.
--
--   **Formalization Note** Pinned-down version (operator request). The prover is an `IsQPT` strategy (round 0: $vk\mapsto(u,\beta)$, round 1: $q\mapsto a$). $U$ is the unitary dilation of round 1: controlled on a seed register, the round-1 unitary on the core, then the answer XORed into an answer register of $2L_a+1$ wires ($L_a$ a polynomial bound on answer lengths). The procedure is one uniformly generated sequence of steps of gates $H,S,T,X,\mathrm{CNOT}$ on its own register and calls of $U$, $U^\dagger$, with a halt wire measured after each step. Time counts $1$ per step and per gate and $T_A=|A|+L_a$ per call; the expectation is in $[0,\infty]$.
-- source:
--   Goyal, Koppula, Four-Message Arguments for NP ∘ batchQMA and Six-Message Arguments for QMA from LWE, STOC 2027 submission (sha256 6c523d45…), Definition 3.25, p.23 (PDF 25); §3.5, p.14 (PDF 16)

import Mathlib
import Definitions.Def_FourMsgQMA_Supplement_Kilian
import Definitions.Def_FourMsgQMA_Core

namespace FourMsgQMA

/-!
Goyal, Koppula, STOC 2027 submission (sha256 6c523d45…), Definition 3.25 (p.23, PDF 25) and §3.5
(p.14, PDF 16: "A quantum reduction may call a cheating prover's continuation circuits and their
inverses. It uses a unitary dilation that records all random coins, measurements, discarded
registers, and halting records."): guaranteed extraction for Kilian's argument, the experiment
`GE_A` with a witness-finding procedure that has coherent access to the prover's response circuit
and its inverse, and its expected running time.

Pinned-down version (operator request).

* The cheating prover is a published `TightPQRepetition.Main.Strategy`: its round 0 receives `vk`
  and answers `pack [u, β]`, its round 1 receives the seed `q` and answers `a`. Its random tape is
  sampled once, classically.
* The **response circuit** `U` is the unitary dilation of round 1 on the prover's core and two
  registers: the seed register `Q` (`r` wires) and the answer register `A` (`2 L_a + 1` wires,
  `L_a` a bound on the length of round-1 answers): controlled on the content `q` of `Q`, it applies
  the round-1 unitary of the core for the incoming string `q` and then XORs into `A` the
  self-delimiting encoding of the answer computed from `q` and the values of the round's measured
  wires. Measurement records stay on the core's wires.
* A **witness-finding procedure** acts on its own register: `Q`, then `A`, then a workspace of fresh
  `|0⟩` wires. Step `t` is a list of gates `H, S, T, X, CNOT` on that register and calls of `U` or
  `U†`; after each step it measures a halt wire; on halting it measures its output wires, giving
  `w`. It touches the prover's core only through `U` and `U†` (black-box access), and receives
  `(vk, u, β)` and the register sizes classically. Its steps are generated in polynomial time from
  `(1^λ, vk, u, β, r, L, 1^t)`.
* **Time**: a step costs `1` plus one per gate plus `T_A = |A| + L_a` per call of `U` or `U†`
  (`|A|` the size of the strategy). `Time` is the total cost of the steps run; the remaining stages
  of `GE_A` (setup, the prover's first stage, one run of `U`, the measurement of `B`) have a fixed
  cost polynomial in `(λ, M, T_A)`.
-/

namespace Supplement

open QAlgorithms QAlgorithms.Complexity TightPQRepetition.Main

/-- An instruction of a witness-finding procedure, on its own register (wires numbered from `0`). -/
inductive XOp where
  | h (i : ℕ)
  | s (i : ℕ)
  | t (i : ℕ)
  | x (i : ℕ)
  | cnot (i j : ℕ)
  /-- One call of the response circuit `U`. -/
  | call
  /-- One call of its inverse `U†`. -/
  | callInv

/-- The encoding of an instruction. -/
def XOp.encode : XOp → Str
  | .h i => encNat 0 ++ encNat i
  | .s i => encNat 1 ++ encNat i
  | .t i => encNat 2 ++ encNat i
  | .x i => encNat 3 ++ encNat i
  | .cnot i j => encNat 4 ++ encNat i ++ encNat j
  | .call => encNat 5
  | .callInv => encNat 6

/-- A witness-finding procedure: from `λ` and its classical input `inp`, the width of its
workspace, its step `t`, its halt wire and its output wires. -/
structure Extractor where
  /-- The number of workspace wires. -/
  work : ℕ → Bits → ℕ
  /-- The instructions of step `t`. -/
  step : ℕ → Bits → ℕ → List XOp
  /-- The halt wire. -/
  halt : ℕ → Bits → ℕ
  /-- The output wires. -/
  out : ℕ → Bits → List ℕ

/-- A uniform procedure: its description at step `t` is computed in polynomial time from
`(1^λ, inp, 1^t)`. -/
def Extractor.IsUniform (X : Extractor) : Prop :=
  ∃ g : Str → Str, PolyTimeComputable g ∧ ∀ lam inp t,
    g (pack [unary lam, inp, unary t]) =
      pack [unary (X.work lam inp), encStr ((X.step lam inp t).map XOp.encode), unary (X.halt lam inp),
        encStr ((X.out lam inp).map encNat)]

/-- Joint (unnormalized) states of the prover's `n`-qubit core and an `E`-qubit register. -/
abbrev JState (n E : ℕ) := Qubits n × Qubits E → ℂ

/-- The squared norm, the probability weight of a subnormalized state. -/
noncomputable def JState.weight {n E : ℕ} (ψ : JState n E) : ℝ := ∑ p, ‖ψ p‖ ^ 2

/-- A one- or two-qubit gate on the `E`-register (out-of-range wires: no effect). -/
noncomputable def XOp.gateE (E : ℕ) : XOp → (QState E → QState E)
  | .h i => if hi : i < E then Instr.apply (.h ⟨i, hi⟩) else id
  | .s i => if hi : i < E then Instr.apply (.s ⟨i, hi⟩) else id
  | .t i => if hi : i < E then Instr.apply (.t ⟨i, hi⟩) else id
  | .x i => if hi : i < E then Instr.apply (.x ⟨i, hi⟩) else id
  | .cnot i j => if h : i < E ∧ j < E ∧ i ≠ j then
      Instr.apply (.cnot ⟨i, h.1⟩ ⟨j, h.2.1⟩ (fun e => h.2.2 (congrArg Fin.val e))) else id
  | .call => id
  | .callInv => id

/-- A map on the `E`-register, applied to a joint state. -/
noncomputable def liftE {n E : ℕ} (f : QState E → QState E) (ψ : JState n E) : JState n E :=
  fun p => f (fun e => ψ (p.1, e)) p.2

/-- The content of the first `r` wires (the seed register `Q`). -/
def seedOf {E : ℕ} (r : ℕ) (e : Qubits E) : Bits := (List.range r).map (wireAt e)

/-- The values of a list of wires. -/
def valsOf {E : ℕ} (w : List ℕ) (e : Qubits E) : Bits := w.map (wireAt e)

/-- `e` with the string `a` XORed into the wires `r, …, r + aw − 1` (the answer register). -/
def xorAns {E : ℕ} (r aw : ℕ) (a : Bits) (e : Qubits E) : Qubits E :=
  fun i => if r ≤ i.val ∧ i.val < r + aw then xor (e i) (a.getD (i.val - r) false) else e i

/-- The prover's history after round 0 with incoming `vk` and core outcome `c₀`. -/
def hist0 (vk c0 : Bits) : List (Bits × Bits) := [(vk, c0)]

/-- The prover's round-1 answer on seed `q` with core-outcome string `c`. -/
def ans1 (S : Strategy) (u vk c0 q c : Bits) : Bits :=
  S.toVerifier 1 (pack (controllerView u (hist0 vk c0 ++ [(q, c)])))

/-- The string written into the core in round 1 on seed `q`. -/
def in1 (S : Strategy) (u vk c0 q : Bits) : Bits :=
  S.toCore 1 (pack (controllerView u (hist0 vk c0) ++ [q]))

/-- The values of the wires measured in round 1, read from a core basis state. -/
def outVals (S : Strategy) (z : Qubits S.n) : Bits := (S.stepAt 1).outW.map z

/-- The response circuit `U` on the joint state (core, `Q ‖ A ‖ workspace`): controlled on the
seed `q`, the round-1 unitary of the core, then the answer XORed into `A` (`aw` wires) as
`padTo aw (packOne a)`. -/
noncomputable def respU (S : Strategy) (u vk c0 : Bits) (E r aw : ℕ) (ψ : JState S.n E) :
    JState S.n E :=
  fun p =>
    let e := xorAns r aw (padTo aw (packOne (ans1 S u vk c0 (seedOf r p.2) (outVals S p.1)))) p.2
    ∑ z : Qubits S.n, (S.stepAt 1).op (in1 S u vk c0 (seedOf r e)) p.1 z * ψ (z, e)

/-- The inverse `U†` of the response circuit. -/
noncomputable def respUInv (S : Strategy) (u vk c0 : Bits) (E r aw : ℕ) (ψ : JState S.n E) :
    JState S.n E :=
  fun p =>
    ∑ z : Qubits S.n, star ((S.stepAt 1).op (in1 S u vk c0 (seedOf r p.2)) z p.1) *
      ψ (z, xorAns r aw (padTo aw (packOne (ans1 S u vk c0 (seedOf r p.2) (outVals S z)))) p.2)

/-- One instruction of the procedure on the joint state. -/
noncomputable def XOp.run (S : Strategy) (u vk c0 : Bits) (E r aw : ℕ) :
    XOp → JState S.n E → JState S.n E
  | .call => respU S u vk c0 E r aw
  | .callInv => respUInv S u vk c0 E r aw
  | o => liftE (o.gateE E)

/-- The cost of an instruction: `1` for a gate, `T_A` for a call. -/
def XOp.cost (TA : ℕ) : XOp → ℕ
  | .call => TA
  | .callInv => TA
  | _ => 1

/-- The projector onto the halt wire having value `v`. -/
def haltProj {n E : ℕ} (hw : ℕ) (v : Bool) (ψ : JState n E) : JState n E :=
  fun p => if wireAt p.2 hw = v then ψ p else 0

/-- The data of the experiment `GE_A` once the setup coins, the prover tape `u` and the round-0
outcome `c₀` are fixed: `vk`, the classical `(u, β)` the prover outputs, the seed length `r`, the
answer width `aw = 2 L_a + 1`, the procedure's classical input `(vk, u, β, r, L_a)`, the size `E`
of the procedure's register, and the state `ρ_B` of the branch `B = 1` on the joint register: the
core state after round 0, the uniform superposition `2^{-r/2} ∑_q |q⟩` in `Q` and `|0⟩` on the
other wires of the register, one application of `U`, and the projection onto
`B = Verify(vk, u, β, q, a) = 1`. Only `B` is measured. -/
structure GEBranch (n : ℕ) where
  /-- `vk`. -/
  vk : Bits
  /-- The round-0 core outcome. -/
  c0 : Bits
  /-- The instance `u` chosen by the prover. -/
  inst : Bits
  /-- The seed length `r`. -/
  r : ℕ
  /-- The answer-register width. -/
  aw : ℕ
  /-- The procedure's classical input. -/
  inp : Bits
  /-- The size `E` of the procedure's register. -/
  E : ℕ
  /-- `ρ_B` for `B = 1`, subnormalized. -/
  state : JState n E

/-- `GEBranch` for setup coins `rv`, prover tape `u` and round-0 outcome `c₀`. -/
noncomputable def geBranch (K : Kilian) (X : Extractor) (lam : ℕ) (S : Strategy) (La : ℕ)
    (rv u : Bits) (c0 : Qubits (S.outLen 0)) : GEBranch S.n :=
  let vk := K.setup lam rv
  let x0 := S.toCore 0 (pack (controllerView u [] ++ [vk]))
  let ψ := act (roundOp S 0 x0 (toBits c0)) S.init
  let a0 := unpack (S.toVerifier 0 (pack (controllerView u (hist0 vk (toBits c0)))))
  let ui := a0.getD 0 []
  let β := a0.getD 1 []
  let r := K.pcp.seedLen lam ui.length
  let aw := 2 * La + 1
  let inp := pack [vk, ui, β, unary r, unary La]
  let E := r + aw + X.work lam inp
  let init : JState S.n E := fun p =>
    if ∀ i : Fin E, r ≤ i.val → p.2 i = false then
      (((Real.sqrt ((2 : ℝ) ^ r))⁻¹ : ℝ) : ℂ) * ψ p.1 else 0
  let φ := respU S u vk (toBits c0) E r aw init
  { vk := vk, c0 := toBits c0, inst := ui, r := r, aw := aw, inp := inp, E := E,
    state := fun p =>
      if K.verify lam vk ui β (seedOf r p.2) (ans1 S u vk (toBits c0) (seedOf r p.2) (outVals S p.1))
      then φ p else 0 }

/-- Step `t` of the procedure, before its halting measurement. -/
noncomputable def geStep (X : Extractor) (lam : ℕ) (S : Strategy) (u : Bits) (b : GEBranch S.n)
    (t : ℕ) (φ : JState S.n b.E) : JState S.n b.E :=
  (X.step lam b.inp t).foldl (fun φ o => o.run S u b.vk b.c0 b.E b.r b.aw φ) φ

/-- The state of the procedure before step `t`, on the branch where it has not halted yet. -/
noncomputable def geRun (X : Extractor) (lam : ℕ) (S : Strategy) (u : Bits) (b : GEBranch S.n) :
    ℕ → JState S.n b.E
  | 0 => b.state
  | t + 1 => haltProj (X.halt lam b.inp) false (geStep X lam S u b t (geRun X lam S u b t))

/-- The projector onto the output wires having the values `w`. -/
def outProj {n E : ℕ} (out : List ℕ) (w : Bits) (ψ : JState n E) : JState n E :=
  fun p => if valsOf out p.2 = w then ψ p else 0

/-- The average over uniform coins of length `c`, in `ℝ≥0∞`. -/
noncomputable def avgE (c : ℕ) (g : Bits → ENNReal) : ENNReal :=
  ((2 : ENNReal) ^ c)⁻¹ * ∑ r : Qubits c, g (toBits r)

/-- On one branch: the weight of halting at some step with an output `w` such that `R(u, w) ≠ 1`. -/
noncomputable def geFailBranch (R : Relation) (X : Extractor) (lam : ℕ) (S : Strategy) (u : Bits)
    (b : GEBranch S.n) : ENNReal :=
  ∑' t : ℕ, ∑ w : Qubits (X.out lam b.inp).length,
    if R.rel b.inst (toBits w) = true then 0 else
      ENNReal.ofReal (JState.weight (outProj (X.out lam b.inp) (toBits w)
        (haltProj (X.halt lam b.inp) true (geStep X lam S u b t (geRun X lam S u b t)))))

/-- On one branch: the expected cost, `∑_t Pr[step t is run] · cost(step t)`. -/
noncomputable def geTimeBranch (X : Extractor) (lam : ℕ) (S : Strategy) (TA : ℕ) (u : Bits)
    (b : GEBranch S.n) : ENNReal :=
  ∑' t : ℕ, ENNReal.ofReal (JState.weight (geRun X lam S u b t)) *
    ((1 + ((X.step lam b.inp t).map (XOp.cost TA)).sum : ℕ) : ENNReal)

/-- `Pr[B = 1 ∧ R(u, w) ≠ 1 : (u, B, w) ← GE_A(1^λ)]`, over key generation, the prover's tape and
first-stage outcome, the measurement of `B` and every internal outcome of the procedure. -/
noncomputable def Kilian.geFail (K : Kilian) (R : Relation) (X : Extractor) (lam : ℕ) (S : Strategy)
    (La : ℕ) : ENNReal :=
  avgE (K.setupCoins lam) fun rv => avgE S.tape fun u =>
    ∑ c0 : Qubits (S.outLen 0), geFailBranch R X lam S u (geBranch K X lam S La rv u c0)

/-- `E[Time]` of the procedure in `GE_A(1^λ)`, over the whole experiment (the branch `B = 0` runs no
step), with `T_A = |A| + L_a` per call. -/
noncomputable def Kilian.geTime (K : Kilian) (X : Extractor) (lam : ℕ) (S : Strategy) (La : ℕ) :
    ENNReal :=
  avgE (K.setupCoins lam) fun rv => avgE S.tape fun u =>
    ∑ c0 : Qubits (S.outLen 0), geTimeBranch X lam S (S.size + La) u (geBranch K X lam S La rv u c0)

/-- Guaranteed extraction, Definition 3.25 (p.23), for Kilian's argument and the relation `R`:
there is a uniform witness-finding procedure and a polynomial `P` such that, for every QPT prover
`A` (an `IsQPT` strategy with quantum advice) and every polynomial bound `L_a` on the length of
its round-1 answers,

1. `Pr[B = 1 ∧ R(u, w) ≠ 1 : (u, B, w) ← GE_A(1^λ)] ≤ ν(λ)` for a negligible `ν`, and
2. `E[Time_GE] ≤ P(λ, M, T_A)` for every `λ`, with `T_A = |A| + L_a`.

Both are over the whole experiment, including key generation, the adaptive `(u, β)`, the initial
accepting measurement and every internal outcome; they are not conditional bounds for fixed
`(vk, u, β)` or for `B = 1`. The procedure works on the one residual state `ρ_B`. -/
def Kilian.GuaranteedExtraction (K : Kilian) (R : Relation) : Prop :=
  ∃ X : Extractor, X.IsUniform ∧ ∃ P : MvPolynomial (Fin 4) ℕ,
    ∀ Adv : ℕ → Strategy, IsQPT Adv → ∀ La : ℕ → ℕ, PolyBound La →
      (∀ lam v, ((Adv lam).toVerifier 1 v).length ≤ La lam) →
      (∃ ν : ℕ → ℝ, Negligible ν ∧ ∀ lam, K.geFail R X lam (Adv lam) (La lam) ≤ ENNReal.ofReal (ν lam)) ∧
      ∀ lam, K.geTime X lam (Adv lam) (La lam) ≤
        ((eval4 P lam (K.pcp.proofLen lam) ((Adv lam).size + La lam) 0 : ℕ) : ENNReal)

end Supplement

end FourMsgQMA


