-- Prove2me | Definitions.Def_FourMsgQMA_Supplement_BatchArg
-- name    : FourMsgQMA_Supplement_BatchArg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:26:11.419557+00:00
-- url     : https://prove2.me/theorems/0f91933a-e08f-49a7-8b11-8083713f0b26
-- title:
--   Four-message batch arguments with $X$-independent questions: completeness, semi-adaptive soundness (Def 3.5), batch communication
-- statement:
--   A **four-message batch argument whose verifier questions are generated without $X$** has $v_0\leftarrow\mathrm{Pre}(1^\lambda,(k,T),\perp)$, $(q_1,v_1)\leftarrow V_1(v_0)$, $(q_2,v_2)\leftarrow V_2(v_1,a_1)$ and a decision $\mathrm{Dec}(X,v_2,a_2)$ that alone reads the batch $X=(x_1,\dots,x_k)$ of a QMA promise problem $L$.
--
--   1. **Completeness**: overwhelming acceptance for every yes-batch with $t_L(x_i)\le T$ and the honest resource $\bigotimes_{i\in[k]}\omega_i$, $\omega_i=\rho_i^{\otimes N(\lambda,T)}$, $\rho_i\in W_Q(x_i,2/3)$.
--   2. **Semi-adaptive batch soundness** (Definition 3.5): for every fixed $i^*\in[k]$ and $x^*\in L_{\mathrm{no}}$ chosen before setup and every two-stage QPT adversary that outputs $(X,a_2)$ with its last message,
--   $$
--   \Pr\big[b=1\ \wedge\ x_{i^*}=x^*\big]\le\nu(\lambda)
--   $$
--   for a negligible $\nu$.
--   3. **Batch communication** (§3.3): every message has length at most $p(\lambda,T,\log(k+1))$ for one polynomial $p$, longer answers are rejected, and the honest answers on an admissible batch ($t_L(x_i)\le T$) and on every view the honest prover can have in an execution are within the same bound.
--
--   These are the conclusions of Theorem 4.1.
--
--   **Formalization Note** The honest resource places $\omega_i$ on the $i$-th consecutive region of the prover's core; $\log$ is $\lceil\log_2\rceil$; adversaries are `IsQPT` strategies.
-- source:
--   Goyal, Koppula, Four-Message Arguments for NP ∘ batchQMA and Six-Message Arguments for QMA from LWE, STOC 2027 submission (sha256 6c523d45…), §3.3, pp.11–12 (PDF 13–14); Definition 3.5, p.12 (PDF 14)

import Mathlib
import Definitions.Def_FourMsgQMA_WQ
import Definitions.Def_FourMsgQMA_Core
import Definitions.Def_FourMsgQMA_Supplement_HashFamily

namespace FourMsgQMA

/-!
Goyal, Koppula, STOC 2027 submission (sha256 6c523d45…), §3.3 (pp.11–12, PDF 13–14) and
Definition 3.5 (p.12, PDF 14): four-message batch arguments "whose verifier questions can be
generated without knowing `X`", for batches `X = (x₁, …, x_k)` of a QMA promise problem, with the
public resource descriptor `b = (k, T)`; their honest execution, completeness, semi-adaptive batch
soundness, and batch communication.

Pinned-down version (operator request): the verifier stages are deterministic maps of their inputs
and explicit uniform coins; the honest prover is a quantum core with two classical controllers,
generated from `(1^λ, T, X)`; its quantum input is the honest resource `⊗_{i ∈ [k]} ω_i` with
`ω_i = ρ_i^{⊗N(λ, T)}`, `ρ_i ∈ W_Q(x_i, 2/3)`: the core's wires are split into consecutive regions,
one per entry, region `i` holding `ω_i` on its first wires and `|0⟩` on the rest, and the wires after
the last region hold `|0⟩`. Adversaries are the published `IsQPT` strategies.
-/

namespace Supplement

open QAlgorithms QAlgorithms.Complexity TightPQRepetition.Main

/-- A four-message batch argument with verifier questions independent of `X`. -/
structure BatchArg where
  /-- The coin lengths of `Pre`, `V₁`, `V₂` at `(λ, k, T)`. -/
  coins0 : ℕ → ℕ → ℕ → ℕ
  /-- See `coins0`. -/
  coins1 : ℕ → ℕ → ℕ → ℕ
  /-- See `coins0`. -/
  coins2 : ℕ → ℕ → ℕ → ℕ
  /-- `v₀ ← Pre(1^λ, (k, T), ⊥)`, with coins. -/
  pre : ℕ → ℕ → ℕ → Bits → Bits
  /-- `(q₁, v₁) ← V₁(⊥, v₀, ⊥)`, with coins. -/
  v1 : ℕ → Bits → Bits → Bits × Bits
  /-- `(q₂, v₂) ← V₂(⊥, v₁, a₁)`, with coins. -/
  v2 : ℕ → Bits → Bits → Bits → Bits × Bits
  /-- `b = Dec(X, v₂, a₂)`, deterministic. -/
  dec : ℕ → List Bits → Bits → Bits → Bool
  /-- The number `N(λ, T)` of witness copies in each entry's resource. -/
  copies : ℕ → ℕ → ℕ
  /-- The honest prover's quantum core, generated from `(λ, T, X)`. -/
  core : ℕ → ℕ → List Bits → Core
  /-- The sizes of the consecutive regions of the core, one per entry: `(λ, T, X, i)`. -/
  region : ℕ → ℕ → List Bits → ℕ → ℕ
  /-- The honest controller writing into the core: `(λ, T, X, j, view)`. -/
  toCore : ℕ → ℕ → List Bits → ℕ → Bits → Bits
  /-- The honest controller computing the answers: `(λ, T, X, j, view)`. -/
  toVerifier : ℕ → ℕ → List Bits → ℕ → Bits → Bits

/-- The verifier's coins split into those of `Pre`, `V₁`, `V₂`. -/
def BatchArg.coinParts (A : BatchArg) (lam k T : ℕ) (r : Bits) : Bits × Bits × Bits :=
  (r.take (A.coins0 lam k T), (r.drop (A.coins0 lam k T)).take (A.coins1 lam k T),
    (r.drop (A.coins0 lam k T + A.coins1 lam k T)).take (A.coins2 lam k T))

/-- `(q₁, v₁)` at `(λ, k, T)` with coins `r`. -/
def BatchArg.firstMsg (A : BatchArg) (lam k T : ℕ) (r : Bits) : Bits × Bits :=
  let c := A.coinParts lam k T r
  A.v1 lam (A.pre lam k T c.1) c.2.1

/-- `(q₂, v₂)` after the answer `a₁`. -/
def BatchArg.secondMsg (A : BatchArg) (lam k T : ℕ) (r a1 : Bits) : Bits × Bits :=
  A.v2 lam (A.firstMsg lam k T r).2 a1 (A.coinParts lam k T r).2.2

/-- The honest execution on the batch `X` with descriptor `(|X|, T)`, as a published
`TightPQRepetition.Main.Verifier` (semantic carrier): two rounds `q₁, q₂`, verdict `Dec(X, v₂, a₂)`. -/
def BatchArg.honestVerifier (A : BatchArg) (T : ℕ) (X : List Bits) : Verifier where
  rounds := fun _ => 2
  coins := fun lam => A.coins0 lam X.length T + A.coins1 lam X.length T + A.coins2 lam X.length T
  qLen := fun _ _ => 0
  query := fun lam r j as =>
    if j = 0 then (A.firstMsg lam X.length T r).1 else (A.secondMsg lam X.length T r (as.headD [])).1
  verdict := fun lam r τ =>
    A.dec lam X (A.secondMsg lam X.length T r (τ.getD 0 ([], [])).2).2 (τ.getD 1 ([], [])).2

/-- The `m` wires of `y` from wire `o` on. -/
def regionOf {n : ℕ} (y : Qubits n) (o m : ℕ) : Qubits m := fun j => wireAt y (o + j.val)

/-- The honest initial state: region `i` (of size `sizes i`, consecutive from wire `0`) holds
`ρ_i^{⊗N}` on its first wires and `|0⟩` on the rest; every wire after the last region holds `|0⟩`. -/
noncomputable def batchResource (F : QMAFamily) (X : List Str) (N : ℕ) (sizes : ℕ → ℕ)
    (ρ : (i : Fin X.length) → Matrix (Qubits (F.wit (X.get i).length)) (Qubits (F.wit (X.get i).length)) ℂ)
    (n : ℕ) : Matrix (Qubits n) (Qubits n) ℂ :=
  let off : ℕ → ℕ := fun i => ∑ j ∈ Finset.range i, sizes j
  Matrix.of fun y z =>
    if off X.length ≤ n ∧ (∀ m : Fin n, off X.length ≤ m.val → y m = false ∧ z m = false) then
      ∏ i : Fin X.length,
        loadedState (fun _ : Unit => F.wit (X.get i).length) (fun _ => ρ i) (List.replicate N ()) (sizes i)
          (regionOf y (off i) (sizes i)) (regionOf z (off i) (sizes i))
    else 0

/-- The acceptance probability of the honest execution on `X` at resource bound `T` with the
resource `⊗_i ρ_i^{⊗N(λ, T)}`. -/
noncomputable def BatchArg.honestAccept (A : BatchArg) (F : QMAFamily) (lam T : ℕ) (X : List Str)
    (ρ : (i : Fin X.length) → Matrix (Qubits (F.wit (X.get i).length)) (Qubits (F.wit (X.get i).length)) ℂ) :
    ℝ :=
  let S := A.core lam T X
  S.acceptMixed (A.toCore lam T X) (A.toVerifier lam T X) (A.honestVerifier T X) lam
    (batchResource F X (A.copies lam T) (A.region lam T X) ρ S.n)

/-- Overwhelming completeness for every yes-batch and every honest resource (§3.3, p.11): for every
polynomial bound `B'` there is a negligible `ν` such that for every `λ`, every `T ≤ B'(λ)` and every
batch `X = (x₁, …, x_k)` with `1 ≤ k ≤ B'(λ)`, all `x_i ∈ L_yes` and `t_L(x_i) ≤ T`, and all
`ρ_i ∈ W_Q(x_i, 2/3)`, the honest execution accepts with probability at least `1 − ν(λ)`. -/
def BatchArg.Complete (A : BatchArg) (L : PromiseProblem) (F : QMAFamily) : Prop :=
  ∀ B' : ℕ → ℕ, PolyBound B' → ∃ ν : ℕ → ℝ, Negligible ν ∧
    ∀ (lam T : ℕ) (X : List Str), T ≤ B' lam → 1 ≤ X.length → X.length ≤ B' lam →
      (∀ x ∈ X, x ∈ L.yes ∧ localCost F x ≤ T) →
      ∀ ρ : (i : Fin X.length) → Matrix (Qubits (F.wit (X.get i).length)) (Qubits (F.wit (X.get i).length)) ℂ,
        (∀ i, ρ i ∈ WQ F (X.get i) (2 / 3)) → 1 - ν lam ≤ A.honestAccept F lam T X ρ

/-- The experiment of Definition 3.5 (p.12) for `(k, T)(λ)`, the index `i*` and the false instance
`x*`, as a published `TightPQRepetition.Main.Verifier` (semantic carrier): the verifier questions
`q₁ = V₁(⊥, v₀, ⊥)` and `q₂ = V₂(⊥, v₁, a₁)` are computed without `X`; the adversary's last answer is
`pack [pack X, a₂]`; it wins when `Dec(X, v₂, a₂) = 1` and `x_{i*} = x*`. The adversary may hardwire
`(i*, x*)`. -/
def BatchArg.semiAdaptiveVerifier (A : BatchArg) (k T istar : ℕ → ℕ) (xstar : ℕ → Str) : Verifier where
  rounds := fun _ => 2
  coins := fun lam => A.coins0 lam (k lam) (T lam) + A.coins1 lam (k lam) (T lam) + A.coins2 lam (k lam) (T lam)
  qLen := fun _ _ => 0
  query := fun lam r j as =>
    if j = 0 then (A.firstMsg lam (k lam) (T lam) r).1
    else (A.secondMsg lam (k lam) (T lam) r (as.headD [])).1
  verdict := fun lam r τ =>
    let fin := unpack (τ.getD 1 ([], [])).2
    let X := unpack (fin.getD 0 [])
    A.dec lam X (A.secondMsg lam (k lam) (T lam) r (τ.getD 0 ([], [])).2).2 (fin.getD 1 []) &&
      decide (X.getD (istar lam - 1) [] = xstar lam)

/-- Semi-adaptive batch soundness, Definition 3.5 (p.12): for all polynomially bounded `k ≥ 1` and
`T`, every fixed `i* ∈ [k]` and every fixed `x* ∈ L_no` with `t_L(x*) ≤ T`, chosen before setup, and
every QPT adversary, `Pr[b = 1 ∧ x_{i*} = x*] ≤ ν(λ)` for a negligible `ν`. -/
def BatchArg.SemiAdaptiveSound (A : BatchArg) (L : PromiseProblem) (F : QMAFamily) : Prop :=
  ∀ k T : ℕ → ℕ, PolyBound k → PolyBound T → (∀ lam, 1 ≤ k lam) →
    ∀ istar : ℕ → ℕ, (∀ lam, 1 ≤ istar lam ∧ istar lam ≤ k lam) →
    ∀ xstar : ℕ → Str, (∀ lam, xstar lam ∈ L.no ∧ localCost F (xstar lam) ≤ T lam) →
    ∀ Adv : ℕ → Strategy, IsQPT Adv →
      Negligible fun lam => (Adv lam).acceptProb (A.semiAdaptiveVerifier k T istar xstar) lam

/-- Batch communication (§3.3, p.12: "Every message has length at most `p(λ, T, log(k + 1))`"; "for
every admissible input, setup outcome, and transcript within the prescribed length bounds"): one
polynomial `p` such that, with `P = p(λ, T, ⌈log₂(k + 1)⌉)`, for every `λ, k, T`, every coin outcome
and every transcript within the bounds, `|q₁| ≤ P`, `|q₂| ≤ P` whenever `|a₁| ≤ P`, `Dec` accepts only
answers with `|a₁|, |a₂| ≤ P`, and both answers of the honest prover have length at most `P` on every
admissible batch (`t_L(x_i) ≤ T`) and every view it can have in an execution: its tape of the
prescribed length, the genuine `q₁`, any core outcome `c₀`, then the genuine `q₂` (for any `a₁`) and
any core outcome `c₁`. -/
def BatchArg.ShortMessages (A : BatchArg) (F : QMAFamily) : Prop :=
  ∃ p : MvPolynomial (Fin 4) ℕ, ∀ (lam k T : ℕ) (r : Bits),
    r.length = A.coins0 lam k T + A.coins1 lam k T + A.coins2 lam k T →
    let P := eval4 p lam T (clog2 (k + 1)) 0
    (A.firstMsg lam k T r).1.length ≤ P ∧
    (∀ a1 : Bits, a1.length ≤ P → (A.secondMsg lam k T r a1).1.length ≤ P) ∧
    (∀ (X : List Bits) (a1 a2 : Bits), X.length = k →
      A.dec lam X (A.secondMsg lam k T r a1).2 a2 = true → a1.length ≤ P ∧ a2.length ≤ P) ∧
    (∀ (X : List Bits) (tape c0 a1 c1 : Bits), X.length = k → (∀ x ∈ X, localCost F x ≤ T) →
      tape.length = (A.core lam T X).tape →
      (A.toVerifier lam T X 0 (pack [tape, (A.firstMsg lam k T r).1, c0])).length ≤ P ∧
      (A.toVerifier lam T X 1
        (pack [tape, (A.firstMsg lam k T r).1, c0, (A.secondMsg lam k T r a1).1, c1])).length ≤ P)

end Supplement

end FourMsgQMA


