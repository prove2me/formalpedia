-- Prove2me | Definitions.Def_FourMsgQMA_Arg4
-- name    : FourMsgQMA_Arg4
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:34:59.647502+00:00
-- url     : https://prove2.me/theorems/5281af39-ad8c-4cce-93c0-6732d747efb8
-- title:
--   Four-message classical-verifier arguments $\Pi=(\mathrm{Pre},V_1,P_1,V_2,P_2,\mathrm{Dec})$ for NP ∘ batchQMA
-- statement:
--   A **four-message argument** ($m=2$ in §3.3) consists of:
--
--   1. $v_0\leftarrow\mathrm{Pre}(1^\lambda,u)$, preprocessing of the statement $u=(C,X)$ into a private state;
--   2. $(q_1,v_1)\leftarrow V_1(v_0)$ and $(q_2,v_2)\leftarrow V_2(v_1,a_1)$, the verifier's questions and private states;
--   3. $b=\mathrm{Dec}(v_2,a_2)$, a deterministic decision that may use the private state (designated verifier);
--   4. an honest prover: a copy count $N(\lambda,t)$, and a quantum core with two controllers generated from $(\lambda,u,(y,a))$.
--
--   The verifier stages are deterministic maps of their inputs and explicit uniform coins, whose lengths depend on $\lambda$ and $|u|$.
--
--   The **experiment** on a statement sequence $(u_\lambda)$ samples all verifier coins after $u_\lambda$ is fixed, sends $q_1$, receives $a_1$, sends $q_2=V_2(v_1,a_1)$, receives $a_2$, and accepts when $\mathrm{Dec}(v_2,a_2)=1$. It is a published `TightPQRepetition.Main.Verifier`, used only to carry the semantics.
--
--   The **honest execution** on an admissible $u$ with an authorized $y$ and witnesses $\rho_i$ runs the generated core from
--   $$
--   \bigotimes_{i:\,y_i=1}\rho_i^{\otimes N(\lambda,t(X))}\otimes|0\cdots0\rangle\langle0\cdots0|,
--   $$
--   with the registers in increasing order of $i$.
--
--   **Formalization Note** Pinned-down version (operator request). The statement is available to $V_1,V_2,\mathrm{Dec}$ through the private state, as in the paper ("Both parties retain this transcript as part of their state", p.11).
-- source:
--   Goyal, Koppula, Four-Message Arguments for NP ∘ batchQMA and Six-Message Arguments for QMA from LWE, STOC 2027 submission (sha256 6c523d45…), §3.3, pp.11–12 (PDF 13–14); Definition 3.6, p.13 (PDF 15)

import Mathlib
import Definitions.Def_FourMsgQMA_Inst
import Definitions.Def_FourMsgQMA_Core

namespace FourMsgQMA

/-!
Goyal, Koppula, STOC 2027 submission (sha256 6c523d45…), §3.3 (pp.11–12, PDF 13–14) and
Definition 3.6 (p.13, PDF 15): four-message (`m = 2`) classical-verifier arguments
`Π = (Pre, V₁, P₁, V₂, P₂, Dec)` for NP ∘ batchQMA, their honest execution and the selective
soundness experiment.

Pinned-down version (operator request). The verifier stages are deterministic maps of their
inputs and explicit uniform coins; their efficiency is stated in `Arg4.IsUniform` and
`Arg4.Succinct`. The honest prover is generated from `(1^λ, u, y, a)` as a quantum core
(`FourMsgQMA.Core`) with two classical controllers; its quantum input is the honest resource.
-/

open QAlgorithms QAlgorithms.Complexity TightPQRepetition.Main

/-- A four-message argument for NP ∘ batchQMA (§3.3, p.11, with `m = 2`). Statements are encoded
instances `u.encode`; `λ` is the first argument of every algorithm. -/
structure Arg4 where
  /-- Coin lengths of `Pre`, `V₁`, `V₂` as functions of `λ` and `|u|`. -/
  coins0 : ℕ → ℕ → ℕ
  /-- See `coins0`. -/
  coins1 : ℕ → ℕ → ℕ
  /-- See `coins0`. -/
  coins2 : ℕ → ℕ → ℕ
  /-- `v₀ ← Pre(1^λ, b, u)`, with coins: the private state after preprocessing. -/
  pre : ℕ → Bits → Bits → Bits
  /-- `(q₁, v₁) ← V₁(u, v₀, ⊥)`, with coins. The statement is available through `v₀`. -/
  v1 : ℕ → Bits → Bits → Bits × Bits
  /-- `(q₂, v₂) ← V₂(u, v₁, a₁)`, with coins. -/
  v2 : ℕ → Bits → Bits → Bits → Bits × Bits
  /-- `b = Dec(u, v₂, a₂)`, deterministic. -/
  dec : ℕ → Bits → Bits → Bool
  /-- The number `N(λ, t)` of copies of each selected witness in the honest resource. -/
  copies : ℕ → ℕ → ℕ
  /-- The honest prover's quantum core, generated from `(λ, u, w)`, `w` the classical witness. -/
  core : ℕ → Bits → Bits → Core
  /-- The honest prover's controller writing into the core: `(λ, u, w, j, view)`. -/
  toCore : ℕ → Bits → Bits → ℕ → Bits → Bits
  /-- The honest prover's controller computing its answers: `(λ, u, w, j, view)`. -/
  toVerifier : ℕ → Bits → Bits → ℕ → Bits → Bits

/-- The verifier's coins split into those of `Pre`, `V₁`, `V₂`. -/
def Arg4.coinParts (A : Arg4) (lam m : ℕ) (r : Bits) : Bits × Bits × Bits :=
  (r.take (A.coins0 lam m), (r.drop (A.coins0 lam m)).take (A.coins1 lam m),
    (r.drop (A.coins0 lam m + A.coins1 lam m)).take (A.coins2 lam m))

/-- The verifier's state `v₁` and first message `q₁` on statement `x` and coins `r`. -/
def Arg4.firstMsg (A : Arg4) (lam : ℕ) (x r : Bits) : Bits × Bits :=
  let c := A.coinParts lam x.length r
  A.v1 lam (A.pre lam x c.1) c.2.1

/-- The verifier of the experiment of §3.3 / Definition 3.6 on the instance sequence `u`, as a
published `TightPQRepetition.Main.Verifier` (semantic carrier only; its `qLen` is unused): two
rounds, with `q₁ = V₁(…)` and `q₂ = V₂(…, a₁)`, and verdict `Dec(v₂, a₂)`. All verifier coins are
sampled before the interaction, and the statement `u λ` precedes them. -/
def Arg4.verifierSeq (A : Arg4) (u : ℕ → Inst) : Verifier where
  rounds := fun _ => 2
  coins := fun lam =>
    A.coins0 lam (u lam).size + A.coins1 lam (u lam).size + A.coins2 lam (u lam).size
  qLen := fun _ _ => 0
  query := fun lam r j as =>
    let x := (u lam).encode
    let m1 := A.firstMsg lam x r
    if j = 0 then m1.1
    else (A.v2 lam m1.2 (as.headD []) (A.coinParts lam x.length r).2.2).1
  verdict := fun lam r τ =>
    let x := (u lam).encode
    let m1 := A.firstMsg lam x r
    let m2 := A.v2 lam m1.2 (τ.getD 0 ([], [])).2 (A.coinParts lam x.length r).2.2
    A.dec lam m2.2 (τ.getD 1 ([], [])).2

/-- The width of the witness register of coordinate `i`: `F.wit |x_i|` qubits. -/
def witWidth (F : QMAFamily) (u : Inst) (i : Fin u.k) : ℕ := F.wit (u.X i).length

/-- The witness registers of the honest resource, in order: for each selected coordinate
`i` (`y_i = 1`), in increasing order of `i`, `N` copies of its witness register. -/
def witBlocks {k : ℕ} (y : Fin k → Bool) (N : ℕ) : List (Fin k) :=
  (List.finRange k).flatMap fun i => if y i then List.replicate N i else []

/-- The probability that the honest verifier accepts in the honest execution of §3.3 (p.11) at
security parameter `λ` on the instance `u`, with the classical witness `(y, a)` (`a` the wire
values of `C` on `y`) and the quantum resource `⊗_{i : y_i = 1} ρ_i^{⊗N}`, `N = N(λ, t(X))`, placed
on the first wires of the honest core (in increasing order of `i`; all other wires `|0⟩`). -/
noncomputable def Arg4.honestAccept (A : Arg4) (F : QMAFamily) (lam : ℕ) (u : Inst)
    (y : Fin u.k → Bool)
    (ρ : (i : Fin u.k) → Matrix (Qubits (witWidth F u i)) (Qubits (witWidth F u i)) ℂ) : ℝ :=
  let w := u.classicalWitness y
  let S := A.core lam u.encode w
  S.acceptMixed (A.toCore lam u.encode w) (A.toVerifier lam u.encode w)
    (A.verifierSeq fun _ => u) lam
    (loadedState (witWidth F u) ρ (witBlocks y (A.copies lam (batchCost F u))) S.n)

end FourMsgQMA


