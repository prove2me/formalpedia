-- Prove2me | Definitions.Def_FourMsgQMA_BaseProtocol
-- name    : FourMsgQMA_BaseProtocol
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:31:53.811449+00:00
-- url     : https://prove2.me/theorems/e73b35bc-a1b5-4764-85bc-a45d91c87f1e
-- title:
--   Four-message base protocols $\Pi_0=(\mathrm{Gen},P_1,P_2,V)$, completeness and soundness (Definition 3.7)
-- statement:
--   A **base protocol** for a promise problem $L$ (§3.4) consists of $(p,r)\leftarrow\mathrm{Gen}(1^\lambda,T)$, which does not read the instance; a first response $\mu\leftarrow P_1(x,p,\omega)$; a uniform challenge $c\in\{0,1\}^{m(\lambda,T)}$; a last response $z\leftarrow P_2(c,\rho)$; and a deterministic total verdict $V(x,r,\mu,c,z)$. The honest prover is a generated quantum core whose resource $W_0(x)$ is $N(\lambda,T)$ copies of a witness $\rho\in W_Q(x,2/3)$.
--
--   Its properties:
--
--   1. **uniformity**: $\mathrm{Gen}$, $V$, the coin and challenge lengths, the copy count and the honest prover are polynomial time;
--   2. **size bounds** $\mathrm{poly}(\lambda,T)$: one polynomial bounds $|p|$, $|r|$, $m(\lambda,T)$, $N(\lambda,T)$, the honest core, the accepted responses (longer ones are rejected) and the circuit computing $V$;
--   3. **overwhelming statistical completeness**: for every polynomial bound $B$ there is a negligible $\nu$ such that for all $\lambda$, all $x\in L_{\mathrm{yes}}$ with $|x|\le B(\lambda)$ and all $\rho\in W_Q(x,2/3)$, the honest execution accepts with probability at least $1-\nu(\lambda)$;
--   4. **negligible soundness** (Definition 3.7 with $s_0=0$): for every sequence of fixed $x_\lambda\in L_{\mathrm{no}}$ of polynomial length and every QPT $(A_1,A_2)$,
--   $$
--   \Pr\big[V(x,r,\mu,c,z)=1:\ (p,r)\leftarrow\mathrm{Gen};\ (\mu,\zeta_1)\leftarrow A_1(x,\zeta_\lambda,p);\ c\leftarrow\{0,1\}^m;\ (z,\zeta_2)\leftarrow A_2(\zeta_1,c)\big]
--   $$
--   is negligible.
--
--   **Formalization Note** Pinned-down version (operator request): $T=t_L(x)$; adversaries are `IsQPT`; the experiment is a published `Verifier` carrier.
-- source:
--   Goyal, Koppula, Four-Message Arguments for NP ∘ batchQMA and Six-Message Arguments for QMA from LWE, STOC 2027 submission (sha256 6c523d45…), §3.4 and Definition 3.7, pp.13–14 (PDF 15–16)

import Mathlib
import Definitions.Def_FourMsgQMA_WQ
import Definitions.Def_FourMsgQMA_Core

namespace FourMsgQMA

/-!
Goyal, Koppula, STOC 2027 submission (sha256 6c523d45…), §3.4 (pp.13–14, PDF 15–16): four-message
base protocols `Π₀ = (Gen, P₁, P₂, V)` for a QMA promise problem, their statistical completeness and
computational soundness (Definition 3.7).

Pinned-down version (operator request): the local resource parameter `T` is `t_L(x)`
(`localCost`), the honest resource `W₀(x)` is `N(λ, T)` copies of a witness `ρ ∈ W_Q(x, 2/3)`, the
honest prover is a uniformly generated quantum core (`FourMsgQMA.Core`), adversaries are the
published `TightPQRepetition.Main.IsQPT` families, and "PPT"/"poly" are polynomial-time
computability and polynomial bounds.
-/

open QAlgorithms QAlgorithms.Complexity TightPQRepetition.Main

/-- A four-message base protocol (§3.4, p.13). -/
structure BaseProtocol where
  /-- The number of coins of `Gen` at `(λ, T)`. -/
  genCoins : ℕ → ℕ → ℕ
  /-- `(p, r) ← Gen(1^λ, T)`, with coins: public setup `p` and complete private state `r`. It does
  not read the instance. -/
  gen : ℕ → ℕ → Bits → Bits × Bits
  /-- The challenge length `m(λ, T)`. -/
  chalLen : ℕ → ℕ → ℕ
  /-- `b = V(x, r, µ, c, z)`, a deterministic total predicate (with `λ`). -/
  verdict : ℕ → Bits → Bits → Bits → Bits → Bits → Bool
  /-- The number `N(λ, T)` of witness copies in the honest resource `W₀(x)`. -/
  copies : ℕ → ℕ → ℕ
  /-- The honest prover's quantum core, generated from `(λ, x)`. -/
  core : ℕ → Bits → Core
  /-- The honest prover's controller writing into the core: `(λ, x, j, view)`. -/
  toCore : ℕ → Bits → ℕ → Bits → Bits
  /-- The honest prover's controller computing `µ` (round 0) and `z` (round 1): `(λ, x, j, view)`. -/
  toVerifier : ℕ → Bits → ℕ → Bits → Bits

/-- The experiment of §3.4 / Definition 3.7 on the instance sequence `x` with resource parameter
`T`, as a published `TightPQRepetition.Main.Verifier` (semantic carrier only): the prover receives
the setup `p` and answers `µ`, then receives a uniform challenge `c ∈ {0,1}^{m(λ,T)}` and answers
`z`; the verdict is `V(x, r, µ, c, z)`. -/
def BaseProtocol.verifierSeq (B : BaseProtocol) (x : ℕ → Str) (T : ℕ → ℕ) : Verifier where
  rounds := fun _ => 2
  coins := fun lam => B.genCoins lam (T lam) + B.chalLen lam (T lam)
  qLen := fun _ _ => 0
  query := fun lam r j _ =>
    if j = 0 then (B.gen lam (T lam) (r.take (B.genCoins lam (T lam)))).1
    else r.drop (B.genCoins lam (T lam))
  verdict := fun lam r τ =>
    B.verdict lam (x lam) (B.gen lam (T lam) (r.take (B.genCoins lam (T lam)))).2
      (τ.getD 0 ([], [])).2 (r.drop (B.genCoins lam (T lam))) (τ.getD 1 ([], [])).2

/-- The acceptance probability of the honest execution on `x` with the resource
`ρ^{⊗N(λ, t_L(x))}` on the first wires of the honest core (all other wires `|0⟩`). -/
noncomputable def BaseProtocol.honestAccept (B : BaseProtocol) (F : QMAFamily) (lam : ℕ) (x : Str)
    (ρ : Matrix (Qubits (F.wit x.length)) (Qubits (F.wit x.length)) ℂ) : ℝ :=
  let S := B.core lam x
  S.acceptMixed (B.toCore lam x) (B.toVerifier lam x) (B.verifierSeq (fun _ => x)
    (fun _ => localCost F x)) lam
    (loadedState (fun _ : Unit => F.wit x.length) (fun _ => ρ)
      (List.replicate (B.copies lam (localCost F x)) ()) S.n)

/-- Uniformity: `Gen`, `V`, the coin and challenge lengths, the honest core, its controllers and
the copy count are polynomial-time computable (§3.4, p.13: "A PPT algorithm generates…", "A QPT
algorithm…", "A deterministic total predicate"). -/
def BaseProtocol.IsUniform (B : BaseProtocol) : Prop :=
  (∃ g : Str → Str, PolyTimeComputable g ∧ ∀ lam T,
      g (pack [unary lam, unary T]) =
        pack [unary (B.genCoins lam T), unary (B.chalLen lam T), unary (B.copies lam T)]) ∧
  (∃ g : Str → Str, PolyTimeComputable g ∧ ∀ lam T r,
      g (pack [unary lam, unary T, r]) = pack [(B.gen lam T r).1, (B.gen lam T r).2]) ∧
  (∃ g : Str → Str, PolyTimeComputable g ∧ ∀ lam x r μ c z,
      g (pack [unary lam, x, r, μ, c, z]) = [B.verdict lam x r μ c z]) ∧
  (∃ g : Str → Str, PolyTimeComputable g ∧ ∀ lam x,
      g (pack [unary lam, x]) = (B.core lam x).encode) ∧
  (∃ g : Str → Str, PolyTimeComputable g ∧ ∀ lam x j v,
      g (pack [unary lam, x, unary j, v]) = B.toCore lam x j v) ∧
  (∃ g : Str → Str, PolyTimeComputable g ∧ ∀ lam x j v,
      g (pack [unary lam, x, unary j, v]) = B.toVerifier lam x j v)

/-- Size bounds (§3.4, p.13: "All messages, the state `r`, and the circuit for `V` have fixed size
bounds poly(λ, T). Key generation and honest work have the same local polynomial bound. Honest
witnesses and their copy count are part of `W₀`."). One polynomial `p` bounds, with
`P = p(λ, T, 0, 0)` and `T = t_L(x)`: the setup `p` and state `r` for every coin outcome, the
challenge length, the accepted responses (`V` rejects longer `µ`, `z`), the size of circuits
computing `V` on the inputs that occur, the size of the honest core and the copy count, and the
length of every honest response `µ`, `z` (for any view). -/
def BaseProtocol.Bounded (B : BaseProtocol) (F : QMAFamily) : Prop :=
  ∃ p : MvPolynomial (Fin 4) ℕ,
    (∀ lam T (r : Bits), r.length = B.genCoins lam T → (B.gen lam T r).1.length ≤ eval4 p lam T 0 0 ∧
      (B.gen lam T r).2.length ≤ eval4 p lam T 0 0) ∧
    (∀ lam T, B.chalLen lam T ≤ eval4 p lam T 0 0 ∧ B.copies lam T ≤ eval4 p lam T 0 0) ∧
    (∀ lam (x : Str) r μ c z, B.verdict lam x r μ c z = true →
      μ.length ≤ eval4 p lam (localCost F x) 0 0 ∧ z.length ≤ eval4 p lam (localCost F x) 0 0) ∧
    (∀ lam T n, ComputedOn
      (fun w => let l := unpack w
        [B.verdict lam (l.getD 0 []) (l.getD 1 []) (l.getD 2 []) (l.getD 3 []) (l.getD 4 [])])
      {w | ∃ (x : Str) (r : Bits) (μ c z : Bits), localCost F x ≤ T ∧
        r.length = B.genCoins lam T ∧ μ.length ≤ eval4 p lam T 0 0 ∧
        c.length = B.chalLen lam T ∧ z.length ≤ eval4 p lam T 0 0 ∧
        w = pack [x, (B.gen lam T r).2, μ, c, z]} n (eval4 p lam T 0 0)) ∧
    (∀ lam (x : Str), (B.core lam x).size ≤ eval4 p lam (localCost F x) 0 0) ∧
    (∀ lam (x : Str) (j : ℕ) (v : Bits),
      (B.toVerifier lam x j v).length ≤ eval4 p lam (localCost F x) 0 0)

/-- Overwhelming statistical completeness (§3.4, p.13; "In the batch construction, … `ε₀` is
negligible"): for every polynomial bound `B'` on the instance length there is a negligible `ν`
such that for every `λ`, every `x ∈ L_yes` with `|x| ≤ B'(λ)` and every witness
`ρ ∈ W_Q(x, 2/3)`, the honest execution with `W₀(x) = ρ^{⊗N}` accepts with probability at least
`1 − ν(λ)`. -/
def BaseProtocol.Complete (B : BaseProtocol) (L : PromiseProblem) (F : QMAFamily) : Prop :=
  ∀ B' : ℕ → ℕ, PolyBound B' → ∃ ν : ℕ → ℝ, Negligible ν ∧
    ∀ (lam : ℕ) (x : Str), x ∈ L.yes → x.length ≤ B' lam →
    ∀ ρ ∈ WQ F x (2 / 3), 1 - ν lam ≤ B.honestAccept F lam x ρ

/-- Negligible base soundness, Definition 3.7 (p.13) with `s₀ = 0`: for every polynomial bound
`B'`, every sequence of fixed no-instances `x_λ ∈ L_no` with `|x_λ| ≤ B'(λ)` and every QPT
adversary `(A₁, A₂)` (one `IsQPT` strategy whose two rounds are the stages, with quantum advice),
the acceptance probability is negligible. -/
def BaseProtocol.Sound (B : BaseProtocol) (L : PromiseProblem) (F : QMAFamily) : Prop :=
  ∀ B' : ℕ → ℕ, PolyBound B' → ∀ x : ℕ → Str, (∀ lam, x lam ∈ L.no ∧ (x lam).length ≤ B' lam) →
    ∀ Adv : ℕ → Strategy, IsQPT Adv →
      Negligible fun lam =>
        (Adv lam).acceptProb (B.verifierSeq x fun lam => localCost F (x lam)) lam

end FourMsgQMA


