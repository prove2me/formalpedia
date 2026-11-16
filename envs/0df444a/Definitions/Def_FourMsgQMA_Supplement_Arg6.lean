-- Prove2me | Definitions.Def_FourMsgQMA_Supplement_Arg6
-- name    : FourMsgQMA_Supplement_Arg6
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:24:05.20955+00:00
-- url     : https://prove2.me/theorems/677062f2-6e34-4dd5-9002-32282c187a37
-- title:
--   Six-message classical-verifier arguments for QMA: completeness, selective soundness (Def 3.4), public coins, succinctness
-- statement:
--   A **six-message argument** $\Pi=(\mathrm{Pre},V_1,P_1,V_2,P_2,V_3,P_3,\mathrm{Dec})$ for a QMA promise problem $L$ on common input $(1^\lambda,x,T)$ (§3.3 with $m=3$) has PPT verifier stages exchanging classical questions $q_1,q_2,q_3$ with a QPT prover's classical answers $a_1,a_2,a_3$, and a deterministic decision $\mathrm{Dec}(v_3,a_3)$.
--
--   1. **Completeness**: overwhelming acceptance for every $x\in L_{\mathrm{yes}}$ and the honest resource of $N(\lambda,T)$ copies of any $\rho\in W_Q(x,2/3)$.
--   2. **Selective soundness** $s$ (Definition 3.4): for every fixed sequence $x_\lambda\in L_{\mathrm{no}}$ and every QPT adversary,
--   $$
--   \Pr[b=1]\le s(\lambda)+\nu(\lambda)
--   $$
--   for a negligible $\nu$.
--   3. **Public coins except for the first message** (§3.3, following [GJM25]): $q_2$ and $q_3$ are fresh uniform strings of their prescribed lengths; the verifier may keep setup secrets for its decision.
--   4. **General-QMA succinctness** (§3.3): every message, and the work of every verifier stage, is at most $p(\lambda,|x|,\log(T+1))$ for one polynomial $p$; longer answers are rejected.
--   5. **Polynomially many copies**: $N(\lambda,T)\le\mathrm{poly}(\lambda,T)$.
--
--   These are the conclusions of Theorem 7.5.
--
--   **Formalization Note** As for the published `FourMsgQMA.Arg4`: verifier stages are deterministic maps of explicit uniform coins; $T=t_L(x)$; $\log$ is $\lceil\log_2\rceil$; work is circuit size on the inputs that occur.
-- source:
--   Goyal, Koppula, Four-Message Arguments for NP ∘ batchQMA and Six-Message Arguments for QMA from LWE, STOC 2027 submission (sha256 6c523d45…), §3.3, pp.11–12 (PDF 13–14); Definition 3.4, p.12 (PDF 14)

import Mathlib
import Definitions.Def_FourMsgQMA_WQ
import Definitions.Def_FourMsgQMA_Core
import Definitions.Def_FourMsgQMA_Supplement_HashFamily

namespace FourMsgQMA

/-!
Goyal, Koppula, STOC 2027 submission (sha256 6c523d45…), §3.3 (pp.11–12, PDF 13–14) and
Definition 3.4 (p.12, PDF 14) with `m = 3`: six-message classical-verifier arguments
`Π = (Pre, V₁, P₁, V₂, P₂, V₃, P₃, Dec)` for a QMA promise problem on common input `(1^λ, x, T)`,
their honest execution, selective soundness, public coins after setup, and general-QMA
succinctness.

Pinned-down version (operator request), as for the published `FourMsgQMA.Arg4`: the verifier stages
are deterministic maps of their inputs and explicit uniform coins; the honest prover is a quantum
core with two classical controllers, generated from `(1^λ, x)`, whose quantum input is
`N(λ, T)` copies of a witness `ρ ∈ W_Q(x, 2/3)`; the resource parameter is `T = t_L(x)`
(`localCost`); adversaries are the published `IsQPT` strategies.
-/

namespace Supplement

open QAlgorithms QAlgorithms.Complexity TightPQRepetition.Main

/-- A six-message argument (§3.3 with `m = 3`). -/
structure Arg6 where
  /-- The coin lengths of `Pre`, `V₁`, `V₂`, `V₃` at `(λ, |x|, T)`. -/
  coins0 : ℕ → ℕ → ℕ → ℕ
  /-- See `coins0`. -/
  coins1 : ℕ → ℕ → ℕ → ℕ
  /-- See `coins0`. -/
  coins2 : ℕ → ℕ → ℕ → ℕ
  /-- See `coins0`. -/
  coins3 : ℕ → ℕ → ℕ → ℕ
  /-- `v₀ ← Pre(1^λ, T, x)`, with coins. -/
  pre : ℕ → ℕ → Bits → Bits → Bits
  /-- `(q₁, v₁) ← V₁(v₀)`, with coins. -/
  v1 : ℕ → Bits → Bits → Bits × Bits
  /-- `(q₂, v₂) ← V₂(v₁, a₁)`, with coins. -/
  v2 : ℕ → Bits → Bits → Bits → Bits × Bits
  /-- `(q₃, v₃) ← V₃(v₂, a₂)`, with coins. -/
  v3 : ℕ → Bits → Bits → Bits → Bits × Bits
  /-- `b = Dec(v₃, a₃)`, deterministic. -/
  dec : ℕ → Bits → Bits → Bool
  /-- The number `N(λ, T)` of witness copies in the honest resource. -/
  copies : ℕ → ℕ → ℕ
  /-- The honest prover's quantum core, generated from `(λ, x)`. -/
  core : ℕ → Bits → Core
  /-- The honest controller writing into the core: `(λ, x, j, view)`. -/
  toCore : ℕ → Bits → ℕ → Bits → Bits
  /-- The honest controller computing the answers: `(λ, x, j, view)`. -/
  toVerifier : ℕ → Bits → ℕ → Bits → Bits

/-- The total number of verifier coins. -/
def Arg6.totalCoins (A : Arg6) (lam m T : ℕ) : ℕ :=
  A.coins0 lam m T + A.coins1 lam m T + A.coins2 lam m T + A.coins3 lam m T

/-- The verifier's coins split into those of `Pre`, `V₁`, `V₂`, `V₃`. -/
def Arg6.coinParts (A : Arg6) (lam m T : ℕ) (r : Bits) : Bits × Bits × Bits × Bits :=
  let a := A.coins0 lam m T
  let b := A.coins1 lam m T
  let c := A.coins2 lam m T
  (r.take a, (r.drop a).take b, (r.drop (a + b)).take c, (r.drop (a + b + c)).take (A.coins3 lam m T))

/-- `(q₁, v₁)` on `x` with resource parameter `T` and coins `r`. -/
def Arg6.stage1 (A : Arg6) (lam T : ℕ) (x r : Bits) : Bits × Bits :=
  let c := A.coinParts lam x.length T r
  A.v1 lam (A.pre lam T x c.1) c.2.1

/-- `(q₂, v₂)` after the answer `a₁`. -/
def Arg6.stage2 (A : Arg6) (lam T : ℕ) (x r a1 : Bits) : Bits × Bits :=
  A.v2 lam (A.stage1 lam T x r).2 a1 (A.coinParts lam x.length T r).2.2.1

/-- `(q₃, v₃)` after the answers `a₁, a₂`. -/
def Arg6.stage3 (A : Arg6) (lam T : ℕ) (x r a1 a2 : Bits) : Bits × Bits :=
  A.v3 lam (A.stage2 lam T x r a1).2 a2 (A.coinParts lam x.length T r).2.2.2

/-- The verifier of the experiment of §3.3 / Definition 3.4 on the instance sequence `x` with
resource parameter `T`, as a published `TightPQRepetition.Main.Verifier` (semantic carrier): three
rounds with `q₁, q₂, q₃` and verdict `Dec(v₃, a₃)`; all verifier coins are sampled before the
interaction and the input precedes them. -/
def Arg6.verifierSeq (A : Arg6) (x : ℕ → Str) (T : ℕ → ℕ) : Verifier where
  rounds := fun _ => 3
  coins := fun lam => A.totalCoins lam (x lam).length (T lam)
  qLen := fun _ _ => 0
  query := fun lam r j as =>
    if j = 0 then (A.stage1 lam (T lam) (x lam) r).1
    else if j = 1 then (A.stage2 lam (T lam) (x lam) r (as.getD 0 [])).1
    else (A.stage3 lam (T lam) (x lam) r (as.getD 0 []) (as.getD 1 [])).1
  verdict := fun lam r τ =>
    A.dec lam (A.stage3 lam (T lam) (x lam) r (τ.getD 0 ([], [])).2 (τ.getD 1 ([], [])).2).2
      (τ.getD 2 ([], [])).2

/-- The acceptance probability of the honest execution on `x` with the resource
`ρ^{⊗N(λ, t_L(x))}` on the first wires of the honest core (all other wires `|0⟩`). -/
noncomputable def Arg6.honestAccept (A : Arg6) (F : QMAFamily) (lam : ℕ) (x : Str)
    (ρ : Matrix (Qubits (F.wit x.length)) (Qubits (F.wit x.length)) ℂ) : ℝ :=
  let S := A.core lam x
  S.acceptMixed (A.toCore lam x) (A.toVerifier lam x)
    (A.verifierSeq (fun _ => x) (fun _ => localCost F x)) lam
    (loadedState (fun _ : Unit => F.wit x.length) (fun _ => ρ)
      (List.replicate (A.copies lam (localCost F x)) ()) S.n)

/-- Every algorithm is uniform and polynomial time (§3.3, p.11: "A PPT verifier …", "a QPT
prover", "A deterministic classical algorithm outputs an acceptance bit"): the coin lengths from
`(1^λ, 1^{|x|}, T)`, `Pre` from `(1^λ, T, x, coins)` (with `T` in binary), `V₁`, `V₂`, `V₃`, `Dec`
from their packed inputs, the honest core from `(1^λ, x)`, its controllers from
`(1^λ, x, 1^j, view)`, and `N(λ, T)` from `(1^λ, 1^T)`. -/
def Arg6.IsUniform (A : Arg6) : Prop :=
  (∃ g : Str → Str, PolyTimeComputable g ∧ ∀ lam m T,
      g (pack [unary lam, unary m, binNat T]) =
        pack [unary (A.coins0 lam m T), unary (A.coins1 lam m T), unary (A.coins2 lam m T),
          unary (A.coins3 lam m T)]) ∧
  (∃ g : Str → Str, PolyTimeComputable g ∧ ∀ lam T x r, g (pack [unary lam, binNat T, x, r]) = A.pre lam T x r) ∧
  (∃ g : Str → Str, PolyTimeComputable g ∧ ∀ lam v r,
      g (pack [unary lam, v, r]) = pack [(A.v1 lam v r).1, (A.v1 lam v r).2]) ∧
  (∃ g : Str → Str, PolyTimeComputable g ∧ ∀ lam v a r,
      g (pack [unary lam, v, a, r]) = pack [(A.v2 lam v a r).1, (A.v2 lam v a r).2]) ∧
  (∃ g : Str → Str, PolyTimeComputable g ∧ ∀ lam v a r,
      g (pack [unary lam, v, a, r]) = pack [(A.v3 lam v a r).1, (A.v3 lam v a r).2]) ∧
  (∃ g : Str → Str, PolyTimeComputable g ∧ ∀ lam v a, g (pack [unary lam, v, a]) = [A.dec lam v a]) ∧
  (∃ g : Str → Str, PolyTimeComputable g ∧ ∀ lam x, g (pack [unary lam, x]) = (A.core lam x).encode) ∧
  (∃ g : Str → Str, PolyTimeComputable g ∧ ∀ lam x j v,
      g (pack [unary lam, x, unary j, v]) = A.toCore lam x j v) ∧
  (∃ g : Str → Str, PolyTimeComputable g ∧ ∀ lam x j v,
      g (pack [unary lam, x, unary j, v]) = A.toVerifier lam x j v) ∧
  (∃ g : Str → Str, PolyTimeComputable g ∧ ∀ lam T, g (pack [unary lam, unary T]) = unary (A.copies lam T))

/-- Public coin except for the first message (§3.3, p.11, following [GJM25]): every later verifier
message is a fresh uniform string of the prescribed length, independent of the preceding
interaction: `V₂` and `V₃` send exactly their own fresh coins. The verifier may keep secrets from
setup in its state and use them in its decision. -/
def Arg6.PublicCoinAfterFirst (A : Arg6) : Prop :=
  ∀ lam (v a r : Bits), (A.v2 lam v a r).1 = r ∧ (A.v3 lam v a r).1 = r

/-- Overwhelming acceptance completeness (§3.3, p.11): for every polynomial bound `B'` on the
instance length there is a negligible `ν` such that for every `λ`, every `x ∈ L_yes` with
`|x| ≤ B'(λ)` and every `ρ ∈ W_Q(x, 2/3)`, the honest execution with `ρ^{⊗N(λ, T)}` accepts with
probability at least `1 − ν(λ)`. -/
def Arg6.Complete (A : Arg6) (L : PromiseProblem) (F : QMAFamily) : Prop :=
  ∀ B' : ℕ → ℕ, PolyBound B' → ∃ ν : ℕ → ℝ, Negligible ν ∧
    ∀ (lam : ℕ) (x : Str), x ∈ L.yes → x.length ≤ B' lam →
    ∀ ρ ∈ WQ F x (2 / 3), 1 - ν lam ≤ A.honestAccept F lam x ρ

/-- Selective computational soundness `s`, Definition 3.4 (p.12): for every polynomial bound `B'`,
every fixed sequence `x_λ ∈ L_no` with `|x_λ| ≤ B'(λ)` and every QPT adversary (one `IsQPT`
strategy whose three rounds are the stages, with one quantum advice state), there is a negligible
`ν` with acceptance probability at most `s(λ) + ν(λ)` for every `λ`. -/
def Arg6.Sound (A : Arg6) (L : PromiseProblem) (F : QMAFamily) (s : ℕ → ℝ) : Prop :=
  ∀ B' : ℕ → ℕ, PolyBound B' → ∀ x : ℕ → Str, (∀ lam, x lam ∈ L.no ∧ (x lam).length ≤ B' lam) →
    ∀ Adv : ℕ → Strategy, IsQPT Adv →
      ∃ ν : ℕ → ℝ, Negligible ν ∧ ∀ lam,
        (Adv lam).acceptProb (A.verifierSeq x fun lam => localCost F (x lam)) lam ≤ s lam + ν lam

/-- The instances of length `n` with `t_L(x) ≤ t`. -/
def lenClass (F : QMAFamily) (n t : ℕ) : Set Str := {x | x.length = n ∧ localCost F x ≤ t}

/-- General-QMA succinctness (§3.3, p.12: "Every message has length at most `p(λ, |x|, log(T + 1))`,
and total verifier work has the same bound"; §7.4, p.53: "This accounts for total verifier work,
including the first message"). There is one polynomial `p` such that, with `T = t_L(x)` and
`P = p(λ, |x|, ⌈log₂(T + 1)⌉)`, for every `λ`, every `x`, every outcome of the verifier's coins and
every transcript within the bounds:

1. `|q₁| ≤ P`, `|q₂| ≤ P` whenever `|a₁| ≤ P`, `|q₃| ≤ P` whenever `|a₁|, |a₂| ≤ P`;
2. the verifier rejects longer answers (if `Dec` accepts, `|a₁|, |a₂|, |a₃| ≤ P`), and every
   answer of the honest prover has length at most `P`;
3. the work of each of `Pre`, `V₁`, `V₂`, `V₃`, `Dec`: on the inputs that occur for the instances
   of length `n` with `t_L(x) ≤ t` (answers of length at most `P`), each is computed, at every input
   length, by Boolean circuits of total size at most `p(λ, n, ⌈log₂(t + 1)⌉)`. -/
def Arg6.Succinct (A : Arg6) (F : QMAFamily) : Prop :=
  ∃ p : MvPolynomial (Fin 4) ℕ,
    (∀ (lam : ℕ) (x : Str) (r : Bits), r.length = A.totalCoins lam x.length (localCost F x) →
      let T := localCost F x
      let P := eval4 p lam x.length (clog2 (T + 1)) 0
      (A.stage1 lam T x r).1.length ≤ P ∧
      (∀ a1 : Bits, a1.length ≤ P → (A.stage2 lam T x r a1).1.length ≤ P) ∧
      (∀ a1 a2 : Bits, a1.length ≤ P → a2.length ≤ P → (A.stage3 lam T x r a1 a2).1.length ≤ P) ∧
      (∀ a1 a2 a3 : Bits, A.dec lam (A.stage3 lam T x r a1 a2).2 a3 = true →
        a1.length ≤ P ∧ a2.length ≤ P ∧ a3.length ≤ P) ∧
      (∀ (j : ℕ) (v : Bits), (A.toVerifier lam x j v).length ≤ P)) ∧
    ∀ lam n t m : ℕ,
      let P := eval4 p lam n (clog2 (t + 1)) 0
      let occurs : (Str → Bits → Bits → Bits → Bits) → Set Bits := fun f =>
        {w | ∃ x ∈ lenClass F n t, ∃ r : Bits, r.length = A.totalCoins lam n (localCost F x) ∧
          ∃ a1 a2 : Bits, a1.length ≤ P ∧ a2.length ≤ P ∧ w = f x r a1 a2}
      ComputedOn (fun w => let l := unpack w; A.pre lam (bitsVal (l.getD 0 [])) (l.getD 1 []) (l.getD 2 []))
        (occurs fun x r _ _ => pack [binNat (localCost F x), x, (A.coinParts lam n (localCost F x) r).1]) m P ∧
      ComputedOn (fun w => let l := unpack w; let o := A.v1 lam (l.getD 0 []) (l.getD 1 []); pack [o.1, o.2])
        (occurs fun x r _ _ =>
          let c := A.coinParts lam n (localCost F x) r
          pack [A.pre lam (localCost F x) x c.1, c.2.1]) m P ∧
      ComputedOn (fun w => let l := unpack w
          let o := A.v2 lam (l.getD 0 []) (l.getD 1 []) (l.getD 2 []); pack [o.1, o.2])
        (occurs fun x r a1 _ =>
          pack [(A.stage1 lam (localCost F x) x r).2, a1, (A.coinParts lam n (localCost F x) r).2.2.1]) m P ∧
      ComputedOn (fun w => let l := unpack w
          let o := A.v3 lam (l.getD 0 []) (l.getD 1 []) (l.getD 2 []); pack [o.1, o.2])
        (occurs fun x r a1 a2 =>
          pack [(A.stage2 lam (localCost F x) x r a1).2, a2, (A.coinParts lam n (localCost F x) r).2.2.2]) m P ∧
      ComputedOn (fun w => let l := unpack w; [A.dec lam (l.getD 0 []) (l.getD 1 [])])
        {w | ∃ x ∈ lenClass F n t, ∃ r : Bits, r.length = A.totalCoins lam n (localCost F x) ∧
          ∃ a1 a2 a3 : Bits, a1.length ≤ P ∧ a2.length ≤ P ∧ a3.length ≤ P ∧
            w = pack [(A.stage3 lam (localCost F x) x r a1 a2).2, a3]} m P

/-- The honest prover uses polynomially many witness copies: `N(λ, T) ≤ p(λ, T)`. -/
def Arg6.CopiesPoly (A : Arg6) : Prop :=
  ∃ p : MvPolynomial (Fin 4) ℕ, ∀ lam T : ℕ, A.copies lam T ≤ eval4 p lam T 0 0

end Supplement

end FourMsgQMA


