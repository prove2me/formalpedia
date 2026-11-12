-- Prove2me | Definitions.Def_PoQHierarchy_Main_Compiled
-- name    : PoQHierarchy_Main_Compiled
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T06:52:25.723573+00:00
-- url     : https://prove2.me/theorems/17af3a86-647d-4f04-a1f5-4e9c0da77b50
-- title:
--   The KLVY compiled games $G_{\mathrm{comp}}$ and $G_{\mathrm{all\text{-}comp}}$, and non-adaptive provers
-- statement:
--   Fix a QFHE scheme and an $n$-player game $G$. A question $x_i$ is sent as its fixed-length code, and an answer is valid if it is the code of an element of $O_i$. The **compiled game** (Fig. 4, p.22), at security parameter $\lambda$, runs as follows; the prover receives $1^\lambda$.
--
--   1. The verifier samples $x\leftarrow\mu$ and $sk_i\leftarrow\mathsf{Gen}(1^\lambda)$ for every encrypted round.
--   2. In round $i$ it sends $\mathsf{Enc}(sk_i,x_i)$, or $x_i$ in the clear, and receives $\alpha_i$. The first question opens the interaction, and after the $n$-th answer the interaction is closed.
--   3. It decrypts $a_i=\mathsf{Dec}(sk_i,\alpha_i)$ in the encrypted rounds and reads $a_i=\alpha_i$ in the clear ones. An invalid answer loses.
--   4. The prover wins iff it sent exactly $n$ answers and $V(a_1,\dots,a_n,x_1,\dots,x_n)=1$.
--
--   In $G_{\mathrm{comp}}$ rounds $1,\dots,n-1$ are encrypted under independent keys and the last question is sent in the clear. In $G_{\mathrm{all\text{-}comp}}$ (p.23) every round is encrypted, with a fresh key $sk_n$. $\Pr[P\text{ wins }G^\lambda_{\mathrm{comp}}]$ is taken over the verifier's sampling and keys, the prover's coins and the device's measurement outcomes.
--
--   A prover is **non-adaptive with schedule $b\in B(n,k)$** (§4.2, p.26) if, for every $\lambda$, all coins and every transcript, it invokes the device only inside round $i$ (after receiving question $i$ and before answering it) when $b_i=1$, at most once there, and answers question $i$ only after exactly $b_i$ invocations in that round.
--
--   **Formalization Note** In the compiled game the verifier decrypts with $\mathsf{Dec}$, a $\mathsf{QPT}$ algorithm, as Definition 3.3 allows. The game is defined as a winning probability, not as a verifier machine.
-- source:
--   Kaniuar Bacho, Dominik Leichtle, Atul Singh Arora, Alexandru Cojocaru, STOC 2027 submission #1666 (October 2026), Fig. 4 (p.22), Remark 3.5 (p.22), p.23 (G_all-comp), §4.2 (pp.25–26); canonical PDF sha256 3009a0afeb95e5789f4e029db39d01935081f03d75e7fa263cb4b408aed40fb1

import Mathlib
import Definitions.Def_PoQHierarchy_Main_QFHE
import Definitions.Def_PoQHierarchy_Main_NonlocalGame

open QAlgorithms.Complexity
set_option autoImplicit false

namespace PoQHierarchy.Main

/-!
Bacho, Leichtle, Arora, Cojocaru, STOC 2027 submission #1666, §3.3 (Fig. 4, p.22; p.23) and §4.2
(pp.25–26): the KLVY compiled games `G_comp` and `G_all-comp`, a prover's winning probability, and
non-adaptive provers with a fixed query schedule.

The question `x_i ∈ Fin (q i)` is sent as its fixed-length code `codeFin (q i) x_i`; an answer is
valid if it is the code of an element of `Fin (o i)`. Round `i` uses a fresh key `sk_i ← Gen(1^λ)`
if it is encrypted. The prover receives `1^λ`, gets the first (encrypted) question as the opening
message, and after its `n`-th answer the interaction is closed. It wins iff it sent exactly `n`
answers, every decryption is a valid answer and `V(a, x) = 1`.
-/

namespace NonlocalGame

variable {n : ℕ} (G : NonlocalGame n)

/-- Reading the answers off the decryptions: `some a` if every decryption is the code of an
element of the answer set, `none` otherwise (an invalid decryption loses). -/
def decodeAnswers (ys : List (Option Str)) : Option ((i : Fin n) → Fin (G.o i)) :=
  if h : ∀ i : Fin n, ((ys.getD i.val none).bind (decodeFin (G.o i))).isSome then
    some fun i => ((ys.getD i.val none).bind (decodeFin (G.o i))).get (h i)
  else none

end NonlocalGame

/-- The verifier as an environment: it opens with the first message and answers the prover's
`j`-th message (for `j < n`) with message `j + 1`; after the `n`-th answer it closes. -/
def roundsEnv (n : ℕ) (msgs : List Str) : Env := fun sent =>
  if sent.length < n then WList.pure (some (msgs.getD sent.length [])) else WList.pure none

/-- The winning probability `Pr[P wins G_comp^λ]` of a prover `P` in the KLVY compilation of `G`
under the scheme `Sch`, where `enc i` says whether round `i` is encrypted:
1. sample `x ← μ` and `sk_i ← Gen(1^λ)` for the encrypted rounds;
2. in round `i` send `Enc(sk_i, x_i)` (or `x_i` in the clear) and receive `α_i`;
3. decrypt `a_i = Dec(sk_i, α_i)` (or read `a_i = α_i`); an invalid answer loses;
4. the prover wins iff `V(a, x) = 1`. -/
noncomputable def compiledWin {n : ℕ} (Sch : QFHE) (G : NonlocalGame n) (enc : Fin n → Bool)
    (P : IntMachine) (lam : ℕ) : ℝ :=
  ∑ x, G.μ x *
    (WList.seq ((List.finRange n).map fun i =>
        if enc i then Sch.genDist lam else WList.pure [])).expect fun sks =>
    (WList.seq ((List.finRange n).map fun i =>
        if enc i then Sch.encDist lam (sks.getD i.val []) (codeFin (G.q i) (x i))
        else WList.pure (codeFin (G.q i) (x i)))).expect fun cts =>
    (P.outcomes (unary lam) (roundsEnv n cts)).expect fun res =>
      if res.1 = .finished ∧ res.2.length = n then
        (WList.seq ((List.finRange n).map fun i =>
            if enc i then Sch.decDist lam (sks.getD i.val []) (res.2.getD i.val [])
            else WList.pure (some (res.2.getD i.val [])))).prob fun ys =>
          match G.decodeAnswers ys with
          | some a => G.V a x
          | none => false
      else 0

/-- `Pr[P^λ wins G_comp^λ]`: the KLVY compiled game of Fig. 4, questions `1, …, n-1` encrypted under
independent keys and the last question in the clear. -/
noncomputable def winComp {n : ℕ} (Sch : QFHE) (G : NonlocalGame n) (P : IntMachine) (lam : ℕ) :
    ℝ :=
  compiledWin Sch G (fun i => decide (i.val + 1 < n)) P lam

/-- `Pr[P wins G_all-comp^λ]`: the fully encrypted variant of p.23, with a fresh key `sk_n` for the
last question too. -/
noncomputable def winAllComp {n : ℕ} (Sch : QFHE) (G : NonlocalGame n) (P : IntMachine)
    (lam : ℕ) : ℝ :=
  compiledWin Sch G (fun _ => true) P lam

/-! ### Non-adaptive provers (§4.2) -/

/-- A prover is **non-adaptive with schedule `b ∈ B(n,k)`** (§4.2, p.26): in every execution, for
every `λ`, all coins and every transcript, it invokes the device only inside round `j` (after
receiving question `j` and before answering it) when `b_j = 1`, at most once there, and it answers
question `j` only after exactly `b_j` invocations in round `j`. -/
def IntMachine.NonAdaptive {n k : ℕ} (P : IntMachine) (b : Schedule n k) : Prop :=
  ∀ (lam : ℕ) (r : Str) (hist : List Event), P.Consistent (unary lam) r hist →
    let j := (hist.filter Event.isSent).length
    let cur := ((hist.reverse.takeWhile fun e => !e.isRecv).filter Event.isQuery).length
    (∀ c, P.action (unary lam) r hist = .query c →
      ∃ h : j < n, (hist.filter Event.isRecv).length = j + 1 ∧ b.val ⟨j, h⟩ = true ∧ cur = 0) ∧
    (∀ a, P.action (unary lam) r hist = .send a →
      ∃ h : j < n, (hist.filter Event.isRecv).length = j + 1 ∧
        cur = if b.val ⟨j, h⟩ then 1 else 0)

end PoQHierarchy.Main


