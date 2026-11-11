-- Prove2me | Definitions.Def_KAQROM_ClassicalProtocol
-- name    : KAQROM_ClassicalProtocol
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:31:46.199246+00:00
-- url     : https://prove2.me/theorems/04fdfddc-5440-4f64-b6b7-4795be056f08
-- title:
--   Classical two-party random-oracle protocols, the views $U_P$, the conditional distributions $\mu_{m,h}$ and $\Delta_{\mathrm{TV}}$
-- statement:
--   A **classical two-party random-oracle protocol** has parties Alice and Bob that are deterministic functions of their private randomness $R_A,R_B$ (drawn independently from distributions on finite sets), of the public transcript so far and of their own query–answer transcript so far. The parties alternate messages, Alice first; before each message the sender makes some classical oracle queries. With $H\leftarrow\mathcal H$ uniform and independent of the randomness, the execution produces the complete public transcript $M$ and the transcripts $T_A,T_B$; the views are $U_P=(R_P,M,T_P)$.
--
--   For a deterministic classical-query algorithm $L$ on transcripts and a pair $(m,h)$, $\mu^{AB}_{m,h}$ is the conditional distribution of $(U_A,U_B)$ given $M=m$ and $L^H(m)=h$, with marginals $\mu^A_{m,h},\mu^B_{m,h}$; $\Pr[x\in\mathrm{Dom}(T_P)\mid M=m,h]$ are the conditional query probabilities. The product of two distributions and the total variation distance $\Delta_{\mathrm{TV}}(\mu,\nu)=\tfrac12\sum_z|\mu(z)-\nu(z)|$ complete the vocabulary of Lemma 5.10.
--
--   **Formalization Note** Since $M=m$ is fixed by the conditioning, a view is stored as $(R_P,T_P)$. Alternation with Alice first and a fixed number of query steps per message (with "no query" allowed) lose nothing: dummy messages and idle steps pad any protocol. Private randomness ranges over finite sets, as for the random tapes of [BMG17] and for the exact classical simulation of §5.2.1.
-- source:
--   Kitagawa–Nishimaki–Villányi–Yamakawa, Towards the Impossibility of Imperfectly Complete Key Agreement in the QROM, arXiv:2608.17610 (held version, sha256 ab8528fe…2c10), Lemma 5.10, p.34; §5.2.1, p.32

import Mathlib
import Definitions.Def_KAQROM_Oracle
import Definitions.Def_KAQROM_QueryTree

namespace KAQROM

/-- **A classical two-party random-oracle protocol** (Lemma 5.10, p.34; [BMG17, §3.1]): Alice and
Bob are deterministic functions of their private randomness `R_A`, `R_B` (finite sets with
probability mass functions `pA`, `pB`), of the public transcript so far and of their own oracle
query–answer transcript so far. There are `nMsg` messages; Alice sends the messages of even
(0-based) index and Bob the others. Before each of its messages the sender makes `D` query steps,
each either a query `some x` or no query.

Kitagawa–Nishimaki–Villányi–Yamakawa, *Towards the Impossibility of Imperfectly Complete Key
Agreement in the QROM*, arXiv:2608.17610 (held version, sha256 ab8528fe…2c10), Lemma 5.10, p.34.

**Formalization Note.** Alternation with Alice first loses nothing: a protocol where Bob speaks
first, or a party speaks twice in a row, gets a constant dummy message. -/
structure ClassicalProtocol (X : Type) [Fintype X] (ℓ : ℕ) (Msg : Type) where
  /-- Alice's private randomness. -/
  RndA : Type
  /-- Bob's private randomness. -/
  RndB : Type
  [fA : Fintype RndA]
  [fB : Fintype RndB]
  /-- The distribution of Alice's randomness. -/
  pA : RndA → ℝ
  /-- The distribution of Bob's randomness. -/
  pB : RndB → ℝ
  pA_nonneg : ∀ r, 0 ≤ pA r
  pA_sum : ∑ r, pA r = 1
  pB_nonneg : ∀ r, 0 ≤ pB r
  pB_sum : ∑ r, pB r = 1
  /-- The number of messages. -/
  nMsg : ℕ
  /-- Query steps per message. -/
  D : ℕ
  /-- Alice's next query (or none), given her randomness, the public and her own transcript. -/
  queryA : RndA → List Msg → Transcript X ℓ → Fin D → Option X
  /-- Alice's message. -/
  sendA : RndA → List Msg → Transcript X ℓ → Msg
  /-- Bob's next query (or none). -/
  queryB : RndB → List Msg → Transcript X ℓ → Fin D → Option X
  /-- Bob's message. -/
  sendB : RndB → List Msg → Transcript X ℓ → Msg

attribute [instance] ClassicalProtocol.fA ClassicalProtocol.fB

namespace ClassicalProtocol

variable {X : Type} [Fintype X] [DecidableEq X] {ℓ : ℕ} {Msg : Type}

/-- One classical stage: `D` query steps on the transcript `t`, then the message. -/
def cstage {D : ℕ} (query : List Msg → Transcript X ℓ → Fin D → Option X)
    (send : List Msg → Transcript X ℓ → Msg) (H : Oracle X ℓ) (pub : List Msg)
    (t : Transcript X ℓ) : Transcript X ℓ × Msg :=
  let t' := (List.finRange D).foldl
    (fun s k => s ++ ((query pub s k).map (fun x => (x, H x))).toList) t
  (t', send pub t')

/-- The execution with oracle `H` and randomness `rA`, `rB`: the complete public transcript `M`
and the two query–answer transcripts `T_A`, `T_B`. -/
def exec (P : ClassicalProtocol X ℓ Msg) (H : Oracle X ℓ) (rA : P.RndA) (rB : P.RndB) :
    List Msg × Transcript X ℓ × Transcript X ℓ :=
  (List.range P.nMsg).foldl
    (fun s i => if i % 2 = 0 then
        let a := cstage (P.queryA rA) (P.sendA rA) H s.1 s.2.1
        (s.1 ++ [a.2], a.1, s.2.2)
      else
        let b := cstage (P.queryB rB) (P.sendB rB) H s.1 s.2.2
        (s.1 ++ [b.2], s.2.1, b.1))
    ([], [], [])

/-- The probability weight of `(H, rA, rB)`: `H ← ℋ` uniform, independent of the randomness. -/
noncomputable def weight (P : ClassicalProtocol X ℓ Msg) (rA : P.RndA) (rB : P.RndB) : ℝ :=
  (Fintype.card (Oracle X ℓ) : ℝ)⁻¹ * P.pA rA * P.pB rB

/-- `Pr[M = m, L^H(m) = h]`. -/
noncomputable def probMH (P : ClassicalProtocol X ℓ Msg) (L : QueryTree (List Msg) X ℓ)
    (m : List Msg) (h : PartialOracle X ℓ) : ℝ := by
  classical
  exact ∑ H : Oracle X ℓ, ∑ rA : P.RndA, ∑ rB : P.RndB,
    if (P.exec H rA rB).1 = m ∧ L.output H m = h then P.weight rA rB else 0

/-- **`μ^{AB}_{m,h}`**: the conditional distribution of the views `(U_A, U_B)`,
`U_P = (R_P, M, T_P)`, given `M = m, L^H(m) = h` (Lemma 5.10, p.34).

**Formalization Note.** `M = m` is fixed by the conditioning, so each view is stored as
`(R_P, T_P)`. -/
noncomputable def muAB (P : ClassicalProtocol X ℓ Msg) (L : QueryTree (List Msg) X ℓ)
    (m : List Msg) (h : PartialOracle X ℓ) :
    (P.RndA × Transcript X ℓ) × (P.RndB × Transcript X ℓ) →₀ ℝ := by
  classical
  exact (P.probMH L m h)⁻¹ • ∑ H : Oracle X ℓ, ∑ rA : P.RndA, ∑ rB : P.RndB,
    if (P.exec H rA rB).1 = m ∧ L.output H m = h then
      Finsupp.single ((rA, (P.exec H rA rB).2.1), (rB, (P.exec H rA rB).2.2)) (P.weight rA rB)
    else 0

/-- Alice's marginal `μ^A_{m,h}`. -/
noncomputable def muA (P : ClassicalProtocol X ℓ Msg) (L : QueryTree (List Msg) X ℓ)
    (m : List Msg) (h : PartialOracle X ℓ) : P.RndA × Transcript X ℓ →₀ ℝ :=
  (P.muAB L m h).sum (fun c v => Finsupp.single c.1 v)

/-- Bob's marginal `μ^B_{m,h}`. -/
noncomputable def muB (P : ClassicalProtocol X ℓ Msg) (L : QueryTree (List Msg) X ℓ)
    (m : List Msg) (h : PartialOracle X ℓ) : P.RndB × Transcript X ℓ →₀ ℝ :=
  (P.muAB L m h).sum (fun c v => Finsupp.single c.2 v)

/-- `Pr[x ∈ Dom(T_A) | M = m, L^H(m) = h]`. -/
noncomputable def condQueriedA (P : ClassicalProtocol X ℓ Msg) (L : QueryTree (List Msg) X ℓ)
    (m : List Msg) (h : PartialOracle X ℓ) (x : X) : ℝ := by
  classical
  exact (P.probMH L m h)⁻¹ * ∑ H : Oracle X ℓ, ∑ rA : P.RndA, ∑ rB : P.RndB,
    if (P.exec H rA rB).1 = m ∧ L.output H m = h ∧ x ∈ (P.exec H rA rB).2.1.dom then
      P.weight rA rB else 0

/-- `Pr[x ∈ Dom(T_B) | M = m, L^H(m) = h]`. -/
noncomputable def condQueriedB (P : ClassicalProtocol X ℓ Msg) (L : QueryTree (List Msg) X ℓ)
    (m : List Msg) (h : PartialOracle X ℓ) (x : X) : ℝ := by
  classical
  exact (P.probMH L m h)⁻¹ * ∑ H : Oracle X ℓ, ∑ rA : P.RndA, ∑ rB : P.RndB,
    if (P.exec H rA rB).1 = m ∧ L.output H m = h ∧ x ∈ (P.exec H rA rB).2.2.dom then
      P.weight rA rB else 0

end ClassicalProtocol

/-- The product `μ × ν` of two finitely supported distributions. -/
noncomputable def prodDist {α β : Type} (μ : α →₀ ℝ) (ν : β →₀ ℝ) : α × β →₀ ℝ :=
  μ.sum (fun a v => ν.sum (fun b w => Finsupp.single (a, b) (v * w)))

/-- The total variation distance `Δ_TV(μ, ν) = ½ ∑_z |μ(z) − ν(z)|`. -/
noncomputable def tvDist {α : Type} (μ ν : α →₀ ℝ) : ℝ :=
  (1 / 2 : ℝ) * (μ - ν).sum (fun _ v => |v|)

end KAQROM


