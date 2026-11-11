-- Prove2me | Definitions.Def_KAQROM_Protocol
-- name    : KAQROM_Protocol
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:32:00.226193+00:00
-- url     : https://prove2.me/theorems/f1ab8446-f2de-4fc1-82f6-22c2927ff787
-- title:
--   Definition 3.10: multi-round key agreement with a classical-query prefix and its agreement probability $\alpha$
-- statement:
--   A **multi-round key-agreement protocol with a classical-query prefix** is $\Pi^{\mathrm{mr}}=((\mathcal A_i)_{i=1}^r,(\mathcal B_i)_{i=1}^{r-1},\mathcal B_{\mathsf q},\mathcal A_{\mathsf{fin}})$ with $r\ge1$. Alice and Bob start in an oracle-independent product state $\rho_{A,0}\otimes\rho_{B,0}$. In the prefix, Alice sends the messages $M_1,M_3,\dots,M_{2r-1}$ and Bob $M_2,\dots,M_{2r-2}$; all prefix queries and messages are classical. Let $M=(M_1,\dots,M_{2r-1})$, let $T_A,T_B$ be the parties' ordered query–answer transcripts and $S_A,S_B$ their residual registers. Then Bob runs $(\Psi,K_B)\leftarrow\mathcal B^H_{\mathsf q}(M,S_B)$, with $\Psi$ a possibly quantum message register and $K_B\in K\cup\{\bot\}$, and Alice runs $K_A\leftarrow\mathcal A^H_{\mathsf{fin}}(M,S_A,\Psi)$. The final stages make at most $q_{B,\mathsf q}$ and $q_{A,\mathsf{fin}}$ quantum queries.
--
--   Write $q_{A,\mathrm{pre}}=\max|T_A|$, $q_{B,\mathrm{pre}}=\max|T_B|$. The **valid agreement probability** is
--   $$
--   \alpha_{\Pi^{\mathrm{mr}}}=\Pr_{\mathsf{Real}_{\Pi^{\mathrm{mr}}}}[K_A=K_B\neq\bot],
--   $$
--   with $H\leftarrow\mathcal H$ uniform.
--
--   This is the class of protocols attacked by the goal theorem.
--
--   **Formalization Note** The security parameter is fixed. The registers and the Kraus index type are part of the protocol. Because the parties start in a product state and exchange only classical messages, the joint unnormalized state of a prefix branch is $\rho_A\otimes\rho_B$, computed per party; this is exact. Bob's final instrument maps onto $\Psi$ alone, since only $K_B$ and $\Psi$ are used afterwards. $q_{A,\mathrm{pre}}$, $q_{B,\mathrm{pre}}$ are maxima over every oracle and every prefix branch of positive probability. Keys are `Option K` with $\bot$ = `none`.
-- source:
--   Kitagawa–Nishimaki–Villányi–Yamakawa, Towards the Impossibility of Imperfectly Complete Key Agreement in the QROM, arXiv:2608.17610 (held version, sha256 ab8528fe…2c10), Definition 3.10, pp.21–22

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_KAQROM_Instrument
import Definitions.Def_KAQROM_Oracle
import Definitions.Def_KAQROM_QAlg
import Definitions.Def_KAQROM_PrefixParty

namespace KAQROM

open Matrix
open scoped Kronecker

/-- **Definition 3.10 (Multi-round key agreement with a classical-query prefix).** A protocol
`Π^{mr} = ((A_i)_{i=1}^r, (B_i)_{i=1}^{r-1}, B_q, A_fin)` relative to the random oracle
`H : X → {0,1}^ℓ`, with classical messages in `Msg` and non-abort keys in `K` (abort `⊥` is
`none : Option K`):

* `r ≥ 1` is the number of prefix messages sent by Alice; the prefix has `2r − 1` classical
  messages `M₁, …, M_{2r−1}`, Alice sending the odd-numbered ones (stages `0, 2, …` in 0-based
  indexing) and Bob the even-numbered ones;
* Alice and Bob start in an oracle-independent product state `ρ_{A,0} ⊗ ρ_{B,0}` on registers
  `RA`, `RB`; during the prefix they make only classical oracle queries (`alice`, `bob`);
* Bob's final stage `B_q(M, S_B)` is a `qBq`-query quantum algorithm on his residual register,
  with classical output `K_B ∈ K ∪ {⊥}` and output register `Ψ` (the possibly quantum message);
* Alice's final stage `A_fin(M, S_A, Ψ)` is a `qAfin`-query quantum algorithm on her residual
  register and `Ψ`, with classical output `K_A ∈ K ∪ {⊥}`.

Kitagawa–Nishimaki–Villányi–Yamakawa, *Towards the Impossibility of Imperfectly Complete Key
Agreement in the QROM*, arXiv:2608.17610 (held version, sha256 ab8528fe…2c10), Definition 3.10,
pp.21–22.

**Formalization Note.** The security parameter is fixed and `1^λ` arguments are dropped. The
register types and the Kraus index type are part of the protocol. `qBq` and `qAfin` are the
numbers of query rounds of `B_q` and `A_fin` (worst-case query bounds; see `QAlg`). Bob's final
instrument maps onto `Ψ` alone: whatever else Bob keeps is traced out, as only `K_B` and `Ψ` are
used afterwards. The prefix stages `A_i`, `B_i` are the stages of `alice`, `bob` selected by the
length of the public transcript. -/
structure Protocol (X : Type) [Fintype X] [DecidableEq X] (ℓ : ℕ) (Msg K : Type) [Fintype Msg]
    [DecidableEq Msg] [Fintype K] where
  /-- Alice's register. -/
  RA : Type
  /-- Bob's register. -/
  RB : Type
  /-- The register of Bob's final (possibly quantum) message `Ψ`. -/
  Ψ : Type
  /-- Work register of `A_fin`. -/
  WA : Type
  /-- Work register of `B_q`. -/
  WB : Type
  /-- Kraus index type of every instrument of the protocol. -/
  ι : Type
  [fRA : Fintype RA] [dRA : DecidableEq RA]
  [fRB : Fintype RB] [dRB : DecidableEq RB]
  [fΨ : Fintype Ψ] [dΨ : DecidableEq Ψ]
  [fWA : Fintype WA] [dWA : DecidableEq WA]
  [fWB : Fintype WB] [dWB : DecidableEq WB]
  [fι : Fintype ι]
  /-- The number `r ≥ 1` of prefix messages sent by Alice. -/
  r : ℕ
  one_le_r : 1 ≤ r
  /-- The number of classical query steps per prefix stage. -/
  D : ℕ
  /-- Alice's initial state `ρ_{A,0}`. -/
  ρA0 : Matrix RA RA ℂ
  /-- Bob's initial state `ρ_{B,0}`. -/
  ρB0 : Matrix RB RB ℂ
  ρA0_density : WildeQIT.IsDensityOperator ρA0
  ρB0_density : WildeQIT.IsDensityOperator ρB0
  /-- Alice's prefix stages `A_1, …, A_r` (classical queries, classical messages). -/
  alice : PrefixParty X ℓ Msg RA ι D
  /-- Bob's prefix stages `B_1, …, B_{r−1}` (classical queries, classical messages). -/
  bob : PrefixParty X ℓ Msg RB ι D
  /-- The query bound `q_{B,q}` of Bob's final stage. -/
  qBq : ℕ
  /-- The query bound `q_{A,fin}` of Alice's final stage. -/
  qAfin : ℕ
  /-- Bob's final stage `(Ψ, K_B) ← B_q^H(M, S_B)`. -/
  Bq : (Fin (2 * r - 1) → Msg) → QAlg X ℓ RB WB Ψ (Option K) ι qBq
  /-- Alice's final stage `K_A ← A_fin^H(M, S_A, Ψ)`. -/
  Afin : (Fin (2 * r - 1) → Msg) → QAlg X ℓ (RA × Ψ) WA Unit (Option K) ι qAfin

attribute [instance] Protocol.fRA Protocol.dRA Protocol.fRB Protocol.dRB Protocol.fΨ Protocol.dΨ
  Protocol.fWA Protocol.dWA Protocol.fWB Protocol.dWB Protocol.fι

namespace Protocol

variable {X : Type} [Fintype X] [DecidableEq X] {ℓ : ℕ} {Msg K : Type} [Fintype Msg]
  [DecidableEq Msg] [Fintype K]

/-- The number `2r − 1` of prefix messages. -/
abbrev n (P : Protocol X ℓ Msg K) : ℕ := 2 * P.r - 1

/-- The classical outcomes of the whole prefix: for each of the `2r − 1` stages, the outcomes of
its `D` query steps and the message sent. -/
abbrev Outcome (P : Protocol X ℓ Msg K) := Fin P.n → (Fin P.D → Option X) × Msg

/-- The complete public prefix transcript `M = (M₁, …, M_{2r−1})` of a prefix outcome. -/
def msgs (P : Protocol X ℓ Msg K) (o : P.Outcome) : Fin P.n → Msg := fun i => (o i).2

/-- Alice's prefix run (she acts in stages `0, 2, 4, …`): her unnormalized residual state `S_A`
and her complete ordered query–answer transcript `T_A`. -/
noncomputable def aliceRun (P : Protocol X ℓ Msg K) (H : Oracle X ℓ) (o : P.Outcome) :
    Matrix P.RA P.RA ℂ × Transcript X ℓ :=
  P.alice.run H (fun i => i % 2 = 0) P.n o P.ρA0

/-- Bob's prefix run (he acts in stages `1, 3, …`): his unnormalized residual state `S_B` and his
complete ordered query–answer transcript `T_B`. -/
noncomputable def bobRun (P : Protocol X ℓ Msg K) (H : Oracle X ℓ) (o : P.Outcome) :
    Matrix P.RB P.RB ℂ × Transcript X ℓ :=
  P.bob.run H (fun i => i % 2 = 1) P.n o P.ρB0

/-- The probability weight of the prefix branch `o` under oracle `H` (not yet divided by `|ℋ|`):
`Tr ρ_A · Tr ρ_B`. Since the parties start in a product state and exchange only classical
messages, the joint unnormalized state of the branch is `ρ_A ⊗ ρ_B`. -/
noncomputable def weight (P : Protocol X ℓ Msg K) (H : Oracle X ℓ) (o : P.Outcome) : ℝ :=
  (P.aliceRun H o).1.trace.re * (P.bobRun H o).1.trace.re

/-- `q_{A,pre} := max |T_A|`, the maximum over every oracle and every prefix branch of positive
probability (Definition 3.10, p.22). -/
noncomputable def qApre (P : Protocol X ℓ Msg K) : ℕ := by
  classical
  exact Finset.univ.sup (fun p : Oracle X ℓ × P.Outcome =>
    if 0 < P.weight p.1 p.2 then (P.aliceRun p.1 p.2).2.length else 0)

/-- `q_{B,pre} := max |T_B|`, the maximum over every oracle and every prefix branch of positive
probability (Definition 3.10, p.22). -/
noncomputable def qBpre (P : Protocol X ℓ Msg K) : ℕ := by
  classical
  exact Finset.univ.sup (fun p : Oracle X ℓ × P.Outcome =>
    if 0 < P.weight p.1 p.2 then (P.bobRun p.1 p.2).2.length else 0)

/-- **The valid agreement probability** `α_{Π^{mr}} = Pr_{Real_{Π^{mr}}}[K_A = K_B ≠ ⊥]`
(Definition 3.10, p.22) of the honest experiment: `H ← ℋ` uniform, the honest prefix, Bob's
final stage on `S_B` (outcome `K_B = some k`, message `Ψ`), then Alice's final stage on `S_A ⊗ Ψ`
(outcome `K_A = some k`). -/
noncomputable def alpha (P : Protocol X ℓ Msg K) : ℝ :=
  (Fintype.card (Oracle X ℓ) : ℝ)⁻¹ * ∑ H : Oracle X ℓ, ∑ o : P.Outcome, ∑ k : K,
    ((P.Afin (P.msgs o)).run H
        ((P.aliceRun H o).1 ⊗ₖ (P.Bq (P.msgs o)).run H (P.bobRun H o).1 (some k))
        (some k)).trace.re

end Protocol

end KAQROM


