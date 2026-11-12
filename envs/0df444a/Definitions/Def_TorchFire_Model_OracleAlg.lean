-- Prove2me | Definitions.Def_TorchFire_Model_OracleAlg
-- name    : TorchFire_Model_OracleAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:33:50.680474+00:00
-- url     : https://prove2.me/theorems/9d22ca45-8bc7-4790-9953-dd22796ea9c4
-- title:
--   Query-bounded quantum oracle algorithms with quantum input
-- statement:
--   A **$T$-query quantum oracle algorithm with quantum input** (§3, p.18, with Fact 3.1). The algorithm has an input register $I$, the query and answer registers $D,\kappa$ of an oracle collection, and a finite workspace $W$ of its own choosing. It starts from $\rho_I\otimes|\mathrm{init}\rangle\langle\mathrm{init}|$ and applies
--   $$U^O = G_T\,O\,G_{T-1}\cdots G_1\,O\,G_0,$$
--   where $G_0,\dots,G_T$ are unitaries that **do not depend on the oracle** and $O$ is the superposition oracle of the collection. A designated output register is kept and the rest is traced out; a classical output is the computational-basis measurement of the output register.
--
--   Classical inputs are modelled by families of algorithms indexed by the classical input. Intermediate measurements and classical randomness are deferred, as in Fact 3.1.
--
--   This is the adversary model of every security statement of the mission: the number of queries $T$ is the only resource that is bounded.
--
--   **Formalization Note** No uniformity, gate count or workspace bound is imposed (paper.md decision 2). Every QPT oracle algorithm is such an algorithm with polynomially many queries ("each oracle query counts as one gate; in particular, its total number of oracle queries is polynomially bounded", p.18), so a security statement against this class implies the paper's.
-- source:
--   Chatterjee, Mukherjee, Pathak, Podder, Quantum Fire with Delegated Cloning, arXiv:2610.03593 (held version, sha256 4e43d2f2…afd593), §3 Query-Bounded Quantum Algorithms and QPT, Fact 3.1, p.18

import Mathlib
import Definitions.Def_TorchFire_Model_traceDist
import Definitions.Def_TorchFire_Model_xorOracle

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 2048

open Matrix

namespace TorchFire.Model

/-- **Interleaving unitaries and queries.** `evolve G Q t = G_t Q_{t−1} G_{t−1} ⋯ G_1 Q_0 G_0`: the
unitary part of a computation up to (and including) the `t`-th inter-query unitary, with the
`j`-th query (`0`-based) applied as `Q_j`. With `t = T` this is the full computation
`U^O = G_T O_T G_{T−1} ⋯ G_1 O_1 G_0` of §3 (p.18); with `t = j` it is the prefix `U_{<j+1}` before
the `(j+1)`-th query ((67), p.60). -/
def evolve {S : Type} [Fintype S] (G : ℕ → Matrix S S ℂ) (Q : ℕ → Matrix S S ℂ) :
    ℕ → Matrix S S ℂ
  | 0 => G 0
  | t + 1 => G (t + 1) * Q t * evolve G Q t

/-- **A query-bounded quantum oracle algorithm with quantum input** (Chatterjee–Mukherjee–Pathak–
Podder, *Quantum Fire with Delegated Cloning*, arXiv:2610.03593, held version sha256
4e43d2f2…afd593, §3 "Query-Bounded Quantum Algorithms" and Fact 3.1, p.18; paper.md decision 2).

The algorithm has an input register `I`, a query register `D` and answer register `κ` for the
oracle collection, and a workspace `W` of its own choosing. It starts from `ρ_I ⊗ |init⟩⟨init|` and
applies `U^O = G_T O G_{T−1} ⋯ G_1 O G_0`, where `G_0, …, G_T` are unitaries that **do not depend on
the oracle** and `O = I_I ⊗ O_f ⊗ I_W` is the XOR oracle of the collection `f`. The output register
`O` is designated by the bijection `uv : O × Junk → I × (D × κ) × W`; the rest is traced out.

Classical inputs are modelled by families of algorithms (a function from the classical input to
`OracleAlg`), so the unitaries and even the workspace may depend on them. Intermediate measurements
and classical randomness are deferred (Fact 3.1). A classical output is the computational-basis
measurement of `O` (the diagonal of the output state).

**Formalization Note** No uniformity, gate count or workspace bound is imposed; only the number of
queries `T` is bounded where a statement requires it. This class contains every QPT oracle algorithm
("each oracle query counts as one gate; in particular, its total number of oracle queries is
polynomially bounded", p.18), so a security statement against it implies the paper's. The algorithm
interacts with the oracle only through queries. -/
structure OracleAlg (I O D κ : Type) [Fintype I] [DecidableEq I] [Fintype D] [DecidableEq D]
    [Fintype κ] [DecidableEq κ] where
  /-- The workspace register. -/
  W : Type
  [instFintypeW : Fintype W]
  [instDecEqW : DecidableEq W]
  /-- The number of oracle queries. -/
  T : ℕ
  /-- The oracle-independent unitaries `G_0, …, G_T`. -/
  G : Fin (T + 1) → Matrix.unitaryGroup (I × (D × κ) × W) ℂ
  /-- The initial basis state of the query, answer and work registers. -/
  init : (D × κ) × W
  /-- The discarded registers. -/
  Junk : Type
  [instFintypeJunk : Fintype Junk]
  [instDecEqJunk : DecidableEq Junk]
  /-- The split of the final registers into the output `O` and the discarded part. -/
  uv : O × Junk → I × (D × κ) × W
  uv_bijective : Function.Bijective uv

attribute [instance] OracleAlg.instFintypeW OracleAlg.instDecEqW OracleAlg.instFintypeJunk
  OracleAlg.instDecEqJunk

namespace OracleAlg

variable {I O D κ : Type} [Fintype I] [DecidableEq I] [Fintype D] [DecidableEq D]
  [Fintype κ] [DecidableEq κ]

/-- The oracle query `I_I ⊗ O_f ⊗ I_W` on the algorithm's registers. -/
def queryMat [Add κ] (A : OracleAlg I O D κ) (f : D → κ) :
    Matrix (I × (D × κ) × A.W) (I × (D × κ) × A.W) ℂ :=
  basisMat fun s => (s.1, (s.2.1.1, s.2.1.2 + f s.2.1.1), s.2.2)

/-- The inter-query unitaries as a sequence (identity beyond `T`). -/
def Gseq (A : OracleAlg I O D κ) : ℕ → Matrix (I × (D × κ) × A.W) (I × (D × κ) × A.W) ℂ :=
  fun t => if h : t < A.T + 1 then (A.G ⟨t, h⟩ : Matrix _ _ ℂ) else 1

/-- The full unitary `U^f = G_T O_f G_{T−1} ⋯ G_1 O_f G_0`. -/
def unitary [Add κ] (A : OracleAlg I O D κ) (f : D → κ) :
    Matrix (I × (D × κ) × A.W) (I × (D × κ) × A.W) ℂ :=
  evolve A.Gseq (fun _ => A.queryMat f) A.T

/-- The input `ρ_I ⊗ |init⟩⟨init|`. -/
def input (A : OracleAlg I O D κ) (ρ : Matrix I I ℂ) :
    Matrix (I × (D × κ) × A.W) (I × (D × κ) × A.W) ℂ :=
  Matrix.of fun x y => if x.2 = A.init ∧ y.2 = A.init then ρ x.1 y.1 else 0

/-- **The output state** `Tr_Junk[U^f (ρ ⊗ |init⟩⟨init|) U^f†]` on the output register `O`. -/
def run [Add κ] [Fintype O] (A : OracleAlg I O D κ) (f : D → κ) (ρ : Matrix I I ℂ) :
    Matrix O O ℂ :=
  traceOutVia A.uv (conjMat (A.unitary f) (A.input ρ))

end OracleAlg

end TorchFire.Model


