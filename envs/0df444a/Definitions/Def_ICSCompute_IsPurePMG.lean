-- Prove2me | Definitions.Def_ICSCompute_IsPurePMG
-- name    : ICSCompute_IsPurePMG
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:49:18.478823+00:00
-- url     : https://prove2.me/theorems/e112d62b-41ce-4f95-850b-ee7046fff3b6
-- title:
--   Circuit descriptions, generated channel, process matrix generators and pure PMGs
-- statement:
--   A **circuit description** is a pair $D = (n, C)$ with $C$ an $(n+r)$-to-$(n+\ell)$ quantum circuit; its first $n$ input and output qubits form $n$ single-qubit feedback pairs, the remaining input and output qubits are the external registers $P = \mathcal S(r)$ and $F = \mathcal S(\ell)$. Its **generated channel** is
--   $$\mathrm{PMO}_D := \mathrm{PMO}\big(\mathrm{CJ}(\mathcal C_C), H_{AI}, H_{AO}\big),$$
--   the induced map of the identity connection. $D$ is a **process matrix generator (PMG)** if $\mathrm{CJ}(\mathcal C_C)$ is a process matrix for these feedback pairs, and a **pure PMG** if moreover $C$ is a unitary circuit.
--
--   A pure PMG is the paper's notion of an efficiently described pure process: a polynomial-size unitary circuit whose feedback wires may be closed with arbitrary local operations, always yielding a channel.
--
--   **Formalization Note** A unitary circuit has equally many input and output qubits, so a pure PMG has $r = \ell$. The generated channel is defined with the identity-connection formula of Definition 4.3.
-- source:
--   Shmueli, What Can Be Computed with Indefinite Causal Structure?, arXiv:2610.40573 (version of 2026-11-03, sha256 d3e36399…b606), Definitions 4.5 and 4.8, pp.19–21 (PDF pp.21–23)

import Mathlib
import Definitions.Def_ICSCompute_cj
import Definitions.Def_ICSCompute_pmo
import Definitions.Def_ICSCompute_IsProcessMatrix
import Definitions.Def_ICSCompute_QCirc

namespace ICSCompute

open QAlgorithms

/-- A **circuit description** `D = (n, C)` (Definition 4.5, p.19): an `(n + r)`-to-`(n + ℓ)`
quantum circuit `C`, whose first `n` input and output qubits are the feedback pairs. -/
abbrev Desc (n r ℓ : ℕ) := QCirc (n + r) (n + ℓ)

/-- `CJ(𝒞_C) ∈ L(H_AI ⊗ H_P ⊗ H_AO ⊗ H_F)` for a description `(n, C)` (Definition 4.5, p.19):
the Choi operator of the circuit's channel, with the input `S(n + r)` split into `AI = S(n)`,
`P = S(r)` and the output `S(n + ℓ)` into `AO = S(n)`, `F = S(ℓ)` (first `n` qubits =
feedback). -/
def choiW {n r ℓ : ℕ} (D : Desc n r ℓ) :
    Matrix ((Qubits n × Qubits r) × (Qubits n × Qubits ℓ))
      ((Qubits n × Qubits r) × (Qubits n × Qubits ℓ)) ℂ :=
  Matrix.reindex (Equiv.prodCongr (splitQ n r) (splitQ n ℓ))
    (Equiv.prodCongr (splitQ n r) (splitQ n ℓ)) (cj D.channel)

/-- The **generated channel** `PMO_D := PMO(CJ(𝒞_C), H_AI, H_AO)` of a description (Shmueli,
arXiv:2610.40573, Definition 4.5, p.19 (PDF p.21)): the induced map of the identity connection
(Definition 4.3), a linear map from `L(S(r))` to `L(S(ℓ))`. -/
def pmoD {n r ℓ : ℕ} (D : Desc n r ℓ) :
    Matrix (Qubits r) (Qubits r) ℂ →ₗ[ℂ] Matrix (Qubits ℓ) (Qubits ℓ) ℂ :=
  pmoId (choiW D)

/-- **Process matrix generator (PMG)** (Shmueli, arXiv:2610.40573, Definition 4.5, p.19
(PDF p.21)): "If `CJ(𝒞_C)` is a process matrix for these feedback pairs, we call `D` a process
matrix generator (PMG)." -/
def IsPMG {n r ℓ : ℕ} (D : Desc n r ℓ) : Prop :=
  IsProcessMatrix (choiW D)

/-- **Pure process matrix generator** (Shmueli, *What Can Be Computed with Indefinite Causal
Structure?*, arXiv:2610.40573, version of 2026-11-03, sha256 d3e36399…b606, Definition 4.8,
p.21 (PDF p.23)): "Let `D = (n, C)` be a PMG as in Definition 4.5. We say that `D` is a pure
process matrix generator, or pure PMG, if `C` is a unitary quantum circuit."

**Formalization Note** A unitary circuit has as many output as input qubits, so a pure PMG has
`r = ℓ`. Validity (`IsPMG`) quantifies over all local channels with arbitrary auxiliary
registers (Definition 4.4); unitarity of the circuit is `QCirc.IsUnitary` (work wires returned
to `|0⟩`, §3, p.14). -/
def IsPurePMG {n r : ℕ} (D : Desc n r r) : Prop :=
  IsPMG D ∧ D.IsUnitary

end ICSCompute


