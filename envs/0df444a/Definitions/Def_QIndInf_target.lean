-- Prove2me | Definitions.Def_QIndInf_target
-- name    : QIndInf_target
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T08:27:53.762985+00:00
-- url     : https://prove2.me/theorems/92054489-a4e1-4e06-a832-5340be141e8b
-- title:
--   Conditional state $\rho_{\le i|h<i}$ and prediction target $\tau_{\le i|h<i}$
-- statement:
--   Let $\mathcal I_1,\dots,\mathcal I_i$ be instruments, $h_{<i}$ the history with past outcomes $x_1,\dots,x_{i-1}$, and $\mathcal M_{\mathcal I}(\rho)=\sum_x|x\rangle\langle x|\otimes\mathcal E_x(\rho)$ the **measurement channel** of an instrument (Eq. (21)). The **conditional state before the $i$-th measurement** and the **prediction target** are
--
--   $$
--   \rho_{\le i|h<i}=\frac{(\mathcal A_{h<i}\otimes\mathrm{id}_{R_i})(\rho_{R_1\dots R_i})}{D^{\mathcal I,\rho}_{<i}(x)},\qquad
--   \tau_{\le i|h<i}=(\mathrm{id}_{R_{<i}}\otimes\mathcal M_{\mathcal I_i})(\rho_{\le i|h<i}),
--   $$
--
--   states on $(R_1,\dots,R_i)$ and on $(R_1,\dots,R_i,X_i)$ respectively (Eqs. (54), (55)). The target keeps the past registers, so it records the correlations of the next register and its outcome with them.
--
--   **Formalization Note** The target is indexed by (past registers) × (next register × next outcome); the paper writes the outcome register first in $\mathcal M_{\mathcal I}$. Reordering tensor factors is a relabelling that changes no trace distance, fidelity or relative entropy, and with this order $\mathrm{Tr}_{R_iX_i}$ is the published right partial trace. Auxiliary definitions: `pastInstr` (the first $i-1$ instruments), `splitLast`, `superopTensorId` ($\Phi\otimes\mathrm{id}$), `measNext` ($\mathrm{id}\otimes\mathcal M_{\mathcal I}$), `condNext` ($\rho_{\le i|h<i}$). Zero on histories of probability zero.
-- source:
--   Hiroka, Hsieh, Shirakawa, arXiv:2609.36912 (PDF of 2026-11-02), §4.1, Eqs. (54)–(55), p.19; Definition 3.1, Eq. (21), p.15

import Mathlib
import Definitions.Def_QIndInf_outcomeProb

set_option autoImplicit false

namespace QIndInf

open QAlgorithms QAlgorithms.CopyMeasurements

/-- The instruments of the first `j` rounds, from a list of `j + 1` instruments
(`(I₁, …, I_j)` from `(I₁, …, I_{j+1})`). -/
def pastInstr {n j : ℕ} {k : Fin (j + 1) → ℕ}
    (I : (l : Fin (j + 1)) → QuantumInstrument (Reg n) (Fin (k l))) :
    (l : Fin j) → QuantumInstrument (Reg n) (Fin (k l.castSucc)) :=
  fun l => I l.castSucc

/-- An operator on `R₁ … R_{j+1}` regarded as an operator on `(R₁ … R_j) ⊗ R_{j+1}` (the index
`(a, r)` stands for the configuration `Fin.snoc a r`). -/
def splitLast {n j : ℕ} (X : Matrix (Regs n (j + 1)) (Regs n (j + 1)) ℂ) :
    Matrix (Regs n j × Reg n) (Regs n j × Reg n) ℂ :=
  Matrix.of fun p q => X (Fin.snoc p.1 p.2) (Fin.snoc q.1 q.2)

/-- `Φ ⊗ id_R`: the superoperator `Φ` applied to the first tensor factor, the identity on the
second, on every operator (block by block: `Φ` is applied to `X_{(·,r),(·,r')}` for each pair
`r, r'`). -/
def superopTensorId {A B R : Type*} (Φ : Superop A B) : Superop (A × R) (B × R) :=
  fun X => Matrix.of fun p q => Φ (Matrix.of fun a a' => X (a, p.2) (a', q.2)) p.1 q.1

/-- `(id ⊗ M_J)`: the measurement channel of the instrument `J` (Definition 3.1, Eq. (21),
`M_J(ρ) = ∑_x |x⟩⟨x| ⊗ E_x(ρ)`) applied to the last factor `R` of an operator on `A ⊗ R`, the
outcome register `X` placed after `R`: the output on `A ⊗ (R ⊗ X)` is block diagonal in the
outcome, with block `(id_A ⊗ E_x)(Y)` for outcome `x`.

arXiv:2609.36912 (PDF of 2026-11-02), Definition 3.1, Eq. (21), p.15.

**Formalization Note.** The paper writes the outcome register first (`|x⟩⟨x| ⊗ E_x(ρ)`); here it
is the last factor, so that discarding `(R_i, X_i)` is the published right partial trace
`WildeQIT.partialTraceRight`. The order of tensor factors is a relabelling of the index set and
changes no trace distance, fidelity or relative entropy. -/
noncomputable def measNext {A : Type*} {n K : ℕ} (J : QuantumInstrument (Reg n) (Fin K))
    (Y : Matrix (A × Reg n) (A × Reg n) ℂ) :
    Matrix (A × (Reg n × Fin K)) (A × (Reg n × Fin K)) ℂ :=
  Matrix.of fun p q =>
    if p.2.2 = q.2.2 then
      idTensorSuperop (R := A) (instrumentBranch J p.2.2) Y (p.1, p.2.1) (q.1, q.2.1)
    else 0

/-- **Conditional state before the `i`-th measurement `ρ_{≤i|h<i}`** (Eq. (54)):
`(A_{h<i} ⊗ id_{R_i})(ρ_{R₁…R_i}) / D^{I,ρ}_{<i}(x)`, on `(R₁ … R_{i−1}) ⊗ R_i`.

arXiv:2609.36912 (PDF of 2026-11-02), §4.1, Eq. (54), p.19.

**Formalization Note.** Round `i` of the paper has `j = i − 1` past registers; `I` lists the
instruments `I₁, …, I_i` (the last one, `I (Fin.last j)`, is the next instrument `I_i`), and `x`
the past outcomes `x₁, …, x_{i−1}`. Zero on histories of probability zero (`0⁻¹ = 0`). -/
noncomputable def condNext {n j : ℕ} (σ : (m : ℕ) → Matrix (Regs n m) (Regs n m) ℂ)
    {k : Fin (j + 1) → ℕ} (I : (l : Fin (j + 1)) → QuantumInstrument (Reg n) (Fin (k l)))
    (x : (l : Fin j) → Fin (k l.castSucc)) : Matrix (Regs n j × Reg n) (Regs n j × Reg n) ℂ :=
  ((outcomeProb σ (pastInstr I) x : ℂ))⁻¹ •
    superopTensorId (histOp (pastInstr I) x) (splitLast (σ (j + 1)))

/-- **Prediction target `τ_{≤i|h<i}`** (Eq. (55)): the state on `(R₁, …, R_i, X_i)` obtained by
applying the next instrument `I_i` to `R_i` in the conditional state `ρ_{≤i|h<i}`,
`τ_{≤i|h<i} = (id_{R<i} ⊗ M_{I_i})(ρ_{≤i|h<i})`. It keeps the past registers, so it records the
correlations of the next register and outcome with them.

arXiv:2609.36912 (PDF of 2026-11-02), §4.1, Eq. (55), p.19.

**Formalization Note.** The index is `(R₁ … R_{i−1}) × (R_i × X_i)`: past registers, then the
next register, then the next outcome. Zero on histories of probability zero. -/
noncomputable def target {n j : ℕ} (σ : (m : ℕ) → Matrix (Regs n m) (Regs n m) ℂ)
    {k : Fin (j + 1) → ℕ} (I : (l : Fin (j + 1)) → QuantumInstrument (Reg n) (Fin (k l)))
    (x : (l : Fin j) → Fin (k l.castSucc)) :
    Matrix (Regs n j × (Reg n × Fin (k (Fin.last j))))
      (Regs n j × (Reg n × Fin (k (Fin.last j)))) ℂ :=
  measNext (I (Fin.last j)) (condNext σ I x)

end QIndInf


