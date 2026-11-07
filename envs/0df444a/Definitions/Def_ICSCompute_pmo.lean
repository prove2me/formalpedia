-- Prove2me | Definitions.Def_ICSCompute_pmo
-- name    : ICSCompute_pmo
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:47:02.173278+00:00
-- url     : https://prove2.me/theorems/cb22b474-291a-4fe0-9da9-d985742d4457
-- title:
--   Indefinite operator $G_{W,AI,AO}[A]$ and induced map $\mathrm{PMO}(W,H_{AI},H_{AO})[A]$
-- statement:
--   Fix $n$ single-qubit feedback pairs $(R_i, S_i)$: the $R_i$ are circuit inputs, the $S_i$ circuit outputs, $H_{AI} = \bigotimes_i H_{R_i}$ and $H_{AO} = \bigotimes_i H_{S_i}$. Let $W\in\mathcal L(H_{AI}\otimes H_P\otimes H_{AO}\otimes H_F)$, and let $A_i : \mathcal L(H_{S_i}\otimes H_{E_i}) \to \mathcal L(H_{R_i}\otimes H_{E'_i})$ be local maps with auxiliary registers $E_i, E'_i$; write $E = (E_1,\dots,E_n)$, $E' = (E'_1,\dots,E'_n)$.
--
--   The **indefinite operator** is
--   $$G_{W,AI,AO}[A] := \operatorname{Tr}_{AI,AO}\Big[\big(W^{T_{AI,AO}}\otimes I_{H_E\otimes H_{E'}}\big)\Big(I_{H_P\otimes H_F}\otimes \bigotimes_{i=1}^n \mathrm{CJ}(A_i)\Big)\Big],$$
--   where $T_{AI,AO}$ is the partial transpose on the feedback registers; after the partial trace the registers are ordered $P, E, F, E'$. The **induced map** from $P,E$ to $F,E'$ is
--   $$\mathrm{PMO}(W, H_{AI}, H_{AO})[A] := \mathrm{CJ}^{-1}\big(G_{W,AI,AO}[A],\, H_P\otimes H_E,\, H_F\otimes H_{E'}\big).$$
--   When every local channel is the identity and there are no auxiliary registers, the **identity connection** is $G_{W,AI,AO} = (\langle\Phi_n|\otimes I)\,W\,(|\Phi_n\rangle\otimes I)$ with $|\Phi_n\rangle = \sum_x |x\rangle_{AI}|x\rangle_{AO}$, and $\mathrm{PMO}(W,H_{AI},H_{AO}) := \mathrm{CJ}^{-1}(G_{W,AI,AO}, H_P, H_F)$.
--
--   These operations formalize "connecting local operations to the feedback wires" of a process.
--
--   **Formalization Note** The auxiliary registers are qubit registers $E_i = \mathcal S(e_i)$, $E'_i = \mathcal S(e'_i)$ of arbitrary, independent sizes (zero allowed). $W$ is indexed input-first, $((AI,P),(AO,F))$. Both factors are written on the index $(AI\times AO)\times((P\times F)\times(E\times E'))$ by explicit reorderings, the product is traced over $AI\times AO$, and the result reordered to $(P\times E)\times(F\times E')$. The identity connection is defined by its explicit formula (`identityConnection`, `pmoId`), as on p.19.
-- source:
--   Shmueli, What Can Be Computed with Indefinite Causal Structure?, arXiv:2610.40573 (version of 2026-11-03, sha256 d3e36399…b606), Definition 4.3, eq. (4.1), pp.18–19 (PDF pp.20–21)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_ICSCompute_ptraceR
import Definitions.Def_ICSCompute_cj
import Definitions.Def_ICSCompute_piTensor

namespace ICSCompute

open QAlgorithms

/-- The auxiliary registers `E = (E₁, …, Eₙ)` with `Eᵢ = S(e i)` (Definition 4.2, p.18). -/
abbrev AuxReg {n : ℕ} (e : Fin n → ℕ) := (i : Fin n) → Qubits (e i)

/-- A local operation on feedback pair `i`: a linear map
`L(H_{Sᵢ} ⊗ H_{Eᵢ}) → L(H_{Rᵢ} ⊗ H_{E'ᵢ})` (Definition 4.2, p.18), with single-qubit `Sᵢ`, `Rᵢ`
(index `Bool`) and auxiliary registers `Eᵢ = S(e i)`, `E'ᵢ = S(e' i)`. -/
abbrev LocalMap {n : ℕ} (e e' : Fin n → ℕ) (i : Fin n) :=
  Matrix (Bool × Qubits (e i)) (Bool × Qubits (e i)) ℂ →ₗ[ℂ]
    Matrix (Bool × Qubits (e' i)) (Bool × Qubits (e' i)) ℂ

/-- The partial transpose `W^{T_{AI,AO}}` on the feedback registers, in the computational basis
(Definition 4.3, p.18). `W` is indexed input-first, `((AI, P), (AO, F))`. -/
def ptransposeFB {n : ℕ} {P F : Type*}
    (W : Matrix ((Qubits n × P) × (Qubits n × F)) ((Qubits n × P) × (Qubits n × F)) ℂ) :
    Matrix ((Qubits n × P) × (Qubits n × F)) ((Qubits n × P) × (Qubits n × F)) ℂ :=
  Matrix.of fun u v => W ((v.1.1, u.1.2), (v.2.1, u.2.2)) ((u.1.1, v.1.2), (u.2.1, v.2.2))

/-- Reordering the factors of `⨂ᵢ CJ(Aᵢ)`, whose `i`-th factor lives on `Sᵢ, Eᵢ, Rᵢ, E'ᵢ`
(input of `Aᵢ` first, Definition 3.14), into `(AI, AO), (E, E')` with `AI = ⨂ Rᵢ`,
`AO = ⨂ Sᵢ`. -/
def localIdx {n : ℕ} (e e' : Fin n → ℕ) :
    ((i : Fin n) → (Bool × Qubits (e i)) × (Bool × Qubits (e' i))) ≃
      (Qubits n × Qubits n) × (AuxReg e × AuxReg e') where
  toFun t := ((fun i => (t i).2.1, fun i => (t i).1.1), (fun i => (t i).1.2, fun i => (t i).2.2))
  invFun u := fun i => ((u.1.2 i, u.2.1 i), (u.1.1 i, u.2.2 i))
  left_inv _ := rfl
  right_inv _ := rfl

/-- Reordering `X × (S × Y) ≃ S × (X × Y)` (the identity factor first, moved behind the shared
feedback registers `S`). -/
def swapFront (X S Y : Type*) : X × (S × Y) ≃ S × (X × Y) where
  toFun a := (a.2.1, (a.1, a.2.2))
  invFun b := (b.2.1, (b.1, b.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Indefinite operator** `G_{W,AI,AO}[A]` (Shmueli, *What Can Be Computed with Indefinite
Causal Structure?*, arXiv:2610.40573, version of 2026-11-03, sha256 d3e36399…b606,
Definition 4.3, pp.18–19 (PDF pp.20–21)):
`G_{W,AI,AO}[A] := Tr_{AI,AO}[(W^{T_{AI,AO}} ⊗ I_{H_E ⊗ H_{E'}}) (I_{H_P ⊗ H_F} ⊗ ⨂ᵢ CJ(Aᵢ))]`,
"each factor acts on its named registers, with tensor factors reordered accordingly. After taking
the partial trace, the remaining registers are ordered as P, E, F, E′."

**Formalization Note** `n` single-qubit feedback pairs (`Rᵢ`, `Sᵢ`), the paper's default after
Definition 4.4. `W ∈ L(H_AI ⊗ H_P ⊗ H_AO ⊗ H_F)` is indexed `((AI, P), (AO, F))`. Both factors
are written on the index `(AI × AO) × ((P × F) × (E × E'))` by explicit reindexings, the product
is traced over `AI × AO` with `ptraceR`, and the result is reordered to `(P × E) × (F × E')`. -/
def indefOp {n : ℕ} {P F : Type*} [Fintype P] [DecidableEq P] [Fintype F] [DecidableEq F]
    (W : Matrix ((Qubits n × P) × (Qubits n × F)) ((Qubits n × P) × (Qubits n × F)) ℂ)
    {e e' : Fin n → ℕ} (A : (i : Fin n) → LocalMap e e' i) :
    Matrix ((P × AuxReg e) × (F × AuxReg e')) ((P × AuxReg e) × (F × AuxReg e')) ℂ :=
  let S := Qubits n × Qubits n
  let Wt : Matrix (S × (P × F)) (S × (P × F)) ℂ :=
    Matrix.reindex (Equiv.prodProdProdComm _ _ _ _) (Equiv.prodProdProdComm _ _ _ _)
      (ptransposeFB W)
  let factor₁ : Matrix (S × ((P × F) × (AuxReg e × AuxReg e')))
      (S × ((P × F) × (AuxReg e × AuxReg e'))) ℂ :=
    Matrix.reindex (Equiv.prodAssoc _ _ _) (Equiv.prodAssoc _ _ _)
      (Matrix.kronecker Wt (1 : Matrix (AuxReg e × AuxReg e') (AuxReg e × AuxReg e') ℂ))
  let cjA : Matrix (S × (AuxReg e × AuxReg e')) (S × (AuxReg e × AuxReg e')) ℂ :=
    Matrix.reindex (localIdx e e') (localIdx e e') (piTensor fun i => cj (A i))
  let factor₂ : Matrix (S × ((P × F) × (AuxReg e × AuxReg e')))
      (S × ((P × F) × (AuxReg e × AuxReg e'))) ℂ :=
    Matrix.reindex (swapFront _ _ _) (swapFront _ _ _)
      (Matrix.kronecker (1 : Matrix (P × F) (P × F) ℂ) cjA)
  Matrix.reindex (Equiv.prodProdProdComm _ _ _ _) (Equiv.prodProdProdComm _ _ _ _)
    (ptraceR (factor₁ * factor₂))

/-- **Induced linear map** `PMO(W, H_AI, H_AO)[A]` from `P, E` to `F, E'` (Shmueli,
arXiv:2610.40573, Definition 4.3, eq. (4.1), p.18 (PDF p.20)):
`PMO(W, H_AI, H_AO)[A] := CJ⁻¹(G_{W,AI,AO}[A], H_P ⊗ H_E, H_F ⊗ H_{E'})`.

**Formalization Note** `n` single-qubit feedback pairs; the local operations `A i` have
arbitrary qubit auxiliary registers `Eᵢ = S(e i)`, `E'ᵢ = S(e' i)` (sizes independent in and out,
zero allowed). -/
def pmo {n : ℕ} {P F : Type*} [Fintype P] [DecidableEq P] [Fintype F] [DecidableEq F]
    (W : Matrix ((Qubits n × P) × (Qubits n × F)) ((Qubits n × P) × (Qubits n × F)) ℂ)
    {e e' : Fin n → ℕ} (A : (i : Fin n) → LocalMap e e' i) :
    Matrix (P × AuxReg e) (P × AuxReg e) ℂ →ₗ[ℂ] Matrix (F × AuxReg e') (F × AuxReg e') ℂ :=
  cjInv (indefOp W A)

/-- **Identity connection** `G_{W,AI,AO} = (⟨Φₙ| ⊗ I_{H_P ⊗ H_F}) W (|Φₙ⟩ ⊗ I_{H_P ⊗ H_F})` with
`|Φₙ⟩ = ∑_x |x⟩_AI ⊗ |x⟩_AO` (Shmueli, arXiv:2610.40573, Definition 4.3, p.19 (PDF p.21)): the
indefinite operator when every local channel is the identity and there are no auxiliary
registers. Its `((p, f), (p', f'))` entry is `∑_{x,y} W((x, p), (x, f)), ((y, p'), (y, f'))`. -/
def identityConnection {n : ℕ} {P F : Type*}
    (W : Matrix ((Qubits n × P) × (Qubits n × F)) ((Qubits n × P) × (Qubits n × F)) ℂ) :
    Matrix (P × F) (P × F) ℂ :=
  Matrix.of fun a b => ∑ x : Qubits n, ∑ y : Qubits n, W ((x, a.1), (x, a.2)) ((y, b.1), (y, b.2))

/-- **Induced map of the identity connection** `PMO(W, H_AI, H_AO) := CJ⁻¹(G_{W,AI,AO}, H_P, H_F)`
(Shmueli, arXiv:2610.40573, Definition 4.3, p.19 (PDF p.21)). -/
def pmoId {n : ℕ} {P F : Type*} [Fintype P] [Fintype F] [DecidableEq F]
    (W : Matrix ((Qubits n × P) × (Qubits n × F)) ((Qubits n × P) × (Qubits n × F)) ℂ) :
    Matrix P P ℂ →ₗ[ℂ] Matrix F F ℂ :=
  cjInv (identityConnection W)

end ICSCompute


