-- Prove2me | Definitions.Def_ICSCompute_Tmat
-- name    : ICSCompute_Tmat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:47:07.777955+00:00
-- url     : https://prove2.me/theorems/2fb68704-3978-483b-af63-d09ff0a8a84c
-- title:
--   The matrices $U(x)$, $|b_x\rangle$, $T$, $T_s$, $U_C$, $B_{i,a}$, $B^{u,v}_{i,a}$ and $T_{\mathbf V}$ of §6.1
-- statement:
--   Let $h:\{0,1\}^n\to\{0,1\}^n$ and single-qubit operators $U_{i,a}$, $i\in[n]$, $a\in\{0,1\}$. Define
--   $$U(x) := \bigotimes_{i=1}^n U_{i,h_i(x)},\qquad |b_x\rangle := U(x)^\dagger|x\rangle,\qquad T := \sum_{x} |x\rangle\langle b_x|,\qquad T_s := \sum_x |x\rangle\langle s(x)|,$$
--   and the generator's unitary on the feedback register $R$ and the external register $Q$ ($n$ qubits each), eq. (6.4):
--   $$U_C\big(|x\rangle_R\otimes|\psi\rangle_Q\big) = \big(U(x)|\psi\rangle\big)_R\otimes|x\rangle_Q.$$
--   For operators $V_i$ on $R_i, E_i$: $B_{i,a} := V_i(U_{i,a}\otimes I_{E_i})$, its blocks $B^{u,v}_{i,a} := (\langle u|\otimes I)B_{i,a}(|v\rangle\otimes I)$, the products $\bigotimes_i B^{r_i,y_i}_{i,h_i(r)}$, the operator $T_{\mathbf V} := \operatorname{Tr}_R[(\bigotimes_i V_i)(U_C\otimes I_E)]$ on $Q, E$, and its $Q$-blocks $(M)_{x,y} := (\langle x|_Q\otimes I_E)M(|y\rangle_Q\otimes I_E)$.
--
--   These are the objects of the basis-change theorem (Theorem 6.1) and of the USO inversion (Theorem 6.2).
--
--   **Formalization Note** $T$ is defined by its first expression in (6.3); the second expression $\sum_x|x\rangle\langle x|U(x)$ is a milestone. $T_s$ is defined from $s$, not from $s^{-1}$.
-- source:
--   Shmueli, What Can Be Computed with Indefinite Causal Structure?, arXiv:2610.40573 (version of 2026-11-03, sha256 d3e36399…b606), Theorem 6.1, eqs. (6.3)–(6.4), pp.31–32; proof, pp.32–34; Theorem 6.2, eq. (6.9), p.35 (PDF pp.33–37)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_ICSCompute_piTensor
import Definitions.Def_ICSCompute_connectU

namespace ICSCompute

open QAlgorithms

/-- `U(x) := ⨂ᵢ U_{i, hᵢ(x)}` (Theorem 6.1, p.31 (PDF p.33)), for single-qubit operators
`U i a = U_{i,a}`, `i ∈ [n]`, `a ∈ {0, 1}`. -/
def Ux {n : ℕ} (U : Fin n → Bool → Matrix Bool Bool ℂ) (h : Qubits n → Qubits n) (x : Qubits n) :
    Matrix (Qubits n) (Qubits n) ℂ :=
  piTensor fun i => U i (h x i)

/-- `|b_x⟩ := U(x)† |x⟩` (Theorem 6.1, p.31 (PDF p.33)). -/
def bvec {n : ℕ} (U : Fin n → Bool → Matrix Bool Bool ℂ) (h : Qubits n → Qubits n)
    (x : Qubits n) : Qubits n → ℂ :=
  (Ux U h x).conjTranspose.mulVec (Pi.single x 1)

/-- **The basis-change matrix `T`** (Shmueli, *What Can Be Computed with Indefinite Causal
Structure?*, arXiv:2610.40573, version of 2026-11-03, sha256 d3e36399…b606, Theorem 6.1,
eq. (6.3), p.32 (PDF p.34)): `T := ∑_{x ∈ {0,1}ⁿ} |x⟩⟨b_x|`.

**Formalization Note** `|x⟩⟨b_x|` is the outer product of the basis vector `|x⟩` with the
conjugate of `|b_x⟩`. The second expression of (6.3), `∑_x |x⟩⟨x| U(x)`, is a statement
(milestone `theorem_6_1_basis`), not part of the definition. -/
def Tmat {n : ℕ} (U : Fin n → Bool → Matrix Bool Bool ℂ) (h : Qubits n → Qubits n) :
    Matrix (Qubits n) (Qubits n) ℂ :=
  ∑ x : Qubits n, Matrix.vecMulVec (Pi.single x 1) (star (bvec U h x))

/-- **The matrix `T_s`** (Shmueli, arXiv:2610.40573, Theorem 6.2, eq. (6.9), p.35 (PDF p.37)):
`T_s := ∑_{x ∈ {0,1}ⁿ} |x⟩⟨s(x)|`. -/
def Ts {n : ℕ} (s : Qubits n → Qubits n) : Matrix (Qubits n) (Qubits n) ℂ :=
  ∑ x : Qubits n, Matrix.single x (s x) 1

/-- **The generator's unitary `U_C`** (Shmueli, arXiv:2610.40573, Theorem 6.1, proof, eq. (6.4),
p.32 (PDF p.34)): `U_C(|x⟩_R ⊗ |ψ⟩_Q) = (U(x)|ψ⟩)_R ⊗ |x⟩_Q`, on the feedback register `R` (first
factor) and the external register `Q` (second factor), `n` qubits each. -/
def UCmat {n : ℕ} (U : Fin n → Bool → Matrix Bool Bool ℂ) (h : Qubits n → Qubits n) :
    Matrix (Qubits n × Qubits n) (Qubits n × Qubits n) ℂ :=
  Matrix.of fun o i => if o.2 = i.1 then Ux U h i.1 o.1 i.2 else 0

/-- `B_{i,a} := Vᵢ (U_{i,a} ⊗ I_{L(H_{Eᵢ})})` (§6.1, p.33 (PDF p.35)). -/
def Bblk {n : ℕ} {E : Fin n → Type*} [∀ i, DecidableEq (E i)] [∀ i, Fintype (E i)]
    (V : (i : Fin n) → Matrix (Bool × E i) (Bool × E i) ℂ)
    (U : Fin n → Bool → Matrix Bool Bool ℂ) (i : Fin n) (a : Bool) :
    Matrix (Bool × E i) (Bool × E i) ℂ :=
  V i * Matrix.kronecker (U i a) (1 : Matrix (E i) (E i) ℂ)

/-- `B^{u,v} := (⟨u| ⊗ I) B (|v⟩ ⊗ I)` (§6.1, p.33 (PDF p.35)): the block of an operator `B` on
`Bool × E` with output feedback bit `u` and input feedback bit `v`. -/
def Bsub {E : Type*} (B : Matrix (Bool × E) (Bool × E) ℂ) (u v : Bool) : Matrix E E ℂ :=
  Matrix.of fun ε ε' => B (u, ε) (v, ε')

/-- `⨂ᵢ B^{rᵢ, yᵢ}_{i, hᵢ(r)}`, the operator on `E` in (6.6) (§6.1, p.33 (PDF p.35)). -/
def Bprod {n : ℕ} {E : Fin n → Type*} [∀ i, DecidableEq (E i)] [∀ i, Fintype (E i)]
    (V : (i : Fin n) → Matrix (Bool × E i) (Bool × E i) ℂ)
    (U : Fin n → Bool → Matrix Bool Bool ℂ) (h : Qubits n → Qubits n) (r y : Qubits n) :
    Matrix ((i : Fin n) → E i) ((i : Fin n) → E i) ℂ :=
  piTensor fun i => Bsub (Bblk V U i (h r i)) (r i) (y i)

/-- **`T_V := Tr_R[(⨂ᵢ Vᵢ)(U_C ⊗ I_{L(H_E)})]`** (Shmueli, arXiv:2610.40573, §6.1, p.32
(PDF p.34)), an operator on the registers `Q, E`. -/
def TV {n : ℕ} {E : Fin n → Type*} [∀ i, DecidableEq (E i)] [∀ i, Fintype (E i)]
    (V : (i : Fin n) → Matrix (Bool × E i) (Bool × E i) ℂ)
    (U : Fin n → Bool → Matrix Bool Bool ℂ) (h : Qubits n → Qubits n) :
    Matrix (Qubits n × ((i : Fin n) → E i)) (Qubits n × ((i : Fin n) → E i)) ℂ :=
  connectU (UCmat U h) V

/-- `(M)_{x,y} := (⟨x|_Q ⊗ I_{L(H_E)}) M (|y⟩_Q ⊗ I_{L(H_E)})`, the `Q`-block of an operator on
`Q, E` (§6.1, p.34 (PDF p.36)). -/
def qBlock {n : ℕ} {E : Type*} (M : Matrix (Qubits n × E) (Qubits n × E) ℂ) (x y : Qubits n) :
    Matrix E E ℂ :=
  Matrix.of fun ε ε' => M (x, ε) (y, ε')

end ICSCompute


