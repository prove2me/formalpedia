-- Prove2me | Definitions.Def_ExactAmpDich_QTract
-- name    : ExactAmpDich_QTract
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:29:22.99562+00:00
-- url     : https://prove2.me/theorems/9b82d399-ba00-48e9-8d78-e9562ccced4f
-- title:
--   Monomial, product-preserving and common-diagonal-Clifford-frame gates; $\mathrm{QTract}(G)$
-- statement:
--   Let $U$ be a $k$-qubit matrix and write $\mathrm{wt}(x)$ for the Hamming weight of $x\in\{0,1\}^k$.
--
--   1. $U$ is **monomial** if $U|x\rangle=\omega_x|\pi(x)\rangle$ for a permutation $\pi$ of $\{0,1\}^k$ and scalars $|\omega_x|=1$.
--   2. A vector $v$ is a **product state** if $v\neq 0$ and $v=\psi_1\otimes\cdots\otimes\psi_k$ for one-qubit vectors $\psi_i$, i.e. $v(x)=\prod_i\psi_i(x_i)$. $U$ is **product-preserving** if it maps every product state to a product state, and **entangling** if it maps some product state to a non-product state. Both notions quantify over all product inputs, not only basis states.
--   3. For $z\in\mathbb C$ let $D(z)=\mathrm{diag}(1,z)$, so $D(z)^{\otimes k}=\mathrm{diag}(z^{\mathrm{wt}(x)})_x$.
--
--   For a library $G$:
--
--   $$\mathrm{Mono}(G):\ \text{every gate is monomial};\qquad \mathrm{ProdPerm}(G):\ \text{every gate is product-preserving};$$
--
--   $$\mathrm{DC}(G):\ \exists z\in\mathbb C,\ |z|=1,\ \forall j\ \exists\ \text{Clifford } C_j:\ U_j=D(z)^{\otimes k_j}\,C_j\,D(z)^{\dagger\otimes k_j},$$
--
--   where a $k$-qubit unitary is **Clifford** if conjugation by it preserves the Pauli group $\{\pm1,\pm i\}\cdot\{I,X,Y,Z\}^{\otimes k}$; arbitrary global phases are allowed. Finally $\mathrm{QTract}(G)=\mathrm{Mono}(G)\vee\mathrm{ProdPerm}(G)\vee\mathrm{DC}(G)$.
--
--   These are the three tractable classes of the dichotomy. The file also defines the tensor product $V_1\otimes\cdots\otimes V_k$ of one-qubit matrices, the factor permutation $P_\sigma|x\rangle=|x\circ\sigma\rangle$, and the tensor power $M^{\otimes k}$.
--
--   **Formalization Note** Clifford is membership in the published `QAlgorithms.Clifford.normalizer`, the normalizer in the unitary group of the closure of the phase-inclusive Pauli strings.
-- source:
--   Liu–Meng, A Dichotomy for Exact Quantum Circuit Amplitudes, STOC 2027 submission (held manuscript, sha256 40ad9c68…), §1.1 (i)–(iii) and Eq. (1), p.2 (PDF p.3); App. A.2, pp.18–19 (PDF pp.19–20); Eq. (34), p.51 (PDF p.52)

import Mathlib
import Definitions.Def_ExactAmpDich_Library
import Definitions.Def_QAlgorithms_Defs_ProjectiveCliffords

set_option autoImplicit false

namespace ExactAmpDich

open QAlgorithms

/-- The Hamming weight `wt(x) = |x|` of a bit string. Liu–Meng, App. A, p.18 (PDF p.19). -/
def wt {k : ℕ} (x : Qubits k) : ℕ := (Finset.univ.filter (fun i => x i = true)).card

/-- `U` is **monomial**: it permutes the computational basis up to phases,
`U|x⟩ = ω_x |π(x)⟩` with `π` a permutation of `{0,1}^k` and `|ω_x| = 1`. Liu–Meng, §1.1 (i), p.2
(PDF p.3). -/
def IsMonomial {k : ℕ} (U : Matrix (Qubits k) (Qubits k) ℂ) : Prop :=
  ∃ π : Equiv.Perm (Qubits k), ∃ ω : Qubits k → ℂ, (∀ x, ‖ω x‖ = 1) ∧
    ∀ y x, U y x = if y = π x then ω x else 0

/-- `v` is a **product state**: a nonzero vector `|ψ₁⟩ ⊗ ⋯ ⊗ |ψ_k⟩`, i.e.
`v(x) = ∏ᵢ ψᵢ(xᵢ)` for some one-qubit vectors `ψᵢ`. Liu–Meng, App. A.2, p.18 (PDF p.19): "A nonzero
pure state is a product state if it is a tensor product of one-qubit vectors." -/
def IsProductState {k : ℕ} (v : Qubits k → ℂ) : Prop :=
  v ≠ 0 ∧ ∃ ψ : Fin k → Bool → ℂ, ∀ x, v x = ∏ i, ψ i (x i)

/-- `U` is **product-preserving**: it maps *every* product state to a product state. Liu–Meng,
§1.1 (ii), p.2: "Every k-qubit gate maps every product state |ψ1⟩⊗· · · ⊗|ψk⟩ to a product
state." -/
def PreservesProduct {k : ℕ} (U : Matrix (Qubits k) (Qubits k) ℂ) : Prop :=
  ∀ v, IsProductState v → IsProductState (U.mulVec v)

/-- `U` is **entangling**: it takes some product input to a nonproduct state. Liu–Meng, App. A.2,
p.18: "A gate is entangling if it takes some product input to a nonproduct state. This definition
quantifies over all product inputs." -/
def IsEntangling {k : ℕ} (U : Matrix (Qubits k) (Qubits k) ℂ) : Prop :=
  ∃ v, IsProductState v ∧ ¬ IsProductState (U.mulVec v)

/-- The diagonal frame `D(z)^{⊗k}`, `D(z) = diag(1, z)`: the diagonal matrix with entry
`z^{wt(x)}` at `x`. Liu–Meng, Eq. (1), p.2; p.3: "D(z)⊗n|x⟩= z|x||x⟩". `D(z)^{†⊗k}` is
`star (frame z k)`. -/
def frame (z : ℂ) (k : ℕ) : Matrix (Qubits k) (Qubits k) ℂ :=
  Matrix.diagonal (fun x => z ^ wt x)

/-- `Mono(G)`: every gate of the library is monomial (condition (i)). Liu–Meng, §1.1, p.2;
App. A.2, p.19. -/
def Mono (L : Library) : Prop := ∀ j, IsMonomial (L.U j)

/-- `ProdPerm(G)`: every gate of the library is product-preserving (condition (ii)). -/
def ProdPerm (L : Library) : Prop := ∀ j, PreservesProduct (L.U j)

/-- `DC(G)`: the library has a **common diagonal Clifford frame** (condition (iii)): a single
`z ∈ ℂ`, `|z| = 1`, such that every gate is `U = D(z)^{⊗k} C_U D(z)^{†⊗k}` with `C_U` Clifford.
Liu–Meng, §1.1 (iii) and Eq. (1), p.2; App. G, p.51: "In DC, the common diagonal phase may be any
z ∈C with |z| = 1."

**Formalization Note.** "Clifford" is membership in `QAlgorithms.Clifford.normalizer k`, the
normalizer in the unitary group of the full phase-inclusive Pauli group, so arbitrary global
phases are allowed (p.19: "We include arbitrary overall phases in the term 'Clifford unitary'"). -/
def DC (L : Library) : Prop :=
  ∃ z : ℂ, ‖z‖ = 1 ∧ ∀ j, ∃ C ∈ Clifford.normalizer (L.k j),
    L.U j = frame z (L.k j) * (C : Matrix (Qubits (L.k j)) (Qubits (L.k j)) ℂ) *
      star (frame z (L.k j))

/-- `QTract(G) = Mono(G) ∨ ProdPerm(G) ∨ DC(G)`. Liu–Meng, App. A.2, p.19; Eq. (34), p.51. -/
def QTract (L : Library) : Prop := Mono L ∨ ProdPerm L ∨ DC L

/-- The tensor product `V₁ ⊗ ⋯ ⊗ V_k` of one-qubit matrices: entry `(y, x)` is
`∏ᵢ Vᵢ(yᵢ, xᵢ)`. -/
def tensorProd {k : ℕ} (V : Fin k → Matrix Bool Bool ℂ) : Matrix (Qubits k) (Qubits k) ℂ :=
  fun y x => ∏ i, V i (y i) (x i)

/-- The matrix `P_σ` permuting the `k` tensor factors: `P_σ |x⟩ = |x ∘ σ⟩`. -/
def factorPerm {k : ℕ} (σ : Equiv.Perm (Fin k)) : Matrix (Qubits k) (Qubits k) ℂ :=
  fun y x => if y = x ∘ σ then 1 else 0

/-- The tensor power `M^{⊗k}` of a `2 × 2` matrix. -/
def tensorPow (M : Matrix Bool Bool ℂ) (k : ℕ) : Matrix (Qubits k) (Qubits k) ℂ :=
  tensorProd (fun _ => M)

end ExactAmpDich


