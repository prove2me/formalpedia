-- Prove2me | Definitions.Def_OptQJunta_Supplement_ProductTester
-- name    : OptQJunta_Supplement_ProductTester
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:14:22.476206+00:00
-- url     : https://prove2.me/theorems/2ce8d0a5-e3c1-43b2-a438-b4ed3be2d4b6
-- title:
--   Nonadaptive testers with product inputs and single-qubit measurements
-- statement:
--   A **nonadaptive** query algorithm (§2.5) fixes, before its first query, the input state of every query and the measurement applied to the output of every query. In the testers of Theorems 5.5 and 6.2 every query acts on a **product input state without ancillas** and is followed by **single-qubit measurements**.
--
--   Such a tester with $t$ queries draws a seed $r$ with probability $\mu(r)$. For each query $j$ the seed fixes single-qubit states $|\psi_{r,j,i}\rangle$ and single-qubit unitaries $B_{r,j,i}$ ($i\in[n]$). Query $j$ applies the channel $\Phi$ to $\rho_{r,j}=\bigotimes_i|\psi_{r,j,i}\rangle\langle\psi_{r,j,i}|$ and measures qubit $i$ in the basis $\{B_{r,j,i}|0\rangle,B_{r,j,i}|1\rangle\}$, so that the outcome $w\in\{0,1\}^n$ has probability
--
--   $$
--   \Pr[w\mid r,j]=\langle b_{r,j}(w)|\,\Phi(\rho_{r,j})\,|b_{r,j}(w)\rangle,\qquad |b_{r,j}(w)\rangle=\bigotimes_iB_{r,j,i}|w_i\rangle .
--   $$
--
--   After all queries it accepts with probability $F(r,w_1,\dots,w_t)\in[0,1]$, so its acceptance probability is $\sum_r\mu(r)\sum_{w}\prod_j\Pr[w_j\mid r,j]\,F(r,w)$.
--
--   **Formalization Note** Single-qubit measurements are taken in an orthonormal basis, the form of Influence-Sample (Lemma 5.4). The seed space is a finite type; the tester makes exactly $t$ queries. For a unitary $U$ the tester is run on $\Phi_U$ (one forward query, Eq. (14)).
-- source:
--   Bao, Gao, Yao, Optimal Quantum Junta Testing, preprint (version of November 3, 2026, sha256 a97d09a4…), §2.5, p.22; Lemma 5.4, p.63; Theorems 5.5 and 6.2, pp.64, 72

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Channel

namespace OptQJunta.Supplement

open QAlgorithms

/-- A nonadaptive `t`-query tester with product inputs and single-qubit measurements (Bao, Gao, Yao,
*Optimal Quantum Junta Testing*, preprint, version of November 3, 2026, sha256 a97d09a4…, §2.5, p.22:
"A query algorithm is nonadaptive if, before its first query, it fixes the input state of every
query and the measurement applied to the output of every query"; Theorems 5.5 and 6.2, pp.64, 72:
"Every query acts on a product input state without ancillas and is followed by single-qubit
measurements"; Lemma 5.4, p.63).

A random seed `r ∈ R` is drawn with probability `μ(r)` before any query. For each query `j < t`
the seed fixes the product input state `⊗_i |ψ_{r,j,i}⟩` on the `n` query qubits (no ancilla) and,
for each qubit `i`, a measurement basis `{B_{r,j,i}|0⟩, B_{r,j,i}|1⟩}`. After all `t` queries the
tester accepts with probability `F(r, w) ∈ [0, 1]`, `w_j ∈ {0,1}^n` the outcomes of query `j`.

**Formalization Note** Single-qubit measurements are measurements of each output qubit in an
orthonormal basis (the form used by Influence-Sample, Lemma 5.4); the classical post-processing,
which may use the seed, is the acceptance function `F`. Exactly `t` queries are made. -/
structure ProductTester (n t : ℕ) (R : Type) [Fintype R] where
  /-- The law of the seed. -/
  μ : R → ℝ
  /-- It is a probability distribution. -/
  μ_dist : (∀ r, 0 ≤ μ r) ∧ ∑ r, μ r = 1
  /-- The single-qubit input states `ψ_{r,j,i}`. -/
  ψ : R → Fin t → Fin n → EuclideanSpace ℂ Bool
  /-- They are unit vectors. -/
  ψ_unit : ∀ r j i, ‖ψ r j i‖ = 1
  /-- The single-qubit measurement bases: `B_{r,j,i}|w⟩` is the basis vector of outcome `w`. -/
  B : R → Fin t → Fin n → Matrix.unitaryGroup Bool ℂ
  /-- The acceptance probability given the seed and all outcomes. -/
  F : R → (Fin t → Qubits n) → ℝ
  /-- It lies in `[0, 1]`. -/
  F_mem : ∀ r w, 0 ≤ F r w ∧ F r w ≤ 1

namespace ProductTester

variable {n t : ℕ} {R : Type} [Fintype R]

/-- The product input vector `⊗_i |ψ_{r,j,i}⟩` of query `j` under seed `r`. -/
noncomputable def inputVec (A : ProductTester n t R) (r : R) (j : Fin t) : Qubits n → ℂ :=
  fun x => ∏ i, A.ψ r j i (x i)

/-- The input density matrix `ρ_{r,j} = ⊗_i |ψ_{r,j,i}⟩⟨ψ_{r,j,i}|` of query `j`. -/
noncomputable def inputState (A : ProductTester n t R) (r : R) (j : Fin t) :
    Matrix (Qubits n) (Qubits n) ℂ :=
  Matrix.vecMulVec (A.inputVec r j) (star (A.inputVec r j))

/-- The measurement vector `|b_{r,j}(w)⟩ = ⊗_i B_{r,j,i}|w_i⟩` of outcome `w` of query `j`. -/
noncomputable def measVec (A : ProductTester n t R) (r : R) (j : Fin t) (w : Qubits n) :
    Qubits n → ℂ :=
  fun x => ∏ i, (A.B r j i : Matrix Bool Bool ℂ) (x i) (w i)

/-- `Pr[w_j = w | r] = ⟨b_{r,j}(w)| Φ(ρ_{r,j}) |b_{r,j}(w)⟩`. -/
noncomputable def outcomeProb (A : ProductTester n t R) (Φ : Superop (Qubits n) (Qubits n)) (r : R)
    (j : Fin t) (w : Qubits n) : ℝ :=
  (star (A.measVec r j w) ⬝ᵥ (Φ (A.inputState r j)).mulVec (A.measVec r j w)).re

/-- The acceptance probability `Σ_r μ(r) Σ_w (Π_j Pr[w_j | r]) F(r, w)` on the channel `Φ`. -/
noncomputable def acc (A : ProductTester n t R) (Φ : Superop (Qubits n) (Qubits n)) : ℝ :=
  ∑ r, A.μ r * ∑ w : Fin t → Qubits n, (∏ j, A.outcomeProb Φ r j (w j)) * A.F r w

end ProductTester

end OptQJunta.Supplement


