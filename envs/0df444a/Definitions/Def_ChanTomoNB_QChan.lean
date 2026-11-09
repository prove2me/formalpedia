-- Prove2me | Definitions.Def_ChanTomoNB_QChan
-- name    : ChanTomoNB_QChan
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T11:27:11.219494+00:00
-- url     : https://prove2.me/theorems/edf1f634-6167-4f74-86d2-54740bd75517
-- title:
--   Linear maps, Kraus maps and $\mathbf{QChan}^r_{d_1,d_2}$ (channels of Kraus rank at most $r$)
-- statement:
--   Operators on $\mathbb C^{A}$ are matrices indexed by a finite set $A$; a **superoperator** is a $\mathbb C$-linear map $\mathcal E:L(\mathbb C^{A})\to L(\mathbb C^{B})$. For $V:\mathbb C^A\to\mathbb C^B$ the map $X\mapsto VXV^\dagger$ is written $\mathrm{iso}(V)$, and a family $K_1,\dots,K_r$ of operators $\mathbb C^{d_1}\to\mathbb C^{d_2}$ defines the **Kraus map**
--   $$
--   \mathcal K(X)=\sum_{i=1}^{r}K_iXK_i^\dagger .
--   $$
--   The set $\mathbf{QChan}^r_{d_1,d_2}$ of quantum channels $L(\mathbb C^{d_1})\to L(\mathbb C^{d_2})$ of Kraus rank at most $r$ consists of the Kraus maps of families of length $r$ with $\sum_i K_i^\dagger K_i=I_{d_1}$ (trace preservation).
--
--   These are the unknown objects of channel tomography; estimates are arbitrary superoperators.
--
--   **Formalization Note** Zero Kraus operators are allowed, so a family of length exactly $r$ expresses "Kraus rank at most $r$"; the Kraus rank equals the rank of the Choi operator (p.10).
-- source:
--   Chen, Oufkir, Quantum channel tomography: optimal bounds in the near-boundary regime, arXiv:2611.03639v1, §2.1, p.10

import Mathlib

open Matrix

namespace ChanTomoNB

/-- Linear maps `L(ℂ^A) → L(ℂ^B)` (superoperators). Chen, Oufkir, *Quantum channel tomography:
optimal bounds in the near-boundary regime*, arXiv:2611.03639v1, §2.1, p.10. Channels and the
learner's estimates are elements of this type.

**Formalization Note.** Operators on `ℂ^A` are matrices indexed by a finite type `A`; the paper's
`ℂ^{d}` is `A = Fin d`. -/
abbrev Superop (A B : Type) := Matrix A A ℂ →ₗ[ℂ] Matrix B B ℂ

/-- The map `X ↦ V X V†` of a matrix `V : ℂ^A → ℂ^B`; for an isometry `V` this is the isometry
channel whose Choi operator is `|V⟩⟩⟨⟨V|` (arXiv:2611.03639v1, §2.1, p.9 and §4, p.22). -/
def isoChan {A B : Type} [Fintype A] (V : Matrix B A ℂ) : Superop A B where
  toFun X := V * X * Vᴴ
  map_add' X Y := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by simp [Matrix.mul_smul, Matrix.smul_mul]

/-- The Kraus map `X ↦ ∑ᵢ Kᵢ X Kᵢ†` of a family of `r` operators `Kᵢ : ℂ^A → ℂ^B`
(arXiv:2611.03639v1, §2.1, p.10). -/
noncomputable def krausMap {A B : Type} [Fintype A] {r : ℕ} (K : Fin r → Matrix B A ℂ) :
    Superop A B :=
  ∑ i, isoChan (K i)

/-- `QChan^r_{d1,d2}`: the quantum channels `L(ℂ^{d1}) → L(ℂ^{d2})` of Kraus rank at most `r`
(arXiv:2611.03639v1, §2.1, p.10).

**Formalization Note.** A channel of Kraus rank at most `r` is a map `X ↦ ∑_{i<r} Kᵢ X Kᵢ†`
with `∑ᵢ Kᵢ† Kᵢ = I`; zero Kraus operators are allowed, so a family of length exactly `r`
expresses "at most `r`" (the Kraus rank is the rank of the Choi operator, p.10). -/
def QChan (r d1 d2 : ℕ) : Set (Superop (Fin d1) (Fin d2)) :=
  {E | ∃ K : Fin r → Matrix (Fin d2) (Fin d1) ℂ, ∑ i, (K i)ᴴ * K i = 1 ∧ E = krausMap K}

end ChanTomoNB


