-- Prove2me | Definitions.Def_RandPurIso_Completion_Supplement_prepUnitary
-- name    : RandPurIso_Completion_Supplement_prepUnitary
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:53:08.73908+00:00
-- url     : https://prove2.me/theorems/5b31ecc0-c057-4f97-95e3-ae2a4d1a71ed
-- title:
--   State preparation unitaries $U^\rho=(I_N\otimes W)D_0(I\oplus U)$ and purifications
-- statement:
--   Let $\rho$ be a density matrix on $\mathcal H([N])$ and $D\ge N$. A **purification** of $\rho$ is a vector $\psi$ on $\mathcal H([N])\otimes\mathcal H([D])$ with $\mathrm{Tr}_{D}|\psi\rangle\langle\psi|=\rho$. Fix a purification $\psi_0$ and a unitary $D_0$ on $\mathcal H([N])\otimes\mathcal H([D])\cong\mathcal H([ND])$ with $D_0|0\rangle=\psi_0$ (a completion of $|0\rangle\mapsto\psi_0$, Definition 5.2). For $W\in\mathrm U(D)$ and $U\in\mathrm U(ND-1)$ set
--
--   $$
--   U^\rho=(I_N\otimes W)\,D_0\,(I_{\mathcal H([1])}\oplus U).
--   $$
--
--   With $W$ and $U$ independent and Haar distributed, $(I\otimes W)\psi_0$ is a Haar-random purification of $\rho$ and $U^\rho$ is a Haar-random unitary completion of $|0\rangle\mapsto(I\otimes W)\psi_0$; this is the distribution $\mathcal D^\rho$ of Theorem 6.9, a distribution over state preparation unitaries for $\rho$ (Definition 6.6).
--
--   **Formalization Note** $\mathcal H([N])\otimes\mathcal H([D])\cong\mathcal H([ND])$ by `finProdFinEquiv`; $I\oplus U$ is the base mission's `randomCompletion` with $N=1$.
-- source:
--   Goldin, On Random Purifications of Isometries and Channels, arXiv:2611.04573, Definition 6.6, p. 42; Theorem 6.9, p. 43; Definition 5.2, p. 29

import Mathlib
import Definitions.Def_RandPurIso_Completion_randomCompletion
open Matrix

namespace RandPurIso.Completion.Supplement

open RandPurIso.Completion

/-- **Purification** (Goldin, *On Random Purifications of Isometries and Channels*, arXiv:2611.04573, Definition 6.6, p. 42): a vector `ψ` on `H([N]) ⊗ H([D]) ≅ H([N·D])`
(`finProdFinEquiv`) with `Tr_D |ψ⟩⟨ψ| = ρ`, i.e. `Σ_b ψ(a, b) conj ψ(a', b) = ρ_{a a'}`. For a density
matrix `ρ` this forces `‖ψ‖ = 1`. -/
def IsPurification {N D : ℕ} (ρ : Matrix (Fin N) (Fin N) ℂ) (ψ : Fin (N * D) → ℂ) : Prop :=
  ∀ a a' : Fin N, ∑ b : Fin D, ψ (finProdFinEquiv (a, b)) * star (ψ (finProdFinEquiv (a', b))) = ρ a a'

/-- The state preparation isometry `|0⟩ ↦ |ψ⟩`, `H([1]) → H([N·D])`. -/
def purifIso {K : ℕ} (ψ : Fin K → ℂ) : Matrix (Fin K) (Fin 1) ℂ := fun i _ => ψ i

/-- `I_N ⊗ W` on `H([N]) ⊗ H([D]) ≅ H([N·D])` (`finProdFinEquiv`). -/
def idTensor {N D : ℕ} (W : Matrix (Fin D) (Fin D) ℂ) : Matrix (Fin (N * D)) (Fin (N * D)) ℂ :=
  fun i j =>
    if (finProdFinEquiv.symm i).1 = (finProdFinEquiv.symm j).1 then
      W (finProdFinEquiv.symm i).2 (finProdFinEquiv.symm j).2
    else 0

/-- **A sample of `D^ρ`** (Goldin, *On Random Purifications of Isometries and Channels*, arXiv:2611.04573, Theorem 6.9, p. 43: "first chooses a Haar-random purification
`|ψ_ρ⟩` on the specified registers, and then chooses a Haar-random unitary completion of
`|0⟩ ↦ |ψ_ρ⟩`").

Given a fixed purification `ψ₀` of `ρ` and a fixed completion `D₀` of `|0⟩ ↦ ψ₀`
(`IsCompletion (purifIso ψ₀) D₀`), for `W ∈ U(D)` and `U ∈ U(N·D − 1)`:
`U^ρ = (I_N ⊗ W) · D₀ (I_{H([1])} ⊕ U)`. With `W`, `U` Haar, `(I ⊗ W)ψ₀` is a Haar-random purification
(Haar unitary on the purifying register of a fixed purification, p. 43, Lemma 6.8) and
`(I ⊗ W) D₀ (I ⊕ U)` is the random completion (Definition 5.2) of `|0⟩ ↦ (I ⊗ W)ψ₀` with fixed
completion `(I ⊗ W) D₀`; by Remark 5.3 its law does not depend on that fixed completion. -/
def prepUnitary {N D : ℕ} (D₀ : Matrix.unitaryGroup (Fin (N * D)) ℂ)
    (W : Matrix.unitaryGroup (Fin D) ℂ) (U : Matrix.unitaryGroup (Fin (N * D - 1)) ℂ) :
    Matrix (Fin (N * D)) (Fin (N * D)) ℂ :=
  idTensor (N := N) (W : Matrix (Fin D) (Fin D) ℂ) * randomCompletion (N := 1) D₀ U

end RandPurIso.Completion.Supplement


