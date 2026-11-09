-- Prove2me | Definitions.Def_PersistQMem_drift
-- name    : PersistQMem_drift
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T08:42:29.968568+00:00
-- url     : https://prove2.me/theorems/0eb4428f-d8d0-4acb-a9a5-10f9484440e3
-- title:
--   The resolvent $f_\alpha$, the one-step drift $d_{j,z}(A,H)$, the dilation $V$, the lift $\hat X$ and the residual $J(X)$
-- statement:
--   For $\alpha>1$ the **resolvent transformation** of a matrix $H$ is (42)
--   $$f_\alpha(H)=\alpha H(\alpha I-H)^{-1},$$
--   applied blockwise to recorded tests. For a complete refined instrument $\Phi$, an entering memory matrix $A$ and a recorded test $H=\bigoplus_aH_a$, the **one-step test drift** is (44)
--   $$d_{j,z}(A,H)=\operatorname{Tr}\big[Af_\alpha(N_{j,z}^*H)\big]-\operatorname{Tr}\big[N_0(A)f_\alpha(H)\big].$$
--   The **null-source Stinespring isometry** and the **accessible lift** are (45)–(46)
--   $$Vw=D^{-1/2}\bigoplus_a\sum_{i=1}^DM_a(w\otimes|i\rangle)\otimes|i\rangle,\qquad\hat X=\bigoplus_a(X_a\otimes I_D).$$
--   For a unit $u$, the regularized test is $X=T^{-1}$ with $T=I-H/\alpha$, and the **residual** is (48) $J(X)=\|(I-VV^*)\hat Xv\|^2$, $v=Vu$.
--
--   The drift is the one-step change of the backward score of §6.5; Lemma 6.4 bounds it by the charge $b_j$.
--
--   **Formalization Note** `⁻¹` is Mathlib's total matrix inverse; for Hermitian contractions $H$ and $\alpha>1$ the matrices inverted are invertible (milestone `eq_43_resolvent`). The drift is real for positive $A$ and Hermitian contractions; its real part is taken. $\bigoplus_a\mathbb C^{k_a}\otimes\mathbb C^D$ is indexed by `Σ a, Fin (k a) × Fin D`.
-- source:
--   Tao, Shen, Structural Lower Bounds for Quantum Property Estimation with Persistent Memory, STOC 2027 submission (manuscript of 2026-11-03, sha256 6d48ad24…), §6.4, (42), (44), p.23 (PDF p.26); (45)–(48), p.24 (PDF p.27)

import Mathlib
import Definitions.Def_PersistQMem_FinInstrument

open scoped Matrix ComplexOrder Kronecker

namespace PersistQMem

/-- The resolvent transformation `f_α(H) = α H (α I − H)⁻¹` of (42), p.23 (Tao, Shen, *Structural
Lower Bounds for Quantum Property Estimation with Persistent Memory*, STOC 2027 submission,
manuscript of 2026-11-03, sha256 6d48ad24…).

**Formalization Note.** `⁻¹` is Mathlib's matrix inverse; `αI − H` is invertible for every
Hermitian contraction `H` and `α > 1` (milestone `eq_43_resolvent`). -/
noncomputable def fAlpha {n : Type} [Fintype n] [DecidableEq n] (α : ℝ) (H : Matrix n n ℂ) :
    Matrix n n ℂ :=
  ((α : ℂ) • H) * ((α : ℂ) • (1 : Matrix n n ℂ) - H)⁻¹

variable {ι : Type} [Fintype ι] {r D K : ℕ}

/-- The one-step test drift of (44), p.23:
`d_{j,z}(A, H) = Tr[A f_α(N^*_{j,z} H)] − Tr[N_0(A) f_α(H)]`, for an entering memory matrix `A`
on `C^r` and a recorded test `H = ⊕_a H_a`, with `f_α` acting blockwise
(`f_α(⊕_a H_a) = ⊕_a f_α(H_a)`, p.23). The alternative source is `ρ` (`ρ = ρ_{j,z}` in the paper)
and the null source is `τ`.

**Formalization Note.** The real part is taken (both traces are real for positive `A` and Hermitian
contractions `H`). -/
noncomputable def drift (Φ : FinInstrument ι r D K) (α : ℝ) (ρ : Matrix (Fin D) (Fin D) ℂ)
    (A : Matrix (Fin r) (Fin r) ℂ) (H : RecTest Φ) : ℝ :=
  (A * fAlpha α (recAdjoint Φ ρ H)).trace.re -
    (recTrace Φ (recChannel Φ (tau D) A) (fun a => fAlpha α (H a))).re

/-- The null-source Stinespring isometry `V w = D^{−1/2} ⊕_a Σ_{i=1}^D M_a(w ⊗ |i⟩) ⊗ |i⟩` of (45),
p.24, as a matrix from `C^r` to `⊕_a C^{k_a} ⊗ C^D` (index `Σ a, Fin k_a × Fin D`). -/
noncomputable def stineV (Φ : FinInstrument ι r D K) :
    Matrix (Σ a : ι, Fin (Φ.k a) × Fin D) (Fin r) ℂ :=
  Matrix.of fun q c => ((Real.sqrt D : ℂ)⁻¹) * Φ.M q.1 q.2.1 (c, q.2.2)

/-- The accessible lift `X̂ = ⊕_a (X_a ⊗ I_D)` of (46), p.24. -/
def liftHat [DecidableEq ι] (Φ : FinInstrument ι r D K) (X : RecTest Φ) :
    Matrix (Σ a : ι, Fin (Φ.k a) × Fin D) (Σ a : ι, Fin (Φ.k a) × Fin D) ℂ :=
  Matrix.blockDiagonal' fun a => X a ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)

/-- The residual `J(X) = ‖(I − V V*) X̂ v‖²`, `v = V u`, of (48), p.24. -/
noncomputable def invLossJ [DecidableEq ι] (Φ : FinInstrument ι r D K) (u : Fin r → ℂ)
    (X : RecTest Φ) : ℝ :=
  let w := (1 - stineV Φ * (stineV Φ)ᴴ) *ᵥ (liftHat Φ X *ᵥ (stineV Φ *ᵥ u))
  (star w ⬝ᵥ w).re

/-- The regularized test `X = T⁻¹`, `T = I − H/α`, of (48), p.24, blockwise. -/
noncomputable def invTest (Φ : FinInstrument ι r D K) (α : ℝ) (H : RecTest Φ) : RecTest Φ :=
  fun a => (1 - ((α : ℂ)⁻¹) • H a)⁻¹

end PersistQMem


