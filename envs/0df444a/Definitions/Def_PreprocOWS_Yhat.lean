-- Prove2me | Definitions.Def_PreprocOWS_Yhat
-- name    : PreprocOWS_Yhat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:27:55.345035+00:00
-- url     : https://prove2.me/theorems/6d1661a1-8e47-4e36-a55c-8146bfecc06b
-- title:
--   The operator $\widehat Y$ in the compressed oracle database mode
-- statement:
--   For an algorithm $A$, the operator $\widehat Y$ on (advice register)$\otimes$(database register) is
--   $$
--   \widehat Y=\frac1N\cdot\mathbb E_k\sum_{x_1,x_2}T_{k,x_1}\,\Big(\langle x_1|\langle0^w|\,(U^\dagger\mathsf{cO}^\dagger)^T\,\Pi_k\,(\mathsf{cO}\,U)^T\,|x_2\rangle|0^w\rangle\Big)\,T_{k,x_2},
--   $$
--   where the bracket is the block of the operator on $\mathbb C^\Omega\otimes\mathbb C^{\mathrm{DB}}$ with challenge register $x_1$ (row), $x_2$ (column) and workspace $|0^w\rangle$, an operator on (advice)$\otimes$(database).
--
--   It is the compressed-oracle form of $Y_R$: the trace moments of $Y_R$ averaged over $R$ are the diagonal entries of $\widehat Y^{2t}$ at the empty database (display (6)).
--
--   **Formalization Note** The page writes "$\langle x_1|\langle0^w|(U^\dagger\mathsf{cO}^\dagger)^T\Pi_k(\mathsf{cO}\,U)^T|x_2\rangle|0^w\rangle\otimes T_{k,x_1}T_{k,x_2}$". The block itself acts on the database register (through $\mathsf{cO}$), so the toggles are read as multiplying it on both sides, the reading under which $\widehat Y$ is Hermitian and the Reformulation of Lemma 5.3 holds.
-- source:
--   Dong, Lombardi, Lower Bounds for Preprocessing Attacks on Quantum Cryptography, arXiv:2610.02101 (version of 2026-11-02, sha256 7a0bd8da…), §5.1, display for Ŷ, p.18 (PDF p.21)

import Mathlib
import Definitions.Def_PreprocOWS_cO
open Matrix

namespace PreprocOWS

/-- The block `⟨x₁|⟨0^w| M |x₂⟩|0^w⟩` of an operator `M` on `Ω × DB`, an operator on
(advice register) ⊗ (database register) (arXiv:2610.02101, §5.1, p.18). -/
def blockAt {S K N w : ℕ} (M : Matrix (Ω S N w × DB K N) (Ω S N w × DB K N) ℂ) (x₁ x₂ : Fin N) :
    Matrix (Fin (2 ^ S) × DB K N) (Fin (2 ^ S) × DB K N) ℂ :=
  Matrix.of fun a b => M ((a.1, x₁, wsZero w), a.2) ((b.1, x₂, wsZero w), b.2)

/-- The operator **`Ŷ`** in the compressed oracle database mode, Dong–Lombardi, arXiv:2610.02101
(version of 2026-11-02, sha256 7a0bd8da…), §5.1, p.18 (PDF p.21):
`Ŷ = (1/N) · E_k ∑_{x₁,x₂} ⟨x₁|⟨0^w| (U†cO†)^T Π_k (cO U)^T |x₂⟩|0^w⟩ ⊗ T_{k,x₁} T_{k,x₂}`,
on (advice register `[2^S]`) ⊗ (database register).

**Formalization Note.** The block `⟨x₁|⟨0^w| (U†cO†)^T Π_k (cO U)^T |x₂⟩|0^w⟩` itself acts on the
database register (through `cO`), so the page's "`⊗ T_{k,x₁} T_{k,x₂}`" is read as the product
`T_{k,x₁} · (block) · T_{k,x₂}`, the reading under which `Ŷ` is Hermitian and the Reformulation of
Lemma 5.3 (p.19) holds. `(cO U)^T` is `cRun A`. -/
noncomputable def Yhat {S T K N w : ℕ} (A : Alg S T K N w) :
    Matrix (Fin (2 ^ S) × DB K N) (Fin (2 ^ S) × DB K N) ℂ :=
  ((N : ℂ)⁻¹ * (K : ℂ)⁻¹) • ∑ k, ∑ x₁, ∑ x₂,
    liftR (togMat (k, x₁)) * blockAt ((cRun A)ᴴ * liftL (A.proj k) * cRun A) x₁ x₂ *
      liftR (togMat (k, x₂))

end PreprocOWS


