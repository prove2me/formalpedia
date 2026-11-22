-- Prove2me | Definitions.Def_CertRandQROM_Supplement_qft
-- name    : CertRandQROM_Supplement_qft
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:42:10.987861+00:00
-- url     : https://prove2.me/theorems/c2bd3ed9-6012-4712-a27e-1687ea4b7443
-- title:
--   $\mathrm{QFT}_\Sigma^{\otimes n}$ over $\Sigma=\mathbb F_q^m$ in characteristic 2 (trace character)
-- statement:
--   Let $q$ be a power of $2$, $\Sigma=\mathbb F_q^m$, and let $\mathrm{Tr}:\mathbb F_q\to\mathbb F_2$, $\mathrm{Tr}(a)=\sum_{i<\log_2 q}a^{2^i}$, be the absolute trace. For a vector $v\in\mathbb C^{\Sigma^n}$,
--
--   $$
--   \big(\mathrm{QFT}_\Sigma^{\otimes n}v\big)(y)=q^{-nm/2}\sum_{x\in\Sigma^n}(-1)^{\mathrm{Tr}(x\cdot y)}\,v(x),
--   $$
--
--   where $x\cdot y$ is the dot product of the unfolded words in $\mathbb F_q^{nm}$. The inverse transform $(\mathrm{QFT}_\Sigma^{-1})^{\otimes n}$ is its adjoint.
--
--   This is the transform of Yamakawa–Zhandry (Section 2.2 of their paper), which the construction uses: it sends $|x\rangle$, $x\in\Sigma$, to $q^{-m/2}\sum_{y\in\Sigma}(-1)^{\mathrm{Tr}(x\cdot y)}|y\rangle$, and maps the uniform superposition over a linear code to the uniform superposition over its dual.
--
--   **Formalization Note** `absTrace` is $\mathrm{Tr}$ (with $\log_2 q$ computed as `Nat.log 2 (card K)`), `trSign a` is $(-1)^{\mathrm{Tr}(a)}$ as a complex number, `qft` and `qftInv` are the transform and its adjoint. In characteristic 2 the character is real and the transform is its own inverse.
-- source:
--   Coladangelo, Khurana, Mutreja, Roberts, Slote, Tal, Unconditional Certified Randomness without Structure, arXiv:2608.31112 (sha256 b75095a2…), Construction 6.2, step 4 with footnote 6, p.29 (PDF p.31); q(λ) = 2^{2⌊log λ⌋}, §5.2, p.23 (PDF p.25)

import Mathlib
import Definitions.Def_CertRandQROM_Supplement_dualCode

set_option autoImplicit false

namespace CertRandQROM.Supplement

/-- The **absolute trace** `Tr : F_q → F_2` of a field of order `q = 2^e`,
`Tr(a) = a + a^2 + a^4 + ⋯ + a^{2^{e−1}}`, with `e = log₂ q` (used by `QFT_Σ` of [YZ24, §2.2],
footnote 6 on p.29 of Coladangelo et al., arXiv:2608.31112, sha256 b75095a2…).

**Formalization Note** The value lies in the prime field `{0, 1} ⊆ F_q` when `F_q` has
characteristic 2, which is the case for `q(λ) = 2^{2⌊log λ⌋}` (§5.2). `e` is `Nat.log 2 q`. -/
def absTrace {K : Type} [Field K] [Fintype K] (a : K) : K :=
  ∑ i ∈ Finset.range (Nat.log 2 (Fintype.card K)), a ^ (2 ^ i)

/-- The additive character `a ↦ (−1)^{Tr(a)}` of `F_q` (characteristic 2), as a complex number:
`1` if `Tr(a) = 0`, `−1` otherwise. -/
noncomputable def trSign {K : Type} [Field K] [Fintype K] [DecidableEq K] (a : K) : ℂ :=
  if absTrace a = 0 then 1 else -1

/-- **`QFT_Σ^{⊗n}`** on `ℂ^{Σ^n}`, `Σ = F_q^m` (Construction 6.2, step 4, p.29, with footnote 6:
"We use the definition of `QFT_Σ` given in [YZ24, Section 2.2]"):
`QFT_Σ |x⟩ = q^{−m/2} Σ_{y ∈ Σ} (−1)^{Tr(x·y)} |y⟩`, and its `n`-fold tensor power is
`(QFT^{⊗n} v)(y) = q^{−nm/2} Σ_{x ∈ Σ^n} (−1)^{Tr(x·y)} v(x)` with `x·y` the unfolded dot
product (`Tr` is additive, so the tensor product of the blockwise transforms is this). -/
noncomputable def qft {K : Type} [Field K] [Fintype K] [DecidableEq K] {n m : ℕ}
    (v : (Fin n → Fin m → K) → ℂ) (y : Fin n → Fin m → K) : ℂ :=
  ((Real.sqrt ((Fintype.card K : ℝ) ^ (n * m)))⁻¹ : ℂ) *
    ∑ x, trSign (unfoldDot x y) * v x

/-- **`(QFT_Σ^{−1})^{⊗n}`**: the adjoint of `qft`,
`(QFT^{−1 ⊗n} v)(x) = q^{−nm/2} Σ_{y} conj((−1)^{Tr(x·y)}) v(y)` (Construction 6.2, step 5).

**Formalization Note** It is written as the conjugate transpose of the `qft` matrix; since the
character is real and `x·y = y·x`, it coincides with `qft` (in characteristic 2 the transform
is its own inverse). -/
noncomputable def qftInv {K : Type} [Field K] [Fintype K] [DecidableEq K] {n m : ℕ}
    (v : (Fin n → Fin m → K) → ℂ) (x : Fin n → Fin m → K) : ℂ :=
  ((Real.sqrt ((Fintype.card K : ℝ) ^ (n * m)))⁻¹ : ℂ) *
    ∑ y, star (trSign (unfoldDot x y)) * v y

end CertRandQROM.Supplement


