-- Prove2me | Definitions.Def_DimFreeShadow_labelRecovery
-- name    : DimFreeShadow_labelRecovery
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:02:28.052195+00:00
-- url     : https://prove2.me/theorems/61648c0c-0d76-4870-9efd-05d36f6a897f
-- title:
--   App. B.2 — the label recovery $R_u$, $R$ and its completion $\widehat R$, Eq. (41)
-- statement:
--   Let $C_a$ be positive operators on $K$, indexed by a classical label $a$, with $B=\sum_a C_a$, $P=\Pi_{\operatorname{supp}B}$ and $\omega_{JK}=\sum_a|a\rangle\langle a|\otimes C_a$. For $u\in\mathbb R$ and $\alpha=(1-iu)/2$ the **rotated label recovery** is
--
--   $$
--   R_u(X)=\sum_a|a\rangle\langle a|\otimes C_a^{\alpha}B^{-\alpha}XB^{-\bar\alpha}C_a^{\bar\alpha},
--   $$
--
--   its average is $R=\int_{\mathbb R}\beta_0(u)R_u\,du$, and the **full-space completion** is
--
--   $$
--   \widehat R(X)=R(PXP)+\operatorname{Tr}((I-P)X)\,\omega_{JK}.
--   $$
--
--   The module also defines the block operator $\omega_{JK}$ and the map $\Phi\otimes\mathrm{id}_C$, which applies $\Phi$ to every block of an operator on $K\otimes C$, so correlated inputs are included.
--
--   **Formalization Note** Powers are the published `supportPow`: inverse powers on the support, and powers with positive real part zero on the kernel. The integral is entrywise.
-- source:
--   Jeronimo, Huang, Liu, Dimension-Free Polylogarithmic Quantum Shadow Tomography, arXiv:2608.06345 (sha256 a1a42249…), App. B.2, Eq. (41), p.36

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P21
import Definitions.Def_WildeQIT_Recover_spectralFun

namespace DimFreeShadow

open QAlgorithms.Papers.Independent.Dependency50.P21 (betaZero)

/-- **Classical–quantum block operator** `Σ_a |a⟩⟨a| ⊗ C_a` on `J ⊗ K` (arXiv:2608.06345,
sha256 a1a42249…, App. B.2, p.36: "ωJK = Σa |a⟩⟨a| ⊗ Ca"). The label register `J` is indexed by
`A`, the quantum register `K` by `κ`; the operator is block diagonal in `J`. -/
def blockDiag {A κ : Type} [DecidableEq A] (C : A → Matrix κ κ ℂ) :
    Matrix (A × κ) (A × κ) ℂ :=
  Matrix.of fun p q => if p.1 = q.1 then C p.1 p.2 q.2 else 0

/-- **The rotated label recovery map** `R_u` (arXiv:2608.06345, sha256 a1a42249…, App. B.2,
p.36): with `B = Σ_a C_a`, `α = (1 − iu)/2`, `ᾱ = (1 + iu)/2`,
`R_u(X) = Σ_a |a⟩⟨a| ⊗ C_a^α B^{−α} X B^{−ᾱ} C_a^{ᾱ}` for an operator `X` on `K`.

**Formalization Note** Powers are `WildeQIT.Recover.supportPow` (taken on the support, `0 ↦ 0`), so
`C_a^α` vanishes on `ker C_a` (`Re α = 1/2 > 0`) and `B^{−α}` is the inverse power on `supp B`,
as App. B prescribes ("Inverse powers are taken on supports, and complex powers with positive
real part are zero on kernels", p.35). The map is defined on every operator; the paper uses it
on operators supported on `supp B`. -/
noncomputable def labelRotated {A κ : Type} [Fintype A] [DecidableEq A] [Fintype κ]
    [DecidableEq κ] (C : A → Matrix κ κ ℂ) (u : ℝ) (X : Matrix κ κ ℂ) :
    Matrix (A × κ) (A × κ) ℂ :=
  blockDiag fun a =>
    WildeQIT.Recover.supportPow (C a) ((1 - (u : ℂ) * Complex.I) / 2) *
      WildeQIT.Recover.supportPow (∑ b, C b) (-((1 - (u : ℂ) * Complex.I) / 2)) * X *
      WildeQIT.Recover.supportPow (∑ b, C b) (-((1 + (u : ℂ) * Complex.I) / 2)) *
      WildeQIT.Recover.supportPow (C a) ((1 + (u : ℂ) * Complex.I) / 2)

/-- **The averaged label recovery map** `R = ∫_ℝ β₀(u) R_u du` (arXiv:2608.06345, sha256
a1a42249…, App. B.2, p.36), with `β₀` the published `P21.betaZero`.

**Formalization Note** Entrywise Bochner integral over `ℝ` (each entry is continuous in `u` and
bounded by a constant times `β₀(u)`, hence integrable). -/
noncomputable def labelRecovery {A κ : Type} [Fintype A] [DecidableEq A] [Fintype κ]
    [DecidableEq κ] (C : A → Matrix κ κ ℂ) (X : Matrix κ κ ℂ) :
    Matrix (A × κ) (A × κ) ℂ :=
  Matrix.of fun p q => ∫ u : ℝ, (betaZero u : ℂ) * labelRotated C u X p q

/-- **The full-space completion of the label recovery** (arXiv:2608.06345, sha256 a1a42249…,
App. B.2, Eq. (41), p.36): `R̂(X) = R(PXP) + Tr((I − P)X) ω_JK`, with `P = Π_{supp B}`,
`B = Σ_a C_a` and `ω_JK = Σ_a |a⟩⟨a| ⊗ C_a`. -/
noncomputable def labelCompletion {A κ : Type} [Fintype A] [DecidableEq A] [Fintype κ]
    [DecidableEq κ] (C : A → Matrix κ κ ℂ) (X : Matrix κ κ ℂ) :
    Matrix (A × κ) (A × κ) ℂ :=
  labelRecovery C (WildeQIT.Recover.supportProj (∑ b, C b) * X * WildeQIT.Recover.supportProj (∑ b, C b)) +
    Matrix.trace ((1 - WildeQIT.Recover.supportProj (∑ b, C b)) * X) • blockDiag C

/-- **A map tensored with the identity on a spectator register** `Φ ⊗ id_C`
(arXiv:2608.06345, sha256 a1a42249…, App. B.2, p.36: "the rotated map equals Ru ⊗ idC,
including correlated operators"). The map `Φ` acts on every `κ`-block
`X_{c c'} = (X_{(k,c),(k',c')})_{k,k'}` of an operator on `κ × γ`, so correlated (entangled)
inputs are included. -/
def tensorIdRight {κ κ' γ : Type} (Φ : Matrix κ κ ℂ → Matrix κ' κ' ℂ) :
    Matrix (κ × γ) (κ × γ) ℂ → Matrix (κ' × γ) (κ' × γ) ℂ :=
  fun X => Matrix.of fun p q => Φ (Matrix.of fun k k' => X (k, p.2) (k', q.2)) p.1 q.1

end DimFreeShadow


