-- Prove2me | Definitions.Def_GL2QFT_InductionTransform
-- name    : GL2QFT_InductionTransform
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:15:40.065925+00:00
-- url     : https://prove2.me/theorems/48db5348-b1df-4e41-879c-abc49b20f5a5
-- title:
--   Subgroup-adapted bases, the encoding unitary Enc and the induction transform $U_{\mathrm{Ind}}$ (§3)
-- statement:
--   The general objects of §3.1–3.2 for a finite group $G$, a subgroup $H$ and a left transversal $\mathcal T$.
--
--   1. **Adapted labels** (Definition 3.1). The basis of a $G$-irrep $\mu$ is indexed by $\mathcal B_\mu=\{P:\lambda\to\mu\mid\lambda\in N^-(\mu),\ P\in\mathcal B_\lambda\}$. It is **subgroup-adapted** if for every $h\in H$
--   $$[R_\mu(h)]^{Q:\tilde\lambda\to\mu}_{P:\lambda\to\mu}=\delta^{\tilde\lambda}_\lambda\,[R_\lambda(h)]^Q_P. \tag{35}$$
--   2. **Encoding** (Definition 3.2). $\mathrm{Enc}|g\rangle=|t\rangle\otimes|h\rangle$ for $g=th$, $t\in\mathcal T$, $h\in H$.
--   3. **Induction transform** (Definition 3.3). $U_{\mathrm{Ind}}=\sum_\lambda|\lambda\rangle\langle\lambda|\otimes U^\lambda_{\mathrm{Ind}}$ with
--   $$[U^\lambda_{\mathrm{Ind}}]^{Q:\tilde\lambda\to\mu}_{t,P}=\sqrt{\frac{d_\mu}{d_\lambda|\mathcal T|}}\,[R_\mu(t)]^{Q:\tilde\lambda\to\mu}_{P:\lambda\to\mu},$$
--   and $U_{\mathrm{Ind}}\otimes I$ acts on $\mathbb C[\mathcal T]\otimes\bigoplus_\lambda V_\lambda\otimes V_\lambda^*$.
--   4. **Identification.** The basis vector $|\mu,Q:\tilde\lambda\to\mu,(R:\lambda\to\mu)^*\rangle$ corresponds to $|\lambda,Q:\tilde\lambda\to\mu,R^*\rangle$.
--
--   These are the ingredients of the factorization $\mathfrak F_G=(U_{\mathrm{Ind}}\otimes I)(I\otimes\mathfrak F_H)\mathrm{Enc}$ (Lemma 3.5), which the proof of Theorem 6.1 applies to $B<\mathrm{GL}_2(\mathbb F_q)$.
-- source:
--   Bruinsma, Posta, Stokvis, Grinko, Ozols, Quantum Fourier transform toolbox, arXiv:2608.28573 (held version, sha256 ecd45073…), Definition 3.1 eqs. (34)–(35), Definition 3.2 eq. (36), Definition 3.3 eqs. (37)–(38), pp.17–18 (PDF pp.18–19); Lemma 3.5 p.19

import Definitions.Def_GL2QFT_RepBasics

noncomputable section

open Classical

namespace GL2QFT

namespace Induction

variable {G : Type} [Group G] [Fintype G] (H : Subgroup G) [Fintype H] (T : Set G) [Fintype T]
variable {ΛH ΛG : Type} [Fintype ΛH] [Fintype ΛG] (BH : ΛH → Type) [∀ l, Fintype (BH l)]
  [∀ l, DecidableEq (BH l)] (Nminus : ΛG → Finset ΛH)

/-- arXiv:2608.28573 (held version, sha256 ecd45073…), Definition 3.1, item 1, p.17 (PDF p.18):
the label set of a subgroup-adapted basis of the `G`-irrep `μ`,
`B_μ = {P : λ → μ | λ ∈ N⁻(μ), P ∈ B_λ}`: a pair of an `H`-irrep `λ` in the predecessor set
`N⁻(μ)` (the `λ` occurring in `Res^G_H V_μ`, (34)) and a basis label `P ∈ B_λ`. -/
abbrev AdBas (μ : ΛG) : Type := Σ l : (Nminus μ), BH l.1

/-- arXiv:2608.28573, Definition 3.1, item 2, eq. (35), p.18: the basis of every `μ` is
subgroup-adapted: for `h ∈ H`, `[R_μ(h)]^{Q : λ̃ → μ}_{P : λ → μ} = δ^{λ̃}_λ [R_λ(h)]^Q_P`. -/
def IsSubgroupAdapted (RH : ∀ l, H → Matrix (BH l) (BH l) ℂ)
    (RG : ∀ μ, G → Matrix (AdBas BH Nminus μ) (AdBas BH Nminus μ) ℂ) : Prop :=
  ∀ (μ : ΛG) (h : H) (Q P : AdBas BH Nminus μ),
    RG μ (h : G) Q P =
      if e : Q.1 = P.1 then RH P.1.1 h (cast (congrArg (fun l => BH l.1) e) Q.2) P.2 else 0

/-- arXiv:2608.28573, Definition 3.2, eq. (36), p.18: the encoding unitary
`Enc : ℂ[G] → ℂ[T] ⊗ ℂ[H]`, `Enc|g⟩ = |t⟩ ⊗ |h⟩` for `g = th`, `t ∈ T`, `h ∈ H` (a permutation
matrix when `T` is a left transversal). -/
def Enc : Matrix (T × H) G ℂ :=
  Matrix.of fun th g => if g = (th.1 : G) * (th.2 : G) then 1 else 0

/-- arXiv:2608.28573, Definition 3.3, eq. (38), p.18: the `λ`-induction transform
`U^λ_Ind : ℂ[T] ⊗ V_λ → ⊕_{μ ∈ N⁺(λ)} V_μ`,
`[U^λ_Ind]^{Q : λ̃ → μ}_{t, P} = √(d_μ / (d_λ |T|)) [R_μ(t)]^{Q : λ̃ → μ}_{P : λ → μ}`.
The successors `N⁺(λ)` are the `μ` with `λ ∈ N⁻(μ)`. -/
def UIndLam (RG : ∀ μ, G → Matrix (AdBas BH Nminus μ) (AdBas BH Nminus μ) ℂ) (l : ΛH) :
    Matrix (Σ μ : {μ : ΛG // l ∈ Nminus μ}, AdBas BH Nminus μ.1) (T × BH l) ℂ :=
  Matrix.of fun M tP =>
    (Real.sqrt ((Fintype.card (AdBas BH Nminus M.1.1) : ℝ) /
      ((Fintype.card (BH l) : ℝ) * (Fintype.card T : ℝ))) : ℂ) *
      RG M.1.1 (tP.1 : G) M.2 ⟨⟨l, M.1.2⟩, tP.2⟩

/-- The codomain of the right-hand side of (43): `⊕_λ |λ⟩ ⊗ (⊕_{μ ∈ N⁺(λ)} V_μ) ⊗ V_λ*`, basis
`|λ, Q : λ̃ → μ, R*⟩`. -/
abbrev RHSOut : Type := Σ l : ΛH, (Σ μ : {μ : ΛG // l ∈ Nminus μ}, AdBas BH Nminus μ.1) × BH l

/-- arXiv:2608.28573, Definition 3.3, eq. (37), p.18, tensored with the identity on `V_λ*` as in
(43): `U_Ind ⊗ I = Σ_λ |λ⟩⟨λ| ⊗ U^λ_Ind ⊗ I_{V_λ*}`, from `ℂ[T] ⊗ (⊕_λ |λ⟩ ⊗ V_λ ⊗ V_λ*)` (the
codomain of `I ⊗ F_H`, basis `|t⟩|λ, P, R*⟩`) to `RHSOut`. -/
def UIndTensorI (RG : ∀ μ, G → Matrix (AdBas BH Nminus μ) (AdBas BH Nminus μ) ℂ) :
    Matrix (RHSOut BH Nminus) (T × Σ l : ΛH, BH l × BH l) ℂ :=
  Matrix.of fun out inp =>
    if e : inp.2.1 = out.1 then
      UIndLam T BH Nminus RG out.1 out.2.1 (inp.1, cast (congrArg BH e) inp.2.2.1) *
        (if cast (congrArg BH e) inp.2.2.2 = out.2.2 then 1 else 0)
    else 0

/-- arXiv:2608.28573, Lemma 3.5, p.19–20: the identification of the basis vector
`|μ, Q : λ̃ → μ, (R : λ → μ)*⟩` of the codomain of `F_G` with the basis vector `|λ, Q : λ̃ → μ, R*⟩`
of the codomain of `(U_Ind ⊗ I)(I ⊗ F_H) Enc`. -/
def ident : (Σ μ : ΛG, AdBas BH Nminus μ × AdBas BH Nminus μ) → RHSOut BH Nminus :=
  fun o => ⟨o.2.2.1.1, ⟨⟨o.1, o.2.2.1.2⟩, o.2.1⟩, o.2.2.2⟩

end Induction

end GL2QFT


