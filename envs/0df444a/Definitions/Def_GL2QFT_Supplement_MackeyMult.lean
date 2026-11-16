-- Prove2me | Definitions.Def_GL2QFT_Supplement_MackeyMult
-- name    : GL2QFT_Supplement_MackeyMult
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:37:28.294471+00:00
-- url     : https://prove2.me/theorems/76131ba3-7f54-4554-84cb-4a04a1d72744
-- title:
--   Mackey circuit with multiplicities (App. C) — embeddings (290), maps (291)–(293), blocks $A_{\lambda,\nu}$ of (294)
-- statement:
--   The objects of Appendix C for $H\le G$ with $\Omega$, $H_\omega$, $T_\omega$, $T$ as in Remark 5.2, $n=[G:H]$, $n_\omega=[H:H_\omega]$, without multiplicity-freeness.
--
--   1. **Adapted labels with multiplicities** (Definition B.1): the basis of a $G$-irrep $\mu$ is indexed by $P:\lambda\xrightarrow{r}\mu$, $r\in[m_{\lambda,\mu}]$, and $[R_\mu(h)]^{Q:\tilde\lambda\xrightarrow{s}\mu}_{P:\lambda\xrightarrow{r}\mu}=\delta^{\tilde\lambda}_\lambda\delta^s_r[R_\lambda(h)]^Q_P$ for $h\in H$; $J_{\lambda,\mu,r}$ is the embedding they define.
--   2. **Embedding families** (290): isometric $H_\omega$-embeddings $L^\omega_{\kappa,\nu,m}:V_\kappa\to\mathrm{Res}^H_{H_\omega}V_\nu$ and $E^\omega_{\lambda,\kappa,e}:V_\kappa\to V^\omega_\lambda$ with pairwise orthogonal images spanning the target, i.e. unitary block matrices intertwining $\bigoplus_\kappa I\otimes R_\kappa$ with the target action.
--   3. $U^\lambda_{\rm Ind}(|t\rangle|v\rangle)=\sum_{\mu,b}\sqrt{d_\mu/(d_\lambda n)}\,R_\mu(t)J_{\lambda,\mu,b}|v\rangle|b\rangle$ (291); the untwisting (292); the smaller induction transform (293); $N_\lambda$ (the first three steps of Figure 20); the blocks (294)
--   $$[A_{\lambda,\nu}]^{\mu,r,b}_{\omega,\kappa,m,e}=\sqrt{\frac{d_\mu n_\omega}{d_\kappa d_\lambda d_\nu n}}\;\mathrm{tr}_{V_\kappa}\!\big[(L^\omega_{\kappa,\nu,m})^\dagger J^\dagger_{\nu,\mu,r}R_\mu(\omega)J_{\lambda,\mu,b}E^\omega_{\lambda,\kappa,e}\big];$$
--   and $A_\lambda=\bigoplus_\nu I_{V_\nu}\otimes A_{\lambda,\nu}$ (289).
--
--   **Formalization Note** Multiplicities are arbitrary counts; an embedding family is a unitary matrix whose columns are $L^\omega_{\kappa,\nu,m}|\tilde P\rangle$.
-- source:
--   Bruinsma, Posta, Stokvis, Grinko, Ozols, Quantum Fourier transform toolbox, arXiv:2608.28573 (held version, sha256 ecd45073…), Definition B.1 p.81, §C.1 eqs. (284)–(293) pp.84–85, eq. (294) and Figure 20 pp.85–86 (PDF pp.82, 85–87)

import Definitions.Def_GL2QFT_Supplement_Mackey

noncomputable section

open Classical

namespace GL2QFT

namespace Supplement

namespace MackeyMult

open Mackey
open scoped Matrix ComplexConjugate

variable {G : Type} [Group G] [Fintype G] (H : Subgroup G) (Ω : Set G) (Tω : G → Set H)
variable {ΛH ΛG : Type} [Fintype ΛH] [Fintype ΛG] (BH : ΛH → Type) [∀ l, Fintype (BH l)]
  [∀ l, DecidableEq (BH l)] (mult : ΛH → ΛG → ℕ)

/-- arXiv:2608.28573 (held version, sha256 ecd45073…), Definition B.1, item 1, p.81 (PDF p.82): the
labels `B_μ = ∪_λ {P : λ →^r μ | P ∈ B_λ, r ∈ [m_{λ,μ}]}` of a basis of the `G`-irrep `μ` adapted to
`H` with multiplicities (`m_{λ,μ} = 0` when `λ ∉ N⁻(μ)`). -/
abbrev AdBasM (μ : ΛG) : Type := Σ ν : ΛH, Fin (mult ν μ) × BH ν

/-- arXiv:2608.28573, Definition B.1, item 2, p.81: the basis is subgroup-adapted with
multiplicities: `[R_μ(h)]^{Q : λ̃ →^s μ}_{P : λ →^r μ} = δ^λ̃_λ δ^s_r [R_λ(h)]^Q_P` for `h ∈ H`. -/
def IsAdaptedMult (RH : ∀ l, H → Matrix (BH l) (BH l) ℂ)
    (RG : ∀ μ, G → Matrix (AdBasM BH mult μ) (AdBasM BH mult μ) ℂ) : Prop :=
  ∀ (μ : ΛG) (h : H) (Q P : AdBasM BH mult μ),
    RG μ (h : G) Q P =
      if e : Q.1 = P.1 then
        (if cast (congrArg (fun ν => Fin (mult ν μ)) e) Q.2.1 = P.2.1 then
          RH P.1 h (cast (congrArg BH e) Q.2.2) P.2.2 else 0)
      else 0

variable {Λω : G → Type} [∀ ω, Fintype (Λω ω)] (Bω : ∀ ω, Λω ω → Type) [∀ ω κ, Fintype (Bω ω κ)]
  [∀ ω κ, DecidableEq (Bω ω κ)]

/-- Block-diagonal action `⊕_κ I_{ℂ^{m_κ}} ⊗ R_κ(h)` on `⊕_κ ℂ^{m_κ} ⊗ V_κ` (basis `(κ, m, P̃)`). -/
def blockRep {ω : G} (mm : Λω ω → ℕ) (Rω : ∀ κ, interSub H ω → Matrix (Bω ω κ) (Bω ω κ) ℂ)
    (h : interSub H ω) :
    Matrix (Σ κ : Λω ω, Fin (mm κ) × Bω ω κ) (Σ κ : Λω ω, Fin (mm κ) × Bω ω κ) ℂ :=
  Matrix.of fun x y =>
    if e : x.1 = y.1 then
      (if cast (congrArg (fun κ => Fin (mm κ)) e) x.2.1 = y.2.1 then
        Rω y.1 h (cast (congrArg (Bω ω) e) x.2.2) y.2.2 else 0)
    else 0

/-- arXiv:2608.28573, §C.1, eq. (290), p.85 (PDF p.86): a choice of isometric `H_ω`-embeddings
`L^ω_{κ,ν,m} : V_κ → Res^H_{H_ω} V_ν` (`m ∈ [m_κ]`) whose images are pairwise orthogonal and together
span `Res V_ν`: the matrix `L` with columns `L^ω_{κ,ν,m}|P̃⟩` is unitary and intertwines
`⊕_κ I ⊗ R_κ` with `Res R_ν`. The same notion with `V^ω_λ` (61) in place of `Res V_ν` is the choice
of the embeddings `E^ω_{λ,κ,e}`. -/
def IsEmbeddingFamily {ω : G} {ι : Type} [Fintype ι] (Rtarget : interSub H ω → Matrix ι ι ℂ)
    (mm : Λω ω → ℕ) (Rω : ∀ κ, interSub H ω → Matrix (Bω ω κ) (Bω ω κ) ℂ)
    (Lmat : Matrix ι (Σ κ : Λω ω, Fin (mm κ) × Bω ω κ) ℂ) : Prop :=
  Lmat * Lmatᴴ = 1 ∧ Lmatᴴ * Lmat = 1 ∧
    ∀ h : interSub H ω, Lmat * blockRep H Bω mm Rω h = Rtarget h * Lmat

variable (RH : ∀ l, H → Matrix (BH l) (BH l) ℂ)
  (RG : ∀ μ, G → Matrix (AdBasM BH mult μ) (AdBasM BH mult μ) ℂ)
  (mL : ∀ ω, ΛH → Λω ω → ℕ) (Lmat : ∀ ω ν, Matrix (BH ν) (Σ κ : Λω ω, Fin (mL ω ν κ) × Bω ω κ) ℂ)
  (mE : ∀ ω, ΛH → Λω ω → ℕ) (Emat : ∀ ω l, Matrix (BH l) (Σ κ : Λω ω, Fin (mE ω l κ) × Bω ω κ) ℂ)

/-- arXiv:2608.28573, eq. (291), p.85 (PDF p.86): the induction transform with multiplicities
`U^λ_Ind(|t⟩ ⊗ |v⟩) = Σ_{μ,b} √(d_μ/(d_λ n)) R_μ(t) J_{λ,μ,b}|v⟩ ⊗ |b⟩`, `n = [G : H]`, where
`J_{λ,μ,b}|P⟩ = |P : λ →^b μ⟩` is the embedding given by the fixed `H`-adapted basis. Output label:
`(μ, Q, b)`, `Q ∈ B_μ`, `b ∈ [m_{λ,μ}]`. -/
def UIndMult (l : ΛH) :
    Matrix (Σ μ : ΛG, AdBasM BH mult μ × Fin (mult l μ)) (mackeyT H Ω Tω × BH l) ℂ :=
  Matrix.of fun o tP =>
    (Real.sqrt ((Fintype.card (AdBasM BH mult o.1) : ℝ) /
      ((Fintype.card (BH l) : ℝ) * (H.index : ℝ))) : ℂ) *
      RG o.1 (tP.1 : G) o.2.1 ⟨l, o.2.2, tP.2⟩

/-- The multiplicity labels `(ω, κ, m, e)` of `K_{λ,ν} = ⊕_{ω,κ} D^ω_{κ,ν} ⊗ E^ω_{λ,κ}` (288). -/
abbrev KM (l ν : ΛH) : Type := Σ ω : Ω, Σ κ : Λω ω.1, Fin (mL ω.1 ν κ) × Fin (mE ω.1 l κ)

/-- The multiplicity labels `(μ, r, b)` of `M_{λ,ν} = ⊕_μ R_{ν,μ} ⊗ B_{λ,μ}` (288). -/
abbrev MM (l ν : ΛH) : Type := Σ μ : ΛG, Fin (mult ν μ) × Fin (mult l μ)

/-- arXiv:2608.28573, eq. (294), p.85 (PDF p.86): the block
`[A_{λ,ν}]^{μ,r,b}_{ω,κ,m,e} = √(d_μ n_ω / (d_κ d_λ d_ν n)) tr_{V_κ}[(L^ω_{κ,ν,m})† J_{ν,μ,r}† R_μ(ω)
J_{λ,μ,b} E^ω_{λ,κ,e}]`, `n = [G:H]`, `n_ω = [H:H_ω]`, `tr_{V_κ}` the unnormalized trace. -/
def AblockM (l ν : ΛH) : Matrix (MM mult l ν) (KM Ω mL mE (Λω := Λω) l ν) ℂ :=
  Matrix.of fun μrb x =>
    (Real.sqrt (((Fintype.card (AdBasM BH mult μrb.1) : ℝ) * ((interSub H x.1.1).index : ℝ)) /
      ((Fintype.card (Bω x.1.1 x.2.1) : ℝ) * (Fintype.card (BH l) : ℝ) *
        (Fintype.card (BH ν) : ℝ) * (H.index : ℝ))) : ℂ) *
      ∑ Pt : Bω x.1.1 x.2.1, ∑ Q : BH ν, ∑ P : BH l,
        conj (Lmat x.1.1 ν Q ⟨x.2.1, x.2.2.1, Pt⟩) *
          RG μrb.1 (x.1 : G) ⟨ν, μrb.2.1, Q⟩ ⟨l, μrb.2.2, P⟩ *
          Emat x.1.1 l P ⟨x.2.1, x.2.2.2, Pt⟩

/-- The output index `(ν, Q, (ω, κ, m, e))` of the first three steps of the circuit of Figure 20. -/
abbrev NOutM (l : ΛH) : Type := Σ ν : ΛH, BH ν × KM Ω mL mE (Λω := Λω) l ν

/-- arXiv:2608.28573, §C.2 and Figure 20, p.86 (PDF p.87): the first three steps `N_λ` of the
circuit: `Enc` writes `t = aω` (`a ∈ T_ω`); controlled on `(λ, ω)` the untwisting (292)
`U^ω_twist|v⟩ = Σ_{κ,e} (E^ω_{λ,κ,e})†|v⟩ ⊗ |e⟩` sends `P` to `(κ, P̃, e)`; controlled on `(ω, κ)` the
smaller induction transform (293) `U^{κ,ω}_Ind(|a⟩ ⊗ |w⟩) = Σ_{ν,m} √(d_ν/(d_κ n_ω)) R_ν(a)
L^ω_{κ,ν,m}|w⟩ ⊗ |m⟩` sends `(a, P̃)` to `(ν, Q, m)`, leaving `e` unchanged. -/
def NopM (l : ΛH) : Matrix (NOutM Ω BH mL mE (Λω := Λω) l) (mackeyT H Ω Tω × BH l) ℂ :=
  Matrix.of fun o tP =>
    if h : ∃ a : Tω o.2.2.1.1, ((a : H) : G) * (o.2.2.1 : G) = (tP.1 : G) then
      ∑ Pt : Bω o.2.2.1.1 o.2.2.2.1,
        ((Real.sqrt ((Fintype.card (BH o.1) : ℝ) /
            ((Fintype.card (Bω o.2.2.1.1 o.2.2.2.1) : ℝ) *
              ((interSub H o.2.2.1.1).index : ℝ))) : ℂ) *
          (RH o.1 ((Classical.choose h : Tω o.2.2.1.1) : H) * Lmat o.2.2.1.1 o.1) o.2.1
            ⟨o.2.2.2.1, o.2.2.2.2.1, Pt⟩) *
        conj (Emat o.2.2.1.1 l tP.2 ⟨o.2.2.2.1, o.2.2.2.2.2, Pt⟩)
    else 0

/-- arXiv:2608.28573, eq. (289), p.85, and the last step of Figure 20: `A_λ = ⊕_ν I_{V_ν} ⊗ A_{λ,ν}`,
controlled on `(λ, ν)`, sending `(ω, κ, m, e)` to `(μ, r, b)`; the output `(μ, Q : ν →^r μ, b)` labels
a basis vector of `V_μ ⊗ B_{λ,μ}`. -/
def AopM (l : ΛH) :
    Matrix (Σ μ : ΛG, AdBasM BH mult μ × Fin (mult l μ)) (NOutM Ω BH mL mE (Λω := Λω) l) ℂ :=
  Matrix.of fun out o =>
    if e : out.2.1.1 = o.1 then
      (if cast (congrArg BH e) out.2.1.2.2 = o.2.1 then
        AblockM H Ω BH mult Bω RG mL Lmat mE Emat l o.1
          ⟨out.1, cast (congrArg (fun ν => Fin (mult ν out.1)) e) out.2.1.2.1, out.2.2⟩ o.2.2
      else 0)
    else 0

end MackeyMult

end Supplement

end GL2QFT


