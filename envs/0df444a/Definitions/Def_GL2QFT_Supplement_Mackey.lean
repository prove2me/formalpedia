-- Prove2me | Definitions.Def_GL2QFT_Supplement_Mackey
-- name    : GL2QFT_Supplement_Mackey
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:36:35.28902+00:00
-- url     : https://prove2.me/theorems/472b0915-d552-45ab-8c4c-0ed4091551e8
-- title:
--   The Mackey circuit of §5 — $T=\bigsqcup T_\omega\omega$, untwisting, $N_\lambda$, the blocks $A_{\lambda,\tilde\lambda}$ of (70)
-- statement:
--   The objects of §5.1 for $H\le G$, a double-coset transversal $\Omega$ of $H\backslash G/H$, $H_\omega=H\cap\omega H\omega^{-1}$ and left transversals $T_\omega$ of $H_\omega$ in $H$.
--
--   1. The left transversal $T=\bigsqcup_{\omega\in\Omega}T_\omega\omega$ (62).
--   2. The $H$-irreps in their $H_\omega$-adapted labels $\tilde P:\kappa\to\lambda$ (Remark 5.2: one fixed basis, adapted to every $H_\omega$).
--   3. An **untwisting** $U^\omega_{\rm twist}$: a unitary $V^\omega_\lambda\to\bigoplus_{\kappa\in N(\lambda^\omega)}V_\kappa$ with $U^\omega_{\rm twist}R^\omega_\lambda U^{\omega\dagger}_{\rm twist}=\sum_\kappa|\kappa\rangle\langle\kappa|\otimes R_\kappa$ (67).
--   4. The label sets $M_{\lambda,\tilde\lambda}=N^+(\lambda)\cap N^+(\tilde\lambda)$ (63) and $K_{\lambda,\tilde\lambda}=\{(\omega,\kappa):\kappa\in N(\lambda^\omega)\cap N^-_{H_\omega\le H}(\tilde\lambda)\}$ (64), and the blocks (70)
--   $$[A_{\lambda,\tilde\lambda}]^\mu_{\kappa,\omega}=\sqrt{\frac{d_\mu[H:H_\omega]}{d_\kappa d_\lambda d_{\tilde\lambda}[G:H]}}\sum_{P\in B_\lambda,\tilde P\in B_\kappa}[R_\mu(\omega)]^{\tilde P:\kappa\to\tilde\lambda\to\mu}_{P:\lambda\to\mu}\,[(U^\omega_{\rm twist})^\dagger]^P_{\tilde P,\kappa}.$$
--   5. $N_\lambda$, Steps 1–3 of Algorithm 1: encode $t=t_\omega\omega$ (66), untwist controlled on $(\lambda,\omega)$, apply the induction transform $U^{\kappa,\omega}_{\rm Ind}$ for $H_\omega\le H$ controlled on $(\omega,\kappa)$; and $A_\lambda=\bigoplus_{\tilde\lambda}A_{\lambda,\tilde\lambda}\otimes I_{V_{\tilde\lambda}}$ (65), Step 4.
--
--   **Formalization Note** $[H:H_\omega]$ and $[G:H]$ are subgroup indices. $U^{\kappa,\omega}_{\rm Ind}$ is the published `UIndLam`.
-- source:
--   Bruinsma, Posta, Stokvis, Grinko, Ozols, Quantum Fourier transform toolbox, arXiv:2608.28573 (held version, sha256 ecd45073…), Remark 5.2 eq. (62), Definition 5.3 eqs. (63)–(70), Algorithm 1, pp.28–30 (PDF pp.29–31)

import Definitions.Def_GL2QFT_InductionTransform
import Definitions.Def_GL2QFT_Supplement_RepTheory

noncomputable section

open Classical

namespace GL2QFT

namespace Supplement

namespace Mackey

open Induction
open scoped Matrix ComplexConjugate

variable {G : Type} [Group G] [Fintype G] (H : Subgroup G) (Ω : Set G) (Tω : G → Set H)

/-- arXiv:2608.28573 (held version, sha256 ecd45073…), Remark 5.2, eq. (62), p.28 (PDF p.29): the
left transversal `T = ⊔_{ω ∈ Ω} T_ω ω` of `H` in `G` built from the double-coset transversal `Ω` and
the left transversals `T_ω` of `H_ω` in `H`. -/
def mackeyT : Set G := {g | ∃ ω ∈ Ω, ∃ a ∈ Tω ω, g = ((a : H) : G) * ω}

/-! The `H`-irreps `R_λ` (labels `ΛH`, bases `BH`), the `G`-irreps `R_μ` in `H`-adapted labels, and
for every `ω` the `H_ω`-irreps `R_κ` (labels `Λω ω`, bases `Bω ω`). -/
variable {ΛH ΛG : Type} [Fintype ΛH] [Fintype ΛG] (BH : ΛH → Type) [∀ l, Fintype (BH l)]
  [∀ l, DecidableEq (BH l)] (Nminus : ΛG → Finset ΛH)
  (RH : ∀ l, H → Matrix (BH l) (BH l) ℂ)
  (RG : ∀ μ, G → Matrix (AdBas BH Nminus μ) (AdBas BH Nminus μ) ℂ)
  {Λω : G → Type} [∀ ω, Fintype (Λω ω)] (Bω : ∀ ω, Λω ω → Type) [∀ ω κ, Fintype (Bω ω κ)]
  [∀ ω κ, DecidableEq (Bω ω κ)]
  (Rω : ∀ ω κ, interSub H ω → Matrix (Bω ω κ) (Bω ω κ) ℂ)
  (NmW : ∀ ω, ΛH → Finset (Λω ω))
  (adapt : ∀ ω l, BH l ≃ AdBas (Bω ω) (NmW ω) l)

/-- The `H`-irrep `R_λ` written in its `H_ω`-adapted labels `P̃ : κ → λ` (Remark 5.2: the fixed basis
of `λ` is subgroup-adapted to `H_ω`, through the relabelling `adapt ω λ`). -/
def RHad (ω : G) (l : ΛH) (h : H) : Matrix (AdBas (Bω ω) (NmW ω) l) (AdBas (Bω ω) (NmW ω) l) ℂ :=
  (RH l h).submatrix (adapt ω l).symm (adapt ω l).symm

/-- Remark 5.2: for every `ω`, the fixed basis of every `λ ∈ Ĥ` is subgroup-adapted to `H_ω`
((35) for `H_ω ≤ H`). -/
def IsAdaptedToInter (ω : G) : Prop :=
  IsSubgroupAdapted (interSub H ω) (Bω ω) (NmW ω) (Rω ω) (RHad H BH RH Bω NmW adapt ω)

variable (Ntw : ∀ ω, ΛH → Finset (Λω ω))
  (Utw : ∀ ω l, Matrix (Σ κ : Ntw ω l, Bω ω κ.1) (BH l) ℂ)

/-- arXiv:2608.28573, Definition 5.3, eq. (67), p.29 (PDF p.30): `U^ω_twist` is a unitary
`V^ω_λ → ⊕_{κ ∈ N(λ^ω)} V_κ` with `U^ω_twist R^ω_λ(h) U^ω_twist† = Σ_κ |κ⟩⟨κ| ⊗ R_κ(h)` for every
`h ∈ H_ω` (`Ntw ω λ` is the support `N(λ^ω)`; the decomposition is multiplicity-free). -/
def IsUntwisting (ω : G) (l : ΛH) : Prop :=
  Utw ω l * (Utw ω l)ᴴ = 1 ∧ (Utw ω l)ᴴ * Utw ω l = 1 ∧
    ∀ h : interSub H ω,
      Utw ω l * twistRep H ω (RH l) h * (Utw ω l)ᴴ =
        Matrix.of fun (x y : Σ κ : Ntw ω l, Bω ω κ.1) =>
          if e : x.1 = y.1 then Rω ω y.1.1 h (cast (congrArg (fun κ => Bω ω κ.1) e) x.2) y.2
          else 0

/-- arXiv:2608.28573, eq. (63), p.28: `M_{λ,λ̃} = N⁺(λ) ∩ N⁺(λ̃)`. -/
abbrev MSet (l lt : ΛH) : Type := {μ : ΛG // l ∈ Nminus μ ∧ lt ∈ Nminus μ}

/-- arXiv:2608.28573, eq. (64), p.28: `K_{λ,λ̃} = {(ω, κ) : ω ∈ Ω, κ ∈ N(λ^ω) ∩ N⁻_{H_ω≤H}(λ̃)}`. -/
abbrev KSet (l lt : ΛH) : Type := Σ ω : Ω, {κ : Λω ω.1 // κ ∈ Ntw ω.1 l ∧ κ ∈ NmW ω.1 lt}

/-- arXiv:2608.28573, Definition 5.3, eq. (70), p.30 (PDF p.31): the block
`A_{λ,λ̃} : ℂ[K_{λ,λ̃}] → ℂ[M_{λ,λ̃}]`,
`[A_{λ,λ̃}]^μ_{κ,ω} = √(d_μ [H:H_ω] / (d_κ d_λ d_λ̃ [G:H])) Σ_{P ∈ B_λ, P̃ ∈ B_κ}
[R_μ(ω)]^{P̃:κ→λ̃→μ}_{P:λ→μ} [(U^ω_twist)†]^P_{P̃,κ}`.

**Formalization Note** `P̃ : κ → λ̃ → μ` is the `G`-label `(λ̃, P')` with `P' ∈ B_λ̃` the basis
vector labelled `P̃ : κ → λ̃` in the `H_ω`-adapted labels of `λ̃` (`(adapt ω λ̃).symm`). `[H : H_ω]` and
`[G : H]` are `Subgroup.index`. -/
def Ablock (l lt : ΛH) :
    Matrix (MSet Nminus l lt) (KSet Ω NmW Ntw (Λω := Λω) l lt) ℂ :=
  Matrix.of fun μ ωκ =>
    (Real.sqrt (((Fintype.card (AdBas BH Nminus μ.1) : ℝ) * ((interSub H ωκ.1.1).index : ℝ)) /
      ((Fintype.card (Bω ωκ.1.1 ωκ.2.1) : ℝ) * (Fintype.card (BH l) : ℝ) *
        (Fintype.card (BH lt) : ℝ) * (H.index : ℝ))) : ℂ) *
      ∑ P : BH l, ∑ Pt : Bω ωκ.1.1 ωκ.2.1,
        RG μ.1 (ωκ.1 : G)
            ⟨⟨lt, μ.2.2⟩, (adapt ωκ.1.1 lt).symm ⟨⟨ωκ.2.1, ωκ.2.2.2⟩, Pt⟩⟩
            ⟨⟨l, μ.2.1⟩, P⟩ *
          conj (Utw ωκ.1.1 l ⟨⟨ωκ.2.1, ωκ.2.2.1⟩, Pt⟩ P)

/-- The output index of the first three steps of Algorithm 1: `|κ, ω⟩ ⊗ |λ̃, Q⟩` with `ω ∈ Ω`,
`κ ∈ N(λ^ω)`, `λ̃ ∈ N⁺_{H_ω≤H}(κ)` and `Q ∈ B_λ̃`. -/
abbrev NOut (l : ΛH) : Type :=
  Σ ω : Ω, Σ κ : Ntw ω.1 l, Σ lt : {lt : ΛH // κ.1 ∈ NmW ω.1 lt}, BH lt.1

/-- arXiv:2608.28573, Algorithm 1, steps 1–3, p.30 (PDF p.31): the operator `N_λ` (the circuit of
Figure 11 up to, but not including, `A_λ`): 1. `Enc` (66) writes `t = t_ω ω`; 2. controlled on
`(λ, ω)`, `U^ω_twist` sends `|P⟩` to `Σ_{κ, P̃} [U^ω_twist]^{P̃,κ}_P |κ⟩|P̃⟩`; 3. controlled on
`(ω, κ)`, the induction transform `U^{κ,ω}_Ind` of Definition 3.3 for `H_ω ≤ H` (transversal `T_ω`)
sends `|t_ω⟩|P̃⟩` to `|λ̃⟩|Q⟩`. The entry at `(ω, κ, λ̃, Q; t, P)` is
`Σ_{P̃} [U^{κ,ω}_Ind]^{Q}_{t_ω, P̃} [U^ω_twist]^{P̃,κ}_P` when `t = t_ω ω` with `t_ω ∈ T_ω`, and `0`
otherwise.

**Formalization Note** `U^{κ,ω}_Ind` is the base mission's `UIndLam` for `H_ω ≤ H` with the
`H`-irreps in their `H_ω`-adapted labels; its output label `Q : κ' → λ̃` is converted back to the
fixed basis label of `λ̃` by `adapt ω λ̃`. -/
def Nop (l : ΛH) : Matrix (NOut Ω BH NmW Ntw (Λω := Λω) l) (mackeyT H Ω Tω × BH l) ℂ :=
  Matrix.of fun o tP =>
    if h : ∃ a : Tω o.1.1, ((a : H) : G) * (o.1 : G) = (tP.1 : G) then
      ∑ Pt : Bω o.1.1 o.2.1.1,
        UIndLam (Tω o.1.1) (Bω o.1.1) (NmW o.1.1) (RHad H BH RH Bω NmW adapt o.1.1) o.2.1.1
            ⟨⟨o.2.2.1.1, o.2.2.1.2⟩, adapt o.1.1 o.2.2.1.1 o.2.2.2⟩ (Classical.choose h, Pt) *
          Utw o.1.1 l ⟨o.2.1, Pt⟩ tP.2
    else 0

/-- arXiv:2608.28573, Definition 5.3 and eq. (65), p.29–30, Algorithm 1 step 4: the operator
`A_λ = ⊕_{λ̃} A_{λ,λ̃} ⊗ I_{V_λ̃}`, controlled on `(λ, λ̃)`, sending `|κ, ω⟩|λ̃, Q⟩` to
`Σ_{μ ∈ M_{λ,λ̃}} [A_{λ,λ̃}]^μ_{κ,ω} |μ⟩|Q : λ̃ → μ⟩`. Its output label `(μ, Q : λ̃ → μ)` is the
subgroup-adapted basis vector of `⊕_{μ ∈ N⁺(λ)} V_μ`. -/
def Aop (l : ΛH) :
    Matrix (Σ μ : {μ : ΛG // l ∈ Nminus μ}, AdBas BH Nminus μ.1) (NOut Ω BH NmW Ntw (Λω := Λω) l)
      ℂ :=
  Matrix.of fun out o =>
    if e : out.2.1.1 = o.2.2.1.1 then
      (if cast (congrArg BH e) out.2.2 = o.2.2.2 then
        Ablock H Ω BH Nminus RG Bω NmW adapt Ntw Utw l o.2.2.1.1
          ⟨out.1.1, out.1.2, e ▸ out.2.1.2⟩ ⟨o.1, ⟨o.2.1.1, o.2.1.2, o.2.2.1.2⟩⟩
      else 0)
    else 0

end Mackey

end Supplement

end GL2QFT


