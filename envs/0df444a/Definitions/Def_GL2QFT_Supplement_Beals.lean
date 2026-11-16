-- Prove2me | Definitions.Def_GL2QFT_Supplement_Beals
-- name    : GL2QFT_Supplement_Beals
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:36:02.158541+00:00
-- url     : https://prove2.me/theorems/3c937c59-fde8-40b0-b9d9-e0a34654b310
-- title:
--   Registers and gates $U$, $V_k$, $R(\tau_k)$, $W_k$ of Beals' construction (§4)
-- statement:
--   The register model and gates of §4 (Figure 7, Definition 4.1), for $H<G$, a left transversal $T=\{\tau_1,\dots,\tau_n\}$ and $G$-irreps in subgroup-adapted bases.
--
--   1. **Registers** (in the ket order of (45)): transversal $T\sqcup\{\star\}$; an $H$-module register encoding every $B_\lambda$ injectively; $H$-irrep register $\widehat H\sqcup\{0\}$; successor register $\widehat G\sqcup\{0\}$; control $\lambda\in\widehat H$.
--   2. $|\phi_\lambda\rangle=\sum_{\mu\in N^+(\lambda)}\sqrt{d_\mu/(nd_\lambda)}\,|\mu\rangle$ (47); an **admissible** $U_\lambda$ is any unitary with $U_\lambda|0\rangle=|\phi_\lambda\rangle$; $U=|\star\rangle\langle\star|\otimes\sum_\lambda U_\lambda\otimes|\lambda\rangle\langle\lambda|+\sum_m|\tau_m\rangle\langle\tau_m|\otimes I\otimes I$ (48).
--   3. $X_k$ swaps $\star$ and $\tau_k$; $V_k$ applies $X_k$ when $\mu=0$ and $\tilde\lambda=\lambda$.
--   4. $R(\tau_k)$ applies $R_\mu(\tau_k)$ to the joint states $|Q\rangle|\tilde\lambda\rangle$ encoding $Q:\tilde\lambda\to\mu$, when the transversal register is $\star$; identity otherwise.
--   5. $W_k=R(\tau_k)\,U\,V_k\,U^\dagger R(\tau_k)^\dagger$ (52), the product $W_nW_{n-1}\cdots W_1$ (53), and the target state $|\star\rangle|\Psi_{k,P}\rangle|\lambda\rangle$ of (45)–(46),
--   $$|\Psi_{k,P}\rangle=\sum_{\mu\in N^+(\lambda)}\sum_{Q:\tilde\lambda\to\mu}\sqrt{\frac{d_\mu}{nd_\lambda}}\,[R_\mu(\tau_k)]^{Q:\tilde\lambda\to\mu}_{P:\lambda\to\mu}|Q\rangle|\tilde\lambda\rangle|\mu\rangle .$$
--
--   **Formalization Note** $\star$ and the initial states $|0\rangle$ are `none` in `Option` registers. $R(\tau_k)$ is controlled by $\mu$ and the transversal register only, as Definition 4.1 states.
-- source:
--   Bruinsma, Posta, Stokvis, Grinko, Ozols, Quantum Fourier transform toolbox, arXiv:2608.28573 (held version, sha256 ecd45073…), §4, Figure 7, eqs. (45)–(48), Definition 4.1, eq. (52)–(53), pp.23–25 (PDF pp.24–26)

import Definitions.Def_GL2QFT_InductionTransform

noncomputable section

open Classical

namespace GL2QFT

namespace Supplement

namespace Beals

open Induction
open scoped Matrix

variable {G : Type} [Group G] (T : Set G) [Fintype T]
variable {ΛH ΛG : Type} [Fintype ΛH] [Fintype ΛG] (BH : ΛH → Type) [∀ l, Fintype (BH l)]
  [∀ l, DecidableEq (BH l)] (Nminus : ΛG → Finset ΛH) (Mod : Type) [Fintype Mod]

/-- arXiv:2608.28573 (held version, sha256 ecd45073…), §4, p.23 and Figure 7 (PDF p.24): the
registers of the Beals implementation, in the ket order of (45) `|τ_k⟩|P⟩|0, 0⟩|λ⟩`:
1. the transversal register, basis `T ⊔ {⋆}` (`none` is `⋆`);
2. the `H`-module register `Mod`, holding the basis labels of every `V_λ` (through `emb`);
3. the `H`-irrep register, basis `Ĥ ⊔ {0}` (`none` is `|0⟩`);
4. the successor (`G`-irrep) register, basis `Ĝ ⊔ {0}` (`none` is `|0⟩`);
5. the control register `|λ⟩`, `λ ∈ Ĥ`. -/
abbrev Reg : Type := Option T × Mod × Option ΛH × Option ΛG × ΛH

/-- The computational basis vector `|r⟩` of the register space. -/
def ket (r : Reg T Mod (ΛH := ΛH) (ΛG := ΛG)) : Reg T Mod (ΛH := ΛH) (ΛG := ΛG) → ℂ :=
  fun s => if s = r then 1 else 0

variable (emb : ∀ l, BH l → Mod)

/-- §4, p.24: the joint state `|Q⟩|λ̃⟩` of the `H`-module and `H`-irrep registers encoding the
subgroup-adapted label `Q : λ̃ → μ ∈ B_μ`. -/
def encAd (μ : ΛG) (Q : AdBas BH Nminus μ) : Mod × Option ΛH := (emb Q.1.1 Q.2, some Q.1.1)

/-- The `G`-irrep dimension `d_μ = |B_μ|` and the `H`-irrep dimension `d_λ = |B_λ|`. -/
abbrev dG (μ : ΛG) : ℝ := Fintype.card (AdBas BH Nminus μ)
abbrev dH (l : ΛH) : ℝ := Fintype.card (BH l)

/-- arXiv:2608.28573, Definition 4.1, eq. (47), p.24 (PDF p.25): the state
`|ϕ_λ⟩ = Σ_{μ ∈ N⁺(λ)} √(d_μ/(n d_λ)) |μ⟩` of the successor register, `n = |T|`. -/
def phi (l : ΛH) : Option ΛG → ℂ
  | none => 0
  | some μ => if l ∈ Nminus μ then
      (Real.sqrt (dG BH Nminus μ / ((Fintype.card T : ℝ) * dH BH l)) : ℂ) else 0

/-- Definition 4.1, p.24: an admissible choice of the isometries `U_λ`: unitaries of the successor
register with `U_λ|0⟩ = |ϕ_λ⟩` ("`U_λ` can be any unitary embedding that maps `|0⟩` to `|ϕ_λ⟩`"). -/
def IsAdmissibleU (Ul : ΛH → Matrix (Option ΛG) (Option ΛG) ℂ) : Prop :=
  ∀ l, Ul l ∈ Matrix.unitaryGroup (Option ΛG) ℂ ∧ ∀ m, Ul l m none = phi T BH Nminus l m

/-- arXiv:2608.28573, Definition 4.1, eq. (48), p.24: the controlled isometry
`U := |⋆⟩⟨⋆| ⊗ Σ_λ U_λ ⊗ |λ⟩⟨λ| + Σ_m |τ_m⟩⟨τ_m| ⊗ I ⊗ I` (`U_λ` acts on the successor register;
the identity on the `H`-module and `H`-irrep registers). -/
def Ugate (Ul : ΛH → Matrix (Option ΛG) (Option ΛG) ℂ) :
    Matrix (Reg T Mod (ΛH := ΛH) (ΛG := ΛG)) (Reg T Mod (ΛH := ΛH) (ΛG := ΛG)) ℂ :=
  Matrix.of fun r' r =>
    if r.1 = none then
      (if r'.1 = none ∧ r'.2.1 = r.2.1 ∧ r'.2.2.1 = r.2.2.1 ∧ r'.2.2.2.2 = r.2.2.2.2 then
        Ul r.2.2.2.2 r'.2.2.2.1 r.2.2.2.1 else 0)
    else if r' = r then 1 else 0

/-- Definition 4.1, p.24: `X_k` swaps `⋆` and `τ_k` in the transversal register and fixes every
other `τ_m`. -/
def Xk (τ : T) : Matrix (Option T) (Option T) ℂ :=
  Matrix.of fun a b =>
    if b = none then (if a = some τ then 1 else 0)
    else if b = some τ then (if a = none then 1 else 0)
    else if a = b then 1 else 0

/-- Definition 4.1, p.24: `V_k`, controlled by `λ̃`, `μ` and `λ`: it acts as `X_k` on the transversal
register when `μ = 0` and `λ̃ = λ`, and as the identity otherwise. -/
def Vgate (τ : T) :
    Matrix (Reg T Mod (ΛH := ΛH) (ΛG := ΛG)) (Reg T Mod (ΛH := ΛH) (ΛG := ΛG)) ℂ :=
  Matrix.of fun r' r =>
    if r.2.2.2.1 = none ∧ r.2.2.1 = some r.2.2.2.2 then
      (if r'.2 = r.2 then Xk T τ r'.1 r.1 else 0)
    else if r' = r then 1 else 0

/-- arXiv:2608.28573, Definition 4.1, p.24: the gate `R(τ_k)`, controlled by `μ` and by the
transversal register being `⋆`: on the joint states `|⋆⟩|Q⟩|λ̃⟩|μ⟩|c⟩` with `μ ∈ Ĝ` and `|Q⟩|λ̃⟩`
encoding a label `Q : λ̃ → μ ∈ B_μ` it applies `R_μ(τ_k)` to `|Q⟩|λ̃⟩` (leaving `|μ⟩` and the external
control `|c⟩` unchanged); it acts as the identity when the transversal register is not `⋆` or the
other registers do not encode an element of `V_μ`:
`R(τ_k) = (I − Π_valid) + Σ_{c, μ} Σ_{Q', Q ∈ B_μ} [R_μ(τ_k)]^{Q'}_{Q} |⋆, Q', μ, c⟩⟨⋆, Q, μ, c|`. -/
def Rgate (RG : ∀ μ, G → Matrix (AdBas BH Nminus μ) (AdBas BH Nminus μ) ℂ) (τ : T) :
    Matrix (Reg T Mod (ΛH := ΛH) (ΛG := ΛG)) (Reg T Mod (ΛH := ΛH) (ΛG := ΛG)) ℂ :=
  let vec : ∀ μ, AdBas BH Nminus μ → ΛH → Reg T Mod (ΛH := ΛH) (ΛG := ΛG) :=
    fun μ Q c => (none, (encAd BH Nminus Mod emb μ Q).1, (encAd BH Nminus Mod emb μ Q).2, some μ, c)
  (1 - ∑ c : ΛH, ∑ μ : ΛG, ∑ Q : AdBas BH Nminus μ, Matrix.single (vec μ Q c) (vec μ Q c) 1) +
    ∑ c : ΛH, ∑ μ : ΛG, ∑ Q' : AdBas BH Nminus μ, ∑ Q : AdBas BH Nminus μ,
      Matrix.single (vec μ Q' c) (vec μ Q c) (RG μ (τ : G) Q' Q)

/-- arXiv:2608.28573, eq. (52), p.25 (PDF p.26): the gate sandwich
`W_k := R(τ_k) U V_k U† R(τ_k)†`. -/
def Wgate (RG : ∀ μ, G → Matrix (AdBas BH Nminus μ) (AdBas BH Nminus μ) ℂ)
    (Ul : ΛH → Matrix (Option ΛG) (Option ΛG) ℂ) (τ : T) :
    Matrix (Reg T Mod (ΛH := ΛH) (ΛG := ΛG)) (Reg T Mod (ΛH := ΛH) (ΛG := ΛG)) ℂ :=
  Rgate T BH Nminus Mod emb RG τ * Ugate T Mod Ul * Vgate T Mod τ *
    (Ugate T Mod Ul)ᴴ * (Rgate T BH Nminus Mod emb RG τ)ᴴ

/-- arXiv:2608.28573, eq. (53), p.25: the ordered product `W_n W_{n−1} ⋯ W_1` for the enumeration
`T = {τ_1, …, τ_n}` (`τ i` is `τ_{i+1}`). -/
def Wprod (RG : ∀ μ, G → Matrix (AdBas BH Nminus μ) (AdBas BH Nminus μ) ℂ)
    (Ul : ΛH → Matrix (Option ΛG) (Option ΛG) ℂ) (τ : Fin (Fintype.card T) ≃ T) :
    Matrix (Reg T Mod (ΛH := ΛH) (ΛG := ΛG)) (Reg T Mod (ΛH := ΛH) (ΛG := ΛG)) ℂ :=
  (List.ofFn fun i : Fin (Fintype.card T) => Wgate T BH Nminus Mod emb RG Ul (τ i.rev)).prod

/-- arXiv:2608.28573, eqs. (45)–(46), pp.23–24 (PDF pp.24–25): the image
`U_Ind|τ_k⟩|P⟩|0, 0⟩|λ⟩ = |⋆⟩|Ψ_{k,P}⟩|λ⟩` of a valid input under the induction transform in the Beals
encoding, `|Ψ_{k,P}⟩ = Σ_{μ ∈ N⁺(λ)} Σ_{Q : λ̃ → μ ∈ B_μ} √(d_μ/(n d_λ)) [R_μ(τ_k)]^{Q:λ̃→μ}_{P:λ→μ}
|Q⟩|λ̃⟩|μ⟩`. -/
def bealsTarget (RG : ∀ μ, G → Matrix (AdBas BH Nminus μ) (AdBas BH Nminus μ) ℂ) (τ : T)
    (l : ΛH) (P : BH l) : Reg T Mod (ΛH := ΛH) (ΛG := ΛG) → ℂ :=
  ∑ μ : ΛG, ∑ Q : AdBas BH Nminus μ,
    if h : l ∈ Nminus μ then
      ((Real.sqrt (dG BH Nminus μ / ((Fintype.card T : ℝ) * dH BH l)) : ℂ) *
          RG μ (τ : G) Q ⟨⟨l, h⟩, P⟩) •
        ket T Mod (none, emb Q.1.1 Q.2, some Q.1.1, some μ, l)
    else 0

end Beals

end Supplement

end GL2QFT


