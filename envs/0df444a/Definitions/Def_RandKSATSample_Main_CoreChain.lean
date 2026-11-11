-- Prove2me | Definitions.Def_RandKSATSample_Main_CoreChain
-- name    : RandKSATSample_Main_CoreChain
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T03:00:05.719016+00:00
-- url     : https://prove2.me/theorems/1f3f8bc8-89ac-4881-87a9-7a424b25bf8d
-- title:
--   The core marginal µbad, the block heat-bath kernel K, its Dirichlet form and spectral gap, γ_mix, the polymer representation (χ_a, Z(σ), a_Γ, U_Γ, K_Γ, Y_Γ, J_Γ) and the assumptions (4.1), (4.5)–(4.8)
-- statement:
--   $\mu^{\mathrm{bad}}$ is the marginal of $\mu_\Phi$ on $V_{\mathrm{bad}}$. The **random-scan block heat-bath chain** $\mathcal K$ chooses $j\in[s]$ uniformly and resamples the assignment of $B_j$ from $\mu^{\mathrm{bad}}(\cdot\mid X_{-j}=\sigma_{-j})$. Its Dirichlet form is $\mathcal E_{\mathcal K}(f,f)=\frac12\sum_{\sigma,\omega}\mu^{\mathrm{bad}}(\sigma)\mathcal K(\sigma,\omega)(f(\omega)-f(\sigma))^2$ and
--   $$\mathrm{gap}(\mathcal K)=\inf_{\mathrm{Var}_{\mu^{\mathrm{bad}}}(f)>0}\frac{\mathcal E_{\mathcal K}(f,f)}{\mathrm{Var}_{\mu^{\mathrm{bad}}}(f)},\qquad\mathrm{gap}(\mathcal K)=1\text{ if }|\Omega|=1.$$
--   (4.9): $c_k=1-\frac{25}{3k^3}$, $\rho_0=\rho e^{-2\tau}$, $\gamma_{\mathrm{mix}}=64\rho_0/c_k$.
--
--   **Polymer representation.** $\chi_a(\sigma)=1$ if all bad-variable literals of $C_a$ are false at $\sigma$ (also when there are none) and $0$ otherwise; $Z(\sigma)=\mathbb E_{\nu_{\mathrm{good}}}\prod_{a\in\mathcal C^{\mathrm{good}}}(1-\chi_a(\sigma)\mathbf 1_{E_a})$ (4.13). A polymer is a nonempty $\gamma\subseteq\mathcal C^{\mathrm{good}}$ with $H_\Psi[\gamma]$ connected; two polymers are incompatible if they intersect or an edge of $H_\Psi$ joins them. For a tuple $\Gamma=(\gamma_1,\dots,\gamma_\ell)$ (4.17):
--   $$U_\Gamma=\bigcup_i\gamma_i,\quad K_\Gamma=\sum_i|\gamma_i|,\quad a_\Gamma=\frac{\varphi(\Gamma)}{\ell!}\prod_i(-1)^{|\gamma_i|}q_{\gamma_i},\quad Y_\Gamma(\sigma)=\prod_{a\in U_\Gamma}\chi_a(\sigma),$$
--   and $J_\Gamma=\{i:B_i\cap\mathrm{vbl}(U_\Gamma)\neq\emptyset\}$ (4.60), $\mathrm{vbl}$ of the original clauses.
--
--   **Assumptions of §4.** (4.1): every $\Omega_i\neq\emptyset$ and every $\sigma\in\Omega$ extends to a satisfying assignment of $\Phi$. (4.5): every nonempty union $W_J$ of components has $|W_J|\le\frac k2|W_J\cap V_{\mathrm{high}}|$. (4.6): every connected $U$ has $I(U)\le C_{\mathrm{INC}}|U|+4\ln n$. (4.7): $|N_{H_\Psi}[a]|\le D$ for $a\in\mathcal C^{\mathrm{good}}$. (4.8): $\tau\ge1$ and the polymer-root estimate.
--
--   **Formalization Note.** Core configurations are all assignments of $V_{\mathrm{bad}}$; $\mu^{\mathrm{bad}}$ vanishes off $\Omega$, so every $\mu^{\mathrm{bad}}$-weighted sum is a sum over $\Omega$ and functions on $\Omega$ are functions on all core assignments whose values off $\Omega$ do not matter. Blocks are indexed by the components themselves. `gapK` is the real infimum, which is over a nonempty set bounded below by $0$ when $|\Omega|\ge2$, and $1$ when $|\Omega|\le1$. (4.5)'s second clause $\deg(v)\ge\Delta$ on $V_{\mathrm{high}}$ is the definition of $V_{\mathrm{high}}$ and is not repeated. Cluster labels are `ClusterLabel (Poly Φ)`.
-- source:
--   He, Li, Yang, Fast Almost-Uniform Sampling of Random k-SAT Solutions, arXiv:2610.10474 (version not printed; file sha256 563a4d84…), §4, pp. 21–23, (4.1), (4.4)–(4.9), (4.13), (4.14), (4.17), p. 31 (4.60)

import Mathlib
import Definitions.Def_RandKSATSample_Main_Structure
import Definitions.Def_RandKSATSample_Main_PolymerModel
import Definitions.Def_RandKSATSample_Main_FiniteInteraction

set_option autoImplicit false

open scoped BigOperators

namespace RandKSATSample.Main

noncomputable section

open Classical

/-!
# The core marginal, its cluster expansion and the block heat-bath chain

He, Li, Yang, *Fast Almost-Uniform Sampling of Random k-SAT Solutions*, arXiv:2610.10474
(version not printed; file sha256 563a4d84…), §4: p. 21 (`µbad`, `K`, `V_j`, Dirichlet form,
spectral gap with `gap(K) = 1` when `|Ω| = 1`), pp. 22–23 ((4.9), `χ_a`, (4.13), polymers,
(4.17)), p. 31 ((4.60)).

Core configurations are assignments to `V_bad` (`PartAssign n (Vbad Φ)`); `µbad` vanishes outside
the feasible set `Ω`, so sums over all core assignments weighted by `µbad` are sums over `Ω`. The
block index set `[s]` is the set `blocks Φ` of components themselves.
-/

variable {n m k : ℕ}

/-- A core configuration (an assignment to `V_bad`). -/
abbrev BadAssign (Φ : Formula n m k) : Type := PartAssign n (Vbad Φ)

/-- A block index: one of the components `B_1, …, B_s`. -/
abbrev Blk (Φ : Formula n m k) : Type := {B : Finset (Fin n) // B ∈ blocks Φ}

/-- `µbad`, the marginal of `µ_Φ` on `V_bad`. -/
def muBad (Φ : Formula n m k) (σ : BadAssign Φ) : ℝ :=
  ∑ η ∈ Finset.univ.filter (fun η : Assignment n => ∀ v (h : v ∈ Vbad Φ), η v = σ ⟨v, h⟩),
    muPhi Φ η

/-- The core configurations `σ, σ'` agree outside the block `B` (`X_{−j} = σ_{−j}` on
`V_bad ∖ B_j`). -/
def AgreeOutside (Φ : Formula n m k) (B : Finset (Fin n)) (σ σ' : BadAssign Φ) : Prop :=
  ∀ v : {v // v ∈ Vbad Φ}, v.1 ∉ B → σ v = σ' v

/-- The transition kernel `K` of the random-scan block heat-bath chain: choose a block `B_j`
uniformly and resample it from `µbad(· | X_{−j} = σ_{−j})`. -/
def heatBath (Φ : Formula n m k) (σ ω : BadAssign Φ) : ℝ :=
  (1 / ((blocks Φ).card : ℝ)) * ∑ B : Blk Φ,
    if AgreeOutside Φ B.1 σ ω then
      muBad Φ ω / ∑ ω' ∈ Finset.univ.filter (AgreeOutside Φ B.1 σ), muBad Φ ω'
    else 0

/-- The `t`-step kernel `K^t`. -/
def heatBathPow (Φ : Formula n m k) : ℕ → BadAssign Φ → BadAssign Φ → ℝ
  | 0 => fun σ ω => if σ = ω then 1 else 0
  | t + 1 => fun σ ω => ∑ u, heatBathPow Φ t σ u * heatBath Φ u ω

/-- The Dirichlet form `E_K(f,f) = ½ Σ_{σ,ω} µbad(σ) K(σ,ω) (f(ω) − f(σ))²`. -/
def dirichlet (Φ : Formula n m k) (f : BadAssign Φ → ℝ) : ℝ :=
  (1 / 2) * ∑ σ, ∑ ω, muBad Φ σ * heatBath Φ σ ω * (f ω - f σ) ^ 2

/-- The spectral gap `gap(K) = inf_{Var_{µbad}(f) > 0} E_K(f,f)/Var_{µbad}(f)`, with the paper's
convention `gap(K) = 1` when `|Ω| ≤ 1`. -/
def gapK (Φ : Formula n m k) : ℝ :=
  if (Omega Φ).card ≤ 1 then 1
  else sInf {g : ℝ | ∃ f : BadAssign Φ → ℝ, 0 < variance (muBad Φ) f ∧
    g = dirichlet Φ f / variance (muBad Φ) f}

/-- `c_k = 1 − 25/(3k³)` (4.9). -/
def ck (k : ℕ) : ℝ := 1 - 25 / (3 * (k : ℝ) ^ 3)

/-- `ρ0 = ρ e^{−2τ}` (4.9). -/
def rho0 (n m k : ℕ) : ℝ := rho n m k * Real.exp (-2 * tau n m k)

/-- `γ_mix = 64 ρ0 / c_k` (4.9). -/
def gammaMix (n m k : ℕ) : ℝ := 64 * rho0 n m k / ck k

/-! ## The polymer representation of the core marginal -/

/-- `χ_a(σ) = 1` if all bad-variable literals of `C_a` are false at `σ` (in particular if `C_a`
has none), `0` otherwise. -/
def chi (Φ : Formula n m k) (a : Fin m) (σ : BadAssign Φ) : ℝ :=
  if ∀ i : Fin k, ∀ h : (Φ a i).1 ∈ Vbad Φ, σ ⟨(Φ a i).1, h⟩ ≠ (Φ a i).2 then 1 else 0

/-- `Z(σ) = E_{ν_good} Π_{a ∈ C_good} (1 − χ_a(σ) 1_{E_a})` (4.13). -/
def Zcore (Φ : Formula n m k) (σ : BadAssign Φ) : ℝ :=
  (∑ τ : PartAssign n (Vgood Φ),
      ∏ a ∈ Cgood Φ, (1 - chi Φ a σ * (if Viol Φ a τ then 1 else 0))) /
    (Fintype.card (PartAssign n (Vgood Φ)) : ℝ)

/-- The polymers of `Ψ`: nonempty sets of good clause labels inducing a connected subgraph of
`H_Ψ`. -/
def polymers (Φ : Formula n m k) : Finset (Finset (Fin m)) :=
  (Cgood Φ).powerset.filter fun γ => IsConnectedSet (HPsi Φ) γ

/-- A polymer of `Ψ`. -/
abbrev Poly (Φ : Formula n m k) : Type := {γ : Finset (Fin m) // γ ∈ polymers Φ}

/-- Two polymers are incompatible when they intersect or an edge of `H_Ψ` joins them. -/
def polyInc (Φ : Formula n m k) (γ γ' : Poly Φ) : Prop :=
  (γ.1 ∩ γ'.1).Nonempty ∨ ∃ a ∈ γ.1, ∃ b ∈ γ'.1, (HPsi Φ).Adj a b

/-- `U_Γ = ⋃_i γ_i` (4.17). -/
def UGam (Φ : Formula n m k) (Γ : ClusterLabel (Poly Φ)) : Finset (Fin m) :=
  Finset.univ.biUnion fun i => (Γ.2 i).1

/-- `K_Γ = Σ_i |γ_i|` (4.17). -/
def KGam (Φ : Formula n m k) (Γ : ClusterLabel (Poly Φ)) : ℕ := ∑ i, (Γ.2 i).1.card

/-- `a_Γ = φ(Γ)/ℓ! · Π_i (−1)^{|γ_i|} q_{γ_i}` (4.17). -/
def aGam (Φ : Formula n m k) (Γ : ClusterLabel (Poly Φ)) : ℝ :=
  ((ursell (polyInc Φ) Γ.2 : ℤ) : ℝ) / ((Γ.1 + 1).factorial : ℝ) *
    ∏ i, ((-1 : ℝ) ^ (Γ.2 i).1.card * qS Φ (Γ.2 i).1)

/-- `Y_Γ(σ) = Π_{a ∈ U_Γ} χ_a(σ)` (4.17). -/
def YGam (Φ : Formula n m k) (Γ : ClusterLabel (Poly Φ)) (σ : BadAssign Φ) : ℝ :=
  ∏ a ∈ UGam Φ Γ, chi Φ a σ

/-- The geometric scope `J_Γ`: the blocks meeting `vbl(U_Γ)` (variables of the original clauses,
good and bad) (4.60). -/
def JGam (Φ : Formula n m k) (Γ : ClusterLabel (Poly Φ)) : Finset (Blk Φ) :=
  Finset.univ.filter fun B => (B.1 ∩ vblSet Φ (UGam Φ Γ)).Nonempty

/-! ## The standing assumptions of §4 -/

/-- (4.1): every `Ω_i` is nonempty, and every feasible core assignment extends to a satisfying
assignment of `Φ`. -/
def Cond41 (Φ : Formula n m k) : Prop :=
  (∀ B ∈ blocks Φ, (OmegaBlock Φ B).Nonempty) ∧
    ∀ σ ∈ Omega Φ, ∃ η : Assignment n, Sat Φ η ∧ ∀ v (h : v ∈ Vbad Φ), η v = σ ⟨v, h⟩

/-- (4.5), first clause: for every nonempty set of blocks with union `W_J`,
`|W_J| ≤ (k/2)|W_J ∩ V_high|` (its second clause, `deg(v) ≥ ∆` on `V_high`, is the definition of
`V_high`). -/
def Cond45 (Φ : Formula n m k) : Prop :=
  ∀ Jb ⊆ blocks Φ, Jb.Nonempty →
    ((Jb.biUnion id).card : ℝ) ≤ (k : ℝ) / 2 * ((Jb.biUnion id ∩ Vhigh Φ).card : ℝ)

/-- (4.6): every connected variable set `U` of `G_Φ` has `I(U) ≤ C_INC |U| + 4 ln n`. -/
def Cond46 (Φ : Formula n m k) : Prop :=
  ∀ U : Finset (Fin n), IsConnectedSet (primalGraph Φ) U →
    (incident Φ U : ℝ) ≤ CINC n m k * U.card + 4 * Real.log n

/-- (4.7): `|N_{H_Ψ}[a]| ≤ D` for every good clause `a`. -/
def Cond47 (Φ : Formula n m k) : Prop := ∀ a ∈ Cgood Φ, (closedNbhd Φ a).card ≤ Dpar n m k

/-- (4.8): `τ ≥ 1` and the polymer-root estimate. -/
def Cond48 (Φ : Formula n m k) : Prop := 1 ≤ tau n m k ∧ PolyRoot Φ

end

end RandKSATSample.Main


