-- Prove2me | Definitions.Def_PetzMix_petzAmp
-- name    : PetzMix_petzAmp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T04:13:13.020395+00:00
-- url     : https://prove2.me/theorems/4055d1d0-4505-418c-8f80-4ae14ae0e122
-- title:
--   Block Gibbs states, conditional expectation $E_B$, Petz amplitude $Q_B$, $F_B(z)$ and Assumptions 4.3–4.4
-- statement:
--   Fix a block $B$ and write $T=\tau_B\otimes I_{B^c}$ for a full-rank state $\tau_B$ on $B$.
--
--   1. The block Hamiltonian $H_B=\sum_{\{i,i+1\}\subset B}h^{(i)}_{i,i+1}$ and its Gibbs state $\tau_B=e^{-\beta H_B}/\operatorname{tr}_B e^{-\beta H_B}$ (101), (103).
--   2. The **product conditional expectation** $E_B(A)=I_B\otimes\operatorname{tr}_B\big[(\tau_B^{1/2}\otimes I_{B^c})A(\tau_B^{1/2}\otimes I_{B^c})\big]$ (55).
--   3. The **conditional Petz amplitude** $Q_B=\sigma_\beta^{1/2}\big(\tau_B^{-1/2}\otimes\sigma_{\beta,B^c}^{-1/2}\big)$ (56).
--   4. Complex matrix powers $A^z=\exp(z\log A)$ for positive definite $A$, and the analytic family $F_B(z)=\sigma_\beta^{z}\big(\tau_B^{-z}\otimes\sigma_{\beta,B^c}^{-z}\big)$, $0\le\operatorname{Re}z\le1$ (104); $F_B(1/2)=Q_B$.
--   5. **Assumption 4.3** for $B$ with constants $c_0,C_Q,M_Q,\mu_Q$: for every integer $r\ge0$ there is $\tilde Q_{B,r}$ supported on $N_{r+c_0}(\partial B)$ with
--   $$
--   \|Q_B-\tilde Q_{B,r}\|\le C_Qe^{-\mu_Qr},\qquad \|Q_B\|+\|\tilde Q_{B,r}\|\le M_Q .
--   $$
--   6. **Assumption 4.4** for $B$ with constants $C_F,\mu_F$: for every decomposition $B=L,G_L,V,G_R,R$ into five consecutive intervals, with $m=\min\{|G_L|,|G_R|\}$,
--   $$
--   \|(\tau_B)_{LRV}-(\tau_B)_{LR}\otimes(\tau_B)_V\|_1\le C_Fe^{-\mu_Fm}.
--   $$
--
--   These are the static objects of Sections 4 and 5.
--
--   **Formalization Note** $T$ is positive definite, acts trivially on $B^c$, and has $\operatorname{tr}_B$ equal to the identity; §5 uses $T=d^{|B^c|}\,\mathrm{gibbs}(\beta,H_B)$. The two assumptions are predicates of one block and its constants; theorems quantify the constants before $n$ and $B$. $c_0$ is a natural number (distances are integers). In Assumption 4.4 the five intervals are given by cut points along the block from its left end and may be empty; marginals are the public normalized full-space `marg`/`margProd`, which have the same trace norms.
-- source:
--   Kim, Rapid mixing of quantum spin chains at any finite temperature, arXiv:2610.01190 (held copy sha256 38ff48d0…), Definition 4.1, (55)–(56), p.19; Assumptions 4.3–4.4, (60)–(62), p.20; §5 Setup, (101)–(103), p.28; (104), p.29

import Mathlib
import Definitions.Def_PetzMix_heatBathGen
import Definitions.Def_QDSGibbs_traceNorm
import Definitions.Def_QDSGibbs_cov

open scoped Matrix ComplexOrder

set_option autoImplicit false

namespace PetzMix

open QDSGibbs

/-- The block Hamiltonian `H_B = Σ_{{i,i+1} ⊂ B} h^{(i)}_{i,i+1}`: the interactions contained
entirely in `B` (Kim, arXiv:2610.01190 (held copy sha256 38ff48d0…), §5 Setup, (101), p.28). As a
full-space operator `H_B ⊗ I_{B^c}`. -/
noncomputable def HB {n d : ℕ} (h : Fin n → ChainOp n d) (B : Finset (Fin n)) : ChainOp n d :=
  ∑ i ∈ Finset.univ.filter (fun i => bond i ⊆ B), h i

/-- The block Gibbs state tensored with the identity, `τ_B ⊗ I_{B^c}`, where
`τ_B = e^{−βH_B} / tr_B[e^{−βH_B}]` (arXiv:2610.01190, (103), p.28).

**Formalization Note** The full-space `gibbs β H_B` equals `τ_B ⊗ I_{B^c} / d^{|B^c|}`, so
`τ_B ⊗ I_{B^c} = d^{|B^c|} · gibbs β H_B`. -/
noncomputable def tauFull {n d : ℕ} (β : ℝ) (h : Fin n → ChainOp n d) (B : Finset (Fin n)) :
    ChainOp n d :=
  ((dimOf (fun _ : Fin n => d) Bᶜ : ℂ)) • gibbs β (HB h B)

/-- `T = τ_B ⊗ I_{B^c}` for a **full-rank state `τ_B` on `B`** (arXiv:2610.01190, §4.1, p.19: "Let
τ_B be a full-rank state on B"): `T` is positive definite, acts trivially on `B^c`, and
`ptr B T = tr(τ_B) · I = I`.

**Formalization Note** §4 is stated for an arbitrary full-rank `τ_B`; §5 and the main theorem use
`T = tauFull β h B`. -/
def IsBlockRef {n d : ℕ} (B : Finset (Fin n)) (T : ChainOp n d) : Prop :=
  T.PosDef ∧ SupportedOn B T ∧ ptr B T = 1

/-- The **product conditional expectation** (arXiv:2610.01190, Definition 4.1, (55), p.19):
`E_B(A) = I_B ⊗ tr_B[(τ_B^{1/2} ⊗ I_{B^c}) A (τ_B^{1/2} ⊗ I_{B^c})]`, with `T = τ_B ⊗ I_{B^c}`.

**Formalization Note** `(τ_B ⊗ I)^{1/2} = τ_B^{1/2} ⊗ I` is `msqrt T`, and `I_B ⊗ tr_B[·]` is the
public unnormalized `ptr B`. -/
noncomputable def condExp {n d : ℕ} (B : Finset (Fin n)) (T A : ChainOp n d) : ChainOp n d :=
  ptr B (msqrt T * A * msqrt T)

/-- The **conditional Petz amplitude** (arXiv:2610.01190, Definition 4.1, (56), p.19):
`Q_B = σ^{1/2} (τ_B^{−1/2} ⊗ σ_{B^c}^{−1/2})`, `σ_{B^c} = tr_B[σ]`, with `T = τ_B ⊗ I_{B^c}`.

**Formalization Note** `τ_B^{−1/2} ⊗ σ_{B^c}^{−1/2} = (τ_B^{−1/2} ⊗ I)(I_B ⊗ σ_{B^c}^{−1/2})` is
`misqrt T * misqrt (ptr B σ)`; the two factors commute. -/
noncomputable def petzAmp {n d : ℕ} (σ : ChainOp n d) (B : Finset (Fin n)) (T : ChainOp n d) :
    ChainOp n d :=
  msqrt σ * misqrt T * misqrt (ptr B σ)

/-- The complex power `A^z = exp(z log A)` of a positive definite matrix (arXiv:2610.01190, (104),
p.29).

**Formalization Note** `cfc Real.log A` is the Hermitian logarithm of `A`, and `exp` is the matrix
exponential `NormedSpace.exp`; for positive definite `A` this is the holomorphic functional calculus
of `z ↦ A^z`. -/
noncomputable def cpow {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) (z : ℂ) :
    Matrix ι ι ℂ :=
  NormedSpace.exp (z • cfc Real.log A)

/-- The interpolation family `F_B(z) = σ_β^z (τ_B^{−z} ⊗ σ_{β,B^c}^{−z})`, `0 ≤ Re z ≤ 1`
(arXiv:2610.01190, (104), p.29), with `σ_β = gibbs β (Σ_i h i)` and `τ_B` the block Gibbs state of
(103).

**Formalization Note** `τ_B^{−z} ⊗ σ_{B^c}^{−z} = (τ_B ⊗ I)^{−z} (I_B ⊗ σ_{B^c})^{−z}` is
`cpow (tauFull β h B) (−z) * cpow (ptr B σ) (−z)` (the two factors commute). The order of the
factors is the paper's. -/
noncomputable def FB {n d : ℕ} (β : ℝ) (h : Fin n → ChainOp n d) (B : Finset (Fin n)) (z : ℂ) :
    ChainOp n d :=
  cpow (gibbs β (∑ i, h i)) z * cpow (tauFull β h B) (-z) * cpow (ptr B (gibbs β (∑ i, h i))) (-z)

/-- **Assumption 4.3 (boundary quasi-locality of the Petz amplitude)** for one block `B` and one
`T = τ_B ⊗ I`, with constants `c₀, C_Q, M_Q, µ_Q` (arXiv:2610.01190, Assumption 4.3, (60), p.20):
for every integer `r ≥ 0` there is `Q̃_{B,r} ∈ A_{N_{r+c₀}(∂B)}` with
`‖Q_B − Q̃_{B,r}‖ ≤ C_Q e^{−µ_Q r}` and `‖Q_B‖ + ‖Q̃_{B,r}‖ ≤ M_Q`.

**Formalization Note** A predicate of `(σ, B, T)` and the constants; the theorems quantify the
constants before the system (constants independent of `n` and `B`). `c₀` is a natural number: the
distance is integer valued, so `N_{r+c₀} = N_{r+⌊c₀⌋}`. -/
def Asm43 {n d : ℕ} (σ : ChainOp n d) (B : Finset (Fin n)) (T : ChainOp n d) (c₀ : ℕ)
    (CQ MQ μQ : ℝ) : Prop :=
  ∀ r : ℕ, ∃ Qt : ChainOp n d, SupportedOn (nbhd (r + c₀) (bdry B)) Qt ∧
    opNorm (petzAmp σ B T - Qt) ≤ CQ * Real.exp (-(μQ * r)) ∧
    opNorm (petzAmp σ B T) + opNorm Qt ≤ MQ

/-- **Assumption 4.4 (boundary-to-interior Gibbs factorization)** for the block `B = cycBlock ℓ a`
and `T = τ_B ⊗ I`, with constants `C_F, µ_F` (arXiv:2610.01190, Assumption 4.4, (61)–(62), p.20):
for every decomposition `B = L, G_L, V, G_R, R` into five consecutive intervals, with
`m = min{|G_L|, |G_R|}`,
`‖(τ_B)_{LRV} − (τ_B)_{LR} ⊗ (τ_B)_V‖₁ ≤ C_F e^{−µ_F m}`.

**Formalization Note** The decomposition is given by cut points `0 ≤ p₁ ≤ p₂ ≤ p₃ ≤ p₄ ≤ ℓ` along the
block from its left end `a`: `L = [0, p₁)`, `G_L = [p₁, p₂)`, `V = [p₂, p₃)`, `G_R = [p₃, p₄)`,
`R = [p₄, ℓ)`; every part may be empty. Marginals are the public normalized full-space `marg` and
`margProd` of the normalized state `T / d^{|B^c|}` (= `τ_B ⊗ I_{B^c}/d^{|B^c|}`), which have the
same trace norms as the paper's marginals. -/
def Asm44 {n d : ℕ} (a : Fin n) (ℓ : ℕ) (T : ChainOp n d) (CF μF : ℝ) : Prop :=
  ∀ p₁ p₂ p₃ p₄ : ℕ, p₁ ≤ p₂ → p₂ ≤ p₃ → p₃ ≤ p₄ → p₄ ≤ ℓ →
    traceNorm
        (marg (seg a 0 p₁ ∪ seg a p₄ ℓ ∪ seg a p₂ p₃)
            (((dimOf (fun _ : Fin n => d) (cycBlock ℓ a)ᶜ : ℂ))⁻¹ • T) -
          margProd (seg a 0 p₁ ∪ seg a p₄ ℓ) (seg a p₂ p₃)
            (((dimOf (fun _ : Fin n => d) (cycBlock ℓ a)ᶜ : ℂ))⁻¹ • T)) ≤
      CF * Real.exp (-(μF * ((min (p₂ - p₁) (p₄ - p₃) : ℕ) : ℝ)))

end PetzMix


