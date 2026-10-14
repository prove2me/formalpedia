-- Prove2me | Definitions.Def_DRUQChance_Markov_Basic
-- name    : DRUQChance_Markov_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T18:48:04.658248+00:00
-- url     : https://prove2.me/theorems/6b57f797-b66e-4a2d-aacf-dbe767d098b5
-- title:
--   Markov ambiguity sets, essential strict feasibility, (S) at I = 1, problem (17) at I = 1 and system (26) (pp. 5–6, 11–12, 18)
-- statement:
--   This module fixes the objects of Hanasusanto, Roitch, Kuhn and Wiesemann (2015) that are needed to study individual chance constraints over **Markov ambiguity sets**. It builds on the published module `DRConvexOpt.Reform.Setting` (proper cones $\mathcal K$, dual cones $\mathcal K^\star$, confidence sets $\mathcal C_i$ of (5) and the nested moment ambiguity set $\mathcal P^n$ of (4)).
--
--   Throughout, $\tilde z \in \mathbb R^P$, $\tilde u \in \mathbb R^Q$, $A \in \mathbb R^{K\times P}$, $B \in \mathbb R^{K\times Q}$, $b \in \mathbb R^K$, and there is a single confidence set
--   $$\mathcal C_1 = \{(z,u) \in \mathbb R^P\times\mathbb R^Q : C_1 z + D_1 u \preccurlyeq_{\mathcal K_1} d_1\},$$
--   with $C_1 \in \mathbb R^{L_1\times P}$, $D_1 \in \mathbb R^{L_1\times Q}$, $d_1 \in \mathbb R^{L_1}$ and a cone $\mathcal K_1 \subseteq \mathbb R^{L_1}$.
--
--   1. **Markov ambiguity set** (p. 18): an instance of (4) with $I = 1$ and $\underline p_1 = \overline p_1 = 1$, i.e. $\mathcal P = \{\mathbb P : \mathbb E_{\mathbb P}[A\tilde z + B\tilde u] = b,\ \mathbb P[(\tilde z,\tilde u) \in \mathcal C_1] = 1\}$.
--   2. **Essential strict feasibility** (footnote 1, p. 6): $\mathcal C_1$ contains a point satisfying all non-polyhedral constraints of (5) strictly. We read this as: $\mathcal K_1 = \mathcal K_p \cap \mathcal K_n$ for a polyhedral cone $\mathcal K_p = \{y : Gy \ge 0\}$ and a closed convex cone $\mathcal K_n$, and some $(z,u)$ has $d_1 - C_1 z - D_1 u \in \mathcal K_p \cap \operatorname{int}\mathcal K_n$. For polyhedral $\mathcal K_1$ (take $\mathcal K_n = \mathbb R^{L_1}$) this is plain nonemptiness of $\mathcal C_1$; for a cone with no polyhedral part it is strict feasibility.
--   3. **The Slater condition (S) for $I = 1$** (p. 11): $b$ lies in the interior of the convex set $\{Az + Bu : (z,u) \in \mathcal C_1\}$.
--   4. **The index set $\mathcal L$** of (17) (p. 12) for $I = 1$ and a system $Sz \le t$ with rows $s_j^\top$, $j \in \mathcal J = \{1,\dots,J\}$: $\mathcal L = \{j : \exists (z,u) \in \mathcal C_1,\ s_j^\top z > t_j\}$.
--   5. **The conic program (17) for $I = 1$** (p. 12), where $\mathcal A(1) = \{1\}$:
--   $$\begin{aligned} \sup\ & b^\top\gamma + \underline p_1\lambda - \overline p_1\kappa\\ \text{s.t. }& \gamma \in \mathbb R^K,\ \lambda,\kappa \ge 0,\ \phi \in \mathcal K_1^\star,\ \tau_j \ge 0,\ \psi_j \in \mathcal K_1^\star\ (j \in \mathcal L)\\ & \lambda - \kappa + d_1^\top\phi \le 1,\quad A^\top\gamma = C_1^\top\phi,\quad B^\top\gamma = D_1^\top\phi\\ & \lambda - \kappa + d_1^\top\psi_j - \tau_j t_j \le 0,\quad A^\top\gamma + \tau_j s_j = C_1^\top\psi_j,\quad B^\top\gamma = D_1^\top\psi_j \quad (j \in \mathcal L). \end{aligned}$$
--   The module defines its feasible set and its objective separately.
--   6. **The system (26)** of Theorem 7 (p. 18), for $s \in \mathbb R^P$, $t \in \mathbb R$, $\epsilon \in \mathbb R$: there are $\beta \in \mathbb R$, $\gamma \in \mathbb R^K$, $\phi,\psi \in \mathcal K_1^\star$, $\tau \ge 0$ with
--   $$\beta + b^\top\gamma \ge (1-\epsilon)\tau,\quad \beta + d_1^\top\phi \le \tau,\quad \beta + d_1^\top\psi \le t,\quad A^\top\gamma = C_1^\top\phi,\quad B^\top\gamma = D_1^\top\phi,\quad A^\top\gamma + s = C_1^\top\psi,\quad B^\top\gamma = D_1^\top\psi.$$
--
--   These are the objects in which Theorem 3 (case $I = 1$), Theorem 7 and the feasibility claim of §5 are stated.
--
--   **Formalization Note** `paperAmbiguitySet` uses the reused `AmbData` and confidence sets but asks only for integrability of $A\tilde z+B\tilde u$; this preserves the paper's void expectation condition when $K=0$. $I = 1$ is `AmbData nP nQ nK 0` with the single index `0 : Fin 1`; the paper's $d_1$ is the field `c 0` (the reused module follows Wiesemann, Kuhn and Sim, who write $c_i$). $\lambda,\kappa$ are `lam`, `kap`. In (17) the variables $\tau_j,\psi_j$ are indexed by all of $\mathcal J$, but are constrained only for $j \in \mathcal L$; those with $j \notin \mathcal L$ are unused. The essential-strict-feasibility reading quantifies over all decompositions $\mathcal K_1 = \mathcal K_p \cap \mathcal K_n$ rather than fixing one coordinate split, since the paper does not fix a representation of $\mathcal K_1$.
-- source:
--   Hanasusanto, Roitch, Kuhn & Wiesemann, A distributionally robust perspective on uncertainty quantification and chance constrained programming, Math. Program. 151(1) (2015); authors' accepted manuscript, pp. 5–6 ((4), (5), footnote 1), p. 11 ((S)), p. 12 ((17)), p. 18 (Markov ambiguity sets, (26))

import Mathlib
import Definitions.Def_DRConvexOpt_Reform_Setting

namespace DRUQChance.Markov

open MeasureTheory Matrix DRConvexOpt.Reform

/-- The paper's ambiguity set (4) at `I = 1`. The expectation condition requires the
observed moment `A z + B u` to be integrable. In particular, when `nK = 0` the
expectation condition is void, as stated on p. 6. -/
def paperAmbiguitySet {nP nQ nK : ℕ} (amb : AmbData nP nQ nK 0) :
    Set (Measure ((Fin nP → ℝ) × (Fin nQ → ℝ))) :=
  {μ | IsProbabilityMeasure μ ∧
    Integrable (fun ω => amb.A *ᵥ ω.1 + amb.B *ᵥ ω.2) μ ∧
    ∫ ω, (amb.A *ᵥ ω.1 + amb.B *ᵥ ω.2) ∂μ = amb.b ∧
    ∀ i, μ.real (amb.conf i) ∈ Set.Icc (amb.plo i) (amb.phi i)}

/-- Markov ambiguity sets, p. 18: instances of (4) with `I = 1` (the data `amb : AmbData nP nQ nK 0`,
whose single confidence set is `amb.conf 0`) and `p̲₁ = p̄₁ = 1`. -/
def IsMarkov {nP nQ nK : ℕ} (amb : AmbData nP nQ nK 0) : Prop :=
  amb.plo 0 = 1 ∧ amb.phi 0 = 1

/-- Essential strict feasibility, footnote 1, p. 6: the confidence set
`{(z, u) : C z + D u ≼_K c}` contains a point that satisfies all non-polyhedral constraints
strictly. Read as: `K` splits as `K = Kp ∩ Kn` with `Kp = {y : G y ≥ 0}` polyhedral and `Kn` a
closed convex cone, and some `(z, u)` has `c − (C z + D u) ∈ Kp ∩ interior Kn`. -/
def EssStrictFeas {nP nQ m : ℕ} (C : Matrix (Fin m) (Fin nP) ℝ) (D : Matrix (Fin m) (Fin nQ) ℝ)
    (c : Fin m → ℝ) (K : Set (Fin m → ℝ)) : Prop :=
  ∃ (r : ℕ) (G : Matrix (Fin r) (Fin m) ℝ) (Kn : Set (Fin m → ℝ)),
    IsClosed Kn ∧ Convex ℝ Kn ∧ (∀ y ∈ Kn, ∀ a : ℝ, 0 ≤ a → a • y ∈ Kn) ∧
    K = {y | ∀ k, 0 ≤ (G *ᵥ y) k} ∩ Kn ∧
    ∃ ω : (Fin nP → ℝ) × (Fin nQ → ℝ),
      c - (C *ᵥ ω.1 + D *ᵥ ω.2) ∈ {y | ∀ k, 0 ≤ (G *ᵥ y) k} ∩ interior Kn

/-- The Slater condition (S) for `I = 1`, p. 11: `b` lies in the interior of the convex set
`{A z + B u : (z, u) ∈ C₁}`. -/
def SlaterI1 {nP nQ nK : ℕ} (amb : AmbData nP nQ nK 0) : Prop :=
  amb.b ∈ interior
    ((fun ω : (Fin nP → ℝ) × (Fin nQ → ℝ) => amb.A *ᵥ ω.1 + amb.B *ᵥ ω.2) '' amb.conf 0)

open Classical in
/-- The index set `ℒ` of (17), p. 12, for `I = 1`: the rows `j` of `S z ≤ t` violated by some
`(z, u) ∈ C₁`, i.e. `ℒ = {j : ∃ (z, u) ∈ C₁, s_jᵀ z > t_j}` (row `j` of `S` is `s_jᵀ`). -/
noncomputable def violIdx {nP nQ nK nJ : ℕ} (amb : AmbData nP nQ nK 0)
    (S : Matrix (Fin nJ) (Fin nP) ℝ) (t : Fin nJ → ℝ) : Finset (Fin nJ) :=
  Finset.univ.filter fun j => ∃ ω ∈ amb.conf 0, t j < S j ⬝ᵥ ω.1

/-- The feasible set of the conic program (17), p. 12, for `I = 1` (so `𝒜(1) = {1}`): the
variables are `γ ∈ ℝ^K`, `λ, κ ≥ 0`, `φ ∈ K₁⋆`, and for `j ∈ ℒ` also `τ_j ≥ 0`, `ψ_j ∈ K₁⋆`;
`d₁` is `amb.c 0`. Variables indexed by `j ∉ ℒ` are unconstrained. -/
def UQFeasible {nP nQ nK nJ : ℕ} (amb : AmbData nP nQ nK 0) (S : Matrix (Fin nJ) (Fin nP) ℝ)
    (t : Fin nJ → ℝ) (γ : Fin nK → ℝ) (lam kap : ℝ) (φ : Fin (amb.L 0) → ℝ) (τ : Fin nJ → ℝ)
    (ψ : Fin nJ → Fin (amb.L 0) → ℝ) : Prop :=
  0 ≤ lam ∧ 0 ≤ kap ∧ φ ∈ dualCone (amb.K 0) ∧
  (lam - kap) + amb.c 0 ⬝ᵥ φ ≤ 1 ∧
  amb.Aᵀ *ᵥ γ = (amb.C 0)ᵀ *ᵥ φ ∧ amb.Bᵀ *ᵥ γ = (amb.D 0)ᵀ *ᵥ φ ∧
  ∀ j ∈ violIdx amb S t,
    0 ≤ τ j ∧ ψ j ∈ dualCone (amb.K 0) ∧
    (lam - kap) + amb.c 0 ⬝ᵥ ψ j - τ j * t j ≤ 0 ∧
    amb.Aᵀ *ᵥ γ + τ j • S j = (amb.C 0)ᵀ *ᵥ ψ j ∧ amb.Bᵀ *ᵥ γ = (amb.D 0)ᵀ *ᵥ ψ j

/-- The objective of (17), p. 12, for `I = 1`: `bᵀγ + p̲₁ λ − p̄₁ κ`. -/
def uqObjective {nP nQ nK : ℕ} (amb : AmbData nP nQ nK 0) (γ : Fin nK → ℝ) (lam kap : ℝ) : ℝ :=
  amb.b ⬝ᵥ γ + amb.plo 0 * lam - amb.phi 0 * kap

/-- The system (26) of Theorem 7, p. 18, at a fixed decision (`s`, `t` stand for `s(x)`, `t(x)`):
`β ∈ ℝ`, `γ ∈ ℝ^K`, `φ, ψ ∈ K₁⋆`, `τ ≥ 0` with
`β + bᵀγ ≥ (1 − ε)τ`, `β + d₁ᵀφ ≤ τ`, `β + d₁ᵀψ ≤ t`, `Aᵀγ = C₁ᵀφ`, `Bᵀγ = D₁ᵀφ`,
`Aᵀγ + s = C₁ᵀψ`, `Bᵀγ = D₁ᵀψ`. -/
def System26 {nP nQ nK : ℕ} (amb : AmbData nP nQ nK 0) (s : Fin nP → ℝ) (t ε β : ℝ)
    (γ : Fin nK → ℝ) (φ ψ : Fin (amb.L 0) → ℝ) (τ : ℝ) : Prop :=
  φ ∈ dualCone (amb.K 0) ∧ ψ ∈ dualCone (amb.K 0) ∧ 0 ≤ τ ∧
  (1 - ε) * τ ≤ β + amb.b ⬝ᵥ γ ∧ β + amb.c 0 ⬝ᵥ φ ≤ τ ∧ β + amb.c 0 ⬝ᵥ ψ ≤ t ∧
  amb.Aᵀ *ᵥ γ = (amb.C 0)ᵀ *ᵥ φ ∧ amb.Bᵀ *ᵥ γ = (amb.D 0)ᵀ *ᵥ φ ∧
  amb.Aᵀ *ᵥ γ + s = (amb.C 0)ᵀ *ᵥ ψ ∧ amb.Bᵀ *ᵥ γ = (amb.D 0)ᵀ *ᵥ ψ

end DRUQChance.Markov


