-- Prove2me | Definitions.Def_BipColorHard_RandomGraph
-- name    : BipColorHard_RandomGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:34:57.955692+00:00
-- url     : https://prove2.me/theorems/32830b4e-746e-4ebb-a85d-36fee3cc038c
-- title:
--   The entropy functional $\Psi$, the random base graph $\Gamma$, $\nu_\varphi$, $\xi_m$, $\mu_\Gamma$, and the phase family
-- statement:
--   For probability vectors $\alpha,\beta$ on $[q]$, $\Xi(\alpha,\beta)$ is the set of nonnegative $q\times q$ matrices with zero diagonal, row sums $\alpha$ and column sums $\beta$. The pair is **feasible** if $\Xi(\alpha,\beta)\ne\emptyset$, and on feasible pairs
--   $$\Psi(\alpha,\beta)=\max_{\xi\in\Xi(\alpha,\beta)}\big(DH(\xi)-(D-1)H(\alpha)-(D-1)H(\beta)\big),$$
--   with $0\log0=0$. $\mathcal P$ is the set of global maximizers. A maximizer $\varphi=(\alpha,\beta)$ determines $P_{\varphi,i}\propto\alpha_i^{1/p}$, $R_{\varphi,i}\propto\beta_i^{1/p}$, and $\nu_\varphi(\tau,\tau')=P_\varphi^{\otimes m}(\tau)R_\varphi^{\otimes m}(\tau')$.
--
--   The **random bipartite base graph** $\Gamma$ has, on each side, $n$ ordinary vertices and $m$ ordered open vertices: $D-1$ independent uniform perfect matchings between the two sides, and one more between the ordinary vertices. $\mu_\Gamma(\tau,\tau')$ is the probability that the left and right open vertices receive the colors $\tau,\tau'$ under a uniformly random proper coloring. With $P_S,R_S$ the phases of Lemma 28,
--   $$\xi_m(\tau,\tau')=\frac1{2Q}\sum_{S\in\Omega}\big(P_S^{\otimes m}(\tau)R_S^{\otimes m}(\tau')+R_S^{\otimes m}(\tau)P_S^{\otimes m}(\tau')\big).$$
--
--   These are the objects of the finite-port theorem and of the base graph used to build the gadget.
--
--   **Formalization Note** A perfect matching is a permutation of the index set of a side. Since the model is uniform on a finite space, "with positive probability" is the existence of a point of the model, and no measure theory is needed; probabilities are ratios of counts. $\Psi$ is a real supremum, which is the maximum on feasible pairs because $\Xi$ is compact. An infeasible pair has supremum $0$ rather than the manuscript's $-\infty$, so $\mathcal P$ is defined over feasible pairs only.
-- source:
--   Galanis, Guo, He, Štefankovič, Vigoda, NP-hardness for Bipartite Colorings up to the Maximum Degree, manuscript of Nov. 3, 2026 (sha256 78a66d1f…), §6.2, pp.27–28 (PDF pp.29–30), (29); §7.1, p.30 (PDF p.32); §A.1, p.46 (PDF p.48); Lemma 28, p.31 (PDF p.33)

import Definitions.Def_BipColorHard_Objective
import Definitions.Def_BipColorHard_PhaseLabeling

set_option autoImplicit false

namespace BipColorHard

variable {q : ℕ}

/-- `x^{⊗m}(τ) = ∏_j x_{τ_j}`, the product distribution on `[q]^m`. Galanis, Guo, He, Štefankovič, Vigoda,
manuscript of Nov. 3, 2026 (sha256 78a66d1f…), §A.1, p.46 (PDF p.48). -/
def tensorPow {m : ℕ} (x : Fin q → ℝ) (τ : Fin m → Fin q) : ℝ := ∏ j, x (τ j)

/-- `Ξ(α, β)`: nonnegative `q × q` matrices with zero diagonal, row sums `α` and column sums `β`,
§A.1, p.46 (PDF p.48). -/
def IsCoupling (α β : Fin q → ℝ) (ξ : Fin q → Fin q → ℝ) : Prop :=
  (∀ i j, 0 ≤ ξ i j) ∧ (∀ i, ξ i i = 0) ∧ (∀ i, ∑ j, ξ i j = α i) ∧ ∀ j, ∑ i, ξ i j = β j

/-- `H(a) = -∑ a_i log a_i`, with `0 log 0 = 0`, §A.1, p.46 (PDF p.48). -/
noncomputable def entVec (a : Fin q → ℝ) : ℝ := ∑ i, Real.negMulLog (a i)

/-- `H(ξ) = -∑ ξ_{ij} log ξ_{ij}`, with `0 log 0 = 0`, §A.1, p.46 (PDF p.48). -/
noncomputable def entMat (ξ : Fin q → Fin q → ℝ) : ℝ := ∑ i, ∑ j, Real.negMulLog (ξ i j)

/-- The pair `(α, β)` is **feasible**, §A.1, p.46 (PDF p.48): two probability vectors with `Ξ(α, β) ≠ ∅`. -/
def PsiFeasible (α β : Fin q → ℝ) : Prop :=
  (∀ i, 0 ≤ α i) ∧ (∀ i, 0 ≤ β i) ∧ ∑ i, α i = 1 ∧ ∑ i, β i = 1 ∧ ∃ ξ, IsCoupling α β ξ

/-- `Ψ(α, β) = max_{ξ ∈ Ξ(α, β)} (D H(ξ) - (D - 1) H(α) - (D - 1) H(β))`, §A.1, p.46 (PDF p.48).

**Formalization Note.** `Ξ(α, β)` is compact and the objective is continuous, so on a feasible pair the real
`sSup` is the maximum. An infeasible pair has `sSup ∅ = 0`, not the manuscript's `-∞`; this is why the set of
global maximizers `psiMaxSet` is restricted to feasible pairs. -/
noncomputable def psi (D : ℕ) (α β : Fin q → ℝ) : ℝ :=
  sSup {v | ∃ ξ, IsCoupling α β ξ ∧
    v = (D : ℝ) * entMat ξ - ((D : ℝ) - 1) * entVec α - ((D : ℝ) - 1) * entVec β}

/-- `𝒫`, the set of global maximizers of `Ψ` over its domain, the feasible pairs, §A.1, p.46 (PDF p.48). -/
def psiMaxSet (q D : ℕ) : Set ((Fin q → ℝ) × (Fin q → ℝ)) :=
  {φ | PsiFeasible φ.1 φ.2 ∧ ∀ α β : Fin q → ℝ, PsiFeasible α β → psi D α β ≤ psi D φ.1 φ.2}

/-- `P_{φ,i} = a_i^{1/p} / ∑_j a_j^{1/p}` (also `R_{φ,i}`), §A.1, p.46 (PDF p.48). -/
noncomputable def openDist (p : ℝ) (a : Fin q → ℝ) (i : Fin q) : ℝ :=
  a i ^ (1 / p) / ∑ j, a j ^ (1 / p)

/-- The exponent `p = D/(D - 1)`, Lemma 12, p.12 (PDF p.14), with the `D` of §3. -/
noncomputable def expP (D : ℕ) : ℝ := (D : ℝ) / ((D : ℝ) - 1)

/-- `ν_φ(τ, τ') = P_φ^{⊗m}(τ) R_φ^{⊗m}(τ')`, §A.1, p.46 (PDF p.48). -/
noncomputable def nuPhi {m : ℕ} (p : ℝ) (φ : (Fin q → ℝ) × (Fin q → ℝ)) (τ τ' : Fin m → Fin q) : ℝ :=
  tensorPow (openDist p φ.1) τ * tensorPow (openDist p φ.2) τ'

/-- A point of the random bipartite graph model of §6.2, p.27 (PDF p.29), and §7.1, p.30 (PDF p.32): each side
has `n` ordinary vertices (`Sum.inl`) and `m` ordered open vertices (`Sum.inr`); `D - 1` perfect matchings
between the two sides, and one more between the ordinary vertices of the two sides.

**Formalization Note.** A perfect matching is a permutation of the common index set, sending a left vertex to
its partner on the right. The model is uniform on this finite space, so "with positive probability" is the
existence of a point of it. -/
structure BaseMatchings (D n m : ℕ) where
  between : Fin (D - 1) → Equiv.Perm (Fin n ⊕ Fin m)
  ordinary : Equiv.Perm (Fin n)

variable {D n m : ℕ}

/-- The graph `Γ`, the union of the matchings, is **simple**: no two of the matchings share an edge. A point of
the model has all degrees as stated in §6.2: `D` for ordinary vertices, `D - 1` for open ones, counting
multiplicities, and so also without multiplicities when `Γ` is simple. -/
def BaseMatchings.IsSimple (M : BaseMatchings D n m) : Prop :=
  (∀ j j' x, M.between j x = M.between j' x → j = j') ∧
    ∀ j i, M.between j (Sum.inl i) ≠ Sum.inl (M.ordinary i)

/-- `(σL, σR)` is a proper `q`-coloring of `Γ`. -/
def BaseMatchings.IsProper (M : BaseMatchings D n m) (σL σR : Fin n ⊕ Fin m → Fin q) : Prop :=
  (∀ j x, σL x ≠ σR (M.between j x)) ∧ ∀ i, σL (Sum.inl i) ≠ σR (Sum.inl (M.ordinary i))

/-- The proper `q`-colorings of `Γ`. -/
abbrev BaseColoring (q : ℕ) (M : BaseMatchings D n m) : Type :=
  {σ : (Fin n ⊕ Fin m → Fin q) × (Fin n ⊕ Fin m → Fin q) // M.IsProper σ.1 σ.2}

/-- `σ⁺ = τ` and `σ⁻ = τ'`: the left and right open vertices receive the colors `τ`, `τ'`. -/
def BaseColoring.OpenAre {M : BaseMatchings D n m} (σ : BaseColoring q M) (τ τ' : Fin m → Fin q) : Prop :=
  (∀ j, σ.1.1 (Sum.inr j) = τ j) ∧ ∀ j, σ.1.2 (Sum.inr j) = τ' j

/-- `μ_Γ(τ, τ')`, §6.2, p.28 (PDF p.30): the probability that the left and right open vertices receive the
colors `τ`, `τ'` under a uniformly random proper coloring of `Γ`. -/
noncomputable def muGamma (M : BaseMatchings D n m) (τ τ' : Fin m → Fin q) : ℝ :=
  (Nat.card {σ : BaseColoring q M // σ.OpenAre τ τ'} : ℝ) / (Nat.card (BaseColoring q M) : ℝ)

/-- `ξ_m(τ, τ')`, (29), p.27 (PDF p.29), for the phase families `P_S`, `R_S`. -/
noncomputable def xiM {k m : ℕ} (Pf Rf : Omega k → Fin (2 * k + 1) → ℝ)
    (τ τ' : Fin m → Fin (2 * k + 1)) : ℝ :=
  (1 / (2 * (Fintype.card (Omega k) : ℝ))) *
    ∑ S : Omega k, (tensorPow (Pf S) τ * tensorPow (Rf S) τ' + tensorPow (Rf S) τ * tensorPow (Pf S) τ')

/-- `(P, R)` is the phase of Lemma 28, p.31 (PDF p.33), attached to `S`, for the exponent `p`: a phase in which
both vectors are positive and constant on `S` and on `Sᶜ`, with `P_i > P_j` and `R_i < R_j` whenever `i ∈ S`,
`j ∈ Sᶜ`. -/
def IsOrientedPhase {k : ℕ} (p : ℝ) (S : Omega k) (P R : Fin (2 * k + 1) → ℝ) : Prop :=
  IsPhase p P R ∧ (∀ i, 0 < P i) ∧ (∀ i, 0 < R i) ∧
    ConstOn S.1 P ∧ ConstOn S.1ᶜ P ∧ ConstOn S.1 R ∧ ConstOn S.1ᶜ R ∧
    ∀ i ∈ S.1, ∀ j ∈ S.1ᶜ, P j < P i ∧ R i < R j

/-- `Pf S`, `Rf S` are the unique oriented phases of every `S` (first clause of Lemma 28, p.31 (PDF p.33)). -/
def IsPhaseFamily {k : ℕ} (p : ℝ) (Pf Rf : Omega k → Fin (2 * k + 1) → ℝ) : Prop :=
  ∀ (S : Omega k) (P R : Fin (2 * k + 1) → ℝ), IsOrientedPhase p S P R ↔ P = Pf S ∧ R = Rf S

end BipColorHard


