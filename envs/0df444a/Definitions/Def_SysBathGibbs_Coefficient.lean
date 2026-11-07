-- Prove2me | Definitions.Def_SysBathGibbs_Coefficient
-- name    : SysBathGibbs_Coefficient
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:36:10.846001+00:00
-- url     : https://prove2.me/theorems/dd53185b-4c35-4bd8-abc0-3ab05f9b7f51
-- title:
--   Coefficient-local maps $\mathcal A(S)$, spectral conditional expectations $p_I$ and the Pauli energy $\mathcal E_K$
-- statement:
--   The **weighted multiplication map** of (4.1) is $\mathcal B_{B,C}(O)=\Gamma^{-1/2}(B\,\Gamma^{1/2}(O)\,C)$. For $S\subseteq[n]$, $\mathcal A(S)$ is the set of finite sums of maps $\mathcal B_{B,C}$ with $B,C$ supported on $S$ (Definition 6.3). A family $(\mathcal A_x)_{x\in[n]}$ is **uniformly coefficient-quasi-local** with constants $C,c$ when
--   $$
--   \|\mathcal A_x\|_{\rho_\beta\to\rho_\beta}\le C,\qquad \inf_{\mathcal A_{x,r}\in\mathcal A(N_r(x))}\|\mathcal A_x-\mathcal A_{x,r}\|_{\rho_\beta\to\rho_\beta}\le Ce^{-cr}\quad(r\ge0).
--   $$
--   A map is KMS-self-adjoint ($\mathcal A^\star=\mathcal A$) when $\langle O,\mathcal A(P)\rangle_{\rho_\beta}=\langle\mathcal A(O),P\rangle_{\rho_\beta}$. The **spectral conditional expectation** $p_I$ (Definition 6.1) is the KMS-orthogonal projection onto the operators acting as the identity on $I$; it is characterized by $p_I(O)$ lying in that subspace and $O-p_I(O)$ being KMS-orthogonal to it. The **Pauli energy** is $\mathcal E_K(O)=\sum_{x,a}\|[P_{x,a},O]\|^2_{\rho_\beta}$. Finally, the hypothesis (6.17) of Corollary 6.8 on a family $(F_x)$ with constants $C,c$: each $F_x$ is Gibbs-centered, $\operatorname{Tr}(\rho_\beta F_x)=0$, and for $|u|\le\beta/4$, $\|F_x(-iu)\|_{\mathrm{op}}\le C$ and $\|(\mathrm{id}-\mathcal E_{x,r})F_x(-iu)\|_{\mathrm{op}}\le Ce^{-cr}$ for $r\ge0$.
--
--   **Formalization Note** $\mathcal A(S)$ is the additive closure of the maps $\mathcal B_{B,C}$; it is closed under complex scalars since $\lambda\mathcal B_{B,C}=\mathcal B_{\lambda B,C}$. $p_I$ is passed to the theorems as any map with the characterizing property, which determines it uniquely.
-- source:
--   Ding, Li, Zhang, Efficient thermalization of one-dimensional noncommuting Hamiltonians via system-bath interactions with Θ(n) ancilla qubits, arXiv:2611.03422 (held file sha256 a60a3c09826df3b5399a5589f83ef3a1d2ea768d74c5e39e8a3b29d1323f024f), (4.1), p.30; (2.17), p.12; Definitions 6.1 and 6.3 with (6.5), pp.46–47; (6.17), p.51

import Definitions.Def_SysBathGibbs_Generator

open Matrix

namespace SysBathGibbs

/-!
# Coefficient-local maps and spectral conditional expectations

Ding, Li, Zhang, arXiv:2611.03422 (held file sha256 a60a3c09…), (4.1), p.30; (2.17), p.12;
Definitions 6.1 and 6.3, (6.5), pp.46–47.
-/

variable {n q : ℕ}

/-- The weighted multiplication map `B_{B,C}(O) = Γ^{-1/2}(B Γ^{1/2}(O) C)`, (4.1). -/
noncomputable def weightedMul (β : ℝ) (H B C : SysMat n q) : SysMat n q → SysMat n q :=
  fun O => Gam β H (-1 / 2) (B * Gam β H (1 / 2) O * C)

/-- `A(S)`, Definition 6.3: the finite sums of maps `B_{B,C}` with `B, C` supported on `S`. -/
noncomputable def coefLocal (β : ℝ) (H : SysMat n q) (S : Set (Fin n)) :
    AddSubmonoid (SysMat n q → SysMat n q) :=
  AddSubmonoid.closure
    {T | ∃ B C : SysMat n q, SupportedOn S B ∧ SupportedOn S C ∧ T = weightedMul β H B C}

/-- `(A_x)` is uniformly coefficient-quasi-local with the constants `C, c`, (6.5):
`‖A_x‖ ≤ C` and `inf_{A_{x,r} ∈ A(N_r(x))} ‖A_x - A_{x,r}‖ ≤ C e^{-cr}` for `r ≥ 0`. -/
def IsCoefQuasiLocal (β : ℝ) (H : SysMat n q) (C c : ℝ) (A : Fin n → SysMat n q → SysMat n q) :
    Prop :=
  ∀ x, kmsOpNorm β H (A x) ≤ ENNReal.ofReal C ∧
    ∀ r : ℝ, 0 ≤ r →
      (⨅ B ∈ coefLocal β H (nbhd r {x}), kmsOpNorm β H (A x - B)) ≤
        ENNReal.ofReal (C * Real.exp (-c * r))

/-- `A⋆ = A`: self-adjointness of a map in the KMS inner product, (2.6). -/
def IsKmsSelfAdjoint (β : ℝ) (H : SysMat n q) (A : SysMat n q → SysMat n q) : Prop :=
  ∀ O P, kmsInner β H O (A P) = kmsInner β H (A O) P

/-- The spectral conditional expectation `p_I`, Definition 6.1: the KMS-orthogonal projection onto
the operators acting as the identity on `I`, that is, onto `{1_I ⊗ B}`. As a predicate on a map: `p`
sends every `O` into that subspace, and `O - p O` is KMS-orthogonal to the subspace. These two
properties determine `p`. Existence is the orthogonal projection in finite dimension. -/
def IsSpectralCE (β : ℝ) (H : SysMat n q) (I : Set (Fin n)) (p : SysMat n q → SysMat n q) : Prop :=
  ∀ O, SupportedOn Iᶜ (p O) ∧ ∀ B, SupportedOn Iᶜ B → kmsInner β H B (O - p O) = 0

/-- The Pauli energy `E_K(O) = ∑_{x,a} ‖[P_{x,a}, O]‖²_{ρ_β}`, (2.17). -/
noncomputable def pauliEnergy (β : ℝ) (H O : SysMat n q) : ℝ :=
  ∑ x : Fin n, ∑ a : Coupling q, kmsNorm β H (comm (pauliString x a.1) O) ^ 2

/-- The hypotheses of Corollary 6.8, (6.17), with constants `C, c`, on a family `(F_x)`: each `F_x` is
Gibbs-centered, `Tr(ρ_β F_x) = 0`, and for `|u| ≤ β/4` the imaginary-time evolution `F_x(-iu)` is
quasi-local at `x`. -/
def IsCenteredQuasiLocal (β : ℝ) (H : SysMat n q) (C c : ℝ) (F : Fin n → SysMat n q) : Prop :=
  ∀ x, Matrix.trace (gibbs β H * F x) = 0 ∧
    ∀ u : ℝ, |u| ≤ β / 4 →
      opNorm (evo H (-(Complex.I * u)) (F x)) ≤ C ∧
        ∀ r : ℝ, 0 ≤ r →
          opNorm (evo H (-(Complex.I * u)) (F x) -
            traceAt x r (evo H (-(Complex.I * u)) (F x))) ≤ C * Real.exp (-c * r)

end SysBathGibbs


