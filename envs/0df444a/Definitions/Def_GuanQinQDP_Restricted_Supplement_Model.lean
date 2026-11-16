-- Prove2me | Definitions.Def_GuanQinQDP_Restricted_Supplement_Model
-- name    : GuanQinQDP_Restricted_Supplement_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T12:35:55.990583+00:00
-- url     : https://prove2.me/theorems/5276e7c7-46b2-4d7d-9ab4-344e1d750963
-- title:
--   Pure-privacy factors, the cost $g(r)$, measure-and-prepare maps, Bloch matrices and the transport norms $\|\cdot\|_{\mathrm{LO}}$, $\|\cdot\|_{W_1}$
-- statement:
--   This file fixes the objects of §§5–6 of the paper that the published base model does not yet contain. Qubits are $\mathbb C^2$, density operators, effects, channels, the neighbor relation $\rho\sim_i\sigma$, the regrouping $H\cong H_i\otimes H_{\bar\imath}$, the partial trace $\operatorname{Tr}_i$ over register $i$, the standalone profile $\Delta^{\mathrm{ALL}}_E$ and the tensor channel $\bigotimes_j A_j$ are those of the base mission.
--
--   1. **Sandwich cost** (§5.2). For $r\ge1$,
--   $$g(r)=\max\Big\{1,\frac{2r-1}{3}\Big\}.$$
--   2. **Pure-privacy factor** (§2.4). For a qubit channel $E$, $r(E)=e^{\varepsilon^*(E)}$ is the smallest $\gamma\ge1$ with $\Delta^{\mathrm{ALL}}_E(\gamma)=0$. One writes $r(E)<\infty$ when such a $\gamma$ exists.
--   3. **Composition cost** (§5.3). For qubit maps $A_1,\dots,A_n$ and a register $i$, $G_i=\prod_{j\ne i}g(r_j)$ with $r_j=r(A_j)$; the empty product is $1$.
--   4. **Completely positive order** (§5.2). For linear maps $S,T:M_2\to M_2$, $S\preceq_{\mathrm{CP}}T$ when $T-S$ is completely positive.
--   5. **Measure-and-prepare maps** (Lemma 5.3). $T:M_2\to M_2$ is measure-and-prepare if $T(N)=\sum_{x\in X}\operatorname{Tr}(\tau_xN)F_x$ for a finite set $X$, density matrices $\tau_x$ and positive semidefinite $F_x$.
--   6. **Spectral ratio bound** (Lemma 5.3). $\lambda_{\max}(\Lambda(N))\le r\,\lambda_{\min}(\Lambda(N))$ for every $N\succeq0$.
--   7. **Bloch matrix** (§6.2). For a qubit map $E$, the real $3\times3$ matrix $\Theta$ with $E(\sigma_b)=\sum_a\Theta_{ab}\sigma_a$, that is $\Theta_{ab}=\tfrac12\operatorname{Tr}[\sigma_aE(\sigma_b)]$, where $\sigma_x,\sigma_y,\sigma_z$ are the Pauli matrices. The translation $t$ in $E(I)=I+t\cdot\sigma$ is not part of $\Theta$. $\|\Theta\|$ is its largest singular value.
--   8. **Dual seminorms** (§6.1). For a Hermitian $H$ on $n$ qubit registers,
--   $$\kappa_i(H)=\sup_{\rho\sim_i\sigma}\operatorname{Tr}[H(\rho-\sigma)],\qquad \lambda_i(H)=\sup_{\operatorname{Tr}_i\rho=\operatorname{Tr}_i\sigma}\operatorname{Tr}[H(\rho-\sigma)],$$
--   both over pairs of density operators.
--   9. **Transport norms** (§6.1). With $C_{\mathrm{LO}}=\bigcup_i\{\rho-\sigma:\rho\sim_i\sigma\}$ and $C_{\mathrm{EM}}=\bigcup_i\{\rho-\sigma:\operatorname{Tr}_i\rho=\operatorname{Tr}_i\sigma\}$, for a traceless Hermitian $X$, $\|X\|_{\mathrm{LO}}$ and $\|X\|_{W_1}$ are the smallest $c\ge0$ with $X\in c\cdot\operatorname{conv}(C_{\mathrm{LO}})$, respectively $X\in c\cdot\operatorname{conv}(C_{\mathrm{EM}})$. The second is the quantum Wasserstein distance of order one of De Palma, Marvian, Trevisan and Lloyd.
--
--   These objects state the measure-and-prepare sandwich and the unrestricted composition bound of §5, and the exact contraction of the transport norms in §6.
--
--   **Formalization Note** Operators are complex matrices over finite index types; the Pauli matrices are the published `BaconThesis.ExchangeUniv.pauli` with indices $0,1,2$ for $x,y,z$. Traces of Hermitian products are taken by real part. $r(E)$ is an infimum over $\{\gamma\ge1:\Delta^{\mathrm{ALL}}_E(\gamma)=0\}$, so it is the source's value only when that set is nonempty; every statement using it assumes this. $\|\Theta\|$ is the operator norm of $\Theta$ on Euclidean $\mathbb R^3$. The eigenvalue bound quantifies over the proof that $\Lambda(N)$ is Hermitian, which holds for completely positive $\Lambda$. The norms are infima of $\{c\ge0: X\in c\cdot\operatorname{conv}(C)\}$; they are defined by this primal formula, not by the dual formula (34). $\kappa_i,\lambda_i$ are suprema of nonempty bounded real sets.
-- source:
--   Ji Guan, Yecheng Qin, Parallel Composition of Quantum Differential Privacy: The Role of Measurement Restrictions, STOC 2027 submission #1640 (October 2026), source.pdf SHA-256 da23c8347251683a16df4c61de3fa1604211cdbf34d757a7a45feb0efd54c694, §2.4 (printed p. 14 / PDF p. 15), §5.2 and Lemma 5.3 (printed p. 22 / PDF p. 23), §5.3 (printed p. 25 / PDF p. 26), §6.1 (printed p. 31 / PDF p. 32), §6.2 (printed p. 32 / PDF p. 33)

import Definitions.Def_GuanQinQDP_Restricted_Model
import Definitions.Def_QAlgorithms_Defs_MatrixMapPositivity
import Definitions.Def_BaconThesis_ExchangeUniv_pauli

/-!
# Pure-privacy factors, the sandwich cost `g`, measure-and-prepare maps, Bloch matrices and the
# two transport norms

Ji Guan, Yecheng Qin, *Parallel Composition of Quantum Differential Privacy: The Role of
Measurement Restrictions*, STOC 2027 submission #1640 (October 2026):
§2.4 (printed p. 14 / PDF p. 15), §5.2 (printed p. 22 / PDF p. 23), §5.3 (printed p. 25 /
PDF p. 26), §6.1 (printed p. 31 / PDF p. 32), §6.2 (printed p. 32 / PDF p. 33).

Everything here builds on the published base model `GuanQinQDP.Restricted` (qubits `Fin 2`,
density operators, effects, `standaloneProfile`, `NeighborAt`, `splitAt`, `traceLeft`) and on
the published Pauli matrices `BaconThesis.ExchangeUniv.pauli` (`0, 1, 2 = x, y, z`).
-/

namespace GuanQinQDP.Restricted.Supplement

open QAlgorithms QAlgorithms.Entanglement GuanQinQDP.Restricted
open scoped Matrix ComplexOrder Pointwise

/-- §5.2 (printed p. 22 / PDF p. 23): the cost of the measure-and-prepare replacement,
`g(r) = max{1, (2r − 1)/3}` for `r ≥ 1`. -/
noncomputable def gcost (r : ℝ) : ℝ := max 1 ((2 * r - 1) / 3)

/-- §2.4 (printed p. 14 / PDF p. 15): the pure-privacy factor `r(E) = e^{ε*(E)}`, the smallest
`γ ≥ 1` with `Δ^ALL_E(γ) = 0`. It is a genuine infimum only when some `γ` has zero standalone
profile (`r(E) < ∞`); every statement using it assumes this explicitly. -/
noncomputable def pureFactor (E : Matrix Qubit Qubit ℂ → Matrix Qubit Qubit ℂ) : ℝ :=
  sInf {γ : ℝ | 1 ≤ γ ∧ standaloneProfile E γ = 0}

/-- §5.3 (printed p. 25 / PDF p. 26): `G_i = ∏_{j ≠ i} g(r_j)` for qubit maps `A_1, …, A_n`
(the empty product is `1`). -/
noncomputable def compCost {n : ℕ} (A : Fin n → (Matrix Qubit Qubit ℂ →ₗ[ℂ] Matrix Qubit Qubit ℂ))
    (i : Fin n) : ℝ :=
  ∏ j ∈ Finset.univ.filter (fun j => j ≠ i), gcost (pureFactor ⇑(A j))

/-- §5.2 (printed p. 22 / PDF p. 23): the completely positive order, `S ⪯_CP T` iff `T − S` is
completely positive (at every finite amplification, the published `IsCompletelyPositive`). -/
def CPLe {I J : Type*} [Fintype I] [Fintype J] (S T : Matrix I I ℂ →ₗ[ℂ] Matrix J J ℂ) : Prop :=
  IsCompletelyPositive (T - S)

/-- Lemma 5.3 (printed p. 22 / PDF p. 23): `T : M₂ → M₂` is measure-and-prepare,
`T(N) = ∑_{x ∈ X} Tr(τ_x N) F_x` for a finite index set `X`, density matrices `τ_x` and positive
semidefinite `F_x`. -/
def IsMeasurePrepare (T : Matrix Qubit Qubit ℂ →ₗ[ℂ] Matrix Qubit Qubit ℂ) : Prop :=
  ∃ m : ℕ, ∃ τ F : Fin m → Matrix Qubit Qubit ℂ,
    (∀ x, IsDensityMatrix (τ x)) ∧ (∀ x, (F x).PosSemidef) ∧
      ∀ N : Matrix Qubit Qubit ℂ, T N = ∑ x, (τ x * N).trace • F x

/-- Lemma 5.3 (printed p. 22 / PDF p. 23), hypothesis: `λ_max(Λ(N)) ≤ r λ_min(Λ(N))` for every
`N ⪰ 0`, with `λ_max`, `λ_min` the largest and smallest eigenvalues of the Hermitian matrix
`Λ(N)` (for a completely positive `Λ`, `Λ(N)` is Hermitian for every `N ⪰ 0`). -/
def SpectralRatioLe (Λ : Matrix Qubit Qubit ℂ →ₗ[ℂ] Matrix Qubit Qubit ℂ) (r : ℝ) : Prop :=
  ∀ N : Matrix Qubit Qubit ℂ, N.PosSemidef → ∀ h : (Λ N).IsHermitian,
    (⨆ k, h.eigenvalues k) ≤ r * ⨅ k, h.eigenvalues k

/-- §6.2 (printed p. 32 / PDF p. 33): the Bloch matrix `Θ` of a qubit map `E`, the real `3 × 3`
matrix with `E(σ_b) = ∑_a Θ_{ab} σ_a`, i.e. `Θ_{ab} = ½ Tr[σ_a E(σ_b)]` (`σ_0, σ_1, σ_2 =
σ_x, σ_y, σ_z`). The translation `t` (`E(I) = I + t·σ`) is not part of `Θ`. -/
noncomputable def blochMatrix (E : Matrix Qubit Qubit ℂ → Matrix Qubit Qubit ℂ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun a b =>
    (1 / 2 : ℝ) * ((BaconThesis.ExchangeUniv.pauli a * E (BaconThesis.ExchangeUniv.pauli b)).trace).re

/-- §6.2 (printed p. 32 / PDF p. 33): `∥Θ∥`, the largest singular value of a real `3 × 3` matrix,
i.e. its operator norm from Euclidean `ℝ³` to Euclidean `ℝ³` (not the Frobenius norm). -/
noncomputable def specNorm (Θ : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin Θ)‖

/-- §6.1 (printed p. 31 / PDF p. 32): `κ_i(H) = sup_{ρ ∼ᵢ σ} Tr[H(ρ − σ)]`, over pairs of
density operators on `n` qubit registers neighboring at register `i` (Definition 2.1, the base
`NeighborAt`). The trace is taken by real part (real for Hermitian `H`). -/
noncomputable def kappa {n : ℕ} (i : Fin n) (H : Matrix (Fin n → Qubit) (Fin n → Qubit) ℂ) : ℝ :=
  sSup {x | ∃ ρ σ : Matrix (Fin n → Qubit) (Fin n → Qubit) ℂ,
    IsDensityMatrix ρ ∧ IsDensityMatrix σ ∧ NeighborAt i ρ σ ∧ x = (H * (ρ - σ)).trace.re}

/-- §6.1 (printed p. 31 / PDF p. 32): `λ_i(H) = sup_{Tr_i ρ = Tr_i σ} Tr[H(ρ − σ)]`, over pairs
of density operators on `n` qubit registers with equal marginals on the complement of register
`i`. -/
noncomputable def lambdaEM {n : ℕ} (i : Fin n) (H : Matrix (Fin n → Qubit) (Fin n → Qubit) ℂ) :
    ℝ :=
  sSup {x | ∃ ρ σ : Matrix (Fin n → Qubit) (Fin n → Qubit) ℂ,
    IsDensityMatrix ρ ∧ IsDensityMatrix σ ∧ traceLeft (splitAt i ρ) = traceLeft (splitAt i σ) ∧
      x = (H * (ρ - σ)).trace.re}

/-- §6.1 (printed p. 31 / PDF p. 32): `C_LO = ⋃_i {ρ − σ : ρ ∼ᵢ σ}`. -/
def movesLO (n : ℕ) : Set (Matrix (Fin n → Qubit) (Fin n → Qubit) ℂ) :=
  {X | ∃ i : Fin n, ∃ ρ σ : Matrix (Fin n → Qubit) (Fin n → Qubit) ℂ,
    IsDensityMatrix ρ ∧ IsDensityMatrix σ ∧ NeighborAt i ρ σ ∧ X = ρ - σ}

/-- §6.1 (printed p. 31 / PDF p. 32): `C_EM = ⋃_i {ρ − σ : Tr_i ρ = Tr_i σ}`. -/
def movesEM (n : ℕ) : Set (Matrix (Fin n → Qubit) (Fin n → Qubit) ℂ) :=
  {X | ∃ i : Fin n, ∃ ρ σ : Matrix (Fin n → Qubit) (Fin n → Qubit) ℂ,
    IsDensityMatrix ρ ∧ IsDensityMatrix σ ∧ traceLeft (splitAt i ρ) = traceLeft (splitAt i σ) ∧
      X = ρ - σ}

/-- The gauge of a set `C`: the smallest `c ≥ 0` with `X ∈ c · conv(C)` (convex hull over `ℝ`). -/
noncomputable def gaugeNorm {ι : Type*} (C : Set (Matrix ι ι ℂ)) (X : Matrix ι ι ℂ) : ℝ :=
  sInf {c : ℝ | 0 ≤ c ∧ X ∈ c • convexHull ℝ C}

/-- §6.1 (printed p. 31 / PDF p. 32): `∥X∥_LO`, the gauge of `conv(C_LO)` (the norm generated by
local channels, De Palma et al.'s Appendix A norm), for traceless Hermitian `X`. -/
noncomputable def normLO {n : ℕ} (X : Matrix (Fin n → Qubit) (Fin n → Qubit) ℂ) : ℝ :=
  gaugeNorm (movesLO n) X

/-- §6.1 (printed p. 31 / PDF p. 32): `∥X∥_W1`, the gauge of `conv(C_EM)` (the quantum
Wasserstein distance of order one of De Palma et al.), for traceless Hermitian `X`. -/
noncomputable def normW1 {n : ℕ} (X : Matrix (Fin n → Qubit) (Fin n → Qubit) ℂ) : ℝ :=
  gaugeNorm (movesEM n) X

/-! ### Sanity checks -/

/-- `g(r) = 1` for `r ≤ 2`. -/
example : gcost 2 = 1 := by norm_num [gcost]

/-- `g(5) = 3`. -/
example : gcost 5 = 3 := by norm_num [gcost]

end GuanQinQDP.Restricted.Supplement


