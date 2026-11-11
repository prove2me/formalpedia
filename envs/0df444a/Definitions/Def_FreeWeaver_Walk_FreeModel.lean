-- Prove2me | Definitions.Def_FreeWeaver_Walk_FreeModel
-- name    : FreeWeaver_Walk_FreeModel
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T23:33:57.868197+00:00
-- url     : https://prove2.me/theorems/6cc2556c-5990-49ee-9014-4fd912b98f07
-- title:
--   Definitions 4.1, 4.5, (4.4), §4.4, §6–§7, Definition D.2 — profiles, the free model of a state, the potential, q/p/r, the semicircular mass, (7.1), second variation, balanced moments and responses
-- statement:
--   Definition 4.1: the cusp profile $c^\circ(t)=u(2-t^2-|t|)$ and the smooth profile $c_\zeta(t)=u(1-t^2+\sqrt{1+\zeta^2}-\sqrt{t^2+\zeta^2})$, $0<\zeta\le1$; `IsProfile u c` says $c$ is one of them. With $D=2m$ (coordinates `Fin 2 × Fin m`), $J=\operatorname{diag}(I_m,-I_m)$, $B_i=I_2\otimes A_i$, $\check H(x)=J\sum_ix_iB_i$, Pauli matrices $\sigma_0=I_2,\sigma_1,\sigma_2,\sigma_3$, the **free model** (4.4) of a state $x$ for the variance function $c$ is the pencil
--   $$\mathcal Y(x)=\check H(x)\otimes I+\sum_{(i,\alpha)}K_{(i,\alpha)}\otimes s_{(i,\alpha)},\qquad K_{(i,\alpha)}=\sqrt{c(x_i)/2}\,(\sigma_\alpha\otimes A_i),$$
--   over a family indexed by `Fin n × Fin 4`. `edge` is $\lambda_+(\mathcal Y(x))$, `resM` its resolvent moments $G_j(x,z)$, `potential` $\mathcal F(x,z)=D^{-1}\operatorname{Tr}G_2(x,z)$ (Definition 4.5), `budget u ε` $=B=1/(u\varepsilon)$, `zStart u ε` $=z_0=5\sqrt{u\varepsilon}$. A coordinate is live if $|x_i|<1$; `numLive` is $k$. $q_i=\operatorname{Tr}(B_iG)$, $p_i=\operatorname{Tr}(B_iG_2)$, $r_i=\operatorname{Tr}(B_iG_3)$; the semicircular mass is $\mathfrak m=\sum_{i\text{ live}}c_iq_i^2$. `secondVar` is $\mathcal F''[h,h]=\frac{d^2}{dt^2}\mathcal F(x+th,z)|_{t=0}$. `Assumption71 … u L` is (7.1): for every live $i$, $c''(x_i)\le-2u$, $|c'(x_i)|q_i\le1$, $c_iq_i^2\le L/u$. Section 6: $P=G^{-1/2}G_2G^{-1/2}$, $Q=G^{-1/2}G_3G^{-1/2}$, $\Phi(M)=\sum_ic_i\operatorname{Tr}(B_iG^{1/2}MG^{1/2})G^{1/2}B_iG^{1/2}$, $\Lambda=I-\Phi$, $\Psi_1(M)=\sum_ic'(x_i)h_i\operatorname{Tr}(B_iG^{1/2}MG^{1/2})G^{1/2}B_iG^{1/2}$, and the responses $\mathcal G_t$, $\mathcal G_{st}$, the partial derivatives at $(0,0)$ of $\mathcal G(t,s)=G^{-1/2}G_1(x+th,z-s)G^{-1/2}$. `hsInner` is $\langle M,N\rangle=\operatorname{Tr}(M^*N)$. `dirOf` is the direction of $y$ (Definition D.2): $h_i=\sqrt{c_iq_i/(ur_i)}\,y_i$ for live $i$, $0$ otherwise.
--
--   **Formalization Note** $c'$, $c''$ are `deriv`; derivatives of matrix-valued maps are taken entrywise; $G^{\pm1/2}$ is the continuous functional calculus; traces the paper treats as real are real parts.
-- source:
--   Kathuria, A Walk From Free Probability to Matrix Discrepancy II, arXiv:2609.18913 (version dated November 3, 2026; sha256 c06bf728…), pp. 24–30, Definitions 4.1, 4.5, (4.4), §4.4, §6, §7 (7.1), Appendix D Definition D.2 (p. 53)

import Mathlib
import Definitions.Def_FreeWeaver_Walk_Pencil
import Definitions.Def_FreeWeaver_Walk_Weaver

namespace FreeWeaver.Walk

open scoped Kronecker ComplexOrder

noncomputable section

/-!
# The state, its free model and the potential

Kathuria, *A Walk From Free Probability to Matrix Discrepancy II*, arXiv:2609.18913 (version dated
November 3, 2026; sha256 c06bf728…), §4 (pp. 24–27: Definition 4.1, (4.4), Definition 4.5, §4.3,
§4.4), §6 (p. 29–30: the setting, `P`, `Q`, `Φ`, `Λ`, `Ψ₁`, the responses), §7 (p. 32: assumption
(7.1) and the semicircular mass), Appendix D, Definition D.2 (the direction of `y`).

**Formalization Note** `ℂ^D` with `D = 2m` is indexed by `Fin 2 × Fin m`, so a `D × D` matrix is a
`2 × 2` block matrix with `m × m` blocks and `I_2 ⊗ A` is `1 ⊗ₖ A`. The free semicircular family of
(4.4) is indexed by `Fin n × Fin 4` (`J = [n] × {0,1,2,3}`). The free model is defined for any
variance function `c : ℝ → ℝ` (`c_i = c(x_i)`); the profiles of Definition 4.1 are particular `c`.
Traces of products of Hermitian matrices that the paper treats as real numbers (`q_i`, `p_i`, `r_i`,
`Tr G_2`) are taken as real parts. `c'`, `c''` are `deriv c`, `deriv (deriv c)`, used only where the
paper assumes `c` differentiable. `ℱ''[h, h]` is the second derivative of `t ↦ ℱ(x + t h, z)` at `0`;
the responses `𝒢_t`, `𝒢_st` are the partial derivatives at `(0, 0)` of
`𝒢(t, s) = G^{-1/2} G_1(x + t h, z − s) G^{-1/2}`, taken entrywise. `G^{±1/2}` is the continuous
functional calculus of the Hermitian matrix `G`.
-/

/-- The cusp profile `c°(t) = u(2 − t² − |t|)` (Definition 4.1). -/
def cuspProfile (u t : ℝ) : ℝ := u * (2 - t ^ 2 - |t|)

/-- The smooth profile `c_ζ(t) = u(1 − t² + √(1 + ζ²) − √(t² + ζ²))` (Definition 4.1). -/
def smoothProfile (u ζ t : ℝ) : ℝ :=
  u * (1 - t ^ 2 + Real.sqrt (1 + ζ ^ 2) - Real.sqrt (t ^ 2 + ζ ^ 2))

/-- `c` is one of the two profiles of Definition 4.1 at scale `u`: the cusp profile, or the smooth
profile for some `0 < ζ ≤ 1`. -/
def IsProfile (u : ℝ) (c : ℝ → ℝ) : Prop :=
  c = cuspProfile u ∨ ∃ ζ : ℝ, 0 < ζ ∧ ζ ≤ 1 ∧ c = smoothProfile u ζ

/-- `σ_0 = I_2` and the Pauli matrices `σ_1, σ_2, σ_3`. -/
def pauli : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => 1
  | 1 => !![0, 1; 1, 0]
  | 2 => !![0, -Complex.I; Complex.I, 0]
  | 3 => !![1, 0; 0, -1]

/-- `J = diag(I_m, −I_m)`. -/
def Jmat (m : ℕ) : Matrix (Fin 2 × Fin m) (Fin 2 × Fin m) ℂ :=
  !![(1 : ℂ), 0; 0, -1] ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)

/-- `B_i = I_2 ⊗ A_i = diag(A_i, A_i)`. -/
def Bmat {m : ℕ} (v : Fin m → ℂ) : Matrix (Fin 2 × Fin m) (Fin 2 × Fin m) ℂ :=
  (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ rankOne v

/-- `Ȟ(x) = J Σ_i x_i B_i = diag(H(x), −H(x))`. -/
def Hcheck {n m : ℕ} (v : Fin n → Fin m → ℂ) (x : Fin n → ℝ) :
    Matrix (Fin 2 × Fin m) (Fin 2 × Fin m) ℂ :=
  Jmat m * ∑ i, ((x i : ℝ) : ℂ) • Bmat (v i)

/-- The free model (4.4) of the state `x` with the variance function `c`:
`Y(x) = Ȟ(x) ⊗ I + Σ_{(i,α)} K_(i,α) ⊗ s_(i,α)`, `K_(i,α) = √(c(x_i)/2) (σ_α ⊗ A_i)`. -/
def freeModel {n m : ℕ} (c : ℝ → ℝ) (v : Fin n → Fin m → ℂ) (x : Fin n → ℝ) :
    Pencil (Fin 2 × Fin m) (Fin n × Fin 4) where
  V := Hcheck v x
  K := fun γ => ((Real.sqrt (c (x γ.1) / 2) : ℝ) : ℂ) • (pauli γ.2 ⊗ₖ rankOne (v γ.1))

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {n m : ℕ}

/-- The resolvent moment `G_j(x, z)` of the free model. -/
def resM (c : ℝ → ℝ) (v : Fin n → Fin m → ℂ) (s : Fin n × Fin 4 → H →L[ℂ] H) (ω : H)
    (x : Fin n → ℝ) (z : ℝ) (j : ℕ) : Matrix (Fin 2 × Fin m) (Fin 2 × Fin m) ℂ :=
  (freeModel c v x).resMoment s ω z j

/-- The upper edge `λ₊(Y(x))` of the free model. -/
def edge (c : ℝ → ℝ) (v : Fin n → Fin m → ℂ) (s : Fin n × Fin 4 → H →L[ℂ] H)
    (x : Fin n → ℝ) : ℝ :=
  upperEdge ((freeModel c v x).op s)

/-- The potential `ℱ(x, z) = D⁻¹ Tr G_2(x, z)`, `D = 2m` (Definition 4.5). -/
def potential (c : ℝ → ℝ) (v : Fin n → Fin m → ℂ) (s : Fin n × Fin 4 → H →L[ℂ] H) (ω : H)
    (x : Fin n → ℝ) (z : ℝ) : ℝ :=
  (1 / (2 * (m : ℝ))) * (resM c v s ω x z 2).trace.re

/-- The budget `B = 1/(uε)` (§4.3). -/
def budget (u ε : ℝ) : ℝ := 1 / (u * ε)

/-- The starting threshold `z_0 = 5√(uε)` (§4.3). -/
def zStart (u ε : ℝ) : ℝ := 5 * Real.sqrt (u * ε)

/-- Coordinate `i` is live if `|x_i| < 1`, frozen otherwise (§5.1). -/
def IsLive (x : Fin n → ℝ) (i : Fin n) : Prop := |x i| < 1

/-- The number `k = |I|` of live coordinates. -/
def numLive (x : Fin n → ℝ) : ℕ := (Finset.univ.filter fun i => |x i| < 1).card

/-- `q_i = Tr(B_i G)` (§4.4). -/
def qCoef (c : ℝ → ℝ) (v : Fin n → Fin m → ℂ) (s : Fin n × Fin 4 → H →L[ℂ] H) (ω : H)
    (x : Fin n → ℝ) (z : ℝ) (i : Fin n) : ℝ :=
  (Bmat (v i) * resM c v s ω x z 1).trace.re

/-- `p_i = Tr(B_i G_2)` (§4.4). -/
def pCoef (c : ℝ → ℝ) (v : Fin n → Fin m → ℂ) (s : Fin n × Fin 4 → H →L[ℂ] H) (ω : H)
    (x : Fin n → ℝ) (z : ℝ) (i : Fin n) : ℝ :=
  (Bmat (v i) * resM c v s ω x z 2).trace.re

/-- `r_i = Tr(B_i G_3)` (§4.4). -/
def rCoef (c : ℝ → ℝ) (v : Fin n → Fin m → ℂ) (s : Fin n × Fin 4 → H →L[ℂ] H) (ω : H)
    (x : Fin n → ℝ) (z : ℝ) (i : Fin n) : ℝ :=
  (Bmat (v i) * resM c v s ω x z 3).trace.re

/-- The semicircular mass `𝔪 = Σ_{i live} c_i q_i²` (§7). -/
def mass (c : ℝ → ℝ) (v : Fin n → Fin m → ℂ) (s : Fin n × Fin 4 → H →L[ℂ] H) (ω : H)
    (x : Fin n → ℝ) (z : ℝ) : ℝ :=
  ∑ i, if |x i| < 1 then c (x i) * qCoef c v s ω x z i ^ 2 else 0

/-- The second variation `ℱ''[h, h] = d²/dt² ℱ(x + t h, z)|_{t=0}` (Proposition 6.2). -/
def secondVar (c : ℝ → ℝ) (v : Fin n → Fin m → ℂ) (s : Fin n × Fin 4 → H →L[ℂ] H) (ω : H)
    (x : Fin n → ℝ) (z : ℝ) (h : Fin n → ℝ) : ℝ :=
  deriv (deriv fun t : ℝ => potential c v s ω (x + t • h) z) 0

/-- Assumption (7.1) at `(x, z)` with constant `L` and scale `u`: for every live `i`,
`c''(x_i) ≤ −2u`, `|c'(x_i)| q_i ≤ 1` and `c_i q_i² ≤ L/u`. -/
def Assumption71 (c : ℝ → ℝ) (v : Fin n → Fin m → ℂ) (s : Fin n × Fin 4 → H →L[ℂ] H) (ω : H)
    (x : Fin n → ℝ) (z u L : ℝ) : Prop :=
  ∀ i, |x i| < 1 →
    deriv (deriv c) (x i) ≤ -2 * u ∧ |deriv c (x i)| * qCoef c v s ω x z i ≤ 1 ∧
      c (x i) * qCoef c v s ω x z i ^ 2 ≤ L / u

/-- `G^{1/2}` for the matrix resolvent `G = G_1(x, z)`. -/
def Ghalf (c : ℝ → ℝ) (v : Fin n → Fin m → ℂ) (s : Fin n × Fin 4 → H →L[ℂ] H) (ω : H)
    (x : Fin n → ℝ) (z : ℝ) : Matrix (Fin 2 × Fin m) (Fin 2 × Fin m) ℂ :=
  cfc Real.sqrt (resM c v s ω x z 1)

/-- `G^{-1/2}` for the matrix resolvent `G = G_1(x, z)`. -/
def Gmhalf (c : ℝ → ℝ) (v : Fin n → Fin m → ℂ) (s : Fin n × Fin 4 → H →L[ℂ] H) (ω : H)
    (x : Fin n → ℝ) (z : ℝ) : Matrix (Fin 2 × Fin m) (Fin 2 × Fin m) ℂ :=
  cfc (fun t : ℝ => (Real.sqrt t)⁻¹) (resM c v s ω x z 1)

/-- The balanced moment `P = G^{-1/2} G_2 G^{-1/2}` (§2.5). -/
def balP (c : ℝ → ℝ) (v : Fin n → Fin m → ℂ) (s : Fin n × Fin 4 → H →L[ℂ] H) (ω : H)
    (x : Fin n → ℝ) (z : ℝ) : Matrix (Fin 2 × Fin m) (Fin 2 × Fin m) ℂ :=
  Gmhalf c v s ω x z * resM c v s ω x z 2 * Gmhalf c v s ω x z

/-- The balanced moment `Q = G^{-1/2} G_3 G^{-1/2}` (§2.5). -/
def balQ (c : ℝ → ℝ) (v : Fin n → Fin m → ℂ) (s : Fin n × Fin 4 → H →L[ℂ] H) (ω : H)
    (x : Fin n → ℝ) (z : ℝ) : Matrix (Fin 2 × Fin m) (Fin 2 × Fin m) ℂ :=
  Gmhalf c v s ω x z * resM c v s ω x z 3 * Gmhalf c v s ω x z

/-- `Φ(M) = Σ_i c_i Tr(B_i G^{1/2} M G^{1/2}) G^{1/2} B_i G^{1/2}` (§6, p. 29). -/
def PhiMap (c : ℝ → ℝ) (v : Fin n → Fin m → ℂ) (s : Fin n × Fin 4 → H →L[ℂ] H) (ω : H)
    (x : Fin n → ℝ) (z : ℝ) (M : Matrix (Fin 2 × Fin m) (Fin 2 × Fin m) ℂ) :
    Matrix (Fin 2 × Fin m) (Fin 2 × Fin m) ℂ :=
  ∑ i, (((c (x i) : ℝ) : ℂ) *
      (Bmat (v i) * Ghalf c v s ω x z * M * Ghalf c v s ω x z).trace) •
    (Ghalf c v s ω x z * Bmat (v i) * Ghalf c v s ω x z)

/-- `Λ = I − Φ` (§2.5). -/
def LamMap (c : ℝ → ℝ) (v : Fin n → Fin m → ℂ) (s : Fin n × Fin 4 → H →L[ℂ] H) (ω : H)
    (x : Fin n → ℝ) (z : ℝ) (M : Matrix (Fin 2 × Fin m) (Fin 2 × Fin m) ℂ) :
    Matrix (Fin 2 × Fin m) (Fin 2 × Fin m) ℂ :=
  M - PhiMap c v s ω x z M

/-- `Ψ₁(M) = Σ_i c'(x_i) h_i Tr(B_i G^{1/2} M G^{1/2}) G^{1/2} B_i G^{1/2}` (§6, p. 29). -/
def Psi1Map (c : ℝ → ℝ) (v : Fin n → Fin m → ℂ) (s : Fin n × Fin 4 → H →L[ℂ] H) (ω : H)
    (x : Fin n → ℝ) (z : ℝ) (h : Fin n → ℝ) (M : Matrix (Fin 2 × Fin m) (Fin 2 × Fin m) ℂ) :
    Matrix (Fin 2 × Fin m) (Fin 2 × Fin m) ℂ :=
  ∑ i, (((deriv c (x i) * h i : ℝ) : ℂ) *
      (Bmat (v i) * Ghalf c v s ω x z * M * Ghalf c v s ω x z).trace) •
    (Ghalf c v s ω x z * Bmat (v i) * Ghalf c v s ω x z)

/-- The path `G(t, s) = G_1(x + t h, z − s)` of §6.1. -/
def Gpath (c : ℝ → ℝ) (v : Fin n → Fin m → ℂ) (s : Fin n × Fin 4 → H →L[ℂ] H) (ω : H)
    (x : Fin n → ℝ) (z : ℝ) (h : Fin n → ℝ) (t σ : ℝ) :
    Matrix (Fin 2 × Fin m) (Fin 2 × Fin m) ℂ :=
  resM c v s ω (x + t • h) (z - σ) 1

/-- The first response `𝒢_t = ∂_t 𝒢(0, 0)`, `𝒢(t, s) = G^{-1/2} G(t, s) G^{-1/2}` (§6.1). -/
def respT (c : ℝ → ℝ) (v : Fin n → Fin m → ℂ) (s : Fin n × Fin 4 → H →L[ℂ] H) (ω : H)
    (x : Fin n → ℝ) (z : ℝ) (h : Fin n → ℝ) : Matrix (Fin 2 × Fin m) (Fin 2 × Fin m) ℂ :=
  Gmhalf c v s ω x z *
    Matrix.of (fun k l => deriv (fun t : ℝ => Gpath c v s ω x z h t 0 k l) 0) *
    Gmhalf c v s ω x z

/-- The second response `𝒢_st = ∂_s ∂_t 𝒢(0, 0)` (§6.1). -/
def respST (c : ℝ → ℝ) (v : Fin n → Fin m → ℂ) (s : Fin n × Fin 4 → H →L[ℂ] H) (ω : H)
    (x : Fin n → ℝ) (z : ℝ) (h : Fin n → ℝ) : Matrix (Fin 2 × Fin m) (Fin 2 × Fin m) ℂ :=
  Gmhalf c v s ω x z *
    Matrix.of (fun k l =>
      deriv (fun σ : ℝ => deriv (fun t : ℝ => Gpath c v s ω x z h t σ k l) 0) 0) *
    Gmhalf c v s ω x z

/-- The Hilbert–Schmidt inner product `⟨M, N⟩ = Tr(M* N)` (§1.4). -/
def hsInner {ι : Type*} [Fintype ι] (M N : Matrix ι ι ℂ) : ℂ := (M.conjTranspose * N).trace

/-- The direction of `y ∈ ℝ^k` (Definition D.2): `h_i = √(c_i q_i / (u r_i)) y_i` for live `i` and
`h_i = 0` otherwise (`y` is a vector of `ℝ^n` supported on the live coordinates). -/
def dirOf (c : ℝ → ℝ) (v : Fin n → Fin m → ℂ) (s : Fin n × Fin 4 → H →L[ℂ] H) (ω : H)
    (x : Fin n → ℝ) (z u : ℝ) (y : Fin n → ℝ) : Fin n → ℝ :=
  fun i => if |x i| < 1 then
      Real.sqrt (c (x i) * qCoef c v s ω x z i / (u * rCoef c v s ω x z i)) * y i
    else 0

end

end FreeWeaver.Walk


