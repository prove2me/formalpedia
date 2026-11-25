-- Prove2me | Definitions.Def_Arxiv2205_09423_Basic
-- name    : Arxiv2205_09423_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-25T11:48:59.537744+00:00
-- url     : https://prove2.me/theorems/b2d04b91-48e0-4f88-bc89-b79bd21e7a53
-- title:
--   Random scattering matrices of particle slabs: modes, normalized blocks, ensemble, phases and cascades
-- statement:
--   Objects of Section 2 and Appendices A–D of Byrnes and Foreman (2022).
--
--   1. **Modes (Section 2.1).** A mode set consists of a wavenumber $k=2\pi/\lambda>0$ and $2N_k+1$ distinct transverse wavevectors $\boldsymbol\kappa_i=(k_{ix},k_{iy})$, $i=-N_k,\dots,N_k$, with $|\boldsymbol\kappa_i|<k$ and $\boldsymbol\kappa_{-i}=-\boldsymbol\kappa_i$ (so $\boldsymbol\kappa_0=\mathbf 0$), each with the cubature weight $w=\pi k^2/(2N_k+1)$. Write $k_{iz}=(k^2-k_{ix}^2-k_{iy}^2)^{1/2}>0$, $\mathbf k_i=(k_{ix},k_{iy},k_{iz})$, $\widetilde{\mathbf k}_i=(k_{ix},k_{iy},-k_{iz})$, $\mathbf u_i=\mathbf k_i/k$, $\widetilde{\mathbf u}_i=\widetilde{\mathbf k}_i/k$, and
--   $$C_{ji}=\frac{w}{2\pi k\sqrt{k_{jz}k_{iz}}},\qquad C_{ijuv}=\frac{wn\Delta L}{k^2\sqrt{k_{iz}k_{jz}k_{uz}k_{vz}}}.$$
--   $\delta^R_{ijuv}=1$ if $\boldsymbol\kappa_i-\boldsymbol\kappa_j=\boldsymbol\kappa_u-\boldsymbol\kappa_v$ and $0$ otherwise; $\delta^P_{ijuv}=1$ if $\boldsymbol\kappa_i-\boldsymbol\kappa_j=-(\boldsymbol\kappa_u-\boldsymbol\kappa_v)$ and $0$ otherwise.
--   2. **Polar basis (Eq. 11).** For a unit direction $\mathbf e_k$: $\mathbf e_\phi=\hat{\mathbf z}\times\mathbf e_k/|\hat{\mathbf z}\times\mathbf e_k|$ ($\mathbf e_\phi=\pm\hat{\mathbf y}$ if $\mathbf e_k=\pm\hat{\mathbf z}$) and $\mathbf e_\theta=\mathbf e_\phi\times\mathbf e_k/|\mathbf e_\phi\times\mathbf e_k|$. The reduction of a complex $3\times3$ matrix $X$ from direction $\mathbf u_{\rm in}$ to direction $\mathbf u_{\rm out}$ is the $2\times2$ matrix $[\mathbf e_m(\mathbf u_{\rm out})^{\mathrm T}X\,\mathbf e_n(\mathbf u_{\rm in})]_{m,n\in\{\theta,\phi\}}$.
--   3. **Slab (Eqs. 9–17).** A slab contains $N$ particles with centres $\mathbf r_p$ and far-field amplitude matrices $\mathbf A_p(\mathbf u_{\rm out},\mathbf u_{\rm in})$ (complex $3\times3$). Its discretized transmission and reflection matrices are $\mathbf t(\boldsymbol\kappa_j,\boldsymbol\kappa_i)=\frac{\delta_{ij}}{w}\mathbb I_3+\frac{1}{2\pi kk_{jz}}\sum_p\mathbf A_p(\mathbf u_j,\mathbf u_i)e^{i(\mathbf k_i-\mathbf k_j)\cdot\mathbf r_p}$ and $\mathbf r(\boldsymbol\kappa_j,\boldsymbol\kappa_i)=\frac{1}{2\pi kk_{jz}}\sum_p\mathbf A_p(\widetilde{\mathbf u}_j,\mathbf u_i)e^{i(\mathbf k_i-\widetilde{\mathbf k}_j)\cdot\mathbf r_p}$; $\mathbf t_{(j,i)}$, $\mathbf r_{(j,i)}$ are their reductions (Eqs. 12–13), and $\sqrt{k_{jz}/k_{iz}}\,\mathbf t_{(j,i)}w$, $\sqrt{k_{jz}/k_{iz}}\,\mathbf r_{(j,i)}w$ their normalizations. The normalized blocks are
--   $$\bar{\mathbf t}_{(j,i)}=\delta_{ij}\mathbb I_2+C_{ji}\sum_p\mathbf A^t_{p(j,i)}e^{i(\mathbf k_i-\mathbf k_j)\cdot\mathbf r_p},\qquad \bar{\mathbf r}_{(j,i)}=C_{ji}\sum_p\mathbf A^r_{p(j,i)}e^{i(\mathbf k_i-\widetilde{\mathbf k}_j)\cdot\mathbf r_p},$$
--   with $\mathbf A^t_{p(j,i)}$, $\mathbf A^r_{p(j,i)}$ the reductions of $\mathbf A_p(\mathbf u_j,\mathbf u_i)$ and $\mathbf A_p(\widetilde{\mathbf u}_j,\mathbf u_i)$. For incidence from the right, $\bar{\mathbf t}'_{(j,i)}=\delta_{ij}\mathbb I_2+C_{ji}\sum_p\mathbf A^{t'}_{p(j,i)}e^{i(\widetilde{\mathbf k}_i-\widetilde{\mathbf k}_j)\cdot\mathbf r_p}$ and $\bar{\mathbf r}'_{(j,i)}=C_{ji}\sum_p\mathbf A^{r'}_{p(j,i)}e^{i(\widetilde{\mathbf k}_i-\mathbf k_j)\cdot\mathbf r_p}$, with incident direction $\widetilde{\mathbf u}_i$ and outgoing directions $\widetilde{\mathbf u}_j$, $\mathbf u_j$. The blocks are assembled as in Eq. (16) (block row $j$, block column $i$) and $\bar{\mathbf S}=\begin{pmatrix}\bar{\mathbf r}&\bar{\mathbf t}'\\\bar{\mathbf t}&\bar{\mathbf r}'\end{pmatrix}$.
--   4. **Ensemble (Section 2.2).** On a probability space, the pairs $(\mathbf r_p,\mathbf A_p)$ are independent across particles, $\mathbf r_p$ is independent of $\mathbf A_p$, the $\mathbf A_p$ are identically distributed with square-integrable entries, the $z$ coordinate of $\mathbf r_p$ is uniform on $[-\Delta L/2,\Delta L/2]$ and independent of the transverse position $\boldsymbol\rho_p$, $\Delta L>0$, $n>0$, and for every $\mathbf q=\boldsymbol\kappa_i-\boldsymbol\kappa_j-\boldsymbol\kappa_u+\boldsymbol\kappa_v$
--   $$N\langle e^{i\mathbf q\cdot\boldsymbol\rho_p}\rangle=\frac{(2\pi)^2n\Delta L}{w}\,\delta_{\mathbf q,\mathbf 0}.$$
--   Covariance: $\operatorname{cov}(X,Y)=\langle XY^*\rangle-\langle X\rangle\langle Y\rangle^*$; pseudo-covariance: $\operatorname{pcov}(X,Y)=\langle XY\rangle-\langle X\rangle\langle Y\rangle$. $\operatorname{sinc}x=\sin x/x$, $\operatorname{sinc}0=1$.
--   5. **Position and cascades (Section 2.3, Appendices B, C).** Translating every particle by $L_0\hat{\mathbf z}$ moves the slab centre to $L_0$. $\Lambda_+^{L_0}=\mathrm{diag}(e^{ik_{mz}L_0})_{m=-N_k}^{N_k}\otimes\mathbb I_2$, $\Lambda_-^{L_0}=(\Lambda_+^{L_0})^*$, $\Lambda_\pm^{L_0}=\mathrm{diag}(\Lambda_+^{L_0},\Lambda_-^{L_0})$, $\Lambda_\mp^{L_0}=(\Lambda_\pm^{L_0})^*$. The transfer matrix of $\mathbf S=\begin{pmatrix}\mathbf r&\mathbf t'\\\mathbf t&\mathbf r'\end{pmatrix}$ is $\mathbf M=\begin{pmatrix}\mathbf t-\mathbf r'\mathbf t'^{-1}\mathbf r&\mathbf r'\mathbf t'^{-1}\\-\mathbf t'^{-1}\mathbf r&\mathbf t'^{-1}\end{pmatrix}$. $\mathbf J_n$ is the $n\times n$ exchange matrix, $\boldsymbol\sigma_z=\mathrm{diag}(1,-1)$, and $\bar{\mathbf S}$ is reciprocal if $\bar{\mathbf S}=\Pi\bar{\mathbf S}^{\mathrm T}\Pi$ with $\Pi=\mathrm{diag}(\mathbf J_{2N_k+1}\otimes\boldsymbol\sigma_z,\mathbf J_{2N_k+1}\otimes\boldsymbol\sigma_z)$. $\mathbf S$ is the cascade of $\mathbf S_1$ (left) and $\mathbf S_2$ (right) if for all incoming amplitudes $\mathbf a$ (left) and $\mathbf d$ (right) there are amplitudes $\mathbf b,\mathbf c$ between the slabs with $\mathbf b=\mathbf t_1\mathbf a+\mathbf r_1'\mathbf c$, $\mathbf c=\mathbf r_2\mathbf b+\mathbf t_2'\mathbf d$, and $\mathbf S(\mathbf a,\mathbf d)=(\mathbf r_1\mathbf a+\mathbf t_1'\mathbf c,\ \mathbf t_2\mathbf b+\mathbf r_2'\mathbf d)$.
--   6. **Scattering plane (Appendix D).** For incident and outgoing unit directions $\mathbf e_{ki},\mathbf e_{kj}$: $\mathbf e_\perp=\mathbf e_{ki}\times\mathbf e_{kj}/|\mathbf e_{ki}\times\mathbf e_{kj}|$, $\mathbf e_{\parallel i}=\mathbf e_\perp\times\mathbf e_{ki}$, $\mathbf e_{\parallel j}=\mathbf e_\perp\times\mathbf e_{kj}$; if $\mathbf e_{ki}\times\mathbf e_{kj}=\mathbf 0$, then $\mathbf e_{\parallel i}=\mathbf e_{\theta i}$, $\mathbf e_{\parallel j}=\mathbf e_{\theta j}$, $\mathbf e_\perp=\mathbf e_{\phi i}$. $\theta$ is the signed angle from $\mathbf e_\theta$ to $\mathbf e_\parallel$ about $\mathbf e_k$, $\mathbf R(\theta)=\begin{pmatrix}\cos\theta&\sin\theta\\-\sin\theta&\cos\theta\end{pmatrix}$, and $\begin{pmatrix}S_2&S_3\\S_4&S_1\end{pmatrix}$ is the matrix of $X$ between the frames $(\mathbf e_{\parallel i},\mathbf e'_\perp)$ and $(\mathbf e_{\parallel j},\mathbf e'_\perp)$ with $\mathbf e'_\perp=-\mathbf e_\perp$ (Bohren–Huffman convention).
--
--   **Formalization Note** Mode $i\in\{-N_k,\dots,N_k\}$ is indexed by $i+N_k\in\{0,\dots,2N_k\}$, so mode $-i$ is the reversed index and $\mathbf J_{2N_k+1}$ is the reversal. Polarization index $0$ is $\theta$, $1$ is $\phi$. The blocks $\bar{\mathbf t}'$, $\bar{\mathbf r}'$ are not printed in the paper ("analogous expressions"). They are written by analogy with Eqs. (14)–(15), using the phases implied by Table A1. The transfer-matrix convention is not written in the paper; Beenakker's convention, which the paper cites, is used. The reciprocity relation is taken from Byrnes and Foreman, Phys. Rev. Research 3, 013129 (2021), Eq. (98). The signed angle is the argument of $\langle\mathbf e_\theta,\mathbf e_\parallel\rangle+i\langle\mathbf e_\theta\times\mathbf e_\parallel,\mathbf e_k\rangle$, which also covers $\theta=\pi$, a value the paper's range $-\pi<\theta<\pi$ leaves out.
-- source:
--   Byrnes and Foreman, Random matrix theory of polarized light scattering in disordered media, arXiv:2205.09423v1 (2022), Section 2.1 (Eqs. (9)-(17)), Section 2.2 (Eqs. (18)-(27)), Section 2.3 (Eq. (28)), Appendices A-D (Table A1, Eqs. (B1)-(B2), (C1)-(C3), (D1)-(D2))

import Mathlib

/-!
N. Byrnes and M. R. Foreman, *Random matrix theory of polarized light scattering in disordered
media*, arXiv:2205.09423v1 (2022).

Definitions for Section 2 (Eqs. (9)–(17), (19), (22)–(28)) and Appendices A–D: the discrete mode
set, the polar basis of Eq. (11), the transmission and reflection matrices of a slab of particles in
the single-scattering approximation and their normalized `2 × 2` blocks, the block scattering matrix,
the ensemble assumptions of Section 2.2, covariances and pseudo-covariances, the propagation phase
matrices of Appendix C, the transfer matrix, reciprocity, the cascade of two slabs (Appendix B) and
the scattering-plane frames of Appendix D.

Mode `i : Fin (2 * Nk + 1)` stands for the paper's index `i - Nk ∈ {-Nk, …, Nk}`, so the paper's
mode `-i` is `Fin.rev i`. Polarization index `0` is `θ` and `1` is `φ`.
-/

open MeasureTheory ProbabilityTheory Matrix

noncomputable section

namespace Arxiv2205_09423

/-- Section 2.1, p. 5: the discrete mode set `K = {-κ_{N_k}, …, -κ_1, 0, κ_1, …, κ_{N_k}}` of
transverse wavevectors `κ_i = (kx i, ky i)`, the wavenumber `k = 2π/λ` and the common cubature
weight `w`. -/
structure ModeSet (Nk : ℕ) where
  /-- wavenumber `k = 2π/λ` -/
  k : ℝ
  /-- `x` components of the transverse wavevectors -/
  kx : Fin (2 * Nk + 1) → ℝ
  /-- `y` components of the transverse wavevectors -/
  ky : Fin (2 * Nk + 1) → ℝ
  /-- cubature weight of every mode -/
  w : ℝ

namespace ModeSet

variable {Nk : ℕ} (K : ModeSet Nk)

/-- Section 2.1, pp. 4–5: `k > 0`; every mode is a homogeneous plane wave, `|κ_i| < k`; modes come
in inverse pairs, `κ_{-i} = -κ_i` (so `κ_0 = 0`); the `2 N_k + 1` modes are distinct; and the equal
weights are `w = π k² / (2 N_k + 1)`. -/
def IsValid : Prop :=
  0 < K.k ∧ (∀ i, K.kx i ^ 2 + K.ky i ^ 2 < K.k ^ 2) ∧
    (∀ i, K.kx (Fin.rev i) = -K.kx i ∧ K.ky (Fin.rev i) = -K.ky i) ∧
    Function.Injective (fun i => (K.kx i, K.ky i)) ∧
    K.w = Real.pi * K.k ^ 2 / (2 * Nk + 1)

/-- Section 2.1, p. 4: `k_{iz} = (k² - k_{ix}² - k_{iy}²)^{1/2}`. -/
def kz (i : Fin (2 * Nk + 1)) : ℝ := Real.sqrt (K.k ^ 2 - K.kx i ^ 2 - K.ky i ^ 2)

/-- Section 2.1, p. 4: the right-propagating wavevector `k_i = (k_{ix}, k_{iy}, k_{iz})`. -/
def kvec (i : Fin (2 * Nk + 1)) : Fin 3 → ℝ := ![K.kx i, K.ky i, K.kz i]

/-- Section 2.1, p. 5: the left-propagating wavevector `k̃_i = (k_{ix}, k_{iy}, -k_{iz})`. -/
def kvecT (i : Fin (2 * Nk + 1)) : Fin 3 → ℝ := ![K.kx i, K.ky i, -K.kz i]

/-- Eq. (14), p. 6: `C_{ji} = w / (2π k √(k_{jz} k_{iz}))`. -/
def cji (j i : Fin (2 * Nk + 1)) : ℝ :=
  K.w / (2 * Real.pi * K.k * Real.sqrt (K.kz j * K.kz i))

/-- Eq. (25), p. 8: `C_{ijuv} = w n ΔL / (k² √(k_{iz} k_{jz} k_{uz} k_{vz}))`, for particle
density `n` and slab thickness `ΔL = dL`. -/
def cijuv (n dL : ℝ) (i j u v : Fin (2 * Nk + 1)) : ℝ :=
  K.w * n * dL / (K.k ^ 2 * Real.sqrt (K.kz i * K.kz j * K.kz u * K.kz v))

/-- Eqs. (24)–(25), p. 8: `δ^R = 1` when `k_{ix} - k_{jx} = k_{ux} - k_{vx}` and
`k_{iy} - k_{jy} = k_{uy} - k_{vy}` (the memory-effect condition), and `0` otherwise. -/
def deltaR (i j u v : Fin (2 * Nk + 1)) : ℝ :=
  if K.kx i - K.kx j = K.kx u - K.kx v ∧ K.ky i - K.ky j = K.ky u - K.ky v then 1 else 0

/-- Eqs. (27)–(28), p. 9: `δ^P = 1` when `k_{ix} - k_{jx} = -(k_{ux} - k_{vx})` and
`k_{iy} - k_{jy} = -(k_{uy} - k_{vy})`, and `0` otherwise. -/
def deltaP (i j u v : Fin (2 * Nk + 1)) : ℝ :=
  if K.kx i - K.kx j = -(K.kx u - K.kx v) ∧ K.ky i - K.ky j = -(K.ky u - K.ky v) then 1 else 0

end ModeSet

/-- Euclidean norm `|v|` of a vector of `ℝ³`. -/
def vnorm (v : Fin 3 → ℝ) : ℝ := Real.sqrt (dotProduct v v)

/-- The unit vector `v / |v|`. -/
def normalize (v : Fin 3 → ℝ) : Fin 3 → ℝ := (vnorm v)⁻¹ • v

/-- The unit vector `ẑ`. -/
def zhat : Fin 3 → ℝ := ![0, 0, 1]

/-- Eq. (11), p. 5: `e_φ = (ẑ × e_k)/|ẑ × e_k|` for the unit propagation direction `e_k`, with
`e_φ = ±ŷ` in the special cases `e_k = ±ẑ`. -/
def ePhi (e : Fin 3 → ℝ) : Fin 3 → ℝ :=
  if e 0 = 0 ∧ e 1 = 0 then (if 0 < e 2 then ![0, 1, 0] else ![0, -1, 0])
  else normalize (crossProduct zhat e)

/-- Eq. (11), p. 5: `e_θ = (e_φ × e_k)/|e_φ × e_k|`. -/
def eTheta (e : Fin 3 → ℝ) : Fin 3 → ℝ := normalize (crossProduct (ePhi e) e)

/-- Eq. (11): the polarization basis `(e_θ, e_φ)` attached to the unit direction `e`. -/
def polarBasis (e : Fin 3 → ℝ) : Fin 2 → Fin 3 → ℝ := ![eTheta e, ePhi e]

/-- Eq. (2), p. 4: the far-field amplitude of one particle, `A(u_out, u_in)`, a `3 × 3` complex
matrix (entries `a b`) for each observation direction `u_out` and incidence direction `u_in`. -/
abbrev Amp := (Fin 3 → ℝ) → (Fin 3 → ℝ) → Fin 3 → Fin 3 → ℂ

/-- Eqs. (12)–(13), p. 5: the reduced `2 × 2` matrix `[e_m(u_out)ᵀ X e_n(u_in)]_{m n}` of a
`3 × 3` matrix `X`, in the polar bases of the incident direction `u_in` and outgoing direction
`u_out`. -/
def reduce (X : Fin 3 → Fin 3 → ℂ) (uin uout : Fin 3 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun m n => ∑ a, ∑ b, (polarBasis uout m a : ℂ) * X a b * (polarBasis uin n b : ℂ)

section Slab

variable {Nk : ℕ} (K : ModeSet Nk) {N : ℕ}

/-- Eq. (9), p. 5: the discretized `3 × 3` transmission matrix of a slab containing `N` particles
with centres `r p` and amplitudes `A p`:
`t(κ_j, κ_i) = (δ_{ij}/w) I₃ + (2π k k_{jz})⁻¹ ∑_p A_p(u_j, u_i) e^{i(k_i - k_j)·r_p}`. -/
def tMat3 (A : Fin N → Amp) (r : Fin N → Fin 3 → ℝ) (j i : Fin (2 * Nk + 1)) :
    Fin 3 → Fin 3 → ℂ :=
  fun a b => (if i = j then ((K.w : ℂ)⁻¹ * (if a = b then 1 else 0)) else 0) +
    ((2 * Real.pi * K.k * K.kz j : ℝ) : ℂ)⁻¹ *
      ∑ p, A p (K.k⁻¹ • K.kvec j) (K.k⁻¹ • K.kvec i) a b *
        Complex.exp (Complex.I * ((dotProduct (K.kvec i - K.kvec j) (r p) : ℝ) : ℂ))

/-- Eq. (10), p. 5: the discretized `3 × 3` reflection matrix
`r(κ_j, κ_i) = (2π k k_{jz})⁻¹ ∑_p A_p(ũ_j, u_i) e^{i(k_i - k̃_j)·r_p}`. -/
def rMat3 (A : Fin N → Amp) (r : Fin N → Fin 3 → ℝ) (j i : Fin (2 * Nk + 1)) :
    Fin 3 → Fin 3 → ℂ :=
  fun a b => ((2 * Real.pi * K.k * K.kz j : ℝ) : ℂ)⁻¹ *
      ∑ p, A p (K.k⁻¹ • K.kvecT j) (K.k⁻¹ • K.kvec i) a b *
        Complex.exp (Complex.I * ((dotProduct (K.kvec i - K.kvecT j) (r p) : ℝ) : ℂ))

/-- Eq. (14), first equality, p. 6: `t̄_{(j,i)} = √(k_{jz}/k_{iz}) t_{(j,i)} w`, where `t_{(j,i)}` is
the reduction (12) of the matrix (9). -/
def tNorm (A : Fin N → Amp) (r : Fin N → Fin 3 → ℝ) (j i : Fin (2 * Nk + 1)) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  ((Real.sqrt (K.kz j / K.kz i) * K.w : ℝ) : ℂ) •
    reduce (tMat3 K A r j i) (K.k⁻¹ • K.kvec i) (K.k⁻¹ • K.kvec j)

/-- Eq. (15), first equality, p. 6: `r̄_{(j,i)} = √(k_{jz}/k_{iz}) r_{(j,i)} w`, where `r_{(j,i)}` is
the reduction (13) of the matrix (10). -/
def rNorm (A : Fin N → Amp) (r : Fin N → Fin 3 → ℝ) (j i : Fin (2 * Nk + 1)) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  ((Real.sqrt (K.kz j / K.kz i) * K.w : ℝ) : ℂ) •
    reduce (rMat3 K A r j i) (K.k⁻¹ • K.kvec i) (K.k⁻¹ • K.kvecT j)

/-- Eqs. (14)–(15), p. 6: the reduced single-particle matrix `A_{(j,i)}` ("defined analogously to
`t_{(j,i)}`") for incident wavevector `vin i` and outgoing wavevector `vout j`:
`A^t_{(j,i)}` is `ampRed K X K.kvec K.kvec j i`, `A^r_{(j,i)}` is `ampRed K X K.kvec K.kvecT j i`. -/
def ampRed (X : Amp) (vin vout : Fin (2 * Nk + 1) → Fin 3 → ℝ) (j i : Fin (2 * Nk + 1)) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  reduce (X (K.k⁻¹ • vout j) (K.k⁻¹ • vin i)) (K.k⁻¹ • vin i) (K.k⁻¹ • vout j)

/-- Eqs. (14)–(15), p. 6: the scattered part `C_{ji} ∑_p A_{p(j,i)} e^{i(vin_i - vout_j)·r_p}`
of a normalized block, for incident wavevectors `vin` and outgoing wavevectors `vout`. -/
def blockSum (A : Fin N → Amp) (r : Fin N → Fin 3 → ℝ) (vin vout : Fin (2 * Nk + 1) → Fin 3 → ℝ)
    (j i : Fin (2 * Nk + 1)) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((K.cji j i : ℝ) : ℂ) • ∑ p,
    Complex.exp (Complex.I * ((dotProduct (vin i - vout j) (r p) : ℝ) : ℂ)) •
      ampRed K (A p) vin vout j i

/-- Eq. (14), second equality, p. 6: the normalized transmission block
`t̄_{(j,i)} = δ_{ij} I₂ + C_{ji} ∑_p A^t_{p(j,i)} e^{i(k_i - k_j)·r_p}`. -/
def tbar (A : Fin N → Amp) (r : Fin N → Fin 3 → ℝ) (j i : Fin (2 * Nk + 1)) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  (if i = j then 1 else 0) + blockSum K A r K.kvec K.kvec j i

/-- Eq. (15), second equality, p. 6: the normalized reflection block
`r̄_{(j,i)} = C_{ji} ∑_p A^r_{p(j,i)} e^{i(k_i - k̃_j)·r_p}`. -/
def rbar (A : Fin N → Amp) (r : Fin N → Fin 3 → ℝ) (j i : Fin (2 * Nk + 1)) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  blockSum K A r K.kvec K.kvecT j i

/-- Section 2.1, p. 6 ("analogous expressions … for a left-propagating plane wave incident upon the
right side"; not printed in the paper): the normalized transmission block for incidence from the
right, `t̄'_{(j,i)} = δ_{ij} I₂ + C_{ji} ∑_p A^{t'}_{p(j,i)} e^{i(k̃_i - k̃_j)·r_p}`, with incident
direction `ũ_i` and outgoing direction `ũ_j`; these are the phases of Table A1, p. 24. -/
def tpbar (A : Fin N → Amp) (r : Fin N → Fin 3 → ℝ) (j i : Fin (2 * Nk + 1)) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  (if i = j then 1 else 0) + blockSum K A r K.kvecT K.kvecT j i

/-- Section 2.1, p. 6 (not printed in the paper, see `tpbar`): the normalized reflection block for
incidence from the right, `r̄'_{(j,i)} = C_{ji} ∑_p A^{r'}_{p(j,i)} e^{i(k̃_i - k_j)·r_p}`, with
incident direction `ũ_i` and outgoing direction `u_j`. -/
def rpbar (A : Fin N → Amp) (r : Fin N → Fin 3 → ℝ) (j i : Fin (2 * Nk + 1)) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  blockSum K A r K.kvecT K.kvec j i

end Slab

/-- Index set of the rows of `t̄` in Eq. (16): a mode and a polarization (`θ = 0`, `φ = 1`). -/
abbrev MIdx (Nk : ℕ) := Fin (2 * Nk + 1) × Fin 2

/-- Eq. (16), p. 6: the full matrix built from the `2 × 2` blocks `B_{(j,i)}`, block row `j`,
block column `i`. -/
def assemble {Nk : ℕ} (B : Fin (2 * Nk + 1) → Fin (2 * Nk + 1) → Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (MIdx Nk) (MIdx Nk) ℂ :=
  Matrix.of fun x y => B x.1 y.1 x.2 y.2

/-- Eq. (17), p. 6: the normalized scattering matrix `S̄ = [[r̄, t̄'], [t̄, r̄']]` of a slab. -/
def sMat {Nk N : ℕ} (K : ModeSet Nk) (A : Fin N → Amp) (r : Fin N → Fin 3 → ℝ) :
    Matrix (MIdx Nk ⊕ MIdx Nk) (MIdx Nk ⊕ MIdx Nk) ℂ :=
  Matrix.fromBlocks (assemble (rbar K A r)) (assemble (tpbar K A r)) (assemble (tbar K A r))
    (assemble (rpbar K A r))

/-- Section 2.2, pp. 6–7: the ensemble of slabs of thickness `ΔL = dL` and particle density `n`.
On the probability space `(Ω, P)`, particle `p` has centre `r p` and amplitude `A p`, and:
the particles are statistically independent; each particle's morphology is independent of its
position; the amplitudes are identically distributed (with finite second moments); the `z`
coordinate of each centre is uniform on `[-ΔL/2, ΔL/2]` and independent of the transverse
position (uniform distribution in the slab); and the transverse phase averages obey the paper's
discretization of Eq. (19), `N ⟨e^{i q·ρ}⟩ = (2π)² n ΔL δ_{q,0} / w`, for every transverse vector
`q = κ_i - κ_j - κ_u + κ_v` built from the modes (the replacement
`δ(q_x) δ(q_y) → δ_{q,0}/w` of p. 7, made after the limit `N, V → ∞` at fixed `n = N/V`). -/
def IsSlabEnsemble {Nk : ℕ} (K : ModeSet Nk) (dL n : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {N : ℕ} (r : Fin N → Ω → Fin 3 → ℝ) (A : Fin N → Ω → Amp) : Prop :=
  IsProbabilityMeasure P ∧ 0 < dL ∧ 0 < n ∧
    (∀ p, Measurable (r p)) ∧ (∀ p, Measurable (A p)) ∧
    iIndepFun (fun p ω => (r p ω, A p ω)) P ∧
    (∀ p, IndepFun (r p) (A p) P) ∧
    (∀ p q, IdentDistrib (A p) (A q) P P) ∧
    (∀ p uo ui a b, MemLp (fun ω => A p ω uo ui a b) 2 P) ∧
    (∀ p, IndepFun (fun ω => (r p ω 0, r p ω 1)) (fun ω => r p ω 2) P) ∧
    (∀ p, pdf.IsUniform (fun ω => r p ω 2) (Set.Icc (-dL / 2) (dL / 2)) P) ∧
    (∀ p i j u v,
      (N : ℂ) * ∫ ω, Complex.exp (Complex.I *
          ((((K.kx i - K.kx j - K.kx u + K.kx v) * r p ω 0 +
            (K.ky i - K.ky j - K.ky u + K.ky v) * r p ω 1 : ℝ)) : ℂ)) ∂P =
        if K.kx i - K.kx j - K.kx u + K.kx v = 0 ∧ K.ky i - K.ky j - K.ky u + K.ky v = 0 then
          (((2 * Real.pi) ^ 2 * n * dL / K.w : ℝ) : ℂ)
        else 0)

/-- Eq. (25), left side, p. 8: the covariance `⟨X Y*⟩ - ⟨X⟩⟨Y*⟩` of two complex random
variables. -/
def covC {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X Y : Ω → ℂ) : ℂ :=
  (∫ ω, X ω * star (Y ω) ∂P) - (∫ ω, X ω ∂P) * star (∫ ω, Y ω ∂P)

/-- Eq. (27), left side, p. 9: the pseudo-covariance `⟨X Y⟩ - ⟨X⟩⟨Y⟩` (no complex conjugate). -/
def pcovC {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X Y : Ω → ℂ) : ℂ :=
  (∫ ω, X ω * Y ω ∂P) - (∫ ω, X ω ∂P) * (∫ ω, Y ω ∂P)

/-- Appendix C, p. 25: the slab moved rigidly so that every particle centre is translated by
`L₀` along `z`. -/
def shiftZ {N : ℕ} (L0 : ℝ) (r : Fin N → Fin 3 → ℝ) : Fin N → Fin 3 → ℝ :=
  fun p => r p + ![0, 0, L0]

/-- Eq. (C1), p. 25: `Λ₊^{L₀} = diag(e^{i k_{-N_k z} L₀}, …, e^{i k_{N_k z} L₀}) ⊗ I₂`. -/
def lamPlus {Nk : ℕ} (K : ModeSet Nk) (L0 : ℝ) : Matrix (MIdx Nk) (MIdx Nk) ℂ :=
  Matrix.kroneckerMap (· * ·)
    (Matrix.diagonal fun i => Complex.exp (Complex.I * ((K.kz i * L0 : ℝ) : ℂ)))
    (1 : Matrix (Fin 2) (Fin 2) ℂ)

/-- Appendix C, p. 25: `Λ₋^{L₀} = (Λ₊^{L₀})*` (entrywise complex conjugate). -/
def lamMinus {Nk : ℕ} (K : ModeSet Nk) (L0 : ℝ) : Matrix (MIdx Nk) (MIdx Nk) ℂ :=
  (lamPlus K L0).map star

/-- Appendix C, p. 25: `Λ_±^{L₀} = diag(Λ₊^{L₀}, Λ₋^{L₀})`. -/
def lamPM {Nk : ℕ} (K : ModeSet Nk) (L0 : ℝ) :
    Matrix (MIdx Nk ⊕ MIdx Nk) (MIdx Nk ⊕ MIdx Nk) ℂ :=
  Matrix.fromBlocks (lamPlus K L0) 0 0 (lamMinus K L0)

/-- Appendix C, p. 25: `Λ_∓^{L₀} = (Λ_±^{L₀})*` (entrywise complex conjugate). -/
def lamMP {Nk : ℕ} (K : ModeSet Nk) (L0 : ℝ) :
    Matrix (MIdx Nk ⊕ MIdx Nk) (MIdx Nk ⊕ MIdx Nk) ℂ :=
  (lamPM K L0).map star

/-- Section 2.3, p. 10 (the paper cites Beenakker, Rev. Mod. Phys. 69, 731 (1997), and does not
write the convention out): the transfer matrix of `S = [[r, t'], [t, r']]`, which maps the
right- and left-propagating amplitudes on the left of the slab to those on its right,
`M = [[t - r' t'⁻¹ r, r' t'⁻¹], [-t'⁻¹ r, t'⁻¹]]` (meaningful when `t'` is invertible). -/
def transfer {V : Type*} [Fintype V] [DecidableEq V] (S : Matrix (V ⊕ V) (V ⊕ V) ℂ) :
    Matrix (V ⊕ V) (V ⊕ V) ℂ :=
  Matrix.fromBlocks (S.toBlocks₂₁ - S.toBlocks₂₂ * S.toBlocks₁₂⁻¹ * S.toBlocks₁₁)
    (S.toBlocks₂₂ * S.toBlocks₁₂⁻¹) (-(S.toBlocks₁₂⁻¹ * S.toBlocks₁₁)) S.toBlocks₁₂⁻¹

/-- Appendix B, p. 25: the `n × n` exchange matrix `J_n`, with ones on the anti-diagonal. -/
def exch (n : ℕ) : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun a b => if a = Fin.rev b then 1 else 0

/-- Appendix B, p. 25: `σ_z = diag(1, -1)`. -/
def sigmaZ : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal ![1, -1]

/-- Appendix B, p. 25: `J_{2N_k+1} ⊗ σ_z`. -/
def piMat (Nk : ℕ) : Matrix (MIdx Nk) (MIdx Nk) ℂ :=
  Matrix.kroneckerMap (· * ·) (exch (2 * Nk + 1)) sigmaZ

/-- Reciprocity of a normalized scattering matrix, used in Appendix B (p. 25) and Section 2.3
(p. 10), as derived in Byrnes and Foreman, Phys. Rev. Research 3, 013129 (2021), Eq. (98):
`S̄ = Π S̄ᵀ Π` with `Π = diag(J ⊗ σ_z, J ⊗ σ_z)`; blockwise `r̄ = (J⊗σ_z) r̄ᵀ (J⊗σ_z)`,
`t̄' = (J⊗σ_z) t̄ᵀ (J⊗σ_z)`, `r̄' = (J⊗σ_z) r̄'ᵀ (J⊗σ_z)`. -/
def IsReciprocal {Nk : ℕ} (S : Matrix (MIdx Nk ⊕ MIdx Nk) (MIdx Nk ⊕ MIdx Nk) ℂ) : Prop :=
  S = Matrix.fromBlocks (piMat Nk) 0 0 (piMat Nk) * S.transpose *
    Matrix.fromBlocks (piMat Nk) 0 0 (piMat Nk)

/-- Appendix B, p. 24: `S` is the scattering matrix of the system made of slab 1 (scattering matrix
`S₁ = [[r₁, t₁'], [t₁, r₁']]`) to the left of slab 2 (`S₂`): for all incoming amplitudes `a` (from
the left) and `d` (from the right) there are amplitudes `b` (right-propagating) and `c`
(left-propagating) between the slabs such that `b = t₁ a + r₁' c`, `c = r₂ b + t₂' d`, and `S`
maps `(a, d)` to the outgoing amplitudes `(r₁ a + t₁' c, t₂ b + r₂' d)`. -/
def IsCascade {V : Type*} [Fintype V] (S1 S2 S : Matrix (V ⊕ V) (V ⊕ V) ℂ) : Prop :=
  ∀ a d : V → ℂ, ∃ b c : V → ℂ,
    b = S1.toBlocks₂₁ *ᵥ a + S1.toBlocks₂₂ *ᵥ c ∧
    c = S2.toBlocks₁₁ *ᵥ b + S2.toBlocks₁₂ *ᵥ d ∧
    S *ᵥ Sum.elim a d =
      Sum.elim (S1.toBlocks₁₁ *ᵥ a + S1.toBlocks₁₂ *ᵥ c) (S2.toBlocks₂₁ *ᵥ b + S2.toBlocks₂₂ *ᵥ d)

/-- Appendix D, p. 26: the unit normal `e_⊥ = (e_{ki} × e_{kj})/|e_{ki} × e_{kj}|` of the
scattering plane of incident direction `ui` and outgoing direction `uj`; when the two directions
are parallel (cross product zero), `e_⊥ = e_{φ i}`. -/
def ePerp (ui uj : Fin 3 → ℝ) : Fin 3 → ℝ :=
  if crossProduct ui uj = 0 then ePhi ui else normalize (crossProduct ui uj)

/-- Appendix D, p. 26: `e_{∥ i} = e_⊥ × e_{ki}`, and `e_{∥ i} = e_{θ i}` when the directions are
parallel. -/
def eParIn (ui uj : Fin 3 → ℝ) : Fin 3 → ℝ :=
  if crossProduct ui uj = 0 then eTheta ui else crossProduct (ePerp ui uj) ui

/-- Appendix D, p. 26: `e_{∥ j} = e_⊥ × e_{kj}`, and `e_{∥ j} = e_{θ j}` when the directions are
parallel. -/
def eParOut (ui uj : Fin 3 → ℝ) : Fin 3 → ℝ :=
  if crossProduct ui uj = 0 then eTheta uj else crossProduct (ePerp ui uj) uj

/-- Appendix D, p. 26: the signed angle `θ` from `e_θ` to `e_∥` about the propagation direction
`e_k`: `|θ|` is the angle between them and `θ > 0` when `e_θ × e_∥` points along `e_k`
(the argument of `⟨e_θ, e_∥⟩ + i ⟨e_θ × e_∥, e_k⟩`, in `(-π, π]`). -/
def signedAngle (eth epar ek : Fin 3 → ℝ) : ℝ :=
  Complex.arg ⟨dotProduct eth epar, dotProduct (crossProduct eth epar) ek⟩

/-- Eq. (D1), p. 26: `R(θ) = [[cos θ, sin θ], [-sin θ, cos θ]]`. -/
def rotM (t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Real.cos t : ℂ), (Real.sin t : ℂ); (-(Real.sin t) : ℂ), (Real.cos t : ℂ)]

/-- Appendix D, p. 26: the amplitude matrix `[[S₂, S₃], [S₄, S₁]]` of a `3 × 3` matrix `X` with
respect to the scattering plane, in the convention of Bohren and Huffman: components along
`(e_∥, e'_⊥)` with `e'_⊥ = -e_⊥`, for incidence direction `ui` and outgoing direction `uj`. -/
def ampScatPlane (X : Fin 3 → Fin 3 → ℂ) (ui uj : Fin 3 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun m n => ∑ a, ∑ b,
    ((![eParOut ui uj, -ePerp ui uj] m a : ℝ) : ℂ) * X a b *
      ((![eParIn ui uj, -ePerp ui uj] n b : ℝ) : ℂ)

end Arxiv2205_09423


