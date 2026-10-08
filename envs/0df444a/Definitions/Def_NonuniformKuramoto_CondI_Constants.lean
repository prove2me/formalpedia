-- Prove2me | Definitions.Def_NonuniformKuramoto_CondI_Constants
-- name    : NonuniformKuramoto_CondI_Constants
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T11:24:00.115587+00:00
-- url     : https://prove2.me/theorems/0f2cad72-b809-43a3-8265-d8b54181b3a0
-- title:
--   Constants: $\varphi_{\max}$, $\Gamma_{\min}$, $\Gamma_{\mathrm{critical}}$ (26), $\gamma_{\min}$, $\gamma_{\max}$, $L(P_{ij})$, $\lambda_2$, $\cos\angle(D\mathbf 1,\mathbf 1)$, $\Omega$
-- statement:
--   Let $D\in\mathbb R^n$, $\omega\in\mathbb R^n$ and $P,\varphi\in\mathbb R^{n\times n}$ be the parameters of the non-uniform Kuramoto model (8). This file defines the explicit quantities appearing in Theorems V.1 and V.3.
--
--   1. $\varphi_{\max}=\max_{i,j}\varphi_{ij}$ (over all pairs), $D_{\max}=\max_i D_i$, $D_{\min}=\min_i D_i$.
--   2. The minimal lossless coupling and the critical coupling of (26):
--   $$\Gamma_{\min}:=n\min_{i\neq j}\Big\{\frac{P_{ij}}{D_i}\cos(\varphi_{ij})\Big\},\qquad \Gamma_{\mathrm{critical}}:=\frac{1}{\cos(\varphi_{\max})}\Big(\max_{i\neq j}\Big|\frac{\omega_i}{D_i}-\frac{\omega_j}{D_j}\Big|+2\max_{i}\sum_{j=1}^n\frac{P_{ij}}{D_i}\sin(\varphi_{ij})\Big),$$
--   where the minimum and the first maximum range over ordered pairs $(i,j)$ with $i\ne j$. The two terms inside the bracket are named `omegaSpread` and `lossMax`.
--   3. With $c=\cos(\varphi_{\max})\,\Gamma_{\mathrm{critical}}/\Gamma_{\min}$, the arc lengths $\gamma_{\min}=\arcsin c$ and $\gamma_{\max}=\pi-\arcsin c$; under (26) these are the unique solutions of $\sin\gamma=c$ in $[0,\pi/2-\varphi_{\max}[$ and in $]\pi/2,\pi]$ respectively.
--   4. The Laplacian $L(a_{ij})=\operatorname{diag}(\sum_j a_{ij})-A$ and the second-smallest eigenvalue $\lambda_2(M)$ (counted with multiplicity) of a real symmetric matrix $M$.
--   5. $\cos\angle(D\mathbf 1_n,\mathbf 1_n)=\dfrac{\sum_iD_i}{\sqrt n\,\sqrt{\sum_iD_i^2}}$, the cosine of the angle between the vector $(D_1,\dots,D_n)$ and $\mathbf 1_n$.
--   6. $\Omega=\sum_i\omega_i/\sum_iD_i$ and the Euclidean norm $\|x\|_2=\sqrt{\sum_ix_i^2}$.
--
--   These are the constants in which the paper's sufficient conditions and convergence rates are expressed.
--
--   **Formalization Note** Minima and maxima are finite and are taken with `Finset.inf'`/`sup'`; when the index set is empty ($n\le1$ for pairs $i\ne j$, $n=0$ for single indices) they return $0$, and every statement assumes $n\ge2$. $\lambda_2$ is the published second-smallest-eigenvalue function `AlonMilman.PropertyT.lambda1`, specialised to matrices indexed by $\{1,\dots,n\}$; it returns $0$ on non-symmetric matrices or $n<2$, and since Lean lists eigenvalues in decreasing order it is the entry of index $n-2$. Only $\cos\angle(D\mathbf 1,\mathbf 1)$ is defined, no arccos is taken. $\gamma_{\min}$ and $\gamma_{\max}$ are defined by $\arcsin$; the milestone `gamma_min_max` proves that they are the paper's unique solutions.
-- source:
--   Dörfler & Bullo, Synchronization and Transient Stability in Power Networks and Nonuniform Kuramoto Oscillators, arXiv:0910.5673v4, p. 20, (26) and the definition of γ_min, γ_max; p. 4 (A_max, ∠(x, y), L(a_ij)); p. 5 (λ₂); p. 16, (19) and Ω

import Mathlib
import Definitions.Def_AlonMilman_PropertyT_lambda1

namespace NonuniformKuramoto.CondI

open Classical in
/-- The minimum of `f (i, j)` over ordered pairs `i ≠ j` (`0` if there is no such pair, i.e. `n ≤ 1`). -/
noncomputable def minOffDiag {n : ℕ} (f : Fin n × Fin n → ℝ) : ℝ :=
  if h : (Finset.univ.filter (fun p : Fin n × Fin n => p.1 ≠ p.2)).Nonempty then
    (Finset.univ.filter (fun p : Fin n × Fin n => p.1 ≠ p.2)).inf' h f
  else 0

open Classical in
/-- The maximum of `f (i, j)` over ordered pairs `i ≠ j` (`0` if there is no such pair, i.e. `n ≤ 1`). -/
noncomputable def maxOffDiag {n : ℕ} (f : Fin n × Fin n → ℝ) : ℝ :=
  if h : (Finset.univ.filter (fun p : Fin n × Fin n => p.1 ≠ p.2)).Nonempty then
    (Finset.univ.filter (fun p : Fin n × Fin n => p.1 ≠ p.2)).sup' h f
  else 0

/-- The maximum of `f i` over `i ∈ {1, …, n}` (`0` if `n = 0`). -/
noncomputable def maxIdx {n : ℕ} (f : Fin n → ℝ) : ℝ :=
  if h : (Finset.univ : Finset (Fin n)).Nonempty then Finset.univ.sup' h f else 0

/-- The minimum of `f i` over `i ∈ {1, …, n}` (`0` if `n = 0`). -/
noncomputable def minIdx {n : ℕ} (f : Fin n → ℝ) : ℝ :=
  if h : (Finset.univ : Finset (Fin n)).Nonempty then Finset.univ.inf' h f else 0

/-- `ϕ_max = max_{i,j} ϕ_ij`, the maximum over all pairs (p. 4: `A_max = max_{i,j} A_ij`). -/
noncomputable def phiMax {n : ℕ} (ϕ : Fin n → Fin n → ℝ) : ℝ :=
  maxIdx (fun i => maxIdx (fun j => ϕ i j))

/-- `D_max = max_i D_i`. -/
noncomputable def Dmax {n : ℕ} (D : Fin n → ℝ) : ℝ := maxIdx D

/-- `D_min = min_i D_i`. -/
noncomputable def Dmin {n : ℕ} (D : Fin n → ℝ) : ℝ := minIdx D

/-- `Γ_min = n · min_{i ≠ j} (P_ij / D_i) cos(ϕ_ij)` (p. 20, (26)). -/
noncomputable def GammaMin {n : ℕ} (D : Fin n → ℝ) (P ϕ : Fin n → Fin n → ℝ) : ℝ :=
  (n : ℝ) * minOffDiag (fun p => P p.1 p.2 / D p.1 * Real.cos (ϕ p.1 p.2))

/-- `max_{i ≠ j} |ω_i / D_i − ω_j / D_j|`, the worst-case non-uniformity of the natural
frequencies (p. 20, (26)). -/
noncomputable def omegaSpread {n : ℕ} (D ω : Fin n → ℝ) : ℝ :=
  maxOffDiag (fun p => |ω p.1 / D p.1 - ω p.2 / D p.2|)

/-- `max_{i ∈ {1,…,n}} ∑_{j=1}^n (P_ij / D_i) sin(ϕ_ij)`, the worst-case lossy coupling
(p. 20, (26); `= max_i ∑_j b_ij` with `b_ij = P_ij sin(ϕ_ij)/D_i`, p. 21). -/
noncomputable def lossMax {n : ℕ} (D : Fin n → ℝ) (P ϕ : Fin n → Fin n → ℝ) : ℝ :=
  maxIdx (fun i => ∑ j, P i j / D i * Real.sin (ϕ i j))

/-- `Γ_critical = (1 / cos ϕ_max) (max_{i≠j} |ω_i/D_i − ω_j/D_j| + 2 max_i ∑_j (P_ij/D_i) sin ϕ_ij)`
(p. 20, (26)). -/
noncomputable def GammaCrit {n : ℕ} (D ω : Fin n → ℝ) (P ϕ : Fin n → Fin n → ℝ) : ℝ :=
  1 / Real.cos (phiMax ϕ) * (omegaSpread D ω + 2 * lossMax D P ϕ)

/-- `γ_min = arcsin(cos(ϕ_max) Γ_critical / Γ_min)` (p. 20: the solution of
`sin γ_min = cos(ϕ_max) Γ_critical / Γ_min` in `[0, π/2 − ϕ_max[`). -/
noncomputable def gammaMin {n : ℕ} (D ω : Fin n → ℝ) (P ϕ : Fin n → Fin n → ℝ) : ℝ :=
  Real.arcsin (Real.cos (phiMax ϕ) * GammaCrit D ω P ϕ / GammaMin D P ϕ)

/-- `γ_max = π − arcsin(cos(ϕ_max) Γ_critical / Γ_min)` (p. 20: the solution of
`sin γ_max = cos(ϕ_max) Γ_critical / Γ_min` in `]π/2, π]`). -/
noncomputable def gammaMax {n : ℕ} (D ω : Fin n → ℝ) (P ϕ : Fin n → Fin n → ℝ) : ℝ :=
  Real.pi - Real.arcsin (Real.cos (phiMax ϕ) * GammaCrit D ω P ϕ / GammaMin D P ϕ)

/-- The Laplacian `L(a_ij) = diag(∑_j a_ij) − A` (p. 4). -/
def lap {n : ℕ} (A : Fin n → Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal (fun i => ∑ j, A i j) - Matrix.of A

/-- `λ₂(M)`: the second-smallest eigenvalue, counted with multiplicity, of a real symmetric matrix
`M` (p. 5: "the second-smallest eigenvalue λ₂(L(a_ij))"). This is the published
`AlonMilman.PropertyT.lambda1` (Mathlib's `eigenvalues₀` lists the eigenvalues in decreasing order,
so the second-smallest one has index `n − 2`), specialised to matrices indexed by `Fin n`. Junk value
`0` when `M` is not symmetric or `n < 2`. -/
noncomputable def lambda2 {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  AlonMilman.PropertyT.lambda1 M

/-- `cos(∠(D1_n, 1_n)) = (D1_n)ᵀ1_n / (‖D1_n‖ ‖1_n‖) = ∑_i D_i / (√n · √(∑_i D_i²))` (p. 4). -/
noncomputable def cosAngleD {n : ℕ} (D : Fin n → ℝ) : ℝ :=
  (∑ i, D i) / (Real.sqrt n * Real.sqrt (∑ i, D i ^ 2))

/-- `Ω = ∑_i ω_i / ∑_i D_i` (p. 16, Theorem V.1 2)). -/
noncomputable def Omega {n : ℕ} (D ω : Fin n → ℝ) : ℝ := (∑ i, ω i) / (∑ i, D i)

/-- The Euclidean norm `‖x‖₂ = √(∑_i x_i²)` of a vector of `ℝⁿ` (p. 4). -/
noncomputable def norm2 {n : ℕ} (x : Fin n → ℝ) : ℝ := Real.sqrt (∑ i, x i ^ 2)

end NonuniformKuramoto.CondI


