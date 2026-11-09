-- Prove2me | Definitions.Def_MuonLastIterate110_Stochastic_NewtonSchulz
-- name    : MuonLastIterate110_Stochastic_NewtonSchulz
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T07:55:40.57631+00:00
-- url     : https://prove2.me/theorems/589fad6d-1de0-42c8-b3c7-8db3aa2c6a2f
-- title:
--   Finite quintic Newton–Schulz map $\Phi_\varepsilon$, the constants $\ell_J, u_J$, and $\psi_\varepsilon$
-- statement:
--   Parameters are real $m\times n$ matrices with the Frobenius norm $\|X\|=\|X\|_F$ and inner product $\langle X,Y\rangle=\operatorname{tr}(X^\top Y)$.
--
--   **Coefficients and scalar polynomial.** With the practical quintic coefficients $(a,b,c)=(3.4445,\,-4.7750,\,2.0315)$ of (3.5), let
--
--   $$
--   P(s)=as+bs^3+cs^5,\qquad \varphi_J=P^{\circ J},\qquad
--   q_J(s)=\begin{cases}\varphi_J(s)/s,& s>0,\\ a^J,& s=0,\end{cases}
--   $$
--
--   and $\ell_J=\min_{0\le s\le1}q_J(s)$, $u_J=\max_{0\le s\le1}q_J(s)$; also $B:=u_J$.
--
--   **Newton–Schulz map.** For $J\ge1$ and $\varepsilon\ge0$, $\Phi_\varepsilon(N)$ is the output $Z_J$ of
--
--   $$
--   Z_0=\frac{N}{\|N\|_F+\varepsilon},\qquad Z_{j+1}=aZ_j+bZ_jZ_j^\top Z_j+c(Z_jZ_j^\top)^2Z_j,\quad j=0,\dots,J-1,
--   $$
--
--   with $\Phi_0(0)=0$.
--
--   **Radial function.** $\psi_\varepsilon(x)=x^2/(x+\varepsilon)$ when $x+\varepsilon>0$, and $\psi_\varepsilon(x)=0$ when $x=\varepsilon=0$; in particular $\psi_0(x)=x$ for $x\ge0$.
--
--   These are the objects of Lemma 3.2 and of every descent estimate of the paper: the map is the matrix polynomial iteration actually run by Muon, not the polar factor.
--
--   **Formalization Note** A matrix is stored as a vector of `EuclideanSpace ℝ (Fin m × Fin n)`, whose norm and inner product are the Frobenius ones; `toMat`/`ofMat` convert for the matrix products. The coefficients are exact real decimals. $\ell_J$ and $u_J$ are written as the infimum and supremum of $q_J([0,1])$; Lemma 3.2 asserts they are attained. Lean's $x/0=0$ and $0^{-1}=0$ give exactly the source's conventions $\Phi_0(0)=0$ (as $Z_0=0$ and every step maps $0$ to $0$) and $\psi_0(0)=0$; both are proved in the verification file.
-- source:
--   Ping Li and Vincent Y. F. Tan, Last-Iterate Stationarity of Muon with Finitely Many Newton-Schulz Iterations, STOC 2027 submission #110 preprint (2026), source.pdf SHA-256 5362e7185a9ddcba39d1a70da110a8b04f1d179ad818e6d5d0ec73bf29586372, pp.5–7, §3.1 (3.4), (3.5), §3.2 definitions of P, φ_J, q_J, ℓ_J, u_J, and p.7 definitions of B and ψ_ε; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/110.pdf

import Mathlib

namespace MuonLastIterate110.Stochastic

/-- The parameter space `ℝ^{m×n}` (§3.1, p.5). A matrix is stored as a Euclidean vector indexed
by `Fin m × Fin n`, so the norm is the Frobenius norm `‖X‖_F = (∑ᵢⱼ Xᵢⱼ²)^{1/2}` and the inner
product is the Frobenius inner product `⟨X, Y⟩ = ∑ᵢⱼ XᵢⱼYᵢⱼ = tr(XᵀY)`; these are the only norm and
inner product on this type. -/
abbrev Mat (m n : ℕ) := EuclideanSpace ℝ (Fin m × Fin n)

/-- Read a parameter as an `m × n` matrix, for the matrix products of (3.4). -/
def toMat {m n : ℕ} (X : Mat m n) : Matrix (Fin m) (Fin n) ℝ :=
  fun i j => X.ofLp (i, j)

/-- Store an `m × n` matrix as a parameter (inverse of `toMat`). -/
def ofMat {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : Mat m n :=
  WithLp.toLp 2 (fun p : Fin m × Fin n => A p.1 p.2)

/-- The quintic Newton–Schulz coefficients (3.5): `a = 3.4445`. -/
noncomputable def nsA : ℝ := 3.4445

/-- The quintic Newton–Schulz coefficients (3.5): `b = −4.7750`. -/
noncomputable def nsB : ℝ := -4.7750

/-- The quintic Newton–Schulz coefficients (3.5): `c = 2.0315`. -/
noncomputable def nsC : ℝ := 2.0315

/-- The scalar polynomial `P(s) = a s + b s³ + c s⁵` (§3.2, p.6). -/
noncomputable def P (s : ℝ) : ℝ := nsA * s + nsB * s ^ 3 + nsC * s ^ 5

/-- `φ_J = P^{∘J}`, the `J`-fold composition of `P` (§3.2, p.6). -/
noncomputable def phi (J : ℕ) : ℝ → ℝ := P^[J]

/-- The amplification factor `q_J(s) = φ_J(s)/s` for `s > 0`, and `q_J(0) = a^J` (§3.2, p.6).
Only its values on `[0, 1]` are used. -/
noncomputable def q (J : ℕ) (s : ℝ) : ℝ :=
  if 0 < s then phi J s / s else nsA ^ J

/-- `ℓ_J = min_{0 ≤ s ≤ 1} q_J(s)` (§3.2, p.6), written as the infimum of the image of `[0,1]`;
Lemma 3.2 asserts that this infimum is attained. -/
noncomputable def ellJ (J : ℕ) : ℝ := sInf (q J '' Set.Icc 0 1)

/-- `u_J = max_{0 ≤ s ≤ 1} q_J(s)` (§3.2, p.6), written as the supremum of the image of `[0,1]`;
Lemma 3.2 asserts that this supremum is attained. Also `B := u_J` (p.7). -/
noncomputable def uJ (J : ℕ) : ℝ := sSup (q J '' Set.Icc 0 1)

/-- One quintic Newton–Schulz step of (3.4): `Z ↦ aZ + bZZᵀZ + c(ZZᵀ)²Z`. -/
noncomputable def nsStep {m n : ℕ} (Z : Matrix (Fin m) (Fin n) ℝ) : Matrix (Fin m) (Fin n) ℝ :=
  nsA • Z + nsB • (Z * Z.transpose * Z) + nsC • ((Z * Z.transpose) ^ 2 * Z)

/-- The finite Newton–Schulz map `Φ_ε(N) = Z_J` of (3.4): `Z₀ = N / (‖N‖_F + ε)` and
`J` steps of `nsStep`. When `N = 0` and `ε = 0`, Lean's `0⁻¹ = 0` gives `Z₀ = 0`, hence
`Φ₀(0) = 0`, the source's convention (p.6). -/
noncomputable def Phi {m n : ℕ} (J : ℕ) (ε : ℝ) (N : Mat m n) : Mat m n :=
  ofMat (nsStep^[J] (toMat ((‖N‖ + ε)⁻¹ • N)))

/-- `ψ_ε(x) = x² / (x + ε)` when `x + ε > 0`, and `ψ_ε(x) = 0` when `x = ε = 0` (p.7). Lean's
division by zero returns `0`, which is exactly the source's value at `x = ε = 0`; only `x ≥ 0`,
`ε ≥ 0` are used. -/
noncomputable def psi (ε x : ℝ) : ℝ := x ^ 2 / (x + ε)

end MuonLastIterate110.Stochastic


