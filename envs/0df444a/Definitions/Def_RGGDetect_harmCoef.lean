-- Prove2me | Definitions.Def_RGGDetect_harmCoef
-- name    : RGGDetect_harmCoef
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:39:46.149672+00:00
-- url     : https://prove2.me/theorems/94b3fcb2-3a3b-4ef9-947c-e5858adf2902
-- title:
--   Harmonic coefficients and operators: $\alpha_\ell$, $w_\ell$, $b_h$, $A_{h;\mathbf a}$, $T^{u,S}_{\mathbf a}$, $\gamma$, $D_{\mathbf a}$ and the remainders
-- statement:
--   Let $\rho=\langle x,y\rangle$ with $x,y$ independent uniform on $S^{d-1}$, $P_\ell=P_{\ell,d}$, $N_\ell=N_{\ell,d}$. For a multidegree $\mathbf a=(a_i:i\in S)$ and $h\ge0$ write $A=\|\mathbf a\|_1$, $q=(A+h)/2$, $s=(A-h)/2$ (55).
--
--   1. (54), (129) $\alpha_\ell=N_\ell\,\mathbb E[P_\ell(\rho)\kappa(\rho)]$, the zonal coefficients of $\kappa$; $w_\ell=\alpha_\ell^2/N_\ell$.
--   2. (127) $b_h=N_h\,\mathbb E_\rho\big[P_h(\rho)\prod_{i\in S}P_{a_i}(\rho)\big]$, the coefficient of $P_h$ in $\prod_{i\in S}P_{a_i}$.
--   3. (56) $\gamma_{h;\mathbf a}=d^{-q}\prod_{j\in S}\alpha_{a_j}$.
--   4. (57) $A_{h;\mathbf a}(x_u,x_S)=d^q\int P_h(\langle x_u,z\rangle)\prod_{j\in S}P_{a_j}(\langle x_j,z\rangle)\,d\sigma(z)$.
--   5. (60) $(T^{u,S}_{\mathbf a}D)(x_{V\setminus u},x_S)=N_h\,\mathbb E_{x_u}[D(x_u,x_{V\setminus u})A_{h;\mathbf a}(x_u,x_S)]$, $h$ the degree of $D$ in $x_u$.
--   6. (63) $\mathcal A_{k,M}(h)$: the $\mathbf a\in\mathbb N^k$ with $q(h;\mathbf a)\le M$, $A\ge\max\{h,k\}$ and $s\in\mathbb Z$; the remainder $R_{D,S,M}=\eta_{D,S}-\sum_{\mathbf a\in\mathcal A_{k,M}(h)}\gamma_{h;\mathbf a}T^{u,S}_{\mathbf a}D$ of (62).
--   7. (16) $\mathcal A_{k,q}=\{\mathbf a\in\mathbb N^k:\|\mathbf a\|_1=2q\}$; (143) $D_{\mathbf a}(x_1,\dots,x_k)=d^q\int\prod_jP_{a_j}(\langle x_j,z\rangle)\,d\sigma(z)$ and $\gamma_{\mathbf a}=\gamma_{0;\mathbf a}$ with $q=\|\mathbf a\|_1/2$; the remainder $R_{k,M}=\eta_k-\sum_{q=\lceil k/2\rceil}^M\sum_{\mathbf a\in\mathcal A_{k,q}}\gamma_{\mathbf a}D_{\mathbf a}$ of (17).
--
--   **Formalization Note** $\mathbb N=\{1,2,\dots\}$ in multidegrees, as in the paper. A multidegree on $S$ is a function on the index type, positive on $S$ and $0$ off $S$; the paper's $\mathbf a\in\mathbb N^k$ is attached to $S$ through an ordering of $S$. Powers $d^{\pm q}$ with half-integer $q$ are real powers. $D_{\mathbf a}$ and $\gamma_{\mathbf a}$ are the paper's explicit objects (143), (56), not existential ones.
-- source:
--   Du, Mao, Sun, Wu, Xu, Sharp detection thresholds for random geometric graphs with polynomial average degrees, arXiv:2610.08517 (held version, sha256 e7bebd4a…), eqs. (54)–(57), p.18 (PDF p.20); (60), p.19 (PDF p.21); (62)–(63), pp.19–20; (16), (17), p.7; (127), p.34; (129), p.35; (143), p.40

import Mathlib
import Definitions.Def_RGGDetect_cavity
import Definitions.Def_RGGDetect_harmPoly

open MeasureTheory

namespace RGGDetect

/-- `E_ρ[f(ρ)]` for `ρ = ⟨x, y⟩`, `x, y` independent and uniform on `S^{d-1}`
(arXiv:2610.08517, held version, §6, p.30). -/
noncomputable def rhoExp (d : ℕ) (f : ℝ → ℝ) : ℝ :=
  ∫ q, f (ip q.1 q.2) ∂((unifSphere d).prod (unifSphere d))

/-- The zonal coefficients `α_ℓ` of the cap kernel (54), `κ(⟨x, z⟩) = ∑_{ℓ≥1} α_ℓ P_ℓ(⟨x, z⟩)`, given by
(129): `α_ℓ / N_ℓ = E[P_ℓ(ρ) κ(ρ)]` (arXiv:2610.08517, held version, p.18, eq. (54); p.35,
eq. (129)). -/
noncomputable def alphaC (d : ℕ) (τ : ℝ) (ℓ : ℕ) : ℝ :=
  harmDim d ℓ * rhoExp d (fun t => (zonal d ℓ).eval t * kappa d τ t)

/-- The normalized cap coefficients `w_ℓ := (α_ℓ)²/N_ℓ` (arXiv:2610.08517, held version, §6.3, p.35). -/
noncomputable def wC (d : ℕ) (τ : ℝ) (ℓ : ℕ) : ℝ :=
  alphaC d τ ℓ ^ 2 / harmDim d ℓ

/-- The coefficient `b_h` of `P_h` in `Φ_a(t) = ∏_{v∈S} P_{a_v}(t) = ∑_m b_m P_m(t)` (Lemma 11, p.31),
given by (127): `b_h / N_h = E_ρ[P_h(ρ) ∏_{i∈S} P_{a_i}(ρ)]` (arXiv:2610.08517, held version, p.34,
eq. (127)). -/
noncomputable def bCoef {ι : Type*} (d h : ℕ) (S : Finset ι) (a : ι → ℕ) : ℝ :=
  harmDim d h * rhoExp d (fun t => (zonal d h).eval t * ∏ i ∈ S, (zonal d (a i)).eval t)

/-- `q(h; a) = (h + ‖a‖₁)/2` (55), as a real number (arXiv:2610.08517, held version, p.18, eq. (55)). -/
noncomputable def qHA {ι : Type*} (h : ℕ) (S : Finset ι) (a : ι → ℕ) : ℝ :=
  ((h : ℝ) + ∑ j ∈ S, (a j : ℝ)) / 2

/-- The kernel (57), `A_{h;a}(x_u, x_S) := d^q ∫ P_h(⟨x_u, z⟩) ∏_{j∈S} P_{a_j}(⟨x_j, z⟩) dσ(z)`,
`q = q(h; a)` (arXiv:2610.08517, held version, p.18, eq. (57)). -/
noncomputable def kernelA {ι : Type*} (d h : ℕ) (S : Finset ι) (a : ι → ℕ) (u : ι)
    (x : ι → Sph d) : ℝ :=
  (d : ℝ) ^ qHA h S a *
    ∫ z, (zonal d h).eval (ip (x u) z) * ∏ j ∈ S, (zonal d (a j)).eval (ip (x j) z) ∂(unifSphere d)

/-- The averaging operator (60), `(T^{u,S}_a D)(x_{V∖u}, x_S) := N_h E_{x_u}[D(x_u, x_{V∖u})
A_{h;a}(x_u, x_S)]`, where `h` is the degree of `D` in `x_u` (arXiv:2610.08517, held version, p.19,
eq. (60)). The result does not depend on `x_u`.

**Formalization Note** `h = ℓ_u` is passed explicitly. -/
noncomputable def opT {ι : Type*} [DecidableEq ι] (d h : ℕ) (u : ι) (S : Finset ι) (a : ι → ℕ)
    (D : (ι → Sph d) → ℝ) (x : ι → Sph d) : ℝ :=
  harmDim d h *
    ∫ z, D (Function.update x u z) * kernelA d h S a u (Function.update x u z) ∂(unifSphere d)

/-- `γ_{h;a} := d^{-q} ∏_{j∈S} α_{a_j}` (56) (arXiv:2610.08517, held version, p.18, eq. (56)). -/
noncomputable def gammaHA {ι : Type*} (d : ℕ) (τ : ℝ) (h : ℕ) (S : Finset ι) (a : ι → ℕ) : ℝ :=
  (d : ℝ) ^ (-qHA h S a) * ∏ j ∈ S, alphaC d τ (a j)

/-- `A_{k,M}(h)` (63) for the index set `S` (`|S| = k`): the multidegrees `a = (a_i : i ∈ S)` with
every `a_i ≥ 1`, `q(h; a) ≤ M`, and (59): `‖a‖₁ ≥ max{h, k}` and `(‖a‖₁ - h)/2 ∈ ℤ`
(arXiv:2610.08517, held version, p.20, eq. (63)).

**Formalization Note** The paper's `a ∈ ℕ^k` is attached to `S` through an ordering of `S`; here `a`
is a function on the index type, positive on `S` and `0` off `S` (an encoding of `ℕ^S`). -/
noncomputable def multiIdx {ι : Type*} [Fintype ι] [DecidableEq ι] (S : Finset ι) (M h : ℕ) :
    Finset (ι → ℕ) :=
  (Fintype.piFinset fun j => if j ∈ S then Finset.Icc 1 (2 * M) else {0}).filter fun a =>
    h + ∑ j ∈ S, a j ≤ 2 * M ∧ h ≤ ∑ j ∈ S, a j ∧ S.card ≤ ∑ j ∈ S, a j ∧
      Even (∑ j ∈ S, a j - h)

/-- The harmonic remainder `R_{D,S,M}` of (62): `η_{D,S}` minus the main term
`∑_{a ∈ A_{k,M}(h)} γ_{h;a} (T^{u,S}_a D)` (arXiv:2610.08517, held version, pp.19–20, eq. (62)). -/
noncomputable def remDS {ι : Type*} [Fintype ι] [DecidableEq ι] (d : ℕ) (τ : ℝ) (h : ℕ) (u : ι)
    (S : Finset ι) (M : ℕ) (D : (ι → Sph d) → ℝ) (x : ι → Sph d) : ℝ :=
  etaDS d τ D u S x - ∑ a ∈ multiIdx S M h, gammaHA d τ h S a * opT d h u S a D x

/-- `A_{k,q} := {a ∈ ℕ^k : ‖a‖₁ = 2q}` (16), with `ℕ = {1, 2, …}` (arXiv:2610.08517, held version,
p.7, eq. (16)).

**Formalization Note** The entries are positive, as in the paper (`ℓ_v ≥ 1` in (14); proof of
Lemma 8, p.19: "a_j ≥ 1 for every 1 ≤ j ≤ k"; (19): `A_{k,1} = ∅` for `k > 2`). -/
noncomputable def Akq (k q : ℕ) : Finset (Fin k → ℕ) :=
  (Fintype.piFinset fun _ : Fin k => Finset.Icc 1 (2 * q)).filter fun a => ∑ j, a j = 2 * q

/-- `D_a(x₁, …, x_k) := d^q ∫ ∏_{j=1}^k P_{a_j}(⟨x_j, z⟩) dσ(z) = A_{0;a}` (143), `q = ‖a‖₁/2`
(arXiv:2610.08517, held version, p.40, eq. (143)). -/
noncomputable def Da {d k : ℕ} (a : Fin k → ℕ) (x : Fin k → Sph d) : ℝ :=
  (d : ℝ) ^ ((∑ j, (a j : ℝ)) / 2) *
    ∫ z, ∏ j, (zonal d (a j)).eval (ip (x j) z) ∂(unifSphere d)

/-- `γ_a := γ_{0;a} = d^{-q} ∏_{j=1}^k α_{a_j}` (56), `q = ‖a‖₁/2` (arXiv:2610.08517, held version,
p.18, eq. (56); p.39). -/
noncomputable def gammaA {k : ℕ} (d : ℕ) (τ : ℝ) (a : Fin k → ℕ) : ℝ :=
  (d : ℝ) ^ (-((∑ j, (a j : ℝ)) / 2)) * ∏ j, alphaC d τ (a j)

/-- The harmonic remainder `R_{k,M} := η_k - ∑_{q=⌈k/2⌉}^{M} ∑_{a ∈ A_{k,q}} γ_a D_a` of (17)
(arXiv:2610.08517, held version, p.7, eq. (17)). -/
noncomputable def remK (d : ℕ) (τ : ℝ) (k M : ℕ) (x : Fin k → Sph d) : ℝ :=
  eta d τ k x - ∑ q ∈ Finset.Icc ((k + 1) / 2) M, ∑ a ∈ Akq k q, gammaA d τ a * Da a x

end RGGDetect


