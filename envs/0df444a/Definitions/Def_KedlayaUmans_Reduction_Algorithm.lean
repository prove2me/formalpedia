-- Prove2me | Definitions.Def_KedlayaUmans_Reduction_Algorithm
-- name    : KedlayaUmans_Reduction_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T06:46:59.53041+00:00
-- url     : https://prove2.me/theorems/dc5a2c22-6587-4f82-9f23-5ec510591184
-- title:
--   The six-step reduction algorithm of Theorem 3.1
-- statement:
--   Fix integers $2 \le d_0 < d$, $m, N \ge 1$, and let
--   $$
--   \ell = \lceil \log_{d_0} d \rceil, \qquad N' = N m \ell d_0 .
--   $$
--   Given $f \in R[X_0, \dots, X_{m-1}]$, polynomials $g_0, \dots, g_{m-1}, h \in R[X]$ and points $\beta_0, \dots, \beta_{N'-1} \in R$, the algorithm in the proof of Theorem 3.1 performs:
--
--   1. $f' = \psi_{d_0,\ell}(f)$.
--   2. $g_{i,j}(X) = g_i(X)^{d_0^{\,j}} \bmod h(X)$ for all $i$ and $j = 0, \dots, \ell - 1$.
--   3. $\alpha_{i,j,k} = g_{i,j}(\beta_k)$ for all $i, j, k$.
--   4. $f'(\alpha_{0,0,k}, \dots, \alpha_{m-1,\ell-1,k})$ for $k = 0, \dots, N'-1$ (one call to multivariate multipoint evaluation, Problem 2.1).
--   5. Interpolate the values of Step 4 at the nodes $\beta_0, \dots, \beta_{N'-1}$.
--   6. Output the result of Step 5 modulo $h(X)$.
--
--   Each step is a separate definition (`step1`, …, `step5`, `algorithm`), so that the intermediate quantities $f'$ and $g_{i,j}$ can be named in the milestones.
--
--   **Formalization Note** $\ell$ is `Nat.clog d₀ d`, the least $\ell$ with $d \le d_0^{\ell}$, which is $\lceil \log_{d_0} d \rceil$ for $d_0 \ge 2$. "mod $h$" is `modLc` and the interpolation is `interpolate` (both from the `PolyOps` definition). Step 4 is `MvPolynomial.eval`, exactly the output Problem 2.1 specifies. Step 5 uses only the $N'$ values of Step 4 and the nodes, not the polynomial they come from. The running time is not formalized.
-- source:
--   Kedlaya, Umans, Fast polynomial factorization and modular composition, Dagstuhl Seminar Proceedings 08381 (version of Aug. 31, 2008), pp. 9-10, Theorem 3.1 and its proof (Steps 1-6)

import Mathlib
import Definitions.Def_KedlayaUmans_Reduction_Psi
import Definitions.Def_KedlayaUmans_Reduction_PolyOps

namespace KedlayaUmans.Reduction

open Polynomial

/-- `ℓ = ⌈log_{d₀} d⌉`, the number of base-`d₀` digits used (Theorem 3.1). -/
def ell (d₀ d : ℕ) : ℕ := Nat.clog d₀ d

/-- `N' = N m ℓ d₀`, the number of evaluation points (Theorem 3.1). -/
def Nprime (N m d₀ d : ℕ) : ℕ := N * m * ell d₀ d * d₀

/-- Step 1 of the proof of Theorem 3.1: `f' = ψ_{d₀,ℓ}(f)`. -/
noncomputable def step1 {R : Type*} [CommRing R] {m : ℕ} (d₀ d : ℕ)
    (f : MvPolynomial (Fin m) R) : MvPolynomial (Fin m × Fin (ell d₀ d)) R :=
  psi d₀ (ell d₀ d) f

/-- Step 2: `g_{i,j}(X) = g_i(X)^{d₀^j} mod h(X)` for all `i` and `j = 0, …, ℓ - 1`. -/
noncomputable def step2 {R : Type*} [CommRing R] {m : ℕ} (d₀ d : ℕ)
    (g : Fin m → R[X]) (h : R[X]) : Fin m × Fin (ell d₀ d) → R[X] :=
  fun ij => modLc (g ij.1 ^ (d₀ ^ (ij.2 : ℕ))) h

/-- Step 3: `α_{i,j,k} = g_{i,j}(β_k)` for the supplied points `β_0, …, β_{N'-1}`. -/
noncomputable def step3 {R : Type*} [CommRing R] {m N : ℕ} (d₀ d : ℕ)
    (g : Fin m → R[X]) (h : R[X]) (β : Fin (Nprime N m d₀ d) → R) :
    Fin m × Fin (ell d₀ d) → Fin (Nprime N m d₀ d) → R :=
  fun ij k => (step2 d₀ d g h ij).eval (β k)

/-- Step 4 (the single invocation of MULTIVARIATE MULTIPOINT EVALUATION, Problem 2.1):
`f'(α_{0,0,k}, …, α_{m-1,ℓ-1,k})` for `k = 0, …, N' - 1`. -/
noncomputable def step4 {R : Type*} [CommRing R] {m N : ℕ} (d₀ d : ℕ)
    (f : MvPolynomial (Fin m) R) (g : Fin m → R[X]) (h : R[X])
    (β : Fin (Nprime N m d₀ d) → R) : Fin (Nprime N m d₀ d) → R :=
  fun k => MvPolynomial.eval (fun ij => step3 d₀ d g h β ij k) (step1 d₀ d f)

/-- Step 5: interpolate from the `N'` values of Step 4 at the nodes `β_k`. -/
noncomputable def step5 {R : Type*} [CommRing R] {m N : ℕ} (d₀ d : ℕ)
    (f : MvPolynomial (Fin m) R) (g : Fin m → R[X]) (h : R[X])
    (β : Fin (Nprime N m d₀ d) → R) : R[X] :=
  interpolate β (step4 d₀ d f g h β)

/-- Step 6, the output of the algorithm of Theorem 3.1: the result of Step 5 modulo `h(X)`. -/
noncomputable def algorithm {R : Type*} [CommRing R] {m N : ℕ} (d₀ d : ℕ)
    (f : MvPolynomial (Fin m) R) (g : Fin m → R[X]) (h : R[X])
    (β : Fin (Nprime N m d₀ d) → R) : R[X] :=
  modLc (step5 d₀ d f g h β) h

end KedlayaUmans.Reduction


