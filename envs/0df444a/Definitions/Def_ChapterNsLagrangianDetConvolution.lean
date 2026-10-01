-- Prove2me | Definitions.Def_ChapterNsLagrangianDetConvolution
-- name    : ChapterNsLagrangianDetConvolution
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T04:31:45.851574+00:00
-- url     : https://prove2.me/theorems/08d940fc-1cd1-4720-8905-7ea0f92abd0e
-- title:
--   Chapter NsLagrangianDetConvolution
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterNsLagrangianDetConvolution.lean`): generated def bundle for ChapterNsLagrangianDetConvolution. See BookProof/ChapterNsLagrangianDetConvolution.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNsLagrangianDetConvolution.lean

import Mathlib


/-!
# Lagrangian Navier–Stokes: the incompressibility determinant as a momentum convolution

In Lagrangian (material) variables a fluid configuration is the flow map
`X(a) = a + ξ(a)` of the reference points `a ∈ 𝕋³`, and incompressibility is the constraint
on the **determinant of the deformation gradient**

```
det F(a) = 1,        F(a) = I + ∇ₐξ(a) .
```

This module writes that constraint in momentum space for a Galerkin displacement field with a
finite set `K` of base wave vectors `k ∈ ℝ³`,

```
ξ(a) = Σ_{k ∈ K} ( ξ̂_k e^{i k·a} + conj(ξ̂_k) e^{−i k·a} )        (real by construction),
```

whose complex coefficients `ξ̂_{k,i} = x_{k,i,Re} + i x_{k,i,Im}` are the real phase-space
coordinates `x : K × Fin 3 × Bool → ℝ`.

* **Spatial derivatives are momenta.**  The derivative `∂_{a_c} ξ_r` is the Fourier series with
  coefficients `i w_c ξ̂_{m,r}` (`gradCoef`), `w = ±k` the wave vector of the signed mode `m`:
  `hasDerivAt_dispField` proves that this is literally the derivative of the displacement field.
* **Products are momentum convolutions.**  Expanding `det(I + ∇ξ)` row by row (the determinant
  is multilinear in the rows) turns the local cubic product into the triple convolution
  ```
  (det F)^(q) = Σ_{τ : Fin 3 → Option(modes),  w(τ 0)+w(τ 1)+w(τ 2) = q}  det [row r of B_{τ r}]
  ```
  where `B_none = I` (the identity part of `F`, wave vector `0`) and `B_m = (i w_c ξ̂_{m,r})_{rc}`
  (`detCoef`).  **`det_deformation_eq`** proves that the Fourier series with these coefficients is
  exactly `det(I + ∇ξ(a))` at every point `a` and every configuration.  Because the sum runs over
  *tuples of different modes*, the cross-mode minors survive: the constraint is **not** the
  degenerate rank-one single-mode substitution `F ↦ i ℓ ⊗ ξ` (whose determinant and cofactor
  vanish identically, `NsLagFourier.lagElimSubst_detPoly`).
* `volCoef q = (det F)^(q) − δ_{q,0}` are the Fourier coefficients of the constraint residual
  `det F − 1` (`volume_residual_eq`), and the **volume penalty**
  `V_κ = (κ/2) Σ_q |volCoef q|²` (`volPot`) is a real polynomial, non-negative at every real
  configuration (`volPot_eval_nonneg`), whose zero set consists of incompressible configurations:
  `det_eq_one_of_volPot_eq_zero` (for `κ > 0`, `V_κ = 0` forces `det F(a) = 1` for **all** `a`).
* `dispField_im` — the displacement field is real.

Everything is `sorry`-free and `axiom`-free.  The dynamics and the Faris–Lavine argument are in
`BookProof.ChapterNsLagrangianDetFarisLavine`.
-/

namespace BookProof.NsLagrangianDet

open MvPolynomial Matrix

noncomputable section

variable {K : Type*} [Fintype K]

/-! ## 1. Modes, coefficients and the momentum-space derivative -/

/-- Indices of the real displacement coordinates: base mode `k`, component `i`, and
`false` for the real part, `true` for the imaginary part of `ξ̂_{k,i}`. -/
abbrev DIdx (K : Type*) := K × Fin 3 × Bool

/-- Signed modes: `(k, true)` carries the wave vector `+k` and the coefficient `ξ̂_k`,
`(k, false)` carries `−k` and `conj ξ̂_k`. -/
abbrev SMode (K : Type*) := K × Bool

/-- The wave vector of a signed mode. -/
def wv (kv : K → Fin 3 → ℝ) (m : SMode K) : Fin 3 → ℝ := if m.2 then kv m.1 else -kv m.1

/-- The complex Fourier coefficient of `ξ_i` at the signed mode `m`, as a polynomial in the
real coordinates: `ξ̂_{k,i} = x_{Re} + i x_{Im}` for `+k`, its conjugate for `−k`. -/
def scoef (m : SMode K) (i : Fin 3) : MvPolynomial (DIdx K) ℂ :=
  X (m.1, i, false) + (if m.2 then Complex.I else -Complex.I) • X (m.1, i, true)

/-- **The spatial derivative in momentum space**: the Fourier coefficient of `∂_{a_c} ξ_r` at
the signed mode `m` is `i w_c ξ̂_{m,r}`. -/
def gradCoef (kv : K → Fin 3 → ℝ) (m : SMode K) (r c : Fin 3) : MvPolynomial (DIdx K) ℂ :=
  (Complex.I * ((wv kv m c : ℝ) : ℂ)) • scoef m r

/-- The Fourier coefficients of the deformation gradient `F = I + ∇ξ`: the identity at the
zero mode (`none`) and `gradCoef` at the signed mode `m`. -/
def rowCoef (kv : K → Fin 3 → ℝ) : Option (SMode K) → Fin 3 → Fin 3 → MvPolynomial (DIdx K) ℂ
  | none, r, c => if r = c then 1 else 0
  | some m, r, c => gradCoef kv m r c

/-- The wave vector of an entry of `F`: `0` for the identity part. -/
def owv (kv : K → Fin 3 → ℝ) : Option (SMode K) → Fin 3 → ℝ
  | none => 0
  | some m => wv kv m

/-- The total momentum of a choice of one Fourier component of `F` per row. -/
def tupleWave (kv : K → Fin 3 → ℝ) (τ : Fin 3 → Option (SMode K)) : Fin 3 → ℝ :=
  ∑ r, owv kv (τ r)

open Classical in
/-- **The determinant as a triple momentum convolution**: the Fourier coefficient at `q` of
`det(I + ∇ξ)`, the sum over all choices `τ` of one Fourier component of `F` per row with total
momentum `q` of the determinant of the chosen rows. -/
def detCoef (kv : K → Fin 3 → ℝ) (q : Fin 3 → ℝ) : MvPolynomial (DIdx K) ℂ :=
  ∑ τ ∈ Finset.univ.filter (fun τ => tupleWave kv τ = q),
    (Matrix.of fun r c => rowCoef kv (τ r) r c).det

open Classical in
/-- The Fourier coefficient at `q` of the incompressibility residual `det F − 1`. -/
def volCoef (kv : K → Fin 3 → ℝ) (q : Fin 3 → ℝ) : MvPolynomial (DIdx K) ℂ :=
  detCoef kv q - if q = 0 then 1 else 0

open Classical in
/-- The (finite) set of momenta that occur in `det F`. -/
def waveSet (kv : K → Fin 3 → ℝ) : Finset (Fin 3 → ℝ) := Finset.univ.image (tupleWave kv)

/-- Complex conjugation of the coefficients. -/
def conjP (p : MvPolynomial (DIdx K) ℂ) : MvPolynomial (DIdx K) ℂ := map (starRingEnd ℂ) p

/-- **The incompressibility (volume) penalty** `V_κ = (κ/2) Σ_q |(det F − 1)^(q)|²`, a real
polynomial of degree six in the displacement coordinates. -/
def volPot (kappa : ℝ) (kv : K → Fin 3 → ℝ) : MvPolynomial (DIdx K) ℂ :=
  ((kappa / 2 : ℝ) : ℂ) • ∑ q ∈ waveSet kv, conjP (volCoef kv q) * volCoef kv q



/-! ## 2. The fields in position space -/

/-- Evaluation at a real configuration. -/
def ev (y : DIdx K → ℝ) : MvPolynomial (DIdx K) ℂ →+* ℂ := eval fun j => ((y j : ℝ) : ℂ)

/-- The plane wave `e^{i w·a}`. -/
def phase (w a : Fin 3 → ℝ) : ℂ := Complex.exp (Complex.I * ((∑ c, w c * a c : ℝ) : ℂ))

/-- The displacement field `ξ_i(a)` of the configuration `y`. -/
def dispField (kv : K → Fin 3 → ℝ) (y : DIdx K → ℝ) (a : Fin 3 → ℝ) (i : Fin 3) : ℂ :=
  ∑ m : SMode K, ev y (scoef m i) * phase (wv kv m) a

/-- The displacement gradient `∂_{a_c} ξ_r(a)`, assembled from its momentum-space coefficients. -/
def dispGrad (kv : K → Fin 3 → ℝ) (y : DIdx K → ℝ) (a : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.of fun r c => ∑ m : SMode K, ev y (gradCoef kv m r c) * phase (wv kv m) a









/-! ## 3. The determinant of the deformation gradient is the triple convolution -/



/-- The plane wave of an entry of `F`. -/
def ophase (kv : K → Fin 3 → ℝ) (a : Fin 3 → ℝ) (o : Option (SMode K)) : ℂ :=
  phase (owv kv o) a

















end

end BookProof.NsLagrangianDet


