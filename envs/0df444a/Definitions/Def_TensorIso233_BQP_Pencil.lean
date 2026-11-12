-- Prove2me | Definitions.Def_TensorIso233_BQP_Pencil
-- name    : TensorIso233_BQP_Pencil
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T07:07:21.308132+00:00
-- url     : https://prove2.me/theorems/0f675f80-8b08-4aef-ab2b-3af6980cc33a
-- title:
--   Normal rank, common kernels, polynomial kernel vectors, the pencils (7.1) and the quadratic-kernel data $K_T$, $H_T$, $\Sigma_2$, $N$, $P$, $Q$
-- statement:
--   Let $T=(A,B)$ be a tensor and $\mu_T((x,y),v)=(xA-yB)v$ its bilinear map $\mathbb Z^2\times\mathbb Z^3\to\mathbb Z^3$ (2.3).
--
--   1. The **normal rank** of $T$ is the rank of $xA-yB$ over the field $\mathbb Q(x,y)$.
--   2. The **common kernels** (6.2) are $K_R=\ker A\cap\ker B$ and $K_L=\ker A^{\mathsf T}\cap\ker B^{\mathsf T}$ in $\mathbb Q^3$.
--   3. A **homogeneous polynomial kernel vector of degree $d$**, $v_T=\sum_{j=0}^dx^{d-j}y^jv_j$ with $M_Tv_T=0$, corresponds to a tuple $(v_0,\dots,v_d)\in(\mathbb Q^3)^{d+1}$ solving (6.4):
--
--   $$
--   Av_0=0,\qquad Av_j=Bv_{j-1}\ (1\le j\le d),\qquad Bv_d=0 .
--   $$
--
--   The **least degree** $d_T$ is the least $d$ admitting a nonzero solution. The **linear-kernel case** is normal rank $2$, $K_R=0$, $d_T=1$; the **quadratic-kernel case** is normal rank $2$, $K_R=0$, $d_T=2$.
--
--   4. A pencil of the form (7.1) is $M_T(z)=\begin{pmatrix}\ell_Tz&(R_Tz)^{\mathsf T}\\C_Tz&0_{2\times2}\end{pmatrix}$, $z=(x,y)^{\mathsf T}$, with $\ell_T\in\mathrm{Mat}_{1\times2}(\mathbb Z)$ and $C_T,R_T\in\mathrm{Mat}_2(\mathbb Z)$. Its marked diagram is $X_T=(\ell_T;C_T;R_T):\mathbb Z^2\to\mathbb Z^5$, with the sublattices $\Lambda_1=\mathbb Z\oplus\mathbb Z^2\oplus0$ and $\Lambda_2=\mathbb Z\oplus0\oplus\mathbb Z^2$ of $\mathbb Z^5$.
--   5. In the quadratic-kernel case, $K_T=(v_0\,v_1\,v_2)\in\mathrm{Mat}_3(\mathbb Z)$ is the coefficient matrix of a primitive least-degree kernel vector (gcd of its nine entries $1$). The saturated output span $H$ is (2.5) for $\mu_T$. For an integral basis $W=(w_1\,w_2)$ of $H$, the reduced pencil $\bar M_T(x,y)=x\bar A-y\bar B$ is given by $A=W\bar A$, $B=W\bar B$, and $H_T\in\mathrm{Mat}_2(\mathbb Z)$ is defined by (7.5), $\bar M_T(x,y)K_T=H_TL(x,y)$ with $L(x,y)=\begin{pmatrix}-y&x&0\\0&-y&x\end{pmatrix}$. Such a triple $(K_T,W,H_T)$ is called **admissible**.
--   6. For $S=\begin{pmatrix}r&s\\t&u\end{pmatrix}$, (7.6) is $\Sigma_2(S)=\begin{pmatrix}r^2&2rs&s^2\\rt&ru+st&su\\t^2&2tu&u^2\end{pmatrix}$.
--   7. (8.1)–(8.2): $N=2|\det H_T\det K_T|$, $P(S)=N\,H_{T'}SH_T^{-1}$ and $Q(S)=N\,K_{T'}\Sigma_2(S)K_T^{-1}$, integer polynomial matrices in the entries of $S$, evaluated over any commutative ring (in particular over $\mathbb Z/N\mathbb Z$).
--
--   These objects carry the zero-determinant comparison of §§6–8.
--
--   **Formalization Note** $d_T$ is the predicate "$d$ is the least degree with a nonzero solution" (no value is assigned when no kernel vector exists). The identity (7.5) of matrices of linear forms is stated coefficientwise: $\bar AK_T=H_TL_x$ and $-\bar BK_T=H_TL_y$, where $L=xL_x+yL_y$. The integer matrices $NH_T^{-1}=2|\det K_T|\operatorname{sgn}(\det H_T)\operatorname{adj}H_T$ and $NK_T^{-1}=2|\det H_T|\operatorname{sgn}(\det K_T)\operatorname{adj}K_T$ are written without division.
-- source:
--   Thomas Huffstutler, Integral 2 × 3 × 3 Tensor Isomorphism is in BQP, STOC 2027 submission #319 (October 2026), §2.1 (2.3), p. 13; §6.1–6.3, pp. 26–28, (6.1)–(6.4); §7.1, pp. 30–31, (7.1), X_T, Λ₁, Λ₂; §7.2, pp. 36–37, (7.4)–(7.6); §8.2, p. 41, (8.1)–(8.2); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/319.pdf

import Definitions.Def_TensorIso233_BQP_Tensor
import Definitions.Def_TensorIso233_BQP_Bilinear

/-!
# The zero-determinant case: normal rank, common kernels, polynomial kernels and kernel data

Thomas Huffstutler, *Integral 2 × 3 × 3 Tensor Isomorphism is in BQP*, STOC 2027 submission #319
(October 2026), §2.1 (2.3), §6 (pp. 26–29), §7 (pp. 29–37), §8.2 (p. 41).
-/

namespace TensorIso233.BQP

open MvPolynomial
open scoped Matrix

/-! ### The bilinear map (2.3) -/

/-- (2.3), p. 13: the tensor as a bilinear map `μ_T : ℤ² × ℤ³ → ℤ³`,
`μ_T((x, y), v) = (xA − yB) v`. -/
def tensorBilin (T : Tensor) : (Fin 2 → ℤ) →ₗ[ℤ] (Fin 3 → ℤ) →ₗ[ℤ] (Fin 3 → ℤ) :=
  LinearMap.mk₂ ℤ (fun z v => (z 0 • T.1 - z 1 • T.2) *ᵥ v)
    (fun z₁ z₂ v => by
      simp only [Pi.add_apply, add_smul]
      rw [show z₁ 0 • T.1 + z₂ 0 • T.1 - (z₁ 1 • T.2 + z₂ 1 • T.2)
          = (z₁ 0 • T.1 - z₁ 1 • T.2) + (z₂ 0 • T.1 - z₂ 1 • T.2) by abel, Matrix.add_mulVec])
    (fun c z v => by
      simp only [Pi.smul_apply, smul_eq_mul, mul_smul]
      rw [← smul_sub, Matrix.smul_mulVec])
    (fun z v₁ v₂ => by rw [Matrix.mulVec_add])
    (fun c z v => by rw [Matrix.mulVec_smul])

/-! ### Normal rank and common kernels (§6.1, (6.2)) -/

/-- The field `ℚ(x, y)` of rational functions in two variables. -/
abbrev RatFun2 := FractionRing (MvPolynomial (Fin 2) ℚ)

/-- §6.1, p. 26: the normal rank of `T`, the rank of the pencil `xA − yB` over `ℚ(x, y)`. -/
noncomputable def normalRank (T : Tensor) : ℕ :=
  (Matrix.of fun i j : Fin 3 =>
    (algebraMap (MvPolynomial (Fin 2) ℚ) RatFun2)
      (X 0 * C ((T.1 i j : ℤ) : ℚ) - X 1 * C ((T.2 i j : ℤ) : ℚ))).rank

/-- (6.2), p. 27: the common right kernel `K_R = ker A ∩ ker B ⊆ ℚ³`. -/
noncomputable def KR (T : Tensor) : Submodule ℚ (Fin 3 → ℚ) :=
  LinearMap.ker (toQ T.1).mulVecLin ⊓ LinearMap.ker (toQ T.2).mulVecLin

/-- (6.2), p. 27: the common left kernel `K_L = ker Aᵀ ∩ ker Bᵀ ⊆ ℚ³` (in the dual output
space). -/
noncomputable def KL (T : Tensor) : Submodule ℚ (Fin 3 → ℚ) :=
  LinearMap.ker (toQ T.1).transpose.mulVecLin ⊓ LinearMap.ker (toQ T.2).transpose.mulVecLin

/-! ### Homogeneous polynomial kernel vectors (6.3)–(6.4) -/

/-- (6.4), p. 28: `(v₀, …, v_d) ∈ (ℚ³)^{d+1}` solves the coefficient system of a homogeneous
polynomial kernel vector `v_T(x, y) = ∑ⱼ x^{d−j} yʲ vⱼ` of degree `d`:
`A v₀ = 0`, `A vⱼ = B vⱼ₋₁` for `1 ≤ j ≤ d`, and `B v_d = 0`. -/
def IsKerSol (T : Tensor) (d : ℕ) (v : Fin (d + 1) → Fin 3 → ℚ) : Prop :=
  toQ T.1 *ᵥ v 0 = 0 ∧
  (∀ j : Fin d, toQ T.1 *ᵥ v j.succ = toQ T.2 *ᵥ v j.castSucc) ∧
  toQ T.2 *ᵥ v (Fin.last d) = 0

/-- The rational solution space of (6.4) at degree `d`. -/
def kerSolSpace (T : Tensor) (d : ℕ) : Submodule ℚ (Fin (d + 1) → Fin 3 → ℚ) where
  carrier := {v | IsKerSol T d v}
  zero_mem' := by
    refine ⟨?_, fun j => ?_, ?_⟩ <;> simp [Matrix.mulVec_zero]
  add_mem' := by
    rintro v w ⟨hv0, hv1, hv2⟩ ⟨hw0, hw1, hw2⟩
    refine ⟨?_, fun j => ?_, ?_⟩
    · simp [Matrix.mulVec_add, hv0, hw0]
    · simp [Matrix.mulVec_add, hv1 j, hw1 j]
    · simp [Matrix.mulVec_add, hv2, hw2]
  smul_mem' := by
    rintro c v ⟨hv0, hv1, hv2⟩
    refine ⟨?_, fun j => ?_, ?_⟩
    · rw [Pi.smul_apply, Matrix.mulVec_smul, hv0, smul_zero]
    · rw [Pi.smul_apply, Pi.smul_apply, Matrix.mulVec_smul, Matrix.mulVec_smul, hv1 j]
    · rw [Pi.smul_apply, Matrix.mulVec_smul, hv2, smul_zero]

/-- A nonzero homogeneous polynomial kernel vector of degree `d` exists. -/
def HasKerDeg (T : Tensor) (d : ℕ) : Prop :=
  ∃ v : Fin (d + 1) → Fin 3 → ℚ, v ≠ 0 ∧ IsKerSol T d v

/-- §6.3, p. 28: `d` is the least degree `d_T` of a nonzero homogeneous polynomial kernel
vector: one exists at degree `d` and none exists at any smaller degree. (No value is assigned
when no kernel vector exists.) -/
def IsLeastKerDeg (T : Tensor) (d : ℕ) : Prop :=
  HasKerDeg T d ∧ ∀ d' < d, ¬ HasKerDeg T d'

/-- `w` is primitive: the only integers dividing all of its entries are `±1`
(so `w ≠ 0` and the gcd of the entries is `1`). -/
def IsPrimitive {ι : Type*} (w : ι → ℤ) : Prop :=
  ∀ m : ℤ, (∀ i, m ∣ w i) → IsUnit m

/-- §7, p. 29: the linear-kernel case: normal rank two, `K_R = 0`, and `d_T = 1`. -/
def LinearKernelCase (T : Tensor) : Prop :=
  normalRank T = 2 ∧ KR T = ⊥ ∧ IsLeastKerDeg T 1

/-- §7.2, p. 36: the quadratic-kernel case: normal rank two, `K_R = 0`, and `d_T = 2`. -/
def QuadKernelCase (T : Tensor) : Prop :=
  normalRank T = 2 ∧ KR T = ⊥ ∧ IsLeastKerDeg T 2

/-! ### Pencils in the form (7.1), the marked diagram `X_T`, and `Λ₁, Λ₂` (§7.1) -/

/-- (7.1), p. 30: the pencil `M_T(z) = (ℓ_T z, (R_T z)ᵀ; C_T z, 0₂ₓ₂)`, `z = (x, y)ᵀ`, with
`ℓ_T ∈ Mat₁ₓ₂(ℤ)` and `C_T, R_T ∈ Mat₂(ℤ)`, as the tensor `(A, B)` with `M_T = xA − yB`. -/
def pencil71 (ℓ : Matrix (Fin 1) (Fin 2) ℤ) (Cm R : Matrix (Fin 2) (Fin 2) ℤ) : Tensor :=
  (!![ℓ 0 0, R 0 0, R 1 0; Cm 0 0, 0, 0; Cm 1 0, 0, 0],
   !![-ℓ 0 1, -R 0 1, -R 1 1; -Cm 0 1, 0, 0; -Cm 1 1, 0, 0])

/-- p. 31: the marked diagram `X_T = (ℓ_T; C_T; R_T) : ℤ² → ℤ⁵`. -/
def markedX (ℓ : Matrix (Fin 1) (Fin 2) ℤ) (Cm R : Matrix (Fin 2) (Fin 2) ℤ) :
    Matrix (Fin 5) (Fin 2) ℤ :=
  !![ℓ 0 0, ℓ 0 1; Cm 0 0, Cm 0 1; Cm 1 0, Cm 1 1; R 0 0, R 0 1; R 1 0, R 1 1]

/-- `GL₅(ℤ)`. -/
abbrev GL5 := Matrix.GeneralLinearGroup (Fin 5) ℤ

/-- p. 31: `Λ₁ = ℤ ⊕ ℤ² ⊕ 0 ⊆ ℤ⁵` (the `ℓ_T` and `C_T` coordinates). -/
def Lambda1 : Submodule ℤ (Fin 5 → ℤ) :=
  LinearMap.ker (LinearMap.proj (R := ℤ) (φ := fun _ : Fin 5 => ℤ) 3) ⊓
    LinearMap.ker (LinearMap.proj (R := ℤ) (φ := fun _ : Fin 5 => ℤ) 4)

/-- p. 31: `Λ₂ = ℤ ⊕ 0 ⊕ ℤ² ⊆ ℤ⁵` (the `ℓ_T` and `R_T` coordinates). -/
def Lambda2 : Submodule ℤ (Fin 5 → ℤ) :=
  LinearMap.ker (LinearMap.proj (R := ℤ) (φ := fun _ : Fin 5 => ℤ) 1) ⊓
    LinearMap.ker (LinearMap.proj (R := ℤ) (φ := fun _ : Fin 5 => ℤ) 2)

/-! ### Quadratic-kernel data `K_T`, `H_T` (§7.2) -/

/-- (7.4), p. 36: `K = (v₀ v₁ v₂)` is a coefficient matrix of a primitive least-degree
quadratic kernel vector `v_T = x²v₀ + xyv₁ + y²v₂`: its columns solve (6.4) with `d = 2`, and
the gcd of its nine entries is `1`. -/
def IsPrimKernelMatrix (T : Tensor) (K : Mat3) : Prop :=
  IsKerSol T 2 (fun j i => ((K i j : ℤ) : ℚ)) ∧ IsPrimitive (fun p : Fin 3 × Fin 3 => K p.1 p.2)

/-- The saturated output span `H = span_ℚ μ_T(E, F) ∩ ℤ³` of the tensor ((2.5) for (2.3)). -/
def outSpan (T : Tensor) : Submodule ℤ (Fin 3 → ℤ) := satSpan (tensorBilin T)

/-- The two columns `w₁, w₂` of `W` form a `ℤ`-basis of the saturated output span: both lie in
it, and every element of it is `W c` for exactly one `c ∈ ℤ²`. -/
def IsOutBasis (T : Tensor) (W : Matrix (Fin 3) (Fin 2) ℤ) : Prop :=
  (∀ j, (fun i => W i j) ∈ outSpan T) ∧ ∀ w ∈ outSpan T, ∃! c : Fin 2 → ℤ, W *ᵥ c = w

/-- p. 36: `M̄_T(x, y) = xĀ − yB̄` is the `2 × 3` pencil of coordinates of `M_T` in the basis
`W` of the saturated output span (the unused output direction deleted): `A = WĀ`, `B = WB̄`. -/
def IsReducedPencil (T : Tensor) (W : Matrix (Fin 3) (Fin 2) ℤ)
    (Ab Bb : Matrix (Fin 2) (Fin 3) ℤ) : Prop :=
  W * Ab = T.1 ∧ W * Bb = T.2

/-- The coefficient of `x` in `L(x, y) = (−y x 0; 0 −y x)` of (7.4). -/
def Lx : Matrix (Fin 2) (Fin 3) ℤ := !![0, 1, 0; 0, 0, 1]

/-- The coefficient of `y` in `L(x, y) = (−y x 0; 0 −y x)` of (7.4). -/
def Ly : Matrix (Fin 2) (Fin 3) ℤ := !![-1, 0, 0; 0, -1, 0]

/-- (7.5), p. 36: `M̄_T(x, y) K_T = H_T L(x, y)` as an identity of matrices of linear forms,
i.e. coefficientwise in `x` and `y`: `Ā K = H Lₓ` and `−B̄ K = H L_y`. -/
def Eq75 (Ab Bb : Matrix (Fin 2) (Fin 3) ℤ) (K : Mat3) (H : Matrix (Fin 2) (Fin 2) ℤ) : Prop :=
  Ab * K = H * Lx ∧ -(Bb * K) = H * Ly

/-- Admissible quadratic-kernel data `(K_T, W, H_T)` for `T` (Lemma 7.3): `K_T` a primitive
coefficient matrix, `W` a basis of the saturated output span, and `H_T` the matrix of (7.5) for
the reduced pencil in that basis. -/
def IsAdmissible (T : Tensor) (K : Mat3) (W : Matrix (Fin 3) (Fin 2) ℤ)
    (H : Matrix (Fin 2) (Fin 2) ℤ) : Prop :=
  IsPrimKernelMatrix T K ∧ IsOutBasis T W ∧
    ∃ Ab Bb, IsReducedPencil T W Ab Bb ∧ Eq75 Ab Bb K H

/-- (7.6), p. 37: for `S = (r s; t u)`,
`Σ₂(S) = (r² 2rs s²; rt ru+st su; t² 2tu u²)`, over any commutative ring. -/
def sigma2 {R : Type*} [CommRing R] (S : Matrix (Fin 2) (Fin 2) R) : Matrix (Fin 3) (Fin 3) R :=
  !![S 0 0 ^ 2, 2 * S 0 0 * S 0 1, S 0 1 ^ 2;
     S 0 0 * S 1 0, S 0 0 * S 1 1 + S 0 1 * S 1 0, S 0 1 * S 1 1;
     S 1 0 ^ 2, 2 * S 1 0 * S 1 1, S 1 1 ^ 2]

/-! ### The congruence data (8.1)–(8.3) -/

/-- (8.1), p. 41: `N = 2 |det H_T · det K_T|`. -/
def Nval (K : Mat3) (H : Matrix (Fin 2) (Fin 2) ℤ) : ℕ := 2 * (H.det * K.det).natAbs

/-- The integer matrix `N H_T⁻¹ = 2 |det K_T| sgn(det H_T) adj(H_T)` (exact, since
`H⁻¹ = adj H / det H`). -/
def NHinv (K : Mat3) (H : Matrix (Fin 2) (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  (2 * |K.det| * Int.sign H.det) • H.adjugate

/-- The integer matrix `N K_T⁻¹ = 2 |det H_T| sgn(det K_T) adj(K_T)`. -/
def NKinv (K : Mat3) (H : Matrix (Fin 2) (Fin 2) ℤ) : Mat3 :=
  (2 * |H.det| * Int.sign K.det) • K.adjugate

/-- (8.2), p. 41: `P(S) = N H_{T'} S H_T⁻¹`, an integer polynomial matrix in the entries of `S`,
evaluated at `S` over any commutative ring. -/
def Pcong {R : Type*} [CommRing R] (K : Mat3) (H H' : Matrix (Fin 2) (Fin 2) ℤ)
    (S : Matrix (Fin 2) (Fin 2) R) : Matrix (Fin 2) (Fin 2) R :=
  H'.map (Int.cast : ℤ → R) * S * (NHinv K H).map (Int.cast : ℤ → R)

/-- (8.2), p. 41: `Q(S) = N K_{T'} Σ₂(S) K_T⁻¹`, an integer polynomial matrix in the entries of
`S`, evaluated at `S` over any commutative ring. -/
def Qcong {R : Type*} [CommRing R] (K K' : Mat3) (H : Matrix (Fin 2) (Fin 2) ℤ)
    (S : Matrix (Fin 2) (Fin 2) R) : Matrix (Fin 3) (Fin 3) R :=
  K'.map (Int.cast : ℤ → R) * sigma2 S * (NKinv K H).map (Int.cast : ℤ → R)

end TensorIso233.BQP


