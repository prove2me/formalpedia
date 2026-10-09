-- Prove2me | Definitions.Def_SphereSOS_DPS_Setting
-- name    : SphereSOS_DPS_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T14:17:44.04889+00:00
-- url     : https://prove2.me/theorems/673a747a-d5d5-478b-aee7-c42321db6144
-- title:
--   §4.1–4.3, pp. 10–13 — the cones SEP, DPS_ℓ, EXT_ℓ, their duals in Herm(d_Ad_B), the polynomial p_M of (25), rsos and csos (Definition 11)
-- statement:
--   This module fixes the objects of §4 of Fang and Fawzi. Let $\mathcal H_A\simeq\mathbb C^{d_A}$ and $\mathcal H_B\simeq\mathbb C^{d_B}$, and let $\ell = m+1\ge 1$ be an integer level. Matrices on $\mathcal H_A\otimes\mathcal H_B$ have rows and columns indexed by pairs $(i,j)$ with $i\in[d_A]$, $j\in[d_B]$; the entry in row $(i,j)$ and column $(k,l)$ is $M_{ij,kl}$. Matrices on $\mathcal H_A\otimes\mathcal H_{B_1}\otimes\cdots\otimes\mathcal H_{B_\ell}$ (each $\mathcal H_{B_i}\simeq\mathbb C^{d_B}$) are indexed by an index of $A$ and an $\ell$-tuple of indices of $B$.
--
--   1. **Separable cone** (18). $\mathcal{SEP}(\mathcal H_A\otimes\mathcal H_B)$ is the set of finite conic combinations
--   $$\rho=\sum_i p_i\,(x_ix_i^\dagger)\otimes(y_iy_i^\dagger),\qquad p_i\ge 0,\ x_i\in\mathbb C^{d_A},\ y_i\in\mathbb C^{d_B}.$$
--   2. **Partial trace** $\mathrm{Tr}_{B[2:\ell]}$: trace out $B_2,\dots,B_\ell$, keeping $A$ and $B_1$.
--   3. **Symmetric projector.** For $\sigma\in\mathfrak S_\ell$, $P_\sigma$ permutes the $\ell$ copies of $\mathcal H_B$, and $\Pi_\ell=\frac{1}{\ell!}\sum_{\sigma\in\mathfrak S_\ell}P_\sigma$ is the orthogonal projector onto the symmetric subspace $\mathrm{Sym}(\mathcal H_B^{\otimes\ell})$.
--   4. **Partial transpose** $R^{\mathsf T_{B[s]}}$: the transpose applied to the first $s$ copies $B_1,\dots,B_s$, as in (22); $R^{\mathsf T_{B[0]}}=R$.
--   5. **DPS cone** (23). $\mathcal{DPS}_\ell$ is the set of positive semidefinite $\rho$ on $\mathcal H_A\otimes\mathcal H_B$ for which there is a positive semidefinite $\rho_{AB[\ell]}$ on $\mathcal H_A\otimes\mathcal H_B^{\otimes\ell}$ with
--   $$\mathrm{Tr}_{B[2:\ell]}\rho_{AB[\ell]}=\rho,\qquad (I\otimes\Pi_\ell)\rho_{AB[\ell]}(I\otimes\Pi_\ell)=\rho_{AB[\ell]},\qquad \rho_{AB[\ell]}^{\mathsf T_{B[s]}}\succeq 0\ \ (s=1,\dots,\ell).$$
--   6. **EXT cone** (24), Remark 3: the same without the partial transpose conditions.
--   7. **Dual cone.** For a set $K$, $K^*=\{M\in\mathrm{Herm}(d_Ad_B):\mathrm{Tr}[M\rho]\ge 0\ \forall\rho\in K\}$.
--   8. **The Hermitian polynomial** (25): $p_M(x,\bar x,y,\bar y)=\sum_{ijkl}M_{ij,kl}\,x_i\bar x_k\,y_j\bar y_l$, and $\|y\|^2=\sum_j|y_j|^2$.
--   9. **rsos and csos** (Definition 11). A function $P(x,\bar x,y,\bar y)$ is a *real sum of squares* (rsos) if it equals $\sum_i g_i^2$ for finitely many real polynomials $g_i$ in the real and imaginary parts of $x$ and $y$; it is a *complex sum of squares* (csos) if it equals $\sum_i|q_i(x,y)|^2$ for finitely many complex polynomials $q_i$ in $x,y$ alone (no conjugates).
--   10. **Tensor vectors** $x\otimes\bar y^{\otimes s}\otimes y^{\otimes(\ell-s)}$, the quadratic form $v^\dagger Wv$, the operator $M_{AB_1}\otimes I_{B[2:\ell]}$, and the support functions $h_{\mathrm{Sep}}(M)=\max\{\mathrm{Tr}[M\rho]:\rho\in\mathcal{SEP},\ \mathrm{Tr}\rho=1\}$ of (4) and $h_{\mathrm{DPS}_\ell}(M)=\max\{\mathrm{Tr}[M\rho]:\rho\in\mathcal{DPS}_\ell,\ \mathrm{Tr}\rho=1\}$ (p. 13).
--
--   These are the objects of the duality Theorem 12 between the DPS hierarchy for entanglement detection and real sums of squares of Hermitian polynomials.
--
--   **Formalization Note** The level is written $\ell=m+1$ with $m\in\mathbb N$, so $\ell\ge1$ is built in, and the copies $B_1,\dots,B_\ell$ are the coordinates $0,\dots,m$ of `Fin (m + 1) → Fin dB`. The cones are named `SEPcone`, `DPScone`, `EXTcone`. Definition 11's rsos is encoded through the page's own remark (p. 12): a Hermitian polynomial is rsos iff the real polynomial $P(a,b)=p(a+ib,a-ib)$ is a sum of squares; the nonnegativity in Definition 11 is implied. $h_{\mathrm{Sep}}$, $h_{\mathrm{DPS}_\ell}$ are real `sSup`s, which are the page's maxima when $d_A,d_B\ge1$ (the sets are nonempty and compact); the theorem using them assumes $d_A,d_B\ge 1$. The partial trace is defined locally rather than through the published `WildeQIT_partialTrace`, because the index layout `Fin dA × (Fin ℓ → Fin dB)` makes the permutation action and the partial transposes uniform.
-- source:
--   Fang, Fawzi, The sum-of-squares hierarchy on the sphere, and applications in quantum information theory, arXiv:1908.05155v1, pp. 10–13, §4.1 (18)–(24), Remark 3, §4.2 Definition 11, §4.3 (25), h_DPS p. 13, (4) p. 3

import Mathlib

namespace SphereSOS.DPS

open Matrix
open scoped ComplexOrder Kronecker

/-! Fang–Fawzi, arXiv:1908.05155v1, §4.1–4.3 (pp. 10–12): the cones SEP, DPS_ℓ, EXT_ℓ,
their duals inside Herm(d_A d_B), the Hermitian polynomial p_M of (25), and rsos / csos
(Definition 11). Levels are written ℓ = m + 1; the B factors B₁, …, B_ℓ are the coordinates
0, …, m of `Fin (m + 1) → Fin dB`. -/

/-- SEP(H_A ⊗ H_B), (18): finite conic combinations `∑ᵢ pᵢ (xᵢxᵢ†) ⊗ (yᵢyᵢ†)`, `pᵢ ≥ 0`. -/
def SEPcone (dA dB : ℕ) : Set (Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ) :=
  {ρ | ∃ (N : ℕ) (p : Fin N → ℝ) (x : Fin N → Fin dA → ℂ) (y : Fin N → Fin dB → ℂ),
    (∀ i, 0 ≤ p i) ∧
    ρ = ∑ i, (p i : ℂ) •
      (Matrix.vecMulVec (x i) (star (x i)) ⊗ₖ Matrix.vecMulVec (y i) (star (y i)))}

/-- Tr_{B[2:ℓ]}, (20): trace out B₂, …, B_ℓ (coordinates 1, …, m), keeping A and B₁
(coordinate 0, the head of `Fin.cons`). -/
def trRest {dA dB m : ℕ}
    (R : Matrix (Fin dA × (Fin (m + 1) → Fin dB)) (Fin dA × (Fin (m + 1) → Fin dB)) ℂ) :
    Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ :=
  fun p q => ∑ c : Fin m → Fin dB, R (p.1, Fin.cons p.2 c) (q.1, Fin.cons q.2 c)

/-- `I_A ⊗ P_σ`: the permutation of the ℓ copies of H_B by `σ ∈ 𝔖_ℓ`. -/
def permOp {dA dB ℓ : ℕ} (σ : Equiv.Perm (Fin ℓ)) :
    Matrix (Fin dA × (Fin ℓ → Fin dB)) (Fin dA × (Fin ℓ → Fin dB)) ℂ :=
  fun p q => if p.1 = q.1 ∧ p.2 = q.2 ∘ σ then 1 else 0

/-- `I_A ⊗ Π_ℓ`, with `Π_ℓ = (1/ℓ!) ∑_{σ ∈ 𝔖_ℓ} P_σ` the orthogonal projector onto the symmetric
subspace Sym(H_B^{⊗ℓ}) (§4.1 (c)). -/
noncomputable def symProj {dA dB : ℕ} (ℓ : ℕ) :
    Matrix (Fin dA × (Fin ℓ → Fin dB)) (Fin dA × (Fin ℓ → Fin dB)) ℂ :=
  ((ℓ.factorial : ℂ)⁻¹) • ∑ σ : Equiv.Perm (Fin ℓ), permOp σ

/-- `R^{T_{B[s]}}`, (22): the partial transpose on the first `s` copies B₁, …, B_s
(coordinates `i < s`). `ptB 0 R = R`. -/
def ptB {dA dB ℓ : ℕ} (s : ℕ)
    (R : Matrix (Fin dA × (Fin ℓ → Fin dB)) (Fin dA × (Fin ℓ → Fin dB)) ℂ) :
    Matrix (Fin dA × (Fin ℓ → Fin dB)) (Fin dA × (Fin ℓ → Fin dB)) ℂ :=
  fun p q => R (p.1, fun i => if (i : ℕ) < s then q.2 i else p.2 i)
    (q.1, fun i => if (i : ℕ) < s then p.2 i else q.2 i)

/-- DPS_ℓ(H_A ⊗ H_B), (23), with ℓ = m + 1: PSD `ρ` with a PSD extension `R` on
H_A ⊗ H_B^{⊗ℓ} satisfying (20) `Tr_{B[2:ℓ]} R = ρ`, (21) `(I ⊗ Π)R(I ⊗ Π) = R`, and (22)
`R^{T_{B[s]}} ⪰ 0` for `s = 1, …, ℓ`. -/
noncomputable def DPScone (dA dB m : ℕ) : Set (Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ) :=
  {ρ | ρ.PosSemidef ∧
    ∃ R : Matrix (Fin dA × (Fin (m + 1) → Fin dB)) (Fin dA × (Fin (m + 1) → Fin dB)) ℂ,
      R.PosSemidef ∧ trRest R = ρ ∧
      symProj (m + 1) * R * symProj (m + 1) = R ∧
      ∀ s ∈ Finset.Icc 1 (m + 1), (ptB s R).PosSemidef}

/-- EXT_ℓ(H_A ⊗ H_B), (24) (Remark 3), with ℓ = m + 1: (23) without the PPT conditions (22). -/
noncomputable def EXTcone (dA dB m : ℕ) : Set (Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ) :=
  {ρ | ρ.PosSemidef ∧
    ∃ R : Matrix (Fin dA × (Fin (m + 1) → Fin dB)) (Fin dA × (Fin (m + 1) → Fin dB)) ℂ,
      R.PosSemidef ∧ trRest R = ρ ∧
      symProj (m + 1) * R * symProj (m + 1) = R}

/-- The dual cone `K* = {M ∈ Herm(d_A d_B) : Tr[Mρ] ≥ 0 ∀ ρ ∈ K}`. -/
def dualCone {dA dB : ℕ} (K : Set (Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ)) :
    Set (Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ) :=
  {M | M.IsHermitian ∧ ∀ ρ ∈ K, 0 ≤ (M * ρ).trace.re}

/-- The Hermitian polynomial (25): `p_M(x, x̄, y, ȳ) = ∑_{ijkl} M_{ij,kl} x_i x̄_k y_j ȳ_l`. -/
def pM {dA dB : ℕ} (M : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ)
    (x : Fin dA → ℂ) (y : Fin dB → ℂ) : ℂ :=
  ∑ i, ∑ j, ∑ k, ∑ l, M (i, j) (k, l) * x i * star (x k) * y j * star (y l)

/-- `‖y‖² = ∑_j |y_j|²`, as a complex number. -/
noncomputable def nsq {dB : ℕ} (y : Fin dB → ℂ) : ℂ :=
  ∑ j, (Complex.normSq (y j) : ℂ)

/-- The real coordinates `(Re x, Im x, Re y, Im y)` of `(x, y) ∈ ℂ^{d_A} × ℂ^{d_B}`. -/
def reIm {dA dB : ℕ} (x : Fin dA → ℂ) (y : Fin dB → ℂ) :
    (Fin dA ⊕ Fin dA) ⊕ (Fin dB ⊕ Fin dB) → ℝ
  | Sum.inl (Sum.inl a) => (x a).re
  | Sum.inl (Sum.inr a) => (x a).im
  | Sum.inr (Sum.inl b) => (y b).re
  | Sum.inr (Sum.inr b) => (y b).im

/-- Real sum-of-squares (rsos), Definition 11 (p. 12), in the page's equivalent form: `P` is a
sum of squares of real polynomials in the real and imaginary parts of `(x, y)`. -/
def IsRSOS {dA dB : ℕ} (P : (Fin dA → ℂ) → (Fin dB → ℂ) → ℂ) : Prop :=
  ∃ (N : ℕ) (g : Fin N → MvPolynomial ((Fin dA ⊕ Fin dA) ⊕ (Fin dB ⊕ Fin dB)) ℝ),
    ∀ x y, P x y = ((∑ i, (MvPolynomial.eval (reIm x y) (g i)) ^ 2 : ℝ) : ℂ)

/-- Complex sum-of-squares (csos), Definition 11 (p. 12): `P = ∑ᵢ |qᵢ(x, y)|²` with `qᵢ`
holomorphic polynomials in `(x, y)` alone (no conjugates). -/
def IsCSOS {dA dB : ℕ} (P : (Fin dA → ℂ) → (Fin dB → ℂ) → ℂ) : Prop :=
  ∃ (N : ℕ) (q : Fin N → MvPolynomial (Fin dA ⊕ Fin dB) ℂ),
    ∀ x y, P x y = ((∑ i, Complex.normSq (MvPolynomial.eval (Sum.elim x y) (q i)) : ℝ) : ℂ)

/-- The tensor vector `x ⊗ ȳ^{⊗s} ⊗ y^{⊗(ℓ−s)}` on H_A ⊗ H_B^{⊗ℓ}: conjugated `y` on the
first `s` copies. `tensVec 0 x y = x ⊗ y^{⊗ℓ}`. -/
def tensVec {dA dB ℓ : ℕ} (s : ℕ) (x : Fin dA → ℂ) (y : Fin dB → ℂ) :
    Fin dA × (Fin ℓ → Fin dB) → ℂ :=
  fun p => x p.1 * ∏ i : Fin ℓ, (if (i : ℕ) < s then star (y (p.2 i)) else y (p.2 i))

/-- The quadratic form `v†Wv`. -/
def qf {ι : Type*} [Fintype ι] (v : ι → ℂ) (W : Matrix ι ι ℂ) : ℂ :=
  star v ⬝ᵥ (W *ᵥ v)

/-- `M_{AB₁} ⊗ I_{B[2:ℓ]}` on H_A ⊗ H_B^{⊗ℓ}, ℓ = m + 1: `M` acts on A and B₁ (coordinate 0),
the identity on B₂, …, B_ℓ. -/
def liftM {dA dB m : ℕ} (M : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ) :
    Matrix (Fin dA × (Fin (m + 1) → Fin dB)) (Fin dA × (Fin (m + 1) → Fin dB)) ℂ :=
  fun p q => if ∀ i : Fin (m + 1), i ≠ 0 → p.2 i = q.2 i then M (p.1, p.2 0) (q.1, q.2 0) else 0

/-- `h_Sep(M) = max_{ρ ∈ Sep} Tr[Mρ]`, (4), with Sep = SEP ∩ {Tr ρ = 1}. -/
noncomputable def hSep {dA dB : ℕ} (M : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ) : ℝ :=
  sSup {r | ∃ ρ ∈ SEPcone dA dB, ρ.trace = 1 ∧ r = (M * ρ).trace.re}

/-- `h_{DPS_ℓ}(M) = max_{ρ ∈ DPS_ℓ} Tr[Mρ]` (p. 13), ℓ = m + 1, over trace-one elements. -/
noncomputable def hDPS {dA dB : ℕ} (m : ℕ) (M : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ) :
    ℝ :=
  sSup {r | ∃ ρ ∈ DPScone dA dB m, ρ.trace = 1 ∧ r = (M * ρ).trace.re}

end SphereSOS.DPS


