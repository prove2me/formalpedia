-- Prove2me | Definitions.Def_PersistQMem_Hsig
-- name    : PersistQMem_Hsig
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T08:42:43.302198+00:00
-- url     : https://prove2.me/theorems/511f3ea7-d4ba-47ea-afd8-83b851f7f69f
-- title:
--   The variance Hilbert space $H_\sigma$, the maps $F^*$, $\ell_j$, $F$, $C$, $\Delta$ and the charges $b_j=\langle c_j,\Delta^+c_j\rangle_\sigma$
-- statement:
--   Fix a complete refined instrument $\Phi$ and a unit vector $u\in\mathbb C^r$ in the entering memory. Put (23)
--   $$\sigma=\Phi(uu^*\otimes\tau),\qquad\delta_j=\Phi(uu^*\otimes G_j/D),\qquad Q_u=I_r-uu^*.$$
--   On Hermitian recorded tests the **covariance** is (24)
--   $$\langle X,Y\rangle_\sigma=\tfrac12\operatorname{Tr}[\sigma(XY+YX)]-\operatorname{Tr}(\sigma X)\operatorname{Tr}(\sigma Y),\qquad\|X\|_\sigma^2=\operatorname{Tr}(\sigma X^2)-[\operatorname{Tr}(\sigma X)]^2 .$$
--   The **variance Hilbert space** $H_\sigma$ is the quotient of Hermitian recorded tests by the zero-variance tests, with this inner product. On tests one has the native-memory map and the source functionals (25)
--   $$F^*X=Q_uN_0^*(X)u\in u^\perp,\qquad\ell_j(X)=\operatorname{Tr}(\delta_jX),$$
--   with $u^\perp$ a real Hilbert space under $\Re\langle w,w'\rangle$. Transported to $H_\sigma$: $c_j\in H_\sigma$ is the Riesz representer of $\ell_j$, $F$ is the real adjoint of $F^*$, and (27)
--   $$C=\sum_jp_j|c_j\rangle\langle c_j|,\qquad\Delta=I-FF^*.$$
--   Finally (33) $b_j=\langle c_j,\Delta^+c_j\rangle_\sigma$, where $\Delta^+$ is the Moore–Penrose pseudoinverse of $\Delta$.
--
--   These are the one-step objects of Lemmas 6.1–6.4: $\Delta$ measures the variance left after the directions already stored in memory, and $b_j$ is the charge a single copy can deliver along $G_j$.
--
--   **Formalization Note** $H_\sigma$ is realized as the range of the real-linear map $\pi X=\bigoplus_a(X_a-\operatorname{Tr}(\sigma X)I)L_a$, $L_a=D^{-1/2}M_a(u\otimes I_D)$, written in real coordinates; since $\sigma_a=L_aL_a^*$, $\pi$ is isometric for $\langle\cdot,\cdot\rangle_\sigma$ and its kernel is the zero-variance tests, so its range is the quotient. $F^*$ and $\ell_j$ are transported to $H_\sigma$ through a fixed linear section of $\pi$; Lemma 6.1 asserts that they are well defined, so the choice does not matter. The values of $F^*$ are written in real coordinates of all of $\mathbb C^r$ (they lie in $u^\perp$), which changes neither $\|F^*X\|$, nor $FF^*$, nor $\operatorname{rank}F$. $\Delta^+$ is the published `HarmonicGames.Decomposition.pinv` on $H_\sigma$.
-- source:
--   Tao, Shen, Structural Lower Bounds for Quantum Property Estimation with Persistent Memory, STOC 2027 submission (manuscript of 2026-11-03, sha256 6d48ad24…), §6.2, (23)–(25), pp.19–20 (PDF pp.22–23); Lemma 6.1, (27), p.20; Lemma 6.2, (33), p.21 (PDF p.24); (38), p.22

import Mathlib
import Definitions.Def_HarmonicGames_Decomposition_Pinv
import Definitions.Def_PersistQMem_FinInstrument

open scoped Matrix ComplexOrder Kronecker InnerProductSpace

namespace PersistQMem

variable {ι : Type} [Fintype ι] {r D K : ℕ}

/-- The rank-one matrix `u u*` of a vector `u ∈ C^r`. -/
def uuStar (u : Fin r → ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.vecMulVec u (star u)

/-- The reference output state `σ = Φ(u u* ⊗ τ)` of (23), p.19 (Tao, Shen, *Structural Lower
Bounds for Quantum Property Estimation with Persistent Memory*, STOC 2027 submission, manuscript of
2026-11-03, sha256 6d48ad24…). -/
noncomputable def sigmaOut (Φ : FinInstrument ι r D K) (u : Fin r → ℂ) : RecTest Φ :=
  recChannel Φ (tau D) (uuStar u)

/-- The source perturbation `δ_j = Φ(u u* ⊗ G_j / D)` of (23), p.19, for `G = G_j`. -/
noncomputable def deltaOut (Φ : FinInstrument ι r D K) (u : Fin r → ℂ)
    (G : Matrix (Fin D) (Fin D) ℂ) : RecTest Φ :=
  recChannel Φ (((D : ℂ)⁻¹) • G) (uuStar u)

/-- The real covariance inner product of (24), p.19, on recorded tests:
`⟨X, Y⟩_σ = ½ Tr[σ(XY + YX)] − Tr(σX) Tr(σY)` (real parts are taken; for Hermitian tests all
three traces are real). -/
noncomputable def covInner (Φ : FinInstrument ι r D K) (u : Fin r → ℂ) (X Y : RecTest Φ) : ℝ :=
  (recTrace Φ (sigmaOut Φ u) (fun a => X a * Y a + Y a * X a)).re / 2 -
    (recTrace Φ (sigmaOut Φ u) X).re * (recTrace Φ (sigmaOut Φ u) Y).re

/-- The variance `‖X‖²_σ = Tr(σX²) − [Tr(σX)]²` of a recorded test ((24), p.19). -/
noncomputable def varSq (Φ : FinInstrument ι r D K) (u : Fin r → ℂ) (X : RecTest Φ) : ℝ :=
  covInner Φ u X X

/-- The real vector space of **Hermitian recorded tests** `X = ⊕_a X_a`, `X_a = X_a*`
(§6.2, p.19). -/
def hermTests (Φ : FinInstrument ι r D K) : Submodule ℝ (RecTest Φ) where
  carrier := {X | ∀ a, (X a).IsHermitian}
  add_mem' hX hY a := (hX a).add (hY a)
  zero_mem' a := Matrix.isHermitian_zero
  smul_mem' c X hX a := by
    change ((c • X a)ᴴ = c • X a)
    rw [Matrix.conjTranspose_smul, (hX a).eq, star_trivial]

/-- The effective source Kraus operator `L_a = D^{−1/2} M_a (u ⊗ I_D) : C^D → C^{k_a}` of (38),
p.22; the output block of `σ` is `σ_a = L_a L_a*`. -/
noncomputable def lfac (Φ : FinInstrument ι r D K) (u : Fin r → ℂ) (a : ι) :
    Matrix (Fin (Φ.k a)) (Fin D) ℂ :=
  ((Real.sqrt D : ℂ)⁻¹) • (Φ.M a * Matrix.of fun (c : Fin r × Fin D) (i : Fin D) =>
    if c.2 = i then u c.1 else 0)

/-- Index type of the real coordinates of block families `⊕_a C^{k_a × D}` (real and imaginary
part of every entry). -/
abbrev CoordIdx (Φ : FinInstrument ι r D K) : Type :=
  Σ a : ι, Fin (Φ.k a) × Fin D × Bool

/-- The real coordinate space `⊕_a C^{k_a × D} ≅ ℝ^{…}` with inner product `ℜ Tr(B* B')`. -/
abbrev CoordSpace (Φ : FinInstrument ι r D K) : Type :=
  EuclideanSpace ℝ (CoordIdx Φ)

/-- The centred, weighted block family `X ↦ ⊕_a (X_a − Tr(σX) I) L_a` (real-linear). -/
noncomputable def centerMul (Φ : FinInstrument ι r D K) (u : Fin r → ℂ) :
    RecTest Φ →ₗ[ℝ] ((a : ι) → Matrix (Fin (Φ.k a)) (Fin D) ℂ) where
  toFun X a := (X a - recTrace Φ (sigmaOut Φ u) X • (1 : Matrix _ _ ℂ)) * lfac Φ u a
  map_add' X Y := by
    funext a
    simp only [Pi.add_apply, recTrace, Matrix.mul_add, Matrix.trace_add, Finset.sum_add_distrib,
      add_smul, Matrix.add_mul, Matrix.sub_mul]
    abel
  map_smul' c X := by
    funext a
    simp only [Pi.smul_apply, recTrace, Matrix.mul_smul, Matrix.trace_smul, RingHom.id_apply,
      Matrix.sub_mul, Matrix.smul_mul, ← Finset.smul_sum, smul_assoc, smul_sub]

/-- Real and imaginary parts of all entries of a block family, as a vector of `CoordSpace`. -/
noncomputable def realify (Φ : FinInstrument ι r D K) :
    ((a : ι) → Matrix (Fin (Φ.k a)) (Fin D) ℂ) →ₗ[ℝ] CoordSpace Φ :=
  (WithLp.linearEquiv 2 ℝ (CoordIdx Φ → ℝ)).symm.toLinearMap ∘ₗ
  { toFun := fun B q => if q.2.2.2 then (B q.1 q.2.1 q.2.2.1).re else (B q.1 q.2.1 q.2.2.1).im
    map_add' := fun B B' => by
      funext q
      by_cases h : q.2.2.2 <;> simp [h]
    map_smul' := fun c B => by
      funext q
      by_cases h : q.2.2.2 <;> simp [h] }

/-- The isometric embedding `π` of Hermitian recorded tests into a real inner product space:
`π X = ⊕_a (X_a − Tr(σX) I) L_a`, so that `‖π X‖² = Tr(σX²) − [Tr(σX)]² = ‖X‖²_σ` and
`⟨π X, π Y⟩ = ⟨X, Y⟩_σ` (because `σ_a = L_a L_a*`). Its kernel is the subspace of zero-variance
tests. -/
noncomputable def embedV (Φ : FinInstrument ι r D K) (u : Fin r → ℂ) :
    hermTests Φ →ₗ[ℝ] CoordSpace Φ :=
  realify Φ ∘ₗ centerMul Φ u ∘ₗ (hermTests Φ).subtype

/-- **The variance Hilbert space `H_σ`** of (24), p.19: the quotient of Hermitian recorded tests by
the zero-variance tests, realized as the range of the isometric embedding `embedV` inside a
finite-dimensional real inner product space. -/
noncomputable def Hsig (Φ : FinInstrument ι r D K) (u : Fin r → ℂ) : Submodule ℝ (CoordSpace Φ) :=
  LinearMap.range (embedV Φ u)

/-- The quotient map `X ↦ [X]` from Hermitian recorded tests onto `H_σ` (surjective). -/
noncomputable def toHsig (Φ : FinInstrument ι r D K) (u : Fin r → ℂ) :
    hermTests Φ →ₗ[ℝ] Hsig Φ u :=
  (embedV Φ u).rangeRestrict

/-- A fixed linear section `H_σ → hermTests` of the quotient map (a right inverse). It is used
only to transport maps on tests to `H_σ`; for maps that vanish on zero-variance tests (Lemma 6.1's
"well-defined", milestone `lemma_6_1`) the result does not depend on the section. -/
noncomputable def secHsig (Φ : FinInstrument ι r D K) (u : Fin r → ℂ) :
    Hsig Φ u →ₗ[ℝ] hermTests Φ :=
  Classical.choose ((toHsig Φ u).exists_rightInverse_of_surjective
    (LinearMap.range_rangeRestrict (embedV Φ u)))

/-- Real coordinates `(ℜ w_c, ℑ w_c)_c` of a vector `w ∈ C^r`; the real inner product of the
image is `ℜ⟨w, w'⟩`. -/
noncomputable def realifyVec (r : ℕ) :
    (Fin r → ℂ) →ₗ[ℝ] EuclideanSpace ℝ (Fin r × Bool) :=
  (WithLp.linearEquiv 2 ℝ (Fin r × Bool → ℝ)).symm.toLinearMap ∘ₗ
  { toFun := fun w q => if q.2 then (w q.1).re else (w q.1).im
    map_add' := fun w w' => by
      funext q
      by_cases h : q.2 <;> simp [h]
    map_smul' := fun c w => by
      funext q
      by_cases h : q.2 <;> simp [h] }

/-- The real-linear map `X ↦ N_0^*(X)` on recorded tests. -/
noncomputable def recAdjointLin (Φ : FinInstrument ι r D K) (ρ : Matrix (Fin D) (Fin D) ℂ) :
    RecTest Φ →ₗ[ℝ] Matrix (Fin r) (Fin r) ℂ where
  toFun X := recAdjoint Φ ρ X
  map_add' X Y := by
    ext i j
    simp [recAdjoint, WildeQIT.partialTraceRight, Matrix.mul_add, Matrix.add_mul,
      Finset.sum_add_distrib]
  map_smul' c X := by
    ext i j
    simp only [recAdjoint, WildeQIT.partialTraceRight, Pi.smul_apply, Matrix.mul_smul,
      Matrix.smul_mul, ← Finset.smul_sum, Matrix.of_apply, Matrix.smul_apply, RingHom.id_apply]

/-- The native-memory map `F* X = Q_u N_0^*(X) u ∈ u^⊥` of (25), p.20, `Q_u = I_r − u u*`, on
Hermitian recorded tests, with values in real coordinates of `C^r` (real inner product
`ℜ⟨w, w'⟩`).

**Formalization Note.** The values lie in `u^⊥` (real dimension `2r − 2`) because of the factor
`Q_u`; the codomain is taken to be all of `C^r` in real coordinates. This changes neither `‖F* X‖`,
nor `F F*`, nor `rank F`. -/
noncomputable def FstarV (Φ : FinInstrument ι r D K) (u : Fin r → ℂ) :
    hermTests Φ →ₗ[ℝ] EuclideanSpace ℝ (Fin r × Bool) :=
  realifyVec r ∘ₗ
  { toFun := fun A => (1 - uuStar u) *ᵥ (A *ᵥ u)
    map_add' := fun A B => by simp [Matrix.add_mulVec, Matrix.mulVec_add]
    map_smul' := fun c A => by simp [Matrix.smul_mulVec, Matrix.mulVec_smul] } ∘ₗ
  recAdjointLin Φ (tau D) ∘ₗ (hermTests Φ).subtype

/-- The source-response functional `ℓ_j(X) = Tr(δ_j X)` of (25), p.20, on Hermitian recorded
tests (`G = G_j`; the trace is real for Hermitian `X`). -/
noncomputable def ellV (Φ : FinInstrument ι r D K) (u : Fin r → ℂ)
    (G : Matrix (Fin D) (Fin D) ℂ) : hermTests Φ →ₗ[ℝ] ℝ where
  toFun X := (recTrace Φ (deltaOut Φ u G) X).re
  map_add' X Y := by
    simp [recTrace, Matrix.mul_add, Finset.sum_add_distrib]
  map_smul' c X := by
    simp [recTrace, Finset.mul_sum]

/-- `F*` as a map on `H_σ` (through the section `secHsig`). -/
noncomputable def FstarH (Φ : FinInstrument ι r D K) (u : Fin r → ℂ) :
    Hsig Φ u →ₗ[ℝ] EuclideanSpace ℝ (Fin r × Bool) :=
  FstarV Φ u ∘ₗ secHsig Φ u

/-- `ℓ_j` as a functional on `H_σ` (through the section `secHsig`). -/
noncomputable def ellH (Φ : FinInstrument ι r D K) (u : Fin r → ℂ)
    (G : Matrix (Fin D) (Fin D) ℂ) : Hsig Φ u →ₗ[ℝ] ℝ :=
  ellV Φ u G ∘ₗ secHsig Φ u

/-- The Riesz representer `c_j ∈ H_σ` of `ℓ_j` (Lemma 6.1, p.20): `⟨c_j, y⟩ = ℓ_j(y)`. -/
noncomputable def cvec (Φ : FinInstrument ι r D K) (u : Fin r → ℂ)
    (G : Matrix (Fin D) (Fin D) ℂ) : Hsig Φ u :=
  (InnerProductSpace.toDual ℝ (Hsig Φ u)).symm (LinearMap.toContinuousLinearMap (ellH Φ u G))

/-- The map `F`, the real adjoint of `F*` (Lemma 6.1, p.20). -/
noncomputable def Fmap (Φ : FinInstrument ι r D K) (u : Fin r → ℂ) :
    EuclideanSpace ℝ (Fin r × Bool) →ₗ[ℝ] Hsig Φ u :=
  LinearMap.adjoint (FstarH Φ u)

/-- The defect operator `Δ = I − F F*` on `H_σ` of (27), p.20. -/
noncomputable def Delta (Φ : FinInstrument ι r D K) (u : Fin r → ℂ) :
    Hsig Φ u →ₗ[ℝ] Hsig Φ u :=
  LinearMap.id - Fmap Φ u ∘ₗ FstarH Φ u

/-- The source covariance operator `C = Σ_j p_j |c_j⟩⟨c_j|` on `H_σ` of (27), p.20. -/
noncomputable def Cop {M : ℕ} (Φ : FinInstrument ι r D K) (u : Fin r → ℂ)
    (G : Fin M → Matrix (Fin D) (Fin D) ℂ) (p : Fin M → ℝ) : Hsig Φ u →ₗ[ℝ] Hsig Φ u :=
  ∑ j, p j • (innerSL ℝ (cvec Φ u (G j))).toLinearMap.smulRight (cvec Φ u (G j))

/-- The charge `b_j = ⟨c_j, Δ⁺ c_j⟩_σ` of (33), p.21, with `Δ⁺` the Moore–Penrose pseudoinverse
of `Δ` on `H_σ` (the published `HarmonicGames.Decomposition.pinv`, taken with respect to the
inner product of `H_σ`). -/
noncomputable def bcoef (Φ : FinInstrument ι r D K) (u : Fin r → ℂ)
    (G : Matrix (Fin D) (Fin D) ℂ) : ℝ :=
  ⟪cvec Φ u G, HarmonicGames.Decomposition.pinv (Delta Φ u) (cvec Φ u G)⟫_ℝ

end PersistQMem


