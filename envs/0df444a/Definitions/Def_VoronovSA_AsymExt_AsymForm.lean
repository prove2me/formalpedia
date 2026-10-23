-- Prove2me | Definitions.Def_VoronovSA_AsymExt_AsymForm
-- name    : VoronovSA_AsymExt_AsymForm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T07:22:41.010072+00:00
-- url     : https://prove2.me/theorems/2d104adc-35b1-4f1d-a45f-221656e24eb5
-- title:
--   Asymmetry form ω*(η, ξ) = (η, f⁺ξ) − (f⁺η, ξ) on D(f⁺) (8), linear independence modulo D_f̄, and the restriction f̂_U of f⁺ cut out by ω*(w_k, ·) = 0 (144)
-- statement:
--   Let $\hat f$ be a linear operator in a complex Hilbert space $\mathcal H$ with adjoint $\hat f^{+}$ and closure $\bar f$, and write $D_g$ for the domain of an operator $g$. This file fixes the objects in which the paper states its characterization of self-adjoint extensions.
--
--   1. **Asymmetry form** (eq. (8)). For $\eta_*,\xi_*\in D_{f^+}$,
--   $$\omega_*(\eta_*,\xi_*)=(\eta_*,\hat f^{+}\xi_*)-(\hat f^{+}\eta_*,\xi_*).$$
--   It is sesquilinear: conjugate-linear in $\eta_*$ and linear in $\xi_*$. It is defined only on $D_{f^+}$.
--
--   2. **Linear independence modulo $D_{\bar f}$** (condition 2) on p. 66). Vectors $w_1,\dots,w_m\in D_{f^+}$ are linearly independent modulo the domain $D_{\bar f}$ of the closure if
--   $$\sum_{k=1}^m c_k w_k\in D_{\bar f}\ \Longrightarrow\ c_1=\dots=c_m=0 .$$
--
--   3. **The operator cut out by a family** (eq. (144)). For $w_1,\dots,w_m\in D_{f^+}$, $\hat f_U$ is the restriction of the adjoint to the joint $\omega_*$-annihilator of the $w_k$:
--   $$D_{f_U}=\{\psi\in D_{f^+}:\ \omega_*(w_k,\psi)=0,\ k=1,\dots,m\},\qquad \hat f_U\psi=\hat f^{+}\psi .$$
--
--   4. **The vectors $e_{U,k}$** (eq. (37), with $\kappa=1$). Let $D_+=\ker(\hat f^{+}-i)$ and $D_-=\ker(\hat f^{+}+i)$ be the deficient subspaces, with orthonormal bases $\{e_{+,k}\}_{k=1}^m$ and $\{e_{-,l}\}_{l=1}^m$, and let $U=(U_{lk})$ be an $m\times m$ complex matrix. Then
--   $$e_{U,k}=e_{+,k}+\sum_{l=1}^m U_{lk}\,e_{-,l}\in D_{f^+},\qquad k=1,\dots,m .$$
--
--   These are the objects in which Theorem 15 describes all self-adjoint extensions without computing the deficient subspaces.
--
--   **Formalization Note** `asymForm f η ξ` takes `η ξ : f.adjoint.domain`, so no junk value outside $D_{f^+}$ exists. `LinIndepModClosure f w` uses `f.closure.domain`, not `f.domain`. The domain in (144) is `cutOutDomain f w`, the image in $H$ of the kernel of the linear map $\psi\mapsto(\omega_*(w_k,\psi))_k$ on $D_{f^+}$, and `cutOut f w = f.adjoint.domRestrict (cutOutDomain f w)`. The deficient subspaces are the published kernels `TeschlQM.SelfAdjoint.kerAdd f.adjoint (-I)` $=\ker(f^+-i)$ and `kerAdd f.adjoint I` $=\ker(f^+ + i)$, and `kerIncl` is the inclusion of such a kernel into $D_{f^+}$. In `eU f eP eM U`, column $k$ of `U` gives $e_{U,k}$. Families are indexed by `Fin m`.
-- source:
--   Voronov, Gitman & Tyutin, Self-adjoint differential operators assosiated with self-adjoint differential expressions, arXiv:quant-ph/0603187v2, p. 10, eq. (8); p. 66, condition 2); p. 68, Theorem 15, eq. (144); p. 23 (D±, κ); p. 24, eq. (37)

import Mathlib
import Definitions.Def_TeschlQM_Shared_IsSymmetric
import Definitions.Def_TeschlQM_SelfAdjoint_addScalar

namespace VoronovSA.AsymExt

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Voronov–Gitman–Tyutin (8), p. 10: the asymmetry form of the adjoint,
`ω*(η*, ξ*) = (η*, f⁺ξ*) − (f⁺η*, ξ*)` for `ξ*, η* ∈ D_{f⁺}`. It is defined only on the domain of
the adjoint `f.adjoint` (no values outside it). The inner product is conjugate-linear in the first
slot, as in the paper (p. 4). -/
noncomputable def asymForm (f : H →ₗ.[ℂ] H) (η ξ : f.adjoint.domain) : ℂ :=
  ⟪(η : H), f.adjoint ξ⟫_ℂ - ⟪f.adjoint η, (ξ : H)⟫_ℂ

/-- For a fixed family `w₁, …, w_m ∈ D_{f⁺}`, the map `ψ ↦ (ω*(w_k, ψ))_{k = 1..m}` on `D_{f⁺}`;
it is linear because `ω*` is linear in its second slot. -/
noncomputable def asymFormRight (f : H →ₗ.[ℂ] H) {m : ℕ} (w : Fin m → f.adjoint.domain) :
    f.adjoint.domain →ₗ[ℂ] (Fin m → ℂ) where
  toFun ψ := fun k => asymForm f (w k) ψ
  map_add' ψ φ := by
    funext k
    simp only [asymForm, Submodule.coe_add, LinearPMap.map_add, inner_add_right, Pi.add_apply]
    ring
  map_smul' c ψ := by
    funext k
    simp only [asymForm, Submodule.coe_smul, LinearPMap.map_smul, inner_smul_right,
      RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
    ring

/-- Voronov–Gitman–Tyutin, condition 2) on p. 66: vectors `w₁, …, w_m ∈ D_{f⁺}` are *linearly
independent modulo `D_{f̄}`* (the domain of the closure `f̄`):
`∑ c_k w_k ∈ D_{f̄}` implies `c_1 = ⋯ = c_m = 0`. -/
def LinIndepModClosure (f : H →ₗ.[ℂ] H) {m : ℕ} (w : Fin m → f.adjoint.domain) : Prop :=
  ∀ c : Fin m → ℂ, (∑ k, c k • (w k : H)) ∈ f.closure.domain → c = 0

/-- The domain in (144), p. 68: `{ψ ∈ D_{f⁺} : ω*(w_k, ψ) = 0, k = 1, …, m}`, as a subspace of `H`. -/
noncomputable def cutOutDomain (f : H →ₗ.[ℂ] H) {m : ℕ} (w : Fin m → f.adjoint.domain) :
    Submodule ℂ H :=
  (LinearMap.ker (asymFormRight f w)).map f.adjoint.domain.subtype

/-- Voronov–Gitman–Tyutin (144), p. 68: the operator `f̂_U` cut out of the adjoint by the family
`w₁, …, w_m`: its domain is `{ψ ∈ D_{f⁺} : ω*(w_k, ψ) = 0, k = 1, …, m}` and it acts as `f⁺`. -/
noncomputable def cutOut (f : H →ₗ.[ℂ] H) {m : ℕ} (w : Fin m → f.adjoint.domain) : H →ₗ.[ℂ] H :=
  f.adjoint.domRestrict (cutOutDomain f w)

omit [CompleteSpace H] in
/-- `Ker(A + z) ⊆ D(A)`: the kernel `TeschlQM.SelfAdjoint.kerAdd A z` consists of vectors of the
domain of `A` (structural). -/
theorem kerAdd_le_domain (A : H →ₗ.[ℂ] H) (z : ℂ) :
    TeschlQM.SelfAdjoint.kerAdd A z ≤ A.domain := by
  rintro x ⟨y, -, rfl⟩
  exact y.2

omit [CompleteSpace H] in
/-- The inclusion of `Ker(A + z)` into the domain `D(A)`. -/
noncomputable def kerIncl (A : H →ₗ.[ℂ] H) (z : ℂ) :
    TeschlQM.SelfAdjoint.kerAdd A z →ₗ[ℂ] A.domain :=
  Submodule.inclusion (kerAdd_le_domain A z)

/-- Voronov–Gitman–Tyutin (37), p. 24 (with `κ = 1`): given orthonormal bases `e_{+,k}` of
`D₊ = Ker(f⁺ − i)` and `e_{−,l}` of `D₋ = Ker(f⁺ + i)` and an `m × m` matrix `U`, the vectors
`e_{U,k} = e_{+,k} + ∑_l U_{lk} e_{−,l}` of `D_{f⁺}` (column `k` of `U`). -/
noncomputable def eU (f : H →ₗ.[ℂ] H) {m : ℕ}
    (eP : OrthonormalBasis (Fin m) ℂ (TeschlQM.SelfAdjoint.kerAdd f.adjoint (-Complex.I)))
    (eM : OrthonormalBasis (Fin m) ℂ (TeschlQM.SelfAdjoint.kerAdd f.adjoint Complex.I))
    (U : Matrix (Fin m) (Fin m) ℂ) : Fin m → f.adjoint.domain :=
  fun k => kerIncl f.adjoint (-Complex.I) (eP k) +
    ∑ l, U l k • kerIncl f.adjoint Complex.I (eM l)

end VoronovSA.AsymExt


