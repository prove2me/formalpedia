-- Prove2me | Definitions.Def_RPLib_S4_LarsenM4
-- name    : RPLib_S4_LarsenM4
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T03:17:16.762345+00:00
-- url     : https://prove2.me/theorems/79f5f0c7-f78d-4957-ae8a-2815ad304c02
-- title:
--   Larsen's alternative library: the fourth moment `M4` and the scalar projection
-- statement:
--   `adComm G = End_G(End V)` (endomorphisms of `Matrix n n K` commuting with `Ad(g)`, `g ∈ G`), `M4 G = finrank (adComm G)`
--   (= dim (V ⊗ V ⊗ V^∨ ⊗ V^∨)^G), the counting lemmas `adComm_eq_span` / `exists_coeffs` / `le_M4`, and the
--   equivariant projections `piK` (onto scalars) and `piSL` (onto `sl_n`).
--
--   **Formalization note.** Library module (namespace `RamanujanPetersson.AlgGrpA/B/C` or `RamanujanPetersson.Larsen`) of a formalization of Larsen's alternative, used in a formalization of the Ramanujan-Petersson conjecture. $\mathrm{GL}_n(K)$ is `Matrix.GeneralLinearGroup n K` with the Zariski topology `RamanujanPetersson.AlgGrpA.zarTop` (induced from $\mathrm{Spec}\,K[x_{ij}, y_{ij}]$ via the entries of $g$ and $g^{-1}$; a local instance). The file contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   N. M. Katz, Larsen's alternative, moments, and the monodromy of Lefschetz pencils, in: Contributions to Automorphic Forms, Geometry, and Number Theory (Shalika volume), Johns Hopkins Univ. Press 2004, 521-560; A. Borel, Linear Algebraic Groups, 2nd ed., GTM 126, Springer 1991, doi:10.1007/978-1-4612-0941-6

import Mathlib
import Definitions.Def_RPLib_S4_AlgGrpCInst

/-!
# S4-Larsen: the fourth moment `M4` and the scalar projection

`adComm G = End_G(End V)` (endomorphisms of `Matrix n n K` commuting with `Ad(g)`, `g ∈ G`), `M4 G = finrank (adComm G)`
(= dim (V ⊗ V ⊗ V^∨ ⊗ V^∨)^G), the counting lemmas `adComm_eq_span` / `exists_coeffs` / `le_M4`, and the
equivariant projections `piK` (onto scalars) and `piSL` (onto `sl_n`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Matrix

noncomputable section

namespace RamanujanPetersson.Larsen

open RamanujanPetersson.AlgGrpA RamanujanPetersson.AlgGrpB RamanujanPetersson.AlgGrpC

attribute [local instance] RamanujanPetersson.AlgGrpA.zarTop

variable {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]

section Comm

/-- `End_G(End V)`: endomorphisms of `Matrix n n K` commuting with `Ad(g)` for `g ∈ G`. -/
def adComm (G : Subgroup (Matrix.GeneralLinearGroup n K)) :
    Submodule K (Matrix n n K →ₗ[K] Matrix n n K) where
  carrier := {φ | ∀ g ∈ G, ∀ x : Matrix n n K,
    φ ((g : Matrix n n K) * x * ((g⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K)) =
      (g : Matrix n n K) * φ x * ((g⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K)}
  add_mem' := by
    intro φ ψ hφ hψ g hg x
    rw [LinearMap.add_apply, LinearMap.add_apply, hφ g hg x, hψ g hg x, Matrix.mul_add, Matrix.add_mul]
  zero_mem' := by
    intro g _ x
    rw [LinearMap.zero_apply, LinearMap.zero_apply, Matrix.mul_zero, Matrix.zero_mul]
  smul_mem' := by
    intro c φ hφ g hg x
    rw [LinearMap.smul_apply, LinearMap.smul_apply, hφ g hg x, Matrix.mul_smul, Matrix.smul_mul]

theorem mem_adComm {G : Subgroup (Matrix.GeneralLinearGroup n K)} {φ : Matrix n n K →ₗ[K] Matrix n n K} :
    φ ∈ adComm G ↔ ∀ g ∈ G, ∀ x : Matrix n n K,
      φ ((g : Matrix n n K) * x * ((g⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K)) =
        (g : Matrix n n K) * φ x * ((g⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K) :=
  Iff.rfl

/-- The fourth absolute moment `M4(G, V) = dim (V ⊗ V ⊗ V^∨ ⊗ V^∨)^G = dim End_G(End V)`. -/
def M4 (G : Subgroup (Matrix.GeneralLinearGroup n K)) : ℕ := Module.finrank K (adComm G)

theorem id_mem_adComm (G : Subgroup (Matrix.GeneralLinearGroup n K)) :
    (LinearMap.id : Matrix n n K →ₗ[K] Matrix n n K) ∈ adComm G := fun _ _ _ => rfl

theorem adComm_eq_span {G : Subgroup (Matrix.GeneralLinearGroup n K)} {m : ℕ} (hM : M4 G ≤ m)
    (v : Fin m → (Matrix n n K →ₗ[K] Matrix n n K)) (hv : ∀ i, v i ∈ adComm G)
    (hli : LinearIndependent K v) : adComm G = Submodule.span K (Set.range v) := by
  symm
  refine Submodule.eq_of_le_of_finrank_le (Submodule.span_le.2 (Set.range_subset_iff.2 hv)) ?_
  rw [finrank_span_eq_card hli, Fintype.card_fin]
  exact hM

theorem exists_coeffs {G : Subgroup (Matrix.GeneralLinearGroup n K)} {m : ℕ} (hM : M4 G ≤ m)
    (v : Fin m → (Matrix n n K →ₗ[K] Matrix n n K)) (hv : ∀ i, v i ∈ adComm G)
    (hli : LinearIndependent K v) {Φ : Matrix n n K →ₗ[K] Matrix n n K} (hΦ : Φ ∈ adComm G) :
    ∃ c : Fin m → K, ∑ i, c i • v i = Φ := by
  rw [adComm_eq_span hM v hv hli] at hΦ
  exact (Submodule.mem_span_range_iff_exists_fun K).1 hΦ

theorem le_M4 {G : Subgroup (Matrix.GeneralLinearGroup n K)} {m : ℕ}
    (v : Fin m → (Matrix n n K →ₗ[K] Matrix n n K)) (hv : ∀ i, v i ∈ adComm G)
    (hli : LinearIndependent K v) : m ≤ M4 G := by
  have h := Submodule.finrank_mono (Submodule.span_le.2 (Set.range_subset_iff.2 hv))
  rw [finrank_span_eq_card hli, Fintype.card_fin] at h
  exact h

end Comm

section PiK

/-- `x ↦ (tr x / n) • 1`, the projection of `End V` onto the scalars. -/
def piK : Matrix n n K →ₗ[K] Matrix n n K :=
  (Matrix.traceLinearMap n K K).smulRight ((Fintype.card n : K)⁻¹ • (1 : Matrix n n K))

theorem piK_apply (x : Matrix n n K) :
    piK x = x.trace • ((Fintype.card n : K)⁻¹ • (1 : Matrix n n K)) := rfl

theorem trace_conj (g : Matrix.GeneralLinearGroup n K) (x : Matrix n n K) :
    ((g : Matrix n n K) * x * ((g⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K)).trace = x.trace := by
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]

theorem piK_mem_adComm (G : Subgroup (Matrix.GeneralLinearGroup n K)) :
    (piK : Matrix n n K →ₗ[K] Matrix n n K) ∈ adComm G := by
  intro g _ x
  simp only [piK_apply, trace_conj, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Units.mul_inv]

theorem piK_eq_zero {x : Matrix n n K} (hx : x.trace = 0) : piK x = 0 := by
  rw [piK_apply, hx, zero_smul]

/-- `id - piK`, the projection onto `sl_n`. -/
def piSL : Matrix n n K →ₗ[K] Matrix n n K := LinearMap.id - piK

theorem piSL_apply (x : Matrix n n K) : piSL x = x - piK x := rfl

theorem piSL_mem_adComm (G : Subgroup (Matrix.GeneralLinearGroup n K)) :
    (piSL : Matrix n n K →ₗ[K] Matrix n n K) ∈ adComm G :=
  Submodule.sub_mem _ (id_mem_adComm G) (piK_mem_adComm G)

theorem piSL_of_trace {x : Matrix n n K} (hx : x.trace = 0) : piSL x = x := by
  rw [piSL_apply, piK_eq_zero hx, sub_zero]

variable [CharZero K]

theorem piK_one [Nonempty n] : piK (1 : Matrix n n K) = 1 := by
  rw [piK_apply, Matrix.trace_one, smul_smul,
    mul_inv_cancel₀ (Nat.cast_ne_zero.2 Fintype.card_ne_zero), one_smul]

theorem piSL_one [Nonempty n] : piSL (1 : Matrix n n K) = 0 := by
  rw [piSL_apply, piK_one, sub_self]

theorem trace_piK [Nonempty n] (x : Matrix n n K) : (piK x).trace = x.trace := by
  rw [piK_apply, Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_one, smul_eq_mul, smul_eq_mul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.2 Fintype.card_ne_zero), mul_one]

theorem trace_piSL [Nonempty n] (x : Matrix n n K) : (piSL x).trace = 0 := by
  rw [piSL_apply, Matrix.trace_sub, trace_piK, sub_self]

end PiK

end RamanujanPetersson.Larsen


