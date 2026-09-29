-- Prove2me | Definitions.Def_ChapterFockSecondQuantization
-- name    : ChapterFockSecondQuantization
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-10T10:49:52.739972+00:00
-- url     : https://prove2.me/theorems/4c01010a-b6ed-47c7-ba00-243989b121b1
-- title:
--   `PLAN_LEAN_SPECIALIST_QYM_FLOW.md` Part F.11 asks for the **second-quantized** Hamiltonian on the finite-occupation stat ...
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.FockSecondQuantization`, source chapter `BookProof/ChapterFockSecondQuantization.lean`).
--
--   `PLAN_LEAN_SPECIALIST_QYM_FLOW.md` Part F.11 asks for the **second-quantized** Hamiltonian on the finite-occupation states over the one-particle core, i.e. the last row of the field-space realization of the gauge-fixed Yang–Mills Hamiltonian.
--
--   The Fock space over a one-particle space with a countable orthonormal basis `(e_k)` is `ℓ²` over the *configurations* `Conf = ℕ →₀ ℕ` (occupation numbers, finitely many excited modes), and the finite-occupation domain is the dense subspace `lpFiniteModes Conf` of finitely supported configuration vectors. All operators are defined at the *algebraic* level on `FockAlg = Conf →₀ ℂ` — where linearity is free — and transported to the Hilbert space by the isomorphism `fockEquiv`.
--
--   * `up`, `dn` — adding and removing one quantum in a mode; * `annA j`, `creA j` — annihilation and creation, with the canonical commutation relation `[a_j, a_j†] = 1` (`ccr_annA_creA`) and the adjoint pairing `⟪a_j† u, v⟫ = ⟪u, a_j v⟫` (`inner_creA_left`); * `dGamma col` — the second quantization `dΓ(A) = Σ_{j,k} ⟪e_j, A e_k⟫ a_j† a_k` of a one-particle operator given by its (column-finite) matrix `col`, and `dGamma_one_particle`, which checks that on the one-particle sector it *is* the one-particle operator; * `dGammaOp_symmetricOn`, `dGammaOp_quadForm_nonneg` — symmetry and positivity of `dΓ(A)` on the finite-occupation domain, from Hermiticity and positivity of the one-particle matrix; * `dGamma_friedrichs_extension` — hence `dΓ(A)` has a positive self-adjoint (Friedrichs) extension; * `secondQuantization_friedrichs` — the same for the matrix of an arbitrary symmetric positive one-particle operator on the finite-mode domain of a Hilbert basis; * `ym_fock_friedrichs_extension` — **F.11**: the second quantization of the field-space Yang–Mills Hamiltonian `H₁ = ½Σπ² + ½ΣB²` of `BookProof.YangMillsHermite` has a positive self-adjoint extension on the Fock space over the Gauss–polynomial core of `L²(ℝ⁹⁹)`; * `dGamma_hashimoto_selects`, `secondQuantization_hashimoto_selects` and `ym_fock_hashimoto_selects` — the Hashimoto/SIRK shift-invert limit selects exactly that Friedrichs extension, with the Galerkin truncations of the shift-inverted operator converging strongly and in the resolvent sense.
--
--   No mass gap and no global existence is claimed; the Millennium problem stays out of scope.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterFockSecondQuantization.lean

import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterYangMillsHermite
import Mathlib

import Mathlib

/-!
# Second quantization over a one-particle core (Part F.11)

`PLAN_LEAN_SPECIALIST_QYM_FLOW.md` Part F.11 asks for the **second-quantized**
Hamiltonian on the finite-occupation states over the one-particle core, i.e. the
last row of the field-space realization of the gauge-fixed Yang–Mills
Hamiltonian.

The Fock space over a one-particle space with a countable orthonormal basis
`(e_k)` is `ℓ²` over the *configurations* `Conf = ℕ →₀ ℕ` (occupation numbers,
finitely many excited modes), and the finite-occupation domain is the dense
subspace `lpFiniteModes Conf` of finitely supported configuration vectors.  All
operators are defined at the *algebraic* level on `FockAlg = Conf →₀ ℂ` — where
linearity is free — and transported to the Hilbert space by the isomorphism
`fockEquiv`.

* `up`, `dn` — adding and removing one quantum in a mode;
* `annA j`, `creA j` — annihilation and creation, with the canonical commutation
  relation `[a_j, a_j†] = 1` (`ccr_annA_creA`) and the adjoint pairing
  `⟪a_j† u, v⟫ = ⟪u, a_j v⟫` (`inner_creA_left`);
* `dGamma col` — the second quantization `dΓ(A) = Σ_{j,k} ⟪e_j, A e_k⟫ a_j† a_k`
  of a one-particle operator given by its (column-finite) matrix `col`, and
  `dGamma_one_particle`, which checks that on the one-particle sector it *is*
  the one-particle operator;
* `dGammaOp_symmetricOn`, `dGammaOp_quadForm_nonneg` — symmetry and positivity of
  `dΓ(A)` on the finite-occupation domain, from Hermiticity and positivity of the
  one-particle matrix;
* `dGamma_friedrichs_extension` — hence `dΓ(A)` has a positive self-adjoint
  (Friedrichs) extension;
* `secondQuantization_friedrichs` — the same for the matrix of an arbitrary
  symmetric positive one-particle operator on the finite-mode domain of a Hilbert
  basis;
* `ym_fock_friedrichs_extension` — **F.11**: the second quantization of the
  field-space Yang–Mills Hamiltonian `H₁ = ½Σπ² + ½ΣB²` of
  `BookProof.YangMillsHermite` has a positive self-adjoint extension on the Fock
  space over the Gauss–polynomial core of `L²(ℝ⁹⁹)`;
* `dGamma_hashimoto_selects`, `secondQuantization_hashimoto_selects` and
  `ym_fock_hashimoto_selects` — the Hashimoto/SIRK shift-invert limit selects
  exactly that Friedrichs extension, with the Galerkin truncations of the
  shift-inverted operator converging strongly and in the resolvent sense.

No mass gap and no global existence is claimed; the Millennium problem stays out
of scope.
-/

namespace BookProof.FockSecondQuantization

open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension
open BookProof.HashimotoShiftInvert

noncomputable section

/-! ## Configurations -/

/-- A **configuration**: the occupation numbers of the one-particle modes, all
but finitely many of them zero. -/
abbrev Conf := ℕ →₀ ℕ

/-- The **algebraic Fock space**: finite linear combinations of configurations. -/
abbrev FockAlg := Conf →₀ ℂ

/-- The **Fock space** `ℓ²(Conf)`. -/
abbrev Fock := L2I Conf

/-- Add one quantum in the mode `j`. -/
def up (j : ℕ) (α : Conf) : Conf := Finsupp.update α j (α j + 1)

/-- Remove one quantum from the mode `j` (nothing happens if the mode is
empty). -/
def dn (j : ℕ) (α : Conf) : Conf := Finsupp.update α j (α j - 1)



















/-! ## Annihilation and creation at the algebraic level -/

/-- **The annihilation operator of the mode `j`**: on a configuration state,
`a_j |β⟩ = √(β_j) |β − e_j⟩`. -/
def annA (j : ℕ) : FockAlg →ₗ[ℂ] FockAlg :=
  Finsupp.lsum ℂ fun β => LinearMap.toSpanSingleton ℂ FockAlg
    (Finsupp.single (dn j β) ((Real.sqrt (β j) : ℝ) : ℂ))

/-- **The creation operator of the mode `j`**: on a configuration state,
`a_j† |β⟩ = √(β_j + 1) |β + e_j⟩`. -/
def creA (j : ℕ) : FockAlg →ₗ[ℂ] FockAlg :=
  Finsupp.lsum ℂ fun β => LinearMap.toSpanSingleton ℂ FockAlg
    (Finsupp.single (up j β) ((Real.sqrt ((β j : ℝ) + 1) : ℝ) : ℂ))



























/-- The set of modes excited by a state of the algebraic Fock space. -/
def modes (u : FockAlg) : Finset ℕ := u.support.biUnion Finsupp.support





/-! ## Transport to `ℓ²(Conf)` -/

/-- A finitely supported configuration vector as an element of `ℓ²(Conf)`. -/
def toLp (u : FockAlg) : Fock :=
  ⟨fun α => u α, memLpTwo_of_finite_support u.finite_support⟩



/-- The transport map is linear. -/
def toLpL : FockAlg →ₗ[ℂ] Fock where
  toFun := toLp
  map_add' u v := by
    refine lp.ext (funext fun α => ?_)
    change u α + v α = u α + v α
    rfl
  map_smul' c u := by
    refine lp.ext (funext fun α => ?_)
    change (c • u) α = c • u α
    rfl



theorem toLp_mem (u : FockAlg) : toLp u ∈ lpFiniteModes Conf := u.finite_support

theorem toLp_injective : Function.Injective toLp := by
  intro u v h
  refine Finsupp.ext fun α => ?_
  have := congrArg (fun f : Fock => (f : Conf → ℂ) α) h
  change (toLp u : Conf → ℂ) α = (toLp v : Conf → ℂ) α at this
  simpa [toLp] using this









/-- The isomorphism of the algebraic Fock space with the finite-occupation
domain of `ℓ²(Conf)`. -/
def fockEquiv : FockAlg ≃ₗ[ℂ] lpFiniteModes Conf := by
  classical
  refine LinearEquiv.ofBijective (toLpL.codRestrict (lpFiniteModes Conf) toLp_mem) ⟨?_, ?_⟩
  · intro u v h
    exact toLp_injective (congrArg Subtype.val h)
  · rintro ⟨x, hx⟩
    refine ⟨Finsupp.onFinset hx.toFinset (fun α => (x : Conf → ℂ) α) ?_, ?_⟩
    · intro α hα
      exact hx.mem_toFinset.mpr hα
    · refine Subtype.ext (lp.ext (funext fun α => ?_))
      rfl





/-! ## Second quantization -/

/-- The creation operator of a finitely supported one-particle vector
`v = Σ_j v_j e_j`: `a†(v) = Σ_j v_j a_j†`. -/
def creVec (v : ℕ →₀ ℂ) : FockAlg →ₗ[ℂ] FockAlg := ∑ j ∈ v.support, (v j) • creA j

/-- **The second quantization** `dΓ(A) = Σ_k a†(A e_k) a_k` of the one-particle
operator whose `k`-th column of matrix elements is `col k` (so
`(col k) j = ⟪e_j, A e_k⟫`). -/
def dGamma (col : ℕ → (ℕ →₀ ℂ)) : FockAlg →ₗ[ℂ] FockAlg :=
  Finsupp.lsum ℂ fun β => LinearMap.toSpanSingleton ℂ FockAlg
    (∑ k ∈ β.support, creVec (col k) (annA k (Finsupp.single β 1)))













/-! ### Symmetry and positivity -/

/-- The matrix is **Hermitian**: `⟪e_j, A e_k⟫ = conj ⟪e_k, A e_j⟫`. -/
def IsHermCol (col : ℕ → (ℕ →₀ ℂ)) : Prop :=
  ∀ j k, (col j) k = (starRingEnd ℂ) ((col k) j)

/-- The matrix is **positive semidefinite** on every finite set of modes. -/
def IsPosCol (col : ℕ → (ℕ →₀ ℂ)) : Prop :=
  ∀ (S : Finset ℕ) (c : ℕ → ℂ),
    0 ≤ (∑ j ∈ S, ∑ k ∈ S, (starRingEnd ℂ) (c j) * (col k) j * c k).re











/-- A finite set of modes large enough for both states and for the columns of
the one-particle matrix over their modes. -/
def closureModes (col : ℕ → (ℕ →₀ ℂ)) (u v : FockAlg) : Finset ℕ :=
  (modes u ∪ modes v) ∪ (modes u ∪ modes v).biUnion fun k => (col k).support











/-! ### The second-quantized operator on the finite-occupation domain -/

/-- **The second-quantized operator** on the finite-occupation domain of the Fock
space. -/
def dGammaOp (col : ℕ → (ℕ →₀ ℂ)) : lpFiniteModes Conf →ₗ[ℂ] Fock :=
  (lpFiniteModes Conf).subtype.comp (fockEquiv.conj (dGamma col))











/-! ## The matrix of a one-particle operator -/

section OneParticle

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- The coordinates of a finite-mode vector, as a finitely supported function. -/
def coordFinsupp (b : HilbertBasis ℕ ℂ F) (x : F) : ℕ →₀ ℂ := by
  classical
  exact if h : x ∈ finiteModeDomain b then
    (Finsupp.mem_span_range_iff_exists_finsupp.mp h).choose else 0



/-- The matrix of a one-particle operator in the basis `b`. -/
def opCol (b : HilbertBasis ℕ ℂ F) (A : finiteModeDomain b →ₗ[ℂ] finiteModeDomain b)
    (k : ℕ) : ℕ →₀ ℂ :=
  coordFinsupp b (A ⟨b k, Submodule.subset_span ⟨k, rfl⟩⟩ : finiteModeDomain b)









end OneParticle

/-! ## The Hashimoto/SIRK selection for the second-quantized operator -/

section Selection

open Filter Topology

/-- The canonical Hilbert basis of the Fock space, indexed by the
configurations. -/
def fockConfBasis : HilbertBasis Conf ℂ Fock :=
  HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)

theorem fockConfBasis_apply (α : Conf) : fockConfBasis α = lp.single 2 α (1 : ℂ) := by
  rw [← HilbertBasis.repr_symm_single]
  rfl

/-- The Fock basis re-indexed by `ℕ`, the form in which the abstract Friedrichs
and Hashimoto theorems are stated. -/
def fockBasisN (ε : ℕ ≃ Conf) : HilbertBasis ℕ ℂ Fock :=
  HilbertBasis.mk (fockConfBasis.orthonormal.comp _ ε.injective)
    (by
      have h := fockConfBasis.dense_span
      rw [Set.range_comp, ε.range_eq_univ, Set.image_univ]
      exact h.ge)

theorem fockBasisN_apply (ε : ℕ ≃ Conf) (n : ℕ) :
    fockBasisN ε n = lp.single 2 (ε n) (1 : ℂ) := by
  rw [fockBasisN, HilbertBasis.coe_mk]
  exact fockConfBasis_apply _

theorem lp_sum_single_coord (S : Finset Conf) (f : Conf → ℂ) (β : Conf) :
    (((∑ α ∈ S, f α • lp.single 2 α (1 : ℂ)) : Fock) : Conf → ℂ) β
      = if β ∈ S then f β else 0 := by
  classical
  induction S using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    simp only [lp.coeFn_add, Pi.add_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
      lp.single_apply, ih]
    by_cases hb : β = a
    · subst hb
      simp [ha]
    · simp [hb, Finset.mem_insert]

/-- **The finite-mode domain of the Fock basis is exactly the finite-occupation
domain**, so the abstract theorems apply verbatim to `dΓ`. -/
theorem finiteModeDomain_fockBasisN (ε : ℕ ≃ Conf) :
    finiteModeDomain (fockBasisN ε) = lpFiniteModes Conf := by
  classical
  refine le_antisymm (Submodule.span_le.mpr ?_) fun x hx => ?_
  · rintro y ⟨n, rfl⟩
    rw [fockBasisN_apply]
    exact lpSingle_mem_lpFiniteModes _ _
  · set S : Finset Conf := hx.toFinset with hS
    have hxeq : x = ∑ α ∈ S, ((x : Conf → ℂ) α) • lp.single 2 α (1 : ℂ) := by
      refine lp.ext (funext fun β => ?_)
      rw [lp_sum_single_coord]
      by_cases hb : β ∈ S
      · simp [hb]
      · have hz : (x : Conf → ℂ) β = 0 := by
          by_contra hc
          exact hb (hx.mem_toFinset.mpr hc)
        simp [hb, hz]
    rw [hxeq]
    refine Submodule.sum_mem _ fun α _ => Submodule.smul_mem _ _ ?_
    refine Submodule.subset_span ⟨ε.symm α, ?_⟩
    rw [fockBasisN_apply, Equiv.apply_symm_apply]

/-- The second-quantized operator on the finite-mode domain of `fockBasisN ε`
(the same subspace as `lpFiniteModes Conf`). -/
def dGammaOpB (ε : ℕ ≃ Conf) (col : ℕ → (ℕ →₀ ℂ)) :
    finiteModeDomain (fockBasisN ε) →ₗ[ℂ] Fock :=
  (dGammaOp col).comp (LinearEquiv.ofEq _ _ (finiteModeDomain_fockBasisN ε)).toLinearMap







/-- A concrete enumeration of the configurations, so that the selection theorem
is not vacuous. -/
def fockEnum : ℕ ≃ Conf :=
  letI : Denumerable Conf := Denumerable.ofEncodableOfInfinite _
  (Denumerable.eqv Conf).symm



end Selection

/-! ## The second-quantized Yang–Mills Hamiltonian (F.11) -/

section YangMills

open BookProof.YangMillsHermite BookProof.HermiteProductCore
open Filter Topology

/-- The inner one-particle Yang–Mills Hamiltonian `H₁ = ½Σπ² + ½ΣB²` as an
endomorphism of the Gauss–polynomial core. The full final nested-Fock
Hamiltonian is its outer creation-left/annihilation-right enclosure; inner
pair terms are retained in `H₁`, and the outer annihilator kills the outer
vacuum.  The operator is realized as the finite-mode domain of
the orthonormal basis `coreBasis e` of `L²(ℝ⁹⁹)`. -/
def ymOnePart (e : ℕ ≃ (Fin 99 →₀ ℕ)) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) :
    finiteModeDomain (coreBasis e) →ₗ[ℂ] finiteModeDomain (coreBasis e) :=
  weylOpDom (piOps (coreRepBasis e)) (magOps (coreRepBasis e) fabc)



/-- The matrix of the one-particle Yang–Mills Hamiltonian in the product Hermite
basis. -/
def ymFockCol (e : ℕ ≃ (Fin 99 →₀ ℕ)) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) : ℕ → (ℕ →₀ ℂ) :=
  opCol (coreBasis e) (ymOnePart e fabc)







end YangMills

end

end BookProof.FockSecondQuantization


