-- Prove2me | Definitions.Def_ChapterFiniteSectionSingleTime
-- name    : ChapterFiniteSectionSingleTime
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-11-08T20:32:09.219704+00:00
-- url     : https://prove2.me/theorems/26ed3ded-6138-4ffd-8cae-40c5159907e4
-- title:
--   Chapter ChapterFiniteSectionSingleTime
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.FiniteSectionSingleTime`, source chapter `BookProof/ChapterFiniteSectionSingleTime.lean`): Chapter ChapterFiniteSectionSingleTime
--
--   Generated def bundle for ChapterFiniteSectionSingleTime. See BookProof/ChapterFiniteSectionSingleTime.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterFiniteSectionSingleTime.lean

import Definitions.Def_ChapterSirkSingleTimeShift
import Theorems.Thm_BookProof_SirkSingleTime_strongResAt_of_ne_zero
import Theorems.Thm_BookProof_SirkSingleTime_singleTime_flow_tendsto_of_strongResAt
import Theorems.Thm_BookProof_SirkSingleTime_isShiftInvertC_neg_resCLM_shift
import Definitions.Def_ChapterQgTimeIndependentFlowPromoted
import Theorems.Thm_BookProof_QgTimeIndependent_eq_prop_of_isSchrodingerSolution
import Definitions.Def_ChapterSirkTrotterKatoGalerkin
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterQgTruncationResolvent
import Theorems.Thm_BookProof_QgTruncationResolvent_strongResolventConvergence_of_core
import Definitions.Def_ChapterStoneBridge
import Mathlib
import Theorems.Thm_BookProof_StoneBridge_exists_stone_flow_of_esa


/-!
# Finite sections: one shift, one finite time, for any essentially self-adjoint mode Hamiltonian

`BookProof.ChapterSirkSingleTimeShift` proves that the SIRK/Hashimoto algorithm needs no
discretization of time — it evaluates the propagator at a *single finite time* through the
**bounded** shift-invert resolvent `(A − iℓ)⁻¹` — and `BookProof.ChapterQgTimeIndependentFlow`
turns "the gauge-fixed Hamiltonian carries no time dependence" into theorems about the
propagator.  Both were instantiated for the quantum-gravity Hamiltonian, where the
approximation analysed is the mode truncation of `BookProof.ChapterQgTruncationResolvent`.

This module supplies the approximation scheme for the *other* two Hamiltonians of the
project — Navier–Stokes and quantum Yang–Mills — which live on an `ℓ²` mode space
`L2I ι = ℓ²(ι)` with the finite-mode core `lpFiniteModes ι`.  The scheme is the **finite
section** (Galerkin) truncation: the matrix of the Hamiltonian in the mode basis, restricted
to a finite window `W` of modes,

`H_W = P_W H P_W`,   `P_W y = Σ_{k ∈ W} ⟪e_k, y⟫ e_k`.

Each `H_W` is a *bounded* (finite-rank) self-adjoint operator, so it has a unique
self-adjoint realization and its shift-invert resolvent is computable; and as the window
exhausts the modes the finite sections converge to the exact Hamiltonian on the core, hence
in the strong resolvent sense, hence — by Trotter–Kato — in the propagator sense at every
single finite time.

## What is proved

* `projW`, `projW_apply_tendsto` — the mode projection and its strong convergence to the
  identity along an exhausting family of windows.
* `secOp`, `secOp_isSelfAdjoint` — the finite section is a bounded self-adjoint operator
  (symmetry of the Hamiltonian on the core is the only input).
* `secOp_tendsto_core` — on every core vector the finite sections converge to the exact
  Hamiltonian.
* **`finiteSection_singleTime`** — the package: for a symmetric, essentially self-adjoint
  mode Hamiltonian there is a self-adjoint realization `T` and self-adjoint realizations
  `S n` of the finite sections such that
  * the propagator `U(t,s) = e^{−i(t−s)H}` is unitary, satisfies Chapman–Kolmogorov, is
    **time-translation invariant** and **uniquely** solves the Schrödinger equation with the
    one fixed generator (no time ordering, no Dyson series);
  * at **every** nonzero shift `ℓ` the bounded Hashimoto shift-invert operators
    `−(· − iℓ)⁻¹` of the finite sections converge strongly to that of `T`;
  * hence at **every single finite time** `t` the finite-section propagators converge to the
    exact one — no step size, no number of steps, no time splitting.
* `windowOfEquiv`, `windowOfEquiv_exhausts` — an admissible family of windows exists on
  every countable mode set.

Everything is `sorry`-free and `axiom`-free.  The Navier–Stokes and Yang–Mills instances are
`BookProof.ChapterNsTimeIndependentFlow` and `BookProof.ChapterQymTimeIndependentFlow`.
-/

open scoped InnerProductSpace

namespace BookProof.FiniteSectionSingleTime

open Filter Topology
open BookProof.ChapterStoneResolvent BookProof.ChapterSirkTrotterKato
open BookProof.FarisLavine BookProof.EsaClosure BookProof.StoneBridge
open BookProof.QgTruncationResolvent BookProof.SirkSingleTime BookProof.QgTimeIndependent
open BookProof.HashimotoShiftInvert
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato

noncomputable section

variable {ι : Type*} [DecidableEq ι]

/-! ## 1. The mode basis and the mode projection -/

/-- The mode basis vector `e_k` of `ℓ²(ι)`. -/
def basisVec (k : ι) : L2I ι := lp.single 2 k (1 : ℂ)

/-- The mode basis vector, as an element of the finite-mode core. -/
def coreVec (k : ι) : lpFiniteModes ι := ⟨basisVec k, lpSingle_mem_lpFiniteModes k 1⟩

@[simp] theorem coreVec_coe (k : ι) : ((coreVec k : lpFiniteModes ι) : L2I ι) = basisVec k := rfl

theorem inner_basisVec (k : ι) (y : L2I ι) : (inner ℂ (basisVec k) y : ℂ) = (y : ι → ℂ) k := by
  rw [basisVec, lp.inner_single_left]
  simp

theorem inner_basisVec' (k : ι) (y : L2I ι) :
    (inner ℂ y (basisVec k) : ℂ) = (starRingEnd ℂ) ((y : ι → ℂ) k) := by
  rw [← inner_conj_symm, inner_basisVec]

theorem smul_basisVec (k : ι) (c : ℂ) : c • basisVec k = lp.single 2 k c := by
  rw [basisVec, ← lp.single_smul, smul_eq_mul, mul_one]

/-- The projection onto the modes in the finite window `W`. -/
def projW (W : Finset ι) : L2I ι →L[ℂ] L2I ι :=
  ∑ c ∈ W, (innerSL ℂ (basisVec c)).smulRight (basisVec c)

theorem projW_apply (W : Finset ι) (y : L2I ι) :
    projW W y = ∑ c ∈ W, ((y : ι → ℂ) c) • basisVec c := by
  simp [projW, inner_basisVec]

/-- The window family `W` **exhausts** the modes: every finite set of modes is eventually
contained in it. -/
def Exhausts (W : ℕ → Finset ι) : Prop := ∀ F : Finset ι, ∀ᶠ n in atTop, F ⊆ W n

/-- **The mode projections converge strongly to the identity** along an exhausting family of
windows. -/
theorem projW_apply_tendsto {W : ℕ → Finset ι} (hW : Exhausts W) (y : L2I ι) :
    Tendsto (fun n => projW (W n) y) atTop (𝓝 y) := by
  have hsum : HasSum (fun k : ι => lp.single 2 k ((y : ι → ℂ) k)) y :=
    lp.hasSum_single (by simp) y
  have hfin : Tendsto (fun F : Finset ι => ∑ c ∈ F, lp.single 2 c ((y : ι → ℂ) c))
      atTop (𝓝 y) := hsum
  have hWtop : Tendsto W atTop (atTop : Filter (Finset ι)) := by
    refine tendsto_atTop.2 fun F => ?_
    exact hW F
  have := hfin.comp hWtop
  refine this.congr fun n => ?_
  rw [projW_apply]
  exact Finset.sum_congr rfl fun c _ => (smul_basisVec c ((y : ι → ℂ) c)).symm

/-! ## 2. The finite section of a mode Hamiltonian -/

variable (H : lpFiniteModes ι →ₗ[ℂ] L2I ι)

/-- **The finite section** `P_W H P_W` of the mode Hamiltonian `H`: the matrix of `H` in the
mode basis, restricted to the window `W`.  It is a finite-rank, hence bounded, operator — it
is what a Galerkin/Krylov scheme actually computes with. -/
def secOp (W : Finset ι) : L2I ι →L[ℂ] L2I ι :=
  ∑ a ∈ W, (innerSL ℂ (basisVec a)).smulRight (projW W (H (coreVec a)))

theorem secOp_apply (W : Finset ι) (x : L2I ι) :
    secOp H W x = ∑ a ∈ W, ((x : ι → ℂ) a) • projW W (H (coreVec a)) := by
  simp [secOp, inner_basisVec]

/-- The finite section is **self-adjoint**: the matrix of a symmetric operator in an
orthonormal basis is Hermitian. -/
theorem secOp_isSelfAdjoint {W : Finset ι} (hsym : SymmetricOn (lpFiniteModes ι) H) :
    IsSelfAdjoint (secOp H W) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro x y
  simp only [ContinuousLinearMap.coe_coe]
  have hherm : ∀ a c : ι, (starRingEnd ℂ) (((H (coreVec a) : L2I ι) : ι → ℂ) c)
      = ((H (coreVec c) : L2I ι) : ι → ℂ) a := by
    intro a c
    have h := hsym (coreVec c) (coreVec a)
    have h1 : (inner ℂ (H (coreVec c)) (basisVec a) : ℂ)
        = (starRingEnd ℂ) (((H (coreVec c) : L2I ι) : ι → ℂ) a) := by
      rw [← inner_conj_symm, inner_basisVec]
    have h2 : (inner ℂ (basisVec c) (H (coreVec a)) : ℂ)
        = ((H (coreVec a) : L2I ι) : ι → ℂ) c := inner_basisVec _ _
    rw [coreVec_coe, coreVec_coe, h1, h2] at h
    rw [← h]
    simp
  have hexp : (inner ℂ (secOp H W x) y : ℂ)
      = ∑ a ∈ W, ∑ c ∈ W, (starRingEnd ℂ) ((x : ι → ℂ) a)
          * (starRingEnd ℂ) (((H (coreVec a) : L2I ι) : ι → ℂ) c) * ((y : ι → ℂ) c) := by
    rw [secOp_apply, sum_inner]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [inner_smul_left, projW_apply, sum_inner, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [inner_smul_left, inner_basisVec]
    ring
  have hexp2 : (inner ℂ x (secOp H W y) : ℂ)
      = ∑ a ∈ W, ∑ c ∈ W, (starRingEnd ℂ) ((x : ι → ℂ) c)
          * (((H (coreVec a) : L2I ι) : ι → ℂ) c) * ((y : ι → ℂ) a) := by
    rw [secOp_apply, inner_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [inner_smul_right, projW_apply, inner_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [inner_smul_right, inner_basisVec']
    ring
  have hcomm : ∑ a ∈ W, ∑ c ∈ W, (starRingEnd ℂ) ((x : ι → ℂ) c)
        * (((H (coreVec a) : L2I ι) : ι → ℂ) c) * ((y : ι → ℂ) a)
      = ∑ a ∈ W, ∑ c ∈ W, (starRingEnd ℂ) ((x : ι → ℂ) a)
        * (((H (coreVec c) : L2I ι) : ι → ℂ) a) * ((y : ι → ℂ) c) := Finset.sum_comm
  rw [hexp, hexp2, hcomm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
  rw [hherm a c]

/-! ## 3. The finite sections converge to the Hamiltonian on the core -/

/-- Every finite-mode vector is the finite sum of its modes. -/
theorem core_eq_sum (x : lpFiniteModes ι) :
    x = ∑ k ∈ (Set.Finite.toFinset (mem_lpFiniteModes.mp x.2)),
      (((x : L2I ι) : ι → ℂ) k) • coreVec k := by
  refine Subtype.ext ?_
  refine lp.ext ?_
  funext j
  classical
  set S := (Set.Finite.toFinset (mem_lpFiniteModes.mp x.2)) with hS
  have hcoe : ((∑ k ∈ S, (((x : L2I ι) : ι → ℂ) k) • coreVec k : lpFiniteModes ι) : L2I ι)
      = ∑ k ∈ S, (((x : L2I ι) : ι → ℂ) k) • basisVec k := by
    push_cast
    rfl
  rw [hcoe]
  have hfun : ((∑ k ∈ S, (((x : L2I ι) : ι → ℂ) k) • basisVec k : L2I ι) : ι → ℂ) j
      = ∑ k ∈ S, (((x : L2I ι) : ι → ℂ) k) * (if j = k then 1 else 0) := by
    rw [lp.coeFn_sum]
    simp only [Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, basisVec]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hjk : j = k
    · subst hjk; simp [lp.single_apply]
    · simp [lp.single_apply, hjk]
  rw [hfun]
  by_cases hj : j ∈ S
  · rw [Finset.sum_eq_single j]
    · simp
    · intro k _ hkj; simp [Ne.symm hkj]
    · intro h; exact absurd hj h
  · have hzero : ((x : L2I ι) : ι → ℂ) j = 0 := by
      by_contra hne
      exact hj (by simpa [hS, Set.Finite.mem_toFinset, Function.mem_support] using hne)
    rw [hzero]
    refine (Finset.sum_eq_zero fun k hk => ?_).symm
    by_cases hjk : j = k
    · exact absurd (hjk ▸ hk) hj
    · simp [hjk]

/-- On the mode basis vectors the finite sections converge to the Hamiltonian. -/
theorem secOp_tendsto_basis {W : ℕ → Finset ι} (hW : Exhausts W) (k : ι) :
    Tendsto (fun n => secOp H (W n) (basisVec k)) atTop (𝓝 (H (coreVec k))) := by
  have heq : (fun n => secOp H (W n) (basisVec k))
      =ᶠ[atTop] fun n => projW (W n) (H (coreVec k)) := by
    filter_upwards [hW {k}] with n hn
    have hk : k ∈ W n := hn (Finset.mem_singleton_self k)
    rw [secOp_apply]
    rw [Finset.sum_eq_single k]
    · simp [basisVec, lp.single_apply]
    · intro b _ hbk
      have hb0 : ((basisVec k : L2I ι) : ι → ℂ) b = 0 := by
        simp [basisVec, lp.single_apply, hbk]
      simp [hb0]
    · intro h; exact absurd hk h
  exact Tendsto.congr' heq.symm (projW_apply_tendsto hW (H (coreVec k)))

/-- **The finite sections converge to the Hamiltonian on the whole finite-mode core.** -/
theorem secOp_tendsto_core {W : ℕ → Finset ι} (hW : Exhausts W) (x : lpFiniteModes ι) :
    Tendsto (fun n => secOp H (W n) ((x : L2I ι))) atTop (𝓝 (H x)) := by
  classical
  set S := (Set.Finite.toFinset (mem_lpFiniteModes.mp x.2)) with hS
  have hx := core_eq_sum x
  have hlhs : ∀ n, secOp H (W n) ((x : L2I ι))
      = ∑ k ∈ S, (((x : L2I ι) : ι → ℂ) k) • secOp H (W n) (basisVec k) := by
    intro n
    conv_lhs => rw [hx]
    push_cast
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul]
    rfl
  have hrhs : H x = ∑ k ∈ S, (((x : L2I ι) : ι → ℂ) k) • H (coreVec k) := by
    conv_lhs => rw [hx]
    rw [map_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [map_smul]
  rw [hrhs]
  simp only [hlhs]
  exact tendsto_finset_sum _ fun k _ =>
    (secOp_tendsto_basis H hW k).const_smul (((x : L2I ι) : ι → ℂ) k)

/-! ## 4. Bounded self-adjoint operators as self-adjoint extensions -/

/-- A bounded self-adjoint operator is a self-adjoint extension of its own restriction to any
subspace. -/
theorem isSelfAdjointExtension_ofBounded {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] [CompleteSpace F] (A : F →L[ℂ] F) (hA : IsSelfAdjoint A)
    (D : Submodule ℂ F) :
    IsSelfAdjointExtension ((A : F →ₗ[ℂ] F).comp D.subtype) (ofBounded A hA).op := by
  have hsymm := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hA
  refine ⟨fun x => ⟨Submodule.mem_top, rfl⟩, fun x y => hsymm _ _, ?_⟩
  intro w u hwu
  refine ⟨Submodule.mem_top, ?_⟩
  have hall : ∀ v : F, (inner ℂ v (A w) : ℂ) = inner ℂ v u := by
    intro v
    have h : (inner ℂ (A v) w : ℂ) = inner ℂ v u := hwu ⟨v, Submodule.mem_top⟩
    rw [← h]
    exact (hsymm v w).symm
  have hzero : ∀ v : F, (inner ℂ v (A w - u) : ℂ) = 0 := by
    intro v; rw [inner_sub_right, hall v]; ring
  have hsub : A w - u = 0 := by
    have h0 := hzero (A w - u)
    simpa using inner_self_eq_zero.mp h0
  exact sub_eq_zero.mp hsub

/-! ## 5. The package: one shift, one finite time, no time dependence -/

/-- **The finite-section scheme needs no discretization of time.**

Let `H` be a symmetric, essentially self-adjoint Hamiltonian on the finite-mode core of
`ℓ²(ι)`, and let `W n` be an exhausting family of finite mode windows.  Then there are a
self-adjoint realization `T` of `H` and self-adjoint realizations `S n` of the finite
sections `P_{W n} H P_{W n}` such that

* the propagator `U(t,s) = e^{−i(t−s)H}` of the **one fixed** generator is unitary, satisfies
  Chapman–Kolmogorov, is invariant under a common shift of both times, and is the *unique*
  solution operator of the Schrödinger equation — there is no time ordering and no Dyson
  series;
* at **every** nonzero shift `ℓ` the Hashimoto shift-invert operators of the finite sections
  converge strongly to that of `T` — the choice of shift is immaterial, and each of these
  operators is bounded (by `1/|ℓ|`) even though `H` is not;
* hence at **every single finite time** `t` the finite-section propagators converge to the
  exact one.  No step size, number of steps or time splitting appears. -/
theorem finiteSection_singleTime (hsym : SymmetricOn (lpFiniteModes ι) H)
    (hesa : EssentiallySelfAdjointOn (lpFiniteModes ι) H)
    {W : ℕ → Finset ι} (hW : Exhausts W) :
    ∃ (T : UnboundedSelfAdjoint (L2I ι)) (S : ℕ → UnboundedSelfAdjoint (L2I ι)),
      IsSelfAdjointExtension H T.op ∧
        (∀ n, IsSelfAdjointExtension
          (((secOp H (W n) : L2I ι →ₗ[ℂ] L2I ι)).comp (lpFiniteModes ι).subtype) (S n).op) ∧
        (∀ t s : ℝ, prop T t s = T.stoneU (t - s)) ∧
        (∀ (t s : ℝ) (x : L2I ι), ‖prop T t s x‖ = ‖x‖) ∧
        (∀ (t s r : ℝ) (x : L2I ι), prop T t s (prop T s r x) = prop T t r x) ∧
        (∀ t s h : ℝ, prop T (t + h) (s + h) = prop T t s) ∧
        (∀ y : ℝ → L2I ι, IsSchrodingerSolution T y → ∀ t s : ℝ, y t = prop T t s (y s)) ∧
        (∀ l : ℝ, l ≠ 0 →
          IsShiftInvertC T.op (((l : ℝ) : ℂ) * Complex.I) (-(T.resCLM l)) ∧
            (∀ n, IsShiftInvertC (S n).op (((l : ℝ) : ℂ) * Complex.I) (-((S n).resCLM l))) ∧
            ∀ u : L2I ι,
              Tendsto (fun n => -((S n).resCLM l u)) atTop (𝓝 (-(T.resCLM l u)))) ∧
        ∀ (v : L2I ι) (t : ℝ), Tendsto (fun n => (S n).stoneU t v) atTop (𝓝 (T.stoneU t v)) := by
  obtain ⟨T, _U, hT, _hflow⟩ :=
    exists_stone_flow_of_esa H lpFiniteModes_dense hsym hesa
  set S : ℕ → UnboundedSelfAdjoint (L2I ι) :=
    fun n => ofBounded (secOp H (W n)) (secOp_isSelfAdjoint H hsym) with hSdef
  have hS : ∀ n, IsSelfAdjointExtension
      (((secOp H (W n) : L2I ι →ₗ[ℂ] L2I ι)).comp (lpFiniteModes ι).subtype) (S n).op :=
    fun n => isSelfAdjointExtension_ofBounded _ _ _
  have hconv : ∀ x : lpFiniteModes ι,
      Tendsto (fun n => ((secOp H (W n) : L2I ι →ₗ[ℂ] L2I ι)).comp
        (lpFiniteModes ι).subtype x) atTop (𝓝 (H x)) := by
    intro x
    exact secOp_tendsto_core H hW x
  have hsrc : StrongResolventConvergence T S :=
    strongResolventConvergence_of_core hesa hT hS hconv
  have hres1 : StrongResAt T S 1 := fun y => hsrc y
  refine ⟨T, S, hT, hS, fun t s => rfl, fun t s x => norm_prop_apply T t s x,
    fun t s r x => prop_apply_prop T t s r x, fun t s h => prop_time_translation T t s h,
    fun _ hy t s => eq_prop_of_isSchrodingerSolution T hy t s,
    fun l hl => ⟨isShiftInvertC_neg_resCLM_shift T hl,
      fun n => isShiftInvertC_neg_resCLM_shift (S n) hl,
      fun u => (strongResAt_of_ne_zero one_ne_zero hl hres1 u).neg⟩,
    fun v t => singleTime_flow_tendsto_of_strongResAt one_ne_zero hres1 v t⟩

/-! ## 6. The propagator of a *selected* self-adjoint extension -/

/-- **A selected self-adjoint extension already carries the whole time-independent evolution
package.**  Whatever selects the extension — essential self-adjointness, or the Friedrichs
construction for a positive Hamiltonian — the resulting generator is a single fixed
self-adjoint operator, so its propagator `U(t,s) = e^{−i(t−s)H}` is unitary, satisfies
Chapman–Kolmogorov, depends on the two times only through their difference and uniquely
solves the Schrödinger equation.  No time ordering and no Dyson series occurs, and the whole
evolution problem is the evaluation of one unitary group at one finite time. -/
theorem timeIndependent_of_selfAdjointExtension {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] [CompleteSpace F] {D Dom : Submodule ℂ F} {Hc : D →ₗ[ℂ] F}
    {A : Dom →ₗ[ℂ] F} (hdense : Dense ((D : Submodule ℂ F) : Set F))
    (h : IsSelfAdjointExtension Hc A) :
    ∃ T : UnboundedSelfAdjoint F,
      IsSelfAdjointExtension Hc T.op ∧
        (∀ t s : ℝ, prop T t s = T.stoneU (t - s)) ∧
        (∀ (t s : ℝ) (x : F), ‖prop T t s x‖ = ‖x‖) ∧
        (∀ (t s r : ℝ) (x : F), prop T t s (prop T s r x) = prop T t r x) ∧
        (∀ t s u : ℝ, prop T (t + u) (s + u) = prop T t s) ∧
        (∀ y : ℝ → F, IsSchrodingerSolution T y → ∀ t s : ℝ, y t = prop T t s (y s)) :=
  ⟨unboundedSelfAdjointOf hdense h, h, fun _ _ => rfl,
    fun t s x => norm_prop_apply _ t s x, fun t s r x => prop_apply_prop _ t s r x,
    fun t s u => prop_time_translation _ t s u,
    fun _ hy t s => eq_prop_of_isSchrodingerSolution _ hy t s⟩

/-! ## 7. Admissible windows exist on every countable mode set -/

/-- The windows produced by an enumeration of the modes. -/
def windowOfEquiv (en : ℕ ≃ ι) (n : ℕ) : Finset ι := (Finset.range n).image en

theorem windowOfEquiv_exhausts (en : ℕ ≃ ι) : Exhausts (windowOfEquiv en) := by
  classical
  intro F
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ k ∈ F, en.symm k < N := by
    refine ⟨(F.image en.symm).sup id + 1, fun k hk => ?_⟩
    have : en.symm k ≤ (F.image en.symm).sup id :=
      Finset.le_sup (f := id) (Finset.mem_image_of_mem _ hk)
    omega
  filter_upwards [eventually_ge_atTop N] with n hn
  intro k hk
  refine Finset.mem_image.mpr ⟨en.symm k, ?_, by simp⟩
  exact Finset.mem_range.mpr (lt_of_lt_of_le (hN k hk) hn)

end

end BookProof.FiniteSectionSingleTime


