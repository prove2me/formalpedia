-- Prove2me | Definitions.Def_ChapterCoreBoundsEsa
-- name    : ChapterCoreBoundsEsa
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-17T12:36:55.082728+00:00
-- url     : https://prove2.me/theorems/023e96f8-6b2e-4e75-9848-e95ebea499ea
-- title:
--   ChapterCoreBoundsEsa
-- statement:
--   ChapterCoreBoundsEsa

import Theorems.Thm_BookProof_NavierStokesFlow_IkebeKato_sum_single_mem_finiteModes

import Theorems.Thm_BookProof_NavierStokesFlow_IkebeKato_coe_sum_single
import Theorems.Thm_BookProof_OperatorSeries_commForm_eq_neg_two_im
import Theorems.Thm_BookProof_OperatorSeries_essentiallySelfAdjointOn_finiteModes_of_bounds




import Definitions.Def_ChapterOperatorSeriesEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Mathlib


/-!
# Faris–Lavine bounds checked on the finite-mode core alone

`BookProof.NavierStokesFlow.IkebeKato.essentiallySelfAdjointOn_finiteModes_of_farisLavine_bounds`
and its repackaging `BookProof.OperatorSeries.essentiallySelfAdjointOn_finiteModes_of_bounds`
ask for an operator defined on the **maximal domain** `maxDom c` of the comparison symbol,
and for the relative bound and the commutator bound to hold there.  Many second-quantized
Hamiltonians, however, are naturally given only on the **finite-mode core**
`lpFiniteModes ι` — the algebraic span of the basis states — where every sum in sight is
finite and no convergence question arises.

This module removes that mismatch once and for all: an operator on the core with a
relative bound against the comparison operator extends, by continuity along the
truncations, to the maximal domain, and the extension inherits the symmetry, the relative
bound and the commutator bound.  Hence:

* `trunc`, `trunc_coe`, `tendsto_trunc`, `tendsto_diag_trunc` — the truncation net of a
  state of the maximal domain and its convergence, in the norm and in the graph norm.
* `coreExt` — the extension of a core operator to `maxDom c`, with
  `tendsto_coreExt`, `coreExt_core` (it *is* the given operator on the core),
  `norm_coreExt_le`, `coreExt_symmetricOn` and `coreExt_commForm_le`.
* **`essentiallySelfAdjointOn_finiteModes_of_core_bounds`** — the instrument: a symmetric
  operator on the finite-mode core with a relative bound `‖H u‖ ≤ A‖N u‖` and a commutator
  bound `|⟪u, i[H, N]u⟫| ≤ B⟪u, N u⟫`, both checked **on the core only**, is essentially
  self-adjoint on that core.
* `essentiallySelfAdjointOn_finiteModes_of_core_bounds_comm` — the special case of a
  vanishing commutator form, the one a number-conserving Hamiltonian satisfies.

Everything is `sorry`-free and `axiom`-free.
-/

namespace BookProof.CoreBounds

open BookProof.FarisLavine BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.OperatorSeries
open Filter Topology

noncomputable section

variable {ι : Type*} {c : ι → ℝ}

/-! ## 1. The truncation net -/

/-- The inclusion of the finite-mode core into the maximal domain of the symbol `c`. -/
def inclC (c : ι → ℝ) : lpFiniteModes ι →ₗ[ℂ] maxDom c :=
  Submodule.inclusion (finiteModes_le_maxDom c)

@[simp] theorem inclC_coe (c : ι → ℝ) (u : lpFiniteModes ι) :
    ((inclC c u : maxDom c) : L2I ι) = (u : L2I ι) := rfl

/-- The **truncation** of a state to the finite set `S` of modes, as an element of the
finite-mode core. -/
def trunc [DecidableEq ι] (c : ι → ℝ) (x : maxDom c) (S : Finset ι) : lpFiniteModes ι :=
  ⟨∑ i ∈ S, lp.single 2 i (((x : L2I ι) : ι → ℂ) i), sum_single_mem_finiteModes S _⟩

theorem trunc_coe [DecidableEq ι] (c : ι → ℝ) (x : maxDom c) (S : Finset ι) (k : ι) :
    ((trunc c x S : lpFiniteModes ι) : L2I ι) k =
      if k ∈ S then ((x : L2I ι) : ι → ℂ) k else 0 := by
  classical
  show ((∑ i ∈ S, lp.single 2 i (((x : L2I ι) : ι → ℂ) i) : L2I ι) : ι → ℂ) k
    = if k ∈ S then ((x : L2I ι) : ι → ℂ) k else 0
  exact coe_sum_single S _ k

theorem trunc_add [DecidableEq ι] (c : ι → ℝ) (x y : maxDom c) (S : Finset ι) :
    trunc c (x + y) S = trunc c x S + trunc c y S := by
  ext k
  have hx := trunc_coe c x S k
  have hy := trunc_coe c y S k
  have hxy := trunc_coe c (x + y) S k
  by_cases hk : k ∈ S <;> simp [hxy, hx, hy, hk]

theorem trunc_smul [DecidableEq ι] (c : ι → ℝ) (a : ℂ) (x : maxDom c) (S : Finset ι) :
    trunc c (a • x) S = a • trunc c x S := by
  ext k
  have hx := trunc_coe c x S k
  have hax := trunc_coe c (a • x) S k
  by_cases hk : k ∈ S <;> simp [hax, hx, hk]

/-- The truncations converge to the state in `ℓ²`. -/
theorem tendsto_trunc [DecidableEq ι] (c : ι → ℝ) (x : maxDom c) :
    Tendsto (fun S : Finset ι => ((trunc c x S : lpFiniteModes ι) : L2I ι)) atTop
      (𝓝 ((x : L2I ι))) := by
  classical
  have h : HasSum (fun i : ι => lp.single 2 i (((x : L2I ι) : ι → ℂ) i)) ((x : L2I ι)) :=
    lp.hasSum_single (by norm_num) _
  simp [trunc]
  exact h

/-- The truncations converge in the graph norm of the comparison operator. -/
theorem tendsto_diag_trunc [DecidableEq ι] (c : ι → ℝ) (x : maxDom c) :
    Tendsto (fun S : Finset ι => (diagMax c (inclC c (trunc c x S)) : L2I ι)) atTop
      (𝓝 ((diagMax c x : L2I ι))) := by
  classical
  set v : ι → ℂ := fun k => ((diagMax c x : L2I ι) : ι → ℂ) k with hv
  have h : HasSum (fun i : ι => lp.single 2 i (v i)) ((diagMax c x : L2I ι)) :=
    lp.hasSum_single (by norm_num) _
  have heq : ∀ S : Finset ι, (diagMax c (inclC c (trunc c x S)) : L2I ι)
      = ∑ i ∈ S, lp.single 2 i (v i) := by
    intro S
    refine lp.ext (funext fun k => ?_)
    rw [diagMax_coe, coe_sum_single]
    have := trunc_coe c x S k
    by_cases hk : k ∈ S
    · simp [hk, this, hv, diagMax_coe]
    · simp [hk, this]
  simp [heq]
  exact h

/-! ## 2. The extension of a core operator -/

variable (H₀ : lpFiniteModes ι →ₗ[ℂ] L2I ι) (A : ℝ)

/-- The relative bound, on the core. -/
def CoreRelBound (c : ι → ℝ) (H₀ : lpFiniteModes ι →ₗ[ℂ] L2I ι) (A : ℝ) : Prop :=
  ∀ u : lpFiniteModes ι, ‖H₀ u‖ ≤ A * ‖(diagMax c (inclC c u) : L2I ι)‖

theorem cauchySeq_coreExt [DecidableEq ι] {c : ι → ℝ} {H₀ : lpFiniteModes ι →ₗ[ℂ] L2I ι}
    {A : ℝ} (hA : CoreRelBound c H₀ A) (x : maxDom c) :
    CauchySeq (fun S : Finset ι => H₀ (trunc c x S)) := by
  classical
  have hd := (tendsto_diag_trunc c x).cauchySeq
  rw [Metric.cauchySeq_iff] at hd ⊢
  intro ε hε
  have hApos : 0 < |A| + 1 := by positivity
  obtain ⟨S₀, hS₀⟩ := hd (ε / (|A| + 1)) (by positivity)
  refine ⟨S₀, fun S hS T hT => ?_⟩
  have hkey := hA (trunc c x S - trunc c x T)
  have hlin : (diagMax c (inclC c (trunc c x S - trunc c x T)) : L2I ι)
      = (diagMax c (inclC c (trunc c x S)) : L2I ι)
        - (diagMax c (inclC c (trunc c x T)) : L2I ι) := by
    simp [map_sub]
  rw [map_sub, hlin] at hkey
  have hd' := hS₀ S hS T hT
  rw [dist_eq_norm] at hd' ⊢
  have hle : ‖(diagMax c (inclC c (trunc c x S)) : L2I ι)
      - (diagMax c (inclC c (trunc c x T)) : L2I ι)‖ < ε / (|A| + 1) := hd'
  have hAle : A ≤ |A| := le_abs_self A
  have hnn : (0:ℝ) ≤ ‖(diagMax c (inclC c (trunc c x S)) : L2I ι)
      - (diagMax c (inclC c (trunc c x T)) : L2I ι)‖ := norm_nonneg _
  have hstep : A * ‖(diagMax c (inclC c (trunc c x S)) : L2I ι)
      - (diagMax c (inclC c (trunc c x T)) : L2I ι)‖
      ≤ (|A| + 1) * ‖(diagMax c (inclC c (trunc c x S)) : L2I ι)
      - (diagMax c (inclC c (trunc c x T)) : L2I ι)‖ :=
    mul_le_mul_of_nonneg_right (by linarith) hnn
  have hstep2 : (|A| + 1) * ‖(diagMax c (inclC c (trunc c x S)) : L2I ι)
      - (diagMax c (inclC c (trunc c x T)) : L2I ι)‖ < (|A| + 1) * (ε / (|A| + 1)) :=
    mul_lt_mul_of_pos_left hle hApos
  have hfin : (|A| + 1) * (ε / (|A| + 1)) = ε := by field_simp
  linarith [hkey, hstep, hstep2]

/-- **The extension of a core operator to the maximal domain**, as a function. -/
def coreExtFun [DecidableEq ι] (c : ι → ℝ) (H₀ : lpFiniteModes ι →ₗ[ℂ] L2I ι)
    (x : maxDom c) : L2I ι :=
  limUnder atTop (fun S : Finset ι => H₀ (trunc c x S))

theorem tendsto_coreExt [DecidableEq ι] {c : ι → ℝ} {H₀ : lpFiniteModes ι →ₗ[ℂ] L2I ι}
    {A : ℝ} (hA : CoreRelBound c H₀ A) (x : maxDom c) :
    Tendsto (fun S : Finset ι => H₀ (trunc c x S)) atTop (𝓝 (coreExtFun c H₀ x)) :=
  (cauchySeq_coreExt hA x).tendsto_limUnder

/-- The extension agrees with the given operator on the core. -/
theorem coreExt_core [DecidableEq ι] {c : ι → ℝ} {H₀ : lpFiniteModes ι →ₗ[ℂ] L2I ι} {A : ℝ}
    (hA : CoreRelBound c H₀ A) (u : lpFiniteModes ι) :
    coreExtFun c H₀ (inclC c u) = H₀ u := by
  classical
  have hfin : (Function.support ((u : L2I ι) : ι → ℂ)).Finite := u.2
  have heq : ∀ S : Finset ι, hfin.toFinset ⊆ S → trunc c (inclC c u) S = u := by
    intro S hS
    ext k
    rw [trunc_coe]
    by_cases hk : k ∈ S
    · simp [hk]
    · have : ((u : L2I ι) : ι → ℂ) k = 0 := by
        by_contra hne
        exact hk (hS (by simpa [Set.Finite.mem_toFinset, Function.mem_support] using hne))
      simp [hk, this]
  have : Tendsto (fun S : Finset ι => H₀ (trunc c (inclC c u) S)) atTop (𝓝 (H₀ u)) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [Filter.eventually_ge_atTop hfin.toFinset] with S hS
    rw [heq S hS]
  exact tendsto_nhds_unique (tendsto_coreExt hA (inclC c u)) this

/-- The extension is linear. -/
def coreExt [DecidableEq ι] {c : ι → ℝ} {H₀ : lpFiniteModes ι →ₗ[ℂ] L2I ι} {A : ℝ}
    (hA : CoreRelBound c H₀ A) : maxDom c →ₗ[ℂ] L2I ι where
  toFun := coreExtFun c H₀
  map_add' x y := by
    refine tendsto_nhds_unique (tendsto_coreExt hA (x + y)) ?_
    have h : Tendsto (fun S : Finset ι => H₀ (trunc c x S) + H₀ (trunc c y S)) atTop
        (𝓝 (coreExtFun c H₀ x + coreExtFun c H₀ y)) :=
      (tendsto_coreExt hA x).add (tendsto_coreExt hA y)
    refine h.congr fun S => ?_
    rw [← map_add, trunc_add]
  map_smul' a x := by
    refine tendsto_nhds_unique (tendsto_coreExt hA (a • x)) ?_
    have h : Tendsto (fun S : Finset ι => a • H₀ (trunc c x S)) atTop
        (𝓝 (a • coreExtFun c H₀ x)) := (tendsto_coreExt hA x).const_smul a
    refine h.congr fun S => ?_
    rw [← map_smul, trunc_smul]

@[simp] theorem coreExt_apply [DecidableEq ι] {c : ι → ℝ} {H₀ : lpFiniteModes ι →ₗ[ℂ] L2I ι}
    {A : ℝ} (hA : CoreRelBound c H₀ A) (x : maxDom c) : coreExt hA x = coreExtFun c H₀ x := rfl

/-- The extension inherits the relative bound. -/
theorem norm_coreExt_le [DecidableEq ι] {c : ι → ℝ} {H₀ : lpFiniteModes ι →ₗ[ℂ] L2I ι} {A : ℝ}
    (hA : CoreRelBound c H₀ A) (x : maxDom c) :
    ‖coreExt hA x‖ ≤ A * ‖(diagMax c x : L2I ι)‖ := by
  have h1 : Tendsto (fun S : Finset ι => ‖H₀ (trunc c x S)‖) atTop (𝓝 ‖coreExt hA x‖) :=
    (tendsto_coreExt hA x).norm
  have h2 : Tendsto (fun S : Finset ι =>
      A * ‖(diagMax c (inclC c (trunc c x S)) : L2I ι)‖) atTop
      (𝓝 (A * ‖(diagMax c x : L2I ι)‖)) := ((tendsto_diag_trunc c x).norm).const_mul A
  exact le_of_tendsto_of_tendsto' h1 h2 fun S => hA _

/-- The extension inherits symmetry. -/
theorem coreExt_symmetricOn [DecidableEq ι] {c : ι → ℝ} {H₀ : lpFiniteModes ι →ₗ[ℂ] L2I ι}
    {A : ℝ} (hA : CoreRelBound c H₀ A)
    (hsym : ∀ u v : lpFiniteModes ι,
      (inner ℂ (H₀ u) ((v : L2I ι)) : ℂ) = inner ℂ ((u : L2I ι)) (H₀ v)) :
    SymmetricOn (maxDom c) (coreExt hA) := by
  intro x y
  have hL : Tendsto (fun S : Finset ι =>
      (inner ℂ (H₀ (trunc c x S)) ((trunc c y S : lpFiniteModes ι) : L2I ι) : ℂ)) atTop
      (𝓝 (inner ℂ (coreExt hA x) ((y : L2I ι)) : ℂ)) :=
    ((tendsto_coreExt hA x).inner (tendsto_trunc c y))
  have hR : Tendsto (fun S : Finset ι =>
      (inner ℂ ((trunc c x S : lpFiniteModes ι) : L2I ι) (H₀ (trunc c y S)) : ℂ)) atTop
      (𝓝 (inner ℂ ((x : L2I ι)) (coreExt hA y) : ℂ)) :=
    ((tendsto_trunc c x).inner (tendsto_coreExt hA y))
  refine tendsto_nhds_unique hL (hR.congr fun S => ?_)
  exact (hsym (trunc c x S) (trunc c y S)).symm

/-- The extension inherits the commutator bound. -/
theorem coreExt_commForm_le [DecidableEq ι] {c : ι → ℝ} {H₀ : lpFiniteModes ι →ₗ[ℂ] L2I ι}
    {A B : ℝ} (hA : CoreRelBound c H₀ A)
    (hcomm : ∀ u : lpFiniteModes ι,
      |(-2 : ℝ) * (inner ℂ (H₀ u) ((diagMax c (inclC c u) : L2I ι)) : ℂ).im|
        ≤ B * (inner ℂ ((u : L2I ι)) ((diagMax c (inclC c u) : L2I ι)) : ℂ).re)
    (x : maxDom c) :
    |commForm (coreExt hA) (diagMax c) x| ≤ B * quadForm (diagMax c) x := by
  have hL : Tendsto (fun S : Finset ι =>
      |(-2 : ℝ) * (inner ℂ (H₀ (trunc c x S))
        ((diagMax c (inclC c (trunc c x S)) : L2I ι)) : ℂ).im|) atTop
      (𝓝 |(-2 : ℝ) * (inner ℂ (coreExt hA x) ((diagMax c x : L2I ι)) : ℂ).im|) := by
    have h := Filter.Tendsto.inner (𝕜 := ℂ) (tendsto_coreExt hA x) (tendsto_diag_trunc c x)
    exact ((Complex.continuous_im.tendsto _).comp h).const_mul (-2 : ℝ) |>.abs
  have hR : Tendsto (fun S : Finset ι =>
      B * (inner ℂ ((trunc c x S : lpFiniteModes ι) : L2I ι)
        ((diagMax c (inclC c (trunc c x S)) : L2I ι)) : ℂ).re) atTop
      (𝓝 (B * (inner ℂ ((x : L2I ι)) ((diagMax c x : L2I ι)) : ℂ).re)) := by
    have h := Filter.Tendsto.inner (𝕜 := ℂ) (tendsto_trunc c x) (tendsto_diag_trunc c x)
    exact ((Complex.continuous_re.tendsto _).comp h).const_mul B
  have hlim := le_of_tendsto_of_tendsto' hL hR fun S => hcomm (trunc c x S)
  rw [commForm_eq_neg_two_im, quadForm]
  exact hlim

/-! ## 3. The instrument -/

/-- **Essential self-adjointness from bounds checked on the finite-mode core.**  A
symmetric operator `H` defined on the finite-mode core of `ℓ²(ι)`, with the relative bound
`‖H u‖ ≤ A‖N u‖` and the commutator bound `|⟪u, i[H, N]u⟫| ≤ B⟪u, N u⟫` against the
comparison operator `N` — multiplication by a non-negative symbol — **both checked on the
core only**, is essentially self-adjoint on that core. -/
theorem essentiallySelfAdjointOn_finiteModes_of_core_bounds
    (c : ι → ℝ) (hc : ∀ k, 0 ≤ c k) (H₀ : lpFiniteModes ι →ₗ[ℂ] L2I ι) (A B : ℝ) (hB : 0 ≤ B)
    (hsym : ∀ u v : lpFiniteModes ι,
      (inner ℂ (H₀ u) ((v : L2I ι)) : ℂ) = inner ℂ ((u : L2I ι)) (H₀ v))
    (hA : CoreRelBound c H₀ A)
    (hcomm : ∀ u : lpFiniteModes ι,
      |(-2 : ℝ) * (inner ℂ (H₀ u) ((diagMax c (inclC c u) : L2I ι)) : ℂ).im|
        ≤ B * (inner ℂ ((u : L2I ι)) ((diagMax c (inclC c u) : L2I ι)) : ℂ).re) :
    EssentiallySelfAdjointOn (lpFiniteModes ι) H₀ := by
  classical
  have hkey := essentiallySelfAdjointOn_finiteModes_of_bounds c hc (coreExt hA) A B hB
    (coreExt_symmetricOn hA hsym) (norm_coreExt_le hA) (coreExt_commForm_le hA hcomm)
  have hres : (coreExt hA).comp (Submodule.inclusion (finiteModes_le_maxDom c)) = H₀ :=
    LinearMap.ext fun u => coreExt_core hA u
  rwa [hres] at hkey

/-- The number-conserving case: the commutator form vanishes on the core. -/
theorem essentiallySelfAdjointOn_finiteModes_of_core_bounds_comm
    (c : ι → ℝ) (hc : ∀ k, 0 ≤ c k) (H₀ : lpFiniteModes ι →ₗ[ℂ] L2I ι) (A : ℝ)
    (hsym : ∀ u v : lpFiniteModes ι,
      (inner ℂ (H₀ u) ((v : L2I ι)) : ℂ) = inner ℂ ((u : L2I ι)) (H₀ v))
    (hA : CoreRelBound c H₀ A)
    (hcomm : ∀ u : lpFiniteModes ι,
      (inner ℂ (H₀ u) ((diagMax c (inclC c u) : L2I ι)) : ℂ).im = 0) :
    EssentiallySelfAdjointOn (lpFiniteModes ι) H₀ := by
  refine essentiallySelfAdjointOn_finiteModes_of_core_bounds c hc H₀ A 0 le_rfl hsym hA ?_
  intro u
  rw [hcomm u]
  simp

end

end BookProof.CoreBounds


