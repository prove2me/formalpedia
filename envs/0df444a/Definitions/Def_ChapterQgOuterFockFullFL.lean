-- Prove2me | Definitions.Def_ChapterQgOuterFockFullFL
-- name    : ChapterQgOuterFockFullFL
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-18T11:09:05.127725+00:00
-- url     : https://prove2.me/theorems/15b3f956-6467-407a-a962-afe78c1bcbe3
-- title:
--   The Lean 4 theorem `isGraphCore_of_eigenbasis` in the `?` chapter of the timepiece formalization
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterQgOuterFockFullFL.lean`): generated def bundle for ChapterQgOuterFockFullFL. See BookProof/ChapterQgOuterFockFullFL.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgOuterFockFullFL.lean

import Theorems.Thm_BookProof_QgOuterFockFL_harmFried_op_core

import Theorems.Thm_BookProof_HermiteProductBasis_hermiteMvBasis_apply


import Theorems.Thm_BookProof_QgHermiteOscillator_harmCore_hermiteMvLp


import Theorems.Thm_BookProof_QgOuterFockFL_polyGaussCore_le_harmFriedDom

import Theorems.Thm_BookProof_SqSumFarisLavine_potFun_le_of_schur

import Theorems.Thm_BookProof_SqSumFarisLavine_norm_sqSumOp_le

import Theorems.Thm_BookProof_QgOuterFock_modeOf_pcoord

import Theorems.Thm_BookProof_QgOuterFock_partOf_pcoord

import Theorems.Thm_BookProof_QgOuterFock_sum_reindex_particles

import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_ChapterSqSumFarisLavine
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGaussCoreQuadBounds
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterQg3DGaugeEsa
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterQgHermiteFriedrichs
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterQgOuterFockEsa
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Definitions.Def_ChapterQuantumGravity3DGauge
import Mathlib


/-!
# The full quantum-gravity Hamiltonian on the outer Fock space, by Faris–Lavine

This module closes the Faris–Lavine route to the quantum-gravity Hamiltonian on the outer
Fock space `𝔉 = ⊕ₙ L²(ℝ^{84n})`.  `BookProof.ChapterQgOuterFockFarisLavine` built the
apparatus — the lifted Friedrichs extension of the positive one-particle operator
`N₁ = −Δ + ‖x‖²/4` as comparison operator, and the `ℓ²`-direct-sum form of Theorem 1 of
Faris–Lavine — but left the *sector data* as hypotheses.  Here they are discharged, so the
conclusion becomes unconditional.

Three things had to be supplied for every particle number `n`, with constants that do not
degrade as `n → ∞`:

1. **A graph core.**  `isGraphCore_of_eigenbasis` shows that a subspace containing an
   eigenbasis of the comparison operator is automatically dense in its graph norm, and
   `harmFried_isGraphCore` applies it to the product Hermite basis: the Gauss–polynomial
   core is a graph core for the Friedrichs oscillator in every dimension.
2. **Uniform Schur data for the gravity sector.**  The `n`-particle torsion family
   `qgTorsionVecN` has row `ℓ¹` norm at most `2` (each torsion form has two nonzero
   entries, `qgTorsionVecN_row_le`) and column `ℓ¹` norm at most `64` (each coordinate is
   touched by at most `64` torsion forms, and — the key point — only by forms of *its own*
   particle, so the bound is **independent of `n`**, `qgTorsionVecN_col_le`).  The
   signature is bounded by `1/16` (`qgKappaN_abs_le`).
3. **The two Faris–Lavine inequalities**, from `BookProof.ChapterSqSumFarisLavine`:
   `qgSectorHam_norm_le` (relative bound, constant `qgFLK`) and
   `qgSectorHam_commForm_le` (commutator bound, constant `qgFLc`), both independent of `n`.

The extension from the Gauss–polynomial core to the whole Friedrichs domain is the
`CoreData` machinery of `BookProof.ChapterQgOuterFockCoreFL` (`qgSectorData`,
`qgSectorExt`), which preserves symmetry, the relative bound and the commutator bound with
the same constants.

## What is proved

* `isGraphCore_of_eigenbasis`, `harmFried_isGraphCore` — the graph-core step;
* `qgKappaN_abs_le`, `abs_torsionVec_le_one`, `sum_abs_torsionVec_le_two`,
  `qgTorsionVecN_row_le`, `qgTorsionVecN_col_le`, `qgSector_potFun_le`,
  `qgSector_gradFun_le` — the uniform sector data;
* `qgFLK`, `qgFLc`, `qgSectorHam_norm_le`, `qgSectorHam_commForm_le` — the two
  Faris–Lavine inequalities for the `n`-particle gravity Hamiltonian, with constants
  uniform in `n`;
* `qgSectorData`, `qgSectorExt`, `qgSectorExt_symmetricOn`, `qgSectorExt_core`,
  `qgSectorExt_rel`, `qgSectorExt_commForm_le` — the sector Hamiltonian on the whole
  domain of the sector comparison operator;
* **`qgOuterFock_esa_farisLavine_full`** — the headline: the full gauge-fixed 3D
  quantum-gravity Hamiltonian is essentially self-adjoint on the domain of the lifted
  Friedrichs extension of `N₁`, and the operator so realized extends `qgOuterHam` on the
  finite-particle core.

## Honest boundary

The Hamiltonian is the outer-Fock second quantization of the one-particle operator of
`BookProof.ChapterQuantumGravity3DGauge`: in each `n`-particle sector,
`½ Σ_j κ_j π_j² + ½ Σ_m T_m²` acting in each particle's own 84 field-space coordinates,
with the physical hyperbolic signature.  The Fock space is the `ℓ²`-direct sum of the
sectors — distinguishable excitations, no symmetrization — and this Hamiltonian preserves
the particle number.  No spectrum, no mass gap and no continuum limit is claimed.  An
independent proof of essential self-adjointness on the *finite-particle core* by the
Carleman route is `BookProof.QgOuterFock.qgOuterFock_esa`; what is new here is the
Faris–Lavine proof on the much larger domain of the lifted comparison operator.

Everything is `sorry`-free and `axiom`-free.
-/

namespace BookProof.QgOuterFockFullFL

open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator BookProof.FarisLavine
open BookProof.QgOuterFock BookProof.QgOuterFockFL BookProof.QgOuterFockCoreFL
open BookProof.Qg3DGaugeEsa BookProof.QuantumGravity3DGauge
open BookProof.GaussCoreQuadBounds BookProof.SqSumFarisLavine
open Filter Topology

noncomputable section

/-! ## 1. An eigenbasis inside the core makes it a graph core -/

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

set_option maxHeartbeats 1000000 in
-- the eigenexpansion argument manipulates large `HilbertBasis` coercions
omit [CompleteSpace F] in
/-- **A core containing an eigenbasis of the comparison operator is a graph core**: the
truncations of the eigenexpansion converge in the graph norm. -/
theorem isGraphCore_of_eigenbasis {ι : Type*} (C : Comparison F) (C₀ : Submodule ℂ F)
    (hle : C₀ ≤ C.dom) (b : HilbertBasis ι ℂ F) (lam : ι → ℝ)
    (hmem : ∀ i, (b i) ∈ C₀)
    (heig : ∀ i, C.op ⟨b i, hle (hmem i)⟩ = ((lam i : ℝ) : ℂ) • b i) :
    IsGraphCore C C₀ := by
  have hnorm : ∀ i, (inner ℂ (b i) (b i) : ℂ) = 1 := by
    intro i
    have h := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (b i)
    rw [h, b.orthonormal.1 i]
    norm_num
  have hlam : ∀ i, 0 ≤ lam i := by
    intro i
    have hq := C.pos ⟨b i, hle (hmem i)⟩
    have hv : (inner ℂ (b i) (C.op ⟨b i, hle (hmem i)⟩) : ℂ) = ((lam i : ℝ) : ℂ) := by
      rw [heig i, inner_smul_right, hnorm i, mul_one]
    rw [quadForm] at hq
    simpa [hv] using hq
  have hne : ∀ i, ((lam i + 1 : ℝ) : ℂ) ≠ 0 := by
    intro i
    have : (0 : ℝ) < lam i + 1 := by linarith [hlam i]
    exact_mod_cast ne_of_gt this
  refine ⟨hle, ?_⟩
  intro x ε hε
  set y : F := C.op x + (x : F) with hy
  set c : ι → ℂ := fun i => b.repr y i / ((lam i + 1 : ℝ) : ℂ) with hc
  have hsum : HasSum (fun i => (b.repr y i) • b i) y := b.hasSum_repr y
  have htend : Tendsto (fun s : Finset ι => ∑ i ∈ s, (b.repr y i) • b i) atTop (𝓝 y) := by
    rw [HasSum] at hsum
    simpa [SummationFilter.unconditional] using hsum
  have hev : ∀ᶠ s : Finset ι in atTop,
      (∑ i ∈ s, (b.repr y i) • b i) ∈ Metric.ball y (ε / 2) :=
    htend (Metric.ball_mem_nhds y (by positivity))
  obtain ⟨s, hs⟩ := hev.exists
  have hs' : ‖(∑ i ∈ s, (b.repr y i) • b i) - y‖ < ε / 2 := by
    rw [← dist_eq_norm]; exact Metric.mem_ball.mp hs
  have hwmem : (∑ i ∈ s, c i • b i) ∈ C₀ :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hmem i)
  set z : C.dom := ⟨∑ i ∈ s, c i • b i, hle hwmem⟩ with hz
  have hdecomp : z = ∑ i ∈ s, c i • (⟨b i, hle (hmem i)⟩ : C.dom) := by
    refine Subtype.ext ?_
    rw [hz]
    push_cast
    rfl
  have hop : C.op z = ∑ i ∈ s, c i • (((lam i : ℝ) : ℂ) • b i) := by
    rw [hdecomp, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, heig i]
  have hshift : C.op z + (z : F) = ∑ i ∈ s, (b.repr y i) • b i := by
    have hzc : (z : F) = ∑ i ∈ s, c i • b i := rfl
    rw [hop, hzc, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, ← add_smul]
    congr 1
    have hnz : ((lam i + 1 : ℝ) : ℂ) ≠ 0 := hne i
    change b.repr y i / ((lam i + 1 : ℝ) : ℂ) * ((lam i : ℝ) : ℂ)
        + b.repr y i / ((lam i + 1 : ℝ) : ℂ) = b.repr y i
    rw [div_mul_eq_mul_div, ← add_div, div_eq_iff hnz]
    push_cast
    ring
  have hball : ‖C.op z + (z : F) - y‖ < ε / 2 := by
    rw [hshift]
    exact hs'
  have hdiff : C.op (z - x) + ((z - x : C.dom) : F) = C.op z + (z : F) - y := by
    rw [map_sub, hy]
    push_cast
    abel
  have h1 : ‖((z - x : C.dom) : F)‖ < ε / 2 := by
    have := norm_le_norm_shift C.op C.pos (z - x)
    rw [hdiff] at this
    exact lt_of_le_of_lt this hball
  have h1' : ‖(z : F) - (x : F)‖ < ε / 2 := by
    have : ((z - x : C.dom) : F) = (z : F) - (x : F) := rfl
    rwa [this] at h1
  refine ⟨z, hwmem, by linarith, ?_⟩
  have h2 : C.op z - C.op x = (C.op z + (z : F) - y) - ((z : F) - (x : F)) := by
    rw [hy]; abel
  calc ‖C.op z - C.op x‖ = ‖(C.op z + (z : F) - y) - ((z : F) - (x : F))‖ := by rw [h2]
    _ ≤ ‖C.op z + (z : F) - y‖ + ‖(z : F) - (x : F)‖ := norm_sub_le _ _
    _ < ε := by linarith

/-- **The Gauss–polynomial core is a graph core for the Friedrichs oscillator.** -/
theorem harmFried_isGraphCore (d : ℕ) :
    IsGraphCore (harmFried d) (polyGaussCore (d := d)) := by
  refine isGraphCore_of_eigenbasis (harmFried d) (polyGaussCore (d := d))
    (polyGaussCore_le_harmFriedDom d) hermiteMvBasis
    (fun a => (mvDeg a : ℝ) + (d : ℝ) / 2)
    (fun a => by rw [hermiteMvBasis_apply]; exact hermiteMvLp_mem_core a) fun a => ?_
  simp only [hermiteMvBasis_apply]
  rw [harmFried_op_core d ⟨hermiteMvLp a, hermiteMvLp_mem_core a⟩]
  exact harmCore_hermiteMvLp a

/-! ## 2. The `n`-particle gravity data, with constants uniform in `n` -/

/-- The bound on the gravity signature. -/
theorem qgKappaN_abs_le (n : ℕ) (I : Fin (n * 84)) : |qgKappaN n I| ≤ 1 / 16 := by
  rw [qgKappaN, qgKappa]
  split_ifs <;> norm_num

/-- Every entry of a torsion form has modulus at most one. -/
theorem abs_torsionVec_le_one (m : Fin 64) (i : Fin 84) : |torsionVec m i| ≤ 1 := by
  rw [torsionVec]
  split_ifs <;> norm_num

/-- A torsion form has `ℓ¹` norm at most `2`: it has two nonzero entries, of modulus one. -/
theorem sum_abs_torsionVec_le_two (m : Fin 64) : ∑ i : Fin 84, |torsionVec m i| ≤ 2 := by
  have hle : ∀ i : Fin 84, |torsionVec m i|
      ≤ (if i = torsionIdx1 m then (1 : ℝ) else 0)
        + (if i = torsionIdx2 m then (1 : ℝ) else 0) := by
    intro i
    rw [torsionVec]
    split_ifs <;> norm_num
  calc ∑ i : Fin 84, |torsionVec m i|
      ≤ ∑ i : Fin 84, ((if i = torsionIdx1 m then (1 : ℝ) else 0)
          + (if i = torsionIdx2 m then (1 : ℝ) else 0)) :=
        Finset.sum_le_sum fun i _ => hle i
    _ = 2 := by
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ (torsionIdx1 m)
          (fun _ => (1 : ℝ)), Finset.sum_ite_eq' Finset.univ (torsionIdx2 m)
          (fun _ => (1 : ℝ))]
        norm_num

/-- The `ℓ¹` bound on a torsion form: two nonzero entries, of modulus one. -/
theorem qgTorsionVecN_row_le (n : ℕ) (r : Fin n × Fin 64) :
    ∑ I : Fin (n * 84), |qgTorsionVecN n r I| ≤ 2 := by
  rw [sum_reindex_particles (fun I => |qgTorsionVecN n r I|)]
  have hterm : ∀ (p : Fin n) (i : Fin 84),
      |qgTorsionVecN n r (pcoord p i)| = if p = r.1 then |torsionVec r.2 i| else 0 := by
    intro p i
    rw [qgTorsionVecN, partOf_pcoord, modeOf_pcoord]
    by_cases h : p = r.1 <;> simp [h]
  simp only [hterm]
  have hinner : ∀ p : Fin n,
      (∑ i : Fin 84, if p = r.1 then |torsionVec r.2 i| else 0)
        = if p = r.1 then ∑ i : Fin 84, |torsionVec r.2 i| else 0 := by
    intro p
    by_cases h : p = r.1 <;> simp [h]
  simp only [hinner]
  rw [Finset.sum_ite_eq' Finset.univ r.1 (fun _ => ∑ i : Fin 84, |torsionVec r.2 i|)]
  simp only [Finset.mem_univ, if_true]
  exact sum_abs_torsionVec_le_two r.2

/-- The `ℓ¹` bound on a coordinate: it is touched by at most `64` torsion forms — the
bound is *independent of the particle number*, because the forms of a given particle
involve only that particle's coordinates. -/
theorem qgTorsionVecN_col_le (n : ℕ) (I : Fin (n * 84)) :
    ∑ r : Fin n × Fin 64, |qgTorsionVecN n r I| ≤ 64 := by
  rw [Fintype.sum_prod_type]
  have hterm : ∀ (p : Fin n) (m : Fin 64),
      |qgTorsionVecN n (p, m) I| = if partOf I = p then |torsionVec m (modeOf I)| else 0 := by
    intro p m
    rw [qgTorsionVecN]
    by_cases h : partOf I = p <;> simp [h]
  simp only [hterm]
  have hinner : ∀ p : Fin n,
      (∑ m : Fin 64, if partOf I = p then |torsionVec m (modeOf I)| else 0)
        = if partOf I = p then ∑ m : Fin 64, |torsionVec m (modeOf I)| else 0 := by
    intro p
    by_cases h : partOf I = p <;> simp [h]
  simp only [hinner]
  rw [Finset.sum_ite_eq Finset.univ (partOf I)
    (fun _ => ∑ m : Fin 64, |torsionVec m (modeOf I)|)]
  simp only [Finset.mem_univ, if_true]
  calc ∑ m : Fin 64, |torsionVec m (modeOf I)| ≤ ∑ _m : Fin 64, (1 : ℝ) :=
        Finset.sum_le_sum fun m _ => abs_torsionVec_le_one m (modeOf I)
    _ = 64 := by simp

theorem qgSector_potFun_le (n : ℕ) (x : Vd (n * 84)) :
    potFun (qgTorsionVecN n) x ≤ 64 * ‖x‖ ^ 2 := by
  have h := potFun_le_of_schur (a := 2) (b := 64) (by norm_num)
    (qgTorsionVecN_row_le n) (qgTorsionVecN_col_le n) x
  norm_num at h
  exact h



/-- The uniform relative-bound constant. -/
def qgFLK : ℝ := 3 / 2 * (1 / 16) + 8 * 64

/-- The uniform commutator constant. -/
def qgFLc : ℝ := (1 / 16) / 2 + 2 * 128

theorem qgFLK_nonneg : 0 ≤ qgFLK := by norm_num [qgFLK]



/-- **The relative bound for the `n`-particle gravity Hamiltonian**, uniform in `n`. -/
theorem qgSectorHam_norm_le (n : ℕ) (u : polyGaussCore (d := n * 84)) :
    ‖qgSectorHam n u‖ ≤ qgFLK * ‖BookProof.QgOuterFockFL.harmCore u + (u : L2d (n * 84))‖ := by
  rw [qgSectorHam, qgFLK]
  exact norm_sqSumOp_le (km := 1 / 16) (B := 64) (by norm_num)
    (qgKappaN_abs_le n) (by norm_num) (qgSector_potFun_le n) u



/-! ## 3. The sector core data and the extension to the whole comparison domain -/

/-- The Faris–Lavine core data of the `n`-particle gravity Hamiltonian. -/
def qgSectorData (n : ℕ) : CoreData (L2d (n * 84)) where
  C := harmFried (n * 84)
  C₀ := polyGaussCore (d := n * 84)
  gc := harmFried_isGraphCore (n * 84)
  H₀ := qgSectorHam n
  K := qgFLK
  hK := qgFLK_nonneg
  rel := by
    intro p
    rw [harmFried_op_core (n * 84) p]
    exact qgSectorHam_norm_le n p

/-- The `n`-particle gravity Hamiltonian, extended from the Gauss–polynomial core to the
whole domain of the sector comparison operator. -/
def qgSectorExt (n : ℕ) : (harmFried (n * 84)).dom →ₗ[ℂ] L2d (n * 84) := (qgSectorData n).ext











/-! ## 4. The headline -/



end

end BookProof.QgOuterFockFullFL


