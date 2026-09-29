-- Prove2me | Definitions.Def_ChapterNavierStokesSignedShift
-- name    : ChapterNavierStokesSignedShift
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-09T23:58:13.503896+00:00
-- url     : https://prove2.me/theorems/3072e790-7b73-46c6-b4f1-dba863c8a0d6
-- title:
--   `BookProof.ChapterNavierStokesShiftHamiltonian` proves the two Faris–Lavine inequalities for a hopping (shift) Hamiltoni ...
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.NavierStokesSignedShift`, source chapter `BookProof/ChapterNavierStokesSignedShift.lean`).
--
--   `BookProof.ChapterNavierStokesShiftHamiltonian` proves the two Faris–Lavine inequalities for a hopping (shift) Hamiltonian whose amplitude `w` is *non-negative* and *non-decreasing along the shift*. Both restrictions are artefacts of the bookkeeping — they are used only to produce a majorant for the two terms of `(H x)_β = i(w(s⁻¹β) x_{s⁻¹β} − w(β) x_{sβ})` — and both are obstacles for the coupled Navier–Stokes symbol:
--
--   * a negative amplitude occurs whenever a strain rate or a fiber constant is negative, and * a non-monotone amplitude occurs for the *number-conserving* hoppings `a_i† a_k` produced by the antisymmetric (vorticity) part of the velocity gradient, whose amplitude `√((β_i+1) β_k)` increases in one coordinate and decreases in the other.
--
--   This module removes both. The observation is that the estimates never need the amplitude itself: they need a **majorant** which is non-negative, monotone along the shift and dominated by the comparison symbol. The canonical such majorant is `¼ σ + K`, which is monotone as soon as the symbol increases along the shift.
--
--   A `SignedHop ι σ` consists of an injective shift `s`, an **arbitrary real** amplitude `w` with `|w| ≤ ¼ σ + K`, and a constant, non-negative symbol increment `σ (s β) = σ β + Δ`. Its `maj` is the majorant `ShiftData` with the same shift and symbol and amplitude `¼ σ + K`, so all the transport lemmas of `ShiftData` are available.
--
--   * `SignedHop.hopH` — the signed hopping Hamiltonian on the maximal domain of the comparison symbol, and `SignedHop.hopH_symmetricOn`; * `SignedHop.hopH_relative_bound` — `‖Hx‖² ≤ ½‖Nx‖² + 8K²‖x‖²`; * `SignedHop.hopH_commForm_bound` — `|⟪x, i[H, N]x⟫| ≤ 2Δ(¼+K) ⟪x, Nx⟫`; * `SignedHop.hopH_essentiallySelfAdjointOn_core` — essential self-adjointness on the finite-mode core; * `listH` and `listH_essentiallySelfAdjointOn_core` — **the instrument**: a finite family of signed hops sharing one comparison symbol sums to an operator that is again essentially self-adjoint on the finite-mode core; * `gaffH` and `gaffH_essentiallySelfAdjointOn_core` — the affine fiber Hamiltonian `½(π V + V π)` for `V(u) = κ u + c` with **no sign hypothesis at all** on `κ` and `c`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesSignedShift.lean

import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Mathlib

import Mathlib

/-!
# Hopping Hamiltonians with **signed**, non-monotone amplitudes

`BookProof.ChapterNavierStokesShiftHamiltonian` proves the two Faris–Lavine
inequalities for a hopping (shift) Hamiltonian whose amplitude `w` is
*non-negative* and *non-decreasing along the shift*.  Both restrictions are
artefacts of the bookkeeping — they are used only to produce a majorant for the
two terms of `(H x)_β = i(w(s⁻¹β) x_{s⁻¹β} − w(β) x_{sβ})` — and both are
obstacles for the coupled Navier–Stokes symbol:

* a negative amplitude occurs whenever a strain rate or a fiber constant is
  negative, and
* a non-monotone amplitude occurs for the *number-conserving* hoppings
  `a_i† a_k` produced by the antisymmetric (vorticity) part of the velocity
  gradient, whose amplitude `√((β_i+1) β_k)` increases in one coordinate and
  decreases in the other.

This module removes both.  The observation is that the estimates never need the
amplitude itself: they need a **majorant** which is non-negative, monotone along
the shift and dominated by the comparison symbol.  The canonical such majorant
is `¼ σ + K`, which is monotone as soon as the symbol increases along the shift.

## The data

A `SignedHop ι σ` consists of an injective shift `s`, an **arbitrary real**
amplitude `w` with `|w| ≤ ¼ σ + K`, and a constant, non-negative symbol
increment `σ (s β) = σ β + Δ`.  Its `maj` is the majorant `ShiftData` with the
same shift and symbol and amplitude `¼ σ + K`, so all the transport lemmas of
`ShiftData` are available.

## What is proved

* `SignedHop.hopH` — the signed hopping Hamiltonian on the maximal domain of
  the comparison symbol, and `SignedHop.hopH_symmetricOn`;
* `SignedHop.hopH_relative_bound` — `‖Hx‖² ≤ ½‖Nx‖² + 8K²‖x‖²`;
* `SignedHop.hopH_commForm_bound` — `|⟪x, i[H, N]x⟫| ≤ 2Δ(¼+K) ⟪x, Nx⟫`;
* `SignedHop.hopH_essentiallySelfAdjointOn_core` — essential self-adjointness on
  the finite-mode core;
* `listH` and `listH_essentiallySelfAdjointOn_core` — **the instrument**: a
  finite family of signed hops sharing one comparison symbol sums to an operator
  that is again essentially self-adjoint on the finite-mode core;
* `gaffH` and `gaffH_essentiallySelfAdjointOn_core` — the affine fiber
  Hamiltonian `½(π V + V π)` for `V(u) = κ u + c` with **no sign hypothesis at
  all** on `κ` and `c`.
-/

open scoped ENNReal

namespace BookProof.NavierStokesFlow

namespace SignedShift

open LpNat FarisLavine IkebeKato ShiftHamiltonian AffineFiber

variable {ι : Type*}

/-- The data of a hopping term with an **arbitrary real** amplitude: an
injective shift, a real amplitude dominated in absolute value by `¼ σ + K`, and
a constant non-negative increment of the symbol along the shift.  Neither
positivity nor monotonicity of the amplitude is assumed. -/
structure SignedHop (ι : Type*) (sym : ι → ℝ) where
  /-- The shift: the hopping `β ↦ s β`. -/
  shift : ι → ι
  /-- The (signed) hopping amplitude. -/
  amp : ι → ℝ
  /-- The additive constant in the domination of the amplitude by the symbol. -/
  K : ℝ
  /-- The increment of the symbol along the shift. -/
  step : ℝ
  shift_injective : Function.Injective shift
  K_nonneg : 0 ≤ K
  step_nonneg : 0 ≤ step
  sym_ge_one : ∀ β, 1 ≤ sym β
  abs_amp_le : ∀ β, |amp β| ≤ (1 / 4) * sym β + K
  sym_step : ∀ β, sym (shift β) = sym β + step

namespace SignedHop

variable {sym : ι → ℝ} (S : SignedHop ι sym)

/-- The majorant amplitude `¼ σ + K`. -/
noncomputable def bnd (β : ι) : ℝ := (1 / 4) * sym β + S.K

theorem bnd_nonneg (β : ι) : 0 ≤ S.bnd β := le_trans (abs_nonneg _) (S.abs_amp_le β)

theorem bnd_mono (β : ι) : S.bnd β ≤ S.bnd (S.shift β) := by
  simp only [bnd, S.sym_step β]
  linarith [S.step_nonneg]

/-- **The majorant shift data**: the same shift and symbol, with the amplitude
replaced by the majorant `¼ σ + K`, which *is* non-negative and monotone.  All
the transport lemmas of `ShiftData` are used through it. -/
noncomputable def maj : ShiftData ι where
  sym := sym
  shift := S.shift
  amp := S.bnd
  K := S.K
  step := S.step
  shift_injective := S.shift_injective
  amp_nonneg := S.bnd_nonneg
  amp_mono := S.bnd_mono
  K_nonneg := S.K_nonneg
  step_nonneg := S.step_nonneg
  sym_ge_one := S.sym_ge_one
  amp_le := fun _ => le_rfl
  sym_step := S.sym_step







theorem abs_amp_le_bnd (β : ι) : |S.amp β| ≤ S.bnd β := S.abs_amp_le β

/-! ## The Hamiltonian -/

/-- The coordinates of the signed hopping Hamiltonian:
`(H x)_β = i ( w(s⁻¹β) x_{s⁻¹β} − w(β) x_{sβ} )`, with `w` of arbitrary sign. -/
noncomputable def hFun (X : ι → ℂ) : ι → ℂ :=
  fun β => Complex.I * (S.maj.hop (fun α => (S.amp α : ℂ) * X α) β
    - (S.amp β : ℂ) * X (S.shift β))

/-- The two terms of the Hamiltonian are dominated by the majorant sequence. -/
theorem norm_hFun_le (X : ι → ℂ) (β : ι) :
    ‖S.hFun X β‖ ≤ S.maj.hop (S.maj.ampSeq X) β + S.maj.ampSeq X (S.shift β) := by
  have h1 : ‖S.maj.hop (fun α => (S.amp α : ℂ) * X α) β‖ ≤ S.maj.hop (S.maj.ampSeq X) β := by
    by_cases hb : ∃ α, S.maj.shift α = β
    · obtain ⟨α, rfl⟩ := hb
      rw [ShiftData.hop_shift, ShiftData.hop_shift, norm_mul, Complex.norm_real,
        Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (S.abs_amp_le_bnd α) (norm_nonneg _)
    · rw [ShiftData.hop_eq_zero _ _ hb, ShiftData.hop_eq_zero _ _ hb, norm_zero]
  have h2 : ‖(S.amp β : ℂ) * X (S.shift β)‖ ≤ S.maj.ampSeq X (S.shift β) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hb1 : |S.amp β| * ‖X (S.shift β)‖ ≤ S.bnd β * ‖X (S.shift β)‖ :=
      mul_le_mul_of_nonneg_right (S.abs_amp_le_bnd β) (norm_nonneg _)
    have hb2 : S.bnd β * ‖X (S.shift β)‖ ≤ S.bnd (S.shift β) * ‖X (S.shift β)‖ :=
      mul_le_mul_of_nonneg_right (S.bnd_mono β) (norm_nonneg _)
    exact le_trans hb1 hb2
  calc ‖S.hFun X β‖
      = ‖S.maj.hop (fun α => (S.amp α : ℂ) * X α) β - (S.amp β : ℂ) * X (S.shift β)‖ := by
        simp [hFun]
    _ ≤ ‖S.maj.hop (fun α => (S.amp α : ℂ) * X α) β‖ + ‖(S.amp β : ℂ) * X (S.shift β)‖ :=
        norm_sub_le _ _
    _ ≤ S.maj.hop (S.maj.ampSeq X) β + S.maj.ampSeq X (S.shift β) := by linarith

/-- The pointwise square bound behind the relative bound. -/
theorem normSq_hFun_le (X : ι → ℂ) (β : ι) :
    ‖S.hFun X β‖ ^ 2
      ≤ 2 * S.maj.hop (fun α => (S.maj.ampSeq X α) ^ 2) β
        + 2 * (S.maj.ampSeq X (S.shift β)) ^ 2 := by
  have h1 := norm_hFun_le S X β
  have h2 : 0 ≤ S.maj.hop (S.maj.ampSeq X) β :=
    ShiftData.hop_nonneg S.maj (ShiftData.ampSeq_nonneg S.maj X) β
  have h3 : 0 ≤ S.maj.ampSeq X (S.shift β) := ShiftData.ampSeq_nonneg S.maj X _
  have h4 := mul_self_le_mul_self (norm_nonneg (S.hFun X β)) h1
  rw [ShiftData.hop_sq]
  nlinarith [h4, sq_nonneg (S.maj.hop (S.maj.ampSeq X) β - S.maj.ampSeq X (S.shift β))]

/-- The Hamiltonian maps the maximal domain of the comparison operator into the
Hilbert space. -/
theorem memLp_hFun (x : maxDom sym) : Memℓp (S.hFun ((x : L2I ι) : ι → ℂ)) 2 := by
  refine memLpTwo_of_summable_normSq ?_
  have hS := ShiftData.summable_ampSeq_sq S.maj x
  have hshift : Summable (S.maj.hop fun β => (S.maj.ampSeq ((x : L2I ι) : ι → ℂ) β) ^ 2) :=
    ShiftData.summable_hop S.maj hS
  have htail : Summable (fun β => (S.maj.ampSeq ((x : L2I ι) : ι → ℂ) (S.maj.shift β)) ^ 2) :=
    ShiftData.summable_comp_shift S.maj hS
  refine Summable.of_nonneg_of_le (fun β => sq_nonneg _) ?_
    ((hshift.mul_left 2).add (htail.mul_left 2))
  intro β
  exact normSq_hFun_le S _ β

/-- **The signed hopping Hamiltonian**, on the maximal domain of the comparison
operator. -/
noncomputable def hopH : maxDom sym →ₗ[ℂ] L2I ι where
  toFun x := ⟨S.hFun ((x : L2I ι) : ι → ℂ), memLp_hFun S x⟩
  map_add' x y := by
    refine lp.ext (funext fun β => ?_)
    by_cases hb : ∃ α, S.maj.shift α = β
    · obtain ⟨α, rfl⟩ := hb
      simp only [lp.coeFn_add, Pi.add_apply, Submodule.coe_add, hFun, ShiftData.hop_shift]
      ring
    · simp only [lp.coeFn_add, Pi.add_apply, Submodule.coe_add, hFun,
        ShiftData.hop_eq_zero _ _ hb]
      ring
  map_smul' a x := by
    refine lp.ext (funext fun β => ?_)
    by_cases hb : ∃ α, S.maj.shift α = β
    · obtain ⟨α, rfl⟩ := hb
      simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
        Submodule.coe_smul, hFun, ShiftData.hop_shift]
      ring
    · simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
        Submodule.coe_smul, hFun, ShiftData.hop_eq_zero _ _ hb]
      ring



/-! ## Symmetry -/

/-- The hopping series `w(β) x̄_β y_{sβ}`. -/
noncomputable def crossA (X Y : ι → ℂ) : ι → ℂ :=
  fun β => (S.amp β : ℂ) * (starRingEnd ℂ) (X β) * Y (S.shift β)

/-- The hopping series `w(β) x̄_{sβ} y_β`. -/
noncomputable def crossB (X Y : ι → ℂ) : ι → ℂ :=
  fun β => (S.amp β : ℂ) * (starRingEnd ℂ) (X (S.shift β)) * Y β



















/-! ## The first Faris–Lavine inequality -/



/-! ## The second Faris–Lavine inequality -/







end SignedHop

/-! ## Finite families of hops sharing one comparison symbol -/

variable {sym : ι → ℝ}

/-- **The Hamiltonian of a finite family of signed hops** sharing one comparison
symbol: the sum of the individual hopping Hamiltonians, on the maximal domain of
the symbol. -/
noncomputable def listH (L : List (SignedHop ι sym)) : maxDom sym →ₗ[ℂ] L2I ι :=
  (L.map SignedHop.hopH).sum













/-! ## Matrix entries on a basis vector -/





/-! ## The affine fiber field with coefficients of **arbitrary sign**

The affine fiber Hamiltonian `½(π V + V π)` for `V(u) = κ u + c` was built in
`BookProof.ChapterNavierStokesAffineFiberEsa` under `κ ≥ 0` and `c ≥ 0`, and the
sign of `c` was removed by the sign-flip unitary of
`BookProof.ChapterNavierStokesSignFlip`.  The signed instrument above removes
both signs at once: the two hopping amplitudes `(κ/2)√((n+1)(n+2))` and
`(c/√2)√(n+1)` are dominated in absolute value by the comparison symbol built
from `|κ|` and `|c|`, whatever their signs. -/

section GeneralAffine

open HermiteFarisLavine

variable (kap cst : ℝ)

/-- The comparison symbol of the affine fiber field with coefficients of
arbitrary sign: the number operator built from `|κ|` and `|c|`. -/
noncomputable def gsym : ℕ → ℝ := oscSymbol (affMu |kap| |cst|)

theorem gsym_ge_one (n : ℕ) : 1 ≤ gsym kap cst n :=
  oscSymbol_ge_one (by unfold affMu; positivity) n

theorem abs_amp_eq (n : ℕ) : |amp kap n| = amp |kap| n := by
  unfold amp
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), abs_div]
  norm_num

theorem abs_shear_eq (n : ℕ) : |shear cst n| = shear |cst| n := by
  unfold shear
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), abs_div,
    abs_of_nonneg (Real.sqrt_nonneg 2)]

/-- The `±2`-hopping of the linear part, with a strain rate of arbitrary
sign. -/
noncomputable def gLinHop : SignedHop ℕ (gsym kap cst) where
  shift := fun n => n + 2
  amp := amp kap
  K := |kap| + |cst|
  step := 4 * affMu |kap| |cst|
  shift_injective := fun a b hab => by simpa using hab
  K_nonneg := by positivity
  step_nonneg := by unfold affMu; positivity
  sym_ge_one := gsym_ge_one kap cst
  abs_amp_le := fun n => by
    rw [abs_amp_eq, gsym]
    exact amp_le_affine (abs_nonneg kap) (abs_nonneg cst) n
  sym_step := fun n => oscSymbol_step n

/-- The `±1`-hopping of the constant part, with a constant of arbitrary
sign. -/
noncomputable def gShearHop : SignedHop ℕ (gsym kap cst) where
  shift := fun n => n + 1
  amp := shear cst
  K := |kap| + |cst|
  step := 2 * affMu |kap| |cst|
  shift_injective := fun a b hab => by simpa using hab
  K_nonneg := by positivity
  step_nonneg := by unfold affMu; positivity
  sym_ge_one := gsym_ge_one kap cst
  abs_amp_le := fun n => by
    rw [abs_shear_eq, gsym]
    exact shear_le (abs_nonneg cst) (abs_nonneg kap) n
  sym_step := fun n => by unfold gsym oscSymbol; push_cast; ring

/-- **The affine fiber Hamiltonian for an arbitrary real strain rate and an
arbitrary real constant** `V(u) = κ u + c`, on the maximal domain of the
comparison symbol built from `|κ|` and `|c|`. -/
noncomputable def gaffH : maxDom (gsym kap cst) →ₗ[ℂ] L2I ℕ :=
  listH [gLinHop kap cst, gShearHop kap cst]





end GeneralAffine

end SignedShift

end BookProof.NavierStokesFlow


