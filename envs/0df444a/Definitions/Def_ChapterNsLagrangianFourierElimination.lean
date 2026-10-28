-- Prove2me | Definitions.Def_ChapterNsLagrangianFourierElimination
-- name    : ChapterNsLagrangianFourierElimination
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-27T13:06:49.588392+00:00
-- url     : https://prove2.me/theorems/6fbedd2f-0a55-4680-878a-3e86aa6911bd
-- title:
--   Chapter NsLagrangianFourierElimination
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterNsLagrangianFourierElimination.lean`): generated def bundle for ChapterNsLagrangianFourierElimination. See BookProof/ChapterNsLagrangianFourierElimination.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNsLagrangianFourierElimination.lean

import Definitions.Def_ChapterNavierStokesFullLagrangianFock
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterYangMillsHermite
import Mathlib


/-!
# The Fourier elimination in **Lagrangian** (material) variables — and the degeneracy it meets

`CONSOLIDATED_PLAN.md` item 6 asks for the Lagrangian version of the Fourier elimination of the
derivative variables, by “the same device” as the Eulerian one: the spatial transform is on the
**reference** coordinate `a`, so the material derivative is diagonal, `∂/∂a_j ↦ i ℓ_j`, and the
coordinates that *represent* derivatives are eliminated by

```
σ(F_{ij}) = i ℓ_j ξ_i ,    σ(V_{ij}) = i ℓ_j v_i ,    σ(S_i) = −|ℓ|² v_i ,    σ(y_j) = 0 ,
```

leaving the twelve coordinates `(ξ_i, v_i, a_i, q_i)` per parcel.

**The content of this chapter is that this device is degenerate, and the proof is short.**  The
substitution makes the deformation gradient the *rank-one* matrix `F = ℓ ⊗ ξ` at every mode, and in
three dimensions

* every `2 × 2` minor of a rank-one matrix vanishes, hence `cof(F) = 0` — so the **Piola pressure
  term** `Σ_j cof(F)_{ji} q_j`, which is the entire pressure coupling of the material momentum
  equation, is annihilated by the elimination (`lagElimSubst_piola`);
* `det F = 0` for the same reason, so the **volume constraint** `det F = 1` collapses to the
  constant `−1` (`lagElimSubst_volumePoly`), whose square is `1`
  (`lagElimSubst_volumePoly_sq`) — it carries no field content and cannot couple to the field.

So the Lagrangian route cannot eliminate `F` mode-wise.  The symbolic checks B1–B3 of
`DESIGN_COMPARISON_N_20260915.md` §9 (Piola quadratic, determinant cubic, volume square sextic) are
*degree* checks and are passed trivially by the zero polynomial; the design note's §6 reading is the
right one: in the material picture the determinant must be treated as an independent scalar mode
(`log det F`, with `grad_logDet` on the physical sector `‖A‖ < 1`), not through `F = i ℓ ⊗ ξ`.  The
elimination of the *velocity* derivative `V_{ij} → i ℓ_j v_i` and of the viscous coordinate
`S_i → −|ℓ|² v_i` is unaffected, and the eliminated momentum equation keeps exactly those two terms
(`lagElimSubst_lagResPoly`).

**Status: complete.**  §1–5 below all elaborate: `lRedIdx`, `lagElimCoord` / `lagLift` /
`lagElimHom` and the coordinate values for `ξ_i`, `v_i`, `a_i`, `q_i`, `y_j`, `S_i`; the two
rank-one coordinate lemmas `lagElimCoord_fIdx` and `lagElimCoord_vgIdx` (previously a heartbeat
timeout in their `Fin 36`-index bookkeeping, now proved by rewriting the index arithmetic before
the dependent `Fin` constructors are touched); and the degeneracy itself (`rankOne_cof_zero`,
`lagElimSubst_cofPoly`/`_piola`/`_detPoly`/`_volumePoly`/`_volumePoly_sq`,
`lagElimSubst_lagResPoly`).  No `sorry` and no `axiom` is used anywhere in the file, and the
module is imported by `BookProof.lean`.  This discharges the handoff of `CONSOLIDATED_PLAN.md`
item 6, “Status — handoff to the Lean specialist”.
-/

namespace BookProof.NsLagFourier

open MvPolynomial
open BookProof.YangMillsHermite BookProof.HermiteProductCore
open BookProof.NsFullLagrangian

noncomputable section

variable {n : ℕ}

/-- The scalar `−1 ∈ ℝ ⊆ ℂ` as a polynomial coefficient is the polynomial `−1`. -/
theorem C_neg_one_real (n : ℕ) :
    (C (((-1 : ℝ) : ℂ)) : MvPolynomial (Fin (n * 12)) ℂ) = -1 := by
  rw [show (((-1 : ℝ) : ℂ)) = -(1 : ℂ) by norm_num, C_neg, C_1]

/-! ## 1. The reduced coordinates and the substitution `σ` -/

/-- The reduced twelve-coordinate block of one parcel: `(ξ_i, v_i, a_i, q_i)`. -/
def lRedIdx (p : Fin n) (i : Fin 12) : Fin (n * 12) := finProdFinEquiv (p, i)

abbrev xiIdx12 (i : Fin 3) : Fin 12 := ⟨i.val, by omega⟩

abbrev vIdx12 (i : Fin 3) : Fin 12 := ⟨3 + i.val, by omega⟩

abbrev accIdx12 (i : Fin 3) : Fin 12 := ⟨6 + i.val, by omega⟩

abbrev qIdx12 (i : Fin 3) : Fin 12 := ⟨9 + i.val, by omega⟩

/-- The elimination substitution on one parcel's 36 coordinates, as a polynomial in the twelve
reduced coordinates.  The layout of `Fin 36` is that of `xiIdx`/`vIdx`/`accIdx`/`fIdx`/`vgIdx`/
`sIdx`/`qIdx`/`yIdx` of `ChapterNavierStokesFullLagrangianFock`. -/
def lagElimCoord (l : Fin 3 → ℝ) (i : Fin 36) : MvPolynomial (Fin 12) ℂ :=
  if h : i.val < 3 then X (xiIdx12 ⟨i.val, h⟩)
  else if h2 : i.val < 6 then X (vIdx12 ⟨i.val - 3, by omega⟩)
  else if h3 : i.val < 9 then X (accIdx12 ⟨i.val - 6, by omega⟩)
  else if _h4 : i.val < 18 then
    C (Complex.I * (((l ⟨(i.val - 9) % 3, by omega⟩ : ℝ)) : ℂ))
      * X (xiIdx12 ⟨(i.val - 9) / 3, by omega⟩)
  else if _h5 : i.val < 27 then
    C (Complex.I * (((l ⟨(i.val - 18) % 3, by omega⟩ : ℝ)) : ℂ))
      * X (vIdx12 ⟨(i.val - 18) / 3, by omega⟩)
  else if _h6 : i.val < 30 then
    -C (((∑ j : Fin 3, (l j) ^ 2 : ℝ)) : ℂ) * X (vIdx12 ⟨i.val - 27, by omega⟩)
  else if h7 : i.val < 33 then X (qIdx12 ⟨i.val - 30, by omega⟩)
  else 0

/-- Reindex a one-parcel reduced polynomial into the `p`-th parcel's block. -/
def lagLift (p : Fin n) : MvPolynomial (Fin 12) ℂ →+* MvPolynomial (Fin (n * 12)) ℂ :=
  MvPolynomial.eval₂Hom (MvPolynomial.C) (fun j => X (lRedIdx p j))

/-- **The elimination `σ`** on the `n`-parcel Lagrangian ring. -/
def lagElimHom (l : Fin 3 → ℝ) (n : ℕ) :
    MvPolynomial (Fin (n * 36)) ℂ →+* MvPolynomial (Fin (n * 12)) ℂ :=
  MvPolynomial.eval₂Hom (MvPolynomial.C)
    (fun s => lagLift (finProdFinEquiv.symm s).1 (lagElimCoord l (finProdFinEquiv.symm s).2))

@[simp] theorem lagLift_X (p : Fin n) (j : Fin 12) : lagLift p (X j) = X (lRedIdx p j) :=
  MvPolynomial.eval₂Hom_X' _ _ j

@[simp] theorem lagLift_C (p : Fin n) (c : ℂ) : lagLift p (C c) = C c := by
  rw [lagLift, MvPolynomial.eval₂Hom_C]

theorem lagElimHom_X (l : Fin 3 → ℝ) (n : ℕ) (s : Fin (n * 36)) :
    lagElimHom l n (X s)
      = lagLift (finProdFinEquiv.symm s).1 (lagElimCoord l (finProdFinEquiv.symm s).2) :=
  MvPolynomial.eval₂Hom_X' _ _ s

theorem lagElimHom_C (l : Fin 3 → ℝ) (n : ℕ) (c : ℂ) :
    lagElimHom l n (C c : MvPolynomial (Fin (n * 36)) ℂ)
      = (C c : MvPolynomial (Fin (n * 12)) ℂ) :=
  MvPolynomial.eval₂Hom_C _ _ c

/-! ## 2. The coordinate values of `σ` -/

@[simp] theorem lagElimCoord_xiIdx (l : Fin 3 → ℝ) (i : Fin 3) :
    lagElimCoord l (xiIdx i) = X (xiIdx12 i) := by
  have h : (xiIdx i).val < 3 := i.isLt
  rw [lagElimCoord, dif_pos h]
  rfl

@[simp] theorem lagElimCoord_vIdx (l : Fin 3 → ℝ) (i : Fin 3) :
    lagElimCoord l (vIdx i) = X (vIdx12 i) := by
  have hv : (vIdx i).val = 3 + i.val := rfl
  have h1 : ¬ (vIdx i).val < 3 := by rw [hv]; omega
  have h2 : (vIdx i).val < 6 := by rw [hv]; omega
  have hlt : (vIdx i).val - 3 < 3 := by omega
  rw [lagElimCoord, dif_neg h1, dif_pos h2]
  have hx : (⟨(vIdx i).val - 3, hlt⟩ : Fin 3) = i := by
    apply Fin.ext
    change (vIdx i).val - 3 = i.val
    rw [hv]; omega
  simp only [hx]

@[simp] theorem lagElimCoord_accIdx (l : Fin 3 → ℝ) (i : Fin 3) :
    lagElimCoord l (accIdx i) = X (accIdx12 i) := by
  have hv : (accIdx i).val = 6 + i.val := rfl
  have h1 : ¬ (accIdx i).val < 3 := by rw [hv]; omega
  have h2 : ¬ (accIdx i).val < 6 := by rw [hv]; omega
  have h3 : (accIdx i).val < 9 := by rw [hv]; omega
  have hlt : (accIdx i).val - 6 < 3 := by omega
  rw [lagElimCoord, dif_neg h1, dif_neg h2, dif_pos h3]
  have hx : (⟨(accIdx i).val - 6, hlt⟩ : Fin 3) = i := by
    apply Fin.ext
    change (accIdx i).val - 6 = i.val
    rw [hv]; omega
  simp only [hx]

@[simp] theorem lagElimCoord_qIdx (l : Fin 3 → ℝ) (i : Fin 3) :
    lagElimCoord l (qIdx i) = X (qIdx12 i) := by
  have hv : (qIdx i).val = 30 + i.val := rfl
  have h1 : ¬ (qIdx i).val < 3 := by rw [hv]; omega
  have h2 : ¬ (qIdx i).val < 6 := by rw [hv]; omega
  have h3 : ¬ (qIdx i).val < 9 := by rw [hv]; omega
  have h4 : ¬ (qIdx i).val < 18 := by rw [hv]; omega
  have h5 : ¬ (qIdx i).val < 27 := by rw [hv]; omega
  have h6 : ¬ (qIdx i).val < 30 := by rw [hv]; omega
  have h7 : (qIdx i).val < 33 := by rw [hv]; omega
  have hlt : (qIdx i).val - 30 < 3 := by omega
  rw [lagElimCoord, dif_neg h1, dif_neg h2, dif_neg h3, dif_neg h4, dif_neg h5, dif_neg h6,
    dif_pos h7]
  have hx : (⟨(qIdx i).val - 30, hlt⟩ : Fin 3) = i := by
    apply Fin.ext
    change (qIdx i).val - 30 = i.val
    rw [hv]; omega
  simp only [hx]

@[simp] theorem lagElimCoord_yIdx (l : Fin 3 → ℝ) (j : Fin 3) :
    lagElimCoord l (yIdx j) = 0 := by
  have hv : (yIdx j).val = 33 + j.val := rfl
  have h1 : ¬ (yIdx j).val < 3 := by rw [hv]; omega
  have h2 : ¬ (yIdx j).val < 6 := by rw [hv]; omega
  have h3 : ¬ (yIdx j).val < 9 := by rw [hv]; omega
  have h4 : ¬ (yIdx j).val < 18 := by rw [hv]; omega
  have h5 : ¬ (yIdx j).val < 27 := by rw [hv]; omega
  have h6 : ¬ (yIdx j).val < 30 := by rw [hv]; omega
  have h7 : ¬ (yIdx j).val < 33 := by rw [hv]; omega
  rw [lagElimCoord, dif_neg h1, dif_neg h2, dif_neg h3, dif_neg h4, dif_neg h5, dif_neg h6,
    dif_neg h7]

/-- **The deformation gradient becomes the rank-one matrix `ℓ ⊗ ξ`** — the source of the degeneracy
proved in §4. -/
theorem lagElimCoord_fIdx (l : Fin 3 → ℝ) (i j : Fin 3) :
    lagElimCoord l (fIdx i j) = C (Complex.I * (((l j : ℝ)) : ℂ)) * X (xiIdx12 i) := by
  have hi : i.val < 3 := i.isLt
  have hj : j.val < 3 := j.isLt
  have hv : (fIdx i j).val = 9 + 3 * i.val + j.val := rfl
  have h1 : ¬ (fIdx i j).val < 3 := by omega
  have h2 : ¬ (fIdx i j).val < 6 := by omega
  have h3 : ¬ (fIdx i j).val < 9 := by omega
  have h4 : (fIdx i j).val < 18 := by omega
  have hsub : ((fIdx i j).val - 9) = 3 * i.val + j.val := by omega
  have hmod : (3 * i.val + j.val) % 3 = j.val := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hj]
  have hdiv : (3 * i.val + j.val) / 3 = i.val := by
    rw [Nat.mul_add_div (by norm_num : 0 < 3), Nat.div_eq_of_lt hj, Nat.add_zero]
  rw [lagElimCoord, dif_neg h1, dif_neg h2, dif_neg h3, dif_pos h4]
  simp only [hsub, hmod, hdiv, Fin.eta]

/-- **The velocity gradient becomes `i ℓ_j v_i`.** -/
theorem lagElimCoord_vgIdx (l : Fin 3 → ℝ) (i j : Fin 3) :
    lagElimCoord l (vgIdx i j) = C (Complex.I * (((l j : ℝ)) : ℂ)) * X (vIdx12 i) := by
  have hi : i.val < 3 := i.isLt
  have hj : j.val < 3 := j.isLt
  have hv : (vgIdx i j).val = 18 + 3 * i.val + j.val := rfl
  have h1 : ¬ (vgIdx i j).val < 3 := by omega
  have h2 : ¬ (vgIdx i j).val < 6 := by omega
  have h3 : ¬ (vgIdx i j).val < 9 := by omega
  have h4 : ¬ (vgIdx i j).val < 18 := by omega
  have h5 : (vgIdx i j).val < 27 := by omega
  have hsub : ((vgIdx i j).val - 18) = 3 * i.val + j.val := by omega
  have hmod : (3 * i.val + j.val) % 3 = j.val := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hj]
  have hdiv : (3 * i.val + j.val) / 3 = i.val := by
    rw [Nat.mul_add_div (by norm_num : 0 < 3), Nat.div_eq_of_lt hj, Nat.add_zero]
  rw [lagElimCoord, dif_neg h1, dif_neg h2, dif_neg h3, dif_neg h4, dif_pos h5]
  simp only [hsub, hmod, hdiv, Fin.eta]

/-- **The viscous coordinate becomes `−|ℓ|² v_i`.** -/
theorem lagElimCoord_sIdx (l : Fin 3 → ℝ) (i : Fin 3) :
    lagElimCoord l (sIdx i)
      = -C (((∑ j : Fin 3, (l j) ^ 2 : ℝ)) : ℂ) * X (vIdx12 i) := by
  have hv : (sIdx i).val = 27 + i.val := rfl
  have h1 : ¬ (sIdx i).val < 3 := by rw [hv]; omega
  have h2 : ¬ (sIdx i).val < 6 := by rw [hv]; omega
  have h3 : ¬ (sIdx i).val < 9 := by rw [hv]; omega
  have h4 : ¬ (sIdx i).val < 18 := by rw [hv]; omega
  have h5 : ¬ (sIdx i).val < 27 := by rw [hv]; omega
  have h6 : (sIdx i).val < 30 := by rw [hv]; omega
  have hlt3 : (sIdx i).val - 27 < 3 := by omega
  rw [lagElimCoord, dif_neg h1, dif_neg h2, dif_neg h3, dif_neg h4, dif_neg h5, dif_pos h6]
  have hx : (⟨(sIdx i).val - 27, hlt3⟩ : Fin 3) = i := by
    apply Fin.ext
    change (sIdx i).val - 27 = i.val
    rw [hv]; omega
  simp only [hx]

/-! ## 3. The lifted substitution on the coordinates -/

theorem lagElimHom_X_xiIdx (l : Fin 3 → ℝ) (n : ℕ) (p : Fin n) (i : Fin 3) :
    lagElimHom l n (X (ycoord p (xiIdx i))) = X (lRedIdx p (xiIdx12 i)) := by
  simp only [lagElimHom_X, ycoord, Equiv.symm_apply_apply, lagElimCoord_xiIdx, lagLift_X, lRedIdx]

theorem lagElimHom_X_vIdx (l : Fin 3 → ℝ) (n : ℕ) (p : Fin n) (i : Fin 3) :
    lagElimHom l n (X (ycoord p (vIdx i))) = X (lRedIdx p (vIdx12 i)) := by
  simp only [lagElimHom_X, ycoord, Equiv.symm_apply_apply, lagElimCoord_vIdx, lagLift_X, lRedIdx]

theorem lagElimHom_X_accIdx (l : Fin 3 → ℝ) (n : ℕ) (p : Fin n) (i : Fin 3) :
    lagElimHom l n (X (ycoord p (accIdx i))) = X (lRedIdx p (accIdx12 i)) := by
  simp only [lagElimHom_X, ycoord, Equiv.symm_apply_apply, lagElimCoord_accIdx, lagLift_X, lRedIdx]

theorem lagElimHom_X_qIdx (l : Fin 3 → ℝ) (n : ℕ) (p : Fin n) (i : Fin 3) :
    lagElimHom l n (X (ycoord p (qIdx i))) = X (lRedIdx p (qIdx12 i)) := by
  simp only [lagElimHom_X, ycoord, Equiv.symm_apply_apply, lagElimCoord_qIdx, lagLift_X, lRedIdx]

theorem lagElimHom_X_fIdx (l : Fin 3 → ℝ) (n : ℕ) (p : Fin n) (i j : Fin 3) :
    lagElimHom l n (X (ycoord p (fIdx i j)))
      = C (Complex.I * (((l j : ℝ)) : ℂ)) * X (lRedIdx p (xiIdx12 i)) := by
  simp only [lagElimHom_X, ycoord, Equiv.symm_apply_apply, lagElimCoord_fIdx, map_mul, lagLift_C,
    lagLift_X, lRedIdx]

theorem lagElimHom_X_vgIdx (l : Fin 3 → ℝ) (n : ℕ) (p : Fin n) (i j : Fin 3) :
    lagElimHom l n (X (ycoord p (vgIdx i j)))
      = C (Complex.I * (((l j : ℝ)) : ℂ)) * X (lRedIdx p (vIdx12 i)) := by
  simp only [lagElimHom_X, ycoord, Equiv.symm_apply_apply, lagElimCoord_vgIdx, map_mul, lagLift_C,
    lagLift_X, lRedIdx]

theorem lagElimHom_X_sIdx (l : Fin 3 → ℝ) (n : ℕ) (p : Fin n) (i : Fin 3) :
    lagElimHom l n (X (ycoord p (sIdx i)))
      = -C (((∑ j : Fin 3, (l j) ^ 2 : ℝ)) : ℂ) * X (lRedIdx p (vIdx12 i)) := by
  simp only [lagElimHom_X, ycoord, Equiv.symm_apply_apply, lagElimCoord_sIdx, map_mul, map_neg,
    lagLift_C, lagLift_X, lRedIdx]

theorem lagElimHom_X_yIdx (l : Fin 3 → ℝ) (n : ℕ) (p : Fin n) (j : Fin 3) :
    lagElimHom l n (X (ycoord p (yIdx j))) = 0 := by
  simp only [lagElimHom_X, ycoord, Equiv.symm_apply_apply, lagElimCoord_yIdx, map_zero]

/-! ## 4. The degeneracy: rank one kills the cofactor and the determinant -/

/-- **The `2 × 2` minors of a rank-one matrix vanish**: with `F_{rc} = b_c ζ_r`,
`b_{c₁}ζ_{r₁}·b_{c₂}ζ_{r₂} − b_{c₂}ζ_{r₁}·b_{c₁}ζ_{r₂} = 0`. -/
theorem rankOne_cof_zero (b ζ : Fin 3 → MvPolynomial (Fin (n * 12)) ℂ) (i j : Fin 3) :
    (b (cyc j 1) * ζ (cyc i 1)) * (b (cyc j 2) * ζ (cyc i 2))
      + (-1) * ((b (cyc j 2) * ζ (cyc i 1)) * (b (cyc j 1) * ζ (cyc i 2))) = 0 := by
  ring

/-- **The eliminated cofactor is zero.** -/
theorem lagElimSubst_cofPoly (l : Fin 3 → ℝ) (n : ℕ) (p : Fin n) (i j : Fin 3) :
    lagElimHom l n (cofPoly p i j) = 0 := by
  have h := rankOne_cof_zero (n := n) (fun c => C (Complex.I * (((l c : ℝ)) : ℂ)))
    (fun r => X (lRedIdx p (xiIdx12 r))) i j
  simpa only [cofPoly, map_add, map_mul, lagElimHom_C, lagElimHom_X_fIdx,
    C_neg_one_real n] using h

/-- **The Piola pressure term is annihilated by the elimination** — the pressure coupling of the
material momentum equation does not survive it. -/
theorem lagElimSubst_piola (l : Fin 3 → ℝ) (n : ℕ) (p : Fin n) (i : Fin 3) :
    lagElimHom l n (∑ j : Fin 3, cofPoly p j i * X (ycoord p (qIdx j))) = 0 := by
  rw [map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [map_mul, lagElimSubst_cofPoly, zero_mul]

/-- **The determinant of the rank-one deformation gradient vanishes.** -/
theorem lagElimSubst_detPoly (l : Fin 3 → ℝ) (n : ℕ) (p : Fin n) :
    lagElimHom l n (detPoly p) = 0 := by
  rw [detPoly, map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [map_mul, lagElimSubst_cofPoly, mul_zero]

/-- **The volume constraint collapses to the constant `−1`**: `σ(det F − 1) = −1`, a constraint with
no field content. -/
theorem lagElimSubst_volumePoly (l : Fin 3 → ℝ) (n : ℕ) (p : Fin n) :
    lagElimHom l n (volumePoly p) = -1 := by
  rw [volumePoly, map_add, lagElimSubst_detPoly, zero_add, lagElimHom_C, C_neg_one_real n]

/-- Hence the eliminated volume square is the constant `1`: no Friedrichs square can be built from
it, and it cannot be the source of the pressure. -/
theorem lagElimSubst_volumePoly_sq (l : Fin 3 → ℝ) (n : ℕ) (p : Fin n) :
    (lagElimHom l n (volumePoly p)) ^ 2 = 1 := by
  rw [lagElimSubst_volumePoly]
  ring

/-- **The eliminated momentum equation**: with the Piola term gone, `σ(R_i) = a_i + |ℓ|² v_i` — the
material acceleration plus the viscous term, and no pressure. -/
theorem lagElimSubst_lagResPoly (l : Fin 3 → ℝ) (n : ℕ) (p : Fin n) (i : Fin 3) :
    lagElimHom l n (lagResPoly p i)
      = X (lRedIdx p (accIdx12 i))
        + C (((∑ j : Fin 3, (l j) ^ 2 : ℝ)) : ℂ) * X (lRedIdx p (vIdx12 i)) := by
  simp only [lagResPoly, map_add, map_mul, lagElimHom_C, C_neg_one_real n,
    lagElimHom_X_accIdx, lagElimHom_X_sIdx, lagElimSubst_piola, add_zero]
  ring

end

end BookProof.NsLagFourier


