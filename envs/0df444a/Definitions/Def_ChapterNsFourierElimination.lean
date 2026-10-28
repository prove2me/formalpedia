-- Prove2me | Definitions.Def_ChapterNsFourierElimination
-- name    : ChapterNsFourierElimination
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-27T13:24:24.806123+00:00
-- url     : https://prove2.me/theorems/92f2b9ca-63c4-4d98-b356-ff30bacd9473
-- title:
--   The Lean 4 theorem `realCoeff_realConst` in the `?` chapter of the timepiece formalization
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterNsFourierElimination.lean`): generated def bundle for ChapterNsFourierElimination. See BookProof/ChapterNsFourierElimination.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNsFourierElimination.lean

import Theorems.Thm_BookProof_YangMillsHermite_starP_mul
import Theorems.Thm_BookProof_YangMillsHermite_mulOp_apply
import Theorems.Thm_BookProof_YangMillsHermite_CoreRep_coe_op
import Theorems.Thm_BookProof_YangMillsHermite_CoreRep_coe_symm
import Theorems.Thm_BookProof_YangMillsHermite_inner_pgLp_pgLp
import Theorems.Thm_BookProof_QgOuterFockFL_Comparison_essentiallySelfAdjointOn
import Theorems.Thm_BookProof_YangMillsHermite_RealCoeff_mul

import Theorems.Thm_BookProof_YangMillsHermite_RealCoeff_sum

import Theorems.Thm_BookProof_YangMillsHermite_realCoeff_X

import Theorems.Thm_BookProof_YangMillsHermite_CoreRep_symmetricOn_op

import Theorems.Thm_BookProof_YangMillsHermite_mulOp_polySym

import Theorems.Thm_BookProof_YangMillsHermite_RealCoeff_add







import Theorems.Thm_BookProof_YangMillsHermite_starP_C


import Theorems.Thm_BookProof_YangMillsHermite_momOp_polySym

import Definitions.Def_ChapterNavierStokesFullEulerianFock
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterQgOuterFockEsa
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterYangMillsHermite
import Mathlib


/-!
# Fourier elimination of the derivative variables — the reduced Eulerian Navier–Stokes sector

Stage 1 of the momentum-space (Fourier-elimination) route of `CONSOLIDATED_PLAN.md`
(§“Latest wave — 2026-09-15”, plan items 1–2; staged list of
`DESIGN_COMPARISON_N_20260915.md` §5.5 items 1–2).

On a mode of momentum `k` the auxiliary jet coordinates are **eliminated** (not gauge-fixed):

```
σ :  u_{i,j} ↦ i k_j u_i ,   w_i ↦ −|k|² u_i ,   y_j ↦ 0 ,   u_i ↦ u_i ,   q_i ↦ q_i ,
```

so the sector lives on **six** coordinates per parcel (`u_i`, `q_i`).  The elimination is applied
**inside the squares of every constraint form, to both of its real parts**: a substituted form is
complex, `σ(Φ_r) = Re σ(Φ_r) + i·Im σ(Φ_r)`, and each part is real-coefficient, hence a symmetric
multiplication form whose square is positive — which is the whole point of the positive-completion
route: the residual

```
σ(R_i) = i (k·u) u_i + q_i + ν|k|² u_i        (quadratic — never a cubic symbol),
σ(Σ_j u_{j,j}) = i (k·u)                      (linear),
```

the two facts `nsElimSubst_resPoly` / `nsElimSubst_divPoly` below.  Splitting
`σ(R_i) = I·Im + Re` into its real-coefficient parts `Re = q_i + ν|k|² u_i` and `Im = (k·u) u_i`,
the reduced one-particle Hamiltonian is again a positive sum of Weyl-ordered squares built with the
same `weylOp` as the full Eulerian sector — and this is where the reduced model is *defined*, since
the outer-Fock Hamiltonian is its particle-number-conserving second quantization `dΓ(H₁)` and not
another sum of squares — and it keeps the nonlinearity **in full**: squaring both real
parts puts `(Re)² = (q_i + ν|k|² u_i)²` *and* `(Im)² = ((k·u) u_i)²` inside the Hamiltonian, so the
advection is one of the squares and the reduced *sector* Hamiltonian is quartic, unlike the
real-part-only truncation.  The skewness of `mulOp (i·Im)` (below, §7) is a statement about the
operator of the *equation*: it is what makes the **coefficientwise** product of the complex form
unusable, and it is also why `L*L` and the two-square form are the same *form* (the skew cross term
of `L*L` contributes nothing).  **Plan of record, 2026‑09‑17b:** the honest Hamiltonian is the
modulus-square one, `N` is free, and the convenient choice `N = ι(Friedrichs(H_n^red))` makes the
commutator vanish (`c = 0`).  **The delta is closed:** `redFieldN` below carries the honest family
`redFormPoly` — the real and imaginary parts of *every* surviving substituted form, i.e. the three
real residual parts `q_i + ν|k|² u_i`, the three advection parts `(k·u) u_i` and the eliminated
incompressibility `k·u`, seven forms per parcel — so `redHam` is the full modulus-square
Hamiltonian, quartic and interacting (`redFieldN_advect` exhibits the advection as one of the
squares), and `redHam_quadForm_nonneg` / `redHam_friedrichs_extension` hold for it unchanged.

Everything is `sorry`-free and `axiom`-free.
-/

namespace BookProof.NsFullEuler

open MvPolynomial
open BookProof.YangMillsHermite BookProof.YangMillsFriedrichs BookProof.FriedrichsExtension
open BookProof.HermiteProductCore BookProof.FarisLavine BookProof.DirectSumEsa
open BookProof.QgOuterFock BookProof.StoneBridge BookProof.QgOuterFockFL

noncomputable section

variable {n : ℕ}
variable {d : ℕ}
variable {D : Submodule ℂ (L2d d)}

/-! ## 1. The reduced coordinates and the substitution `σ` -/

/-- The reduced six-coordinate block of one parcel: `(u_0,u_1,u_2,q_0,q_1,q_2)`. -/
def redIdx (p : Fin n) (i : Fin 6) : Fin (n * 6) := finProdFinEquiv (p, i)

/-- One-parcel reduced coordinate `u_i` as a bare `Fin 6`. -/
abbrev ruIdx6 (i : Fin 3) : Fin 6 := ⟨i.val, by omega⟩

/-- One-parcel reduced coordinate `q_i` as a bare `Fin 6`. -/
abbrev rqIdx6 (i : Fin 3) : Fin 6 := ⟨3 + i.val, by omega⟩

/-- `u_i` inside the reduced block of the `p`-th parcel. -/
def ruIdx (p : Fin n) (i : Fin 3) : Fin (n * 6) := redIdx p (ruIdx6 i)

/-- `q_i` inside the reduced block of the `p`-th parcel. -/
def rqIdx (p : Fin n) (i : Fin 3) : Fin (n * 6) := redIdx p (rqIdx6 i)

/-- The elimination substitution on one parcel's 21 coordinates, as a polynomial in the six
reduced coordinates: `u_{i,j} ↦ i k_j u_i`, `w_i ↦ −|k|² u_i`, `y_j ↦ 0`, `u_i ↦ u_i`,
`q_i ↦ q_i`.  (The layout of `Fin 21` is that of `uIdx`/`dIdx`/`wIdx`/`qIdx`/`yIdx`.) -/
def nsElimCoord (k : Fin 3 → ℝ) (i : Fin 21) : MvPolynomial (Fin 6) ℂ :=
  if h : i.val < 3 then X (⟨i.val, by omega⟩ : Fin 6)
  else if h2 : i.val < 12 then
    C (Complex.I * (((k ⟨(i.val - 3) % 3, by omega⟩ : ℝ)) : ℂ))
      * X (⟨(i.val - 3) / 3, by omega⟩ : Fin 6)
  else if h3 : i.val < 15 then
    -C ((((∑ j : Fin 3, (k j) ^ 2 : ℝ))) : ℂ) * X (⟨i.val - 12, by omega⟩ : Fin 6)
  else if h4 : i.val < 18 then X (⟨3 + (i.val - 15), by omega⟩ : Fin 6)
  else 0

/-- Reindex a one-parcel reduced polynomial into the `p`-th parcel's block. -/
def liftParcel (p : Fin n) : MvPolynomial (Fin 6) ℂ →+* MvPolynomial (Fin (n * 6)) ℂ :=
  MvPolynomial.eval₂Hom (MvPolynomial.C) (fun j => X (redIdx p j))

/-- **The elimination `σ`** on the `n`-parcel polynomial ring, applied parcelwise. -/
def nsElimHom (k : Fin 3 → ℝ) (n : ℕ) :
    MvPolynomial (Fin (n * 21)) ℂ →+* MvPolynomial (Fin (n * 6)) ℂ :=
  MvPolynomial.eval₂Hom (MvPolynomial.C)
    (fun s => liftParcel (finProdFinEquiv.symm s).1 (nsElimCoord k (finProdFinEquiv.symm s).2))

/-! ## 2. One-parcel coordinate facts for `σ` -/

@[simp] theorem nsElimCoord_uIdx (k : Fin 3 → ℝ) (i : Fin 3) :
    nsElimCoord k (uIdx i) = X (ruIdx6 i) := by
  have h : (uIdx i).val < 3 := i.isLt
  rw [nsElimCoord, dif_pos h]
  rfl

theorem nsElimCoord_dIdx (k : Fin 3 → ℝ) (i j : Fin 3) :
    nsElimCoord k (dIdx i j)
      = C (Complex.I * (((k j : ℝ)) : ℂ)) * X (ruIdx6 i) := by
  have hi : i.val < 3 := i.isLt
  have hj : j.val < 3 := j.isLt
  have hv : (dIdx i j).val = 3 + 3 * i.val + j.val := rfl
  have h1 : ¬ (dIdx i j).val < 3 := by omega
  have h2 : (dIdx i j).val < 12 := by omega
  have hv' : (↑(dIdx i j) - 3) = 3 * i.val + j.val := by omega
  have hmod : (3 * i.val + j.val) % 3 = j.val := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hj]
  have hdiv : (3 * i.val + j.val) / 3 = i.val := by
    rw [Nat.mul_add_div (by norm_num : 0 < 3), Nat.div_eq_of_lt hj, Nat.add_zero]
  rw [nsElimCoord, dif_neg h1, dif_pos h2]
  have hk : (⟨(↑(dIdx i j) - 3) % 3, Nat.mod_lt _ (by norm_num)⟩ : Fin 3) = j := by
    apply Fin.ext
    change (↑(dIdx i j) - 3) % 3 = j.val
    rw [hv', hmod]
  have hx : (⟨(↑(dIdx i j) - 3) / 3, by omega⟩ : Fin 6) = ruIdx6 i := by
    apply Fin.ext
    change (↑(dIdx i j) - 3) / 3 = i.val
    rw [hv', hdiv]
  simp only [hk, hx]

@[simp] theorem nsElimCoord_wIdx (k : Fin 3 → ℝ) (i : Fin 3) :
    nsElimCoord k (wIdx i) = -C (((∑ j : Fin 3, (k j) ^ 2 : ℝ)) : ℂ) * X (ruIdx6 i) := by
  have h1 : ¬ (wIdx i).val < 3 := by rw [show (wIdx i).val = 12 + i.val from rfl]; omega
  have h2 : ¬ (wIdx i).val < 12 := by rw [show (wIdx i).val = 12 + i.val from rfl]; omega
  have h3 : (wIdx i).val < 15 := by rw [show (wIdx i).val = 12 + i.val from rfl]; omega
  have hv : (wIdx i).val = 12 + i.val := rfl
  rw [nsElimCoord, dif_neg h1, dif_neg h2, dif_pos h3]
  have hx : (⟨↑(wIdx i) - 12, by omega⟩ : Fin 6) = ruIdx6 i := by
    apply Fin.ext; simp only [hv]; omega
  simp only [hx]

@[simp] theorem nsElimCoord_qIdx (k : Fin 3 → ℝ) (i : Fin 3) :
    nsElimCoord k (qIdx i) = X (rqIdx6 i) := by
  have h1 : ¬ (qIdx i).val < 3 := by rw [show (qIdx i).val = 15 + i.val from rfl]; omega
  have h2 : ¬ (qIdx i).val < 12 := by rw [show (qIdx i).val = 15 + i.val from rfl]; omega
  have h3 : ¬ (qIdx i).val < 15 := by rw [show (qIdx i).val = 15 + i.val from rfl]; omega
  have h4 : (qIdx i).val < 18 := by rw [show (qIdx i).val = 15 + i.val from rfl]; omega
  have hv : (qIdx i).val = 15 + i.val := rfl
  rw [nsElimCoord, dif_neg h1, dif_neg h2, dif_neg h3, dif_pos h4]
  have hx : (⟨3 + (↑(qIdx i) - 15), by omega⟩ : Fin 6) = rqIdx6 i := by
    apply Fin.ext; simp only [hv]; omega
  simp only [hx]

@[simp] theorem nsElimCoord_yIdx (k : Fin 3 → ℝ) (j : Fin 3) :
    nsElimCoord k (yIdx j) = 0 := by
  have h1 : ¬ (yIdx j).val < 3 := by rw [show (yIdx j).val = 18 + j.val from rfl]; omega
  have h2 : ¬ (yIdx j).val < 12 := by rw [show (yIdx j).val = 18 + j.val from rfl]; omega
  have h3 : ¬ (yIdx j).val < 15 := by rw [show (yIdx j).val = 18 + j.val from rfl]; omega
  have h4 : ¬ (yIdx j).val < 18 := by rw [show (yIdx j).val = 18 + j.val from rfl]; omega
  rw [nsElimCoord, dif_neg h1, dif_neg h2, dif_neg h3, dif_neg h4]

/-! ## 3. The lifted substitution on the coordinate ring -/

@[simp] theorem liftParcel_X (p : Fin n) (j : Fin 6) : liftParcel p (X j) = X (redIdx p j) :=
  MvPolynomial.eval₂Hom_X' _ _ j

@[simp] theorem liftParcel_C (p : Fin n) (c : ℂ) : liftParcel p (C c) = C c := by
  rw [liftParcel, MvPolynomial.eval₂Hom_C]

theorem nsElimHom_X (k : Fin 3 → ℝ) (n : ℕ) (s : Fin (n * 21)) :
    nsElimHom k n (X s)
      = liftParcel (finProdFinEquiv.symm s).1 (nsElimCoord k (finProdFinEquiv.symm s).2) :=
  MvPolynomial.eval₂Hom_X' _ _ s

@[simp] theorem nsElimHom_X_u (k : Fin 3 → ℝ) (n : ℕ) (p : Fin n) (i : Fin 3) :
    nsElimHom k n (X (ycoord p (uIdx i))) = X (ruIdx p i) := by
  simp only [nsElimHom_X, ycoord, Equiv.symm_apply_apply, nsElimCoord_uIdx, liftParcel_X, ruIdx]

@[simp] theorem nsElimHom_X_d (k : Fin 3 → ℝ) (n : ℕ) (p : Fin n) (i j : Fin 3) :
    nsElimHom k n (X (ycoord p (dIdx i j)))
      = C (Complex.I * (((k j : ℝ)) : ℂ)) * X (ruIdx p i) := by
  simp only [nsElimHom_X, ycoord, Equiv.symm_apply_apply, nsElimCoord_dIdx, map_mul,
    liftParcel_C, liftParcel_X, ruIdx]

@[simp] theorem nsElimHom_X_w (k : Fin 3 → ℝ) (n : ℕ) (p : Fin n) (i : Fin 3) :
    nsElimHom k n (X (ycoord p (wIdx i)))
      = -C (((∑ j : Fin 3, (k j) ^ 2 : ℝ)) : ℂ) * X (ruIdx p i) := by
  simp only [nsElimHom_X, ycoord, Equiv.symm_apply_apply, nsElimCoord_wIdx, map_mul, map_neg,
    liftParcel_C, liftParcel_X, ruIdx]

@[simp] theorem nsElimHom_X_q (k : Fin 3 → ℝ) (n : ℕ) (p : Fin n) (i : Fin 3) :
    nsElimHom k n (X (ycoord p (qIdx i))) = X (rqIdx p i) := by
  simp only [nsElimHom_X, ycoord, Equiv.symm_apply_apply, nsElimCoord_qIdx, liftParcel_X, rqIdx]

@[simp] theorem nsElimHom_X_y (k : Fin 3 → ℝ) (n : ℕ) (p : Fin n) (j : Fin 3) :
    nsElimHom k n (X (ycoord p (yIdx j))) = 0 := by
  simp only [nsElimHom_X, ycoord, Equiv.symm_apply_apply, nsElimCoord_yIdx, map_zero]

/-! ## 4. The substitution `σ` on the residual and on the divergence

The substitution is a *ring* map, so it commutes with sums and products; the whole content of the
elimination is that the Fourier symbols below come out **quadratic** — the derivative coordinates
`u_{i,j}` and `w_i`, which are what made the residual formally cubic in the field, are gone:

* `σ(u_j u_{i,j}) = i (k·u) u_i`  (`k·u = Σ_j k_j u_j`),
* `σ(q_i) = q_i`,  `σ(−ν w_i) = ν|k|² u_i`,
* `σ(Σ_j u_{j,j}) = i (k·u)`.

Splitting `σ(R_i) = i·(advection symbol) + (real symbol)`, each part is a *legitimate*
(real-coefficient, hence symmetric) multiplication form; multiplication by the **imaginary** part
`i (k·u) u_i` is **skew-adjoint** and its operator square is *negative*, which is what rules out the
**coefficientwise** product of the complex form.  It does **not** rule the advection out of the
Hamiltonian: the real polynomial `(k·u) u_i` has a symmetric operator, so the reduced *one-particle*
Hamiltonian of §5 squares it — `½ ((k·u)u_i)²` alongside `½(q_i + ν|k|²u_i)²` (plan of record
2026‑09‑17b) — and `N` is free, the convenient choice being the lifted Friedrichs extension of that
same one-particle Hamiltonian (`c = 0`), which the outer-Fock lift `dΓ(H₁)` of §6 carries
unchanged. -/

/-- The momentum scalar `k·u` in the reduced ring. -/
def fourierMomentum (k : Fin 3 → ℝ) : MvPolynomial (Fin 6) ℂ :=
  ∑ j : Fin 3, C (((k j : ℝ)) : ℂ) * X (ruIdx6 j)

/-- The real Fourier symbol `(k·u) u_i` of the advection `u_j ∂_j u_i`. -/
def fourierAdvect (k : Fin 3 → ℝ) (i : Fin 3) : MvPolynomial (Fin 6) ℂ :=
  fourierMomentum k * X (ruIdx6 i)

/-- The Fourier symbol `i (k·u)` of the incompressibility `Σ_j u_{j,j}`. -/
def fourierDiv (k : Fin 3 → ℝ) : MvPolynomial (Fin 6) ℂ :=
  C Complex.I * fourierMomentum k

/-- The real Fourier symbol `q_i + ν|k|² u_i` of the pressure-gradient and viscous parts of the
residual.  It has real coefficients, hence multiplication by it is symmetric. -/
def fourierVisc (nu : ℝ) (k : Fin 3 → ℝ) (i : Fin 3) : MvPolynomial (Fin 6) ℂ :=
  X (rqIdx6 i) + C (((nu * ∑ j : Fin 3, (k j) ^ 2 : ℝ)) : ℂ) * X (ruIdx6 i)

/-- A real constant is a real-coefficient polynomial in *any* reduced ring. -/
theorem realCoeff_realConst {m : ℕ} (c : ℝ) :
    RealCoeff (C ((c : ℝ) : ℂ) : MvPolynomial (Fin m) ℂ) := by
  rw [RealCoeff, starP_C, Complex.conj_ofReal]

theorem realCoeff_fourierMomentum (k : Fin 3 → ℝ) : RealCoeff (fourierMomentum k) :=
  RealCoeff.sum fun _ _ => (realCoeff_realConst (k _)).mul (realCoeff_X _)

theorem realCoeff_fourierAdvect (k : Fin 3 → ℝ) (i : Fin 3) :
    RealCoeff (fourierAdvect k i) :=
  (realCoeff_fourierMomentum k).mul (realCoeff_X _)

/-- The transfer weight `k ↦ k·u` is **linear in the momentum**. -/
theorem fourierMomentum_add (k k' : Fin 3 → ℝ) :
    fourierMomentum (k + k') = fourierMomentum k + fourierMomentum k' := by
  rw [fourierMomentum, fourierMomentum, fourierMomentum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Pi.add_apply, Complex.ofReal_add, map_add]
  ring

theorem fourierMomentum_smul (t : ℝ) (k : Fin 3 → ℝ) :
    fourierMomentum (t • k) = C ((t : ℝ) : ℂ) * fourierMomentum k := by
  rw [fourierMomentum, fourierMomentum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul, map_mul]
  ring

/-- **The advection symbol is the transfer-weight pairing** `Σ_j k_j (u_j u_i)`: the momentum of the
eliminated derivative is contracted with the product of the two velocity modes — the polynomial form
of the momentum-conservation convolution of the route. -/
theorem fourierAdvect_eq_transfer (k : Fin 3 → ℝ) (i : Fin 3) :
    fourierAdvect k i
      = ∑ j : Fin 3, C (((k j : ℝ)) : ℂ) * (X (ruIdx6 j) * X (ruIdx6 i)) := by
  rw [fourierAdvect, fourierMomentum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The transfer weight is **linear in the momentum**, hence so is the advection symbol. -/
theorem fourierAdvect_smul (t : ℝ) (k : Fin 3 → ℝ) (i : Fin 3) :
    fourierAdvect (t • k) i = C ((t : ℝ) : ℂ) * fourierAdvect k i := by
  rw [fourierAdvect, fourierAdvect, fourierMomentum_smul]
  ring

theorem realCoeff_fourierVisc (nu : ℝ) (k : Fin 3 → ℝ) (i : Fin 3) :
    RealCoeff (fourierVisc nu k i) :=
  (realCoeff_X _).add ((realCoeff_realConst _).mul (realCoeff_X _))

theorem nsElimHom_C (k : Fin 3 → ℝ) (n : ℕ) (c : ℂ) :
    nsElimHom k n (C c : MvPolynomial (Fin (n * 21)) ℂ)
      = (C c : MvPolynomial (Fin (n * 6)) ℂ) :=
  MvPolynomial.eval₂Hom_C _ _ c

/-- **The advection goes to `i (k·u) u_i`.** -/
theorem nsElimSubst_advect (k : Fin 3 → ℝ) (n : ℕ) (p : Fin n) (i : Fin 3) :
    nsElimHom k n (∑ j : Fin 3, X (ycoord p (uIdx j)) * X (ycoord p (dIdx i j)))
      = C Complex.I * liftParcel p (fourierAdvect k i) := by
  simp only [nsElimHom_X, ycoord, Equiv.symm_apply_apply, nsElimCoord_uIdx, nsElimCoord_dIdx,
    fourierAdvect, fourierMomentum, map_sum, map_mul, liftParcel_C, liftParcel_X]
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **The pressure gradient goes to `q_i`.** -/
theorem nsElimSubst_pressure (k : Fin 3 → ℝ) (n : ℕ) (p : Fin n) (i : Fin 3) :
    nsElimHom k n (X (ycoord p (qIdx i))) = liftParcel p (X (rqIdx6 i)) := by
  rw [nsElimHom_X_q, liftParcel_X, rqIdx]

/-- **The viscous term goes to `ν|k|² u_i`.** -/
theorem nsElimSubst_viscous (nu : ℝ) (k : Fin 3 → ℝ) (n : ℕ) (p : Fin n) (i : Fin 3) :
    nsElimHom k n (C (((-nu : ℝ)) : ℂ) * X (ycoord p (wIdx i)))
      = liftParcel p (C (((nu * ∑ j : Fin 3, (k j) ^ 2 : ℝ)) : ℂ) * X (ruIdx6 i)) := by
  have hcoef : (C (((-nu : ℝ)) : ℂ) : MvPolynomial (Fin (n * 6)) ℂ)
      * (-C (((∑ j : Fin 3, (k j) ^ 2 : ℝ)) : ℂ))
      = C (((nu * ∑ j : Fin 3, (k j) ^ 2 : ℝ)) : ℂ) := by
    rw [Complex.ofReal_neg, Complex.ofReal_mul, map_neg, map_mul]
    ring
  rw [map_mul, nsElimHom_C, nsElimHom_X_w, map_mul, liftParcel_C, liftParcel_X, ruIdx,
    ← mul_assoc, hcoef]

/-- **The elimination of the residual**: `σ(R_i) = i (k·u) u_i + q_i + ν|k|² u_i`.  The bracket is
quadratic in the six surviving coordinates — there is no cubic symbol, which is the point of the
substitution. -/
theorem nsElimSubst_resPoly (nu : ℝ) (k : Fin 3 → ℝ) (n : ℕ) (p : Fin n) (i : Fin 3) :
    nsElimHom k n (nsResPoly nu p i)
      = C Complex.I * liftParcel p (fourierAdvect k i) + liftParcel p (fourierVisc nu k i) := by
  rw [nsResPoly, map_add, map_add, nsElimSubst_advect, nsElimSubst_pressure,
    nsElimSubst_viscous, fourierVisc, map_add]
  ring

/-- **The elimination of incompressibility**: `σ(Σ_j u_{j,j}) = i (k·u)` — linear in the reduced
coordinates. -/
theorem nsElimSubst_divPoly (k : Fin 3 → ℝ) (n : ℕ) (p : Fin n) :
    nsElimHom k n (divPoly p) = liftParcel p (fourierDiv k) := by
  rw [divPoly, map_sum, fourierDiv, fourierMomentum, map_mul, liftParcel_C, map_sum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [nsElimHom_X_d, map_mul, liftParcel_C, liftParcel_X, ruIdx]
  ring

/-- **`i (k·u)` is the real momentum scalar times `i`**: the divergence symbol is the momentum
scalar, so the eliminated incompressibility is the constant-coefficient multiplier `i k·u`. -/
theorem fourierDiv_eq (k : Fin 3 → ℝ) :
    fourierDiv k = C Complex.I * fourierMomentum k := rfl

/-! ## 5. The reduced one-particle Hamiltonian: the sums of squares, the advection included

After the elimination a parcel has **six** canonical coordinates `(u_i, q_i)`.  The real part
`Re σ(R_i) = q_i + ν|k|² u_i` is a real-coefficient multiplication form, so the same `weylOp` that
builds the full Eulerian sector builds the reduced one, and its quadratic form is a sum of squares:
`H_n^red = ½ Σ_m π_m² + ½ Σ_r [(mulOp Re σ(Φ_r))² + (mulOp Im σ(Φ_r))²] ≥ 0` — both real parts of
**every** reduced form squared.  Level bookkeeping: `redHam nu k 1` is the reduced **one-particle**
Hamiltonian, and it — not the Fock operator — is where the choice of squared forms is made;
`redHam nu k n` is that one-particle operator summed over the `n` parcels, and §6's
`nsRedFullFockHam = dsOp (fun n => redHam nu k n)` is its particle-number-conserving second
quantization `dΓ(H₁)`, the lift taking no further square.  That
puts the advection **inside** a square — `½ ((k·u) u_i)²`, via `Im σ(R_i) = fourierAdvect`, whose
multiplication operator is symmetric (`realCoeff_fourierAdvect` + `mulOp_polySym`) — so the reduced
Hamiltonian is quartic and interacting, as Navier–Stokes requires; `N` is then free, and
`N = ι(Friedrichs(H_n^red))` makes the commutator vanish (`c = 0`).  The squared family is
`redFormPoly`: seven real-coefficient forms per parcel — `redVisc` (the real residual part),
`redAdvectPoly` (the advection, the imaginary residual part) and `redMomentumPoly` (the eliminated
incompressibility) — so nothing is dropped and nothing is demoted to a perturbation. -/

/-- The real reduced residual form of a parcel, in the six reduced coordinates. -/
def redVisc (nu : ℝ) (k : Fin 3 → ℝ) (n : ℕ) (p : Fin n) (i : Fin 3) :
    MvPolynomial (Fin (n * 6)) ℂ :=
  X (rqIdx p i) + C (((nu * ∑ j : Fin 3, (k j) ^ 2 : ℝ)) : ℂ) * X (ruIdx p i)

/-- The reduced residual form is the real part of `σ(R_i)`: the lifted `fourierVisc`. -/
theorem redVisc_eq_liftParcel (nu : ℝ) (k : Fin 3 → ℝ) (n : ℕ) (p : Fin n) (i : Fin 3) :
    redVisc nu k n p i = liftParcel p (fourierVisc nu k i) := by
  simp only [redVisc, fourierVisc, map_add, map_mul, liftParcel_C, liftParcel_X, rqIdx, ruIdx]

/-- **The reduced residual form is real-coefficient**, hence a symmetric multiplication form. -/
theorem realCoeff_redVisc (nu : ℝ) (k : Fin 3 → ℝ) (n : ℕ) (p : Fin n) (i : Fin 3) :
    RealCoeff (redVisc nu k n p i) :=
  (realCoeff_X _).add ((realCoeff_realConst _).mul (realCoeff_X _))

/-- The lifted **real** advection symbol `(k·u) u_i` of the `i`-th residual of the `p`-th parcel —
the *imaginary* part `Im σ(R_i)` of the eliminated residual, written as a real-coefficient
polynomial. -/
def redAdvectPoly (k : Fin 3 → ℝ) (n : ℕ) (p : Fin n) (i : Fin 3) :
    MvPolynomial (Fin (n * 6)) ℂ :=
  ∑ j : Fin 3, C (((k j : ℝ)) : ℂ) * (X (ruIdx p j) * X (ruIdx p i))

theorem realCoeff_redAdvectPoly (k : Fin 3 → ℝ) (n : ℕ) (p : Fin n) (i : Fin 3) :
    RealCoeff (redAdvectPoly k n p i) :=
  RealCoeff.sum fun j _ =>
    (realCoeff_realConst (k j)).mul ((realCoeff_X _).mul (realCoeff_X _))

/-- The lifted real advection symbol is the lift of the one-parcel `fourierAdvect`. -/
theorem redAdvectPoly_eq_liftParcel (k : Fin 3 → ℝ) (n : ℕ) (p : Fin n) (i : Fin 3) :
    redAdvectPoly k n p i = liftParcel p (fourierAdvect k i) := by
  rw [redAdvectPoly, fourierAdvect_eq_transfer, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [map_mul, liftParcel_C, liftParcel_X, ruIdx]

/-- The lifted momentum scalar `k·u` of the `p`-th parcel — the *imaginary* part of the eliminated
incompressibility `σ(Σ_j u_{j,j}) = i (k·u)` (its real part is zero). -/
def redMomentumPoly (k : Fin 3 → ℝ) (n : ℕ) (p : Fin n) : MvPolynomial (Fin (n * 6)) ℂ :=
  ∑ j : Fin 3, C (((k j : ℝ)) : ℂ) * X (ruIdx p j)

theorem realCoeff_redMomentumPoly (k : Fin 3 → ℝ) (n : ℕ) (p : Fin n) :
    RealCoeff (redMomentumPoly k n p) :=
  RealCoeff.sum fun j _ => (realCoeff_realConst (k j)).mul (realCoeff_X _)

/-- The lifted momentum scalar is the lift of the one-parcel `fourierMomentum`. -/
theorem redMomentumPoly_eq_liftParcel (k : Fin 3 → ℝ) (n : ℕ) (p : Fin n) :
    redMomentumPoly k n p = liftParcel p (fourierMomentum k) := by
  rw [redMomentumPoly, fourierMomentum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [map_mul, liftParcel_C, liftParcel_X, ruIdx]

/-- Index of the real part `Re σ(R_i) = q_i + ν|k|² u_i` of the `i`-th residual among the seven
forms of a parcel. -/
abbrev reIdx7 (i : Fin 3) : Fin 7 := ⟨i.val, by omega⟩

/-- Index of the imaginary part `Im σ(R_i) = (k·u) u_i` — the **advection** — of the `i`-th
residual among the seven forms of a parcel. -/
abbrev imIdx7 (i : Fin 3) : Fin 7 := ⟨3 + i.val, by omega⟩

/-- Index of the eliminated incompressibility `Im σ(Σ_j u_{j,j}) = k·u` among the seven forms of a
parcel. -/
abbrev divIdx7 : Fin 7 := ⟨6, by omega⟩

/-- **The honest reduced constraint family of one parcel**: the real and imaginary parts of *every*
surviving substituted form — the three real residual parts `q_i + ν|k|² u_i`, the three advection
parts `(k·u) u_i`, and the eliminated incompressibility `k·u`.  (The `y`-gauge forms contribute
nothing, `σ(y_j) = 0`, and the real part of the incompressibility is zero.)  Each member is
real-coefficient, hence a symmetric multiplication form whose square is positive. -/
def redFormPoly (nu : ℝ) (k : Fin 3 → ℝ) (n : ℕ) (p : Fin n) (r : Fin 7) :
    MvPolynomial (Fin (n * 6)) ℂ :=
  if h : r.val < 3 then redVisc nu k n p ⟨r.val, h⟩
  else if h2 : r.val < 6 then redAdvectPoly k n p ⟨r.val - 3, by omega⟩
  else redMomentumPoly k n p

@[simp] theorem redFormPoly_re (nu : ℝ) (k : Fin 3 → ℝ) (n : ℕ) (p : Fin n) (i : Fin 3) :
    redFormPoly nu k n p (reIdx7 i) = redVisc nu k n p i := by
  have h : (reIdx7 i).val < 3 := i.isLt
  rw [redFormPoly, dif_pos h]

@[simp] theorem redFormPoly_im (nu : ℝ) (k : Fin 3 → ℝ) (n : ℕ) (p : Fin n) (i : Fin 3) :
    redFormPoly nu k n p (imIdx7 i) = redAdvectPoly k n p i := by
  have hi : i.val < 3 := i.isLt
  have hv : (imIdx7 i).val = 3 + i.val := rfl
  have h1 : ¬ (imIdx7 i).val < 3 := by omega
  have h2 : (imIdx7 i).val < 6 := by omega
  have hsub : (imIdx7 i).val - 3 = i.val := by omega
  rw [redFormPoly, dif_neg h1, dif_pos h2]
  simp only [hsub, Fin.eta]

@[simp] theorem redFormPoly_div (nu : ℝ) (k : Fin 3 → ℝ) (n : ℕ) (p : Fin n) :
    redFormPoly nu k n p divIdx7 = redMomentumPoly k n p := by
  have h1 : ¬ (divIdx7).val < 3 := by norm_num
  have h2 : ¬ (divIdx7).val < 6 := by norm_num
  rw [redFormPoly, dif_neg h1, dif_neg h2]

/-- **Every member of the reduced family is real-coefficient**, hence its multiplication operator is
symmetric and its square is a positive summand of the Hamiltonian. -/
theorem realCoeff_redFormPoly (nu : ℝ) (k : Fin 3 → ℝ) (n : ℕ) (p : Fin n) (r : Fin 7) :
    RealCoeff (redFormPoly nu k n p r) := by
  rw [redFormPoly]
  split
  · exact realCoeff_redVisc nu k n p _
  · split
    · exact realCoeff_redAdvectPoly k n p _
    · exact realCoeff_redMomentumPoly k n p

/-- The momenta of the six reduced coordinates of each parcel. -/
def redPiN (n : ℕ) (m : Fin (n * 6)) :
    polyGaussCore (d := n * 6) →ₗ[ℂ] polyGaussCore (d := n * 6) :=
  (coreRepPoly (n * 6)).op
    (momOp (redIdx (finProdFinEquiv.symm m).1 (finProdFinEquiv.symm m).2))

/-- The reduced constraint (multiplication) forms of the `n`-parcel sector: the **seven** forms of
each parcel — the real and imaginary parts of every surviving substituted form (three real residual
parts, three advection parts and the eliminated incompressibility). -/
def redFieldN (nu : ℝ) (k : Fin 3 → ℝ) (n : ℕ) (m : Fin (n * 7)) :
    polyGaussCore (d := n * 6) →ₗ[ℂ] polyGaussCore (d := n * 6) :=
  (coreRepPoly (n * 6)).op
    (mulOp (redFormPoly nu k n (finProdFinEquiv.symm m).1 (finProdFinEquiv.symm m).2))

/-- The real residual part `q_i + ν|k|² u_i` is one of the squared forms. -/
theorem redFieldN_re (nu : ℝ) (k : Fin 3 → ℝ) (n : ℕ) (p : Fin n) (i : Fin 3) :
    redFieldN nu k n (finProdFinEquiv (p, reIdx7 i))
      = (coreRepPoly (n * 6)).op (mulOp (redVisc nu k n p i)) := by
  simp only [redFieldN, Equiv.symm_apply_apply, redFormPoly_re]

/-- **The advection is one of the squared forms** — the reduced Hamiltonian is quartic and keeps
the Navier–Stokes nonlinearity, no term being demoted to a perturbation. -/
theorem redFieldN_advect (nu : ℝ) (k : Fin 3 → ℝ) (n : ℕ) (p : Fin n) (i : Fin 3) :
    redFieldN nu k n (finProdFinEquiv (p, imIdx7 i))
      = (coreRepPoly (n * 6)).op (mulOp (redAdvectPoly k n p i)) := by
  simp only [redFieldN, Equiv.symm_apply_apply, redFormPoly_im]

/-- The eliminated incompressibility `k·u` contributes its own square. -/
theorem redFieldN_div (nu : ℝ) (k : Fin 3 → ℝ) (n : ℕ) (p : Fin n) :
    redFieldN nu k n (finProdFinEquiv (p, divIdx7))
      = (coreRepPoly (n * 6)).op (mulOp (redMomentumPoly k n p)) := by
  simp only [redFieldN, Equiv.symm_apply_apply, redFormPoly_div]

theorem redPiN_symmetricOn (n : ℕ) (m : Fin (n * 6)) :
    SymmetricOn (polyGaussCore (d := n * 6))
      ((polyGaussCore (d := n * 6)).subtype.comp (redPiN n m)) :=
  (coreRepPoly (n * 6)).symmetricOn_op (momOp_polySym _)

theorem redFieldN_symmetricOn (nu : ℝ) (k : Fin 3 → ℝ) (n : ℕ) (m : Fin (n * 7)) :
    SymmetricOn (polyGaussCore (d := n * 6))
      ((polyGaussCore (d := n * 6)).subtype.comp (redFieldN nu k n m)) :=
  (coreRepPoly (n * 6)).symmetricOn_op (mulOp_polySym (realCoeff_redFormPoly _ _ _ _ _))

/-- **The reduced `n`-parcel Hamiltonian** on the Gauss–polynomial core of `L²(ℝ^{6n})` — the
`n`-parcel member of the one-particle family (`n = 1` is the reduced one-particle Hamiltonian). -/
def redHam (nu : ℝ) (k : Fin 3 → ℝ) (n : ℕ) :
    polyGaussCore (d := n * 6) →ₗ[ℂ] L2d (n * 6) :=
  weylOp (redPiN n) (redFieldN nu k n)

theorem redHam_symmetricOn (nu : ℝ) (k : Fin 3 → ℝ) (n : ℕ) :
    SymmetricOn (polyGaussCore (d := n * 6)) (redHam nu k n) :=
  weylOpDom_symmetricOn (redPiN_symmetricOn n) (redFieldN_symmetricOn nu k n)

/-- **The reduced Hamiltonian is bounded below** — a sum of Weyl-ordered squares, exactly as in the
full sector. -/
theorem redHam_quadForm_nonneg (nu : ℝ) (k : Fin 3 → ℝ) (n : ℕ)
    (x : polyGaussCore (d := n * 6)) : 0 ≤ quadForm (redHam nu k n) x :=
  weylOpDom_quadForm_nonneg (redPiN_symmetricOn n) (redFieldN_symmetricOn nu k n) x

/-- **The reduced Hamiltonian has a positive self-adjoint (Friedrichs) extension.** -/
theorem redHam_friedrichs_extension (nu : ℝ) (k : Fin 3 → ℝ) (n : ℕ) :
    ∃ (Dom : Submodule ℂ (L2d (n * 6))) (A : Dom →ₗ[ℂ] L2d (n * 6)),
      IsPositiveSelfAdjointExtension (redHam nu k n) A :=
  friedrichs_extension_exists_complete
    ⟨polyGaussCore, redHam nu k n, redHam_symmetricOn nu k n,
      redHam_quadForm_nonneg nu k n⟩
    polyGaussCore_dense

/-- The reduced one-body operators as a densely defined positive symmetric operator. -/
def redPosSym (nu : ℝ) (k : Fin 3 → ℝ) (n : ℕ) : PosSymOp (L2d (n * 6)) where
  dom := polyGaussCore (d := n * 6)
  op := redHam nu k n
  sym := redHam_symmetricOn nu k n
  pos := redHam_quadForm_nonneg nu k n

/-- **The Friedrichs extension of the reduced Hamiltonian as a Faris–Lavine comparison** — the
candidate `N_E` of the plan, with `c = 0`. -/
def redFried (nu : ℝ) (k : Fin 3 → ℝ) (n : ℕ) : Comparison (L2d (n * 6)) :=
  friedrichsComparison (redPosSym nu k n) polyGaussCore_dense

theorem polyGaussCore_le_redFriedDom (nu : ℝ) (k : Fin 3 → ℝ) (n : ℕ) :
    (polyGaussCore (d := n * 6)) ≤ (redFried nu k n).dom := fun v hv =>
  (friedrichsComparison_extends (redPosSym nu k n) polyGaussCore_dense ⟨v, hv⟩).choose

theorem redFried_op_core (nu : ℝ) (k : Fin 3 → ℝ) (n : ℕ) (p : polyGaussCore (d := n * 6))
    (h : (p : L2d (n * 6)) ∈ (redFried nu k n).dom) :
    (redFried nu k n).op ⟨(p : L2d (n * 6)), h⟩ = redHam nu k n p :=
  (friedrichsComparison_extends (redPosSym nu k n) polyGaussCore_dense p).choose_spec

/-! ## 6. The nested Fock space of the reduced sector

The comparison operator the route needs is the lifted Friedrichs realization
(`dsComparison`) of the reduced one-body operators — the `N_E` of the plan.  Positivity,
symmetry and surjectivity of `N + 1` are fibrewise, so they lift verbatim, and
Faris–Lavine then gives essential self-adjointness with `c = 0` exactly as in the full
Eulerian sector. -/

/-- The nested Fock space `⊕ₙ L²(ℝ^{6n})` of the reduced (Fourier-eliminated) sector. -/
abbrev nsRedFockSpace := lp (fun n : ℕ => L2d (n * 6)) 2

/-- The finite-parcel core of the reduced Fock space. -/
def nsRedFockCore : Submodule ℂ nsRedFockSpace :=
  dsCore (fun n : ℕ => polyGaussCore (d := n * 6))

theorem nsRedFockCore_dense :
    Dense ((nsRedFockCore : Submodule ℂ nsRedFockSpace) : Set nsRedFockSpace) :=
  dsCore_dense fun _ => polyGaussCore_dense

/-- **The reduced Hamiltonian on the nested Fock space.** -/
def nsRedFullFockHam (nu : ℝ) (k : Fin 3 → ℝ) : nsRedFockCore →ₗ[ℂ] nsRedFockSpace :=
  dsOp (fun n : ℕ => redHam nu k n)

theorem nsRedFullFockHam_symmetricOn (nu : ℝ) (k : Fin 3 → ℝ) :
    SymmetricOn nsRedFockCore (nsRedFullFockHam nu k) :=
  dsOp_symmetricOn _ fun n => redHam_symmetricOn nu k n

/-- **The reduced Fock Hamiltonian is bounded below** — positivity is fibrewise. -/
theorem nsRedFullFockHam_quadForm_nonneg (nu : ℝ) (k : Fin 3 → ℝ) (x : nsRedFockCore) :
    0 ≤ quadForm (nsRedFullFockHam nu k) x :=
  dsOp_quadForm_nonneg _ (fun n u => redHam_quadForm_nonneg nu k n u) x

/-- **The reduced Fock Hamiltonian has a positive self-adjoint (Friedrichs) extension.** -/
theorem nsRedFullFock_friedrichs_extension (nu : ℝ) (k : Fin 3 → ℝ) :
    ∃ (Dom : Submodule ℂ nsRedFockSpace) (A : Dom →ₗ[ℂ] nsRedFockSpace),
      IsPositiveSelfAdjointExtension (nsRedFullFockHam nu k) A :=
  friedrichs_extension_exists_complete
    ⟨nsRedFockCore, nsRedFullFockHam nu k, nsRedFullFockHam_symmetricOn nu k,
      nsRedFullFockHam_quadForm_nonneg nu k⟩
    nsRedFockCore_dense

/-! ## 7. The advection: the transfer weight, its skewness, and the commutator obligation

The eliminated residual split as `σ(R_i) = i (k·u) u_i + (q_i + ν|k|² u_i)`: the first term is the
**advection**, and it is the only genuinely new object of the route.  This section records what is
proved about it and — just as importantly — what is not:

* the advection symbol is the **transfer-weight pairing** `Σ_j k_j (u_j u_i)`: the momentum `k_j` of
  the eliminated derivative is contracted with the product of the two velocity modes, which is the
  polynomial form of the momentum-space convolution of the route (`fourierMomentum_add` /
  `_smul` record that the weight is linear in the momentum, and `fourierAdvect_eq_transfer` is the
  contraction itself);
* multiplication by the *imaginary* advection symbol is **skew** on the core
  (`mulOp_polySkew`, `CoreRep.skewOn_op`), so it contributes **nothing** to the quadratic form
  (`redAdvect_quadForm_zero`) — which is precisely what makes the *modulus* square of §5 and the
  plain sum of squares agree as forms, and what makes the **coefficientwise** square of the complex
  form unusable.  It does **not** say the advection is excluded from the energy: the real polynomial
  `fourierAdvect` has a symmetric multiplication operator, so `½ a_i²` is a legitimate square
  (`§5`, plan of record 2026‑09‑17b);
* consequently the one remaining obligation of the route is the **commutator bound** against the
  comparison operator, and `nsRedFullFock_esa_of_commBound` states exactly what that obligation
  buys: Faris–Lavine with the comparison of §6, the advection as `H`, and the bound as the single
  hypothesis (the `c = 0` form is `nsRedFullFock_esa_of_zero_comm`).  Nothing here claims the bound;
  it is the analytic input the plan leaves open.

A Gauss-skew polynomial operator transported to the core. -/

def PolySkew (T : Module.End ℂ (MvPolynomial (Fin d) ℂ)) : Prop :=
  PolyAdj T (-T)

/-- **Multiplication by an imaginary multiple of a real polynomial is skew.** -/
theorem mulOp_polySkew {f : MvPolynomial (Fin d) ℂ} (hf : RealCoeff f) :
    PolySkew (mulOp (C Complex.I * f)) := by
  intro p q
  have hL : starP ((C Complex.I * f) * p) * q
      = (-(C Complex.I * f)) * (starP p * q) := by
    simp only [starP_mul, starP_C, Complex.conj_I, show starP f = f from hf, C_neg]
    ring
  have hR : starP p * ((-mulOp (C Complex.I * f)) q) = (-(C Complex.I * f)) * (starP p * q) := by
    simp only [mulOp_apply, LinearMap.neg_apply, neg_mul]
    ring
  change gaussInt (starP ((mulOp (C Complex.I * f)) p) * q)
      = gaussInt (starP p * (-(mulOp (C Complex.I * f))) q)
  rw [mulOp_apply, hL, hR]

set_option maxHeartbeats 1000000 in
-- the `L²` coercions in the rewrite chain need more than the default budget
/-- **A Gauss-skew polynomial operator transports to a skew operator on the core**: its adjoint is
its negative, `⟪T x, y⟫ = −⟪x, T y⟫`. -/
theorem coreRep_skewOn_op (Φ : CoreRep d D) {T : Module.End ℂ (MvPolynomial (Fin d) ℂ)}
    (hT : PolySkew T) (x y : D) :
    inner ℂ ((D.subtype.comp (Φ.op T)) x) ((y : D) : L2d d)
      = -inner ℂ ((x : D) : L2d d) ((D.subtype.comp (Φ.op T)) y) := by
  have hx : (D.subtype.comp (Φ.op T)) x = pgLp (T (Φ.equiv.symm x)) := Φ.coe_op T x
  have hy : (D.subtype.comp (Φ.op T)) y = pgLp (T (Φ.equiv.symm y)) := Φ.coe_op T y
  have hcx : ((x : D) : L2d d) = pgLp (Φ.equiv.symm x) := Φ.coe_symm x
  have hcy : ((y : D) : L2d d) = pgLp (Φ.equiv.symm y) := Φ.coe_symm y
  have hneg : ∀ z : MvPolynomial (Fin d) ℂ, gaussInt (-z) = -gaussInt z := by
    intro z
    rw [show (-z) = (-1 : ℂ) • z by module, gaussInt_smul]
    ring
  have h := hT (Φ.equiv.symm x) (Φ.equiv.symm y)
  simp only [LinearMap.neg_apply, mul_neg, hneg] at h
  rw [hx, hy, hcx, hcy, inner_pgLp_pgLp, inner_pgLp_pgLp]
  exact h

/-- **The quadratic form of a skew operator on the core vanishes identically.** -/
theorem coreRep_quadForm_skew_zero (Φ : CoreRep d D) {T : Module.End ℂ (MvPolynomial (Fin d) ℂ)}
    (hT : PolySkew T) (x : D) : quadForm (D.subtype.comp (Φ.op T)) x = 0 := by
  set z : ℂ := inner ℂ ((x : D) : L2d d) ((D.subtype.comp (Φ.op T)) x) with hz
  have h1 : (inner ℂ ((D.subtype.comp (Φ.op T)) x) ((x : D) : L2d d)) = star z :=
    (inner_conj_symm _ _).symm
  have h2 : star z = -z := by
    rw [← h1]
    exact coreRep_skewOn_op Φ hT x x
  have h4 : z.re = 0 := by
    have h := congrArg Complex.re h2
    simp only [Complex.star_def, Complex.conj_re, Complex.neg_re] at h
    linarith
  change (inner ℂ ((x : D) : L2d d) ((D.subtype.comp (Φ.op T)) x)).re = 0
  exact h4

/-- **The advection term of the eliminated Hamiltonian**: multiplication by `i (k·u) u_i`, one for
each residual direction of each parcel. -/
def redAdvect (k : Fin 3 → ℝ) (n : ℕ) (m : Fin (n * 3)) :
    polyGaussCore (d := n * 6) →ₗ[ℂ] L2d (n * 6) :=
  (polyGaussCore (d := n * 6)).subtype.comp
    ((coreRepPoly (n * 6)).op
      (mulOp (C Complex.I * redAdvectPoly k n (finProdFinEquiv.symm m).1
        (finProdFinEquiv.symm m).2)))

theorem redAdvect_polySkew (k : Fin 3 → ℝ) (n : ℕ) (m : Fin (n * 3)) :
    PolySkew (mulOp
      (C Complex.I * redAdvectPoly k n (finProdFinEquiv.symm m).1 (finProdFinEquiv.symm m).2)) :=
  mulOp_polySkew (realCoeff_redAdvectPoly k n _ _)

/-- **The advection is skew on the reduced core** — multiplication by the imaginary advection
symbol has as adjoint its negative. -/
theorem redAdvect_skew (k : Fin 3 → ℝ) (n : ℕ) (m : Fin (n * 3))
    (x y : polyGaussCore (d := n * 6)) :
    inner ℂ (redAdvect k n m x) (y : L2d (n * 6))
      = -inner ℂ (x : L2d (n * 6)) (redAdvect k n m y) :=
  coreRep_skewOn_op (coreRepPoly (n * 6)) (redAdvect_polySkew k n m) x y

/-- **The advection contributes nothing to the quadratic form**: it is skew, so
`quadForm (redAdvect …) x = 0` for every core vector.  It is therefore *not* a square and cannot be
sourced from one; the positivity of §5 is unaffected by it. -/
theorem redAdvect_quadForm_zero (k : Fin 3 → ℝ) (n : ℕ) (m : Fin (n * 3))
    (x : polyGaussCore (d := n * 6)) : quadForm (redAdvect k n m) x = 0 :=
  coreRep_quadForm_skew_zero (coreRepPoly (n * 6)) (redAdvect_polySkew k n m) x

/-- The restriction of the reduced Fock Hamiltonian to the `n`-parcel sector is the reduced
`n`-parcel Hamiltonian. -/
theorem nsRedFullFockHam_sector (nu : ℝ) (k : Fin 3 → ℝ) (x : nsRedFockCore) (n : ℕ) :
    ((nsRedFullFockHam nu k x : nsRedFockSpace) : ∀ n : ℕ, L2d (n * 6)) n
      = redHam nu k n
        ⟨((x : nsRedFockSpace) : ∀ n : ℕ, L2d (n * 6)) n, x.2.2 n⟩ := rfl

/-- **The reduced Hamiltonian conserves the parcel number** — no lattice or finite-mode
truncation is introduced by the elimination. -/
theorem nsRedFullFockHam_number_conserving (nu : ℝ) (k : Fin 3 → ℝ) (x : nsRedFockCore)
    {n : ℕ} (hx : ∀ m, m ≠ n → ((x : nsRedFockSpace) : ∀ m : ℕ, L2d (m * 6)) m = 0)
    (m : ℕ) (hm : m ≠ n) :
    ((nsRedFullFockHam nu k x : nsRedFockSpace) : ∀ m : ℕ, L2d (m * 6)) m = 0 :=
  BookProof.Qg3DGaugeFL.dsOp_number_conserving _ x hx m hm

/-- **The lifted comparison operator** — the `ℓ²`-direct sum of the reduced Friedrichs
realizations.  This is the `N_E` of the plan's Fourier-elimination route (including the viscous
regularization `ν > 0` and the mode `k`). -/
def nsRedOuterComparison (nu : ℝ) (k : Fin 3 → ℝ) : Comparison nsRedFockSpace :=
  dsComparison (fun n : ℕ => redFried nu k n)

/-- The lifted comparison operator, fibrewise. -/
theorem nsRedOuterN_apply (nu : ℝ) (k : Fin 3 → ℝ) (x : (nsRedOuterComparison nu k).dom)
    (n : ℕ) :
    (((nsRedOuterComparison nu k).op x : nsRedFockSpace) : ∀ n : ℕ, L2d (n * 6)) n
      = (redFried nu k n).op
          ⟨((x : nsRedFockSpace) : ∀ n : ℕ, L2d (n * 6)) n, x.2.1 n⟩ :=
  dsCompOp_fib _ x n

set_option maxHeartbeats 1600000 in
-- the Friedrichs domain is built from a completion: unfolding it is costly
/-- The finite-parcel core sits inside the domain of the lifted comparison operator — the domain
obligation of the plan's “definition of done”. -/
theorem nsRedFockCore_le_friedDom (nu : ℝ) (k : Fin 3 → ℝ) :
    nsRedFockCore ≤ (nsRedOuterComparison nu k).dom := by
  intro x hx
  refine ⟨fun n => polyGaussCore_le_redFriedDom nu k n (hx.2 n), ?_⟩
  have hfun : (fun n : ℕ => opTot (redFried nu k n).op ((x : nsRedFockSpace) n))
      = fun n : ℕ =>
        (redHam nu k n ⟨(x : nsRedFockSpace) n, hx.2 n⟩ : L2d (n * 6)) := by
    funext n
    rw [opTot_of_mem _ (polyGaussCore_le_redFriedDom nu k n (hx.2 n)),
      redFried_op_core nu k n ⟨(x : nsRedFockSpace) n, hx.2 n⟩]
  rw [hfun]
  refine memLp_of_finite_support (Set.Finite.subset hx.1 fun n hn => ?_)
  simp only [Set.mem_setOf_eq] at hn ⊢
  intro h0
  refine hn ?_
  have hz : (⟨(x : nsRedFockSpace) n, hx.2 n⟩ : polyGaussCore (d := n * 6)) = 0 :=
    Subtype.ext h0
  rw [hz, map_zero]

/-- **Faris–Lavine on the reduced nested Fock space**: the lifted realization of the reduced
sector Hamiltonian is essentially self-adjoint on its domain.  This is the `H = N`, `c = 0` case
of the criterion — the comparison is the Friedrichs realization above, so its commutator with the
operator vanishes; the advection is *not* part of `N` (see §4) and is the perturbation the
commutator estimate of the plan bounds against this `N`. -/
theorem nsRedFullOuterN_esa (nu : ℝ) (k : Fin 3 → ℝ) :
    EssentiallySelfAdjointOn (nsRedOuterComparison nu k).dom (nsRedOuterComparison nu k).op :=
  Comparison.esa_self _

set_option maxHeartbeats 2000000 in
-- the Friedrichs domain is built from a completion: defeq checks are costly
/-- **The lifted Friedrichs realization is a positive self-adjoint extension of the reduced
Hamiltonian on the finite-parcel core.**  With `nsRedFullOuterN_esa` this is the full Faris–Lavine
statement of the reduced sector: `N_E` is positive, self-adjoint, extends the eliminated
Hamiltonian, and has the Hamiltonian essentially self-adjoint on its domain (`H = N`, `c = 0`). -/
theorem nsRedFullOuterN_isPositiveSelfAdjointExtension (nu : ℝ) (k : Fin 3 → ℝ) :
    IsPositiveSelfAdjointExtension (nsRedFullFockHam nu k) (nsRedOuterComparison nu k).op :=
  (nsRedOuterComparison nu k).isPositiveSelfAdjointExtension (nsRedFullFockHam nu k)
    (fun x => by
      refine ⟨nsRedFockCore_le_friedDom nu k x.2, ?_⟩
      refine lp.ext (funext fun n => ?_)
      rw [nsRedOuterN_apply, redFried_op_core nu k n ⟨(x : nsRedFockSpace) n, x.2.2 n⟩]
      exact rfl)

/-- **Faris–Lavine on the reduced nested Fock space, with a perturbation of the reduced Hamiltonian
as `H`**: if `H` is symmetric on the domain of the comparison operator and the commutator form is
bounded by the comparison's quadratic form, then `H` is essentially self-adjoint there.  All the
structural hypotheses of the criterion (positivity, symmetry and surjectivity of `N + 1` for `N_E`,
and the extension of the reduced Hamiltonian by it) are already proved above; the **commutator bound
is the single remaining analytic input** of the route (plan item 4) — in particular it is the only
thing standing between the skew-adjoint advection of §7 and the eliminated generator. -/
theorem nsRedFullFock_esa_of_commBound (nu : ℝ) (k : Fin 3 → ℝ)
    (H : (nsRedOuterComparison nu k).dom →ₗ[ℂ] nsRedFockSpace)
    (hH : SymmetricOn (nsRedOuterComparison nu k).dom H) {c : ℝ} (hc : 0 ≤ c)
    (hcomm : ∀ x : (nsRedOuterComparison nu k).dom,
      |commForm H (nsRedOuterComparison nu k).op x|
        ≤ c * quadForm (nsRedOuterComparison nu k).op x) :
    EssentiallySelfAdjointOn (nsRedOuterComparison nu k).dom H :=
  (nsRedOuterComparison nu k).essentiallySelfAdjointOn H hH c hc hcomm

/-- The `c = 0` case: a symmetric `H` whose commutator form against the comparison **vanishes** on
the domain is essentially self-adjoint — the form in which the reduced Hamiltonian itself
(`nsRedFullOuterN_esa`) and its perturbations are handled. -/
theorem nsRedFullFock_esa_of_zero_comm (nu : ℝ) (k : Fin 3 → ℝ)
    (H : (nsRedOuterComparison nu k).dom →ₗ[ℂ] nsRedFockSpace)
    (hH : SymmetricOn (nsRedOuterComparison nu k).dom H)
    (hcomm : ∀ x : (nsRedOuterComparison nu k).dom,
      commForm H (nsRedOuterComparison nu k).op x = 0) :
    EssentiallySelfAdjointOn (nsRedOuterComparison nu k).dom H :=
  nsRedFullFock_esa_of_commBound nu k H hH le_rfl fun x => by rw [hcomm x]; simp

end

end BookProof.NsFullEuler


