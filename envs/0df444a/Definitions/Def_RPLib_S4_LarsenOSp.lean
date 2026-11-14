-- Prove2me | Definitions.Def_RPLib_S4_LarsenOSp
-- name    : RPLib_S4_LarsenOSp
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T03:24:39.133304+00:00
-- url     : https://prove2.me/theorems/c14571eb-915f-4de9-bd68-6ddb622c0733
-- title:
--   Larsen's alternative library: Larsen's alternative, cases (2) and (3) (`O`/`SO`, `Sp`)
-- statement:
--   `larsen_orth` (`G ≤ O(B)`, `M4 = 3`, `dim V ≥ 3` ⇒ `G` finite, `SO(B)` or `O(B)`), `larsen_symp` (`G ≤ Sp(B)`,
--   `M4 = 3`, `dim V ≥ 3` ⇒ `G` finite or `Sp(B)`), and the combined `larsen_alternative`.
--
--   **Formalization note.** Library module (namespace `RamanujanPetersson.AlgGrpA/B/C` or `RamanujanPetersson.Larsen`) of a formalization of Larsen's alternative, used in a formalization of the Ramanujan-Petersson conjecture. $\mathrm{GL}_n(K)$ is `Matrix.GeneralLinearGroup n K` with the Zariski topology `RamanujanPetersson.AlgGrpA.zarTop` (induced from $\mathrm{Spec}\,K[x_{ij}, y_{ij}]$ via the entries of $g$ and $g^{-1}$; a local instance). The file contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   N. M. Katz, Larsen's alternative, moments, and the monodromy of Lefschetz pencils, in: Contributions to Automorphic Forms, Geometry, and Number Theory (Shalika volume), Johns Hopkins Univ. Press 2004, 521-560; A. Borel, Linear Algebraic Groups, 2nd ed., GTM 126, Springer 1991, doi:10.1007/978-1-4612-0941-6

import Mathlib
import Definitions.Def_RPLib_S4_LarsenIso
import Definitions.Def_RPLib_S4_LarsenSL

/-!
# S4-Larsen: Larsen's alternative, cases (2) and (3) (`O`/`SO`, `Sp`)

`larsen_orth` (`G ≤ O(B)`, `M4 = 3`, `dim V ≥ 3` ⇒ `G` finite, `SO(B)` or `O(B)`), `larsen_symp` (`G ≤ Sp(B)`,
`M4 = 3`, `dim V ≥ 3` ⇒ `G` finite or `Sp(B)`), and the combined `larsen_alternative`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Matrix

noncomputable section

namespace RamanujanPetersson.Larsen

open RamanujanPetersson.AlgGrpA RamanujanPetersson.AlgGrpB RamanujanPetersson.AlgGrpC

attribute [local instance] RamanujanPetersson.AlgGrpA.zarTop

variable {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]

section OSp

variable [IsAlgClosed K] [CharZero K]

theorem isUnit_det_of_nondegenerate {B : Matrix n n K} (hnd : B.Nondegenerate) : IsUnit B.det :=
  isUnit_iff_ne_zero.2 (Matrix.nondegenerate_iff_det_ne_zero.1 hnd)

theorem det_of_mem_isoSub {B : Matrix n n K} (hu : IsUnit B.det) {g : Matrix.GeneralLinearGroup n K}
    (hg : g ∈ isoSub B) : (g : Matrix n n K).det = 1 ∨ (g : Matrix n n K).det = -1 := by
  have h := congrArg Matrix.det (mem_isoSub.1 hg)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at h
  have h2 : (g : Matrix n n K).det * (g : Matrix n n K).det = 1 :=
    mul_right_cancel₀ (isUnit_iff_ne_zero.1 hu) (by rw [one_mul]; linear_combination h)
  exact mul_self_eq_one_iff.1 h2

/-- **Larsen's alternative (2)** (orthogonal case, Katz p.27): `G ≤ O(B)` Zariski closed, irreducible,
`M4 = 3`, `dim V ≥ 3` ⇒ `G` finite, `G = SO(B)` or `G = O(B)`. -/
theorem larsen_orth {B : Matrix n n K} (hB : Bᵀ = B) (hnd : B.Nondegenerate) (hn : 3 ≤ Fintype.card n)
    {G : Subgroup (Matrix.GeneralLinearGroup n K)}
    (hGc : IsClosed (G : Set (Matrix.GeneralLinearGroup n K))) (hGB : G ≤ isoSub B)
    (hG : ∀ W : Submodule K (n → K), (∀ g ∈ G, ∀ v ∈ W, (g : Matrix n n K) *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤)
    (hM : M4 G = 3) :
    Finite G ∨ G = isoSub B ⊓ detOne ∨ G = isoSub B := by
  have hu := isUnit_det_of_nondegenerate hnd
  have hBt : Bᵀ = (1 : K) • B := by rw [one_smul, hB]
  rcases lieS_iso_eq_bot_or_eq hGB hG (endIso_scalar hn hu (mul_one 1) hBt hGB hM.le) with h | h
  · exact Or.inl (finite_of_lieS_eq_bot G h)
  · right
    have hSO : ∀ g ∈ isoSub B, (g : Matrix n n K).det = 1 → g ∈ G := fun g hg hd =>
      so_mem_of_so_le_lieS hB hnd hn hGc (fun X hX => by rw [h]; exact mem_isoLie.2 hX) hg hd
    by_cases hall : ∀ g ∈ G, (g : Matrix n n K).det = 1
    · left
      exact le_antisymm (fun g hg => Subgroup.mem_inf.2 ⟨hGB hg, hall g hg⟩)
        (fun g hg => hSO g (Subgroup.mem_inf.1 hg).1 (Subgroup.mem_inf.1 hg).2)
    · right
      obtain ⟨h0, hh0, hd0⟩ := not_forall₂.1 hall
      have hd0' : (h0 : Matrix n n K).det = -1 := (det_of_mem_isoSub hu (hGB hh0)).resolve_left hd0
      have hinv : ((h0⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K).det = -1 := by
        have e : (h0 : Matrix n n K).det * ((h0⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K).det = 1 := by
          rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
        rw [hd0'] at e
        linear_combination -e
      refine le_antisymm hGB (fun g hg => ?_)
      rcases det_of_mem_isoSub hu hg with hd | hd
      · exact hSO g hg hd
      · have hm : h0⁻¹ * g ∈ G := by
          refine hSO _ ((isoSub B).mul_mem ((isoSub B).inv_mem (hGB hh0)) hg) ?_
          rw [Units.val_mul, Matrix.det_mul, hinv, hd]
          norm_num
        have h' := G.mul_mem hh0 hm
        rwa [mul_inv_cancel_left] at h'

/-- **Larsen's alternative (3)** (symplectic case, Katz p.27): `G ≤ Sp(B)` Zariski closed, irreducible,
`M4 = 3`, `dim V > 2` ⇒ `G` finite or `G = Sp(B)`. -/
theorem larsen_symp {B : Matrix n n K} (hB : Bᵀ = -B) (hnd : B.Nondegenerate) (hn : 3 ≤ Fintype.card n)
    {G : Subgroup (Matrix.GeneralLinearGroup n K)}
    (hGc : IsClosed (G : Set (Matrix.GeneralLinearGroup n K))) (hGB : G ≤ isoSub B)
    (hG : ∀ W : Submodule K (n → K), (∀ g ∈ G, ∀ v ∈ W, (g : Matrix n n K) *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤)
    (hM : M4 G = 3) :
    Finite G ∨ G = isoSub B := by
  have hu := isUnit_det_of_nondegenerate hnd
  have hBt : Bᵀ = (-1 : K) • B := by rw [neg_one_smul, hB]
  rcases lieS_iso_eq_bot_or_eq hGB hG (endIso_scalar hn hu (by norm_num) hBt hGB hM.le) with h | h
  · exact Or.inl (finite_of_lieS_eq_bot G h)
  · exact Or.inr (eq_isoSub_of_sp_le_lieS hB hnd hGc hGB (fun X hX => by rw [h]; exact mem_isoLie.2 hX))

/-- **Larsen's alternative** (Katz, Arizona notes pp.27-28), all three cases. `K` algebraically closed of
characteristic 0, `V = K^n` with `dim V ≥ 3`, `G ≤ GL(V)` Zariski closed and irreducible on `V`.
Use in Route K: residue characteristic `p` odd (including `p = 3`) → case (1); `p = 2` → (1) if `F` is not self-dual,
(2) if it is orthogonally self-dual, (3) if it is symplectically self-dual. -/
theorem larsen_alternative (hn : 3 ≤ Fintype.card n) {G : Subgroup (Matrix.GeneralLinearGroup n K)}
    (hGc : IsClosed (G : Set (Matrix.GeneralLinearGroup n K)))
    (hG : ∀ W : Submodule K (n → K), (∀ g ∈ G, ∀ v ∈ W, (g : Matrix n n K) *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤) :
    ((((fun g : Matrix.GeneralLinearGroup n K => (g : Matrix n n K).det) '' (G : Set _)).Finite) → M4 G = 2 →
        Finite G ∨ (detOne ≤ G ∧ (detOne.subgroupOf G).FiniteIndex)) ∧
      (∀ B : Matrix n n K, Bᵀ = B → B.Nondegenerate → G ≤ isoSub B → M4 G = 3 →
        Finite G ∨ G = isoSub B ⊓ detOne ∨ G = isoSub B) ∧
      (∀ B : Matrix n n K, Bᵀ = -B → B.Nondegenerate → G ≤ isoSub B → M4 G = 3 →
        Finite G ∨ G = isoSub B) :=
  ⟨fun hdet hM => larsen_sl (le_trans (by norm_num) hn) hGc hG hdet hM,
    fun _ hB hnd hGB hM => larsen_orth hB hnd hn hGc hGB hG hM,
    fun _ hB hnd hGB hM => larsen_symp hB hnd hn hGc hGB hG hM⟩

end OSp

end RamanujanPetersson.Larsen


