-- Prove2me | Definitions.Def_RPLib_S4_SwanGlobT
-- name    : RPLib_S4_SwanGlobT
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T10:28:19.572038+00:00
-- url     : https://prove2.me/theorems/a350d377-2519-4107-855e-6cc91413265d
-- title:
--   Towers of local data: independence of the level
-- statement:
--   A tower of local data consists of local data for a group $G$ together with a normal subgroup $H$ such that the $H$-fixed field carries the induced local data for $G/H$. The file packages the quotient formula and Herbrand's theorem for towers: upper ramification groups of $G/H$ are the images of those of $G$, and Swan conductors of representations of $G/H$ can be computed at either level.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (Swan conductors and wild ramification at infinity, used for Weil-type bounds of exponential sums). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   J.-P. Serre, Local Fields, GTM 67, Springer (1979), doi:10.1007/978-1-4757-5673-9, Chapter IV, Section 3

import Mathlib
import Definitions.Def_RPLib_S4_SwanLocQc

/-!
# S4-Swan (K2), part 11: towers of local data (independence of the level)

`LocData.Tower D D' ι r`: local data `D` on `L` (group `G`) and `D'` on `L'` (group `G'`), a field embedding
`ι : L → L'` and a surjection `r : G' → G` with `σ • ι x = ι (r σ • x)`, such that `v' ∘ ι = |ker r| · v` and
`v'` takes values in `|ker r| ℤ` on `ker r`-invariants. Then `ι ϖ` is `QData` for `ker r`, Serre's quotient formula
holds for `(D'.ramFn, D.ramFn, r)`, and the Swan conductor and the upper numbering are compatible with `r`.
This is the level-independence step of the global theory (`L ⊆ L'` two finite levels at a place over `∞`).
-/

set_option autoImplicit false

namespace RamanujanPetersson
namespace Swan

noncomputable section

namespace LocData

variable {G L G' L' : Type*} [Group G] [Field L] [MulSemiringAction G L]
  [Group G'] [Field L'] [MulSemiringAction G' L']
  (D : LocData G L) (D' : LocData G' L') (ι : L →+* L') (r : G' →* G) [Fintype r.ker]

/-- Tower hypotheses (see the module docstring). -/
structure Tower : Prop where
  surj : Function.Surjective r
  compat : ∀ (σ : G') (x : L), σ • ι x = ι (r σ • x)
  v_iota : ∀ (x : L) (m : ℤ), D.v x = m →
    D'.v (ι x) = (((Fintype.card r.ker : ℤ) * m : ℤ) : WithTop ℤ)
  val : ∀ x : L', (∀ h ∈ r.ker, h • x = x) → x ≠ 0 →
    ∃ k : ℤ, D'.v x = (((Fintype.card r.ker : ℤ) * k : ℤ) : WithTop ℤ)

variable {D D' ι r}

/-- `ι ϖ` is quotient data for `ker r`. -/
theorem Tower.qdata (hT : Tower D D' ι r) : D'.QData r.ker (ι D.ϖ) where
  fix h hh := by rw [hT.compat, (MonoidHom.mem_ker).1 hh, one_smul]
  v_eq := by
    rw [hT.v_iota D.ϖ 1 (by rw [D.v_ϖ]; rfl), mul_one]
    rfl
  val := hT.val

theorem Tower.nq_eq (hT : Tower D D' ι r) {s : G} (hs : s ≠ 1) (σ : G') (hσ : r σ = s) :
    D'.nq (ι D.ϖ) σ = (D.ramFn.i s).toNat * Fintype.card r.ker := by
  have hne : s • D.ϖ - D.ϖ ≠ 0 := by
    intro h0
    exact hs (D.eq_one_of_fix_ϖ (sub_eq_zero.1 h0))
  have h0 : 0 ≤ D.v (s • D.ϖ - D.ϖ) := D.v_sub_smul_nonneg s (by rw [D.v_ϖ]; exact zero_le_one)
  obtain ⟨m, hm⟩ : ∃ m : ℤ, D.v (s • D.ϖ - D.ϖ) = m := by
    induction h : D.v (s • D.ϖ - D.ϖ) with
    | top => exact absurd ((AddValuation.top_iff _).1 h) hne
    | coe a => exact ⟨a, rfl⟩
  have hm0 : 0 ≤ m := by rw [hm] at h0; exact_mod_cast h0
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hm0
  have h1 : σ • ι D.ϖ - ι D.ϖ = ι (s • D.ϖ - D.ϖ) := by rw [hT.compat, hσ, map_sub]
  rw [LocData.nq, h1, hT.v_iota _ _ hm, D.ramFn_i, hm, toENat_coe, toENat_coe]
  have : ((Fintype.card r.ker : ℤ) * (k : ℤ)) = ((Fintype.card r.ker * k : ℕ) : ℤ) := by push_cast; ring
  rw [this, Int.toNat_natCast, Int.toNat_natCast, ENat.toNat_natCast, ENat.toNat_natCast, mul_comm]

/-- **Serre's quotient formula** along a tower of local data. -/
theorem Tower.quotFormula [Fintype G] [Fintype G'] [DecidableEq G] (hT : Tower D D' ι r) :
    RamFn.QuotFormula D'.ramFn D.ramFn r := by
  intro s hs
  set σ := D'.ramFn.best hT.surj s
  have hσ : r σ = s := D'.ramFn.map_best hT.surj s
  have hσH : σ ∉ r.ker := fun h => hs (by rw [← hσ]; exact h)
  rw [D'.ramFn.sum_fib hT.surj s]
  calc (D.ramFn.i s).toNat * Nat.card r.ker = D'.nq (ι D.ϖ) σ := by
        rw [hT.nq_eq hs σ hσ, Nat.card_eq_fintype_card]
    _ = ∑ h : r.ker, (D'.ramFn.i (σ * h)).toNat := hT.qdata.nq_sum hσH
    _ = _ := by convert rfl

/-- **Herbrand's theorem** along a tower: `r (G'^v) = G^v`. -/
theorem Tower.map_upper [Fintype G] [Fintype G'] [DecidableEq G] (hT : Tower D D' ι r) (v : ℚ) :
    (D'.ramFn.upper v).map r = D.ramFn.upper v :=
  RamFn.map_upper D'.ramFn D.ramFn hT.surj hT.quotFormula v

/-- The Swan conductor does not depend on the level. -/
theorem Tower.swan_comp [Fintype G] [Fintype G'] [DecidableEq G] (hT : Tower D D' ι r)
    {k W : Type*} [Field k] [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (ρ : Representation k G W) : D'.ramFn.swan (ρ.comp r) = D.ramFn.swan ρ :=
  RamFn.swan_comp D'.ramFn D.ramFn ρ hT.surj hT.quotFormula

end LocData

end

end Swan
end RamanujanPetersson


