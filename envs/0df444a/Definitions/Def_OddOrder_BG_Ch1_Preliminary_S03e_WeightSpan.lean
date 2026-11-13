-- Prove2me | Definitions.Def_OddOrder_BG_Ch1_Preliminary_S03e_WeightSpan
-- name    : OddOrder_BG_Ch1_Preliminary_S03e_WeightSpan
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T06:08:59.064197+00:00
-- url     : https://prove2.me/theorems/09c6f0cc-a12e-419a-9c92-ad3120499dac
-- title:
--   Weight spaces span the whole space (abelian kernel, algebraically closed field)
-- statement:
--   For a finite abelian subgroup $K$ acting through $\rho$ on a finite-dimensional space $V$ over an algebraically closed field whose characteristic does not divide $|K|$, the weight spaces (simultaneous $K$-eigenspaces) span $V$: $\bigvee_\chi \mathrm{weightSpace}\,\rho\,K\,\chi=\top$. This is the spanning half of the abelian weight-space decomposition used in BG §3.
--
--   The main declaration: `iSup_weightSpace_eq_top` (Weight spaces span (abelian `K`, algebraically closed `F`, `char ∤ |K|`)).
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch1_Preliminary/S03e_WeightSpan.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch1_Preliminary/S03e_WeightSpan.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S03e_Thm35
import Mathlib.LinearAlgebra.Semisimple
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.FieldTheory.Separable

open Module

namespace OddOrder.BG.Ch1.S03e

variable {F : Type*} [Field F] {G : Type*} [Group G]

variable {W : Type*} [AddCommGroup W] [Module F W]

open Polynomial in
/-- **Weight spaces span** (abelian `K`, algebraically closed `F`, `char ∤ |K|`).  The simultaneous
`K`-eigenspaces `weightSpace ρ K χ` span `V`. -/
theorem iSup_weightSpace_eq_top [Finite G] [FiniteDimensional F W] [IsAlgClosed F]
    (ρ : Representation F G W) (K : Subgroup G)
    (hcomm : ∀ a b : ↥K, (a : G) * (b : G) = (b : G) * (a : G))
    (hchar : (Nat.card ↥K : F) ≠ 0) :
    (⨆ χ : ↥K → F, weightSpace ρ K χ) = ⊤ := by
  classical
  set n : ℕ := Nat.card ↥K with hn
  -- The commuting family of endomorphisms `f k = ρ k`.
  set f : ↥K → Module.End F W := fun k => ρ (k : G) with hf
  -- STEP 1: each `f k` is semisimple, annihilated by the separable `X ^ n - 1`.
  have hpow : ∀ k : ↥K, (f k) ^ n = 1 := by
    intro k
    rw [hf]
    rw [← map_pow]
    have : (k : G) ^ n = 1 := by
      have : (k ^ n : ↥K) = 1 := by rw [hn]; exact pow_card_eq_one'
      simpa using congrArg (Subgroup.subtype K) this
    rw [this, map_one]
  have hsep : ((Polynomial.X ^ n - 1 : F[X])).Separable :=
    Polynomial.X_pow_sub_one_separable_iff.mpr (by rw [hn]; exact hchar)
  have hss : ∀ k : ↥K, (f k).IsSemisimple := by
    intro k
    apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsep.squarefree
    rw [map_sub, map_pow, Polynomial.aeval_X, map_one, hpow k, sub_self]
  -- STEP 2: for semisimple operators, `maxGenEigenspace = eigenspace`.
  have hmax : ∀ (k : ↥K) (μ : F), (f k).maxGenEigenspace μ = (f k).eigenspace μ := by
    intro k μ
    exact (Module.End.isFinitelySemisimple_iff_isSemisimple.mpr (hss
        k)).maxGenEigenspace_eq_eigenspace μ
  -- STEP 3: max generalized eigenspaces of each `f k` span (algebraically closed).
  have hspan : ∀ k : ↥K, (⨆ μ : F, (f k).maxGenEigenspace μ) = ⊤ :=
    fun k => Module.End.iSup_maxGenEigenspace_eq_top (f k)
  -- STEP 4: the family commutes, so simultaneous diagonalization.
  have hcommute : Pairwise fun i j : ↥K => Commute (f i) (f j) := by
    intro i j _
    change f i * f j = f j * f i
    rw [hf]
    simp only
    rw [← map_mul, ← map_mul, hcomm i j]
  have hkey :=
      Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
    f hcommute hspan
  -- STEP 5: rewrite `maxGenEigenspace → eigenspace` to recover the weight spaces.
  rw [← hkey]
  apply iSup_congr
  intro χ
  rw [weightSpace]
  apply iInf_congr
  intro k
  rw [hmax k (χ k)]

end OddOrder.BG.Ch1.S03e


