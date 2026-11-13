-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S06_CertainTypeSubcoherent
-- name    : OddOrder_Peterfalvi_S06_CertainTypeSubcoherent
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T07:18:32.914607+00:00
-- url     : https://prove2.me/theorems/a535a005-7d43-41b2-9c0f-a28825defc33
-- title:
--   Peterfalvi (5.3)(b): subcoherence of an induction family over Hypothesis (4.6)
-- statement:
--   Peterfalvi, *Character Theory for the Odd Order Theorem*, §5, p. 26, Theorem (5.3)(b): assume Hypothesis (4.6), (5.2.a) and $\mathcal{S}\subseteq\{\mathrm{Ind}_K^L\theta\mid\theta\in\mathrm{Irr}\,K,H\not\subseteq\mathrm{Ker}\theta\}$. Then Hypothesis (5.2) holds, with $\tau$ the restriction of the isometry of the Dade setup.
--
--   The main definition is `columnR`, the reducible $R(\chi)$ of (5.3)(b) for a nontrivial column.
--
--   The bundle also proves 2 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S06_CertainTypeSubcoherent.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S06_CertainTypeSubcoherent.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S06_CertainTypeCoherence
import Definitions.Def_OddOrder_Peterfalvi_S06_CertainTypeSupport
import Definitions.Def_OddOrder_Peterfalvi_S08_CrossOrthogonality
import Definitions.Def_OddOrder_Peterfalvi_S08_InducedKernelFamily

namespace OddOrder.Peterfalvi.S06

open OddOrder.RepresentationTheory

open scoped IsMulCommutative

variable {G : Type*} [Group G] [Fintype G]

variable {A : Set G} {L : Subgroup G} [Fintype ↥L]

variable [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥L : ℂ)]

/-- **Peterfalvi (5.3)(b), the reducible `R(χ)`** (issue 0159).  For a nontrivial column
`χ₂ ≠ 1`, any character `φ` equal to the column sum `μ_j = columnSum χ₂` carries the (4.9)
orthonormal difference-image family `R(μ_j)` of clause (5.2.d).

This is `certainTypeR` transported along `hφ : φ = columnSum h χ₂`, with the degree side condition
supplied for free: `certainTypeR` asks for `μ_j(1) = μ̄_j(1)`, which is
`columnSum_inv_apply_one` (the conjugate column `μ_{j⁻¹}` has the same degree, being the complex
conjugate of a sum of positive integers).  Only `image_eq` mentions `φ`, so the transport keeps
`imageSet` definitionally the `certainTypeR` one — which matters because the (5.2.e)
cross-orthogonality lemmas (`certainTypeR_imageSet_orthogonal_certainTypeR`) are stated on
`imageSet`. -/
noncomputable def columnR (h : Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    [Invertible (Nat.card ↥h.K : ℂ)]
    [Fintype ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    [Fintype (ticVdiff h).W] [Invertible (Nat.card (ticVdiff h).W : ℂ)]
    {χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ} (hχ₂ : χ₂ ≠ 1)
    {φ : ClassFunction ↥L ℂ} (hφ : φ = columnSum h χ₂) :
    S07.OrthonormalCharacterImageFamily (S07.dadeIntegralCharacterMap h.dade0 h.tau) φ where
  imageSet := (certainTypeR h hχ₂ (columnSum_inv_apply_one h χ₂).symm).imageSet
  mem_ZIrr := (certainTypeR h hχ₂ (columnSum_inv_apply_one h χ₂).symm).mem_ZIrr
  orthonormal := (certainTypeR h hχ₂ (columnSum_inv_apply_one h χ₂).symm).orthonormal
  image_eq := by
    rw [hφ]
    exact (certainTypeR h hχ₂ (columnSum_inv_apply_one h χ₂).symm).image_eq

@[simp] theorem columnR_imageSet (h : Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    [Invertible (Nat.card ↥h.K : ℂ)]
    [Fintype ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    [Fintype (ticVdiff h).W] [Invertible (Nat.card (ticVdiff h).W : ℂ)]
    {χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ} (hχ₂ : χ₂ ≠ 1)
    {φ : ClassFunction ↥L ℂ} (hφ : φ = columnSum h χ₂) :
    (columnR h hχ₂ hφ).imageSet
      = (certainTypeR h hχ₂ (columnSum_inv_apply_one h χ₂).symm).imageSet :=
  rfl

section

variable (h : Hypothesis46 A L)

variable {S : Set (ClassFunction ↥L ℂ)}

/-- **Peterfalvi (5.3)(b), the anchor** (p. 26: "By the definition of `τ`, `(φ − φ̄)^τ` vanishes
on `V`").

For a class function `α` of `L` that is `A₀`-supported and vanishes off `K`, the (4.6) Dade image
`α^τ` vanishes at every `v ∈ V = W ∖ (W₁ ∪ W₂)`.

Proof, exactly the book's one line: `V ⊆ A₀` (the `V^L` half of `A₀`, conjugator `1`), so `v` is a
Dade **base point** and the explicit (2.5) evaluation `dadeValue_eq` (witness `a = v`, `h = 1`)
gives `α^τ(v) = α(v)`; and `α(v) = 0` because `v` is not even `G`-conjugate into `K`
(`ticVdiffV_not_mem_conjugatesOfSet_K`, a Hypothesis (4.6)-level fact).

This replaces, at (4.6) generality, the three separately proved instances of the anchor — Sibley
`S08.tau_apply_eq_zero_of_mem_ticVdiffV`, type-P `S13.tau_apply_eq_zero_of_mem_typePV` and type-II
`S12.typeII_tau_apply_eq_zero_of_mem_ticVdiffV`. -/
theorem dadeICM_apply_eq_zero_of_mem_ticVdiffV (h : Hypothesis46 A L)
    {α : ClassFunction ↥L ℂ}
    (hαsupp : α.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
      (A ∪ OddOrder.GroupTheory.conjClassSetIn L h.tic.V) L)
    (hαK : ∀ z : ↥L, z ∉ h.K → α z = 0)
    {v : G} (hv : v ∈ (ticVdiff h).V) :
    S07.dadeIntegralCharacterMap h.dade0 h.tau α v = 0 := by
  classical
  -- `V = W ∖ (W₁ ∪ W₂)` is the ambient `(3.1)` exceptional set, hence sits in `A₀`
  have hvV : v ∈ h.tic.V := by rw [h.tic_V]; exact hv
  have hvA0 : v ∈ A ∪ OddOrder.GroupTheory.conjClassSetIn L h.tic.V :=
    Or.inr ⟨v, hvV, 1, L.one_mem, by group⟩
  -- base-point evaluation of the explicit (2.5) Dade map
  rw [S07.dadeIntegralCharacterMap_apply_of_support h.dade0 _ hαsupp,
    OddOrder.Peterfalvi.S04.Hypothesis.dadeMap_apply,
    h.dade0.dadeValue_eq _ (a := ⟨v, hvA0⟩) (Subgroup.one_mem _) (by rw [mul_one])]
  -- `α(v) = 0`: `v` is not `G`-conjugate into `K`, a fortiori not in `K`
  refine hαK _ fun hmem => ?_
  exact OddOrder.Peterfalvi.S08.ticVdiffV_not_mem_conjugatesOfSet_K h hv
    (Group.subset_conjugatesOfSet (Subgroup.mem_map_of_mem _ hmem))

end

end OddOrder.Peterfalvi.S06


