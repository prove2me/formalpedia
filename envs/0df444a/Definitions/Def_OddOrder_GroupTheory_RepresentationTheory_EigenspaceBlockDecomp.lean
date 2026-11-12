-- Prove2me | Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_EigenspaceBlockDecomp
-- name    : OddOrder_GroupTheory_RepresentationTheory_EigenspaceBlockDecomp
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T04:44:49.52002+00:00
-- url     : https://prove2.me/theorems/a64fe747-45a0-4bbf-af9c-c4f3d0ee4038
-- title:
--   Block decomposition of $\mathrm{End}\,V$ (BG Proposition 2.4(c)/(g))
-- statement:
--   Towards step (g) of Proposition 2.4 of Bender–Glauberman, *Local Analysis for the Odd Order Theorem*: $\dim E_m=\sum_i n_i n_{i+m}$ for the conjugation eigenspaces $E_m$, via the block decomposition $\mathrm{End}\,V=\bigoplus_{i,t}\mathrm{Hom}(V_i,V_t)$. It also reaches Proposition 2.4(h), $\sum_i(n_i-n_{i+m})^2=2(\dim E_0-\dim E_m)$.
--
--   Main declarations: `isInternal_cyclicHomBlockFin` (The `(i,t)`-blocks form an internal direct sum `End V = ⊕_{i,t} E_{i,t}` (BG Prop 2.4(c))); `finrank_iSup_of_iSupIndep`; `finrank_iSup_cyclicHomBlockFin_diagonal`; `finrank_cyclicEndConjEigenspaceFin` (BG Proposition 2.4(g)); and 1 more.
--
--   The bundle also proves 5 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/RepresentationTheory/EigenspaceBlockDecomp.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/RepresentationTheory/EigenspaceBlockDecomp.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_EigenspaceUnderCyclicAction
import Mathlib.LinearAlgebra.Trace

namespace OddOrder.RepresentationTheory

open Finset EigenspaceUnderCyclicAction

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

/-- **Reconstruction of a vector from its eigenspace components.** -/
theorem sum_cyclicEigenspaceFinDecomposition_eq {epsilon : F} {g : Module.End F V} {h : ℕ}
    (hV : DirectSum.IsInternal (cyclicEigenspaceFinFamily epsilon g h)) (v : V) :
    ∑ i, ((cyclicEigenspaceFinDecomposition hV v i :
      cyclicEigenspaceFinFamily epsilon g h i) : V) = v := by
  classical
  have hcoe : DirectSum.coeLinearMap (cyclicEigenspaceFinFamily epsilon g h)
      (cyclicEigenspaceFinDecomposition hV v) = v :=
    (LinearEquiv.ofBijective (DirectSum.coeLinearMap (cyclicEigenspaceFinFamily epsilon g h))
      hV).apply_symm_apply v
  conv_rhs => rw [← hcoe, DirectSum.coeLinearMap_eq_dfinsuppSum]
  rw [DFinsupp.sum_eq_sum_fintype _ (fun _ => rfl)]
  simp

/-- **Every endomorphism is the sum of its `(i,t)`-blocks** (BG Prop 2.4(c), spanning half). -/
theorem sum_cyclicHomBlockFinProjection_eq {epsilon : F} {g : Module.End F V} {h : ℕ}
    [FiniteDimensional F V] (hV : DirectSum.IsInternal (cyclicEigenspaceFinFamily epsilon g h))
    (e : Module.End F V) :
    ∑ p : Fin h × Fin h, ((cyclicHomBlockFinProjection hV p.1 p.2 e : Module.End F V)) = e := by
  classical
  ext v
  have hv : v ∈ ⨆ j, cyclicEigenspaceFinFamily epsilon g h j := by
    rw [hV.submodule_iSup_eq_top]; trivial
  induction hv using Submodule.iSup_induction' with
  | mem j w hw =>
    rw [LinearMap.sum_apply, Fintype.sum_prod_type, Finset.sum_eq_single j]
    · rw [Finset.sum_congr rfl
        (fun t _ => cyclicHomBlockFinProjection_apply_of_mem_same hV e hw)]
      exact sum_cyclicEigenspaceFinDecomposition_eq hV (e w)
    · intro i _ hi
      exact Finset.sum_eq_zero
        (fun t _ => cyclicHomBlockFinProjection_apply_of_mem_ne hV (Ne.symm hi) e hw)
    · intro hj; exact absurd (mem_univ j) hj
  | zero => simp
  | add x y _ _ ihx ihy => rw [map_add, map_add, ihx, ihy]

/-- The `(i,t)`-blocks span all of `End V` (BG Prop 2.4(c), supremum form). -/
theorem iSup_cyclicHomBlockFin_eq_top {epsilon : F} {g : Module.End F V} {h : ℕ}
    [FiniteDimensional F V] (hV : DirectSum.IsInternal (cyclicEigenspaceFinFamily epsilon g h)) :
    ⨆ p : Fin h × Fin h, cyclicHomBlockFin epsilon g p.1 p.2 = ⊤ := by
  rw [eq_top_iff]
  intro e _
  rw [← sum_cyclicHomBlockFinProjection_eq hV e]
  exact Submodule.sum_mem _ fun p _ =>
    Submodule.mem_iSup_of_mem p (Submodule.coe_mem _)

open Module in
/-- **The `(i,t)`-blocks form an internal direct sum** `End V = ⊕_{i,t} E_{i,t}` (BG Prop 2.4(c)).
The blocks span (`iSup_cyclicHomBlockFin_eq_top`) and
`∑ dim E_{i,t} = (∑ nᵢ)² = (dim V)² = dim End`, so the coercion `⊕ E_{i,t} → End` is a surjection
between equal-dimensional spaces, hence bijective. -/
theorem isInternal_cyclicHomBlockFin {epsilon : F} {g : Module.End F V} {h : ℕ}
    [FiniteDimensional F V] (hV : DirectSum.IsInternal (cyclicEigenspaceFinFamily epsilon g h)) :
    DirectSum.IsInternal (fun p : Fin h × Fin h => cyclicHomBlockFin epsilon g p.1 p.2) := by
  classical
  have hsurj : Function.Surjective (DirectSum.coeLinearMap
      (fun p : Fin h × Fin h => cyclicHomBlockFin epsilon g p.1 p.2)) := by
    rw [← LinearMap.range_eq_top, DirectSum.range_coeLinearMap, iSup_cyclicHomBlockFin_eq_top hV]
  have hsumV : ∑ i, cyclicEigenspaceFinDim epsilon g (i : Fin h) = finrank F V := by
    rw [← (LinearEquiv.ofBijective
      (DirectSum.coeLinearMap (cyclicEigenspaceFinFamily epsilon g h)) hV).finrank_eq,
      finrank_directSum]
  have hfin : finrank F (DirectSum (Fin h × Fin h)
      (fun p => cyclicHomBlockFin epsilon g p.1 p.2)) = finrank F (Module.End F V) := by
    rw [finrank_directSum]
    simp_rw [finrank_cyclicHomBlockFin hV]
    rw [Fintype.sum_prod_type, ← Finset.sum_mul_sum, hsumV, Module.finrank_linearMap]
  have : ∀ p : Fin h × Fin h, FiniteDimensional F (cyclicHomBlockFin epsilon g p.1 p.2) :=
    fun _ => inferInstance
  have : FiniteDimensional F (DirectSum (Fin h × Fin h)
      (fun p => cyclicHomBlockFin epsilon g p.1 p.2)) :=
    Module.Finite.equiv (DirectSum.linearEquivFunOnFintype F (Fin h × Fin h)
      (fun p => cyclicHomBlockFin epsilon g p.1 p.2)).symm
  refine ⟨?_, hsurj⟩
  intro x y hxy
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (K := F)
    (f := DirectSum.coeLinearMap (R := F)
      (fun p : Fin h × Fin h => cyclicHomBlockFin epsilon g p.1 p.2)) hfin).mpr hsurj
  simpa only [DirectSum.coeLinearMap_eq_dfinsuppSum,
    DirectSum.coeAddMonoidHom_eq_dfinsuppSum] using hxy

open Module in
open Module in
/-- For an **independent** finite family of submodules of a finite-dimensional space, the dimension
of the supremum is the sum of the dimensions. (mathlib has the `IsInternal` finrank facts but not
this `iSupIndep`-only form; here `⨆ p k` need not be all of `M`.) -/
theorem finrank_iSup_of_iSupIndep {M : Type*} [AddCommGroup M] [Module F M]
    [FiniteDimensional F M] {κ : Type*} [Fintype κ]
    (p : κ → Submodule F M) (hp : iSupIndep p) :
    finrank F ((⨆ k, p k : Submodule F M)) = ∑ k, finrank F (p k) := by
  classical
  have hinj : Function.Injective (DirectSum.coeLinearMap p) := hp.dfinsupp_lsum_injective
  have e := (LinearEquiv.ofInjective (DirectSum.coeLinearMap p) hinj).trans
      (LinearEquiv.ofEq _ _ (DirectSum.range_coeLinearMap (A := p)))
  rw [← e.finrank_eq, finrank_directSum]

open Module in
/-- **The `m`-diagonal of blocks** `⨆ᵢ E_{i, i+m}` has dimension `∑ᵢ nᵢ·nᵢ₊ₘ` (the right-hand side
of BG Prop 2.4(g)). The diagonal blocks form an independent sub-family of the full block
decomposition `isInternal_cyclicHomBlockFin`, so the finrank is additive over `i`. -/
theorem finrank_iSup_cyclicHomBlockFin_diagonal {epsilon : F} {g : Module.End F V} {h : ℕ}
    [FiniteDimensional F V] (hV : DirectSum.IsInternal (cyclicEigenspaceFinFamily epsilon g h))
    (m : Fin h) :
    finrank F ((⨆ i, cyclicHomBlockFin epsilon g i (i + m) : Submodule F (Module.End F V)))
      = ∑ i : Fin h,
          cyclicEigenspaceFinDim epsilon g i * cyclicEigenspaceFinDim epsilon g (i + m) := by
  have hindep : iSupIndep (fun i : Fin h => cyclicHomBlockFin epsilon g i (i + m)) :=
    (isInternal_cyclicHomBlockFin hV).submodule_iSupIndep.comp
      (f := fun i : Fin h => (i, i + m)) (fun _ _ hab => congrArg Prod.fst hab)
  rw [finrank_iSup_of_iSupIndep _ hindep]
  exact Finset.sum_congr rfl fun i _ => finrank_cyclicHomBlockFin hV i (i + m)

/-- The `m`-diagonal of blocks lies in the conjugation `εᵐ`-eigenspace: `⨆ᵢ E_{i,i+m} ≤ E_m`
(BG Prop 2.4(e)/(f), supremum form). -/
theorem iSup_cyclicHomBlockFin_diagonal_le {epsilon : F} (hε : epsilon ≠ 0)
    {g : LinearMap.GeneralLinearGroup F V} {h : ℕ}
    (hspan : Submodule.span F (cyclicEigenspaceFinUnion epsilon (g : Module.End F V) h) = ⊤)
    (hperiod : epsilon ^ h = 1) (m : Fin h) :
    (⨆ i, cyclicHomBlockFin epsilon (g : Module.End F V) i (i + m))
      ≤ cyclicEndConjEigenspaceFin epsilon g m := by
  refine iSup_le fun i =>
    cyclicHomBlockFin_le_cyclicEndConjEigenspace_of_modEq hε hspan hperiod ?_
  show i.1 + m.1 ≡ ((i + m : Fin h) : ℕ) [MOD h]
  rw [Fin.val_add]
  exact (Nat.mod_modEq _ _).symm

open Module in
/-- **BG Proposition 2.4(g).** For the conjugation `εᵐ`-eigenspace `E_m` on `End V`,
`dim E_m = ∑ᵢ nᵢ·nᵢ₊ₘ` where `nᵢ = dim Vᵢ`. Sandwich: each diagonal `⨆ᵢ E_{i,i+m} ≤ E_m` gives
`∑ᵢ nᵢnᵢ₊ₘ ≤ dim E_m`; the `E_m` are independent (distinct eigenvalues) so `∑ₘ dim E_m ≤ dim End`;
and `∑ₘ ∑ᵢ nᵢnᵢ₊ₘ = (∑ nᵢ)² = (dim V)² = dim End`, forcing termwise equality. -/
theorem finrank_cyclicEndConjEigenspaceFin {epsilon : F}
    {g : LinearMap.GeneralLinearGroup F V} {h : ℕ} [NeZero h] [FiniteDimensional F V]
    (hprim : IsPrimitiveRoot epsilon h)
    (hV : DirectSum.IsInternal (cyclicEigenspaceFinFamily epsilon (g : Module.End F V) h))
    (m : Fin h) :
    finrank F (cyclicEndConjEigenspaceFin epsilon g m)
      = ∑ i, cyclicEigenspaceFinDim epsilon (g : Module.End F V) i
          * cyclicEigenspaceFinDim epsilon (g : Module.End F V) (i + m) := by
  set n : Fin h → ℕ := fun i => cyclicEigenspaceFinDim epsilon (g : Module.End F V) i with hn
  have hε : epsilon ≠ 0 := hprim.ne_zero (NeZero.ne h)
  have hperiod : epsilon ^ h = 1 := hprim.pow_eq_one
  have hspan := span_cyclicEigenspaceFinUnion_eq_top_of_isInternal hV
  -- `∑ᵢ nᵢnᵢ₊ₘ' ≤ dim E_{m'}` for every `m'`
  have hge : ∀ m' : Fin h, (∑ i, n i * n (i + m'))
      ≤ finrank F (cyclicEndConjEigenspaceFin epsilon g m') := fun m' => by
    rw [← finrank_iSup_cyclicHomBlockFin_diagonal hV m']
    exact Submodule.finrank_mono (iSup_cyclicHomBlockFin_diagonal_le hε hspan hperiod m')
  -- the conjugation eigenspaces are independent (distinct eigenvalues)
  have hindep : iSupIndep (fun m' : Fin h => cyclicEndConjEigenspaceFin epsilon g m') :=
    cyclicEigenspaceFin_iSupIndep (g := cyclicEndConj g) hprim
  have hle : (∑ m' : Fin h, finrank F (cyclicEndConjEigenspaceFin epsilon g m'))
      ≤ finrank F (Module.End F V) := by
    rw [← finrank_iSup_of_iSupIndep _ hindep]
    exact Submodule.finrank_le _
  have hsumV : ∑ i, n i = finrank F V := by
    rw [← (LinearEquiv.ofBijective
      (DirectSum.coeLinearMap (cyclicEigenspaceFinFamily epsilon (g : Module.End F V) h))
      hV).finrank_eq, finrank_directSum]
  -- `∑ₘ ∑ᵢ nᵢnᵢ₊ₘ = (dim V)² = dim End`
  have htotal : (∑ m' : Fin h, ∑ i, n i * n (i + m')) = finrank F (Module.End F V) := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    have hreindex : ∀ i : Fin h, (∑ m', n (i + m')) = ∑ j, n j := fun i =>
      Equiv.sum_comp (Equiv.addLeft i) n
    simp_rw [hreindex]
    rw [← Finset.sum_mul, hsumV, Module.finrank_linearMap]
  -- termwise equality from the sandwich
  have hsum_ab : (∑ m' : Fin h, ∑ i, n i * n (i + m'))
      = ∑ m' : Fin h, finrank F (cyclicEndConjEigenspaceFin epsilon g m') :=
    le_antisymm (Finset.sum_le_sum fun m' _ => hge m') (hle.trans_eq htotal.symm)
  exact ((Finset.sum_eq_sum_iff_of_le fun m' _ => hge m').mp hsum_ab m (mem_univ m)).symm

/-- Elementary sum-of-squares identity: if `∑ bᵢ² = ∑ aᵢ²` then
`∑ (aᵢ − bᵢ)² = 2 ∑ aᵢ² − 2 ∑ aᵢbᵢ`. -/
theorem sum_sub_sq_of_sum_sq_eq {ι : Type*} [Fintype ι] (a b : ι → ℤ)
    (hab : ∑ i, b i ^ 2 = ∑ i, a i ^ 2) :
    ∑ i, (a i - b i) ^ 2 = 2 * ∑ i, a i ^ 2 - 2 * ∑ i, a i * b i := by
  have hexp : ∑ i, (a i - b i) ^ 2
      = ∑ i, a i ^ 2 - 2 * ∑ i, a i * b i + ∑ i, b i ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hexp, hab]; ring

open Module in
/-- **BG Proposition 2.4(h).** `∑ᵢ (nᵢ − nᵢ₊ₘ)² = 2 (dim E₀ − dim E_m)` (worked over `ℤ`; here
`nᵢ = dim Vᵢ` and `E_m` is the conjugation `εᵐ`-eigenspace). Combined with the Theorem 2.5
hypothesis `dim E₀ = dim E_m + 1` (`m ≠ 0`), this gives `∑ᵢ(nᵢ−nᵢ₊ₘ)² = 2`, feeding `prop24j`. -/
theorem sum_sq_sub_finrank_cyclicEndConjEigenspaceFin {epsilon : F}
    {g : LinearMap.GeneralLinearGroup F V} {h : ℕ} [NeZero h] [FiniteDimensional F V]
    (hprim : IsPrimitiveRoot epsilon h)
    (hV : DirectSum.IsInternal (cyclicEigenspaceFinFamily epsilon (g : Module.End F V) h))
    (m : Fin h) :
    (∑ i, ((cyclicEigenspaceFinDim epsilon (g : Module.End F V) i : ℤ)
        - (cyclicEigenspaceFinDim epsilon (g : Module.End F V) (i + m) : ℤ)) ^ 2)
      = 2 * ((finrank F (cyclicEndConjEigenspaceFin epsilon g (0 : Fin h)) : ℤ)
        - (finrank F (cyclicEndConjEigenspaceFin epsilon g m) : ℤ)) := by
  set a : Fin h → ℤ := fun i => (cyclicEigenspaceFinDim epsilon (g : Module.End F V) i : ℤ) with ha
  have hreindex : ∑ i, a (i + m) ^ 2 = ∑ i, a i ^ 2 :=
    Equiv.sum_comp (Equiv.addRight m) (fun j => a j ^ 2)
  rw [sum_sub_sq_of_sum_sq_eq a (fun i => a (i + m)) hreindex,
    finrank_cyclicEndConjEigenspaceFin hprim hV (0 : Fin h),
    finrank_cyclicEndConjEigenspaceFin hprim hV m]
  push_cast
  simp_rw [add_zero]
  simp only [ha]
  ring

end OddOrder.RepresentationTheory


