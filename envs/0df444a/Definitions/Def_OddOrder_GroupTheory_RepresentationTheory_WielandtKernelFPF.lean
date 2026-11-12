-- Prove2me | Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_WielandtKernelFPF
-- name    : OddOrder_GroupTheory_RepresentationTheory_WielandtKernelFPF
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:10:38.977954+00:00
-- url     : https://prove2.me/theorems/f4cab789-6b0d-43b3-adef-e199680befde
-- title:
--   Peterfalvi (9.1): the kernel-FPF dimension fact ($\dagger$) over an algebraically closed field
-- statement:
--   Assembles the kernel fixed-point-free dimension fact ($\dagger$) of Peterfalvi (9.1): for a finite group $\Gamma$ acting through $\psi:\Gamma\to\mathrm{Aut}(G)$ on a $p'$-group $G$ over an algebraically closed field. Along the way it shows the averaging idempotent is central, absorbs multiplication, is the trivial primitive central idempotent, and that the trivial isotypic component is the space of $G$-invariants.
--
--   Main declarations: `average_mul` (The averaging idempotent absorbs right multiplication); `mul_average` (The averaging idempotent absorbs left multiplication too: `z · average = (aug z) • average`); `average_mem_center` (The averaging idempotent is central in `k[G]`); `symm_single_eq_average` (The trivial primitive central idempotent is the averaging idempotent); and 4 more.
--
--   The bundle also proves 3 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/RepresentationTheory/WielandtKernelFPF.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/RepresentationTheory/WielandtKernelFPF.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CenterOrbitFree
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CenterProjConjugation
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_WielandtCounting
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_FreeBlockPermutation
import Mathlib.GroupTheory.GroupAction.Quotient

namespace OddOrder.GroupTheory.WielandtKernelFPF

open OddOrder.GroupTheory.CenterSimplesOrbit (simplesAction)

open OddOrder.GroupTheory.CenterOrbitFree (gamma_free_off_trivial_simple)

open MulAction

variable {G : Type*} [Group G] [Finite G]

/-- **Peterfalvi (9.1), item 1 — the free `Γ`-action on the nontrivial simples.**
Fix a splitting `φ : Z(k[G]) ≃ₐ[k] (Fin N → k)` and let a finite group `Γ` act through
`ψ : Γ →* MulAut G` so that every nonidentity `ψ γ` is fixed-point-free (`hfpf`) with `⟨ψ γ⟩`
coprime to `|G|` (`hcop`).  Then on the simples `Fin N` (acted on by `simplesAction φ ∘ ψ`) there is
a simple `i₀` — the trivial one — fixed by all of `Γ`, and `Γ` acts **freely off it**: for `i ≠ i₀`,
any `γ` fixing `i` is the identity.

This is `gamma_free_off_trivial_simple` (3d.3c) packaged with the canonical induced `Γ`-actions
(`Γ` on `ConjClasses G` via `ψ`, `Γ` on `Fin N` via `simplesAction φ ∘ ψ`), with the orbit-size
statement converted to triviality of the point stabilisers off `i₀`. -/
theorem exists_fixed_simple_free_of_fpf
    {k : Type*} [Field k] {N : ℕ}
    (φ : Subalgebra.center k (MonoidAlgebra k G) ≃ₐ[k] (Fin N → k))
    {Γ : Type*} [Group Γ] [Finite Γ] (ψ : Γ →* MulAut G)
    (hd : 1 < Nat.card Γ)
    (hcop : ∀ γ : Γ, γ ≠ 1 → Nat.Coprime (Nat.card ↥(Subgroup.zpowers (ψ γ))) (Nat.card G))
    (hfpf : ∀ γ : Γ, γ ≠ 1 → ∀ x : G, ψ γ x = x → x = 1) :
    ∃ i₀ : Fin N,
      (∀ γ : Γ, simplesAction φ (ψ γ) i₀ = i₀) ∧
      (∀ (i : Fin N) (γ : Γ), i ≠ i₀ → simplesAction φ (ψ γ) i = i → γ = 1) := by
  classical
  have : Fintype G := Fintype.ofFinite _
  have : Finite (ConjClasses G) := Finite.of_surjective _ ConjClasses.mk_surjective
  have : Fintype (ConjClasses G) := Fintype.ofFinite _
  -- The canonical induced `Γ`-actions, through which 3d.3c applies (`hcl`/`hsi` are then `rfl`).
  let mulCl : MulAction Γ (ConjClasses G) := MulAction.compHom (ConjClasses G) ψ
  let mulSi : MulAction Γ (Fin N) := MulAction.compHom (Fin N) ((simplesAction φ).comp ψ)
  have hcl : ∀ (γ : Γ) (C : ConjClasses G), γ • C = ψ γ • C := fun _ _ => rfl
  have hsi : ∀ (γ : Γ) (i : Fin N), γ • i = simplesAction φ (ψ γ) i := fun _ _ => rfl
  obtain ⟨i₀, hi₀fix, hi₀uniq, hi₀free⟩ :=
    gamma_free_off_trivial_simple φ ψ hcl hsi hd hcop hfpf
  refine ⟨i₀, fun γ => ?_, fun i γ hi hfix => ?_⟩
  · -- `i₀` is fixed by every `γ`: read `mem_fixedPoints` through `hsi`.
    have := mem_fixedPoints.mp hi₀fix γ
    rwa [hsi] at this
  · -- `i ≠ i₀ ⟹ i ∉ fixedPoints` (uniqueness) ⟹ `|orbit i| = |Γ|` ⟹ trivial stabiliser.
    have hi_nf : i ∉ fixedPoints Γ (Fin N) := fun hc => hi (hi₀uniq i hc)
    have horb : Nat.card (orbit Γ i) = Nat.card Γ := hi₀free i hi_nf
    -- orbit–stabiliser: `|Γ| = |orbit i| · |stab i|`, so `|stab i| = 1`, hence `stab i = ⊥`.
    have hqs : Nat.card (Γ ⧸ stabilizer Γ i) = Nat.card Γ := by
      rw [← Nat.card_congr (orbitEquivQuotientStabilizer Γ i), horb]
    have hstab1 : Nat.card ↥(stabilizer Γ i) = 1 := by
      have hmul := Subgroup.card_mul_index (stabilizer Γ i)
      rw [Subgroup.index_eq_card, hqs] at hmul
      have hpos : 0 < Nat.card Γ := Nat.card_pos
      have h1 : Nat.card ↥(stabilizer Γ i) * Nat.card Γ = 1 * Nat.card Γ := by
        rw [one_mul]; exact hmul
      exact Nat.eq_of_mul_eq_mul_right hpos h1
    have hstabbot : stabilizer Γ i = ⊥ := Subgroup.card_eq_one.mp hstab1
    have hγstab : γ ∈ stabilizer Γ i := by
      rw [mem_stabilizer_iff, hsi]; exact hfix
    rw [hstabbot, Subgroup.mem_bot] at hγstab
    exact hγstab

section TrivialIsotypic

open MonoidAlgebra Representation GroupAlgebra

open OddOrder.GroupTheory.CenterClassSum (centerRep)

open OddOrder.GroupTheory.CenterSimplesOrbit (aug aug_apply aug_centerRep
  centerRep_apply_symm_single)

open OddOrder.GroupTheory.CenterModuleDecomp (centerProj)

variable {k : Type*} [Field k] [Fintype G] [Invertible (Fintype.card G : k)]

omit [Finite G] in
/-- **The averaging idempotent absorbs right multiplication.**  `average · z = (aug z) • average`
for every `z ∈ k[G]`: right-multiplying by a group element fixes `average`
(`GroupAlgebra.mul_average_right`), and a general `z` contributes its augmentation coefficient. -/
theorem average_mul (z : MonoidAlgebra k G) :
    average k G * z = MonoidAlgebra.lift k k G 1 z • average k G := by
  induction z using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [mul_add, hx, hy, map_add, add_smul]
  | single g b =>
    rw [MonoidAlgebra.lift_single, MonoidHom.one_apply, smul_eq_mul, mul_one,
      show (MonoidAlgebra.single g b : MonoidAlgebra k G) = b • MonoidAlgebra.single g 1 by
        rw [MonoidAlgebra.smul_single, smul_eq_mul, mul_one],
      mul_smul_comm, GroupAlgebra.mul_average_right]

omit [Finite G] in
/-- The averaging idempotent absorbs left multiplication too: `z · average = (aug z) • average`. -/
theorem mul_average (z : MonoidAlgebra k G) :
    z * average k G = MonoidAlgebra.lift k k G 1 z • average k G := by
  induction z using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [add_mul, hx, hy, map_add, add_smul]
  | single g b =>
    rw [MonoidAlgebra.lift_single, MonoidHom.one_apply, smul_eq_mul, mul_one,
      show (MonoidAlgebra.single g b : MonoidAlgebra k G) = b • MonoidAlgebra.single g 1 by
        rw [MonoidAlgebra.smul_single, smul_eq_mul, mul_one],
      smul_mul_assoc, GroupAlgebra.mul_average_left]

omit [Finite G] in
/-- The averaging idempotent is central in `k[G]`. -/
theorem average_mem_center : average k G ∈ Subalgebra.center k (MonoidAlgebra k G) :=
  Subalgebra.mem_center_iff.mpr fun z => by rw [average_mul, mul_average]

variable {N : ℕ} (φ : Subalgebra.center k (MonoidAlgebra k G) ≃ₐ[k] (Fin N → k))

omit [Finite G] in
/-- **The trivial primitive central idempotent is the averaging idempotent.**  If `i₀` is the
augmentation coordinate (`φ z i₀ = aug z` for all `z`), then `φ.symm (Pi.single i₀ 1) = average`.
Proof: writing `a := ⟨average, _⟩ ∈ Z`, `a · ε_{i₀} = average` (since `aug ε_{i₀} = 1`), so
`φ a · Pi.single i₀ 1 = φ a`, forcing `φ a = Pi.single i₀ (φ a i₀)`; and `φ a i₀ = aug a = 1`. -/
theorem symm_single_eq_average {i₀ : Fin N} (haug : ∀ z, φ z i₀ = aug z) :
    ((φ.symm (Pi.single i₀ 1) : Subalgebra.center k (MonoidAlgebra k G)) : MonoidAlgebra k G)
      = average k G := by
  set a : Subalgebra.center k (MonoidAlgebra k G) := ⟨average k G, average_mem_center⟩ with ha
  -- `aug (φ.symm (Pi.single i₀ 1)) = 1`.
  have haug1 : aug (φ.symm (Pi.single i₀ 1)) = 1 := by
    rw [← haug, AlgEquiv.apply_symm_apply, Pi.single_eq_same]
  -- `aug a = 1` (the augmentation of the averaging idempotent).
  have hauga : aug a = 1 := by
    rw [aug_apply]
    change MonoidAlgebra.lift k k G 1 (average k G) = 1
    rw [show average k G = ⅟(Fintype.card G : k) • ∑ g : G, MonoidAlgebra.of k G g from rfl,
      map_smul, map_sum]
    rw [show (∑ g : G, MonoidAlgebra.lift k k G 1 (MonoidAlgebra.of k G g))
          = (Fintype.card G : k) by
          simp only [MonoidAlgebra.lift_of, MonoidHom.one_apply, Finset.sum_const, Finset.card_univ,
            nsmul_eq_mul, mul_one],
      smul_eq_mul, invOf_mul_self]
  -- `a * φ.symm (Pi.single i₀ 1) = a` (from `average · z = aug z • average` and `aug ε_{i₀} = 1`).
  have hstep : a * φ.symm (Pi.single i₀ 1) = a := by
    apply Subtype.ext
    change average k G * ((φ.symm (Pi.single i₀ 1) : _) : MonoidAlgebra k G) = average k G
    rw [average_mul, show MonoidAlgebra.lift k k G 1
        ((φ.symm (Pi.single i₀ 1) : Subalgebra.center k (MonoidAlgebra k G)) : MonoidAlgebra k G)
        = aug (φ.symm (Pi.single i₀ 1)) from rfl, haug1, one_smul]
  -- Apply `φ`: `φ a * Pi.single i₀ 1 = φ a`, hence `φ a = Pi.single i₀ (φ a i₀)`.
  have hφstep : φ a * Pi.single i₀ 1 = φ a := by
    conv_lhs => rw [show (Pi.single i₀ 1 : Fin N → k) = φ (φ.symm (Pi.single i₀ 1)) from
      (AlgEquiv.apply_symm_apply φ _).symm]
    rw [← map_mul, hstep]
  have hsupp : φ a = Pi.single i₀ (φ a i₀) := by
    funext j
    have hj := congrFun hφstep j
    simp only [Pi.mul_apply, Pi.single_apply, mul_ite, mul_one, mul_zero] at hj
    rw [Pi.single_apply]
    by_cases h : j = i₀
    · subst h; simp
    · rw [if_neg h] at hj ⊢; exact hj.symm
  -- The single coordinate is `1` (`φ a i₀ = aug a = 1`).
  have hval : φ a i₀ = 1 := by rw [haug, hauga]
  rw [hval] at hsupp
  -- `a = φ.symm (Pi.single i₀ 1)`, so `average = (φ.symm (Pi.single i₀ 1)).val`.
  have hae : a = φ.symm (Pi.single i₀ 1) := by rw [← AlgEquiv.symm_apply_apply φ a, hsupp]
  rw [← hae]

omit [Finite G] in
/-- **The trivial isotypic projection is the averaging projection.**  For the augmentation
coordinate `i₀`, `centerProj φ ρ i₀ = averageMap ρ`. -/
theorem centerProj_aug_eq_averageMap {W : Type*} [AddCommGroup W] [Module k W]
    (ρ : Representation k G W) {i₀ : Fin N} (haug : ∀ z, φ z i₀ = aug z) :
    centerProj φ ρ i₀ = averageMap ρ := by
  change asAlgebraHom ρ ((φ.symm (Pi.single i₀ 1) : _) : MonoidAlgebra k G)
    = asAlgebraHom ρ (average k G)
  rw [symm_single_eq_average φ haug]

omit [Finite G] in
/-- **The trivial isotypic component equals the `G`-invariants** (item 2, ingredient g).  For the
augmentation coordinate `i₀`, `range (centerProj φ ρ i₀) = invariants ρ`.  In particular, if
`Wᴳ = 0` then the trivial summand vanishes. -/
theorem range_centerProj_aug_eq_invariants {W : Type*} [AddCommGroup W] [Module k W]
    (ρ : Representation k G W) {i₀ : Fin N} (haug : ∀ z, φ z i₀ = aug z) :
    LinearMap.range (centerProj φ ρ i₀) = invariants ρ := by
  rw [centerProj_aug_eq_averageMap φ ρ haug]
  exact (isProj_averageMap ρ).range

omit [Finite G] in
omit [Invertible (Fintype.card G : k)] in
omit [Fintype G] in
/-- The augmentation coordinate `i₀` is fixed by every `simplesAction φ α` (it is *the* trivial
simple).  Proof: applying `aug` to `centerRep_apply_symm_single` and using `aug`-invariance of
`centerRep` (`aug_centerRep`) shows the idempotent at `simplesAction φ α i₀` has augmentation `1`,
which (read through `φ z i₀ = aug z`) pins that coordinate to `i₀`. -/
theorem simplesAction_fixed_of_aug {i₀ : Fin N} (haug : ∀ z, φ z i₀ = aug z) (α : MulAut G) :
    simplesAction φ α i₀ = i₀ := by
  have key : aug (φ.symm (Pi.single (simplesAction φ α i₀) 1)) = aug (φ.symm (Pi.single i₀ 1)) := by
    rw [← centerRep_apply_symm_single φ α i₀, aug_centerRep]
  rw [← haug, ← haug, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply, Pi.single_eq_same,
    Pi.single_apply] at key
  by_contra h
  rw [if_neg (Ne.symm h)] at key
  exact zero_ne_one key

omit [Fintype G] in
omit [Finite G] in
omit [Invertible (Fintype.card G : k)] in
/-- **The augmentation coordinate exists** (the trivial simple).  There is `i₀ : Fin N` with
`φ z i₀ = aug z` for every `z` — the augmentation read through the splitting — and it is fixed by
every `simplesAction φ α`.  This is the simple whose isotypic component is the `G`-invariants
(`range_centerProj_aug_eq_invariants`). -/
theorem exists_aug_coordinate :
    ∃ i₀ : Fin N, (∀ z, φ z i₀ = aug z) ∧ (∀ α : MulAut G, simplesAction φ α i₀ = i₀) := by
  obtain ⟨i₀, hi₀⟩ := PiAlgebraAut.algHom_pi_eq_eval (aug.comp φ.symm.toAlgHom)
  have haug : ∀ z, φ z i₀ = aug z := by
    intro z
    have h := hi₀ (φ z)
    rw [AlgHom.comp_apply, AlgEquiv.toAlgHom_apply, AlgEquiv.symm_apply_apply] at h
    exact h.symm
  exact ⟨i₀, haug, fun α => simplesAction_fixed_of_aug φ haug α⟩

end TrivialIsotypic

/-- If `V = ⊕_{i:ι} A i` internally and one summand `A i₀ = ⊥`, then dropping it still gives an
internal direct sum `V = ⊕_{i ≠ i₀} A i`.  (Used to restrict the isotypic decomposition to the
nontrivial simples, where the Frobenius complement acts freely.) -/
theorem isInternal_restrict_ne {R M ι : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [DecidableEq ι] {A : ι → Submodule R M} (hint : DirectSum.IsInternal A) {i₀ : ι}
    (h0 : A i₀ = ⊥) :
    DirectSum.IsInternal (fun i : {i : ι // i ≠ i₀} => A i.val) := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top] at hint ⊢
  obtain ⟨hind, hsup⟩ := hint
  refine ⟨hind.comp Subtype.val_injective, le_antisymm le_top ?_⟩
  rw [← hsup]
  refine iSup_le fun i => ?_
  by_cases hi : i = i₀
  · rw [hi, h0]; exact bot_le
  · exact le_iSup (fun j : {j : ι // j ≠ i₀} => A j.val) ⟨i, hi⟩

section KernelFPF

open Module Representation

open OddOrder.GroupTheory.CenterModuleDecomp (centerProj isInternal_centerProj map_range_centerProj)

open OddOrder.GroupTheory.CenterSplitting (exists_center_algEquiv_pi)

variable {k : Type*} [Field k] [IsAlgClosed k]

variable {L : Type*} [Group L] [Finite L] {W : Type*} [AddCommGroup W] [Module k W]

variable [FiniteDimensional k W]

/-- **Peterfalvi (9.1), the kernel-FPF dimension fact (†).**  Let `L` be finite, `U ◁ L` a
`p′`-group
(`char k ∤ |U|`), `E ≤ L` with `U ⊔ E = ⊤` and `|E|` coprime to `|U|`, the conjugation action of `E`
on `U` fixed-point-free (`hfpf`).  Then for any finite-dimensional `k[L]`-module `W` with no
`U`-invariants (`Wᵁ = 0`), `dim W = |E| · dim Wᴱ`.

No hypothesis relates `char k` and `|E|`: the counting is by the block-permutation norm-map
argument, valid in every characteristic (this generality is needed by Peterfalvi Part II, Ch. II
step (3), where `r ≠ p` is a *conclusion*, not an available hypothesis).

Proof: split `W` into its `U`-isotypic components `A i = range (centerProj φ ρᵁ i)` (over a
splitting
`φ : Z(k[U]) ≃ (Fin N → k)`); the trivial component `A i₀` is `Wᵁ = 0`, so `W = ⊕_{i ≠ i₀} A i`.
The
Frobenius complement `E` permutes the `A i` by `simplesAction φ ∘ ψ` (item 0) and acts **freely**
off
`i₀` (item 1, via 3d.3c), so the free block-permutation count
`finrank_eq_card_mul_finrank_invariants_of_freeBlock` gives `dim W = |E| · dim Wᴱ`. -/
theorem finrank_eq_card_mul_finrank_invariants_kernelFPF
    (ρ : Representation k L W) {U E : Subgroup L} [U.Normal]
    [Fintype ↥E] [NeZero (Nat.card ↥U : k)]
    (_hsup : U ⊔ E = ⊤)
    (hcop : Nat.Coprime (Nat.card ↥E) (Nat.card ↥U))
    (hEnt : 1 < Nat.card ↥E)
    (hfpf : ∀ e ∈ E, e ≠ 1 → ∀ u ∈ U, e * u * e⁻¹ = u → u = 1)
    (hWU : invariants (ρ.comp U.subtype) = ⊥) :
    Module.finrank k W
      = Fintype.card ↥E * Module.finrank k ↥(invariants (ρ.comp E.subtype)) := by
  classical
  have : Finite ↥U := Subtype.finite
  have : Fintype ↥U := Fintype.ofFinite _
  have : Invertible (Fintype.card ↥U : k) :=
    invertibleOfNonzero (by rw [Nat.card_eq_fintype_card] at *; exact NeZero.ne _)
  -- The `U`-representation and a splitting of `Z(k[U])`.
  set ρU : Representation k ↥U W := ρ.comp U.subtype with hρU
  obtain ⟨N, ⟨φ⟩⟩ := exists_center_algEquiv_pi k ↥U
  -- The conjugation action `ψ : E → MulAut U`, fixed-point-free and coprime off the identity.
  set ψ : ↥E →* MulAut ↥U := (MulAut.conjNormal (H := U)).comp E.subtype with hψ
  have hψfpf : ∀ γ : ↥E, γ ≠ 1 → ∀ u : ↥U, ψ γ u = u → u = 1 := by
    intro γ hγ u hu
    have hγL : (γ : L) ≠ 1 := fun h => hγ (Subtype.ext h)
    have : (γ : L) * (u : L) * (γ : L)⁻¹ = (u : L) := by
      have := congrArg (Subtype.val) hu
      rwa [hψ, MonoidHom.comp_apply, MulAut.conjNormal_apply] at this
    exact Subtype.ext (hfpf (γ : L) γ.2 hγL (u : L) u.2 this)
  have hψcop : ∀ γ : ↥E, γ ≠ 1 →
      Nat.Coprime (Nat.card ↥(Subgroup.zpowers (ψ γ))) (Nat.card ↥U) := by
    intro γ _
    rw [Nat.card_zpowers]
    exact hcop.coprime_dvd_left ((orderOf_map_dvd ψ γ).trans (orderOf_dvd_natCard γ))
  -- The augmentation coordinate `i₀` (the trivial simple), fixed by all `simplesAction φ α`.
  obtain ⟨i₀, haug, hi₀fix⟩ := exists_aug_coordinate φ
  -- The isotypic family and the vanishing of the trivial summand.
  set A : Fin N → Submodule k W := fun i => LinearMap.range (centerProj φ ρU i) with hA
  have hintA : DirectSum.IsInternal A := isInternal_centerProj φ ρU
  have hAi₀ : A i₀ = ⊥ := by
    rw [hA]; dsimp only
    rw [range_centerProj_aug_eq_invariants φ ρU haug, hρU]; exact hWU
  have hintA' : DirectSum.IsInternal (fun i : {i : Fin N // i ≠ i₀} => A i.val) :=
    isInternal_restrict_ne hintA hAi₀
  -- The free `E`-action on the nontrivial simples (item 1).
  obtain ⟨i₁, hi₁fix, hi₁free⟩ := exists_fixed_simple_free_of_fpf φ ψ hEnt hψcop hψfpf
  have hi₁eq : i₁ = i₀ := by
    by_contra hne
    have : Nontrivial ↥E := Finite.one_lt_card_iff_nontrivial.mp hEnt
    obtain ⟨γ, hγ1⟩ := exists_ne (1 : ↥E)
    exact hγ1 (hi₁free i₀ γ (Ne.symm hne) (hi₀fix (ψ γ)))
  -- The `E`-action on the nontrivial-simple index set `{i ≠ i₀}`.
  let mulE : MulAction ↥E {i : Fin N // i ≠ i₀} :=
    { smul := fun e i => ⟨simplesAction φ (ψ e) i.val, fun hc => i.2
        ((simplesAction φ (ψ e)).injective (hc.trans (hi₀fix (ψ e)).symm))⟩
      one_smul := fun i => Subtype.ext (show simplesAction φ (ψ 1) i.val = i.val by
        rw [map_one, map_one, Equiv.Perm.coe_one, id_eq])
      mul_smul := fun e e' i => Subtype.ext
        (show simplesAction φ (ψ (e * e')) i.val
            = simplesAction φ (ψ e) (simplesAction φ (ψ e') i.val) by
          rw [map_mul, map_mul, Equiv.Perm.mul_apply]) }
  have hsmul : ∀ (e : ↥E) (i : {i : Fin N // i ≠ i₀}),
      (e • i).val = simplesAction φ (ψ e) i.val := fun _ _ => rfl
  -- `hperm`: `E` permutes the nontrivial isotypic summands (item 0).
  have hperm : ∀ (e : ↥E) (i : {i : Fin N // i ≠ i₀}),
      (A i.val).map ((ρ.comp E.subtype) e) = A (e • i).val := by
    intro e i
    -- `τ = ρ (e:L)` as a linear automorphism of `W`.
    let τ : W ≃ₗ[k] W := LinearEquiv.ofLinearMap (ρ (e : L)) (ρ ((e : L)⁻¹))
      (by rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]; rfl)
      (by rw [← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one]; rfl)
    have hτcoe : (τ : W →ₗ[k] W) = ρ (e : L) := rfl
    have hintertwine : ∀ u : ↥U,
        (τ : Module.End k W) * ρU u = ρU (ψ e u) * (τ : Module.End k W) := by
      intro u
      change ρ (e : L) * ρ ((u : L)) = ρ ((ψ e u : ↥U) : L) * ρ (e : L)
      rw [← map_mul, ← map_mul]
      congr 1
      rw [show ((ψ e u : ↥U) : L) = (e : L) * (u : L) * (e : L)⁻¹ from
        MulAut.conjNormal_apply (e : L) u]
      group
    have hmap := map_range_centerProj φ ρU τ (ψ e) hintertwine i.val
    rw [hτcoe] at hmap
    rw [show ((ρ.comp E.subtype) e : W →ₗ[k] W) = ρ (e : L) from rfl, hmap, hsmul]
  -- `hfree`: `E` acts freely (item 1, transported through `i₁ = i₀`).
  have hfree : ∀ (e : ↥E) (i : {i : Fin N // i ≠ i₀}), e • i = i → e = 1 := by
    intro e i hei
    refine hi₁free i.val e (hi₁eq ▸ i.2) ?_
    have := congrArg Subtype.val hei
    rwa [hsmul] at this
  -- Apply the free block-permutation count (characteristic-free) to the nontrivial summands.
  have hcount := Representation.finrank_eq_card_mul_finrank_invariants_of_freeBlock
    (ρ := ρ) (H := E) hintA' hfree hperm
  rwa [Nat.card_eq_fintype_card] at hcount

end KernelFPF

end OddOrder.GroupTheory.WielandtKernelFPF


