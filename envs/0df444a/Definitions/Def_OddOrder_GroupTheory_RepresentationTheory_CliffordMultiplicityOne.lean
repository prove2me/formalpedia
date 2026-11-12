-- Prove2me | Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CliffordMultiplicityOne
-- name    : OddOrder_GroupTheory_RepresentationTheory_CliffordMultiplicityOne
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T04:44:34.003626+00:00
-- url     : https://prove2.me/theorems/a88b0e89-f164-4d49-b101-5879826274ce
-- title:
--   Clifford multiplicity one: the restriction $V_H$ is irreducible
-- statement:
--   The final step of Bender–Glauberman Proposition 2.2(a): with $V_H$ already known to be isotypic, the multiplicity is one, i.e. $V_H$ is itself irreducible, when $G=\langle H,x\rangle$ is cyclic over $H$, $V$ is $G$-irreducible and the field is algebraically closed.
--
--   Main definitions: `cliffordConjMap` (the $k[H]$-linear endomorphism $f\mapsto\rho(x)\circ f\circ\rho(x^{-1})$) and `cliffordConj` (conjugation by $\rho(x)$ as a $k$-algebra automorphism of $\mathrm{End}_{k[H]}V$). Results include `restriction_isSimpleModule` and `restriction_isIrreducible`.
--
--   The bundle also proves 14 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/RepresentationTheory/CliffordMultiplicityOne.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/RepresentationTheory/CliffordMultiplicityOne.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CliffordAlgClosed
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_SkolemNoether
import Mathlib.RepresentationTheory.Maschke
import Mathlib.RepresentationTheory.Semisimple
import Mathlib.LinearAlgebra.Dimension.Constructions

namespace OddOrder.RepresentationTheory

open Representation

open scoped MonoidAlgebra

variable {G : Type*} [Group G]

variable {k : Type*} [Field k]

variable {V : Type*} [AddCommGroup V] [Module k V]

section MultOne

variable (ρ : Representation k G V) (H : Subgroup G) [hH : H.Normal]

/-- Conjugating `H` by `x` then by `x⁻¹` is the identity. -/
theorem conjNormalMulAut_conjNormalMulAut_inv (x : G) (h : H) :
    conjNormalMulAut H x (conjNormalMulAut H x⁻¹ h) = h := by
  apply Subtype.ext
  simp only [conjNormalMulAut_apply_coe]
  group

/-- The induced ring automorphisms of `k[H]` for `x` and `x⁻¹` are mutually inverse. -/
theorem conjMonoidAlgRingHom_conj_inv (x : G) (r : k[↥H]) :
    conjMonoidAlgRingHom (k := k) (H := H) x (conjMonoidAlgRingHom (H := H) x⁻¹ r) = r := by
  induction r using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, ha, hb]
  | single h c =>
      rw [conjMonoidAlgRingHom_single, conjMonoidAlgRingHom_single,
        conjNormalMulAut_conjNormalMulAut_inv]

variable {H}

set_option backward.isDefEq.respectTransparency false in
/-- `ρ x⁻¹` followed by `ρ x` (as semilinear maps on the restriction) is the identity. -/
theorem conjSemilinearEnd_conj_inv (x : G) (v : (resRep ρ H).asModule) :
    conjSemilinearEnd (H := H) ρ x (conjSemilinearEnd (H := H) ρ x⁻¹ v) = v := by
  rw [conjSemilinearEnd_apply, conjSemilinearEnd_apply]
  change (show (resRep ρ H).asModule from ρ x (ρ x⁻¹ v)) = v
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
  rfl

/-- `conjSemilinearEnd ρ 1` is the identity. -/
theorem conjSemilinearEnd_one_apply (v : (resRep ρ H).asModule) :
    conjSemilinearEnd (H := H) ρ 1 v = v := by
  rw [conjSemilinearEnd_apply, map_one]; rfl

set_option backward.isDefEq.respectTransparency false in
/-- `conjSemilinearEnd ρ` is multiplicative (pointwise): `ρ (g₁ g₂) = ρ g₁ ∘ ρ g₂`. -/
theorem conjSemilinearEnd_mul_apply (g₁ g₂ : G) (v : (resRep ρ H).asModule) :
    conjSemilinearEnd (H := H) ρ (g₁ * g₂) v
      = conjSemilinearEnd (H := H) ρ g₁ (conjSemilinearEnd (H := H) ρ g₂ v) := by
  rw [conjSemilinearEnd_apply, conjSemilinearEnd_apply, conjSemilinearEnd_apply]
  change (show (resRep ρ H).asModule from ρ (g₁ * g₂) v)
    = (show (resRep ρ H).asModule from ρ g₁ (ρ g₂ v))
  rw [map_mul, Module.End.mul_apply]

/-- The `k[H]`-linear endomorphism `f ↦ ρ x ∘ f ∘ ρ x⁻¹` of the restriction.  It is `k[H]`-linear
(not merely `k`-linear) because the two conjugation twists cancel. -/
noncomputable def cliffordConjMap (x : G)
    (f : Module.End k[↥H] (resRep ρ H).asModule) :
    Module.End k[↥H] (resRep ρ H).asModule where
  toFun v := conjSemilinearEnd (H := H) ρ x (f (conjSemilinearEnd (H := H) ρ x⁻¹ v))
  map_add' v w := by simp only [map_add]
  map_smul' r v := by
    change conjSemilinearEnd (H := H) ρ x (f (conjSemilinearEnd (H := H) ρ x⁻¹ (r • v)))
      = r • conjSemilinearEnd (H := H) ρ x (f (conjSemilinearEnd (H := H) ρ x⁻¹ v))
    rw [LinearMap.map_smulₛₗ (conjSemilinearEnd (H := H) ρ x⁻¹), LinearMap.map_smul f,
      LinearMap.map_smulₛₗ (conjSemilinearEnd (H := H) ρ x), conjMonoidAlgRingHom_conj_inv]

@[simp] theorem cliffordConjMap_apply (x : G) (f : Module.End k[↥H] (resRep ρ H).asModule)
    (v : (resRep ρ H).asModule) :
    cliffordConjMap ρ x f v
      = conjSemilinearEnd (H := H) ρ x (f (conjSemilinearEnd (H := H) ρ x⁻¹ v)) :=
  rfl

/-- `ρ x` followed by `ρ x⁻¹` is the identity (the other cancellation). -/
theorem conjSemilinearEnd_inv_conj (x : G) (v : (resRep ρ H).asModule) :
    conjSemilinearEnd (H := H) ρ x⁻¹ (conjSemilinearEnd (H := H) ρ x v) = v := by
  have := conjSemilinearEnd_conj_inv ρ x⁻¹ v
  rwa [inv_inv] at this

theorem cliffordConjMap_one (x : G) :
    cliffordConjMap ρ x (1 : Module.End k[↥H] (resRep ρ H).asModule) = 1 := by
  ext v
  simp only [cliffordConjMap_apply, Module.End.one_apply, conjSemilinearEnd_conj_inv]

theorem cliffordConjMap_mul (x : G) (f g : Module.End k[↥H] (resRep ρ H).asModule) :
    cliffordConjMap ρ x (f * g) = cliffordConjMap ρ x f * cliffordConjMap ρ x g := by
  ext v
  simp only [cliffordConjMap_apply, Module.End.mul_apply, conjSemilinearEnd_inv_conj]

theorem cliffordConjMap_cliffordConjMap_inv (x : G)
    (f : Module.End k[↥H] (resRep ρ H).asModule) :
    cliffordConjMap ρ x (cliffordConjMap ρ x⁻¹ f) = f := by
  ext v
  simp only [cliffordConjMap_apply, conjSemilinearEnd_inv_conj, conjSemilinearEnd_conj_inv]

/-- The induced ring automorphism of `k[H]` fixes the image of `k` (scalars). -/
theorem conjMonoidAlgRingHom_algebraMap (x : G) (c : k) :
    conjMonoidAlgRingHom (k := k) (H := H) x (algebraMap k k[↥H] c) = algebraMap k k[↥H] c := by
  have hc : (algebraMap k k[↥H] c) = MonoidAlgebra.single (1 : ↥H) c := by
    rw [Algebra.algebraMap_eq_smul_one, MonoidAlgebra.one_def, MonoidAlgebra.smul_single,
      smul_eq_mul, mul_one]
  rw [hc, conjMonoidAlgRingHom_single, map_one]

/-- `conjSemilinearEnd ρ x` is `k`-linear (the conjugation twist fixes scalars). -/
theorem conjSemilinearEnd_smul_k (x : G) (c : k) (v : (resRep ρ H).asModule) :
    conjSemilinearEnd (H := H) ρ x (c • v) = c • conjSemilinearEnd (H := H) ρ x v := by
  rw [← algebraMap_smul k[↥H] c v, LinearMap.map_smulₛₗ, conjMonoidAlgRingHom_algebraMap,
    algebraMap_smul]

theorem cliffordConjMap_smul (x : G) (c : k)
    (f : Module.End k[↥H] (resRep ρ H).asModule) :
    cliffordConjMap ρ x (c • f) = c • cliffordConjMap ρ x f := by
  ext v
  simp only [cliffordConjMap_apply, LinearMap.smul_apply, conjSemilinearEnd_smul_k]

/-- **Conjugation by `ρ x`, as a `k`-algebra automorphism of `End_{k[H]} V`.**  The fixed
subalgebra is `End_{k[G]} V` (when `G = ⟨H, x⟩`); over an algebraically closed field with `V`
irreducible this is the scalars, which (via Skolem–Noether) forces multiplicity one. -/
noncomputable def cliffordConj (x : G) :
    Module.End k[↥H] (resRep ρ H).asModule ≃ₐ[k] Module.End k[↥H] (resRep ρ H).asModule where
  toFun := cliffordConjMap ρ x
  invFun := cliffordConjMap ρ x⁻¹
  left_inv f := by
    have := cliffordConjMap_cliffordConjMap_inv ρ x⁻¹ f
    rwa [inv_inv] at this
  right_inv f := cliffordConjMap_cliffordConjMap_inv ρ x f
  map_mul' := cliffordConjMap_mul ρ x
  map_add' f g := by ext v; simp only [cliffordConjMap_apply, LinearMap.add_apply, map_add]
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one, cliffordConjMap_smul, cliffordConjMap_one]

@[simp] theorem cliffordConj_apply (x : G) (f : Module.End k[↥H] (resRep ρ H).asModule) :
    cliffordConj ρ x f = cliffordConjMap ρ x f := rfl

/-- If `f ∈ End_{k[H]} V` is fixed by conjugation by `ρ x`, then `f` commutes (pointwise) with
`conjSemilinearEnd ρ g` for **every** `g`, provided `G = ⟨H, x⟩`.  Proof by induction on the
generation of `G`: on `H` from `k[H]`-linearity of `f`, on `x` from the fixed hypothesis. -/
theorem commute_conjSemilinearEnd_of_cliffordConj_fixed (x : G)
    (hgen : Subgroup.closure ((H : Set G) ∪ {x}) = ⊤)
    {f : Module.End k[↥H] (resRep ρ H).asModule} (hf : cliffordConj ρ x f = f) (g : G) :
    ∀ v, f (conjSemilinearEnd (H := H) ρ g v)
      = conjSemilinearEnd (H := H) ρ g (f v) := by
  have hmem : g ∈ Subgroup.closure ((H : Set G) ∪ {x}) := hgen ▸ Subgroup.mem_top g
  induction hmem using Subgroup.closure_induction with
  | mem s hs =>
      intro v
      rcases hs with hsH | hsx
      · -- `s ∈ H`: `f` is `k[H]`-linear, so commutes with `ρ s`.
        have hsmul : ∀ w : (resRep ρ H).asModule,
            conjSemilinearEnd (H := H) ρ s w
              = MonoidAlgebra.single (⟨s, hsH⟩ : ↥H) (1 : k) • w := fun w => by
          simp only [Representation.single_smul, one_smul, resRep_apply, conjSemilinearEnd_apply]
          rfl
        rw [hsmul v, hsmul (f v)]
        exact map_smul f (MonoidAlgebra.single (⟨s, hsH⟩ : ↥H) (1 : k)) v
      · -- `s = x`: from the fixed hypothesis.
        rw [Set.mem_singleton_iff] at hsx
        rw [hsx]
        have hfp := LinearMap.congr_fun ((cliffordConj_apply ρ x f).symm.trans hf)
          (conjSemilinearEnd (H := H) ρ x v)
        rw [cliffordConjMap_apply, conjSemilinearEnd_inv_conj] at hfp
        exact hfp.symm
  | one => intro v; rw [conjSemilinearEnd_one_apply, conjSemilinearEnd_one_apply]
  | mul a b _ _ ha hb =>
      intro v
      rw [conjSemilinearEnd_mul_apply, ha, hb, ← conjSemilinearEnd_mul_apply]
  | inv a _ ha =>
      intro v
      have key := ha (conjSemilinearEnd (H := H) ρ a⁻¹ v)
      rw [conjSemilinearEnd_conj_inv] at key
      rw [key, conjSemilinearEnd_inv_conj]

/-- **The fixed subalgebra of `cliffordConj ρ x` is the scalars** (when `G = ⟨H, x⟩`, `V`
irreducible, `k` algebraically closed).  A fixed `f` commutes with every `ρ g`, so it has an
eigenvalue `c` whose eigenspace is a nonzero `G`-invariant submodule, hence `⊤` (irreducibility);
thus `f = c • id`.  This is the `hfix` hypothesis of `finrank_eq_one_of_aut_fixedScalar`. -/
theorem cliffordConj_fixed_imp_scalar [ρ.IsIrreducible] [IsAlgClosed k] [Module.Finite k V]
    [Nontrivial V]
    (x : G) (hgen : Subgroup.closure ((H : Set G) ∪ {x}) = ⊤)
    (f : Module.End k[↥H] (resRep ρ H).asModule) (hf : cliffordConj ρ x f = f) :
    ∃ c : k, algebraMap k (Module.End k[↥H] (resRep ρ H).asModule) c = f := by
  have hcomm := commute_conjSemilinearEnd_of_cliffordConj_fixed ρ x hgen hf
  -- `f` as a `k`-linear endomorphism of `V` (`asModule = V`), which has an eigenvalue.
  let fk : Module.End k V := f.restrictScalars k
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue fk
  obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
  have hv0 : v ≠ 0 := (Module.End.hasEigenvector_iff.mp hv).2
  have hfkv : fk v = c • v := hv.apply_eq_smul
  -- `fk` commutes with every `ρ g` (the conjugation-fixed property, via `conjSemilinearEnd = ρ`).
  have hfkcomm : ∀ (g : G) (w : V), fk (ρ g w) = ρ g (fk w) := fun g w => hcomm g w
  refine ⟨c, ?_⟩
  -- `fk - c • 1` commutes with `ρ`, so its kernel is a `G`-invariant submodule of `V`.
  have hfkscalar : fk = c • (1 : Module.End k V) := by
    set g₀ : Module.End k V := fk - c • 1 with hg₀
    have hg₀comm : ∀ (y : G) (w : V), g₀ (ρ y w) = ρ y (g₀ w) := fun y w => by
      simp only [hg₀, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
        hfkcomm y w, map_smul, map_sub]
    let W' : Subrepresentation ρ :=
      { toSubmodule := LinearMap.ker g₀
        apply_mem_toSubmodule := fun y w hw => by
          rw [LinearMap.mem_ker] at hw ⊢; rw [hg₀comm y w, hw, map_zero] }
    rcases IsSimpleOrder.eq_bot_or_eq_top W' with hbot | htop
    · refine absurd ?_ hv0
      have hker : LinearMap.ker g₀ = ⊥ := congrArg Subrepresentation.toSubmodule hbot
      have : v ∈ LinearMap.ker g₀ := by
        rw [LinearMap.mem_ker]
        simp only [hg₀, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, hfkv,
          sub_self]
      rw [hker, Submodule.mem_bot] at this; exact this
    · have hker : LinearMap.ker g₀ = ⊤ := congrArg Subrepresentation.toSubmodule htop
      have : g₀ = 0 := LinearMap.ker_eq_top.mp hker
      rw [hg₀, sub_eq_zero] at this; exact this
  -- therefore `f = c • id`.
  refine LinearMap.ext fun w => ?_
  have hfw : f w = c • w := LinearMap.congr_fun hfkscalar w
  rw [Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply]
  exact hfw.symm

set_option backward.isDefEq.respectTransparency false in
/-- **The restriction is irreducible** (Bender–Glauberman Proposition 2.2(a), the multiplicity-one
finish).  Assume `G = ⟨H, x⟩`, `ρ` is irreducible over an algebraically closed field `k` with `V`
finite-dimensional and nontrivial, `H` is finite with `char k ∤ |H|`, and a nonzero simple
`k[H]`-submodule `W` of the restriction has every `G`-conjugate isomorphic to it (the input from
Gorenstein 5.5.4).  Then the restriction `V_H` is itself simple.

The restriction is `W`-isotypic (`isIsotypicOfType_of_conjugates`), so `V_H ≅ Wⁿ` and
`E := End_{k[H]} V ≅ M_n(k)` (`End_{k[H]} W = k` by Schur).  Conjugation by `ρ x` is an algebra
automorphism `cliffordConj ρ x` of `E` whose fixed subalgebra is the scalars
(`cliffordConj_fixed_imp_scalar`), so Skolem–Noether (`finrank_eq_one_of_aut_fixedScalar`) forces
`finrank k E = 1`, i.e. `n = 1`, i.e. `V_H ≅ W` is simple. -/
theorem restriction_isSimpleModule [ρ.IsIrreducible] [IsAlgClosed k] [Module.Finite k V]
    [Nontrivial V]
    (x : G) (hgen : Subgroup.closure ((H : Set G) ∪ {x}) = ⊤)
    (W : Submodule k[↥H] (resRep ρ H).asModule) (hW : W ≠ ⊥) [IsSimpleModule k[↥H] W]
    (hconj : ∀ g : G, Nonempty (W ≃ₗ[k[↥H]] (W.map (conjSemilinearEnd (H := H) ρ g)))) :
    IsSimpleModule k[↥H] (resRep ρ H).asModule := by
  have hVnt : Nontrivial (resRep ρ H).asModule := ‹Nontrivial V›
  have hVfin : Module.Finite k (resRep ρ H).asModule := inferInstance
  have : IsNoetherian k (resRep ρ H).asModule := inferInstance
  have hHfin : Module.Finite k[↥H] (resRep ρ H).asModule :=
    Module.Finite.of_restrictScalars_finite k k[↥H] (resRep ρ H).asModule
  have hWfin : Module.Finite k ↥W :=
    Module.Finite.of_injective ((W.subtype).restrictScalars k) Subtype.val_injective
  have hss : IsSemisimpleModule k[↥H] (resRep ρ H).asModule :=
    isSemisimpleModule_resRep_of_isIrreducible ρ
  -- The restriction is `W`-isotypic, hence `V_H ≅ Wⁿ`.
  have hiso : IsIsotypicOfType k[↥H] (resRep ρ H).asModule ↥W :=
    isIsotypicOfType_of_conjugates ρ W hW hconj
  obtain ⟨n, ⟨e⟩⟩ := hiso.linearEquiv_fun
  -- Schur: `End_{k[H]} W ≅ k`.
  have hbij : Function.Bijective (algebraMap k (Module.End k[↥H] ↥W)) :=
    algebraMap_end_bijective_of_isSimpleModule
  let schur : k ≃ₐ[k] Module.End k[↥H] ↥W := AlgEquiv.ofBijective (Algebra.ofId k _) hbij
  -- `n ≠ 0`: otherwise `V_H` would be a subsingleton.
  have hn0 : n ≠ 0 := by
    rintro rfl
    have : Subsingleton (resRep ρ H).asModule := e.toEquiv.subsingleton
    exact not_subsingleton _ this
  have hne : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn0⟩⟩
  -- `Ψ : E ≅ M_n(k)`.
  let Ψ : Module.End k[↥H] (resRep ρ H).asModule ≃ₐ[k] Matrix (Fin n) (Fin n) k :=
    (e.conjAlgEquiv k).trans
      ((endVecAlgEquivMatrixEnd ..).trans schur.symm.mapMatrix)
  have : IsSimpleRing (Module.End k[↥H] (resRep ρ H).asModule) :=
    IsSimpleRing.of_ringEquiv Ψ.symm.toRingEquiv inferInstance
  have : FiniteDimensional k (Module.End k[↥H] (resRep ρ H).asModule) :=
    Module.Finite.equiv Ψ.symm.toLinearEquiv
  -- Skolem–Noether: the fixed-scalar automorphism `cliffordConj ρ x` forces `finrank k E = 1`.
  have hrank : Module.finrank k (Module.End k[↥H] (resRep ρ H).asModule) = 1 :=
    finrank_eq_one_of_aut_fixedScalar (cliffordConj ρ x)
      (fun f hf => cliffordConj_fixed_imp_scalar ρ x hgen f hf)
  -- `finrank k (M_n k) = n² = 1`, so `n = 1`.
  have hn1 : n = 1 := by
    have h1 : Module.finrank k (Matrix (Fin n) (Fin n) k) = 1 := by
      rw [← Ψ.toLinearEquiv.finrank_eq]; exact hrank
    rw [Module.finrank_matrix, Fintype.card_fin, Module.finrank_self, mul_one] at h1
    exact Nat.dvd_one.mp ⟨n, h1.symm⟩
  -- `n = 1` gives `V_H ≅ W`, and `W` is simple.
  subst hn1
  have e1 : (resRep ρ H).asModule ≃ₗ[k[↥H]] ↥W :=
    e.trans (LinearEquiv.funUnique (Fin 1) k[↥H] ↥W)
  exact IsSimpleModule.congr e1

set_option backward.isDefEq.respectTransparency false in
/-- **Bender–Glauberman Proposition 2.2(a)**, in the form consumed by the group-level Theorem 2.5
(`finrank_modEq_of_faithful_irreducible`): the restriction representation `Res^G_H ρ` is
irreducible.  This repackages `restriction_isSimpleModule` through
`Representation.irreducible_iff_isSimpleModule_asModule`. -/
theorem restriction_isIrreducible [ρ.IsIrreducible] [IsAlgClosed k] [Module.Finite k V]
    [Nontrivial V]
    (x : G) (hgen : Subgroup.closure ((H : Set G) ∪ {x}) = ⊤)
    (W : Submodule k[↥H] (resRep ρ H).asModule) (hW : W ≠ ⊥) [IsSimpleModule k[↥H] W]
    (hconj : ∀ g : G, Nonempty (W ≃ₗ[k[↥H]] (W.map (conjSemilinearEnd (H := H) ρ g)))) :
    (resRep ρ H).IsIrreducible :=
  (Representation.irreducible_iff_isSimpleModule_asModule (resRep ρ H)).mpr
    (restriction_isSimpleModule ρ x hgen W hW hconj)

end MultOne

end OddOrder.RepresentationTheory


