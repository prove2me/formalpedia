-- Prove2me | Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CliffordAlgClosed
-- name    : OddOrder_GroupTheory_RepresentationTheory_CliffordAlgClosed
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T04:40:34.985277+00:00
-- url     : https://prove2.me/theorems/8b3ea665-38dd-4651-8c70-83447539d314
-- title:
--   Clifford's theorem: conjugation permutes the simple constituents of a restriction
-- statement:
--   The field-agnostic, module-theoretic core of Clifford's theorem, the first ingredient of Bender–Glauberman Proposition 2.2(a). For a representation of $G$ over an arbitrary field and a normal subgroup $H$, conjugation by $g$ permutes the simple constituents of the restriction to $H$.
--
--   Main definitions: `conjNormalMulAut` (conjugation automorphism of a normal subgroup), `resRep` (the restriction $\mathrm{Res}^G_H\rho$ as a representation of $H$), `conjMonoidAlgRingHom` (the induced ring automorphism of $k[H]$) and `conjSemilinearEnd` (the map $\rho(g)$ as a semilinear endomorphism).
--
--   The bundle also proves 9 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/RepresentationTheory/CliffordAlgClosed.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/RepresentationTheory/CliffordAlgClosed.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.SimpleModule.Isotypic
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Algebra.Module.Submodule.RestrictScalars

namespace OddOrder.RepresentationTheory

open Representation

open scoped MonoidAlgebra

variable {G : Type*} [Group G]

/-- The automorphism `h ↦ g h g⁻¹` of a normal subgroup `H` induced by conjugation by `g ∈ G`. -/
noncomputable def conjNormalMulAut (H : Subgroup G) [H.Normal] (g : G) : H ≃* H :=
  (MulEquiv.subgroupMap (MulAut.conj g) H).trans
    (MulEquiv.subgroupCongr (Subgroup.Normal.conj_smul_eq_self g H))

@[simp]
theorem conjNormalMulAut_apply_coe (H : Subgroup G) [H.Normal] (g : G) (h : H) :
    (conjNormalMulAut H g h : G) = g * (h : G) * g⁻¹ := rfl

variable {k : Type*} [Field k]

variable {V : Type*} [AddCommGroup V] [Module k V]

section ConjBySimple

variable (ρ : Representation k G V) (H : Subgroup G) [hH : H.Normal]

/-- The restriction `Res^G_H ρ`, packaged as a `Representation k ↥H V` (rather than the bare
`MonoidHom` `ρ.comp H.subtype`) so that its `k[H]`-module `asModule` is available.  A reducible
abbreviation, so the `k[H]`-module instance is found by unfolding to `(ρ.comp H.subtype).asModule`.

(Distinct name from `Representation.restrictRep` in the `ℂ`-pinned `Clifford.lean`.) -/
abbrev resRep : Representation k ↥H V := ρ.comp H.subtype

omit hH in
@[simp] theorem resRep_apply (h : ↥H) : resRep ρ H h = ρ (h : G) := rfl

variable {H}

/-- The ring automorphism of `k[H]` induced by conjugation `h ↦ g h g⁻¹` on the normal subgroup
`H`.  On generators it sends `single h c` to `single (g h g⁻¹) c`. -/
noncomputable def conjMonoidAlgRingHom (g : G) : k[↥H] →+* k[↥H] :=
  MonoidAlgebra.mapDomainRingHom k (conjNormalMulAut H g).toMonoidHom

theorem conjMonoidAlgRingHom_single (g : G) (h : ↥H) (c : k) :
    conjMonoidAlgRingHom (k := k) (H := H) g (MonoidAlgebra.single h c) =
      MonoidAlgebra.single (conjNormalMulAut H g h) c := by
  simp [conjMonoidAlgRingHom]

theorem conjMonoidAlgRingHom_surjective (g : G) :
    Function.Surjective (conjMonoidAlgRingHom (k := k) (H := H) g) :=
  (MonoidAlgebra.mapDomainRingEquiv k (conjNormalMulAut H g)).surjective

instance conjMonoidAlgRingHom_isSurjective (g : G) :
    RingHomSurjective (conjMonoidAlgRingHom (k := k) (H := H) g) :=
  ⟨conjMonoidAlgRingHom_surjective (k := k) (H := H) g⟩

set_option backward.isDefEq.respectTransparency false in
/-- The `k`-linear bijection `ρ g`, packaged as a `conjMonoidAlgRingHom g`-semilinear endomorphism
of the restricted module `(resRep ρ H).asModule`.

This is the module-theoretic incarnation of normality: for `h ∈ H`, the standard `k[H]`-action on
the image satisfies `h • (ρ g v) = ρ g (ρ (g⁻¹ h g) v)`, i.e. `ρ g` intertwines the `H`-action up
to the conjugation twist `conjMonoidAlgRingHom g`. -/
noncomputable def conjSemilinearEnd (g : G) :
    (resRep ρ H).asModule →ₛₗ[conjMonoidAlgRingHom (k := k) (H := H) g]
      (resRep ρ H).asModule where
  toFun v := (show (resRep ρ H).asModule from ρ g v)
  map_add' v w := by simp
  map_smul' s v := by
    induction s using MonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy =>
        change ρ g ((x + y) • v) = _
        rw [add_smul, map_add, map_add, add_smul]
        exact congrArg₂ (· + ·) hx hy
    | single h c =>
        have hHh : (conjNormalMulAut H g h : G) = g * (h : G) * g⁻¹ := rfl
        rw [conjMonoidAlgRingHom_single]
        change ρ g (MonoidAlgebra.single h c • v) =
          MonoidAlgebra.single (conjNormalMulAut H g h) c •
            (show (resRep ρ H).asModule from ρ g v)
        rw [Representation.single_smul, Representation.single_smul, resRep_apply,
          resRep_apply, map_smul]
        congr 1
        change ρ g (ρ (h : G) v) = ρ ((conjNormalMulAut H g h : G)) (ρ g v)
        rw [hHh, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
        congr 2
        group

@[simp] theorem conjSemilinearEnd_apply (g : G) (v : (resRep ρ H).asModule) :
    conjSemilinearEnd (H := H) ρ g v = (show (resRep ρ H).asModule from ρ g v) :=
  rfl

theorem conjSemilinearEnd_bijective (g : G) :
    Function.Bijective (conjSemilinearEnd (H := H) ρ g) :=
  ρ.apply_bijective g

set_option backward.isDefEq.respectTransparency false in
/-- Membership in the image submodule `N.map (conjSemilinearEnd ρ g)` is exactly being of the form
`ρ g v` for `v ∈ N`: the image is, as a set, the `ρ g`-translate of `N`, carrying the standard
`k[H]`-action `h • w = ρ (h : G) w`. -/
theorem mem_map_conjSemilinearEnd (g : G)
    (N : Submodule k[↥H] (resRep ρ H).asModule) (w : (resRep ρ H).asModule) :
    w ∈ N.map (conjSemilinearEnd (H := H) ρ g) ↔
      ∃ v ∈ N, (show (resRep ρ H).asModule from ρ g v) = w := by
  simp only [Submodule.mem_map, conjSemilinearEnd_apply]

set_option backward.isDefEq.respectTransparency false in
/-- **Conjugation permutes simple constituents** (module core of Clifford's theorem; the first
ingredient of BG Prop 2.2(a)).  For `ρ : Representation k G V` over any field `k`, `H ⊴ G`, a simple
`k[H]`-submodule `N` of the restriction `(resRep ρ H).asModule`, and any `g : G`, the image of
`N` under `ρ g` is again a simple `k[H]`-submodule.

The image is `N.map (conjSemilinearEnd ρ g)`, with `h • (ρ g v) = ρ g (ρ (g⁻¹ h g) v)` (normality of
`H`).  Simplicity is transported across the semilinear bijection `ρ g` via the order isomorphism of
submodule lattices it induces (`Submodule.orderIsoMapComapOfBijective`), as `IsSimpleModule` is
equivalent to the submodule being an atom (`isSimpleModule_iff_isAtom`).

No irreducibility of `ρ` and no algebraic closedness is needed: `ρ g` is always a bijection. -/
theorem isSimpleModule_map_conjSemilinearEnd
    (g : G) (N : Submodule k[↥H] (resRep ρ H).asModule)
    [IsSimpleModule k[↥H] N] :
    IsSimpleModule k[↥H]
      (N.map (conjSemilinearEnd (H := H) ρ g) :
        Submodule k[↥H] (resRep ρ H).asModule) := by
  have hatomN : IsAtom N := IsSimpleModule.isAtom
  have hmap : (Submodule.orderIsoMapComapOfBijective
      (conjSemilinearEnd (H := H) ρ g)
      (conjSemilinearEnd_bijective (H := H) ρ g)) N =
      N.map (conjSemilinearEnd (H := H) ρ g) := rfl
  rw [isSimpleModule_iff_isAtom, ← hmap]
  exact (OrderIso.isAtom_iff _ N).mpr hatomN

/-- **The final step of BG Prop 2.2(a).** If `ρ` is irreducible and `W` is a nonzero
`k[H]`-submodule of the restriction `(resRep ρ H).asModule` that is `G`-invariant (stable under
every `ρ g`, expressed via `conjSemilinearEnd`), then `W = ⊤`.  A `G`-invariant `k[H]`-submodule is
the carrier of a
`Subrepresentation ρ`, so irreducibility (`IsSimpleOrder (Subrepresentation ρ)`) forces it to be `⊥`
or `⊤`; nonzero rules out `⊥`. -/
theorem eq_top_of_forall_map_conjSemilinearEnd_le
    [ρ.IsIrreducible] (W : Submodule k[↥H] (resRep ρ H).asModule) (hW : W ≠ ⊥)
    (hinv : ∀ g : G, W.map (conjSemilinearEnd (H := H) ρ g) ≤ W) :
    W = ⊤ := by
  -- `W`, being `G`-invariant, is the carrier of a `Subrepresentation ρ`
  let Wρ : Subrepresentation ρ :=
    { toSubmodule := W.restrictScalars k
      apply_mem_toSubmodule := fun g v hv => by
        have hv' : v ∈ W := hv
        have : (show (resRep ρ H).asModule from ρ g v) ∈ W :=
          hinv g (Submodule.mem_map_of_mem hv')
        exact this }
  rcases IsSimpleOrder.eq_bot_or_eq_top Wρ with hbot | htop
  · -- `Wρ = ⊥` forces `W = ⊥`, contradicting `hW`
    have h0 : W.restrictScalars k = ⊥ := congrArg Subrepresentation.toSubmodule hbot
    refine absurd (eq_bot_iff.mpr fun v hv => ?_) hW
    have hv' : v ∈ W.restrictScalars k := hv
    rw [h0] at hv'
    simpa using hv'
  · -- `Wρ = ⊤` gives `W = ⊤`
    have h1 : W.restrictScalars k = ⊤ := congrArg Subrepresentation.toSubmodule htop
    refine eq_top_iff.mpr fun v _ => ?_
    have hv' : v ∈ W.restrictScalars k := h1 ▸ Submodule.mem_top
    exact hv'

/-- `ρ 1 = id` translates the `g = 1` conjugate to `W` itself. -/
theorem map_conjSemilinearEnd_one (W : Submodule k[↥H] (resRep ρ H).asModule) :
    W.map (conjSemilinearEnd (H := H) ρ 1) = W := by
  ext v
  rw [mem_map_conjSemilinearEnd]
  refine ⟨?_, fun hv => ⟨v, hv, ?_⟩⟩
  · rintro ⟨w, hw, rfl⟩
    have : (show (resRep ρ H).asModule from ρ (1 : G) w) = w := by rw [map_one]; rfl
    rwa [this]
  · show (show (resRep ρ H).asModule from ρ (1 : G) v) = v
    rw [map_one]; rfl

/-- Conjugating by `g₂` then `g₁` is conjugating by `g₁ * g₂` (carrier-level, from
`ρ (g₁ g₂) = ρ g₁ ∘ ρ g₂`).  This avoids the heterogeneous semilinear composition law. -/
theorem map_map_conjSemilinearEnd (W : Submodule k[↥H] (resRep ρ H).asModule) (g₁ g₂ : G) :
    (W.map (conjSemilinearEnd (H := H) ρ g₂)).map (conjSemilinearEnd (H := H) ρ g₁)
      = W.map (conjSemilinearEnd (H := H) ρ (g₁ * g₂)) := by
  ext v
  simp only [mem_map_conjSemilinearEnd]
  constructor
  · rintro ⟨u, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨w, hw, by rw [map_mul]; rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨(show (resRep ρ H).asModule from ρ g₂ w), ⟨w, hw, rfl⟩, by rw [map_mul]; rfl⟩

/-- **Clifford: the restriction is spanned by the `G`-conjugates of any nonzero `k[H]`-submodule.**
For `ρ` irreducible, the supremum of the conjugates `(ρ g)(W)` over all `g ∈ G` is `⊤`. -/
theorem iSup_map_conjSemilinearEnd_eq_top [ρ.IsIrreducible]
    (W : Submodule k[↥H] (resRep ρ H).asModule) (hW : W ≠ ⊥) :
    ⨆ g : G, W.map (conjSemilinearEnd (H := H) ρ g) = ⊤ := by
  refine eq_top_of_forall_map_conjSemilinearEnd_le ρ _ ?_ ?_
  · -- the supremum contains `W` (the `g = 1` term), hence is nonzero
    intro h
    refine hW (le_bot_iff.mp ?_)
    calc W = W.map (conjSemilinearEnd (H := H) ρ 1) := (map_conjSemilinearEnd_one ρ W).symm
      _ ≤ ⨆ g : G, W.map (conjSemilinearEnd (H := H) ρ g) :=
          le_iSup (fun g : G => W.map (conjSemilinearEnd (H := H) ρ g)) 1
      _ = ⊥ := h
  · -- the supremum is `G`-invariant: `(ρ g')` maps `(ρ g)(W)` to `(ρ (g' g))(W)`
    intro g'
    rw [Submodule.map_iSup]
    refine iSup_le fun g => ?_
    rw [map_map_conjSemilinearEnd]
    exact le_iSup (fun g => W.map (conjSemilinearEnd (H := H) ρ g)) (g' * g)

set_option backward.isDefEq.respectTransparency false in
/-- **The restriction is `W`-isotypic** (the Clifford structure of BG Prop 2.2(a)).  If `ρ` is
irreducible, `W` is a nonzero simple `k[H]`-submodule of the restriction, and every `G`-conjugate
of `W` is isomorphic to `W` (the hypothesis `M ≅ M^g`), then *every* simple `k[H]`-submodule of the
restriction is isomorphic to `W`.  Proof: a simple submodule is isomorphic to one of the conjugates
(which span `⊤`, `iSup_map_conjSemilinearEnd_eq_top`), and each conjugate is `≅ W`. -/
theorem isIsotypicOfType_of_conjugates [ρ.IsIrreducible]
    (W : Submodule k[↥H] (resRep ρ H).asModule) (hW : W ≠ ⊥) [IsSimpleModule k[↥H] W]
    (hconj : ∀ g : G, Nonempty (W ≃ₗ[k[↥H]] (W.map (conjSemilinearEnd (H := H) ρ g)))) :
    IsIsotypicOfType k[↥H] (resRep ρ H).asModule W := by
  intro m _
  have : ∀ S : (Set.range fun g : G => W.map (conjSemilinearEnd (H := H) ρ g)),
      IsSimpleModule k[↥H] (S : Submodule k[↥H] (resRep ρ H).asModule) := by
    rintro ⟨_, g, rfl⟩
    exact isSimpleModule_map_conjSemilinearEnd ρ g W
  obtain ⟨S, hS, ⟨e⟩⟩ := Submodule.linearEquiv_of_sSup_eq_top m
    (Set.range fun g : G => W.map (conjSemilinearEnd (H := H) ρ g))
    (by rw [sSup_range]; exact iSup_map_conjSemilinearEnd_eq_top ρ W hW)
  obtain ⟨g, rfl⟩ := hS
  exact ⟨e.trans (hconj g).some.symm⟩

set_option backward.isDefEq.respectTransparency false in
/-- **Clifford semisimplicity** (characteristic-free): the restriction of a nontrivial
finite-dimensional irreducible representation to a normal subgroup is a *semisimple*
`k[H]`-module — with **no** condition relating `char k` and `|H|` (in contrast to Maschke's
theorem).  This is the classical Clifford argument: a simple `k[H]`-submodule exists
(finite-dimensionality), its `G`-conjugates are again simple and span everything
(irreducibility of `ρ`), and a module generated by simples is semisimple. -/
theorem isSemisimpleModule_resRep_of_isIrreducible [ρ.IsIrreducible] [Module.Finite k V]
    [Nontrivial V] :
    IsSemisimpleModule k[↥H] (resRep ρ H).asModule := by
  have : Nontrivial (resRep ρ H).asModule := ‹Nontrivial V›
  -- the submodule lattice is atomic (finite dimension over `k` bounds `k[H]`-chains)
  have : IsArtinian k (resRep ρ H).asModule := inferInstance
  have : IsArtinian k[↥H] (resRep ρ H).asModule := isArtinian_of_tower k inferInstance
  -- a simple (= atomic) `k[H]`-submodule `W₀` exists
  obtain ⟨W₀, hW₀atom, -⟩ :=
    (IsAtomic.eq_bot_or_exists_atom_le (⊤ : Submodule k[↥H] (resRep ρ H).asModule)).resolve_left
      (by simp)
  have : IsSimpleModule k[↥H] W₀ := isSimpleModule_iff_isAtom.mpr hW₀atom
  -- its conjugates are simple and span `⊤`
  refine IsSemisimpleModule.of_sSup_simples_eq_top ?_
  rw [eq_top_iff, ← iSup_map_conjSemilinearEnd_eq_top ρ W₀ hW₀atom.1]
  exact iSup_le fun g => le_sSup (isSimpleModule_map_conjSemilinearEnd ρ g W₀)

end ConjBySimple

end OddOrder.RepresentationTheory


