-- Prove2me | Definitions.Def_AlgebraicCurve_SymmetricPower
-- name    : AlgebraicCurve_SymmetricPower
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/976a9b1e-6741-5e3c-bfaf-605f2c811606
-- title:
--   Fibre powers of a k-scheme and symmetric-power packages
-- statement:
--   Fix a field $k$, a scheme $C$ with a morphism $c : C \to \operatorname{Spec} k$, and $r \in \mathbb{N}$. The abbreviation `finFibrePow c r` is the $r$-fold fibre power $C \times_k \cdots \times_k C$, realised as the wide pullback of the family of $r$ copies of $c$ indexed by `Fin r`; `finFibrePow.proj c r l` is the $l$-th projection to $C$, `finFibrePow.toBase c r` the morphism to $\operatorname{Spec} k$, and `proj_comp` records that the $l$-th projection followed by $c$ is the structure morphism. For a permutation $\sigma$ of `Fin r`, `permHom c r σ` is the endomorphism of the fibre power determined by the requirement that its $j$-th coordinate be the $\sigma^{-1}(j)$-th projection (so the $i$-th coordinate of $\sigma$ applied to a point is its $\sigma^{-1}(i)$-th coordinate), and it commutes with the morphism to the base. These endomorphisms satisfy $\mathrm{permHom}(1) = \mathrm{id}$ and $\mathrm{permHom}(\sigma\tau) = \mathrm{permHom}(\tau)$ followed by $\mathrm{permHom}(\sigma)$; they are assembled into automorphisms `permAut` and into a monoid homomorphism `permAct c r` from the symmetric group on `Fin r` to the automorphism group of the fibre power, with the normalisations $(\mathrm{permAct}\,\sigma)^{-1} = \mathrm{permAct}(\sigma^{-1})$ and $\mathrm{permAct}(\sigma)$ followed by the $\sigma(i)$-th projection equal to the $i$-th projection. The auxiliary `le_preimage_of_comp_eq` states that if $g$ followed by $q$ equals $q$ then $q^{-1}V \le g^{-1}(q^{-1}V)$ for every open $V$ of the target, which is what allows an invariant endomorphism to act on sections over $q^{-1}V$.
--
--   The structure `SymmetricPowerPackage c r` packages a model of the symmetric power together with all the properties required of it, each as a field: a scheme $C^{(r)}$ with a morphism $c_{\mathrm{sym}}$ to $\operatorname{Spec} k$; a morphism $\pi$ from the fibre power to $C^{(r)}$ over $k$; invariance of $\pi$ under $\mathrm{permAct}(\sigma)$ for every $\sigma$; finiteness and surjectivity of $\pi$; the statement that two points have the same image under $\pi$ exactly when they lie in one orbit of the permutation action; injectivity of $\pi$ on sections over every open $V$, with image precisely the sections over $\pi^{-1}V$ fixed by all the maps induced by $\mathrm{permAct}(\sigma)$; for every affine open $U \subseteq C$ the existence of an affine open $V \subseteq C^{(r)}$ with $\pi^{-1}V = \bigcap_{l} \mathrm{proj}_l^{-1}U$; and finally that $C^{(r)}$ is integral and that $c_{\mathrm{sym}}$ is proper and smooth of relative dimension $r$. Thus the structure is a predicate-laden presentation: inhabiting it for given $c$ and $r$ amounts to exhibiting a quotient with these properties, and the geometric properties of the quotient are carried as hypotheses-as-fields rather than derived.
--
--   **Relation to Mathlib.** The fibre power is Mathlib's `widePullback` of a finite family, and the conditions on the morphisms use Mathlib's `IsFinite`, `Surjective`, `IsProper` and `SmoothOfRelativeDimension`; Mathlib has no notion of symmetric power of a scheme or of a quotient by a finite group action, so `SymmetricPowerPackage` is the project's own bundled formulation.
--
--   **Where it is used.** Symmetric powers of a smooth proper curve are the classical route to its divisor classes and its Jacobian, the existence of a package for all $r$ being the input needed for that construction. This module only sets up the fibre power with its symmetric-group action and the list of properties demanded of a quotient; it asserts no existence statement.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicCurve_SymmetricPower.lean

import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k)) (r : ℕ)

noncomputable abbrev finFibrePow : Scheme.{u} :=
  widePullback (Spec (CommRingCat.of k)) (fun _ : Fin r => C) (fun _ => c)

namespace finFibrePow

noncomputable abbrev proj (l : Fin r) : finFibrePow c r ⟶ C :=
  WidePullback.π (fun _ : Fin r => c) l

noncomputable abbrev toBase : finFibrePow c r ⟶ Spec (CommRingCat.of k) :=
  WidePullback.base (fun _ : Fin r => c)

@[reassoc]
theorem proj_comp (l : Fin r) : proj c r l ≫ c = toBase c r :=
  WidePullback.π_arrow _ _

noncomputable def permHom (σ : Equiv.Perm (Fin r)) : finFibrePow c r ⟶ finFibrePow c r :=
  WidePullback.lift (toBase c r) (fun j => proj c r (σ⁻¹ j)) (fun _ => WidePullback.π_arrow _ _)

@[reassoc]
theorem permHom_proj (σ : Equiv.Perm (Fin r)) (j : Fin r) :
    permHom c r σ ≫ proj c r j = proj c r (σ⁻¹ j) :=
  WidePullback.lift_π _ _ _ _ _

@[reassoc]
theorem permHom_toBase (σ : Equiv.Perm (Fin r)) : permHom c r σ ≫ toBase c r = toBase c r :=
  WidePullback.lift_base _ _ _ _

theorem permHom_one : permHom c r 1 = 𝟙 _ := by
  apply WidePullback.hom_ext
  · intro j
    rw [permHom_proj, Category.id_comp, inv_one, Equiv.Perm.one_apply]
  · rw [permHom_toBase, Category.id_comp]

theorem permHom_mul (σ τ : Equiv.Perm (Fin r)) :
    permHom c r (σ * τ) = permHom c r τ ≫ permHom c r σ := by
  apply WidePullback.hom_ext
  · intro j
    rw [permHom_proj, Category.assoc, permHom_proj, permHom_proj, mul_inv_rev,
      Equiv.Perm.mul_apply]
  · rw [permHom_toBase, Category.assoc, permHom_toBase, permHom_toBase]

noncomputable def permAut (σ : Equiv.Perm (Fin r)) : Aut (finFibrePow c r) where
  hom := permHom c r σ
  inv := permHom c r σ⁻¹
  hom_inv_id := by rw [← permHom_mul, inv_mul_cancel, permHom_one]
  inv_hom_id := by rw [← permHom_mul, mul_inv_cancel, permHom_one]

noncomputable def permAct : Equiv.Perm (Fin r) →* Aut (finFibrePow c r) :=
  MonoidHom.mk' (permAut c r) (fun σ τ => by
    ext : 1
    change permHom c r (σ * τ) = (permAut c r τ).hom ≫ (permAut c r σ).hom
    exact permHom_mul c r σ τ)

theorem permAct_hom (σ : Equiv.Perm (Fin r)) : (permAct c r σ).hom = permHom c r σ := rfl

theorem permAct_inv (σ : Equiv.Perm (Fin r)) : (permAct c r σ).inv = permHom c r σ⁻¹ := rfl

@[reassoc]
theorem permAct_hom_proj (σ : Equiv.Perm (Fin r)) (i : Fin r) :
    (permAct c r σ).hom ≫ proj c r (σ i) = proj c r i := by
  rw [permAct_hom, permHom_proj, Equiv.Perm.inv_def, Equiv.symm_apply_apply]

@[reassoc]
theorem permAct_hom_toBase (σ : Equiv.Perm (Fin r)) :
    (permAct c r σ).hom ≫ toBase c r = toBase c r := by
  rw [permAct_hom, permHom_toBase]

end finFibrePow

theorem le_preimage_of_comp_eq {X Y : Scheme.{u}} (g : X ⟶ X) (q : X ⟶ Y) (h : g ≫ q = q)
    (V : Y.Opens) : q ⁻¹ᵁ V ≤ g ⁻¹ᵁ (q ⁻¹ᵁ V) := by
  rw [← Scheme.Hom.comp_preimage, h]

end AlgebraicGeometry

namespace AlgebraicCurve

open AlgebraicGeometry

structure SymmetricPowerPackage {k : Type u} [Field k] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of k)) (r : ℕ) where

  Csym : Scheme.{u}

  csym : Csym ⟶ Spec (CommRingCat.of k)

  π : finFibrePow c r ⟶ Csym

  π_comp_csym : π ≫ csym = finFibrePow.toBase c r

  permAct_comp_π : ∀ σ : Equiv.Perm (Fin r), (finFibrePow.permAct c r σ).hom ≫ π = π

  isFinite_π : IsFinite π

  surjective_π : Surjective π

  π_apply_eq_iff : ∀ x x' : ↥(finFibrePow c r),
    π.base x = π.base x' ↔ ∃ σ : Equiv.Perm (Fin r), (finFibrePow.permAct c r σ).hom.base x = x'

  app_injective : ∀ V : Csym.Opens, Function.Injective (π.app V)

  range_app : ∀ V : Csym.Opens, Set.range (π.app V) =
    {s | ∀ σ : Equiv.Perm (Fin r), (finFibrePow.permAct c r σ).hom.appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V)
      (le_preimage_of_comp_eq _ _ (permAct_comp_π σ) V) s = s}

  exists_affine_chart : ∀ U : C.Opens, IsAffineOpen U →
    ∃ V : Csym.Opens, IsAffineOpen V ∧ π ⁻¹ᵁ V = ⨅ l : Fin r, (finFibrePow.proj c r l) ⁻¹ᵁ U

  integral : IsIntegral Csym

  proper : IsProper csym

  smooth : SmoothOfRelativeDimension r csym

end AlgebraicCurve


