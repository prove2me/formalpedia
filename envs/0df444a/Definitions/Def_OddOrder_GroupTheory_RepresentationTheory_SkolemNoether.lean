-- Prove2me | Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_SkolemNoether
-- name    : OddOrder_GroupTheory_RepresentationTheory_SkolemNoether
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T04:40:34.640789+00:00
-- url     : https://prove2.me/theorems/93047ca5-f166-4bda-8131-7384bac98920
-- title:
--   Skolem–Noether for the endomorphism algebra of a finite-dimensional vector space
-- statement:
--   A $k$-algebra automorphism of $\mathrm{End}_k W_0$, with $W_0$ a finite-dimensional vector space over a field $k$, is inner: it is conjugation by a $k$-linear automorphism of $W_0$. This is the matrix Skolem–Noether theorem, specialised to the case needed here (Mathlib lacks a general Skolem–Noether).
--
--   Main definitions: `EndTwist` ($W_0$ with the $\mathrm{End}_k W_0$-module structure twisted by an algebra automorphism), its module instance `instModuleEnd`, and the scalar-fixed form `finrank_le_one_of_aut_fixedScalar`.
--
--   The bundle also proves 5 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/RepresentationTheory/SkolemNoether.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/RepresentationTheory/SkolemNoether.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Mathlib.RingTheory.SimpleModule.WedderburnArtin
import Mathlib.RingTheory.SimpleModule.IsAlgClosed
import Mathlib.RingTheory.SimpleRing.Matrix
import Mathlib.RingTheory.SimpleRing.Congr
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

namespace OddOrder.RepresentationTheory

open Module

section SimpleArtinian

/-- **All simple modules over a simple Artinian ring are isomorphic.**  Each simple module is
isomorphic to a minimal left ideal (`exists_linearEquiv_ideal_of_isSimpleModule`), and the simple
left ideals are mutually isomorphic because the ring, as a module over itself, is isotypic
(`IsSimpleRing.isIsotypic`). -/
theorem nonempty_linearEquiv_of_isSimpleModule
    {E : Type*} [Ring E] [IsSimpleRing E] [IsArtinianRing E]
    {A B : Type*} [AddCommGroup A] [Module E A] [IsSimpleModule E A]
    [AddCommGroup B] [Module E B] [IsSimpleModule E B] :
    Nonempty (A ≃ₗ[E] B) := by
  obtain ⟨I, ⟨eA⟩⟩ := IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule E A
  obtain ⟨J, ⟨eB⟩⟩ := IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule E B
  have : IsSimpleModule E I := IsSimpleModule.congr eA.symm
  have : IsSimpleModule E J := IsSimpleModule.congr eB.symm
  obtain ⟨eIJ⟩ := IsSimpleRing.isIsotypic E E I J
  exact ⟨eA.trans (eIJ.symm.trans eB.symm)⟩

end SimpleArtinian

section Schur

/-- **Schur's Lemma over an algebraically closed field (module form).**  Every `R`-linear
endomorphism of a finite-dimensional simple `R`-module `M` (over a `k`-algebra `R`, `k`
algebraically closed) is a scalar: `algebraMap k (End R M)` is bijective.

Surjectivity is the eigenvalue argument: `f` (as a `k`-linear map on the finite-dimensional `M`)
has an eigenvalue `c ∈ k`; then `ker (f - c • id)` is a nonzero `R`-submodule of the simple `M`,
hence all of `M`, so `f = c • id`.  This sidesteps the endomorphism-division-ring instance and its
semiring diamond. -/
theorem algebraMap_end_bijective_of_isSimpleModule
    {k : Type*} [Field k] [IsAlgClosed k] {R : Type*} [Ring R] [Algebra k R]
    {M : Type*} [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]
    [IsSimpleModule R M] [Module.Finite k M] :
    Function.Bijective (algebraMap k (Module.End R M)) := by
  have : Nontrivial M := IsSimpleModule.nontrivial R M
  refine ⟨(algebraMap k (Module.End R M)).injective, fun f => ?_⟩
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (f.restrictScalars k)
  obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
  have hv_ne : v ≠ 0 := (Module.End.hasEigenvector_iff.mp hv).2
  refine ⟨c, ?_⟩
  have hfv : f v = c • v := hv.apply_eq_smul
  have hmem : v ∈ LinearMap.ker (f - algebraMap k (Module.End R M) c) := by
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, Module.algebraMap_end_apply, hfv, sub_self]
  rcases eq_bot_or_eq_top (LinearMap.ker (f - algebraMap k (Module.End R M) c)) with hbot | htop
  · rw [hbot, Submodule.mem_bot] at hmem; exact absurd hmem hv_ne
  · exact (sub_eq_zero.mp (LinearMap.ker_eq_top.mp htop)).symm

end Schur

section Twist

variable {k W₀ : Type*} [Field k] [AddCommGroup W₀] [Module k W₀]

/-- `W₀` carrying the `End k W₀`-module structure twisted by an algebra automorphism `θ`:
`f • w = θ f w`.  A type synonym so this twisted action does not clash with the standard one. -/
def EndTwist (_θ : End k W₀ ≃ₐ[k] End k W₀) : Type _ := W₀

namespace EndTwist

instance (θ : End k W₀ ≃ₐ[k] End k W₀) : AddCommGroup (EndTwist θ) :=
  inferInstanceAs (AddCommGroup W₀)

instance (θ : End k W₀ ≃ₐ[k] End k W₀) : Module k (EndTwist θ) :=
  inferInstanceAs (Module k W₀)

/-- The twisted `End k W₀`-action: `f` acts as `θ f`. -/
noncomputable instance instModuleEnd (θ : End k W₀ ≃ₐ[k] End k W₀) :
    Module (End k W₀) (EndTwist θ) :=
  Module.compHom (M := W₀) θ.toRingEquiv.toRingHom

theorem smul_def (θ : End k W₀ ≃ₐ[k] End k W₀) (f : End k W₀) (x : EndTwist θ) :
    f • x = (θ f) (show W₀ from x) := rfl

/-- Twisting by an automorphism preserves simplicity: the identity `EndTwist θ → W₀` is a
`θ`-semilinear bijection, so it transports the submodule lattice (and hence `IsSimpleOrder`). -/
theorem isSimpleModule (θ : End k W₀ ≃ₐ[k] End k W₀) [IsSimpleModule (End k W₀) W₀] :
    IsSimpleModule (End k W₀) (EndTwist θ) := by
  have : RingHomSurjective (θ.toRingEquiv.toRingHom) := ⟨θ.surjective⟩
  -- the identity, as a `θ`-semilinear bijection `EndTwist θ → W₀`
  let g : EndTwist θ →ₛₗ[θ.toRingEquiv.toRingHom] W₀ :=
    { toFun := fun x => (show W₀ from x)
      map_add' := fun _ _ => rfl
      map_smul' := fun f x => by
        change (show W₀ from f • x) = (θ f) • (show W₀ from x)
        rw [EndTwist.smul_def]; rfl }
  exact (g.isSimpleModule_iff_of_bijective Function.bijective_id).mpr inferInstance

end EndTwist

end Twist

section SkolemNoether

variable {k W₀ : Type*} [Field k] [AddCommGroup W₀] [Module k W₀] [FiniteDimensional k W₀]

set_option backward.isDefEq.respectTransparency false in
/-- **Matrix Skolem–Noether, scalar-fixed form.**  If a `k`-algebra automorphism `θ` of `End k W₀`
(with `W₀` finite-dimensional over the field `k`) fixes *only* the scalar endomorphisms, then
`finrank k W₀ ≤ 1`.

This is the multiplicity-one engine of **Bender–Glauberman Proposition 2.2(a)**.  Skolem–Noether
(`End k W₀` is a simple Artinian ring, so its standard module `W₀` is the unique simple module up to
isomorphism — `nonempty_linearEquiv_of_isSimpleModule`) makes `θ` inner: the isomorphism `W₀ ≃ₗ`
(twist of `W₀` by `θ`) is conjugation by some `u ∈ GL(W₀)` with `θ = u.conjAlgEquiv k`.  Then `θ`
fixes `u` itself, so `u` is a scalar, so `θ = id`, so *every* endomorphism is fixed hence scalar;
`finrank k (End k W₀) = (finrank k W₀)² ≤ 1`. -/
theorem finrank_le_one_of_aut_fixedScalar
    (θ : End k W₀ ≃ₐ[k] End k W₀)
    (hfix : ∀ f : End k W₀, θ f = f → ∃ c : k, algebraMap k (End k W₀) c = f) :
    Module.finrank k W₀ ≤ 1 := by
  rcases subsingleton_or_nontrivial W₀ with _ | hnt
  · exact Module.finrank_zero_of_subsingleton.trans_le (Nat.zero_le 1)
  · -- `End k W₀` is simple Artinian (transport to a matrix ring over the field `k`).
    have : NeZero (Module.finrank k W₀) := ⟨Module.finrank_pos.ne'⟩
    have : Nonempty (Fin (Module.finrank k W₀)) := ⟨⟨0, Module.finrank_pos⟩⟩
    have : IsSimpleRing (End k W₀) :=
      IsSimpleRing.of_ringEquiv (algEquivMatrix (Module.finBasis k W₀)).symm.toRingEquiv
        inferInstance
    have : IsArtinianRing (End k W₀) := IsArtinianRing.of_finite k (End k W₀)
    have : IsSimpleModule (End k W₀) W₀ := inferInstance
    have : IsSimpleModule (End k W₀) (EndTwist θ) := EndTwist.isSimpleModule θ
    -- Skolem–Noether: `W₀ ≅ EndTwist θ` as `End k W₀`-modules.
    obtain ⟨e⟩ := nonempty_linearEquiv_of_isSimpleModule
      (E := End k W₀) (A := W₀) (B := EndTwist θ)
    -- `e` intertwines the standard and twisted actions: `e (f w) = θ f (e w)`.
    -- (`@Eq W₀` is explicit: a mere ascription would leave the `Eq` at `EndTwist θ`,
    -- which downstream `simpa` calls no longer unfold.)
    have key : ∀ (f : End k W₀) (w : W₀), @Eq W₀ (e (f • w)) ((θ f) (e w : W₀)) := by
      intro f w
      have h := e.map_smul f w
      rw [EndTwist.smul_def] at h
      exact h
    -- package `e` as a `k`-linear automorphism `u` of `W₀`.
    set uMap : W₀ →ₗ[k] W₀ :=
      { toFun := fun w => (e w : W₀)
        map_add' := fun a b => map_add e a b
        map_smul' := fun c w => by
          have h := key (algebraMap k (End k W₀) c) w
          rw [θ.commutes] at h
          simpa [Module.algebraMap_end_apply] using h } with huMap
    have hubij : Function.Bijective uMap := e.bijective
    set u : W₀ ≃ₗ[k] W₀ := LinearEquiv.ofBijective uMap hubij with hu
    -- intertwining relation in terms of `u` (definitionally `e`).
    have keyU : ∀ (f : End k W₀) (w : W₀), u (f w) = (θ f) (u w) := fun f w => key f w
    -- `θ = u.conjAlgEquiv k`.
    have hθ : θ = u.conjAlgEquiv k := by
      refine AlgEquiv.ext fun f => LinearMap.ext fun w => ?_
      rw [LinearEquiv.conjAlgEquiv_apply, LinearMap.comp_apply, LinearMap.comp_apply]
      change (θ f) w = u (f (u.symm w))
      rw [keyU f (u.symm w), u.apply_symm_apply]
    -- `θ` fixes `u` (conjugation by `u` fixes `u`), so `u` is a scalar `c • id`.
    have hu_fix : θ (u : W₀ →ₗ[k] W₀) = (u : W₀ →ₗ[k] W₀) := by
      rw [hθ, LinearEquiv.conjAlgEquiv_apply]
      refine LinearMap.ext fun w => ?_
      simp
    obtain ⟨c, hc⟩ := hfix (u : W₀ →ₗ[k] W₀) hu_fix
    have hcu : (u : W₀ →ₗ[k] W₀) = algebraMap k (End k W₀) c := hc.symm
    have h2 : ∀ v, u v = c • v := fun v => by
      have := congrArg (fun g : End k W₀ => g v) hcu
      simpa [Module.algebraMap_end_apply] using this
    have hc0 : c ≠ 0 := by
      rintro rfl
      obtain ⟨w, hw⟩ := exists_ne (0 : W₀)
      exact hw (u.injective (by rw [map_zero, h2 w, zero_smul]))
    -- hence `θ = id`: conjugation by the scalar `c • id` is trivial.
    have hθid : ∀ f : End k W₀, θ f = f := by
      intro f
      rw [hθ, LinearEquiv.conjAlgEquiv_apply]
      refine LinearMap.ext fun w => ?_
      rw [LinearMap.comp_apply, LinearMap.comp_apply]
      change u (f (u.symm w)) = f w
      have h3 : u.symm w = c⁻¹ • w := by
        apply u.injective
        rw [u.apply_symm_apply, h2, smul_smul, mul_inv_cancel₀ hc0, one_smul]
      rw [h3, map_smul, h2, smul_smul, mul_inv_cancel₀ hc0, one_smul]
    -- every endomorphism is scalar, so `finrank (End k W₀) ≤ 1`, so `(finrank W₀)² ≤ 1`.
    have hsurj : Function.Surjective (Algebra.linearMap k (End k W₀)) := fun f =>
      hfix f (hθid f)
    have hle : Module.finrank k (End k W₀) ≤ 1 := by
      have := LinearMap.finrank_le_finrank_of_surjective hsurj
      simpa using this
    rw [Module.finrank_linearMap] at hle
    nlinarith [Module.finrank_pos (R := k) (M := W₀), hle]

/-- **Skolem–Noether, scalar-fixed form, for an abstract simple algebra.**  If `E` is a
finite-dimensional simple algebra over an algebraically closed field `k` and a `k`-algebra
automorphism `θ` of `E` fixes only the scalars, then `E` *is* the scalars (`finrank k E = 1`).

Wedderburn–Artin (`exists_algEquiv_matrix_of_isAlgClosed`) identifies `E` with a matrix algebra
`Matrix (Fin n) (Fin n) k ≃ₐ End k (Fin n → k)`; transporting `θ` and applying
`finrank_le_one_of_aut_fixedScalar` gives `n ≤ 1`, and `NeZero n` gives `n = 1`. -/
theorem finrank_eq_one_of_aut_fixedScalar
    {k E : Type*} [Field k] [IsAlgClosed k] [Ring E] [Algebra k E]
    [IsSimpleRing E] [FiniteDimensional k E]
    (θ : E ≃ₐ[k] E)
    (hfix : ∀ f : E, θ f = f → ∃ c : k, algebraMap k E c = f) :
    Module.finrank k E = 1 := by
  obtain ⟨n, hn, ⟨Φ⟩⟩ := IsSimpleRing.exists_algEquiv_matrix_of_isAlgClosed k E
  -- `Ψ : E ≃ₐ[k] End k (Fin n → k)`, via the matrix algebra.
  let Ψ : E ≃ₐ[k] Module.End k (Fin n → k) := Φ.trans algEquivMatrix'.symm
  let θ' : Module.End k (Fin n → k) ≃ₐ[k] Module.End k (Fin n → k) := Ψ.symm.trans (θ.trans Ψ)
  -- `θ'` also fixes only the scalars (transport along `Ψ`).
  have hfix' : ∀ g : Module.End k (Fin n → k), θ' g = g →
      ∃ c : k, algebraMap k (Module.End k (Fin n → k)) c = g := by
    intro g hg
    have hg' : Ψ (θ (Ψ.symm g)) = g := hg
    have h1 : θ (Ψ.symm g) = Ψ.symm g := Ψ.injective (by rw [hg', Ψ.apply_symm_apply])
    obtain ⟨c, hc⟩ := hfix (Ψ.symm g) h1
    exact ⟨c, by rw [← Ψ.commutes c, hc, Ψ.apply_symm_apply]⟩
  have hle := finrank_le_one_of_aut_fixedScalar θ' hfix'
  have hW₀ : Module.finrank k (Fin n → k) = n := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  have hn1 : n = 1 := le_antisymm (hW₀ ▸ hle) (Nat.one_le_iff_ne_zero.mpr hn.out)
  rw [Ψ.toLinearEquiv.finrank_eq, Module.finrank_linearMap, hW₀, hn1, mul_one]

end SkolemNoether

end OddOrder.RepresentationTheory


