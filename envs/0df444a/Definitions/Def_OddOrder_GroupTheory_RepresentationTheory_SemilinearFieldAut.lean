-- Prove2me | Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_SemilinearFieldAut
-- name    : OddOrder_GroupTheory_RepresentationTheory_SemilinearFieldAut
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T04:44:49.212213+00:00
-- url     : https://prove2.me/theorems/90268d23-2e9f-4bc6-87da-dfae65a2a8bb
-- title:
--   Semilinear extension: additive automorphisms multiplicative on a generating scalar set
-- statement:
--   An abstract layer for Peterfalvi (9.7.b): an additive automorphism that is multiplicative on a generating set of scalars extends to a ring automorphism of the field, packaged at the group level.
--
--   Main declarations: `ringEquivOfAddEquivOfMulScalars` (The semilinear-extension ring automorphism); `ringAutHomOfAddAutHom` (Group-level packaging); `ringAutMulEquivAlgAut` (A ring automorphism of a field fixes the prime subfield); `coeFnLinear` (Coercion of `𝔽_p`-linear endomaps to bare functions, as an `F`-linear map (`F` acts on the…).
--
--   The bundle also proves 14 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/RepresentationTheory/SemilinearFieldAut.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/RepresentationTheory/SemilinearFieldAut.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Algebra_QuadraticMapCoordinates
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Ring.Aut
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Ring.AddAut
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Perfect
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.CharP.Algebra

namespace OddOrder.RepresentationTheory

variable {F : Type*} [Ring F]

/-- **Multiplicativity from a generating scalar set**: an additive automorphism `α` that is
multiplicative against every element of `S` (`α (t·s) = α t · α s`) is multiplicative against
every element of the additive closure of `S`; if `S` generates `F` additively, against
everything.  For fixed `t`, the set `{t' | α (t·t') = α t · α t'}` is an additive subgroup
(distributivity + additivity of `α`) containing `S`. -/
theorem addEquiv_mul_of_mul_scalars {K : Type*} [Ring K]
    (α : F ≃+ K) {S : Set F}
    (hgen : AddSubgroup.closure S = ⊤)
    (hmul : ∀ s ∈ S, ∀ t : F, α (t * s) = α t * α s) (t t' : F) :
    α (t * t') = α t * α t' := by
  have hmem : t' ∈ AddSubgroup.closure S := hgen ▸ AddSubgroup.mem_top t'
  induction hmem using AddSubgroup.closure_induction with
  | mem s hs => exact hmul s hs t
  | zero => simp
  | add x y _ _ hpx hpy => rw [mul_add, map_add, hpx, hpy, map_add, mul_add]
  | neg x _ hpx => rw [mul_neg, map_neg, hpx, map_neg, mul_neg]

/-- **The semilinear-extension ring automorphism** (Peterfalvi (9.7.b), abstract form): an
additive automorphism multiplicative against an additively-generating scalar set is a ring
automorphism.  (`map_one` needs no hypothesis: a multiplicative-and-additive equiv of a ring
preserves `1` automatically.) -/
def ringEquivOfAddEquivOfMulScalars {K : Type*} [Ring K]
    (α : F ≃+ K) {S : Set F}
    (hgen : AddSubgroup.closure S = ⊤)
    (hmul : ∀ s ∈ S, ∀ t : F, α (t * s) = α t * α s) : F ≃+* K :=
  { α with
    map_mul' := addEquiv_mul_of_mul_scalars α hgen hmul }

@[simp] theorem ringEquivOfAddEquivOfMulScalars_apply
    {K : Type*} [Ring K] (α : F ≃+ K) {S : Set F}
    (hgen : AddSubgroup.closure S = ⊤)
    (hmul : ∀ s ∈ S, ∀ t : F, α (t * s) = α t * α s) (x : F) :
    ringEquivOfAddEquivOfMulScalars α hgen hmul x = α x := rfl

/-- **Group-level packaging** (the `η : W₁ →* Aut F` of Peterfalvi (9.7.b)): a homomorphism into
the additive automorphisms whose every value is multiplicative against a common
additively-generating scalar set upgrades to a homomorphism into the **ring** automorphisms,
with the same underlying functions.

`AddAut F` is an *additive* group in mathlib, so the source is its multiplicative incarnation
`Multiplicative (AddAut F)` (the same idiom as `AddAut.toZModLinearEquiv` in
`OddOrder/GroupTheory/PRank.lean` and `AddAut.mulLeft` in `OddOrder/BG/AppC_NormSet.lean`).
Both group laws are function composition, so the two `rfl`s below are the real content. -/
def ringAutHomOfAddAutHom {W : Type*} [Group W] (η : W →* Multiplicative (AddAut F))
    {S : Set F} (hgen : AddSubgroup.closure S = ⊤)
    (hmul : ∀ w : W, ∀ s ∈ S, ∀ t : F, Multiplicative.toAdd (η w) (t * s)
      = Multiplicative.toAdd (η w) t * Multiplicative.toAdd (η w) s) :
    W →* RingAut F where
  toFun w := ringEquivOfAddEquivOfMulScalars (Multiplicative.toAdd (η w)) hgen (hmul w)
  map_one' := by
    refine RingEquiv.ext fun x => ?_
    rw [ringEquivOfAddEquivOfMulScalars_apply, map_one η]
    rfl
  map_mul' w w' := by
    refine RingEquiv.ext fun x => ?_
    rw [ringEquivOfAddEquivOfMulScalars_apply, map_mul η]
    rfl

@[simp] theorem ringAutHomOfAddAutHom_apply {W : Type*} [Group W]
    (η : W →* Multiplicative (AddAut F))
    {S : Set F} (hgen : AddSubgroup.closure S = ⊤)
    (hmul : ∀ w : W, ∀ s ∈ S, ∀ t : F, Multiplicative.toAdd (η w) (t * s)
      = Multiplicative.toAdd (η w) t * Multiplicative.toAdd (η w) s) (w : W) (x : F) :
    ringAutHomOfAddAutHom η hgen hmul w x = Multiplicative.toAdd (η w) x := rfl

section FiniteFieldAut

variable (F : Type*) [Field F] (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) F]

/-- **A ring automorphism of a field fixes the prime subfield**, so `RingAut F` *is* the
`𝔽_p`-algebra automorphism group — the Galois group of `F/𝔽_p` — with the same underlying
functions.  (Every element of `ZMod p` is an integer cast, and ring homs preserve integer casts;
both group laws are composition, so all four structure fields are `rfl`.)

This is the shared form of the bridge (issue 9164): the former inline copies in
`Suzuki/SemilinearModel.lean` (`ringAut_isCyclic_of_finite`) and
`Higman/.../TypeAConclusion.lean` are rerouted here. -/
def ringAutMulEquivAlgAut : RingAut F ≃* (F ≃ₐ[ZMod p] F) where
  toFun f := AlgEquiv.ofRingEquiv (f := f) fun x => by
    obtain ⟨n, rfl⟩ := ZMod.intCast_surjective x
    simp
  invFun g := g.toRingEquiv
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

@[simp] theorem ringAutMulEquivAlgAut_apply (f : RingAut F) (x : F) :
    ringAutMulEquivAlgAut F p f x = f x := rfl

/-- Coercion of `𝔽_p`-linear endomaps to bare functions, as an `F`-linear map
(`F` acts on the codomain). -/
private def coeFnLinear : (F →ₗ[ZMod p] F) →ₗ[F] (F → F) where
  toFun g := ⇑g
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- **Dedekind independence for field automorphisms**: the automorphisms of
`F`, viewed as `𝔽_p`-linear endomaps, are `F`-linearly independent. -/
theorem linearIndependent_algAut_toLinearMap [Finite F] :
    LinearIndependent F
      (fun σ : F ≃ₐ[ZMod p] F => (σ.toLinearMap : F →ₗ[ZMod p] F)) := by
  have h0 : LinearIndependent F (fun f : F →* F => (f : F → F)) :=
    linearIndependent_monoidHom F F
  have hinj : Function.Injective (fun σ : F ≃ₐ[ZMod p] F => (σ : F →* F)) := by
    intro σ τ h
    ext x
    exact DFunLike.congr_fun h x
  have hcomp := h0.comp _ hinj
  exact hcomp.of_comp (coeFnLinear F p)

/-- `dim_F Hom_{𝔽_p}(F, F) = [F : 𝔽_p]`: evaluation on an `𝔽_p`-basis is an
`F`-linear equivalence with `F^[F : 𝔽_p]`. -/
theorem finrank_linearMap_self_eq_finrank [Finite F] :
    Module.finrank F (F →ₗ[ZMod p] F) = Module.finrank (ZMod p) F := by
  classical
  let : Fintype F := Fintype.ofFinite F
  let b := Module.finBasis (ZMod p) F
  rw [← (b.constr F : _ ≃ₗ[F] (F →ₗ[ZMod p] F)).finrank_eq]
  simp

/-- **Peterfalvi Appendix III, Lemma 2(a)** (p. 140, characteristic-free form):
the `𝔽_p`-linear mappings `F → F` of a finite field form an `F`-vector space
with basis the automorphisms of `F`. -/
noncomputable def algAutLinearBasis [Finite F] :
    Module.Basis (F ≃ₐ[ZMod p] F) F (F →ₗ[ZMod p] F) :=
  letI : Fintype (F ≃ₐ[ZMod p] F) := Fintype.ofFinite _
  basisOfLinearIndependentOfCardEqFinrank
    (linearIndependent_algAut_toLinearMap F p)
    (by
      rw [finrank_linearMap_self_eq_finrank F p, ← Nat.card_eq_fintype_card]
      exact IsGalois.card_aut_eq_finrank (ZMod p) F)

@[simp] theorem algAutLinearBasis_apply [Finite F] (σ : F ≃ₐ[ZMod p] F) :
    algAutLinearBasis F p σ = σ.toLinearMap := by
  simp [algAutLinearBasis]

/-- The bilinear map `(x, y) ↦ σ(x)·τ(y)` attached to a pair of field
automorphisms. -/
noncomputable def algAutMulBilin (σ τ : F ≃ₐ[ZMod p] F) :
    F →ₗ[ZMod p] F →ₗ[ZMod p] F :=
  (LinearMap.mul (ZMod p) F).compl₁₂ σ.toLinearMap τ.toLinearMap

@[simp] theorem algAutMulBilin_apply (σ τ : F ≃ₐ[ZMod p] F) (x y : F) :
    algAutMulBilin F p σ τ x y = σ x * τ y :=
  rfl

/-- Coercion of `𝔽_p`-bilinear maps to bare two-variable functions, as an
`F`-linear map. -/
private def coeFnBilin :
    (F →ₗ[ZMod p] F →ₗ[ZMod p] F) →ₗ[F] (F × F → F) where
  toFun g := fun xy => g xy.1 xy.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The pair `(σ, τ)` as a monoid character of the product monoid `F × F`
(the map `(x, y) ↦ σ(x)·τ(y)`). -/
private def algAutPairChar (σ τ : F ≃ₐ[ZMod p] F) : (F × F) →* F :=
  ((σ : F →* F).comp (MonoidHom.fst F F)) *
    ((τ : F →* F).comp (MonoidHom.snd F F))

/-- `dim_F` of the space of `𝔽_p`-bilinear maps `F × F → F` is `n²`. -/
theorem finrank_bilinMap_self_eq [Finite F] :
    Module.finrank F (F →ₗ[ZMod p] F →ₗ[ZMod p] F) =
      Module.finrank (ZMod p) F * Module.finrank (ZMod p) F := by
  classical
  let : Fintype F := Fintype.ofFinite F
  let b := Module.finBasis (ZMod p) F
  have he := LinearEquiv.finrank_eq
    (b.constr (M' := F →ₗ[ZMod p] F) F)
  rw [← he, Module.finrank_pi_fintype F]
  simp [finrank_linearMap_self_eq_finrank F p, Finset.sum_const]

/-- The index count matches the dimension: `|Aut F|² = n²` (top-level lemma so
the heavy nested-instance context of the basis construction can cite it
opaquely — inline `by`-proofs there send `whnf` into instance unfolding). -/
theorem card_autProd_eq_finrank_bilinMap [Finite F]
    [Fintype (F ≃ₐ[ZMod p] F)] :
    Fintype.card ((F ≃ₐ[ZMod p] F) × (F ≃ₐ[ZMod p] F)) =
      Module.finrank F (F →ₗ[ZMod p] F →ₗ[ZMod p] F) := by
  rw [← Nat.card_eq_fintype_card, Nat.card_prod,
    IsGalois.card_aut_eq_finrank (ZMod p) F,
    finrank_bilinMap_self_eq F p]

/-- Evaluating the Lemma 2(b) family on an `𝔽_p`-basis of `F`: the
`Basis.constr` equivalence carries the `Pi`-space family
`i ↦ σ(bᵢ) • τ` to the bilinear map `(x, y) ↦ σ(x)·τ(y)`. -/
private theorem constr_smul_toLinearMap [Finite F] {ι : Type*}
    (b : Module.Basis ι (ZMod p) F) (σ τ : F ≃ₐ[ZMod p] F) :
    (b.constr (M' := F →ₗ[ZMod p] F) F)
        (fun i => σ (b i) • τ.toLinearMap) =
      algAutMulBilin F p σ τ := by
  refine b.ext fun i => ?_
  rw [Module.Basis.constr_basis]
  refine LinearMap.ext fun y => ?_
  simp [smul_eq_mul]

/-- Independence of the `Pi`-space avatar `i ↦ σ(bᵢ) • τ` of the
Lemma 2(b) family — proved from Dedekind independence of the pair
characters entirely on the function-space side (`of_comp`), never
touching the doubly-nested hom space. -/
private theorem linearIndependent_bilinPi [Finite F] {ι : Type*}
    (b : Module.Basis ι (ZMod p) F) :
    LinearIndependent F
      (fun στ : (F ≃ₐ[ZMod p] F) × (F ≃ₐ[ZMod p] F) =>
        fun i => στ.1 (b i) • στ.2.toLinearMap) := by
  classical
  have h0 : LinearIndependent F (fun f : (F × F) →* F => (f : F × F → F)) :=
    linearIndependent_monoidHom (F × F) F
  have hinj : Function.Injective
      (fun στ : (F ≃ₐ[ZMod p] F) × (F ≃ₐ[ZMod p] F) =>
        algAutPairChar F p στ.1 στ.2) := by
    intro στ στ' h
    have happ : ∀ x y : F, στ.1 x * στ.2 y = στ'.1 x * στ'.2 y := fun x y =>
      DFunLike.congr_fun h (x, y)
    have h1 : ∀ x : F, στ.1 x = στ'.1 x := fun x => by
      have := happ x 1
      simpa using this
    have h2 : ∀ y : F, στ.2 y = στ'.2 y := fun y => by
      have := happ 1 y
      simpa using this
    exact Prod.ext (AlgEquiv.ext h1) (AlgEquiv.ext h2)
  have hchar := h0.comp _ hinj
  have hGP : (⇑((coeFnBilin F p).comp
        (b.constr (M' := F →ₗ[ZMod p] F) F).toLinearMap)) ∘
      (fun στ : (F ≃ₐ[ZMod p] F) × (F ≃ₐ[ZMod p] F) =>
        fun i => στ.1 (b i) • στ.2.toLinearMap) =
      (fun f : (F × F) →* F => (f : F × F → F)) ∘
        (fun στ : (F ≃ₐ[ZMod p] F) × (F ≃ₐ[ZMod p] F) =>
          algAutPairChar F p στ.1 στ.2) := by
    funext στ
    change (coeFnBilin F p) ((b.constr (M' := F →ₗ[ZMod p] F) F)
      (fun i => στ.1 (b i) • στ.2.toLinearMap)) = _
    rw [constr_smul_toLinearMap]
    rfl
  rw [← hGP] at hchar
  exact hchar.of_comp _

/-- **Peterfalvi Appendix III, Lemma 2(b), bundled form** (p. 140): the
maps `(x, y) ↦ σ(x)·τ(y)` are an `F`-basis of the `𝔽_p`-bilinear maps
`F × F → F`.  The term is constructed in the plain `Pi` function space
`Fin n → (F →ₗ[𝔽_p] F)` (whose instances are pointwise) and transported
along the `Basis.constr` equivalence; constructing it directly in the
doubly-nested hom space diverges in `whnf`/`isDefEq` (see the packaging
note below and issue 0148). -/
noncomputable def algAutMulBilinBasis [Finite F] :
    Module.Basis ((F ≃ₐ[ZMod p] F) × (F ≃ₐ[ZMod p] F)) F
      (F →ₗ[ZMod p] F →ₗ[ZMod p] F) :=
  letI : Fintype F := Fintype.ofFinite F
  letI : Fintype (F ≃ₐ[ZMod p] F) := Fintype.ofFinite _
  (basisOfLinearIndependentOfCardEqFinrank
    (linearIndependent_bilinPi F p (Module.finBasis (ZMod p) F))
    ((card_autProd_eq_finrank_bilinMap F p).trans
      (LinearEquiv.finrank_eq
        ((Module.finBasis (ZMod p) F).constr
          (M' := F →ₗ[ZMod p] F) F)).symm)).map
    ((Module.finBasis (ZMod p) F).constr (M' := F →ₗ[ZMod p] F) F)

@[simp] theorem algAutMulBilinBasis_apply [Finite F]
    (σ τ : F ≃ₐ[ZMod p] F) :
    algAutMulBilinBasis F p (σ, τ) = algAutMulBilin F p σ τ := by
  simp only [algAutMulBilinBasis, Module.Basis.map_apply,
    coe_basisOfLinearIndependentOfCardEqFinrank]
  exact constr_smul_toLinearMap F p _ σ τ

section QuadraticChar2

variable (F : Type*) [Field F] [Algebra (ZMod 2) F]

/-- The quadratic map `x ↦ σ(x)·τ(x)` attached to a pair of field
automorphisms (characteristic `2`). -/
noncomputable def autMulQuadraticMap (σ τ : F ≃ₐ[ZMod 2] F) :
    QuadraticMap (ZMod 2) F F where
  toFun x := σ x * τ x
  toFun_smul a x := by
    rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) a with h | h <;> subst h
    · simp
    · simp
  exists_companion' :=
    ⟨algAutMulBilin F 2 σ τ + algAutMulBilin F 2 τ σ, by
      intro x y
      simp only [map_add, LinearMap.add_apply, algAutMulBilin_apply]
      ring⟩

@[simp] theorem autMulQuadraticMap_apply (σ τ : F ≃ₐ[ZMod 2] F) (x : F) :
    autMulQuadraticMap F σ τ x = σ x * τ x :=
  rfl

end QuadraticChar2

end FiniteFieldAut

end OddOrder.RepresentationTheory


