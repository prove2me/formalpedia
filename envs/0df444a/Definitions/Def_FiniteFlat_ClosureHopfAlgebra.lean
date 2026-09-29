-- Prove2me | Definitions.Def_FiniteFlat_ClosureHopfAlgebra
-- name    : FiniteFlat_ClosureHopfAlgebra
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/8f2f8d79-b533-5d05-88a7-fc91b9bc0742
-- title:
--   Hopf algebra structure on the schematic closure
-- statement:
--   Throughout, $R$ is a commutative ring, $F$ a field that is an $R$-algebra, $G$ a commutative ring, and $B$ a subalgebra of $F \otimes_R G$; for all the substantive statements $R$ is in addition a Noetherian principal ideal domain with $F$ its fraction field, and $G$ is finite and torsion-free as an $R$-module. Recall that [`flatClosure B`](../def/FiniteFlat_SchematicClosure.html#L19) is the $R$-subalgebra $\{g \in G : 1 \otimes g \in B\}$ of $G$ and that [`tensorInclusion B`](../def/FiniteFlat_ClosureHopf.html#L22) is the map $\mathrm{flatClosure}\,B \otimes_R \mathrm{flatClosure}\,B \to G \otimes_R G$ induced by the inclusion. Two triple analogues are defined: [`tensorInclusion3 B`](../def/FiniteFlat_ClosureHopfAlgebra.html#L25) sends $x \otimes w \mapsto x \otimes \mathrm{tensorInclusion}\,B\,w$ into $G \otimes_R (G \otimes_R G)$, and [`tensorInclusion3' B`](../def/FiniteFlat_ClosureHopfAlgebra.html#L36) sends $w \otimes z \mapsto \mathrm{tensorInclusion}\,B\,w \otimes z$ into $(G \otimes_R G) \otimes_R G$. Since $G$ and the closure are free over the principal ideal domain $R$, [`tensorInclusion3 B`](../def/FiniteFlat_ClosureHopfAlgebra.html#L25) is injective; further lemmas record that these maps commute with the associators, that [`tensorInclusion B`](../def/FiniteFlat_ClosureHopf.html#L22) is multiplicative and unital, and that it intertwines the multiplication maps, the counit, the comultiplication [`closureComul`](../def/FiniteFlat_ClosureHopf.html#L249) and the antipode [`closureAntipode`](../def/FiniteFlat_ClosureHopf.html#L287).
--
--   From these compatibilities the coalgebra axioms for $\mathrm{flatClosure}\,B$ are verified: coassociativity of [`closureComul`](../def/FiniteFlat_ClosureHopf.html#L249), the two counit laws, multiplicativity and unitality of [`closureCounit`](../def/FiniteFlat_ClosureHopf.html#L269) and of [`closureComul`](../def/FiniteFlat_ClosureHopf.html#L249), and the two antipode identities. They are assembled into [`closureCoalgebra R F hB`](../def/FiniteFlat_ClosureHopfAlgebra.html#L220), [`closureBialgebra R F hB`](../def/FiniteFlat_ClosureHopfAlgebra.html#L233) (given a comultiplication-stability hypothesis `hB : IsComulStable R F B`, i.e. $\Delta$ carries the closure into the $F$-span of $B \otimes_F B$ inside the generic fibre) and [`closureHopfAlgebra R F hB hB'`](../def/FiniteFlat_ClosureHopfAlgebra.html#L299) (adding antipode stability, i.e. the antipode of $G$ maps the closure into itself); these are definitions, not registered global instances. Finally, [`closureIsCocomm`](../def/FiniteFlat_ClosureHopfAlgebra.html#L323) states that the closure is cocommutative when $G$ is, [`closureValBialgHom`](../def/FiniteFlat_ClosureHopfAlgebra.html#L343) exhibits the inclusion $\mathrm{flatClosure}\,B \to G$ as a morphism of $R$-bialgebras whose underlying algebra map is the coercion, and [`convMul_comp_closureVal`](../def/FiniteFlat_ClosureHopfAlgebra.html#L375) states that restricting $L$-valued points along that inclusion, for a commutative $R$-algebra $L$, is multiplicative for the convolution product on algebra homomorphisms.
--
--   **Relation to Mathlib.** The `Coalgebra`, `Bialgebra` and `HopfAlgebra` classes, the bialgebra-homomorphism notation `→ₐc[R]`, and the convolution monoid `WithConv` on algebra homomorphisms out of a bialgebra are Mathlib's; what is constructed here are such structures on the schematic closure [`flatClosure B`](../def/FiniteFlat_SchematicClosure.html#L19), supplied as definitions rather than as instances.
--
--   **Where it is used.** These structures make the schematic closure of a comultiplication-stable subalgebra of the generic fibre into a finite flat commutative Hopf algebra over the base, so that later modules may speak of the group law, powers and identity on its points. This is the algebraic form of the statement that the schematic closure of a subgroup of the generic fibre of a finite flat commutative group scheme over a principal base is again finite flat, used in the analysis of the finite flat group schemes attached to the $p$-torsion of the relevant elliptic curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_FiniteFlat_ClosureHopfAlgebra.lean

import Mathlib
import Definitions.Def_FiniteFlat_ClosureHopf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

section FlatClosureInstances

universe u v w

variable {R : Type u} [CommRing R]
variable {F : Type v} [Field F] [Algebra R F]
variable {G : Type w} [CommRing G]

attribute [local instance 1000000] SemilinearEquivClass.instSemilinearMapClass

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

section TripleInclusion

variable [Algebra R G]

noncomputable def tensorInclusion3 (B : Subalgebra F (F ⊗[R] G)) :
    (flatClosure B) ⊗[R] ((flatClosure B) ⊗[R] (flatClosure B)) →ₗ[R] G ⊗[R] (G ⊗[R] G) :=
  ((flatClosure B).val.toLinearMap.rTensor (G ⊗[R] G)).comp
    ((tensorInclusion B).lTensor (flatClosure B))

@[simp]
lemma tensorInclusion3_tmul {B : Subalgebra F (F ⊗[R] G)} (x : flatClosure B)
    (w : (flatClosure B) ⊗[R] (flatClosure B)) :
    tensorInclusion3 B (x ⊗ₜ[R] w) = (x : G) ⊗ₜ[R] (tensorInclusion B w) := by
  simp [tensorInclusion3]

noncomputable def tensorInclusion3' (B : Subalgebra F (F ⊗[R] G)) :
    ((flatClosure B) ⊗[R] (flatClosure B)) ⊗[R] (flatClosure B) →ₗ[R] (G ⊗[R] G) ⊗[R] G :=
  ((tensorInclusion B).rTensor G).comp
    ((flatClosure B).val.toLinearMap.lTensor ((flatClosure B) ⊗[R] (flatClosure B)))

@[simp]
lemma tensorInclusion3'_tmul {B : Subalgebra F (F ⊗[R] G)}
    (w : (flatClosure B) ⊗[R] (flatClosure B)) (z : flatClosure B) :
    tensorInclusion3' B (w ⊗ₜ[R] z) = (tensorInclusion B w) ⊗ₜ[R] (z : G) := by
  simp [tensorInclusion3']

theorem tensorInclusion3_injective [IsDomain R] [IsPrincipalIdealRing R] [IsNoetherianRing R]
    [IsFractionRing R F] [Module.Finite R G] [Module.IsTorsionFree R G]
    (B : Subalgebra F (F ⊗[R] G)) : Function.Injective (tensorInclusion3 B) := by
  haveI : Module.Free R G := Module.free_of_finite_type_torsion_free'
  haveI : Module.Free R (flatClosure B) := flatClosure_free B
  unfold tensorInclusion3
  rw [LinearMap.coe_comp]
  exact (Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective).comp
    (Module.Flat.lTensor_preserves_injective_linearMap _ (tensorInclusion_injective B))

theorem tensorInclusion3_assoc_apply {B : Subalgebra F (F ⊗[R] G)}
    (w : ((flatClosure B) ⊗[R] (flatClosure B)) ⊗[R] (flatClosure B)) :
    tensorInclusion3 B
        (TensorProduct.assoc R (flatClosure B) (flatClosure B) (flatClosure B) w)
      = TensorProduct.assoc R G G G (tensorInclusion3' B w) := by
  induction w with
  | zero => simp
  | tmul a z =>
      induction a with
      | zero => simp
      | tmul x y => simp
      | add a₁ a₂ h₁ h₂ =>
          simp only [TensorProduct.add_tmul, map_add, h₁, h₂]
  | add w₁ w₂ h₁ h₂ => simp [map_add, h₁, h₂]

theorem tensorInclusion_mul {B : Subalgebra F (F ⊗[R] G)}
    (z w : (flatClosure B) ⊗[R] (flatClosure B)) :
    tensorInclusion B (z * w) = tensorInclusion B z * tensorInclusion B w := by
  induction z with
  | zero => simp
  | tmul x y =>
      induction w with
      | zero => simp
      | tmul x' y' =>
          simp [Algebra.TensorProduct.tmul_mul_tmul]
      | add b₁ b₂ h₁ h₂ => simp [mul_add, h₁, h₂]
  | add a₁ a₂ h₁ h₂ => simp [add_mul, h₁, h₂]

theorem tensorInclusion_one {B : Subalgebra F (F ⊗[R] G)} :
    tensorInclusion B (1 : (flatClosure B) ⊗[R] (flatClosure B)) = 1 := by
  rw [Algebra.TensorProduct.one_def, Algebra.TensorProduct.one_def, tensorInclusion_tmul]
  simp

theorem val_mul'_tensorInclusion {B : Subalgebra F (F ⊗[R] G)}
    (z : (flatClosure B) ⊗[R] (flatClosure B)) :
    ((LinearMap.mul' R (flatClosure B) z : flatClosure B) : G)
      = LinearMap.mul' R G (tensorInclusion B z) := by
  induction z with
  | zero => simp
  | tmul x y => simp [LinearMap.mul'_apply]
  | add a₁ a₂ h₁ h₂ => simp [map_add, h₁, h₂]

end TripleInclusion

section CoalgebraBialgebra

variable [Bialgebra R G]

theorem tensorInclusion3'_rTensor_closureComul [IsDomain R] [IsPrincipalIdealRing R]
    [IsNoetherianRing R] [IsFractionRing R F] [Module.Finite R G] [Module.IsTorsionFree R G]
    {B : Subalgebra F (F ⊗[R] G)} (hB : IsComulStable R F B)
    (z : (flatClosure B) ⊗[R] (flatClosure B)) :
    tensorInclusion3' B ((closureComul hB).rTensor (flatClosure B) z)
      = (Coalgebra.comul (R := R) (A := G)).rTensor G (tensorInclusion B z) := by
  induction z with
  | zero => simp
  | tmul x y => simp [LinearMap.rTensor_tmul]
  | add a₁ a₂ h₁ h₂ => simp [map_add, h₁, h₂]

theorem tensorInclusion3_lTensor_closureComul [IsDomain R] [IsPrincipalIdealRing R]
    [IsNoetherianRing R] [IsFractionRing R F] [Module.Finite R G] [Module.IsTorsionFree R G]
    {B : Subalgebra F (F ⊗[R] G)} (hB : IsComulStable R F B)
    (z : (flatClosure B) ⊗[R] (flatClosure B)) :
    tensorInclusion3 B ((closureComul hB).lTensor (flatClosure B) z)
      = (Coalgebra.comul (R := R) (A := G)).lTensor G (tensorInclusion B z) := by
  induction z with
  | zero => simp
  | tmul x y => simp [LinearMap.lTensor_tmul]
  | add a₁ a₂ h₁ h₂ => simp [map_add, h₁, h₂]

theorem lTensor_val_rTensor_closureCounit {B : Subalgebra F (F ⊗[R] G)}
    (z : (flatClosure B) ⊗[R] (flatClosure B)) :
    ((flatClosure B).val.toLinearMap.lTensor R)
        ((closureCounit B).rTensor (flatClosure B) z)
      = (Coalgebra.counit (R := R) (A := G)).rTensor G (tensorInclusion B z) := by
  induction z with
  | zero => simp
  | tmul x y => simp [LinearMap.rTensor_tmul, LinearMap.lTensor_tmul]
  | add a₁ a₂ h₁ h₂ => simp [map_add, h₁, h₂]

theorem rTensor_val_lTensor_closureCounit {B : Subalgebra F (F ⊗[R] G)}
    (z : (flatClosure B) ⊗[R] (flatClosure B)) :
    ((flatClosure B).val.toLinearMap.rTensor R)
        ((closureCounit B).lTensor (flatClosure B) z)
      = (Coalgebra.counit (R := R) (A := G)).lTensor G (tensorInclusion B z) := by
  induction z with
  | zero => simp
  | tmul x y => simp [LinearMap.rTensor_tmul, LinearMap.lTensor_tmul]
  | add a₁ a₂ h₁ h₂ => simp [map_add, h₁, h₂]

theorem closureComul_coassoc [IsDomain R] [IsPrincipalIdealRing R] [IsNoetherianRing R]
    [IsFractionRing R F] [Module.Finite R G] [Module.IsTorsionFree R G]
    {B : Subalgebra F (F ⊗[R] G)} (hB : IsComulStable R F B) :
    TensorProduct.assoc R (flatClosure B) (flatClosure B) (flatClosure B) ∘ₗ
        (closureComul hB).rTensor (flatClosure B) ∘ₗ closureComul hB
      = (closureComul hB).lTensor (flatClosure B) ∘ₗ closureComul hB := by
  apply LinearMap.ext
  intro h
  apply tensorInclusion3_injective B
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [tensorInclusion3_assoc_apply, tensorInclusion3'_rTensor_closureComul,
    tensorInclusion_closureComul, tensorInclusion3_lTensor_closureComul,
    tensorInclusion_closureComul]
  exact Coalgebra.coassoc_apply (h : G)

theorem closureCounit_rTensor_comp_closureComul [IsDomain R] [IsPrincipalIdealRing R]
    [IsNoetherianRing R] [IsFractionRing R F] [Module.Finite R G] [Module.IsTorsionFree R G]
    {B : Subalgebra F (F ⊗[R] G)} (hB : IsComulStable R F B) :
    (closureCounit B).rTensor (flatClosure B) ∘ₗ closureComul hB
      = TensorProduct.mk R R (flatClosure B) 1 := by
  apply LinearMap.ext
  intro h
  apply Module.Flat.lTensor_preserves_injective_linearMap
    ((flatClosure B).val.toLinearMap) Subtype.val_injective
  simp only [LinearMap.comp_apply, TensorProduct.mk_apply, LinearMap.lTensor_tmul]
  rw [lTensor_val_rTensor_closureCounit, tensorInclusion_closureComul,
    Coalgebra.rTensor_counit_comul]
  rfl

theorem closureCounit_lTensor_comp_closureComul [IsDomain R] [IsPrincipalIdealRing R]
    [IsNoetherianRing R] [IsFractionRing R F] [Module.Finite R G] [Module.IsTorsionFree R G]
    {B : Subalgebra F (F ⊗[R] G)} (hB : IsComulStable R F B) :
    (closureCounit B).lTensor (flatClosure B) ∘ₗ closureComul hB
      = (TensorProduct.mk R (flatClosure B) R).flip 1 := by
  apply LinearMap.ext
  intro h
  apply Module.Flat.rTensor_preserves_injective_linearMap
    ((flatClosure B).val.toLinearMap) Subtype.val_injective
  simp only [LinearMap.comp_apply, LinearMap.flip_apply, TensorProduct.mk_apply,
    LinearMap.rTensor_tmul]
  rw [rTensor_val_lTensor_closureCounit, tensorInclusion_closureComul,
    Coalgebra.lTensor_counit_comul]
  rfl

theorem closureCounit_one (B : Subalgebra F (F ⊗[R] G)) :
    closureCounit (R := R) (F := F) B 1 = 1 := by
  simp [Bialgebra.counit_one]

theorem closureCounit_mul {B : Subalgebra F (F ⊗[R] G)} (x y : flatClosure B) :
    closureCounit (R := R) (F := F) B (x * y)
      = closureCounit (R := R) (F := F) B x * closureCounit (R := R) (F := F) B y := by
  simp [Bialgebra.counit_mul]

theorem closureComul_one [IsDomain R] [IsPrincipalIdealRing R] [IsNoetherianRing R]
    [IsFractionRing R F] [Module.Finite R G] [Module.IsTorsionFree R G]
    {B : Subalgebra F (F ⊗[R] G)} (hB : IsComulStable R F B) :
    closureComul hB 1 = 1 := by
  apply tensorInclusion_injective B
  rw [tensorInclusion_closureComul, tensorInclusion_one]
  simp [Bialgebra.comul_one]

theorem closureComul_mul [IsDomain R] [IsPrincipalIdealRing R] [IsNoetherianRing R]
    [IsFractionRing R F] [Module.Finite R G] [Module.IsTorsionFree R G]
    {B : Subalgebra F (F ⊗[R] G)} (hB : IsComulStable R F B) (x y : flatClosure B) :
    closureComul hB (x * y) = closureComul hB x * closureComul hB y := by
  apply tensorInclusion_injective B
  rw [tensorInclusion_closureComul, tensorInclusion_mul, tensorInclusion_closureComul,
    tensorInclusion_closureComul]
  simp [Bialgebra.comul_mul]

variable (R F) in

@[reducible]
noncomputable def closureCoalgebra [IsDomain R] [IsPrincipalIdealRing R] [IsNoetherianRing R]
    [IsFractionRing R F] [Module.Finite R G] [Module.IsTorsionFree R G]
    {B : Subalgebra F (F ⊗[R] G)} (hB : IsComulStable R F B) :
    Coalgebra R (flatClosure B) where
  comul := closureComul hB
  counit := closureCounit B
  coassoc := closureComul_coassoc hB
  rTensor_counit_comp_comul := closureCounit_rTensor_comp_closureComul hB
  lTensor_counit_comp_comul := closureCounit_lTensor_comp_closureComul hB

variable (R F) in

@[reducible]
noncomputable def closureBialgebra [IsDomain R] [IsPrincipalIdealRing R] [IsNoetherianRing R]
    [IsFractionRing R F] [Module.Finite R G] [Module.IsTorsionFree R G]
    {B : Subalgebra F (F ⊗[R] G)} (hB : IsComulStable R F B) :
    Bialgebra R (flatClosure B) :=
  letI : Coalgebra R (flatClosure B) := closureCoalgebra R F hB
  Bialgebra.mk' R (flatClosure B)
    (closureCounit_one B)
    (fun {x y} => closureCounit_mul x y)
    (closureComul_one hB)
    (fun {x y} => closureComul_mul hB x y)

end CoalgebraBialgebra

section Hopf

variable [HopfAlgebra R G]

theorem tensorInclusion_rTensor_closureAntipode {B : Subalgebra F (F ⊗[R] G)}
    (hB' : IsAntipodeStable R F B) (z : (flatClosure B) ⊗[R] (flatClosure B)) :
    tensorInclusion B ((closureAntipode hB').rTensor (flatClosure B) z)
      = (HopfAlgebra.antipode R (A := G)).rTensor G (tensorInclusion B z) := by
  induction z with
  | zero => simp
  | tmul x y => simp [LinearMap.rTensor_tmul]
  | add a₁ a₂ h₁ h₂ => simp [map_add, h₁, h₂]

theorem tensorInclusion_lTensor_closureAntipode {B : Subalgebra F (F ⊗[R] G)}
    (hB' : IsAntipodeStable R F B) (z : (flatClosure B) ⊗[R] (flatClosure B)) :
    tensorInclusion B ((closureAntipode hB').lTensor (flatClosure B) z)
      = (HopfAlgebra.antipode R (A := G)).lTensor G (tensorInclusion B z) := by
  induction z with
  | zero => simp
  | tmul x y => simp [LinearMap.lTensor_tmul]
  | add a₁ a₂ h₁ h₂ => simp [map_add, h₁, h₂]

theorem closure_mul_antipode_rTensor_comul [IsDomain R] [IsPrincipalIdealRing R]
    [IsNoetherianRing R] [IsFractionRing R F] [Module.Finite R G] [Module.IsTorsionFree R G]
    {B : Subalgebra F (F ⊗[R] G)} (hB : IsComulStable R F B) (hB' : IsAntipodeStable R F B) :
    LinearMap.mul' R (flatClosure B) ∘ₗ
        (closureAntipode hB').rTensor (flatClosure B) ∘ₗ closureComul hB
      = (Algebra.linearMap R (flatClosure B)) ∘ₗ closureCounit B := by
  apply LinearMap.ext
  intro h
  apply Subtype.val_injective
  simp only [LinearMap.comp_apply]
  rw [val_mul'_tensorInclusion, tensorInclusion_rTensor_closureAntipode,
    tensorInclusion_closureComul, HopfAlgebra.mul_antipode_rTensor_comul_apply]
  simp [Algebra.linearMap_apply]

theorem closure_mul_antipode_lTensor_comul [IsDomain R] [IsPrincipalIdealRing R]
    [IsNoetherianRing R] [IsFractionRing R F] [Module.Finite R G] [Module.IsTorsionFree R G]
    {B : Subalgebra F (F ⊗[R] G)} (hB : IsComulStable R F B) (hB' : IsAntipodeStable R F B) :
    LinearMap.mul' R (flatClosure B) ∘ₗ
        (closureAntipode hB').lTensor (flatClosure B) ∘ₗ closureComul hB
      = (Algebra.linearMap R (flatClosure B)) ∘ₗ closureCounit B := by
  apply LinearMap.ext
  intro h
  apply Subtype.val_injective
  simp only [LinearMap.comp_apply]
  rw [val_mul'_tensorInclusion, tensorInclusion_lTensor_closureAntipode,
    tensorInclusion_closureComul, HopfAlgebra.mul_antipode_lTensor_comul_apply]
  simp [Algebra.linearMap_apply]

variable (R F) in

@[reducible]
noncomputable def closureHopfAlgebra [IsDomain R] [IsPrincipalIdealRing R] [IsNoetherianRing R]
    [IsFractionRing R F] [Module.Finite R G] [Module.IsTorsionFree R G]
    {B : Subalgebra F (F ⊗[R] G)} (hB : IsComulStable R F B) (hB' : IsAntipodeStable R F B) :
    HopfAlgebra R (flatClosure B) :=
  letI : Bialgebra R (flatClosure B) := closureBialgebra R F hB
  { antipode := closureAntipode hB'
    mul_antipode_rTensor_comul := closure_mul_antipode_rTensor_comul hB hB'
    mul_antipode_lTensor_comul := closure_mul_antipode_lTensor_comul hB hB' }

end Hopf

section Cocomm

variable [HopfAlgebra R G]

theorem tensorInclusion_comm_apply {B : Subalgebra F (F ⊗[R] G)}
    (w : (flatClosure B) ⊗[R] (flatClosure B)) :
    tensorInclusion B (TensorProduct.comm R (flatClosure B) (flatClosure B) w)
      = TensorProduct.comm R G G (tensorInclusion B w) := by
  induction w with
  | zero => simp
  | tmul x y => simp
  | add a b ha hb => simp [ha, hb]

theorem closureIsCocomm [IsDomain R] [IsPrincipalIdealRing R] [IsNoetherianRing R]
    [IsFractionRing R F] [Module.Finite R G] [Module.IsTorsionFree R G]
    [Coalgebra.IsCocomm R G]
    {B : Subalgebra F (F ⊗[R] G)} (hB : IsComulStable R F B) :
    letI : Coalgebra R (flatClosure B) := closureCoalgebra R F hB
    Coalgebra.IsCocomm R (flatClosure B) := by
  letI : Coalgebra R (flatClosure B) := closureCoalgebra R F hB
  refine ⟨LinearMap.ext fun h => tensorInclusion_injective B ?_⟩
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, tensorInclusion_comm_apply]
  change TensorProduct.comm R G G (tensorInclusion B (closureComul hB h))
    = tensorInclusion B (closureComul hB h)
  rw [tensorInclusion_closureComul]
  exact Coalgebra.comm_comul R (h : G)

end Cocomm

section BialgHomInclusion

variable [HopfAlgebra R G]

noncomputable def closureValBialgHom [IsDomain R] [IsPrincipalIdealRing R] [IsNoetherianRing R]
    [IsFractionRing R F] [Module.Finite R G] [Module.IsTorsionFree R G]
    {B : Subalgebra F (F ⊗[R] G)} (hB : IsComulStable R F B) :
    letI : Bialgebra R (flatClosure B) := closureBialgebra R F hB
    flatClosure B →ₐc[R] G := by
  letI : Bialgebra R (flatClosure B) := closureBialgebra R F hB
  exact
    { toFun := (flatClosure B).val
      map_add' := map_add _
      map_smul' := fun r x => (flatClosure B).val.toLinearMap.map_smul r x
      counit_comp := rfl
      map_comp_comul := LinearMap.ext fun h => tensorInclusion_closureComul hB h
      map_one' := map_one (flatClosure B).val
      map_mul' := map_mul (flatClosure B).val }

@[simp]
theorem closureValBialgHom_apply [IsDomain R] [IsPrincipalIdealRing R] [IsNoetherianRing R]
    [IsFractionRing R F] [Module.Finite R G] [Module.IsTorsionFree R G]
    {B : Subalgebra F (F ⊗[R] G)} (hB : IsComulStable R F B) (h : flatClosure B) :
    letI : Bialgebra R (flatClosure B) := closureBialgebra R F hB
    closureValBialgHom hB h = (h : G) := rfl

theorem closureValBialgHom_toAlgHom [IsDomain R] [IsPrincipalIdealRing R] [IsNoetherianRing R]
    [IsFractionRing R F] [Module.Finite R G] [Module.IsTorsionFree R G]
    {B : Subalgebra F (F ⊗[R] G)} (hB : IsComulStable R F B) :
    letI : Bialgebra R (flatClosure B) := closureBialgebra R F hB
    ((closureValBialgHom hB : flatClosure B →ₐc[R] G) : flatClosure B →ₐ[R] G)
      = (flatClosure B).val :=
  AlgHom.ext fun _ => rfl

open WithConv in

theorem convMul_comp_closureVal [IsDomain R] [IsPrincipalIdealRing R] [IsNoetherianRing R]
    [IsFractionRing R F] [Module.Finite R G] [Module.IsTorsionFree R G]
    {B : Subalgebra F (F ⊗[R] G)} (hB : IsComulStable R F B)
    {L : Type*} [CommRing L] [Algebra R L] (f g : WithConv (G →ₐ[R] L)) :
    letI : Bialgebra R (flatClosure B) := closureBialgebra R F hB
    toConv ((f * g).ofConv.comp (flatClosure B).val)
      = toConv (f.ofConv.comp (flatClosure B).val) * toConv (g.ofConv.comp (flatClosure B).val) := by
  letI : Bialgebra R (flatClosure B) := closureBialgebra R F hB
  have h := AlgHom.convMul_comp_bialgHom_distrib f g (closureValBialgHom hB)
  rw [closureValBialgHom_toAlgHom hB] at h
  exact congrArg toConv h

end BialgHomInclusion

end FlatClosureInstances


