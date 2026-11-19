-- Prove2me | Definitions.Def_RPLib_F2_003
-- name    : RPLib_F2_003
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-19T03:18:09.372518+00:00
-- url     : https://prove2.me/theorems/25e60276-3571-4c29-8de7-2a3cd8b7494b
-- title:
--   Ramanujan-Petersson curve library, flat edition, file 003 of 70
-- statement:
--   File 003 of 70 of the flat curve library: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_PicDescent_C1`: S4-PicDescent, part C1: the rings of a constant field extension are tensor products
--   * `S4.Def_RP_PicDescent_D1`: S4-PicDescent, part D1: the Galois action of `Gal(L/Fq)` on a constant field extension
--   * `S4.Def_RP_PicDescent_D2`: S4-PicDescent, part D2: unramified Dedekind extensions, generic
--   * `S4.Def_RP_Kummer_Bridge`: S4-Kummer, part K4a (bridge): divisible valuations give `N`-th-power ideal classes
--   * `S4.Def_RP_Kummer_Ram`: S4-Kummer, part K4b: Kummer radicals inside unramified extensions have `N`-divisible valuations
--   * `S4.Def_RP_Kummer_Fix`: S4-Kummer, part K5a: the fixed field of `π₁^geo` is the union of the constant levels
--   * `S4.Def_RP_PicDescent_D3`: S4-PicDescent, part D3: the ring pair `A → A' ≃ L ⊗ A`
--   * `S4.Def_RP_PicDescent_D4a`: S4-PicDescent, part D4a: places of a ring pair `A → A' ≃ L ⊗ A`, generic
--   * `S4.Def_RP_PicDescent_D4b`: S4-PicDescent, part D4b: contraction of places for a constant field extension
--   * `S4.Def_RP_Kummer_Lev`: S4-Kummer, part K5b: Kummer roots at a constant level `F_m = F ⊗ 𝔽_{q^m}`
--   * `S4.Def_RP_Kummer_Inf`: S4-Kummer K5c: Kummer classes at the boundary (generic core)
--   * `S4.Def_RP_CP4a_Res`: S4-CP4a, part e1: residues of boundary primes of the pro-chart are constants
--   * `S4.Def_RP_CP4a_Trans`: S4-CP4a, part e2: `π₁^geo` is transitive on boundary primes with the same residues
--   * `S4.Def_RP_CP4a_Bres`: S4-CP4a, part e3a: the constant residue map of a boundary prime
--   * `S4.Def_RP_CP4a_Bdry`: S4-CP4a, part e3b: fixed boundary points of the true Frobenius permutation (generic chart `R0`)
--   * `S4.Def_RP_CoreA_ZInt`: S4-CoreA, parts Z1 + Z2: the inverse roots of the zeta function
--   * `S4.Def_RP_CP4a_FE`: S4-CP4a, part a: RH equality, the functional equation, and traces of geometric Frobenius
--   * `S4.Def_RP_CoreA_Div`: S4-CoreA part S1: the divisible part of an `l`-primary group with finite `A[l]`
--   * `S4.Def_RP_CoreA_Basis`: S4-CoreA part S2a: compatible bases of `G[l^N]` for a divisible `l`-primary group
--   * `S4.Def_RP_CoreA_Tate`: S4-CoreA part S2b: the Tate module coordinates and the matrix of an endomorphism
--   * `S4.Def_RP_JacAlg_Kernel`: Core B algebra, part 6: the kernel count (unit S4-JacAlg, lemma L3 = route A2)
--   * `S4.Def_RP_CoreA_Det`: S4-CoreA part S3: kernels of endomorphisms of the divisible group through the Tate matrix
--   * `S4.Def_RP_CoreA_Ord`: S4-CoreA part O1: the l-part of the order of an automorphism of an elementary abelian l-group
--   * `S4.Def_RP_CoreA_Fin`: S4-CoreA part F1: `A[l]` is finite
--   * `S4.Def_RP_CoreA_Grow`: S4-CoreA part S4: growth of `det (1 - X ^ (l ^ j))` for `X ≡ 1 mod l ^ 2`
--   * `S4.Def_RP_CoreA_Rank`: S4-CoreA part Rank: helpers for the main assembly
--   * `S4.Def_RP_CoreA_Main`: S4-CoreA part Main: the Tate module of an `l`-primary group with a Frobenius
--   * `S4.Def_RP_CoreA_Val`: S4-CoreA part V1: norms of `x ^ n - 1` in an ultrametric normed field
--   * `S4.Def_RP_CoreA_ValZ`: S4-CoreA part V2: `l`-adic growth of `h_N = Π_i (1 - c_i ^ N)`
--   * `S4.Def_RP_PicDescent_C2`: S4-PicDescent, part C2: class numbers of the constant field extensions, `h_n = L_n(1)`
--
--   **Formalization note.** One file of the flat edition of a library formalizing Poincaré duality for constant coefficients on an affine curve over a finite field and the Lefschetz trace formula for its Frobenius. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves) and Chapter VI, §13 (the Lefschetz trace formula); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité » and « Rapport sur la formule des traces »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_F2_002

/-!
# Ramanujan-Petersson curve library (flat edition), file 003 of 70

Declarations of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field and of the Lefschetz trace formula for its Frobenius, re-hosted declaration by declaration from
the library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_PicDescent_C1`: S4-PicDescent, part C1: the rings of a constant field extension are tensor products
* `S4.Def_RP_PicDescent_D1`: S4-PicDescent, part D1: the Galois action of `Gal(L/Fq)` on a constant field extension
* `S4.Def_RP_PicDescent_D2`: S4-PicDescent, part D2: unramified Dedekind extensions, generic
* `S4.Def_RP_Kummer_Bridge`: S4-Kummer, part K4a (bridge): divisible valuations give `N`-th-power ideal classes
* `S4.Def_RP_Kummer_Ram`: S4-Kummer, part K4b: Kummer radicals inside unramified extensions have `N`-divisible valuations
* `S4.Def_RP_Kummer_Fix`: S4-Kummer, part K5a: the fixed field of `π₁^geo` is the union of the constant levels
* `S4.Def_RP_PicDescent_D3`: S4-PicDescent, part D3: the ring pair `A → A' ≃ L ⊗ A`
* `S4.Def_RP_PicDescent_D4a`: S4-PicDescent, part D4a: places of a ring pair `A → A' ≃ L ⊗ A`, generic
* `S4.Def_RP_PicDescent_D4b`: S4-PicDescent, part D4b: contraction of places for a constant field extension
* `S4.Def_RP_Kummer_Lev`: S4-Kummer, part K5b: Kummer roots at a constant level `F_m = F ⊗ 𝔽_{q^m}`
* `S4.Def_RP_Kummer_Inf`: S4-Kummer K5c: Kummer classes at the boundary (generic core)
* `S4.Def_RP_CP4a_Res`: S4-CP4a, part e1: residues of boundary primes of the pro-chart are constants
* `S4.Def_RP_CP4a_Trans`: S4-CP4a, part e2: `π₁^geo` is transitive on boundary primes with the same residues
* `S4.Def_RP_CP4a_Bres`: S4-CP4a, part e3a: the constant residue map of a boundary prime
* `S4.Def_RP_CP4a_Bdry`: S4-CP4a, part e3b: fixed boundary points of the true Frobenius permutation (generic chart `R0`)
* `S4.Def_RP_CoreA_ZInt`: S4-CoreA, parts Z1 + Z2: the inverse roots of the zeta function
* `S4.Def_RP_CP4a_FE`: S4-CP4a, part a: RH equality, the functional equation, and traces of geometric Frobenius
* `S4.Def_RP_CoreA_Div`: S4-CoreA part S1: the divisible part of an `l`-primary group with finite `A[l]`
* `S4.Def_RP_CoreA_Basis`: S4-CoreA part S2a: compatible bases of `G[l^N]` for a divisible `l`-primary group
* `S4.Def_RP_CoreA_Tate`: S4-CoreA part S2b: the Tate module coordinates and the matrix of an endomorphism
* `S4.Def_RP_JacAlg_Kernel`: Core B algebra, part 6: the kernel count (unit S4-JacAlg, lemma L3 = route A2)
* `S4.Def_RP_CoreA_Det`: S4-CoreA part S3: kernels of endomorphisms of the divisible group through the Tate matrix
* `S4.Def_RP_CoreA_Ord`: S4-CoreA part O1: the l-part of the order of an automorphism of an elementary abelian l-group
* `S4.Def_RP_CoreA_Fin`: S4-CoreA part F1: `A[l]` is finite
* `S4.Def_RP_CoreA_Grow`: S4-CoreA part S4: growth of `det (1 - X ^ (l ^ j))` for `X ≡ 1 mod l ^ 2`
* `S4.Def_RP_CoreA_Rank`: S4-CoreA part Rank: helpers for the main assembly
* `S4.Def_RP_CoreA_Main`: S4-CoreA part Main: the Tate module of an `l`-primary group with a Frobenius
* `S4.Def_RP_CoreA_Val`: S4-CoreA part V1: norms of `x ^ n - 1` in an ultrametric normed field
* `S4.Def_RP_CoreA_ValZ`: S4-CoreA part V2: `l`-adic growth of `h_N = Π_i (1 - c_i ^ N)`
* `S4.Def_RP_PicDescent_C2`: S4-PicDescent, part C2: class numbers of the constant field extensions, `h_n = L_n(1)`
-/

set_option autoImplicit false

-- ===== S4.Def_RP_PicDescent_C1 =====
section

/-!
# S4-PicDescent, part C1: the rings of a constant field extension are tensor products

For a constant field extension `F' / L` of `F / Fq` in the coordinates of `RR.IsConstExt`, the rings
of places are `Rfin L F' ≃ L ⊗[Fq] Rfin Fq F` and `Rinf L F' ≃ L ⊗[Fq] Rinf Fq F` (`tensorEquiv`, one
generic statement for both rings). Hence `B_1(F') = N_m(F)` with `m = [L : Fq]`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Polynomial TensorProduct

namespace RamanujanPetersson.PicDescent

open Polynomial

section TensorIso

variable {Fq : Type*} [Field Fq] {L : Type*} [Field L] [Algebra Fq L]
  {F : Type*} [Field F] [Algebra Fq F] {F' : Type*} [Field F'] [Algebra L F'] [Algebra F F']
  [Algebra Fq F'] [IsScalarTower Fq F F'] [IsScalarTower Fq L F']
  {ι : Type*} [Fintype ι] {c : Module.Basis ι Fq L}
  {A : Type*} [CommRing A] [Algebra Fq A] [Algebra A F] [IsScalarTower Fq A F]
  {A' : Type*} [CommRing A'] [Algebra L A'] [Algebra A' F'] [IsScalarTower L A' F']

variable (hA : Function.Injective (algebraMap A F)) (hA' : Function.Injective (algebraMap A' F'))
  (hli : LinearIndependent F fun j => algebraMap L F' (c j))
  (hsp : ⊤ ≤ Submodule.span F (Set.range fun j => algebraMap L F' (c j)))
  (hc : ∀ f : ι → F, (∑ j, f j • algebraMap L F' (c j)) ∈ (algebraMap A' F').range ↔
    ∀ j, f j ∈ (algebraMap A F).range)

/-- The tensor map as an algebra map into `A'`. -/
noncomputable def tensorToA' : L ⊗[Fq] A →ₐ[L] A' :=
  (AlgEquiv.ofInjective (IsScalarTower.toAlgHom L A' F') hA').symm.toAlgHom.comp
    ((tensorMap Fq L F F' A).codRestrict _ (tensorMap_mem hc))

theorem algebraMap_tensorToA' (t : L ⊗[Fq] A) :
    algebraMap A' F' (tensorToA' hA' hc t) = tensorMap Fq L F F' A t := by
  have h1 := AlgEquiv.ofInjective_apply (IsScalarTower.toAlgHom L A' F') hA' (tensorToA' hA' hc t)
  have h2 : (AlgEquiv.ofInjective (IsScalarTower.toAlgHom L A' F') hA') (tensorToA' hA' hc t) =
      ⟨tensorMap Fq L F F' A t, tensorMap_mem hc t⟩ :=
    AlgEquiv.apply_symm_apply _ _
  rw [h2] at h1
  exact h1.symm

/-- **`L ⊗[Fq] A ≃ A'`** for a constant field extension in coordinates. -/
noncomputable def tensorEquiv : L ⊗[Fq] A ≃ₐ[L] A' :=
  AlgEquiv.ofBijective (tensorToA' hA' hc)
    ⟨fun s t h => tensorMap_injective hA hli (by
        rw [← algebraMap_tensorToA' hA' hc, ← algebraMap_tensorToA' hA' hc, h]),
      fun y => by
        obtain ⟨t, ht⟩ := exists_tensorMap_eq hsp hc y
        exact ⟨t, hA' (by rw [algebraMap_tensorToA', ht])⟩⟩

end TensorIso

section Instances

variable (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (F : Type*) [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable (L : Type*) [Field L] [Fintype L] [Algebra Fq L] [DecidableEq (RatFunc L)]
variable (F' : Type*) [Field F'] [Algebra L F'] [Algebra L[X] F'] [Algebra (RatFunc L) F']
  [IsScalarTower L[X] (RatFunc L) F'] [IsScalarTower L L[X] F'] [FunctionField L F']
  [Algebra.IsSeparable (RatFunc L) F']
variable [Algebra F F'] [Algebra Fq F'] [IsScalarTower Fq F F'] [IsScalarTower Fq L F']
variable {ι : Type*} [Fintype ι] {c : Module.Basis ι Fq L}

variable {Fq F L F'}

/-- `L ⊗[Fq] Rfin(F) ≃ Rfin(F')` for a constant field extension. -/
noncomputable def e1 (h : RR.IsConstExt Fq F L F' c) :
    L ⊗[Fq] Places.Rfin Fq F ≃ₐ[L] Places.Rfin L F' :=
  tensorEquiv (F := F) (F' := F') (c := c) Subtype.val_injective Subtype.val_injective
    h.linearIndependent h.span h.fin

/-- `L ⊗[Fq] Rinf(F) ≃ Rinf(F')` for a constant field extension. -/
noncomputable def e2 (h : RR.IsConstExt Fq F L F' c) :
    L ⊗[Fq] Places.Rinf Fq F ≃ₐ[L] Places.Rinf L F' :=
  tensorEquiv (F := F) (F' := F') (c := c) Subtype.val_injective Subtype.val_injective
    h.linearIndependent h.span h.inf

variable (L' : Type*) [Field L'] [Algebra L L'] [Algebra Fq L'] [IsScalarTower Fq L L']

theorem card_algHom_Rfin_constExt (h : RR.IsConstExt Fq F L F' c) :
    Nat.card (Places.Rfin L F' →ₐ[L] L') = Nat.card (Places.Rfin Fq F →ₐ[Fq] L') :=
  Nat.card_congr ((AlgEquiv.arrowCongr (e1 h) AlgEquiv.refl).symm.trans
    (AlgHom.liftEquiv Fq L (Places.Rfin Fq F) L').symm)

theorem card_algHom_Rinf_constExt (h : RR.IsConstExt Fq F L F' c) :
    Nat.card (Places.Rinf L F' →ₐ[L] L') = Nat.card (Places.Rinf Fq F →ₐ[Fq] L') :=
  Nat.card_congr ((AlgEquiv.arrowCongr (e2 h) AlgEquiv.refl).symm.trans
    (AlgHom.liftEquiv Fq L (Places.Rinf Fq F) L').symm)

theorem numPoints_constExt_of [Finite L'] (h : RR.IsConstExt Fq F L F' c) :
    Places.numPoints L F' (Module.finrank L L') = Places.numPoints Fq F (Module.finrank Fq L') := by
  rw [Places.numPoints_eq_card_algHom L F' L', Places.numPoints_eq_card_algHom Fq F L',
    card_algHom_Rfin_constExt L' h, card_algHom_Rinf_constExt L' h]

/-- **`N_k(F') = N_{mk}(F)`** for a constant field extension `F' / L` of degree `m = [L : Fq]`. -/
theorem numPoints_constExt (h : RR.IsConstExt Fq F L F' c) {k : ℕ} (hk : k ≠ 0) :
    Places.numPoints L F' k = Places.numPoints Fq F (Module.finrank Fq L * k) := by
  have : Fact (ringChar L).Prime := ⟨CharP.char_is_prime L _⟩
  have : NeZero k := ⟨hk⟩
  let : Algebra Fq (FiniteField.Extension L (ringChar L) k) :=
    ((algebraMap L (FiniteField.Extension L (ringChar L) k)).comp (algebraMap Fq L)).toAlgebra
  have : IsScalarTower Fq L (FiniteField.Extension L (ringChar L) k) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have h1 := numPoints_constExt_of (FiniteField.Extension L (ringChar L) k) h
  rwa [FiniteField.finrank_extension, ← Module.finrank_mul_finrank Fq L,
    FiniteField.finrank_extension] at h1

end Instances

end RamanujanPetersson.PicDescent


end

-- ===== S4.Def_RP_PicDescent_D1 =====
section

/-!
# S4-PicDescent, part D1: the Galois action of `Gal(L/Fq)` on a constant field extension

Generic setting of C1 (`F'` with an `F`-basis `c'_j = algebraMap L F' (c j)`, `c` an `Fq`-basis of `L`).
* `fieldEquiv : L ⊗[Fq] F ≃ₐ[L] F'`; `gal τ : F' ≃ₐ[F] F'` acts by `τ ⊗ id`; `galHom` is an injective group hom;
  `gal_algebraMap_L : gal τ l' = (τ l)'`.
* `mem_range_of_forall_gal`: the fixed field of all `gal τ` is `F` (Artin, `[F' : F] = [L : Fq] = #Gal(L/Fq)`).
* On a ring `A' ≃ L ⊗ A` (C1 `tensorEquiv`): `galA' τ` with `algebraMap_galA'`, `galA'Hom`, `toA' : A → A'`,
  `exists_toA'_eq` (fixed elements of `A'` come from `A`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped TensorProduct

namespace RamanujanPetersson.PicDescent

section Galois

variable {Fq : Type*} [Field Fq] {L : Type*} [Field L] [Algebra Fq L]
  {F : Type*} [Field F] [Algebra Fq F] {F' : Type*} [Field F'] [Algebra L F'] [Algebra F F']
  [Algebra Fq F'] [IsScalarTower Fq F F'] [IsScalarTower Fq L F']
  {ι : Type*} [Fintype ι] {c : Module.Basis ι Fq L}
  (hli : LinearIndependent F fun j => algebraMap L F' (c j))
  (hsp : ⊤ ≤ Submodule.span F (Set.range fun j => algebraMap L F' (c j)))

/-- `L ⊗[Fq] F ≃ F'`. -/
noncomputable def fieldEquiv : L ⊗[Fq] F ≃ₐ[L] F' :=
  tensorEquiv (A := F) (A' := F') (F := F) (F' := F') (algebraMap F F).injective
    (algebraMap F' F').injective hli hsp hcF

theorem fieldEquiv_apply (t : L ⊗[Fq] F) : fieldEquiv hli hsp t = tensorMap Fq L F F' F t :=
  algebraMap_tensorToA' (A := F) (F := F) (c := c) (algebraMap F' F').injective hcF t

theorem tensorMap_one_tmul (f : F) : tensorMap Fq L F F' F (1 ⊗ₜ f) = algebraMap F F' f := by
  rw [tensorMap_tmul, map_one, Algebra.smul_def, mul_one]
  rfl

theorem tensorMap_tmul_one {A : Type*} [CommRing A] [Algebra Fq A] [Algebra A F] [IsScalarTower Fq A F]
    (l : L) : tensorMap Fq L F F' A (l ⊗ₜ[Fq] (1 : A)) = algebraMap L F' l := by
  rw [tensorMap_tmul, map_one, one_smul]

/-- `τ ⊗ id` on `F'`, as a ring automorphism. -/
noncomputable def galRing (τ : L ≃ₐ[Fq] L) : F' ≃+* F' :=
  ((fieldEquiv hli hsp).toRingEquiv.symm.trans
    (Algebra.TensorProduct.congr τ (AlgEquiv.refl : F ≃ₐ[Fq] F)).toRingEquiv).trans
    (fieldEquiv hli hsp).toRingEquiv

theorem galRing_fieldEquiv (τ : L ≃ₐ[Fq] L) (t : L ⊗[Fq] F) :
    galRing hli hsp τ (fieldEquiv hli hsp t) =
      fieldEquiv hli hsp (Algebra.TensorProduct.congr τ (AlgEquiv.refl : F ≃ₐ[Fq] F) t) := by
  show fieldEquiv hli hsp (Algebra.TensorProduct.congr τ AlgEquiv.refl
    ((fieldEquiv hli hsp).symm (fieldEquiv hli hsp t))) = _
  rw [AlgEquiv.symm_apply_apply]

theorem galRing_algebraMap_F (τ : L ≃ₐ[Fq] L) (f : F) :
    galRing hli hsp τ (algebraMap F F' f) = algebraMap F F' f := by
  rw [← tensorMap_one_tmul (Fq := Fq) (L := L), ← fieldEquiv_apply hli hsp, galRing_fieldEquiv, Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul]
  simp

/-- **The Galois action**: `gal τ = τ ⊗ id` on `F' = L ⊗ F`. -/
noncomputable def gal (τ : L ≃ₐ[Fq] L) : F' ≃ₐ[F] F' :=
  AlgEquiv.ofRingEquiv (f := galRing hli hsp τ) (galRing_algebraMap_F hli hsp τ)

theorem gal_fieldEquiv (τ : L ≃ₐ[Fq] L) (t : L ⊗[Fq] F) :
    gal hli hsp τ (fieldEquiv hli hsp t) =
      fieldEquiv hli hsp (Algebra.TensorProduct.congr τ (AlgEquiv.refl : F ≃ₐ[Fq] F) t) :=
  galRing_fieldEquiv hli hsp τ t

theorem gal_algebraMap_L (τ : L ≃ₐ[Fq] L) (l : L) :
    gal hli hsp τ (algebraMap L F' l) = algebraMap L F' (τ l) := by
  rw [← tensorMap_tmul_one (Fq := Fq) (F := F) (A := F) l,
    ← tensorMap_tmul_one (Fq := Fq) (F := F) (A := F) (τ l), ← fieldEquiv_apply hli hsp,
    ← fieldEquiv_apply hli hsp, gal_fieldEquiv, Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
  simp

/-- `τ ↦ gal τ` as a group hom. -/
noncomputable def galHom : (L ≃ₐ[Fq] L) →* (F' ≃ₐ[F] F') where
  toFun := gal hli hsp
  map_one' := AlgEquiv.ext fun x => by
    obtain ⟨t, rfl⟩ := (fieldEquiv hli hsp).surjective x
    rw [gal_fieldEquiv, AlgEquiv.one_apply]
    congr 1
    exact DFunLike.congr_fun (Algebra.TensorProduct.congr_refl (S := Fq) (R := Fq) (A := L) (B := F)) t
  map_mul' τ1 τ2 := AlgEquiv.ext fun x => by
    obtain ⟨t, rfl⟩ := (fieldEquiv hli hsp).surjective x
    rw [AlgEquiv.mul_apply, gal_fieldEquiv, gal_fieldEquiv, gal_fieldEquiv]
    congr 1
    exact DFunLike.congr_fun
      (Algebra.TensorProduct.congr_trans τ2 τ1 (AlgEquiv.refl : F ≃ₐ[Fq] F) AlgEquiv.refl) t

theorem galHom_apply (τ : L ≃ₐ[Fq] L) : galHom hli hsp τ = gal hli hsp τ := rfl

theorem galHom_injective : Function.Injective (galHom hli hsp) := by
  rw [injective_iff_map_eq_one]
  intro τ hτ
  ext l
  have h := congrArg (fun g : F' ≃ₐ[F] F' => g (algebraMap L F' l)) hτ
  simp only [galHom_apply, gal_algebraMap_L, AlgEquiv.one_apply] at h
  exact (algebraMap L F').injective h

/-- **The fixed field of `Gal(L/Fq)` acting on `F'` is `F`.** -/
theorem mem_range_of_forall_gal [Finite L] (x : F') (hx : ∀ τ : L ≃ₐ[Fq] L, gal hli hsp τ x = x) :
    x ∈ (algebraMap F F').range := by
  have : FiniteDimensional F F' := Module.Finite.of_basis (Module.Basis.mk hli hsp)
  have hcard : Nat.card (galHom hli hsp).range = Module.finrank F F' := by
    rw [← Nat.card_congr (MonoidHom.ofInjective (galHom_injective hli hsp)).toEquiv,
      IsGalois.card_aut_eq_finrank, finrank_F' hli hsp]
  have h1 : Module.finrank (IntermediateField.fixedField (galHom hli hsp).range) F' =
      Module.finrank F F' := by
    rw [IntermediateField.finrank_fixedField_eq_card, hcard]
  have h2 := Module.finrank_mul_finrank F (IntermediateField.fixedField (galHom hli hsp).range) F'
  rw [h1] at h2
  have hpos : 0 < Module.finrank F F' := Module.finrank_pos
  have h3 : Module.finrank F (IntermediateField.fixedField (galHom hli hsp).range) = 1 :=
    Nat.eq_of_mul_eq_mul_right hpos (h2.trans (one_mul _).symm)
  rw [IntermediateField.finrank_eq_one_iff] at h3
  have hmem : x ∈ IntermediateField.fixedField (galHom hli hsp).range := by
    rw [IntermediateField.mem_fixedField_iff]
    rintro g ⟨τ, rfl⟩
    exact hx τ
  rw [h3, IntermediateField.mem_bot] at hmem
  obtain ⟨y, hy⟩ := hmem
  exact ⟨y, hy⟩

/-- `f' = Σ_j (d_j f) • c'_j` where `1 = Σ d_j c_j`. -/
theorem algebraMap_F_eq_sum (f : F) :
    algebraMap F F' f = ∑ j, (algebraMap Fq F (c.repr 1 j) * f) • algebraMap L F' (c j) := by
  conv_lhs => rw [← mul_one (algebraMap F F' f), ← map_one (algebraMap L F'), ← c.sum_repr 1]
  rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Algebra.smul_def (c.repr 1 j) (c j), Algebra.smul_def (algebraMap Fq F (c.repr 1 j) * f)]
  simp only [map_mul, ← IsScalarTower.algebraMap_apply]
  ring

section Rings

variable {A : Type*} [CommRing A] [Algebra Fq A] [Algebra A F] [IsScalarTower Fq A F]
  {A' : Type*} [CommRing A'] [Algebra L A'] [Algebra A' F'] [IsScalarTower L A' F']
  (hA : Function.Injective (algebraMap A F)) (hA' : Function.Injective (algebraMap A' F'))
  (hc : ∀ f : ι → F, (∑ j, f j • algebraMap L F' (c j)) ∈ (algebraMap A' F').range ↔
    ∀ j, f j ∈ (algebraMap A F).range)

theorem algebraMap_tensorEquiv (t : L ⊗[Fq] A) :
    algebraMap A' F' (tensorEquiv hA hA' hli hsp hc t) = tensorMap Fq L F F' A t :=
  algebraMap_tensorToA' hA' hc t

theorem gal_tensorMap (τ : L ≃ₐ[Fq] L) (t : L ⊗[Fq] A) :
    gal hli hsp τ (tensorMap Fq L F F' A t) =
      tensorMap Fq L F F' A (Algebra.TensorProduct.congr τ (AlgEquiv.refl : A ≃ₐ[Fq] A) t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul l a =>
    rw [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul, tensorMap_tmul, tensorMap_tmul,
      Algebra.smul_def, Algebra.smul_def, map_mul, AlgEquiv.commutes, gal_algebraMap_L]
    rfl
  | add s t hs ht => simp only [map_add, hs, ht]

/-- `τ ⊗ id` on `A' ≃ L ⊗ A`. -/
noncomputable def galA' (τ : L ≃ₐ[Fq] L) : A' ≃+* A' :=
  ((tensorEquiv hA hA' hli hsp hc).toRingEquiv.symm.trans
    (Algebra.TensorProduct.congr τ (AlgEquiv.refl : A ≃ₐ[Fq] A)).toRingEquiv).trans
    (tensorEquiv hA hA' hli hsp hc).toRingEquiv

theorem algebraMap_galA' (τ : L ≃ₐ[Fq] L) (y : A') :
    algebraMap A' F' (galA' hli hsp hA hA' hc τ y) = gal hli hsp τ (algebraMap A' F' y) := by
  obtain ⟨t, rfl⟩ := (tensorEquiv hA hA' hli hsp hc).surjective y
  have e1 : galA' hli hsp hA hA' hc τ (tensorEquiv hA hA' hli hsp hc t) =
      tensorEquiv hA hA' hli hsp hc (Algebra.TensorProduct.congr τ AlgEquiv.refl t) := by
    show tensorEquiv hA hA' hli hsp hc (Algebra.TensorProduct.congr τ AlgEquiv.refl
      ((tensorEquiv hA hA' hli hsp hc).symm (tensorEquiv hA hA' hli hsp hc t))) = _
    rw [AlgEquiv.symm_apply_apply]
  rw [e1, algebraMap_tensorEquiv, algebraMap_tensorEquiv]
  exact (gal_tensorMap hli hsp τ t).symm

/-- `τ ↦ galA' τ` as a group hom into `RingAut A'`. -/
noncomputable def galA'Hom : (L ≃ₐ[Fq] L) →* RingAut A' where
  toFun := galA' hli hsp hA hA' hc
  map_one' := RingEquiv.ext fun y => hA' (by
    rw [algebraMap_galA', show gal hli hsp 1 = 1 from (galHom hli hsp).map_one]
    rfl)
  map_mul' τ1 τ2 := RingEquiv.ext fun y => hA' (by
    rw [algebraMap_galA', show gal hli hsp (τ1 * τ2) = gal hli hsp τ1 * gal hli hsp τ2 from
      (galHom hli hsp).map_mul τ1 τ2]
    show _ = algebraMap A' F' (galA' hli hsp hA hA' hc τ1 (galA' hli hsp hA hA' hc τ2 y))
    rw [algebraMap_galA', algebraMap_galA']
    rfl)

/-- `A → A'`, `a ↦ 1 ⊗ a`. -/
noncomputable def toA' : A →+* A' :=
  (tensorEquiv hA hA' hli hsp hc).toRingHom.comp
    (Algebra.TensorProduct.includeRight : A →ₐ[Fq] L ⊗[Fq] A).toRingHom

theorem algebraMap_toA' (a : A) :
    algebraMap A' F' (toA' hli hsp hA hA' hc a) = algebraMap F F' (algebraMap A F a) := by
  show algebraMap A' F' (tensorEquiv hA hA' hli hsp hc (1 ⊗ₜ a)) = _
  rw [algebraMap_tensorEquiv, tensorMap_tmul, map_one, Algebra.smul_def, mul_one]

/-- **Fixed elements of `A'` come from `A`.** -/
theorem exists_toA'_eq [Finite L] (y : A') (hy : ∀ τ, galA' hli hsp hA hA' hc τ y = y) :
    ∃ a : A, toA' hli hsp hA hA' hc a = y := by
  have hx : ∀ τ, gal hli hsp τ (algebraMap A' F' y) = algebraMap A' F' y := fun τ => by
    rw [← algebraMap_galA' hli hsp hA hA' hc, hy]
  obtain ⟨f, hf⟩ := mem_range_of_forall_gal hli hsp _ hx
  obtain ⟨t, rfl⟩ := (tensorEquiv hA hA' hli hsp hc).surjective y
  obtain ⟨a, rfl⟩ := exists_sum_tmul c t
  rw [algebraMap_tensorEquiv, tensorMap_sum, algebraMap_F_eq_sum (c := c)] at hf
  have hzero : ∑ j, (algebraMap Fq F (c.repr 1 j) * f - algebraMap A F (a j)) •
      algebraMap L F' (c j) = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, hf, sub_self]
  have hcoef := Fintype.linearIndependent_iff.1 hli _ hzero
  obtain ⟨j0, hj0⟩ : ∃ j, c.repr 1 j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have h1 : (1 : L) = 0 := by rw [← c.sum_repr 1]; simp [hcon]
    exact one_ne_zero h1
  have hd : algebraMap Fq F (c.repr 1 j0) ≠ 0 := (map_ne_zero _).2 hj0
  have ha : algebraMap A F (a j0) = algebraMap Fq F (c.repr 1 j0) * f := (sub_eq_zero.1 (hcoef j0)).symm
  refine ⟨(c.repr 1 j0)⁻¹ • a j0, hA' ?_⟩
  rw [algebraMap_toA', algebraMap_tensorEquiv, tensorMap_sum, ← hf, ← algebraMap_F_eq_sum]
  congr 1
  rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply Fq A F, ha, map_inv₀,
    inv_mul_cancel_left₀ hd]

end Rings

end Galois

end RamanujanPetersson.PicDescent


end

-- ===== S4.Def_RP_PicDescent_D2 =====
section

/-!
# S4-PicDescent, part D2: unramified Dedekind extensions, generic

* `A → B` Dedekind, finite, torsion free, formally unramified (`B ≅ A ⊗ L` for a separable `L`):
  every place `w` of `B` has ramification index `1` over `w.under A`, so
  `valuation_under : (w.under A).valuation K x = w.valuation L x'` (orders agree);
  the fibre over `v` is finite and nonempty, `Σ_{w | v} f(w|v) = [B : A]`, `#(A/v)^f = #(B/w)`.
* `pullH σ w = σ⁻¹(w)` for a ring automorphism `σ` of `B`: `valuation_pullH`
  (`(σ⁻¹ w).valuation x = w.valuation (σ x)`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open IsDedekindDomain

namespace RamanujanPetersson.PicDescent

section Unram

variable {A B : Type*} [CommRing A] [IsDedekindDomain A] [CommRing B] [IsDedekindDomain B]
  [Algebra A B] [Module.IsTorsionFree A B] [Algebra.IsIntegral A B]

theorem ramificationIdx'_under [Algebra.EssFiniteType A B] [Algebra.FormallyUnramified A B]
    (w : HeightOneSpectrum B) : (w.under A).asIdeal.ramificationIdx' w.asIdeal = 1 := by
  rw [Ideal.ramificationIdx'_eq_ramificationIdx (w.under A).asIdeal w.asIdeal (w.under A).ne_bot]
  exact Ideal.ramificationIdx_eq_one w.asIdeal A

/-- **Orders agree** in an unramified extension. -/
theorem valuation_under [Algebra.EssFiniteType A B] [Algebra.FormallyUnramified A B]
    {K L : Type*} [Field K] [Field L] [Algebra K L] [Algebra A K] [IsFractionRing A K] [Algebra A L]
    [IsScalarTower A K L] [Algebra B L] [IsFractionRing B L] [IsScalarTower A B L]
    (w : HeightOneSpectrum B) (x : K) :
    (w.under A).valuation K x = w.valuation L (algebraMap K L x) := by
  have h := HeightOneSpectrum.valuation_liesOver L (w.under A) w x
  rwa [ramificationIdx'_under, pow_one] at h

theorem finite_under (v : HeightOneSpectrum A) : {w : HeightOneSpectrum B | w.under A = v}.Finite := by
  refine ((IsDedekindDomain.primesOver_finite v.asIdeal B).preimage
    (f := HeightOneSpectrum.asIdeal) fun _ _ _ _ h => HeightOneSpectrum.ext h).subset ?_
  intro w hw
  refine ⟨w.isPrime, ⟨?_⟩⟩
  have hw' : w.under A = v := hw
  rw [← hw']
  rfl

theorem exists_under_eq (v : HeightOneSpectrum A) : ∃ w : HeightOneSpectrum B, w.under A = v := by
  obtain ⟨Q, -, hQ, hQv⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := B) v.asIdeal ⊥ (by
    rw [← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).1
      (Module.isTorsionFree_iff_algebraMap_injective.1 inferInstance)]
    exact bot_le)
  have hQ0 : Q ≠ ⊥ := by
    rintro rfl
    apply v.ne_bot
    rw [← hQv, ← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).1
      (Module.isTorsionFree_iff_algebraMap_injective.1 inferInstance)]
  exact ⟨⟨Q, hQ, hQ0⟩, HeightOneSpectrum.ext hQv⟩

/-- **`Σ_{w | v} f(w | v) = [B : A]`** (all `e = 1`). -/
theorem sum_inertiaDeg [Module.Finite A B] [Module.Flat A B] [Algebra.EssFiniteType A B]
    [Algebra.FormallyUnramified A B] (v : HeightOneSpectrum A) :
    ∑ w ∈ (finite_under (B := B) v).toFinset, w.asIdeal.inertiaDeg A = Module.finrank A B := by
  classical
  letI : Fintype (v.asIdeal.primesOver B) := (IsDedekindDomain.primesOver_finite v.asIdeal B).fintype
  rw [← Ideal.sum_ramification_inertia_eq_finrank v.asIdeal B]
  refine Finset.sum_bij (fun w hw => ⟨w.asIdeal, w.isPrime, ⟨?_⟩⟩) (fun _ _ => Finset.mem_univ _)
    (fun w1 _ w2 _ h => HeightOneSpectrum.ext (congrArg Subtype.val h)) (fun q _ => ?_) (fun w _ => ?_)
  · have hw' := (Set.Finite.mem_toFinset _).1 hw
    simp only [Set.mem_ofPred_eq] at hw'
    rw [← hw']
    rfl
  · have hq0 : q.1 ≠ ⊥ := Ideal.ne_bot_of_mem_primesOver v.ne_bot q.2
    haveI := q.2.1
    haveI := q.2.2
    refine ⟨⟨q.1, q.2.1, hq0⟩, (Set.Finite.mem_toFinset _).2 ?_, rfl⟩
    exact HeightOneSpectrum.ext (Ideal.LiesOver.over (P := q.1) (p := v.asIdeal)).symm
  · show _ = w.asIdeal.ramificationIdx A * w.asIdeal.inertiaDeg A
    rw [Ideal.ramificationIdx_eq_one w.asIdeal A, one_mul]

/-- `#(A / v)^f = #(B / w)`. -/
theorem card_quot_pow [Module.Finite A B] (w : HeightOneSpectrum B) :
    Nat.card (A ⧸ (w.under A).asIdeal) ^ w.asIdeal.inertiaDeg A = Nat.card (B ⧸ w.asIdeal) := by
  have h := Ideal.cardQuot_pow_inertiaDeg (w.under A).asIdeal w.asIdeal
  rwa [Submodule.cardQuot_apply, Submodule.cardQuot_apply] at h

end Unram

section Equiv

variable {B : Type*} [CommRing B] [IsDedekindDomain B]

/-- `σ⁻¹(w)` for a ring automorphism `σ`. -/
def pullH (σ : B ≃+* B) (w : HeightOneSpectrum B) : HeightOneSpectrum B :=
  HeightOneSpectrum.comap (σ : B →+* B) σ.surjective w

theorem pullH_asIdeal (σ : B ≃+* B) (w : HeightOneSpectrum B) :
    (pullH σ w).asIdeal = w.asIdeal.comap (σ : B →+* B) := rfl

theorem mem_pullH (σ : B ≃+* B) (w : HeightOneSpectrum B) (b : B) :
    b ∈ (pullH σ w).asIdeal ↔ σ b ∈ w.asIdeal := Iff.rfl

theorem pow_pullH (σ : B ≃+* B) (w : HeightOneSpectrum B) (n : ℕ) :
    (pullH σ w).asIdeal ^ n = (w.asIdeal ^ n).comap (σ : B →+* B) := by
  change (w.asIdeal.comap σ) ^ n = (w.asIdeal ^ n).comap σ
  rw [← Ideal.map_symm, ← Ideal.map_symm, Ideal.map_pow]

theorem intValuation_pullH (σ : B ≃+* B) (w : HeightOneSpectrum B) (b : B) :
    (pullH σ w).intValuation b = w.intValuation (σ b) := by
  rcases eq_or_ne b 0 with rfl | hb
  · simp
  have hσb : σ b ≠ 0 := fun h => hb (σ.injective (h.trans (map_zero σ).symm))
  rw [HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity _ hb,
    HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity _ hσb]
  congr 3
  apply multiplicity_eq_of_emultiplicity_eq
  rw [emultiplicity_eq_emultiplicity_iff]
  intro n
  rw [Ideal.dvd_iff_le, Ideal.dvd_iff_le, Ideal.span_le, Ideal.span_le, Set.singleton_subset_iff,
    Set.singleton_subset_iff, pow_pullH]
  exact Iff.rfl

/-- **Transport of valuations**: `(σ⁻¹ w)(x) = w(σ x)`. -/
theorem valuation_pullH {L : Type*} [Field L] [Algebra B L] [IsFractionRing B L] (σ : B ≃+* B)
    (σL : L ≃+* L) (hσ : ∀ b, algebraMap B L (σ b) = σL (algebraMap B L b))
    (w : HeightOneSpectrum B) (x : L) :
    (pullH σ w).valuation L x = w.valuation L (σL x) := by
  obtain ⟨a, s, -, rfl⟩ := IsFractionRing.div_surjective (A := B) x
  rw [map_div₀, map_div₀, map_div₀, ← hσ, ← hσ, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, intValuation_pullH, intValuation_pullH]

end Equiv

end RamanujanPetersson.PicDescent


end

-- ===== S4.Def_RP_Kummer_Bridge =====
section

/-!
# S4-Kummer, part K4a (bridge): divisible valuations give `N`-th-power ideal classes

* `count_spanSingleton`: `val_v((a)) = -log v(a)` for a nonzero `a` in the fraction field of a Dedekind domain.
* `exists_pow_mul_spanSingleton_eq_one`: if `N ∣ log v(a)` for every height-one prime `v`, then
  `I ^ N * (a) = 1` for a fractional ideal `I`.
* `root_mem_maxUnram_of_dvd`: `M ∈ unramSet A K`, `0 ≠ a ∈ M` with `N ∣ log v(a)` at every prime of the integral
  closure of `A` in `M`, `N` invertible in `A`: every `γ ∈ K̄` with `γ ^ N = a` lies in `maxUnram A K`
  (Galois conjugates handled by `PicDescent.valuation_pullH`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open IsDedekindDomain

namespace RamanujanPetersson
namespace Kummer

noncomputable section

section Bridge

variable {B M : Type*} [CommRing B] [IsDedekindDomain B] [Field M] [Algebra B M] [IsFractionRing B M]

/-- `val_v((a)) = -log v(a)`. -/
theorem count_spanSingleton (v : HeightOneSpectrum B) {a : M} (ha : a ≠ 0) :
    FractionalIdeal.count M v (FractionalIdeal.spanSingleton (nonZeroDivisors B) a) =
      -WithZero.log (v.valuation M a) := by
  obtain ⟨r, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := B) a
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact ha (by simp)
  have hspan : ∀ t : B, t ≠ 0 → Ideal.span {t} ≠ 0 := fun t ht => by
    rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
  have hM : ∀ t : B, t ≠ 0 → algebraMap B M t ≠ 0 := fun t ht =>
    (map_ne_zero_iff _ (IsFractionRing.injective B M)).2 ht
  rw [div_eq_mul_inv, ← FractionalIdeal.spanSingleton_mul_spanSingleton, ← FractionalIdeal.spanSingleton_inv,
    FractionalIdeal.count_mul M v ((FractionalIdeal.spanSingleton_ne_zero_iff).2 (hM r hr0))
      (inv_ne_zero ((FractionalIdeal.spanSingleton_ne_zero_iff).2 (hM s hs0))),
    FractionalIdeal.count_inv, ← FractionalIdeal.coeIdeal_span_singleton,
    ← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe M v (hspan r hr0),
    FractionalIdeal.count_coe M v (hspan s hs0), map_mul, map_inv₀, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_def,
    HeightOneSpectrum.intValuation_def, if_neg hr0, if_neg hs0, ← WithZero.exp_neg, ← WithZero.exp_add,
    WithZero.log_exp]
  ring

/-- **Divisible valuations give an `N`-th-power ideal class**: `I ^ N * (a) = 1`. -/
theorem exists_pow_mul_spanSingleton_eq_one {N : ℕ} [NeZero N] {a : M} (ha : a ≠ 0)
    (hdiv : ∀ v : HeightOneSpectrum B, (N : ℤ) ∣ WithZero.log (v.valuation M a)) :
    ∃ I : FractionalIdeal (nonZeroDivisors B) M,
      I ^ N * FractionalIdeal.spanSingleton (nonZeroDivisors B) a = 1 := by
  classical
  have hspan : FractionalIdeal.spanSingleton (nonZeroDivisors B) a ≠ 0 :=
    (FractionalIdeal.spanSingleton_ne_zero_iff).2 ha
  have hfin : (Function.support fun v : HeightOneSpectrum B =>
      -(FractionalIdeal.count M v (FractionalIdeal.spanSingleton (nonZeroDivisors B) a)) / (N : ℤ)).Finite := by
    refine (Filter.eventually_cofinite.1
      (FractionalIdeal.finite_factors (FractionalIdeal.spanSingleton (nonZeroDivisors B) a))).subset ?_
    intro v hv h0
    apply hv
    simp only [h0, neg_zero, EuclideanDomain.zero_div]
  let e := Finsupp.ofSupportFinite _ hfin
  let I : FractionalIdeal (nonZeroDivisors B) M := e.prod (HeightOneSpectrum.asIdeal · ^ ·)
  have hI0 : I ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun v _ => zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.2 v.ne_bot)
  have hJ0 : I ^ N * FractionalIdeal.spanSingleton (nonZeroDivisors B) a ≠ 0 := mul_ne_zero (pow_ne_zero _ hI0) hspan
  have hcount : ∀ v : HeightOneSpectrum B,
      FractionalIdeal.count M v (I ^ N * FractionalIdeal.spanSingleton (nonZeroDivisors B) a) = 0 := by
    intro v
    rw [FractionalIdeal.count_mul M v (pow_ne_zero _ hI0) hspan, FractionalIdeal.count_pow,
      FractionalIdeal.count_finsuppProd, Finsupp.ofSupportFinite_coe, count_spanSingleton v ha]
    obtain ⟨k, hk⟩ := hdiv v
    rw [hk, neg_neg, Int.mul_ediv_cancel_left _ (Int.natCast_ne_zero.2 (NeZero.ne N))]
    ring
  refine ⟨I, ?_⟩
  calc I ^ N * FractionalIdeal.spanSingleton (nonZeroDivisors B) a
      = ∏ᶠ v : HeightOneSpectrum B, (v.asIdeal : FractionalIdeal (nonZeroDivisors B) M) ^
          (FractionalIdeal.count M v (I ^ N * FractionalIdeal.spanSingleton (nonZeroDivisors B) a)) :=
        (FractionalIdeal.finprod_heightOneSpectrum_factorization' M hJ0).symm
    _ = 1 := by simp only [hcount, zpow_zero, finprod_one]

end Bridge

section Assembly

variable {K : Type} [Field K] (A : Type) [CommRing A] [Algebra A K]

/-- **Kummer roots of elements with `N`-divisible valuations are unramified.** -/
theorem root_mem_maxUnram_of_dvd {M : IntermediateField K (AlgebraicClosure K)} (hM : M ∈ unramSet A K)
    [IsDedekindDomain (integralClosure A M)] [IsFractionRing (integralClosure A M) M] {N : ℕ} [NeZero N]
    (hN : IsUnit (N : A)) {a : M} (ha : a ≠ 0)
    (hdiv : ∀ v : HeightOneSpectrum (integralClosure A M), (N : ℤ) ∣ WithZero.log (v.valuation M a))
    {γ : AlgebraicClosure K} (hγ : γ ^ N = (a : AlgebraicClosure K)) : γ ∈ maxUnram A K := by
  refine root_mem_maxUnram A hM hN ha (fun τ => exists_pow_mul_spanSingleton_eq_one
    ((_root_.map_ne_zero τ).2 ha) (fun w => ?_)) hγ
  let σ : integralClosure A M ≃+* integralClosure A M := (τ.restrictScalars A).mapIntegralClosure.toRingEquiv
  have h : w.valuation M (τ a) = (PicDescent.pullH σ w).valuation M a :=
    (PicDescent.valuation_pullH σ τ.toRingEquiv (fun b => rfl) w a).symm
  rw [h]
  exact hdiv _

end Assembly

end

end Kummer
end RamanujanPetersson


end

-- ===== S4.Def_RP_Kummer_Ram =====
section

/-!
# S4-Kummer, part K4b: Kummer radicals inside unramified extensions have `N`-divisible valuations

* `ramificationIdx_eq_one`: every nonzero prime of `B_L` (`L ∈ unramSet A K`, `A` Dedekind with fraction field `K`, perfect
  residue fields at the maximal ideals) has ramification index `1` over `A` (trivial inertia, `Ideal.card_inertia_eq_ramificationIdxIn`).
* `dvd_log_valuation`: `M ≤ L` both in `unramSet`, `α ∈ L`, `α ^ N = a ∈ M`: `N ∣ log v(a)` at every prime `v` of
  `B_M` (tower `Ideal.ramificationIdx_tower` + `valuation_liesOver`).
* `dvd_log_valuation_of_mem_maxUnram`: the same for `α ∈ maxUnram A K`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open IsDedekindDomain

namespace RamanujanPetersson
namespace Kummer

noncomputable section

variable {K : Type} [Field K] (A : Type) [CommRing A] [IsDedekindDomain A] [Algebra A K] [IsFractionRing A K]

theorem algebraMap_integralClosure_injective (L : IntermediateField K (AlgebraicClosure K)) :
    Function.Injective (algebraMap A (integralClosure A L)) := by
  intro a b h
  have hinj : Function.Injective (algebraMap A L) := by
    rw [IsScalarTower.algebraMap_eq A K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)
  exact hinj (by simpa using congrArg Subtype.val h)

/-- Unramified finite Galois subextensions have ramification index `1` at every prime. -/
theorem ramificationIdx_eq_one {L : IntermediateField K (AlgebraicClosure K)} (hL : L ∈ unramSet A K)
    (hperf : ∀ (p : Ideal A) [p.IsMaximal], PerfectField p.ResidueField)
    (Q : Ideal (integralClosure A L)) [hQ : Q.IsPrime] (hQ0 : Q ≠ ⊥) : Q.ramificationIdx A = 1 := by
  obtain ⟨fL, gL, uL⟩ := hL
  have : IsFractionRing (integralClosure A L) L := integralClosure.isFractionRing_of_finite_extension (A := A) K L
  have : Module.Finite A (integralClosure A L) := IsIntegralClosure.finite A K L (integralClosure A L)
  have : IsGaloisGroup (L ≃ₐ[K] L) A (integralClosure A L) :=
    IsGaloisGroup.of_isFractionRing (L ≃ₐ[K] L) A (integralClosure A L) K L
  have : Module.IsTorsionFree A (integralClosure A L) :=
    Module.isTorsionFree_iff_algebraMap_injective.2 (algebraMap_integralClosure_injective A L)
  have : IsDedekindDomain (integralClosure A L) := integralClosure.isDedekindDomain (A := A) (K := K) (L := L)
  have : Q.IsMaximal := hQ.isMaximal hQ0
  have : (Q.under A).IsMaximal := Ideal.IsMaximal.under A Q
  have : PerfectField (Q.under A).ResidueField := hperf (Q.under A)
  have h1 := Ideal.card_inertia_eq_ramificationIdxIn (G := L ≃ₐ[K] L) (Q.under A) Q
  rw [uL Q hQ, Subgroup.card_bot, Ideal.ramificationIdxIn_eq_ramificationIdx (Q.under A) Q (L ≃ₐ[K] L)] at h1
  exact h1.symm

/-- **Kummer radicals in unramified extensions have `N`-divisible valuations.** -/
theorem dvd_log_valuation {M L : IntermediateField K (AlgebraicClosure K)} (hML : M ≤ L) (hM : M ∈ unramSet A K)
    (hL : L ∈ unramSet A K) (hperf : ∀ (p : Ideal A) [p.IsMaximal], PerfectField p.ResidueField)
    {N : ℕ} {α : AlgebraicClosure K} (hαL : α ∈ L) {a : M} (hα : α ^ N = (a : AlgebraicClosure K))
    [IsDedekindDomain (integralClosure A M)] [IsFractionRing (integralClosure A M) M]
    (v : HeightOneSpectrum (integralClosure A M)) : (N : ℤ) ∣ WithZero.log (v.valuation M a) := by
  have := hM.1
  have := hL.1
  have := hL.2.1
  have : IsFractionRing (integralClosure A L) L := integralClosure.isFractionRing_of_finite_extension (A := A) K L
  have : IsDedekindDomain (integralClosure A L) := integralClosure.isDedekindDomain (A := A) (K := K) (L := L)
  letI : Algebra (integralClosure A M) (integralClosure A L) := (incl A K hML).toRingHom.toAlgebra
  letI : SMul (integralClosure A M) (integralClosure A L) := Algebra.toSMul
  letI : Algebra M L := (IntermediateField.inclusion hML).toRingHom.toAlgebra
  letI : Algebra (integralClosure A M) L :=
    ((algebraMap M L).comp (algebraMap (integralClosure A M) M)).toAlgebra
  have : @IsScalarTower (integralClosure A M) M L Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : @IsScalarTower (integralClosure A M) (integralClosure A L) L Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : IsScalarTower A (integralClosure A M) (integralClosure A L) :=
    IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext (Subtype.ext rfl))
  have : Module.IsTorsionFree (integralClosure A M) (integralClosure A L) :=
    Module.isTorsionFree_iff_algebraMap_injective.2 fun x y h =>
      Subtype.ext (Subtype.ext (congrArg (fun z : integralClosure A L => ((z : L) : AlgebraicClosure K)) h))
  have : Algebra.IsIntegral (integralClosure A M) (integralClosure A L) :=
    ⟨fun x => (Algebra.IsIntegral.isIntegral (R := A) x).tower_top⟩
  have : Module.Flat (integralClosure A M) (integralClosure A L) := inferInstance
  obtain ⟨w, rfl⟩ := PicDescent.exists_under_eq (A := integralClosure A M) (B := integralClosure A L) v
  have he : w.asIdeal.ramificationIdx (integralClosure A M) = 1 := by
    have h1 := ramificationIdx_eq_one A hL hperf w.asIdeal w.ne_bot
    rw [Ideal.ramificationIdx_tower (R := A) (w.under (integralClosure A M)).asIdeal w.asIdeal] at h1
    exact Nat.dvd_one.1 ⟨_, h1.symm.trans (mul_comm _ _)⟩
  have he' : (w.under (integralClosure A M)).asIdeal.ramificationIdx' w.asIdeal = 1 := by
    rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _ (w.under (integralClosure A M)).ne_bot]
    exact he
  have hval := HeightOneSpectrum.valuation_liesOver L (w.under (integralClosure A M)) w a
  rw [he', pow_one] at hval
  have hαa : algebraMap M L a = (⟨α, hαL⟩ : L) ^ N := by
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow]
    exact hα.symm
  rw [hval, hαa, map_pow, WithZero.log_pow]
  exact ⟨_, nsmul_eq_mul _ _⟩

/-- The same for a Kummer radical `α ∈ K_U`. -/
theorem dvd_log_valuation_of_mem_maxUnram {M : IntermediateField K (AlgebraicClosure K)} (hM : M ∈ unramSet A K)
    (hperf : ∀ (p : Ideal A) [p.IsMaximal], PerfectField p.ResidueField)
    {N : ℕ} {α : AlgebraicClosure K} (hαU : α ∈ maxUnram A K) {a : M} (hα : α ^ N = (a : AlgebraicClosure K))
    [IsDedekindDomain (integralClosure A M)] [IsFractionRing (integralClosure A M) M]
    (v : HeightOneSpectrum (integralClosure A M)) : (N : ℤ) ∣ WithZero.log (v.valuation M a) := by
  obtain ⟨L, hL, hle⟩ := exists_unramSet_of_finite A K {α} (by simpa using hαU)
  refine dvd_log_valuation A (le_sup_left : M ≤ M ⊔ L) hM (sup_mem_unramSet A K hM hL) hperf ?_ hα v
  exact (le_sup_right : L ≤ M ⊔ L) (hle (IntermediateField.subset_adjoin K _ (by simp)))

end

end Kummer
end RamanujanPetersson


end

-- ===== S4.Def_RP_Kummer_Fix =====
section

/-!
# S4-Kummer, part K5a: the fixed field of `π₁^geo` is the union of the constant levels

`pi1geo A K q` (automorphisms of `K_U` fixing every constant) has fixed field `⋃_k K(𝔽_{p^k}) ∩ K_U`
(infinite Galois correspondence on `K_U / K`):

* `fixed_iff_mem_constLevel`: `x ∈ K_U` is fixed by `π₁^geo` iff `x ∈ constLevel K p k` for some `k > 0`;
* `mem_rad_pi1geo_iff`: `α ∈ rad π₁^geo N` iff `α ^ N` lies in some constant level.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Kummer

open CurveCoh Polynomial

noncomputable section

/-- `y ^ b ^ n = y` implies `y ^ b ^ (n * j) = y`. -/
theorem pow_pow_mul_eq {L : Type*} [Monoid L] {y : L} {b n : ℕ} (h : y ^ b ^ n = y) (j : ℕ) :
    y ^ b ^ (n * j) = y := by
  induction j with
  | zero => simp
  | succ j ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, h]

/-- Generic: an automorphism fixing a set fixes the field it generates. -/
theorem mem_fixingSubgroup_adjoin' {K E : Type*} [Field K] [Field E] [Algebra K E] {S : Set E}
    {σ : E ≃ₐ[K] E} (h : ∀ x ∈ S, σ x = x) : σ ∈ (IntermediateField.adjoin K S).fixingSubgroup := by
  have hle : IntermediateField.adjoin K S ≤
      IntermediateField.fixedField (_root_.fixingSubgroup (E ≃ₐ[K] E) S) := by
    rw [IntermediateField.adjoin_le_iff]
    intro x hx
    rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
    intro f hf
    exact (_root_.mem_fixingSubgroup_iff _).1 hf x hx
  exact (IntermediateField.le_iff_le _ _).1 hle ((_root_.mem_fixingSubgroup_iff _).2 h)

section Fix

variable (A K : Type) [CommRing A] [Field K] [Algebra A K] {p : ℕ} [hp : Fact p.Prime] [CharP K p]

/-- The constants of `K_U` (of level `q`) generate an intermediate field of `K_U / K`. -/
def constFieldU (q : ℕ) : IntermediateField K (maxUnram A K) :=
  IntermediateField.adjoin K {x | IsConst q x}

theorem fixingSubgroup_constFieldU (q : ℕ) : (constFieldU A K q).fixingSubgroup = pi1geo A K q := by
  ext σ
  constructor
  · intro hσ
    rw [mem_pi1geo]
    intro x hx
    exact (IntermediateField.mem_fixingSubgroup_iff ..).1 hσ x (IntermediateField.subset_adjoin K _ hx)
  · intro hσ
    exact mem_fixingSubgroup_adjoin' fun x hx => (mem_pi1geo A K q σ).1 hσ x hx

variable {A K}

/-- Elements of `K_U` fixed by `π₁^geo` lie in a constant level `K(𝔽_{q^k})`. -/
theorem exists_constLevel_of_fixed {e : ℕ} (he : 0 < e) {x : maxUnram A K}
    (hx : ∀ σ ∈ pi1geo A K (p ^ e), σ x = x) :
    ∃ k, 0 < k ∧ (x : AlgebraicClosure K) ∈ constLevel K p (e * k) := by
  have hmem : x ∈ IntermediateField.fixedField (constFieldU A K (p ^ e)).fixingSubgroup := by
    rw [IntermediateField.mem_fixedField_iff]
    intro σ hσ
    rw [fixingSubgroup_constFieldU] at hσ
    exact hx σ hσ
  rw [InfiniteGalois.fixedField_fixingSubgroup] at hmem
  obtain ⟨T, hT, hxT⟩ := IntermediateField.exists_finset_of_mem_adjoin hmem
  have hc : ∀ y ∈ T, IsConst (p ^ e) y := fun y hy => hT hy
  choose! n hn hpow using hc
  refine ⟨∏ y ∈ T, n y, Finset.prod_pos fun y hy => hn y hy, ?_⟩
  have hle : (IntermediateField.adjoin K (T : Set (maxUnram A K))).map (maxUnram A K).val ≤
      constLevel K p (e * ∏ y ∈ T, n y) := by
    rw [IntermediateField.adjoin_map, IntermediateField.adjoin_le_iff]
    rintro _ ⟨y, hy, rfl⟩
    have hk : 0 < e * ∏ y ∈ T, n y := Nat.mul_pos he (Finset.prod_pos fun y hy => hn y hy)
    refine mem_constLevel hk ?_
    obtain ⟨j, hj⟩ := Finset.dvd_prod_of_mem n hy
    have h1 := pow_pow_mul_eq (hpow y hy) j
    rw [← hj, ← pow_mul] at h1
    show ((y : AlgebraicClosure K)) ^ p ^ (e * ∏ y ∈ T, n y) = y
    rw [← SubmonoidClass.coe_pow, h1]
  exact hle ⟨x, hxT, rfl⟩

/-- Elements of a constant level are fixed by `π₁^geo`. -/
theorem fixed_of_mem_constLevel {e k : ℕ} (he : 0 < e) (hk : 0 < k) {x : maxUnram A K}
    (hx : (x : AlgebraicClosure K) ∈ constLevel K p k) : ∀ σ ∈ pi1geo A K (p ^ e), σ x = x := by
  intro σ hσ
  let C : IntermediateField K (maxUnram A K) :=
    IntermediateField.adjoin K {y : maxUnram A K | y ^ p ^ k = y}
  have hσC : σ ∈ C.fixingSubgroup := by
    refine mem_fixingSubgroup_adjoin' ?_
    intro y hy
    refine (mem_pi1geo A K _ σ).1 hσ y ⟨k, hk, ?_⟩
    have hy' : y ^ p ^ k = y := hy
    rw [← pow_mul, mul_comm e k]
    exact pow_pow_mul_eq hy' e
  have hxC : x ∈ C := by
    have hle : constLevel K p k ≤ C.map (maxUnram A K).val := by
      rw [IntermediateField.adjoin_map]
      refine IntermediateField.adjoin_le_iff.2 fun r hr => ?_
      have hr' : r ^ p ^ k = r := by
        rw [mem_rootSet] at hr
        simpa [sub_eq_zero] using hr.2
      refine IntermediateField.subset_adjoin K _ ⟨⟨r, mem_maxUnram_of_pow A hk hr'⟩, ?_, rfl⟩
      exact Subtype.ext hr'
    obtain ⟨y, hy, hyx⟩ := hle hx
    rwa [show y = x from Subtype.ext hyx] at hy
  exact (IntermediateField.mem_fixingSubgroup_iff ..).1 hσC x hxC

end Fix

end

end Kummer
end RamanujanPetersson


end

-- ===== S4.Def_RP_PicDescent_D3 =====
section

/-!
# S4-PicDescent, part D3: the ring pair `A → A' ≃ L ⊗ A`

Setting of D1 section `Rings` plus an algebra `A → A'` compatible with `F → F'`.
* `algebraMap_A_A'`: `algebraMap A A' = toA'`; `eAB : A ⊗[Fq] L ≃ₐ[A] A'`.
* `moduleFree`, `moduleFinite`, `finrank_A_A'` (`= [L : Fq]`), `formallyUnramified`, `isTorsionFree`.
* `galAct`: `Gal(L/Fq)` acts on `A'` by `galA'`; `smulCommClass`, `isInvariant` (fixed ring `A`),
  `exists_pullH_of_under_eq`: `Gal(L/Fq)` is transitive on the places of `A'` over a place of `A`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped TensorProduct Pointwise
open IsDedekindDomain

namespace RamanujanPetersson.PicDescent

section Pair

variable {Fq : Type*} [Field Fq] {L : Type*} [Field L] [Algebra Fq L]
  {F : Type*} [Field F] [Algebra Fq F] {F' : Type*} [Field F'] [Algebra L F'] [Algebra F F']
  [Algebra Fq F'] [IsScalarTower Fq F F'] [IsScalarTower Fq L F']
  {ι : Type*} [Fintype ι] {c : Module.Basis ι Fq L}
  (hli : LinearIndependent F fun j => algebraMap L F' (c j))
  (hsp : ⊤ ≤ Submodule.span F (Set.range fun j => algebraMap L F' (c j)))
  {A : Type*} [CommRing A] [Algebra Fq A] [Algebra A F] [IsScalarTower Fq A F]
  {A' : Type*} [CommRing A'] [Algebra L A'] [Algebra A' F'] [IsScalarTower L A' F']
  (hA : Function.Injective (algebraMap A F)) (hA' : Function.Injective (algebraMap A' F'))
  (hc : ∀ f : ι → F, (∑ j, f j • algebraMap L F' (c j)) ∈ (algebraMap A' F').range ↔
    ∀ j, f j ∈ (algebraMap A F).range)
  [Algebra A A'] [Algebra A F'] [IsScalarTower A F F'] [IsScalarTower A A' F']

theorem algebraMap_A_A' (a : A) : algebraMap A A' a = toA' hli hsp hA hA' hc a :=
  hA' (by rw [algebraMap_toA', ← IsScalarTower.algebraMap_apply A A' F',
    IsScalarTower.algebraMap_apply A F F'])

/-- `A ⊗[Fq] L ≃ₐ[A] A'`. -/
noncomputable def eAB : A ⊗[Fq] L ≃ₐ[A] A' :=
  AlgEquiv.ofRingEquiv (f := (Algebra.TensorProduct.comm Fq A L).toRingEquiv.trans
    (tensorEquiv hA hA' hli hsp hc).toRingEquiv) (fun a => by
      rw [algebraMap_A_A' hli hsp hA hA' hc]
      show tensorEquiv hA hA' hli hsp hc (Algebra.TensorProduct.comm Fq A L (a ⊗ₜ 1)) = _
      rw [Algebra.TensorProduct.comm_tmul]
      rfl)

include hA hA' in
theorem algebraMap_A_A'_injective : Function.Injective (algebraMap A A') := by
  intro a b h
  apply hA
  apply (algebraMap F F').injective
  rw [← IsScalarTower.algebraMap_apply A F F', ← IsScalarTower.algebraMap_apply A F F',
    IsScalarTower.algebraMap_apply A A' F', IsScalarTower.algebraMap_apply A A' F' b, h]

include hli hsp hA hA' hc in
theorem moduleFree : Module.Free A A' :=
  Module.Free.of_equiv (eAB hli hsp hA hA' hc).toLinearEquiv

include hli hsp hA hA' hc in
theorem moduleFinite [Module.Finite Fq L] : Module.Finite A A' :=
  Module.Finite.equiv (eAB hli hsp hA hA' hc).toLinearEquiv

include hli hsp hA hA' hc in
theorem finrank_A_A' [Nontrivial A] : Module.finrank A A' = Module.finrank Fq L :=
  (eAB hli hsp hA hA' hc).toLinearEquiv.finrank_eq.symm.trans Module.finrank_baseChange

include hli hsp hA hA' hc in
theorem formallyUnramified [Algebra.IsSeparable Fq L] : Algebra.FormallyUnramified A A' := by
  haveI := Algebra.FormallyUnramified.of_isSeparable Fq L
  exact Algebra.FormallyUnramified.of_equiv (eAB hli hsp hA hA' hc)

include hA hA' in
theorem isTorsionFree [IsDomain A] [IsDomain A'] : Module.IsTorsionFree A A' :=
  Module.isTorsionFree_iff_algebraMap_injective.2 (algebraMap_A_A'_injective hA hA')

/-- `galA' τ` fixes `A`. -/
theorem galA'_algebraMap (τ : L ≃ₐ[Fq] L) (a : A) :
    galA' hli hsp hA hA' hc τ (algebraMap A A' a) = algebraMap A A' a :=
  hA' (by rw [algebraMap_galA', ← IsScalarTower.algebraMap_apply A A' F',
    IsScalarTower.algebraMap_apply A F F', AlgEquiv.commutes])

/-- `Gal(L/Fq)` acting on `A'` through `galA'`. -/
noncomputable def galAct : MulSemiringAction (L ≃ₐ[Fq] L) A' :=
  MulSemiringAction.compHom A' (galA'Hom hli hsp hA hA' hc)

theorem galAct_smul (τ : L ≃ₐ[Fq] L) (y : A') :
    (galAct hli hsp hA hA' hc).smul τ y = galA' hli hsp hA hA' hc τ y := rfl

theorem smulCommClass : letI := galAct hli hsp hA hA' hc; SMulCommClass (L ≃ₐ[Fq] L) A A' := by
  letI := galAct hli hsp hA hA' hc
  refine ⟨fun τ a y => ?_⟩
  show galA' hli hsp hA hA' hc τ (a • y) = a • galA' hli hsp hA hA' hc τ y
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, galA'_algebraMap]

theorem isInvariant [Finite L] :
    letI := galAct hli hsp hA hA' hc; Algebra.IsInvariant A A' (L ≃ₐ[Fq] L) := by
  letI := galAct hli hsp hA hA' hc
  refine ⟨fun y hy => ?_⟩
  obtain ⟨a, ha⟩ := exists_toA'_eq hli hsp hA hA' hc y hy
  exact ⟨a, (algebraMap_A_A' hli hsp hA hA' hc a).trans ha⟩

theorem finite_gal [Finite L] : Finite (L ≃ₐ[Fq] L) :=
  Finite.of_injective (fun τ : L ≃ₐ[Fq] L => (τ : L → L)) DFunLike.coe_injective

/-- **Transitivity on fibres**: places of `A'` over the same place of `A` are `Gal(L/Fq)`-conjugate. -/
theorem exists_pullH_of_under_eq [Finite L] [IsDedekindDomain A'] (w1 w2 : HeightOneSpectrum A')
    (h : w1.asIdeal.under A = w2.asIdeal.under A) :
    ∃ τ : L ≃ₐ[Fq] L, w2 = pullH (galA' hli hsp hA hA' hc τ) w1 := by
  letI := galAct hli hsp hA hA' hc
  haveI := smulCommClass hli hsp hA hA' hc
  haveI := isInvariant hli hsp hA hA' hc
  haveI := finite_gal (Fq := Fq) (L := L)
  haveI := w1.isPrime
  haveI := w2.isPrime
  obtain ⟨g, hg⟩ :=
    Algebra.IsInvariant.exists_smul_of_under_eq A A' (L ≃ₐ[Fq] L) w1.asIdeal w2.asIdeal h
  refine ⟨g⁻¹, HeightOneSpectrum.ext ?_⟩
  rw [pullH_asIdeal, hg, Ideal.pointwise_smul_eq_comap]
  ext y
  exact Iff.rfl

end Pair

end RamanujanPetersson.PicDescent


end

-- ===== S4.Def_RP_PicDescent_D4a =====
section

/-!
# S4-PicDescent, part D4a: places of a ring pair `A → A' ≃ L ⊗ A`, generic

Setting of D3 (Dedekind `A`, `A'`, finite `L`).
* `cont w = w ∩ A` (contraction); `ord_cont`: `ord_{cont w} f = ord_w f'`; fibres finite (`finite_cont`)
  and nonempty (`exists_cont_eq`); `deg_cont_mul`: `deg (cont w) · f(w) = [L : Fq] · deg_L w`;
  `sum_deg_cont`: `Σ_{cont w = v} deg_L w = deg v`.
* Galois: `cont_pullH`, `ord_pullH` (`ord_{τ⁻¹ w} f = ord_w (gal τ f)`), `pullH_pullH`, `pullH_one`,
  `plEquiv`, `exists_pullH_of_cont_eq` (transitivity on fibres).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open IsDedekindDomain

namespace RamanujanPetersson.PicDescent

section PairPlaces

variable {Fq : Type*} [Field Fq] {L : Type*} [Field L] [Algebra Fq L]
  {F : Type*} [Field F] [Algebra Fq F] {F' : Type*} [Field F'] [Algebra L F'] [Algebra F F']
  [Algebra Fq F'] [IsScalarTower Fq F F'] [IsScalarTower Fq L F']
  {ι : Type*} [Fintype ι] {c : Module.Basis ι Fq L}
  (hli : LinearIndependent F fun j => algebraMap L F' (c j))
  (hsp : ⊤ ≤ Submodule.span F (Set.range fun j => algebraMap L F' (c j)))
  {A : Type*} [CommRing A] [Algebra Fq A] [Algebra A F] [IsScalarTower Fq A F]
  {A' : Type*} [CommRing A'] [Algebra L A'] [Algebra A' F'] [IsScalarTower L A' F']
  (hA : Function.Injective (algebraMap A F)) (hA' : Function.Injective (algebraMap A' F'))
  (hc : ∀ f : ι → F, (∑ j, f j • algebraMap L F' (c j)) ∈ (algebraMap A' F').range ↔
    ∀ j, f j ∈ (algebraMap A F).range)
  [Algebra A A'] [Algebra A F'] [IsScalarTower A F F'] [IsScalarTower A A' F']
  [IsDedekindDomain A] [IsDedekindDomain A'] [Finite L]

include hli hsp hA hA' hc in
theorem isIntegral_AA' : Algebra.IsIntegral A A' := by
  haveI := moduleFinite hli hsp hA hA' hc
  exact Algebra.IsIntegral.of_finite A A'

/-- The contraction `w ↦ w ∩ A`. -/
noncomputable def cont (w : HeightOneSpectrum A') : HeightOneSpectrum A :=
  haveI := isIntegral_AA' hli hsp hA hA' hc
  w.under A

theorem cont_asIdeal (w : HeightOneSpectrum A') :
    (cont hli hsp hA hA' hc w).asIdeal = w.asIdeal.comap (algebraMap A A') := rfl

/-- **Orders agree**: `ord_{w ∩ A} f = ord_w f'`. -/
theorem ord_cont [IsFractionRing A F] [IsFractionRing A' F'] [Algebra.IsSeparable Fq L]
    (w : HeightOneSpectrum A') (f : F) :
    Places.ord (cont hli hsp hA hA' hc w) f = Places.ord w (algebraMap F F' f) := by
  haveI := isIntegral_AA' hli hsp hA hA' hc
  haveI := isTorsionFree hA hA'
  haveI := formallyUnramified hli hsp hA hA' hc
  haveI := moduleFinite hli hsp hA hA' hc
  unfold Places.ord
  rw [show (cont hli hsp hA hA' hc w).valuation F f = w.valuation F' (algebraMap F F' f) from
    valuation_under w f]

theorem finite_cont (v : HeightOneSpectrum A) :
    {w : HeightOneSpectrum A' | cont hli hsp hA hA' hc w = v}.Finite := by
  haveI := isIntegral_AA' hli hsp hA hA' hc
  haveI := isTorsionFree hA hA'
  exact finite_under v

theorem exists_cont_eq (v : HeightOneSpectrum A) : ∃ w : HeightOneSpectrum A', cont hli hsp hA hA' hc w = v := by
  haveI := isIntegral_AA' hli hsp hA hA' hc
  haveI := isTorsionFree hA hA'
  exact exists_under_eq v

theorem deg_cont_mul [Fintype Fq] [Fintype L] [Places.FiniteQuot A] [Places.FiniteQuot A']
    (w : HeightOneSpectrum A') :
    Places.deg Fq (cont hli hsp hA hA' hc w) * w.asIdeal.inertiaDeg A =
      Module.finrank Fq L * Places.deg L w := by
  haveI := isIntegral_AA' hli hsp hA hA' hc
  haveI := isTorsionFree hA hA'
  haveI := moduleFinite hli hsp hA hA' hc
  have h1 := card_quot_pow (A := A) w
  rw [Places.card_residue_eq Fq (w.under A), Places.card_residue_eq L w, Module.card_eq_pow_finrank (K := Fq) (V := L),
    ← pow_mul, ← pow_mul] at h1
  exact Nat.pow_right_injective (Fintype.one_lt_card (α := Fq)) h1

/-- **`Σ_{w | v} deg_L w = deg v`**. -/
theorem sum_deg_cont [Fintype Fq] [Fintype L] [Places.FiniteQuot A] [Places.FiniteQuot A']
    [Algebra.IsSeparable Fq L] (v : HeightOneSpectrum A) :
    ∑ w ∈ (finite_cont hli hsp hA hA' hc v).toFinset, Places.deg L w = Places.deg Fq v := by
  haveI := isIntegral_AA' hli hsp hA hA' hc
  haveI := isTorsionFree hA hA'
  haveI := moduleFinite hli hsp hA hA' hc
  haveI := moduleFree hli hsp hA hA' hc
  haveI := formallyUnramified hli hsp hA hA' hc
  have hk : 0 < Module.finrank Fq L := Module.finrank_pos
  have hs : ∑ w ∈ (finite_cont hli hsp hA hA' hc v).toFinset, w.asIdeal.inertiaDeg A =
      Module.finrank Fq L := by
    rw [← finrank_A_A' hli hsp hA hA' hc]
    exact sum_inertiaDeg v
  apply Nat.eq_of_mul_eq_mul_left hk
  rw [Finset.mul_sum]
  calc ∑ w ∈ (finite_cont hli hsp hA hA' hc v).toFinset, Module.finrank Fq L * Places.deg L w
      = ∑ w ∈ (finite_cont hli hsp hA hA' hc v).toFinset, Places.deg Fq v * w.asIdeal.inertiaDeg A := by
        refine Finset.sum_congr rfl fun w hw => ?_
        have hw' : cont hli hsp hA hA' hc w = v := by
          have h2 := (Set.Finite.mem_toFinset _).1 hw
          exact h2
        rw [← deg_cont_mul hli hsp hA hA' hc w, hw']
    _ = Module.finrank Fq L * Places.deg Fq v := by rw [← Finset.mul_sum, hs, mul_comm]

theorem cont_pullH (τ : L ≃ₐ[Fq] L) (w : HeightOneSpectrum A') :
    cont hli hsp hA hA' hc (pullH (galA' hli hsp hA hA' hc τ) w) = cont hli hsp hA hA' hc w := by
  apply HeightOneSpectrum.ext
  ext a
  show galA' hli hsp hA hA' hc τ (algebraMap A A' a) ∈ w.asIdeal ↔ algebraMap A A' a ∈ w.asIdeal
  rw [galA'_algebraMap]

/-- **Transport of orders**: `ord_{τ⁻¹ w} f = ord_w (gal τ f)`. -/
theorem ord_pullH [IsFractionRing A' F'] (τ : L ≃ₐ[Fq] L) (w : HeightOneSpectrum A') (f : F') :
    Places.ord (pullH (galA' hli hsp hA hA' hc τ) w) f = Places.ord w (gal hli hsp τ f) := by
  unfold Places.ord
  rw [valuation_pullH (galA' hli hsp hA hA' hc τ) (gal hli hsp τ).toRingEquiv
    (fun b => algebraMap_galA' hli hsp hA hA' hc τ b) w f]
  rfl

theorem pullH_pullH (τ1 τ2 : L ≃ₐ[Fq] L) (w : HeightOneSpectrum A') :
    pullH (galA' hli hsp hA hA' hc τ1) (pullH (galA' hli hsp hA hA' hc τ2) w) =
      pullH (galA' hli hsp hA hA' hc (τ2 * τ1)) w := by
  apply HeightOneSpectrum.ext
  ext y
  have e : galA' hli hsp hA hA' hc (τ2 * τ1) y =
      galA' hli hsp hA hA' hc τ2 (galA' hli hsp hA hA' hc τ1 y) :=
    DFunLike.congr_fun ((galA'Hom hli hsp hA hA' hc).map_mul τ2 τ1) y
  show galA' hli hsp hA hA' hc τ2 (galA' hli hsp hA hA' hc τ1 y) ∈ w.asIdeal ↔
    galA' hli hsp hA hA' hc (τ2 * τ1) y ∈ w.asIdeal
  rw [e]

theorem pullH_one (w : HeightOneSpectrum A') : pullH (galA' hli hsp hA hA' hc 1) w = w := by
  apply HeightOneSpectrum.ext
  ext y
  have e : galA' hli hsp hA hA' hc 1 y = y := DFunLike.congr_fun (galA'Hom hli hsp hA hA' hc).map_one y
  show galA' hli hsp hA hA' hc 1 y ∈ w.asIdeal ↔ y ∈ w.asIdeal
  rw [e]

/-- `w ↦ τ⁻¹ w` as a bijection of places. -/
noncomputable def plEquiv (τ : L ≃ₐ[Fq] L) : HeightOneSpectrum A' ≃ HeightOneSpectrum A' where
  toFun := pullH (galA' hli hsp hA hA' hc τ)
  invFun := pullH (galA' hli hsp hA hA' hc τ⁻¹)
  left_inv w := by
    show pullH _ (pullH _ w) = w
    rw [pullH_pullH, mul_inv_cancel, pullH_one]
  right_inv w := by
    show pullH _ (pullH _ w) = w
    rw [pullH_pullH, inv_mul_cancel, pullH_one]

theorem plEquiv_apply (τ : L ≃ₐ[Fq] L) (w : HeightOneSpectrum A') :
    plEquiv hli hsp hA hA' hc τ w = pullH (galA' hli hsp hA hA' hc τ) w := rfl

/-- **Transitivity**: places with the same contraction are `Gal(L/Fq)`-conjugate. -/
theorem exists_pullH_of_cont_eq (w1 w2 : HeightOneSpectrum A')
    (h : cont hli hsp hA hA' hc w1 = cont hli hsp hA hA' hc w2) :
    ∃ τ : L ≃ₐ[Fq] L, w2 = pullH (galA' hli hsp hA hA' hc τ) w1 :=
  exists_pullH_of_under_eq hli hsp hA hA' hc w1 w2 (congrArg HeightOneSpectrum.asIdeal h)

end PairPlaces

end RamanujanPetersson.PicDescent


end

-- ===== S4.Def_RP_PicDescent_D4b =====
section

/-!
# S4-PicDescent, part D4b: contraction of places for a constant field extension

For `h : RR.IsConstExt Fq F L F' c`: the ring pairs `Rfin(F) → Rfin(F')`, `Rinf(F) → Rinf(F')` (`algFin`, `algInf`,
towers), `contract : Place L F' → Place Fq F`, `ord_contract` (orders agree), the finite fibres `fibre h P`
(`mem_fibre`), `sum_deg_fibre` (`Σ_{P' | P} deg_L P' = deg P`), `exists_contract_eq`,
the Galois action on places `plE h τ` with `contract_plE`, `ord_plE`, `exists_plE_of_contract_eq`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Polynomial
open IsDedekindDomain Polynomial

namespace RamanujanPetersson.PicDescent

open Places

section ConstPlaces

variable {Fq : Type*} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type*} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable {L : Type*} [Field L] [Fintype L] [Algebra Fq L] [DecidableEq (RatFunc L)]
variable {F' : Type*} [Field F'] [Algebra L F'] [Algebra L[X] F'] [Algebra (RatFunc L) F']
  [IsScalarTower L[X] (RatFunc L) F'] [IsScalarTower L L[X] F'] [FunctionField L F']
  [Algebra.IsSeparable (RatFunc L) F']
variable [Algebra F F'] [Algebra Fq F'] [IsScalarTower Fq F F'] [IsScalarTower Fq L F']
variable {ι : Type*} [Fintype ι] {c : Module.Basis ι Fq L}
variable (h : RR.IsConstExt Fq F L F' c)

variable (Fq F) in
theorem injFin : Function.Injective (algebraMap (Rfin Fq F) F) := Subtype.val_injective

variable (Fq F) in
theorem injInf : Function.Injective (algebraMap (Rinf Fq F) F) := Subtype.val_injective

/-- `Rfin(F) → Rfin(F')`. -/
noncomputable def algFin : Algebra (Rfin Fq F) (Rfin L F') :=
  (toA' h.linearIndependent h.span (injFin Fq F) (injFin L F') h.fin).toAlgebra

/-- `Rinf(F) → Rinf(F')`. -/
noncomputable def algInf : Algebra (Rinf Fq F) (Rinf L F') :=
  (toA' h.linearIndependent h.span (injInf Fq F) (injInf L F') h.inf).toAlgebra

theorem towerFin : letI := algFin h; IsScalarTower (Rfin Fq F) (Rfin L F') F' := by
  letI := algFin h
  refine IsScalarTower.of_algebraMap_eq fun a => ?_
  rw [IsScalarTower.algebraMap_apply (Rfin Fq F) F F' a]
  exact (algebraMap_toA' h.linearIndependent h.span (injFin Fq F) (injFin L F') h.fin a).symm

theorem towerInf : letI := algInf h; IsScalarTower (Rinf Fq F) (Rinf L F') F' := by
  letI := algInf h
  refine IsScalarTower.of_algebraMap_eq fun a => ?_
  rw [IsScalarTower.algebraMap_apply (Rinf Fq F) F F' a]
  exact (algebraMap_toA' h.linearIndependent h.span (injInf Fq F) (injInf L F') h.inf a).symm

/-- Contraction of finite places. -/
noncomputable def contFin (w : HeightOneSpectrum (Rfin L F')) : HeightOneSpectrum (Rfin Fq F) :=
  letI := algFin h; haveI := towerFin h
  cont h.linearIndependent h.span (injFin Fq F) (injFin L F') h.fin w

/-- Contraction of places over `∞`. -/
noncomputable def contInf (w : HeightOneSpectrum (Rinf L F')) : HeightOneSpectrum (Rinf Fq F) :=
  letI := algInf h; haveI := towerInf h
  cont h.linearIndependent h.span (injInf Fq F) (injInf L F') h.inf w

/-- **Contraction** `P' ↦ P' ∩ F`. -/
noncomputable def contract : Place L F' → Place Fq F := Sum.map (contFin h) (contInf h)

/-- **Orders agree**: `ord_{P' ∩ F} f = ord_{P'} f`. -/
theorem ord_contract (P' : Place L F') (f : F) : (contract h P').ord f = P'.ord (algebraMap F F' f) := by
  rcases P' with w | w
  · letI := algFin h; haveI := towerFin h
    exact ord_cont h.linearIndependent h.span (injFin Fq F) (injFin L F') h.fin w f
  · letI := algInf h; haveI := towerInf h
    exact ord_cont h.linearIndependent h.span (injInf Fq F) (injInf L F') h.inf w f

theorem finite_contFin (v : HeightOneSpectrum (Rfin Fq F)) : {w | contFin h w = v}.Finite := by
  letI := algFin h; haveI := towerFin h
  exact finite_cont h.linearIndependent h.span (injFin Fq F) (injFin L F') h.fin v

theorem finite_contInf (v : HeightOneSpectrum (Rinf Fq F)) : {w | contInf h w = v}.Finite := by
  letI := algInf h; haveI := towerInf h
  exact finite_cont h.linearIndependent h.span (injInf Fq F) (injInf L F') h.inf v

/-- The places of `F'` over `P`. -/
noncomputable def fibre : Place Fq F → Finset (Place L F') :=
  Sum.elim (fun v => (finite_contFin h v).toFinset.map Function.Embedding.inl)
    (fun v => (finite_contInf h v).toFinset.map Function.Embedding.inr)

theorem mem_fibre (P : Place Fq F) (P' : Place L F') : P' ∈ fibre h P ↔ contract h P' = P := by
  rcases P with v | v <;> rcases P' with w | w <;>
    simp [fibre, contract, Set.Finite.mem_toFinset]

theorem exists_contract_eq (P : Place Fq F) : ∃ P' : Place L F', contract h P' = P := by
  rcases P with v | v
  · letI := algFin h; haveI := towerFin h
    obtain ⟨w, hw⟩ := exists_cont_eq h.linearIndependent h.span (injFin Fq F) (injFin L F') h.fin v
    exact ⟨Sum.inl w, congrArg Sum.inl hw⟩
  · letI := algInf h; haveI := towerInf h
    obtain ⟨w, hw⟩ := exists_cont_eq h.linearIndependent h.span (injInf Fq F) (injInf L F') h.inf v
    exact ⟨Sum.inr w, congrArg Sum.inr hw⟩

/-- **`Σ_{P' | P} deg_L P' = deg P`**. -/
theorem sum_deg_fibre (P : Place Fq F) : ∑ P' ∈ fibre h P, P'.deg = P.deg := by
  rcases P with v | v
  · letI := algFin h; haveI := towerFin h
    simp only [fibre, Sum.elim_inl, Finset.sum_map, Function.Embedding.inl_apply, Place.deg_inl]
    exact sum_deg_cont h.linearIndependent h.span (injFin Fq F) (injFin L F') h.fin v
  · letI := algInf h; haveI := towerInf h
    simp only [fibre, Sum.elim_inr, Finset.sum_map, Function.Embedding.inr_apply, Place.deg_inr]
    exact sum_deg_cont h.linearIndependent h.span (injInf Fq F) (injInf L F') h.inf v

/-- `Gal(L/Fq)` acting on the places of `F'`: `P' ↦ τ⁻¹ P'`. -/
noncomputable def plE (τ : L ≃ₐ[Fq] L) : Place L F' ≃ Place L F' :=
  letI := algFin h; haveI := towerFin h; letI := algInf h; haveI := towerInf h
  Equiv.sumCongr (plEquiv h.linearIndependent h.span (injFin Fq F) (injFin L F') h.fin τ)
    (plEquiv h.linearIndependent h.span (injInf Fq F) (injInf L F') h.inf τ)

theorem contract_plE (τ : L ≃ₐ[Fq] L) (P' : Place L F') : contract h (plE h τ P') = contract h P' := by
  rcases P' with w | w
  · letI := algFin h; haveI := towerFin h
    exact congrArg Sum.inl (cont_pullH h.linearIndependent h.span (injFin Fq F) (injFin L F') h.fin τ w)
  · letI := algInf h; haveI := towerInf h
    exact congrArg Sum.inr (cont_pullH h.linearIndependent h.span (injInf Fq F) (injInf L F') h.inf τ w)

/-- **Transport of orders**: `ord_{τ⁻¹ P'} f = ord_{P'} (gal τ f)`. -/
theorem ord_plE (τ : L ≃ₐ[Fq] L) (P' : Place L F') (f : F') :
    (plE h τ P').ord f = P'.ord (gal h.linearIndependent h.span τ f) := by
  rcases P' with w | w
  · letI := algFin h; haveI := towerFin h
    exact ord_pullH h.linearIndependent h.span (injFin Fq F) (injFin L F') h.fin τ w f
  · letI := algInf h; haveI := towerInf h
    exact ord_pullH h.linearIndependent h.span (injInf Fq F) (injInf L F') h.inf τ w f

/-- **Transitivity on fibres.** -/
theorem exists_plE_of_contract_eq (P1 P2 : Place L F') (h12 : contract h P1 = contract h P2) :
    ∃ τ : L ≃ₐ[Fq] L, P2 = plE h τ P1 := by
  rcases P1 with w1 | w1 <;> rcases P2 with w2 | w2
  · letI := algFin h; haveI := towerFin h
    obtain ⟨τ, hτ⟩ := exists_pullH_of_cont_eq h.linearIndependent h.span (injFin Fq F) (injFin L F') h.fin
      w1 w2 (Sum.inl_injective h12)
    exact ⟨τ, congrArg Sum.inl hτ⟩
  · exact absurd h12 Sum.inl_ne_inr
  · exact absurd h12 Sum.inr_ne_inl
  · letI := algInf h; haveI := towerInf h
    obtain ⟨τ, hτ⟩ := exists_pullH_of_cont_eq h.linearIndependent h.span (injInf Fq F) (injInf L F') h.inf
      w1 w2 (Sum.inr_injective h12)
    exact ⟨τ, congrArg Sum.inr hτ⟩

end ConstPlaces

end RamanujanPetersson.PicDescent


end

-- ===== S4.Def_RP_Kummer_Lev =====
section

/-!
# S4-Kummer, part K5b: Kummer roots at a constant level `F_m = F ⊗ 𝔽_{q^m}`

`A = Rfin(F)`, `K = F`, `F_m = Fc Fq F K̄ m ⊆ K̄ = AlgebraicClosure F`.

* `valuation_comap`: valuations are transported along a ring isomorphism of Dedekind domains that commutes with the maps to
  a common fraction field.
* `isIntegral_iff_mem_Rfin` (constant field extension `F'/F`): `x ∈ F'` is integral over `Rfin(F)` iff `x ∈ Rfin(F')`.
* `Fc_eq_constLevel`: `F_m = constLevel F p (e m)` when `#Fq = p ^ e`; `Fc_mem_unramSet`.
* `perfect_Rfin`: residue fields of `Rfin(F)` at maximal ideals are perfect (finite).
* `forall_dvd_ord_iff`: for `a ∈ F_m^×` and `N` invertible: `N ∣ ord_v a` at every finite place `v` of `F_m` iff every
  `N`-th root of `a` lies in `K_U = maxUnram (Rfin F) F`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open IsDedekindDomain
open scoped Polynomial

namespace RamanujanPetersson
namespace Kummer

noncomputable section

section Transport

variable {B1 B2 M : Type*} [CommRing B1] [IsDedekindDomain B1] [CommRing B2] [IsDedekindDomain B2]
  [Field M] [Algebra B1 M] [Algebra B2 M] [IsFractionRing B1 M] [IsFractionRing B2 M]

theorem intValuation_comap (e : B1 ≃+* B2) (w : HeightOneSpectrum B2) (b : B1) :
    (HeightOneSpectrum.comap (e : B1 →+* B2) e.surjective w).intValuation b = w.intValuation (e b) := by
  rcases eq_or_ne b 0 with rfl | hb
  · simp
  have heb : e b ≠ 0 := fun h => hb (e.injective (h.trans (map_zero e).symm))
  rw [HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity _ hb,
    HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity _ heb]
  congr 3
  apply multiplicity_eq_of_emultiplicity_eq
  rw [emultiplicity_eq_emultiplicity_iff]
  intro n
  have hpow : (HeightOneSpectrum.comap (e : B1 →+* B2) e.surjective w).asIdeal ^ n =
      (w.asIdeal ^ n).comap (e : B1 →+* B2) := by
    change (w.asIdeal.comap e) ^ n = (w.asIdeal ^ n).comap e
    rw [← Ideal.map_symm, ← Ideal.map_symm, Ideal.map_pow]
  rw [Ideal.dvd_iff_le, Ideal.dvd_iff_le, Ideal.span_le, Ideal.span_le, Set.singleton_subset_iff,
    Set.singleton_subset_iff, hpow]
  exact Iff.rfl

/-- **Transport of valuations** along `e : B1 ≃+* B2` compatible with the maps to `M`. -/
theorem valuation_comap (e : B1 ≃+* B2) (he : ∀ b, algebraMap B2 M (e b) = algebraMap B1 M b)
    (w : HeightOneSpectrum B2) (x : M) :
    (HeightOneSpectrum.comap (e : B1 →+* B2) e.surjective w).valuation M x = w.valuation M x := by
  obtain ⟨a, s, -, rfl⟩ := IsFractionRing.div_surjective (A := B1) x
  rw [map_div₀, map_div₀, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, intValuation_comap, intValuation_comap, ← he a, ← he s,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]

end Transport

section Generic

open PicDescent Places

variable {Fq : Type*} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type*} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable {L : Type*} [Field L] [Fintype L] [Algebra Fq L] [DecidableEq (RatFunc L)]
variable {F' : Type*} [Field F'] [Algebra L F'] [Algebra L[X] F'] [Algebra (RatFunc L) F']
  [IsScalarTower L[X] (RatFunc L) F'] [IsScalarTower L L[X] F'] [FunctionField L F']
  [Algebra.IsSeparable (RatFunc L) F']
variable [Algebra F F'] [Algebra Fq F'] [IsScalarTower Fq F F'] [IsScalarTower Fq L F']
variable {ι : Type*} [Fintype ι] {c : Module.Basis ι Fq L}

/-- In a constant field extension `F'/F`, the integral closure of `Rfin(F)` in `F'` is `Rfin(F')`. -/
theorem isIntegral_iff_mem_Rfin (h : RR.IsConstExt Fq F L F' c) (x : F') :
    IsIntegral (Rfin Fq F) x ↔ IsIntegral L[X] x := by
  constructor
  · intro hx
    letI := algFin h
    haveI := towerFin h
    refine isIntegral_of_forall_algebraMap (A := Rfin Fq F) (fun a => ?_) hx
    rw [IsScalarTower.algebraMap_apply (Rfin Fq F) (Rfin L F') F']
    exact (algebraMap (Rfin Fq F) (Rfin L F') a).2
  · intro hx
    letI := algFin h
    haveI := towerFin h
    haveI := isIntegral_AA' h.linearIndependent h.span (injFin Fq F) (injFin L F') h.fin
    exact (Algebra.IsIntegral.isIntegral (R := Rfin Fq F) (⟨x, hx⟩ : Rfin L F')).algebraMap

end Generic

section GenericLev

variable {K : Type} [Field K] (A : Type) [CommRing A] [IsDedekindDomain A] [Algebra A K] [IsFractionRing A K]

/-- Generic Kummer criterion at a finite level `M ∈ unramSet`, for any Dedekind model `B` of the integral closure of `A`
in `M` (given by its image in `M`). -/
theorem forall_dvd_iff_of_range {M : IntermediateField K (AlgebraicClosure K)} (hM : M ∈ unramSet A K)
    (hperf : ∀ (p : Ideal A) [p.IsMaximal], PerfectField p.ResidueField) {N : ℕ} [NeZero N] (hN : IsUnit (N : A))
    {a : M} (ha : a ≠ 0) {B : Type*} [CommRing B] [IsDedekindDomain B] [Algebra B M] [IsFractionRing B M]
    (hB : ∀ x : M, IsIntegral A x ↔ x ∈ (algebraMap B M).range) (hBinj : Function.Injective (algebraMap B M)) :
    (∀ v : HeightOneSpectrum B, (N : ℤ) ∣ WithZero.log (v.valuation M a)) ↔
      ∀ γ : AlgebraicClosure K, γ ^ N = (a : AlgebraicClosure K) → γ ∈ maxUnram A K := by
  haveI : FiniteDimensional K M := hM.1
  haveI : IsGalois K M := hM.2.1
  haveI : IsFractionRing (integralClosure A M) M := integralClosure.isFractionRing_of_finite_extension (A := A) K M
  haveI : IsDedekindDomain (integralClosure A M) := integralClosure.isDedekindDomain (A := A) (K := K) (L := M)
  have hrange : (integralClosure A M).toSubring = (algebraMap B M).range :=
    Subring.ext fun x => hB x
  let e1 : integralClosure A M ≃+* (algebraMap B M).range := RingEquiv.subringCongr hrange
  let e2 : B ≃+* (algebraMap B M).range := RingEquiv.ofBijective (algebraMap B M).rangeRestrict
    ⟨fun x y hxy => hBinj (congrArg Subtype.val hxy), RingHom.rangeRestrict_surjective _⟩
  let eR : integralClosure A M ≃+* B := e1.trans e2.symm
  have heR : ∀ x, algebraMap B M (eR x) = algebraMap (integralClosure A M) M x := fun x =>
    congrArg Subtype.val (e2.apply_symm_apply (e1 x))
  have heR' : ∀ b, algebraMap (integralClosure A M) M (eR.symm b) = algebraMap B M b := fun b => by
    rw [← heR, RingEquiv.apply_symm_apply]
  constructor
  · intro hv γ hγ
    refine root_mem_maxUnram_of_dvd A hM hN ha (fun v => ?_) hγ
    have h1 := hv (HeightOneSpectrum.comap (eR.symm : B →+* integralClosure A M) eR.symm.surjective v)
    rwa [valuation_comap eR.symm heR' v] at h1
  · intro hroot v
    obtain ⟨γ, hγ⟩ := IsAlgClosed.exists_pow_nat_eq (a : AlgebraicClosure K) (NeZero.pos N)
    have h1 := dvd_log_valuation_of_mem_maxUnram A hM hperf (hroot γ hγ) hγ
      (HeightOneSpectrum.comap (eR : integralClosure A M →+* B) eR.surjective v)
    rwa [valuation_comap eR heR v] at h1

end GenericLev

section Lev

open PicDescent Places

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (F : Type) [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

/-- Residue fields of `Rfin(F)` at maximal ideals are finite, hence perfect. -/
theorem perfect_Rfin : ∀ (P : Ideal (Rfin Fq F)) [P.IsMaximal], PerfectField P.ResidueField := by
  intro P hP
  have hne : P ≠ ⊥ := by
    rintro rfl
    have hfield : IsField (Rfin Fq F) := Ring.isField_iff_maximal_bot.2 hP
    have hinj : Function.Injective (algebraMap Fq[X] (Rfin Fq F)) := by
      intro a b hab
      apply FaithfulSMul.algebraMap_injective Fq[X] F
      rw [IsScalarTower.algebraMap_apply Fq[X] (Rfin Fq F) F, hab,
        ← IsScalarTower.algebraMap_apply Fq[X] (Rfin Fq F) F]
    exact Polynomial.not_isField Fq (isField_of_isIntegral_of_isField hinj hfield)
  obtain ⟨a, haP, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  haveI := Places.FiniteQuot.finite (S := Rfin Fq F) a ha0
  haveI : Finite (Rfin Fq F ⧸ P) :=
    Finite.of_surjective _ (Ideal.Quotient.factor_surjective ((Ideal.span_singleton_le_iff_mem _).mpr haP))
  haveI : Finite P.ResidueField :=
    Finite.of_surjective _ (Ideal.bijective_algebraMap_quotient_residueField P).2
  infer_instance

variable {Fq F} {p e : ℕ} [Fact p.Prime] [CharP F p]

/-- The constant level `F_m` is `constLevel F p (e m)` (with `#Fq = p ^ e`). -/
theorem Fc_eq_constLevel (hq : Fintype.card Fq = p ^ e) {m : ℕ} (hm : 0 < e * m) :
    Fc Fq F (AlgebraicClosure F) m = constLevel F p (e * m) := by
  have hS : ((Lc Fq (AlgebraicClosure F) m : IntermediateField Fq (AlgebraicClosure F)) : Set (AlgebraicClosure F)) =
      ((Polynomial.X : F[X]) ^ (p ^ (e * m)) - Polynomial.X).rootSet (AlgebraicClosure F) := by
    ext x
    rw [SetLike.mem_coe, mem_Lc, Polynomial.mem_rootSet, hq, ← pow_mul]
    simp only [map_sub, map_pow, Polynomial.aeval_X, sub_eq_zero]
    constructor
    · intro h
      exact ⟨FiniteField.X_pow_card_sub_X_ne_zero F (one_lt_pow_p (p := p) hm), h⟩
    · intro h
      exact h.2
  rw [Fc, constLevel, hS]

theorem Fc_mem_unramSet (hq : Fintype.card Fq = p ^ e) (he : 0 < e) (m : ℕ) [NeZero m] :
    Fc Fq F (AlgebraicClosure F) m ∈ unramSet (Rfin Fq F) F := by
  rw [Fc_eq_constLevel hq (Nat.mul_pos he (NeZero.pos m))]
  exact constLevel_mem_unramSet (Rfin Fq F) (Nat.mul_pos he (NeZero.pos m))

/-- **Kummer criterion at a constant level**: for `a ∈ F_m^×` and `N` invertible, `N` divides `ord_v a` at every finite
place `v` of `F_m` iff every `N`-th root of `a` lies in `K_U`. -/
theorem forall_dvd_ord_iff (hk : constField Fq F = ⊥) (hq : Fintype.card Fq = p ^ e) (he : 0 < e) (m : ℕ) [NeZero m]
    {N : ℕ} [NeZero N] (hN : IsUnit (N : Rfin Fq F)) {a : Fc Fq F (AlgebraicClosure F) m} (ha : a ≠ 0) :
    (∀ v : HeightOneSpectrum (Rfin (Lc Fq (AlgebraicClosure F) m) (Fc Fq F (AlgebraicClosure F) m)),
      (N : ℤ) ∣ Places.ord v a) ↔
    ∀ γ : AlgebraicClosure F, γ ^ N = (a : AlgebraicClosure F) → γ ∈ maxUnram (Rfin Fq F) F := by
  have hB : ∀ x : Fc Fq F (AlgebraicClosure F) m, IsIntegral (Rfin Fq F) x ↔
      x ∈ (algebraMap (Rfin (Lc Fq (AlgebraicClosure F) m) (Fc Fq F (AlgebraicClosure F) m))
        (Fc Fq F (AlgebraicClosure F) m)).range := by
    intro x
    refine (isIntegral_iff_mem_Rfin (isConstExt_Fc Fq F (AlgebraicClosure F) hk m) x).trans ⟨fun hx => ⟨⟨x, hx⟩, rfl⟩, ?_⟩
    rintro ⟨y, rfl⟩
    exact y.2
  refine (forall_congr' fun v => ?_).trans
    (forall_dvd_iff_of_range (Rfin Fq F) (Fc_mem_unramSet hq he m) (perfect_Rfin Fq F) hN ha hB Subtype.val_injective)
  rw [Places.ord]
  exact dvd_neg

end Lev

end

end Kummer
end RamanujanPetersson


end

-- ===== S4.Def_RP_Kummer_Inf =====
section

/-!
# S4-Kummer K5c: Kummer classes at the boundary (generic core)

`R0` is a chart of the boundary (for curves `R0 = Rinf`), `proChart A K R0` its integral closure in `K_U`.
* `mem_curveH1par_iff` (a): with trivial `ZMod N` coefficients, `kclass α ∈ H¹_par` iff `α` is fixed by the geometric
  boundary inertia `I_s ∩ π₁^geo`.
* `fixed_of_bdry_inertia` (b-core): an inertia element of the pro-chart fixing a finite level `M` fixes every `N`-th
  root of `a ∈ M` with `I^N (a) = 1` over `R0` (restriction to a finite level + `fixed_of_inertia`).
* `inertia_le_pi1geo`: boundary inertia fixes the constants (it lies in `π₁^geo`).
* `BdryLift` (explicit TRUE hypothesis: inertia groups surject under restriction) and `mem_maxUnram_of_fixed`
  (c-core): an element of `K_U` fixed by all boundary inertia lies in the maximal extension unramified over `R0`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Kummer

open CurveCoh IsDedekindDomain Polynomial
open scoped Pointwise

noncomputable section

theorem mem_Z1par_iff {k : Type} [CommRing k] {G : Type} [Group G] [TopologicalSpace G]
    {M : Type} [AddCommGroup M] [Module k M] (ρ : Representation k G M) (Γ : Subgroup G) {S : Type}
    (I : S → Subgroup G) (c : Γ → M) :
    c ∈ Z1par ρ Γ I ↔ c ∈ Z1 ρ Γ ∧ ∀ s : S, ∃ b : M, ∀ g : Γ, (g : G) ∈ I s → c g = ρ g b - b := Iff.rfl

/-! ## (a) Parabolic Kummer classes -/

section Par

variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {q N : ℕ} [NeZero N] {ζ : maxUnram A K}
  (hζ : IsPrimitiveRoot ζ N) (hζΓ : ∀ σ ∈ pi1geo A K q, σ ζ = ζ)
  {R0 : Type} [CommRing R0] [Algebra R0 K] {S : Type} (D : BdryData A K q R0 S)

include hζ hζΓ in
/-- **(a)** A Kummer class is parabolic iff `α` is fixed by the geometric boundary inertia. -/
theorem mem_curveH1par_iff {α : (maxUnram A K)ˣ} (hα : α ∈ rad (pi1geo A K q) N) :
    kclass hζ hζΓ hα ∈ curveH1par q (triv K (maxUnram A K) N) D ↔
      ∀ s, ∀ g ∈ pi1geo A K q, g ∈ D.inertia s → g (α : maxUnram A K) = α := by
  have key : ∀ g : pi1geo A K q, kchar hζ α g = 0 ↔ (g : Pi1 A K) (α : maxUnram A K) = α := fun g => by
    rw [kchar_eq_iff hζ hα g 0, epow_zero, one_mul]
  rw [curveH1par, H1par, Submodule.mem_map]
  constructor
  · rintro ⟨c, hc, hce⟩ s g hg hgs
    have hc' : c = ⟨kchar hζ α, kchar_mem_Z1 hζ hζΓ hα⟩ := H1mk_triv_injective N (pi1geo A K q) hce
    subst hc'
    rw [Submodule.mem_comap, Submodule.subtype_apply, mem_Z1par_iff] at hc
    obtain ⟨b, hb⟩ := hc.2 s
    have h0 : kchar hζ α ⟨g, hg⟩ = 0 := by simpa [triv] using hb ⟨g, hg⟩ hgs
    exact (key ⟨g, hg⟩).1 h0
  · intro h
    refine ⟨⟨kchar hζ α, kchar_mem_Z1 hζ hζΓ hα⟩, ?_, rfl⟩
    rw [Submodule.mem_comap, Submodule.subtype_apply, mem_Z1par_iff]
    refine ⟨kchar_mem_Z1 hζ hζΓ hα, fun s => ⟨0, fun g hgs => ?_⟩⟩
    simp only [triv, Representation.trivial_apply, sub_self]
    exact (key g).2 (h s g g.2 hgs)

end Par

/-! ## Restriction of pro-chart inertia to finite levels -/

section Chart

variable {A K : Type} [CommRing A] [Field K] [Algebra A K] (R0 : Type) [CommRing R0] [Algebra R0 K]

/-- The integral closure of `R0` in a finite level `L ≤ K_U`, mapped into the pro-chart. -/
def inclU {L : IntermediateField K (AlgebraicClosure K)} (hLU : L ≤ maxUnram A K) :
    integralClosure R0 L →ₐ[R0] proChart A K R0 :=
  ((IntermediateField.inclusion hLU).restrictScalars R0).mapIntegralClosure

variable {R0}

theorem exists_restrict {L : IntermediateField K (AlgebraicClosure K)} (hLU : L ≤ maxUnram A K) [Normal K L]
    (g : Pi1 A K) : ∃ τ : L ≃ₐ[K] L, ∀ y : L, ((τ y : L) : AlgebraicClosure K) =
      ((g (IntermediateField.inclusion hLU y) : maxUnram A K) : AlgebraicClosure K) := by
  letI : Algebra L (maxUnram A K) := (IntermediateField.inclusion hLU).toAlgebra
  haveI : IsScalarTower K L (maxUnram A K) := IsScalarTower.of_algHom (IntermediateField.inclusion hLU)
  exact ⟨g.restrictNormal L, fun y => congrArg Subtype.val (AlgEquiv.restrictNormal_commutes g L y)⟩

theorem restrict_mem_inertia {L : IntermediateField K (AlgebraicClosure K)} (hLU : L ≤ maxUnram A K)
    {P : Ideal (proChart A K R0)} {g : Pi1 A K} (hg : g ∈ P.inertia (Pi1 A K)) {τ : L ≃ₐ[K] L}
    (hτ : ∀ y : L, ((τ y : L) : AlgebraicClosure K) =
      ((g (IntermediateField.inclusion hLU y) : maxUnram A K) : AlgebraicClosure K)) :
    τ ∈ (P.comap (inclU R0 hLU)).inertia (L ≃ₐ[K] L) := by
  refine AddSubgroup.mem_inertia.2 fun y => ?_
  have h : g • inclU R0 hLU y - inclU R0 hLU y ∈ P := AddSubgroup.mem_inertia.1 hg (inclU R0 hLU y)
  show inclU R0 hLU (τ • y - y) ∈ P
  convert h using 1
  apply Subtype.ext; apply Subtype.ext
  show ((τ (y : L) : L) : AlgebraicClosure K) - ((y : L) : AlgebraicClosure K) =
    ((g ((inclU R0 hLU y : proChart A K R0) : maxUnram A K) : maxUnram A K) : AlgebraicClosure K) -
      ((y : L) : AlgebraicClosure K)
  rw [hτ]
  rfl

/-- **(b-core)** A pro-chart inertia element fixing the finite level `M ∈ unramSet A K` fixes every `α ∈ K_U` with
`α ^ N = a ∈ M`, when `I ^ N (a) = 1` for a fractional ideal `I` of `R0`'s integral closure in `M`. -/
theorem fixed_of_bdry_inertia {M : IntermediateField K (AlgebraicClosure K)} (hM : M ∈ unramSet A K)
    [IsFractionRing (integralClosure R0 M) M] {N : ℕ} [NeZero N] (hN : IsUnit (N : R0))
    {P : Ideal (proChart A K R0)} [P.IsPrime] {g : Pi1 A K} (hg : g ∈ P.inertia (Pi1 A K))
    (hgM : ∀ x : maxUnram A K, (x : AlgebraicClosure K) ∈ M → g x = x) {a : M}
    (I : FractionalIdeal (nonZeroDivisors (integralClosure R0 M)) M)
    (hI : I ^ N * FractionalIdeal.spanSingleton _ a = 1)
    (α : maxUnram A K) (hα : (α : AlgebraicClosure K) ^ N = a) : g α = α := by
  obtain ⟨L1, hL1, hle1⟩ := exists_unramSet_of_finite A K {(α : AlgebraicClosure K)} (by
    intro x hx
    rw [Finset.mem_singleton] at hx
    rw [hx]
    exact α.2)
  have hL : L1 ⊔ M ∈ unramSet A K := sup_mem_unramSet A K hL1 hM
  have hLU : L1 ⊔ M ≤ maxUnram A K := by
    rw [maxUnram_eq_sSup]
    exact le_sSup hL
  haveI : IsGalois K ↥(L1 ⊔ M) := hL.2.1
  have hML : M ≤ L1 ⊔ M := le_sup_right
  obtain ⟨τ, hτ⟩ := exists_restrict hLU g
  have hτI := restrict_mem_inertia hLU hg hτ
  haveI : (P.comap (inclU R0 hLU)).IsPrime := Ideal.IsPrime.comap _
  have hτM : ∀ x : M, τ (IntermediateField.inclusion hML x) = IntermediateField.inclusion hML x := by
    intro x
    apply Subtype.ext
    rw [hτ]
    exact congrArg Subtype.val (hgM ⟨x, hLU (hML x.2)⟩ x.2)
  have hαL : (α : AlgebraicClosure K) ∈ L1 ⊔ M :=
    (le_sup_left : L1 ≤ L1 ⊔ M) (hle1 (IntermediateField.subset_adjoin K _ (by simp)))
  have hpow : (⟨α, hαL⟩ : ↥(L1 ⊔ M)) ^ N = IntermediateField.inclusion hML a :=
    Subtype.ext (by simpa using hα)
  have hfix := fixed_of_inertia hML hN (P.comap (inclU R0 hLU)) τ hτI hτM I hI ⟨α, hαL⟩ hpow
  have h2 := hτ ⟨α, hαL⟩
  rw [hfix] at h2
  exact Subtype.ext h2.symm

/-- Boundary inertia fixes the constants: it lies in `π₁^geo` (`q = p ^ e`). -/
theorem inertia_le_pi1geo {p e : ℕ} [hp : Fact p.Prime] [CharP K p] (he : 0 < e) {q : ℕ} (hq : q = p ^ e)
    {P : Ideal (proChart A K R0)} [hP : P.IsPrime] {g : Pi1 A K} (hg : g ∈ P.inertia (Pi1 A K)) :
    g ∈ pi1geo A K q := by
  subst hq
  haveI : CharP (maxUnram A K) p := charP_of_injective_algebraMap (algebraMap K (maxUnram A K)).injective p
  rw [mem_pi1geo]
  rintro y ⟨n, hn, hyn⟩
  have hk : 0 < e * n := Nat.mul_pos he hn
  have hn1 : 1 < p ^ (e * n) := one_lt_pow_p (p := p) hk
  have hyp : y ^ (p ^ (e * n)) = y := by rw [pow_mul]; exact hyn
  have hint : IsIntegral R0 y := by
    by_cases h0 : y = 0
    · rw [h0]
      exact isIntegral_zero
    · refine IsIntegral.of_pow (by omega : 0 < p ^ (e * n) - 1) ?_
      rw [pow_pred_eq_one hn1.le hyp h0]
      exact isIntegral_one
  let yA : proChart A K R0 := ⟨y, hint⟩
  have hd : g • yA - yA ∈ P := AddSubgroup.mem_inertia.1 hg yA
  have hdval : ((g • yA - yA : proChart A K R0) : maxUnram A K) = g y - y := rfl
  by_contra hne
  have hd0 : g y - y ≠ 0 := sub_ne_zero.2 hne
  have hdp : (g y - y) ^ (p ^ (e * n)) = g y - y := by
    rw [sub_pow_char_pow, ← map_pow, hyp]
  have h1 : (g • yA - yA) ^ (p ^ (e * n) - 1) ∈ P := Ideal.pow_mem_of_mem P hd _ (by omega)
  have h1' : (g • yA - yA) ^ (p ^ (e * n) - 1) = 1 := by
    apply Subtype.val_injective
    change ((g • yA - yA : proChart A K R0) : maxUnram A K) ^ (p ^ (e * n) - 1) = 1
    rw [hdval, pow_pred_eq_one hn1.le hdp hd0]
  rw [h1'] at h1
  exact hP.ne_top ((Ideal.eq_top_iff_one P).2 h1)

/-- The inertia group of the zero ideal is trivial (the integral closure generates `E`). -/
theorem eq_one_of_mem_inertia_bot {E : IntermediateField K (AlgebraicClosure K)}
    [IsFractionRing (integralClosure R0 E) E] {τ : E ≃ₐ[K] E}
    (hτ : τ ∈ (⊥ : Ideal (integralClosure R0 E)).inertia (E ≃ₐ[K] E)) : τ = 1 := by
  have hfix : ∀ y : integralClosure R0 E, τ (y : E) = y := fun y => by
    have h' : τ • y - y ∈ (⊥ : Ideal (integralClosure R0 E)) := AddSubgroup.mem_inertia.1 hτ y
    rw [Ideal.mem_bot] at h'
    exact congrArg Subtype.val (sub_eq_zero.1 h')
  refine AlgEquiv.ext fun x => ?_
  obtain ⟨y, d, -, rfl⟩ := IsFractionRing.div_surjective (A := integralClosure R0 E) x
  rw [AlgEquiv.one_apply, map_div₀]
  exact congrArg₂ (· / ·) (hfix y) (hfix d)

variable (A K R0) in
/-- **Inertia lifting** at the chart `R0` (explicit TRUE hypothesis: inertia groups surject under restriction, as in
`CurveCoh.InertiaLift`): an inertia element of a finite Galois level `L ≤ K_U` at a nonzero prime of `R0`'s integral
closure is the restriction of an inertia element of a boundary prime of the pro-chart. -/
def BdryLift : Prop :=
  ∀ (L : IntermediateField K (AlgebraicClosure K)) (hLU : L ≤ maxUnram A K), FiniteDimensional K L →
    IsGalois K L → ∀ Q : Ideal (integralClosure R0 L), Q.IsPrime → Q ≠ ⊥ → ∀ τ ∈ Q.inertia (L ≃ₐ[K] L),
      ∃ P : Ideal (proChart A K R0), IsBdryPrime A K R0 P ∧ ∃ g ∈ P.inertia (Pi1 A K), ∀ y : L,
        ((τ y : L) : AlgebraicClosure K) = ((g (IntermediateField.inclusion hLU y) : maxUnram A K) : AlgebraicClosure K)

/-- **(c-core)** An element of `K_U` fixed by the inertia of every boundary prime of the pro-chart lies in the maximal
extension unramified over `R0` (the normal closure of `K(α)` is unramified over `R0`, by `BdryLift`). -/
theorem mem_maxUnram_of_fixed [IsDomain R0] [IsFractionRing R0 K] (hlift : BdryLift A K R0) (α : maxUnram A K)
    (hfix : ∀ P : Ideal (proChart A K R0), IsBdryPrime A K R0 P → ∀ g ∈ P.inertia (Pi1 A K), g α = α) :
    (α : AlgebraicClosure K) ∈ maxUnram R0 K := by
  have hconj : ∀ σ : Pi1 A K, ∀ P : Ideal (proChart A K R0), IsBdryPrime A K R0 P →
      ∀ g ∈ P.inertia (Pi1 A K), g (σ α) = σ α := by
    intro σ P hP g hg
    have h2 := hfix _ (isBdryPrime_smul A K R0 σ⁻¹ hP) _ (conj_mem_inertia_smul A K R0 σ⁻¹ hg)
    simp only [AlgEquiv.mul_apply, inv_inv] at h2
    have h3 := congrArg σ h2
    rwa [← AlgEquiv.mul_apply σ σ⁻¹, mul_inv_cancel, AlgEquiv.one_apply] at h3
  have haint : IsIntegral K (α : AlgebraicClosure K) := Algebra.IsIntegral.isIntegral _
  set P0 := minpoly K (α : AlgebraicClosure K) with hP0
  have hsep : P0.Separable := by
    rw [hP0, ← IntermediateField.minpoly_eq]
    exact Algebra.IsSeparable.isSeparable K α
  have hroot : ∀ y ∈ P0.rootSet (AlgebraicClosure K), ∃ σ : Pi1 A K,
      ((σ α : maxUnram A K) : AlgebraicClosure K) = y := by
    intro y hy
    have hy0 : aeval y P0 = 0 := (mem_rootSet.1 hy).2
    have hsplit : ((minpoly K α).map (algebraMap K (maxUnram A K))).Splits := Normal.splits inferInstance α
    rw [IntermediateField.minpoly_eq] at hsplit
    have hmem : y ∈ maxUnram A K := (IntermediateField.splits_iff_mem (IsAlgClosed.splits _)).1 hsplit _ hy
    have hmin : minpoly K (⟨y, hmem⟩ : maxUnram A K) = minpoly K α := by
      rw [IntermediateField.minpoly_eq, IntermediateField.minpoly_eq]
      exact (minpoly.eq_of_irreducible_of_monic (minpoly.irreducible haint) hy0 (minpoly.monic haint)).symm
    obtain ⟨σ, hσ⟩ := MulAction.mem_orbit_iff.1
      ((Normal.minpoly_eq_iff_mem_orbit (F := K) (E := ↥(maxUnram A K))).1 hmin)
    exact ⟨σ, by rw [← AlgEquiv.smul_def, hσ]⟩
  set E : IntermediateField K (AlgebraicClosure K) := IntermediateField.adjoin K (P0.rootSet (AlgebraicClosure K))
    with hEdef
  have hspl : IsSplittingField K E P0 := IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)
  have : FiniteDimensional K E := IsSplittingField.finiteDimensional E P0
  have : IsGalois K E := IsGalois.of_separable_splitting_field hsep
  have hEU : E ≤ maxUnram A K := by
    rw [hEdef, IntermediateField.adjoin_le_iff]
    intro y hy
    obtain ⟨σ, hσ⟩ := hroot y hy
    rw [← hσ]
    exact (σ α).2
  have hE : E ∈ unramSet R0 K := by
    refine ⟨inferInstance, inferInstance, fun Q hQ => ?_⟩
    rw [eq_bot_iff]
    intro τ hτ
    rw [Subgroup.mem_bot]
    by_cases hQ0 : Q = ⊥
    · subst hQ0
      haveI : IsFractionRing (integralClosure R0 E) E :=
        integralClosure.isFractionRing_of_finite_extension (A := R0) K E
      exact eq_one_of_mem_inertia_bot hτ
    · obtain ⟨P, hP, g, hg, hgτ⟩ := hlift E hEU inferInstance inferInstance Q hQ hQ0 τ hτ
      obtain ⟨σ', hσ'⟩ : ∃ σ' : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, ∀ y : E,
          σ' (y : AlgebraicClosure K) = ((τ y : E) : AlgebraicClosure K) :=
        ⟨τ.liftNormal (AlgebraicClosure K), fun y => τ.liftNormal_commutes (AlgebraicClosure K) y⟩
      have hσE : σ' ∈ E.fixingSubgroup := by
        apply mem_fixingSubgroup_adjoin
        intro y hy
        obtain ⟨σ, hσ⟩ := hroot y hy
        have hyE : y ∈ E := IntermediateField.subset_adjoin K _ hy
        have h2 : IntermediateField.inclusion hEU ⟨y, hyE⟩ = σ α := Subtype.ext hσ.symm
        calc σ' y = ((τ ⟨y, hyE⟩ : E) : AlgebraicClosure K) := hσ' ⟨y, hyE⟩
          _ = ((g (IntermediateField.inclusion hEU ⟨y, hyE⟩) : maxUnram A K) : AlgebraicClosure K) :=
              hgτ ⟨y, hyE⟩
          _ = y := by rw [h2, hconj σ P hP g hg]; exact hσ
      ext y
      rw [AlgEquiv.one_apply, ← hσ']
      exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσE _ y.2
  have hαE : (α : AlgebraicClosure K) ∈ E :=
    IntermediateField.subset_adjoin K _ (mem_rootSet.2 ⟨minpoly.ne_zero haint, minpoly.aeval K _⟩)
  exact le_iSup (fun L : unramSet R0 K => (L : IntermediateField K (AlgebraicClosure K))) ⟨E, hE⟩ hαE

end Chart

end

end Kummer
end RamanujanPetersson


end

-- ===== S4.Def_RP_CP4a_Res =====
section

/-!
# S4-CP4a, part e1: residues of boundary primes of the pro-chart are constants

For a nonzero prime `Q` of the pro-chart `B = proChart A K R0` with finite residue ring `R0 ⧸ (Q ∩ R0)` of order a
power of `q = p^e`, and assuming `K_U` contains primitive `(q^a - 1)`-th roots of unity for every `a ≥ 1`:

* `constSub`: the constants of `K_U` that lie in `B` form a subring;
* `const_eq_of_sub_mem`: two constants congruent mod a proper ideal are equal;
* `exists_const_sub_mem`: every element of `B` is congruent mod `Q` to a constant;
* `resEquiv`: so `constSub ≃+* B ⧸ Q`.
-/

set_option autoImplicit false

open Polynomial

namespace RamanujanPetersson.CP4a

open CurveCoh GalCover Kummer

noncomputable section

theorem isConst_pow_mul {L : Type} [Monoid L] {x : L} {Q n : ℕ} (h : x ^ Q ^ n = x) (k : ℕ) :
    x ^ Q ^ (n * k) = x := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, h]

section Field

variable {L : Type} [Field L] {p : ℕ} [Fact p.Prime] [CharP L p] (e : ℕ)

theorem isConst_common {x y : L} (hx : IsConst (p ^ e) x) (hy : IsConst (p ^ e) y) :
    ∃ n, 0 < n ∧ x ^ p ^ (e * n) = x ∧ y ^ p ^ (e * n) = y := by
  obtain ⟨n, hn, hx⟩ := hx
  obtain ⟨m, hm, hy⟩ := hy
  refine ⟨n * m, Nat.mul_pos hn hm, ?_, ?_⟩
  · rw [pow_mul]; exact isConst_pow_mul hx m
  · rw [pow_mul, mul_comm n m]; exact isConst_pow_mul hy n

theorem IsConst.add' {x y : L} (hx : IsConst (p ^ e) x) (hy : IsConst (p ^ e) y) : IsConst (p ^ e) (x + y) := by
  obtain ⟨n, hn, h1, h2⟩ := isConst_common e hx hy
  exact ⟨n, hn, by rw [← pow_mul, add_pow_char_pow, h1, h2]⟩

theorem IsConst.sub' {x y : L} (hx : IsConst (p ^ e) x) (hy : IsConst (p ^ e) y) : IsConst (p ^ e) (x - y) := by
  obtain ⟨n, hn, h1, h2⟩ := isConst_common e hx hy
  exact ⟨n, hn, by rw [← pow_mul, sub_pow_char_pow, h1, h2]⟩

theorem IsConst.mul' {x y : L} (hx : IsConst (p ^ e) x) (hy : IsConst (p ^ e) y) : IsConst (p ^ e) (x * y) := by
  obtain ⟨n, hn, h1, h2⟩ := isConst_common e hx hy
  exact ⟨n, hn, by rw [← pow_mul, mul_pow, h1, h2]⟩

theorem isConst_one : IsConst (p ^ e) (1 : L) := ⟨1, one_pos, one_pow _⟩

theorem isConst_zero : IsConst (p ^ e) (0 : L) :=
  ⟨1, one_pos, zero_pow (pow_ne_zero _ (pow_ne_zero _ (Fact.out : p.Prime).ne_zero))⟩

end Field

section Res

variable (A K : Type) [CommRing A] [Field K] [Algebra A K]
  (R0 : Type) [CommRing R0] [Algebra R0 K] [Algebra R0 (maxUnram A K)] [IsScalarTower R0 K (maxUnram A K)]
  (p e : ℕ) [hp : Fact p.Prime] [CharP K p]

theorem charP_maxUnram : CharP (maxUnram A K) p :=
  charP_of_injective_algebraMap (algebraMap K (maxUnram A K)).injective p

/-- The constants of `K_U` lying in the pro-chart. -/
def constSub : Subring (proChart A K R0) :=
  haveI := charP_maxUnram A K p
  { carrier := {x | IsConst (p ^ e) (x : maxUnram A K)}
    mul_mem' := fun {x y} hx hy => IsConst.mul' e hx hy
    one_mem' := isConst_one e
    add_mem' := fun {x y} hx hy => IsConst.add' e hx hy
    zero_mem' := isConst_zero e
    neg_mem' := fun {x} hx => by
      have h := IsConst.sub' e (isConst_zero e) hx
      simpa using h }

variable {A K R0 p e}

theorem mem_constSub {x : proChart A K R0} : x ∈ constSub A K R0 p e ↔ IsConst (p ^ e) (x : maxUnram A K) :=
  Iff.rfl

/-- Constants are integral over any chart. -/
theorem isIntegral_of_isConst (he : 0 < e) {y : maxUnram A K} (hy : IsConst (p ^ e) y) : IsIntegral R0 y := by
  obtain ⟨n, hn, hyn⟩ := hy
  have hn1 : 1 < p ^ (e * n) := one_lt_pow_p (p := p) (Nat.mul_pos he hn)
  have hyp : y ^ (p ^ (e * n)) = y := by rw [pow_mul]; exact hyn
  by_cases h0 : y = 0
  · rw [h0]; exact isIntegral_zero
  · refine IsIntegral.of_pow (by omega : 0 < p ^ (e * n) - 1) ?_
    rw [pow_pred_eq_one hn1.le hyp h0]
    exact isIntegral_one

/-- A constant as an element of the pro-chart. -/
def mkConst (he : 0 < e) (y : maxUnram A K) (hy : IsConst (p ^ e) y) : proChart A K R0 :=
  ⟨y, isIntegral_of_isConst he hy⟩

theorem mkConst_mem (he : 0 < e) (y : maxUnram A K) (hy : IsConst (p ^ e) y) :
    mkConst (R0 := R0) he y hy ∈ constSub A K R0 p e := hy

/-- Two constants congruent modulo a proper ideal of the pro-chart are equal. -/
theorem const_eq_of_sub_mem (he : 0 < e) {Q : Ideal (proChart A K R0)} (hQ : Q ≠ ⊤) {c c' : proChart A K R0}
    (hc : c ∈ constSub A K R0 p e) (hc' : c' ∈ constSub A K R0 p e) (h : c - c' ∈ Q) : c = c' := by
  haveI := charP_maxUnram A K p
  have hd : c - c' ∈ constSub A K R0 p e := sub_mem hc hc'
  by_contra hne
  obtain ⟨n, hn, hdn⟩ := hd
  have hn1 : 1 < p ^ (e * n) := one_lt_pow_p (p := p) (Nat.mul_pos he hn)
  have hdp : ((c - c' : proChart A K R0) : maxUnram A K) ^ (p ^ (e * n)) = (c - c' : proChart A K R0) := by
    rw [pow_mul]; exact hdn
  have hd0 : ((c - c' : proChart A K R0) : maxUnram A K) ≠ 0 := fun h0 =>
    hne (sub_eq_zero.1 (Subtype.val_injective (by simpa using h0)))
  have h1 : (c - c') ^ (p ^ (e * n) - 1) ∈ Q := Ideal.pow_mem_of_mem Q h _ (by omega)
  have h1' : (c - c') ^ (p ^ (e * n) - 1) = 1 := by
    apply Subtype.val_injective
    change ((c - c' : proChart A K R0) : maxUnram A K) ^ (p ^ (e * n) - 1) = 1
    rw [pow_pred_eq_one hn1.le hdp hd0]
  rw [h1'] at h1
  exact hQ ((Ideal.eq_top_iff_one Q).2 h1)

/-- In a field integral over a finite field of order `Q ^ d` (`d ≠ 0`), every element satisfies `y ^ Q ^ a = y`
for some `a ≥ 1`. -/
theorem exists_pow_eq_self_of_integral {k L : Type} [Field k] [Field L] [Algebra k L] [Finite k]
    [Algebra.IsIntegral k L] {Q d : ℕ} (hcard : Nat.card k = Q ^ d) (hd0 : d ≠ 0) (y : L) :
    ∃ a, 0 < a ∧ y ^ Q ^ a = y := by
  classical
  let E := IntermediateField.adjoin k {y}
  haveI : FiniteDimensional k E := IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral y)
  haveI : Finite E := Module.finite_of_finite k
  letI : Fintype E := Fintype.ofFinite E
  letI : Fintype k := Fintype.ofFinite k
  have hcE : Fintype.card E = Q ^ (d * Module.finrank k E) := by
    rw [Module.card_eq_pow_finrank (K := k) (V := E), ← Nat.card_eq_fintype_card, hcard, pow_mul]
  have hr : 0 < Module.finrank k E := Module.finrank_pos
  refine ⟨d * Module.finrank k E, Nat.mul_pos (Nat.pos_of_ne_zero hd0) hr, ?_⟩
  have hpow := FiniteField.pow_card (⟨y, IntermediateField.mem_adjoin_simple_self k y⟩ : E)
  rw [hcE] at hpow
  exact congrArg Subtype.val hpow

/-- Every element of the residue field of a prime `Q` with finite residue ring below of order a power of `q`
satisfies `x̄ ^ (q ^ a) = x̄` for some `a ≥ 1`. -/
theorem exists_pow_sub_mem {Q : Ideal (proChart A K R0)} [Q.IsPrime]
    [Finite (R0 ⧸ Q.under R0)] (hcard : ∃ d, Nat.card (R0 ⧸ Q.under R0) = (p ^ e) ^ d) (x : proChart A K R0) :
    ∃ a, 0 < a ∧ x ^ (p ^ e) ^ a - x ∈ Q := by
  have hPmax : (Q.under R0).IsMaximal :=
    Ideal.Quotient.maximal_of_isField _ (Finite.isField_of_domain (R0 ⧸ Q.under R0))
  have hQmax : Q.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap Q hPmax
  letI := Ideal.Quotient.field (Q.under R0)
  letI := Ideal.Quotient.field Q
  obtain ⟨d, hd⟩ := hcard
  have hd0 : d ≠ 0 := by
    rintro rfl
    have h1 : Nat.card (R0 ⧸ Q.under R0) = 1 := by rw [hd, pow_zero]
    exact (Finite.one_lt_card (α := R0 ⧸ Q.under R0)).ne' h1
  obtain ⟨a, ha, hpow⟩ := exists_pow_eq_self_of_integral (k := R0 ⧸ Q.under R0) hd hd0 (Ideal.Quotient.mk Q x)
  refine ⟨a, ha, ?_⟩
  rw [← map_pow, Ideal.Quotient.eq] at hpow
  exact hpow

/-- Every element of the pro-chart is congruent to a constant modulo a prime `Q` as above. -/
theorem exists_const_sub_mem (he : 0 < e)
    (hζ : ∀ a, 0 < a → ∃ ζ : maxUnram A K, IsPrimitiveRoot ζ ((p ^ e) ^ a - 1))
    {Q : Ideal (proChart A K R0)} [Q.IsPrime]
    [Finite (R0 ⧸ Q.under R0)] (hcard : ∃ d, Nat.card (R0 ⧸ Q.under R0) = (p ^ e) ^ d) (x : proChart A K R0) :
    ∃ c ∈ constSub A K R0 p e, x - c ∈ Q := by
  classical
  obtain ⟨a, ha, hxa⟩ := exists_pow_sub_mem hcard x
  obtain ⟨ζ, hζp⟩ := hζ a ha
  have hk1 : 1 < (p ^ e) ^ a := by rw [← pow_mul]; exact one_lt_pow_p (p := p) (Nat.mul_pos he ha)
  set k := (p ^ e) ^ a - 1 with hk
  have hkpos : 0 < k := by omega
  have hζc : IsConst (p ^ e) ζ := by
    refine ⟨a, ha, ?_⟩
    have h1 : ζ ^ k = 1 := hζp.pow_eq_one
    calc ζ ^ (p ^ e) ^ a = ζ ^ (k + 1) := by rw [hk, Nat.sub_add_cancel hk1.le]
      _ = ζ := by rw [pow_succ, h1, one_mul]
  let ζB : proChart A K R0 := mkConst he ζ hζc
  have hζB : IsPrimitiveRoot ζB k :=
    IsPrimitiveRoot.of_map_of_injective (f := (integralClosure R0 (maxUnram A K)).val) hζp Subtype.val_injective
  have hprod := congrArg (Polynomial.eval x) (Polynomial.X_pow_sub_one_eq_prod hkpos hζB)
  simp only [eval_sub, eval_pow, eval_X, eval_one, eval_prod, eval_C] at hprod
  have hsplit : x ^ (p ^ e) ^ a - x = x * (x ^ k - 1) := by
    rw [mul_sub, mul_one, ← pow_succ', hk, Nat.sub_add_cancel hk1.le]
  rw [hsplit] at hxa
  rcases (Ideal.IsPrime.mem_or_mem ‹Q.IsPrime› hxa) with h0 | h1
  · exact ⟨0, zero_mem _, by simpa using h0⟩
  · rw [hprod] at h1
    obtain ⟨μ, hμ, hμQ⟩ := Ideal.IsPrime.prod_mem_iff.1 h1
    refine ⟨μ, ?_, hμQ⟩
    have hμk : μ ^ k = 1 := (mem_nthRootsFinset hkpos _).1 hμ
    refine ⟨a, ha, ?_⟩
    have : (μ : maxUnram A K) ^ k = 1 := by
      rw [← Subalgebra.coe_pow, hμk]; rfl
    calc (μ : maxUnram A K) ^ (p ^ e) ^ a = (μ : maxUnram A K) ^ (k + 1) := by rw [hk, Nat.sub_add_cancel hk1.le]
      _ = μ := by rw [pow_succ, this, one_mul]

variable (A K R0 p e)

/-- The residue isomorphism `constants ≃+* B ⧸ Q` at a boundary prime. -/
def resEquiv (he : 0 < e) (hζ : ∀ a, 0 < a → ∃ ζ : maxUnram A K, IsPrimitiveRoot ζ ((p ^ e) ^ a - 1))
    (Q : Ideal (proChart A K R0)) [Q.IsPrime] [Finite (R0 ⧸ Q.under R0)]
    (hcard : ∃ d, Nat.card (R0 ⧸ Q.under R0) = (p ^ e) ^ d) :
    constSub A K R0 p e ≃+* proChart A K R0 ⧸ Q :=
  RingEquiv.ofBijective ((Ideal.Quotient.mk Q).comp (constSub A K R0 p e).subtype)
    ⟨fun c c' h => Subtype.ext (const_eq_of_sub_mem he (Ideal.IsPrime.ne_top ‹_›) c.2 c'.2
        (Ideal.Quotient.eq.1 h)),
     fun y => by
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
      obtain ⟨c, hc, hxc⟩ := exists_const_sub_mem he hζ hcard x
      exact ⟨⟨c, hc⟩, (Ideal.Quotient.eq.2 hxc).symm⟩⟩

end Res

end

end RamanujanPetersson.CP4a


end

-- ===== S4.Def_RP_CP4a_Trans =====
section

/-!
# S4-CP4a, part e2: `π₁^geo` is transitive on boundary primes with the same residues

* `isInvariant_proChart`: `(proChart A K R0)^{π₁(U)} = R0` (`R0` integrally closed with fraction field `K`).
* `exists_smul_of_under_eq'`: `π₁(U)` is transitive on the primes of the pro-chart over a prime of `R0` (profinite).
* `exists_stab_of_algEquiv`: the stabilizer of `Q` surjects onto `Aut((B ⧸ Q)/(R0 ⧸ Q ∩ R0))`.
* `exists_pi1geo_smul`: two primes `Q, Q'` (finite residue rings of `q`-power order) on which every `r ∈ R0` has the
  same constant residue are conjugate under `π₁^geo`.
-/

set_option autoImplicit false

open scoped Pointwise

namespace RamanujanPetersson.CP4a

open CurveCoh GalCover Kummer

noncomputable section

section Trans

variable {A K : Type} [CommRing A] [Field K] [Algebra A K]
  {R0 : Type} [CommRing R0] [Algebra R0 K] [Algebra R0 (maxUnram A K)] [IsScalarTower R0 K (maxUnram A K)]

theorem mul_inv_smul_of_smul_eq {G α : Type*} [Group G] [MulAction G α] {σ δ : G} {x : α} (h : δ • x = x) :
    (σ * δ⁻¹) • x = σ • x := by
  rw [mul_smul, inv_smul_eq_iff.2 h.symm]

variable {p e : ℕ} [hp : Fact p.Prime] [CharP K p]

variable (R0 p e) in
/-- `σ ∈ π₁(U)` permutes the constants of the pro-chart. -/
def constSmul (σ : Pi1 A K) : constSub A K R0 p e ≃+* constSub A K R0 p e where
  toFun c := ⟨σ • (c : proChart A K R0), (mem_constSub.1 c.2).map σ⟩
  invFun c := ⟨σ⁻¹ • (c : proChart A K R0), (mem_constSub.1 c.2).map σ⁻¹⟩
  left_inv c := Subtype.ext (inv_smul_smul σ (c : proChart A K R0))
  right_inv c := Subtype.ext (smul_inv_smul σ (c : proChart A K R0))
  map_mul' x y := Subtype.ext (smul_mul' σ (x : proChart A K R0) y)
  map_add' x y := Subtype.ext (smul_add σ (x : proChart A K R0) y)

end Trans

end

end RamanujanPetersson.CP4a


end

-- ===== S4.Def_RP_CP4a_Bres =====
section

/-!
# S4-CP4a, part e3a: the constant residue map of a boundary prime

* `exists_frob_pow_of_finite`: two embeddings of a finite field `k ⊇ k0` into a field that agree on `k0`
  differ by a power of the `#k0`-Frobenius.
* `bres Q hQ : R0 →+* K_U`: `r ↦` the constant congruent to `r` modulo the boundary prime `Q` (via `resEquiv`),
  with `bres_spec`, `bres_eq`, `bres_isConst`, `bres_ker`, `bres_const`.
* Transport: `bres_smul` (`bres (σ Q) = σ ∘ bres Q`), `bres_geo` (`π₁^geo` does not change it), `bres_frob_pow`
  (`bres (φ^j Q) = Frob_q^j ∘ bres Q` for a Frobenius lift `φ`).
* `bres_conj`: equal residue maps force `π₁^geo`-conjugate primes (`exists_pi1geo_smul`).
* `exists_bres_eq`: every `k0`-compatible `χ : R0 →+* K_U` with nonzero kernel is `bres Q` of a boundary prime
  (lying over, `exists_frob_pow_of_finite`, then `φ^j`).
-/

set_option autoImplicit false

open Polynomial

namespace RamanujanPetersson.CP4a

open CurveCoh GalCover Kummer

open scoped Pointwise

noncomputable section

section FinFrob

/-- Two embeddings of a finite field `k ⊇ k0` into a field that agree on `k0` differ by a power of the
`#k0`-Frobenius. -/
theorem exists_frob_pow_of_finite {k0 k M : Type} [Field k0] [Fintype k0] [Field k] [Finite k] [Algebra k0 k]
    [Field M] (f g : k →+* M) (hfg : ∀ a : k0, f (algebraMap k0 k a) = g (algebraMap k0 k a)) :
    ∃ j : ℕ, ∀ x, g x = f x ^ (Fintype.card k0 ^ j) := by
  classical
  let _ : Fintype k := Fintype.ofFinite k
  have hn1 : 1 < Fintype.card k := Fintype.one_lt_card
  have hX : (X ^ Fintype.card k - X : M[X]) ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero M hn1
  have hroot : ∀ (u : k →+* M) (x : k), u x ∈ (X ^ Fintype.card k - X : M[X]).roots.toFinset := by
    intro u x
    rw [Multiset.mem_toFinset, mem_roots hX, IsRoot.def, eval_sub, eval_pow, eval_X, ← map_pow,
      FiniteField.pow_card, sub_self]
  have hsub : Finset.univ.image f ⊆ (X ^ Fintype.card k - X : M[X]).roots.toFinset := by
    intro y hy
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hy
    exact hroot f x
  have hcard : (X ^ Fintype.card k - X : M[X]).roots.toFinset.card ≤ (Finset.univ.image f).card := by
    rw [Finset.card_image_of_injective _ f.injective, Finset.card_univ]
    calc _ ≤ Multiset.card (X ^ Fintype.card k - X : M[X]).roots := Multiset.toFinset_card_le _
      _ ≤ (X ^ Fintype.card k - X : M[X]).natDegree := card_roots' _
      _ = Fintype.card k := FiniteField.X_pow_card_sub_X_natDegree_eq M hn1
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  have hg : ∀ x, ∃ y, f y = g x := by
    intro x
    have h := hroot g x
    rw [← heq] at h
    obtain ⟨y, -, hy⟩ := Finset.mem_image.1 h
    exact ⟨y, hy⟩
  choose h hh using hg
  let hA : k →ₐ[k0] k :=
    { toFun := h
      map_one' := f.injective (by rw [hh, map_one, map_one])
      map_mul' := fun x y => f.injective (by rw [hh, map_mul, map_mul, hh, hh])
      map_zero' := f.injective (by rw [hh, map_zero, map_zero])
      map_add' := fun x y => f.injective (by rw [hh, map_add, map_add, hh, hh])
      commutes' := fun a => f.injective (by rw [hh, hfg]) }
  obtain ⟨j, hj⟩ := (FiniteField.bijective_frobeniusAlgHom_pow k0 k).2 hA
  refine ⟨j.1, fun x => ?_⟩
  have hx : (FiniteField.frobeniusAlgHom k0 k ^ j.1) x = hA x := DFunLike.congr_fun hj x
  simp only [AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom, pow_iterate] at hx
  rw [← hh x]
  change f (hA x) = _
  rw [← hx, map_pow]

end FinFrob

section Bres

variable {A K : Type} [CommRing A] [Field K] [Algebra A K]
  {R0 : Type} [CommRing R0] [Algebra R0 K] [Algebra R0 (maxUnram A K)] [IsScalarTower R0 K (maxUnram A K)]
  [IsDomain R0] [IsIntegrallyClosed R0] [IsFractionRing R0 K]
  {p e : ℕ} [hp : Fact p.Prime] [CharP K p] (he : 0 < e)
  (hζ : ∀ a, 0 < a → ∃ ζ : maxUnram A K, IsPrimitiveRoot ζ ((p ^ e) ^ a - 1))
  (hgood : ∀ Q : Ideal (proChart A K R0), IsBdryPrime A K R0 Q →
    Finite (R0 ⧸ Q.under R0) ∧ ∃ d, Nat.card (R0 ⧸ Q.under R0) = (p ^ e) ^ d)

theorem algebraMap_proChart_injective : Function.Injective (algebraMap R0 (proChart A K R0)) := by
  intro x y hxy
  have h1 : algebraMap R0 (maxUnram A K) x = algebraMap R0 (maxUnram A K) y := congrArg Subtype.val hxy
  rw [IsScalarTower.algebraMap_apply R0 K (maxUnram A K), IsScalarTower.algebraMap_apply R0 K (maxUnram A K) y] at h1
  exact IsFractionRing.injective R0 K ((algebraMap K (maxUnram A K)).injective h1)

end Bres

end

end RamanujanPetersson.CP4a


end

-- ===== S4.Def_RP_CP4a_Bdry =====
section

/-!
# S4-CP4a, part e3b: fixed boundary points of the true Frobenius permutation (generic chart `R0`)

* `trueTau D ψ`, `trueH D ψ`, `trueTau_spec` (`ψ⁻¹ • P s = h_s • P (τ s)`), `trueCompat`: the boundary permutation of
  `ψ` WITH its defining property (`BdryData.frobTau` is a bare choice without it).
* `sres D s := bres (P s)`: injective (`sres_injective`); `sres (τ s) = (sres s)^q` for `ψ = φ⁻¹` (`sres_trueTau`).
* `iterate_trueTau_eq_iff`: `τ^m s = s ↔ sres s` has values in `𝔽_{q^m}`.
* `levelField k0 M m` (`x^{q^m} = x`), `card_levelField`, `finrank_levelField` (`= m`).
* `card_fix_eq`: `#{s | τ^m s = s} = #Hom_{k0}(R0, 𝔽_{q^m})`.
-/

set_option autoImplicit false

open Polynomial

namespace RamanujanPetersson.CP4a

open CurveCoh GalCover Kummer

open scoped Pointwise

noncomputable section

section True

variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {q : ℕ}
  {R0 : Type} [CommRing R0] [Algebra R0 K] [Algebra R0 (maxUnram A K)] [IsScalarTower R0 K (maxUnram A K)]
  {S : Type} (D : BdryData A K q R0 S)

theorem bdry_exists_true (ψ : Pi1 A K) (s : S) :
    ∃ t, ∃ g ∈ pi1geo A K q, ψ⁻¹ • D.P s = g • D.P t :=
  D.cover _ (D.B_smul ψ⁻¹ _ (D.mem s))

/-- The boundary permutation of `ψ`, with its defining property `trueTau_spec`. -/
def trueTau (ψ : Pi1 A K) : S → S := fun s => (bdry_exists_true D ψ s).choose

/-- The correcting elements of `trueTau`. -/
def trueH (ψ : Pi1 A K) : S → pi1geo A K q := fun s =>
  ⟨(bdry_exists_true D ψ s).choose_spec.choose, (bdry_exists_true D ψ s).choose_spec.choose_spec.1⟩

theorem trueTau_spec (ψ : Pi1 A K) (s : S) :
    ψ⁻¹ • D.P s = ((trueH D ψ s : pi1geo A K q) : Pi1 A K) • D.P (trueTau D ψ s) :=
  (bdry_exists_true D ψ s).choose_spec.choose_spec.2

theorem trueCompat (ψ : Pi1 A K) : BdryCompat (pi1geo A K q) D.inertia ψ (trueTau D ψ) (trueH D ψ) := by
  intro s x hx
  have hx' : (x : Pi1 A K) ∈ (D.P s).inertia (Pi1 A K) := hx
  have h1 := conj_mem_inertia_smul A K R0 ψ⁻¹ hx'
  rw [inv_inv] at h1
  exact inv_conj_mem_inertia A K R0 (trueTau_spec D ψ s) h1

end True

section Level

variable (k0 M : Type) [Field k0] [Fintype k0] [Field M] [Algebra k0 M]

/-- `𝔽_{q^m}` inside `M`: the solutions of `x^{q^m} = x`, `q = #k0`. -/
def levelField (m : ℕ) : IntermediateField k0 M :=
  Subalgebra.toIntermediateField (AlgHom.equalizer (FiniteField.frobeniusAlgHom k0 M ^ m) (AlgHom.id k0 M))
    (fun x hx => by
      rw [AlgHom.mem_equalizer] at hx ⊢
      rw [map_inv₀, hx]
      rfl)

variable {k0 M}

theorem mem_levelField {m : ℕ} {x : M} : x ∈ levelField k0 M m ↔ x ^ (Fintype.card k0 ^ m) = x := by
  show x ∈ AlgHom.equalizer _ _ ↔ _
  rw [AlgHom.mem_equalizer, AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom, pow_iterate]
  rfl

theorem card_levelField {m : ℕ} (hm : 0 < m) {ζ : M} (hζ : IsPrimitiveRoot ζ (Fintype.card k0 ^ m - 1)) :
    Nat.card (levelField k0 M m) = Fintype.card k0 ^ m := by
  classical
  have hq1 : 1 < Fintype.card k0 ^ m := Nat.one_lt_pow hm.ne' Fintype.one_lt_card
  have hn : 0 < Fintype.card k0 ^ m - 1 := by omega
  have hset : ((levelField k0 M m : Set M)) =
      ↑(insert 0 (nthRootsFinset (Fintype.card k0 ^ m - 1) (1 : M))) := by
    ext x
    simp only [SetLike.mem_coe, Finset.coe_insert, Set.mem_insert_iff, mem_nthRootsFinset hn,
      mem_levelField]
    constructor
    · intro hx
      by_cases h0 : x = 0
      · exact Or.inl h0
      · exact Or.inr (pow_pred_eq_one hq1.le hx h0)
    · rintro (h0 | h1)
      · rw [h0, zero_pow (by omega)]
      · calc x ^ Fintype.card k0 ^ m = x ^ (Fintype.card k0 ^ m - 1) * x := by
              rw [← pow_succ, Nat.sub_add_cancel hq1.le]
          _ = x := by rw [h1, one_mul]
  have h0 : (0 : M) ∉ nthRootsFinset (Fintype.card k0 ^ m - 1) (1 : M) := by
    rw [mem_nthRootsFinset hn, zero_pow (by omega)]
    exact zero_ne_one
  have hc : Nat.card (levelField k0 M m) = Nat.card ((levelField k0 M m : Set M)) := rfl
  rw [hc, hset, Nat.card_coe_set_eq, Set.ncard_coe_finset, Finset.card_insert_of_notMem h0,
    IsPrimitiveRoot.card_nthRootsFinset hζ]
  omega

end Level

section Sres

variable {A K : Type} [CommRing A] [Field K] [Algebra A K]
  {R0 : Type} [CommRing R0] [Algebra R0 K] [Algebra R0 (maxUnram A K)] [IsScalarTower R0 K (maxUnram A K)]
  [IsDomain R0] [IsIntegrallyClosed R0] [IsFractionRing R0 K]
  {p e : ℕ} [Fact p.Prime] [CharP K p] (he : 0 < e)
  (hζ : ∀ a, 0 < a → ∃ ζ : maxUnram A K, IsPrimitiveRoot ζ ((p ^ e) ^ a - 1))
  (hgood : ∀ Q : Ideal (proChart A K R0), IsBdryPrime A K R0 Q →
    Finite (R0 ⧸ Q.under R0) ∧ ∃ d, Nat.card (R0 ⧸ Q.under R0) = (p ^ e) ^ d)
  {q : ℕ} {S : Type} (D : BdryData A K q R0 S) (hDB : ∀ Q, D.B Q ↔ IsBdryPrime A K R0 Q)

end Sres

end

end RamanujanPetersson.CP4a


end

-- ===== S4.Def_RP_CoreA_ZInt =====
section

/-!
# S4-CoreA, parts Z1 + Z2: the inverse roots of the zeta function

For a function field `F / Fq` with full constant field, `q = #Fq`, `g = genusF Fq F`, `A_n = numEff Fq F n`, and
ANY multiset `c ⊆ ℂ` with `N_m = 1 + q^m - Σ_i c_i^m` (`m ≥ 1`):
* `prod_eq_zeta_F` (Z1): `Π_i (1 - c_i X) = (1 - X)(1 - q X) Σ_n A_n X^n` in `ℂ⟦X⟧`;
* `exists_int_poly` (Z1): `Π_i (1 - c_i X)` has integer coefficients;
* `numEff_top'` (Z2): `(q - 1) A_{2g-2} = h (q^(g-1) - 1) + q^g - q^(g-1)` (`g ≥ 1`, `h = #Pic⁰`), from Riemann-Roch:
  a class of degree `2g - 2` has `ℓ = g` if it is canonical and `ℓ = g - 1` otherwise;
* **`card_eq_two_genus`** (Z2): if moreover `#c ≤ 2g`, then `#c = 2g`, `Π_i c_i = q^g`, and `Π_i (1 - c_i X)` is the
  image of an integer polynomial.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Polynomial

namespace RamanujanPetersson.CoreA

open Places RR ZetaSB PicDescent

section PS

open PowerSeries

/-- Z1, abstract: Newton's identity and `b_k = 1 + Q^k - Σ c_i^k` force `Π (1 - c_i X) = (1 - X)(1 - Q X) Σ a_k X^k`. -/
theorem prod_eq_zeta (a b : ℕ → ℂ) (Q : ℂ) (c : Multiset ℂ) (ha0 : a 0 = 1)
    (hnewt : ∀ k : ℕ, ((k : ℂ) + 1) * a (k + 1) = ∑ j ∈ Finset.range (k + 1), b (j + 1) * a (k - j))
    (hb : ∀ k : ℕ, b (k + 1) = 1 + Q ^ (k + 1) - (c.map (· ^ (k + 1))).sum) :
    (c.map fun r => 1 - C r * X).prod = (1 - C 1 * X) * ((1 - C Q * X) * PowerSeries.mk a) := by
  obtain ⟨Z, hZ⟩ : ∃ Z : PowerSeries ℂ, Z = PowerSeries.mk a := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : PowerSeries ℂ, G = PowerSeries.mk fun i => b (i + 1) := ⟨_, rfl⟩
  have hdZ : derivative ℂ Z = G * Z := by
    ext n
    rw [coeff_derivative, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, hZ, coeff_mk]
    simp only [hG, coeff_mk]
    linear_combination hnewt n
  have hG' : G = PowerSeries.mk (fun i => (1 : ℂ) ^ (i + 1)) + PowerSeries.mk (fun i => Q ^ (i + 1)) -
      psumSeries c := by
    ext n
    simp only [hG, psumSeries, map_add, map_sub, coeff_mk, hb, one_pow]
  obtain ⟨V, hV⟩ : ∃ V : PowerSeries ℂ, V = (1 - C Q * X) * Z := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W : PowerSeries ℂ, W = (1 - C 1 * X) * V := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : PowerSeries ℂ, P = (c.map fun r => 1 - C r * X).prod := ⟨_, rfl⟩
  have hWd : derivative ℂ W = W * -psumSeries c := by
    have g1 := one_sub_mul_geom 1
    have gQ := one_sub_mul_geom Q
    rw [hW, hV, Derivation.leibniz, Derivation.leibniz, hdZ, deriv_one_sub, deriv_one_sub, smul_eq_mul,
      smul_eq_mul, smul_eq_mul, smul_eq_mul]
    rw [hG']
    linear_combination ((1 - C Q * X) * Z) * g1 + ((1 - C 1 * X) * Z) * gQ
  have hPd : derivative ℂ P = P * -psumSeries c := by
    rw [hP, deriv_prod]
    ring
  have hV0 : coeff 0 V = a 0 := by rw [hV, coeff_zero_one_sub_mul, hZ, coeff_mk]
  have hW0 : coeff 0 W = 1 := by rw [hW, coeff_zero_one_sub_mul, hV0, ha0]
  have hWP : W = P := eq_of_derivative_eq_mul W P _ hWd hPd (by rw [hW0, hP, coeff_zero_prod_one_sub])
  rw [← hP, ← hWP, hW, hV, hZ]

theorem map_mk_int (A : ℕ → ℤ) :
    PowerSeries.map (Int.castRingHom ℂ) (PowerSeries.mk A) = PowerSeries.mk fun k => (A k : ℂ) := by
  ext k
  simp [coeff_map]

/-- Z1, integrality: a product `Π (1 - c_i X)` equal to `(1 - X)(1 - q X) Σ A_k X^k` with `A_k, q ∈ ℤ` comes from
an integer polynomial. -/
theorem exists_int_poly (A : ℕ → ℤ) (q : ℤ) (c : Multiset ℂ)
    (h : (c.map fun r => 1 - C r * X).prod =
      (1 - C 1 * X) * ((1 - C (q : ℂ) * X) * PowerSeries.mk fun k => (A k : ℂ))) :
    ∃ L : ℤ[X], L.map (Int.castRingHom ℂ) = (c.map fun r => 1 - Polynomial.C r * Polynomial.X).prod := by
  set S : PowerSeries ℤ := (1 - C 1 * X) * ((1 - C q * X) * PowerSeries.mk A) with hSdef
  have hS : PowerSeries.map (Int.castRingHom ℂ) S = (c.map fun r => 1 - C r * X).prod := by
    rw [h, hSdef, map_mul, map_mul, map_mk_int]
    simp [map_sub, PowerSeries.map_X]
  set p : ℂ[X] := (c.map fun r => 1 - Polynomial.C r * Polynomial.X).prod with hpdef
  refine ⟨trunc (p.natDegree + 1) S, ?_⟩
  ext k
  rw [Polynomial.coeff_map, coeff_trunc]
  split_ifs with hk
  · have h2 := congrArg (coeff k) hS
    rw [coeff_map, ← coe_prod_one_sub, ← hpdef, Polynomial.coeff_coe] at h2
    exact h2
  · have hlt : p.natDegree < k := by omega
    rw [map_zero, Polynomial.coeff_eq_zero_of_natDegree_lt hlt]

end PS

/-- The coefficient of `X^#c` in `Π (1 - c_i X)` is `(-1)^#c Π c_i`. -/
theorem coeff_card_prod_one_sub (c : Multiset ℂ) :
    ((c.map fun r => 1 - Polynomial.C r * Polynomial.X).prod).coeff (Multiset.card c) =
      (-1) ^ Multiset.card c * c.prod := by
  induction c using Multiset.induction_on with
  | empty => simp
  | cons r c ih =>
    have hlt : ((c.map fun r => 1 - Polynomial.C r * Polynomial.X).prod).natDegree < Multiset.card c + 1 := by
      have := natDegree_prod_one_sub_le c
      omega
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, Multiset.prod_cons,
      show (1 - Polynomial.C r * Polynomial.X) * (c.map fun r => 1 - Polynomial.C r * Polynomial.X).prod =
        (c.map fun r => 1 - Polynomial.C r * Polynomial.X).prod -
          Polynomial.C r * (Polynomial.X * (c.map fun r => 1 - Polynomial.C r * Polynomial.X).prod) by ring,
      Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_X_mul, ih,
      Polynomial.coeff_eq_zero_of_natDegree_lt hlt]
    ring

section Concrete

variable {Fq : Type*} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type*} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

theorem eq_zero_of_deg_eq_zero {D : Divisor Fq F} (hD : 0 ≤ D) (h0 : Divisor.deg D = 0) : D = 0 := by
  classical
  have h1 : D ∈ effDivs Fq F 0 := mem_effDivs.mpr ⟨hD, by simp [h0]⟩
  have h2 : (0 : Divisor Fq F) ∈ effDivs Fq F 0 := mem_effDivs.mpr ⟨le_rfl, by simp [Divisor.deg]⟩
  have h3 : (effDivs Fq F 0).card ≤ 1 := (numEff_zero (Fq := Fq) (F := F)).le
  exact Finset.card_le_one.mp h3 D h1 0 h2

/-- Every divisor of degree `n ≥ g` is equivalent to an effective one. -/
theorem exists_eff_of_deg' (hk : constField Fq F = ⊥) {n : ℕ} (hn : (genusF Fq F : ℤ) ≤ n)
    (D : Divisor Fq F) (hD : Divisor.deg D = n) :
    ∃ E ∈ effDivs Fq F n, cls Fq F E = cls Fq F D := by
  have h1 := riemann_inequalityF' hk D
  rw [hD] at h1
  have hpos : 0 < ellF Fq F D := by
    have : (0 : ℤ) < ellF Fq F D := by omega
    exact_mod_cast this
  obtain ⟨f, hfL, hf0⟩ := Data.exists_ne_zero_of_ell_pos hpos
  refine ⟨Places.div f + D, mem_effDivs.mpr ⟨(mem_LF hf0).mp hfL, ?_⟩, cls_div_add hf0 D⟩
  rw [Divisor.deg_add, Places.deg_div hf0, hD, zero_add]

theorem hcl_le' [DecidableEq (Divisor Fq F ⧸ princ Fq F)] (hk : constField Fq F = ⊥) {n n' : ℕ}
    (hn : (genusF Fq F : ℤ) ≤ n) (B : Divisor Fq F) (hB : Divisor.deg B = (n' : ℤ) - n) :
    hcl Fq F n' ≤ hcl Fq F n := by
  unfold hcl
  refine (Finset.card_le_card (t := ((effDivs Fq F n).image (cls Fq F)).image (· + cls Fq F B))
    fun c hc => ?_).trans Finset.card_image_le
  obtain ⟨E', hE', rfl⟩ := Finset.mem_image.mp hc
  have hdeg : Divisor.deg (E' - B) = n := by
    rw [Divisor.deg_sub, hB, (mem_effDivs.mp hE').2]
    ring
  obtain ⟨E, hE, hEc⟩ := exists_eff_of_deg' hk hn (E' - B) hdeg
  refine Finset.mem_image.mpr ⟨cls Fq F E, Finset.mem_image_of_mem _ hE, ?_⟩
  rw [hEc]
  simp only [cls, QuotientAddGroup.mk_sub, sub_add_cancel]

/-- A divisor in the canonical class has `ℓ = g`. -/
theorem ellF_of_cls_eq (hk : constField Fq F = ⊥) {W E : Divisor Fq F} (hW : IsCanonicalF Fq F W)
    (h : cls Fq F E = cls Fq F W) : ellF Fq F E = genusF Fq F := by
  obtain ⟨f, hf, hdiv⟩ := (mem_princ Fq F).mp (QuotientAddGroup.eq.mp h.symm)
  have hE : E = W + Places.div f := by rw [hdiv]; abel
  rw [hE]
  exact ellF_canonical hk (isCanonicalF_add_div hW hf)

/-- A divisor of degree `2g - 2` outside the canonical class has `ℓ = g - 1`. -/
theorem ellF_of_cls_ne (hk : constField Fq F = ⊥) {W E : Divisor Fq F} (hW : IsCanonicalF Fq F W)
    (hE : Divisor.deg E = 2 * (genusF Fq F : ℤ) - 2) (h : cls Fq F E ≠ cls Fq F W) :
    (ellF Fq F E : ℤ) = genusF Fq F - 1 := by
  have hRR := riemannRochF' hk hW E
  have h0 : ellF Fq F (W - E) = 0 := by
    by_contra hne
    obtain ⟨f, hfL, hf0⟩ := Data.exists_ne_zero_of_ell_pos (Nat.pos_of_ne_zero hne)
    have hnn := (mem_LF hf0).mp hfL
    have hdeg : Divisor.deg (Places.div f + (W - E)) = 0 := by
      rw [Divisor.deg_add, Places.deg_div hf0, Divisor.deg_sub, degF_canonical hk hW, hE]
      ring
    have hz := eq_zero_of_deg_eq_zero hnn hdeg
    rw [← add_sub_assoc] at hz
    apply h
    rw [← sub_eq_zero.mp hz, cls_div_add hf0]
  rw [h0, hE] at hRR
  push_cast at hRR
  linarith

/-- `(q - 1) A_{2g-2} = #(classes of degree 2g-2 with an effective member) (q^(g-1) - 1) + q^g - q^(g-1)`. -/
theorem numEff_top [DecidableEq (Divisor Fq F ⧸ princ Fq F)] (hk : constField Fq F = ⊥) {W : Divisor Fq F}
    (hW : IsCanonicalF Fq F W) (hg : 1 ≤ genusF Fq F) :
    ((Fintype.card Fq : ℤ) - 1) * numEff Fq F (2 * genusF Fq F - 2) =
      hcl Fq F (2 * genusF Fq F - 2) * ((Fintype.card Fq : ℤ) ^ (genusF Fq F - 1) - 1) +
        ((Fintype.card Fq : ℤ) ^ genusF Fq F - (Fintype.card Fq : ℤ) ^ (genusF Fq F - 1)) := by
  set n := 2 * genusF Fq F - 2 with hn
  set I := (effDivs Fq F n).image (cls Fq F) with hI
  have hWI : cls Fq F W ∈ I := by
    have hpos : 0 < ellF Fq F W := by rw [ellF_canonical hk hW]; omega
    obtain ⟨f, hfL, hf0⟩ := Data.exists_ne_zero_of_ell_pos hpos
    refine Finset.mem_image.mpr ⟨Places.div f + W, mem_effDivs.mpr ⟨(mem_LF hf0).mp hfL, ?_⟩, cls_div_add hf0 W⟩
    rw [Divisor.deg_add, Places.deg_div hf0, zero_add, degF_canonical hk hW, hn]
    omega
  have hterm : ∀ C ∈ I, ((((effDivs Fq F n).filter fun E => cls Fq F E = C).card : ℕ) : ℤ) *
      ((Fintype.card Fq : ℤ) - 1) = ((Fintype.card Fq : ℤ) ^ (genusF Fq F - 1) - 1) +
        if C = cls Fq F W then (Fintype.card Fq : ℤ) ^ genusF Fq F - (Fintype.card Fq : ℤ) ^ (genusF Fq F - 1)
        else 0 := by
    intro C hC
    obtain ⟨E0, hE0, rfl⟩ := Finset.mem_image.mp hC
    have h := card_fiber_mul hk hE0
    have hq0 : 1 ≤ Fintype.card Fq := Fintype.card_pos
    have hq1 : 1 ≤ Fintype.card Fq ^ ellF Fq F E0 := Nat.one_le_pow _ _ Fintype.card_pos
    zify [hq0, hq1] at h
    rw [h]
    have hdeg : Divisor.deg E0 = 2 * (genusF Fq F : ℤ) - 2 := by
      rw [(mem_effDivs.mp hE0).2, hn]
      omega
    split_ifs with hc
    · rw [ellF_of_cls_eq hk hW hc]
      ring
    · have h1 := ellF_of_cls_ne hk hW hdeg hc
      have h2 : ellF Fq F E0 = genusF Fq F - 1 := by omega
      rw [h2]
      ring
  rw [numEff, Finset.card_eq_sum_card_fiberwise (f := cls Fq F) (t := I) (fun E hE => Finset.mem_image_of_mem _ hE)]
  push_cast
  rw [mul_comm ((Fintype.card Fq : ℤ) - 1), Finset.sum_mul, Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_const,
    Finset.sum_ite_eq' I (cls Fq F W), if_pos hWI, nsmul_eq_mul, hcl, ← hI]

end Concrete

end RamanujanPetersson.CoreA


end

-- ===== S4.Def_RP_CP4a_FE =====
section

/-!
# S4-CP4a, part a: RH equality, the functional equation, and traces of geometric Frobenius

* `zeta_RH_FE` (function fields with full constant field): the inverse zeta roots `c` (S3-ZetaSB `zeta_shape`)
  satisfy `#c = 2g`, `‖c_i‖ = √q` (RH equality, from `Π c_i = q^g` of CoreA `card_eq_two_genus`), `0 ∉ c`,
  `conj c = c`, the functional equation `{q / c_i} = {c_i}`, and `Π (X - c_i)` is the image of a monic `P0 ∈ ℤ[X]`.
* `det_mul_charpolyRev_of_mul_eq`: `G M = q` gives `det M · det(1 - X G) = (-1)^d · χ_M(q X)`.
* `exists_trace_pow_frob` (review R4): if `χ_M = P0`, `P0 = Π (X - c_i)` over `ℂ`, `{q / c_i} = {c_i}` and
  `G M = q` with `q` a unit, then `tr(M^(k+1))`, `tr(G^(k+1))` and `Σ c_i^(k+1)` are one integer `s k`.
  (`M` = arithmetic Frobenius `π` on `T_l`, `G = q π⁻¹` = geometric Frobenius on `H^1`.)
-/

set_option autoImplicit false

open Polynomial Matrix

namespace RamanujanPetersson.CP4a

section Alg

/-- Nonnegative reals `≤ B` whose product is `B^#r` all equal `B`. -/
theorem eq_of_prod_eq_pow (B : ℝ) (hB : 0 < B) (r : Multiset ℝ) (h0 : ∀ x ∈ r, 0 ≤ x)
    (hle : ∀ x ∈ r, x ≤ B) :
    0 ≤ r.prod ∧ r.prod ≤ B ^ Multiset.card r ∧ (r.prod = B ^ Multiset.card r → ∀ x ∈ r, x = B) := by
  induction r using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have ha0 := h0 a (Multiset.mem_cons_self a s)
    have haB := hle a (Multiset.mem_cons_self a s)
    obtain ⟨hs0, hsB, hseq⟩ := ih (fun x hx => h0 x (Multiset.mem_cons_of_mem hx))
      (fun x hx => hle x (Multiset.mem_cons_of_mem hx))
    have hBk : 0 < B ^ Multiset.card s := pow_pos hB _
    rw [Multiset.prod_cons, Multiset.card_cons, pow_succ]
    refine ⟨mul_nonneg ha0 hs0, ?_, ?_⟩
    · calc a * s.prod ≤ B * B ^ Multiset.card s := mul_le_mul haB hsB hs0 hB.le
        _ = _ := mul_comm _ _
    · intro heq x hx
      have h1 : (B - a) * B ^ Multiset.card s + a * (B ^ Multiset.card s - s.prod) = 0 := by
        linear_combination -1 * heq
      have h2 : 0 ≤ (B - a) * B ^ Multiset.card s := mul_nonneg (by linarith) hBk.le
      have h3 : 0 ≤ a * (B ^ Multiset.card s - s.prod) := mul_nonneg ha0 (by linarith)
      have h4 : (B - a) * B ^ Multiset.card s = 0 := by linarith
      have haeq : a = B := by
        rcases mul_eq_zero.mp h4 with h | h
        · linarith
        · exact absurd h hBk.ne'
      rcases Multiset.mem_cons.mp hx with rfl | hx
      · exact haeq
      · rw [haeq] at heq
        exact hseq (mul_left_cancel₀ hB.ne' (heq.trans (mul_comm _ _))) x hx

theorem norm_multiset_prod_eq (c : Multiset ℂ) : ‖c.prod‖ = (c.map (‖·‖)).prod := by
  induction c using Multiset.induction_on with
  | empty => simp
  | cons a s ih => simp [norm_mul, ih]

/-- RH equality: `‖c_i‖ ≤ B` and `‖Π c_i‖ = B^#c` force `‖c_i‖ = B`. -/
theorem norm_eq_of_norm_prod (c : Multiset ℂ) (B : ℝ) (hB : 0 < B) (hle : ∀ x ∈ c, ‖x‖ ≤ B)
    (hprod : ‖c.prod‖ = B ^ Multiset.card c) : ∀ x ∈ c, ‖x‖ = B := by
  have h := eq_of_prod_eq_pow B hB (c.map (‖·‖)) (fun x hx => by
      obtain ⟨y, -, rfl⟩ := Multiset.mem_map.mp hx; exact norm_nonneg y)
    (fun x hx => by obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hx; exact hle y hy)
  rw [Multiset.card_map, ← norm_multiset_prod_eq] at h
  exact fun x hx => h.2.2 hprod ‖x‖ (Multiset.mem_map_of_mem _ hx)

variable {K : Type*} [Field K]

theorem prod_one_sub_ne_zero (A : Multiset K) : (A.map fun a => 1 - Polynomial.C a * X).prod ≠ 0 := by
  intro h
  have := congrArg (Polynomial.eval 0) h
  simp [Polynomial.eval_multiset_prod] at this

theorem roots_prod_one_sub (A : Multiset K) (hA : (0 : K) ∉ A) :
    (A.map fun a => 1 - Polynomial.C a * X).prod.roots = A.map (·⁻¹) := by
  induction A using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have ha : a ≠ 0 := fun h => hA (h ▸ Multiset.mem_cons_self a s)
    have hs : (0 : K) ∉ s := fun h => hA (Multiset.mem_cons_of_mem h)
    have hlin : (1 - Polynomial.C a * X : K[X]) = Polynomial.C (-a) * (X - Polynomial.C a⁻¹) := by
      have e : Polynomial.C (-a) * Polynomial.C a⁻¹ = (-1 : K[X]) := by
        rw [← Polynomial.C_mul, neg_mul, mul_inv_cancel₀ ha, Polynomial.C_neg, Polynomial.C_1]
      rw [mul_sub, e, Polynomial.C_neg]
      ring
    have hne := prod_one_sub_ne_zero (a ::ₘ s)
    rw [Multiset.map_cons, Multiset.prod_cons] at hne ⊢
    rw [roots_mul hne, ih hs, hlin, roots_C_mul _ (neg_ne_zero.mpr ha), roots_X_sub_C, Multiset.map_cons,
      Multiset.singleton_add]

/-- `Π (1 - a X) = Π (1 - b X)` with no zero roots forces `A = B`. -/
theorem multiset_eq_of_prod_one_sub_eq (A B : Multiset K) (hA : (0 : K) ∉ A) (hB : (0 : K) ∉ B)
    (h : (A.map fun a => 1 - Polynomial.C a * X).prod = (B.map fun a => 1 - Polynomial.C a * X).prod) :
    A = B := by
  have h1 := congrArg Polynomial.roots h
  rw [roots_prod_one_sub A hA, roots_prod_one_sub B hB] at h1
  have h2 := congrArg (Multiset.map (·⁻¹)) h1
  simpa [Multiset.map_map, Function.comp_def] using h2

/-- `reflect` is an involution at a fixed degree bound. -/
theorem reflect_reflect {R : Type*} [Semiring R] (N : ℕ) (f : R[X]) : (f.reflect N).reflect N = f := by
  ext i
  rw [coeff_reflect, coeff_reflect, revAt_invol]

/-- `X^d Π (1/X - c_i) = Π (1 - c_i X)`, `d = #c`. -/
theorem reflect_prod_X_sub_C {R : Type*} [CommRing R] [IsDomain R] (c : Multiset R) :
    ((c.map fun r => X - Polynomial.C r).prod).reflect (Multiset.card c) =
      (c.map fun r => 1 - Polynomial.C r * X).prod := by
  induction c using Multiset.induction_on with
  | empty => simp [reflect_one]
  | cons a s ih =>
    have h1 : reflect 1 (X - Polynomial.C a : R[X]) = 1 - Polynomial.C a * X := by
      rw [reflect_sub, reflect_C, ← pow_one (X : R[X]), reflect_monomial]
      simp
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, add_comm,
      reflect_mul _ _ (natDegree_X_sub_C_le a) (natDegree_multiset_prod_X_sub_C_eq_card s).le, h1, ih,
      Multiset.map_cons, Multiset.prod_cons]

/-- Complex roots of a real (integer) polynomial `Π (1 - c_i X)` are conjugation-stable. -/
theorem conj_stable (c : Multiset ℂ) (L : ℤ[X])
    (hL : L.map (Int.castRingHom ℂ) = (c.map fun r => 1 - Polynomial.C r * X).prod) (h0 : (0 : ℂ) ∉ c) :
    c.map (starRingEnd ℂ) = c := by
  have h := congrArg (Polynomial.map (starRingEnd ℂ)) hL
  rw [Polynomial.map_map, RingHom.ext_int ((starRingEnd ℂ).comp (Int.castRingHom ℂ)) (Int.castRingHom ℂ), hL,
    Polynomial.map_multiset_prod, Multiset.map_map] at h
  have h' : (c.map fun r => 1 - Polynomial.C r * X).prod =
      ((c.map (starRingEnd ℂ)).map fun r => 1 - Polynomial.C r * X).prod := by
    rw [h, Multiset.map_map]
    congr 1
    apply Multiset.map_congr rfl
    intro x _
    simp
  refine (multiset_eq_of_prod_one_sub_eq c _ h0 ?_ h').symm
  intro hm
  obtain ⟨y, hy, hy0⟩ := Multiset.mem_map.mp hm
  exact h0 ((map_eq_zero _).mp hy0 ▸ hy)

/-- With `‖c_i‖ = √q` and conjugation-stable roots, `{q / c_i} = {c_i}`. -/
theorem fe_of_norm (c : Multiset ℂ) (q : ℝ) (hq : 0 < q) (hnorm : ∀ x ∈ c, ‖x‖ = Real.sqrt q)
    (hconj : c.map (starRingEnd ℂ) = c) : c.map (fun x => (q : ℂ) / x) = c := by
  conv_rhs => rw [← hconj]
  apply Multiset.map_congr rfl
  intro x hx
  have hx0 : x ≠ 0 := by
    intro h
    have := hnorm x hx
    rw [h, norm_zero] at this
    exact (Real.sqrt_pos.mpr hq).ne' this.symm
  have h2 : (starRingEnd ℂ) x * x = (q : ℂ) := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm x hx, Real.sq_sqrt hq.le]
  rw [div_eq_iff hx0]
  exact h2.symm

end Alg

section Mat

variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]

end Mat

section Concrete

open Places RR ZetaSB

variable {Fq : Type*} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type*} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

end Concrete

end RamanujanPetersson.CP4a


end

-- ===== S4.Def_RP_CoreA_Div =====
section

/-!
# S4-CoreA part S1: the divisible part of an `l`-primary group with finite `A[l]`

`A` with every element killed by a power of `l` and `A[l]` finite. There is `k0` with
`l^k0 A = l^(k0+j) A` for all `j`; `D := l^k0 A` is divisible, `A = A[l^k0] + D`, `A ⧸ D` is finite,
every `A[l^k]` is finite, and `A[l] ⊆ D` forces `D = A`.
-/

set_option autoImplicit false

namespace RamanujanPetersson.CoreA

/-- `x ↦ n • x` as an additive endomorphism. -/
def smulHom (A : Type*) [AddCommGroup A] (n : ℕ) : A →+ A where
  toFun x := n • x
  map_zero' := smul_zero n
  map_add' x y := smul_add n x y

variable {A : Type*} [AddCommGroup A]

@[simp] theorem smulHom_apply (n : ℕ) (x : A) : smulHom A n x = n • x := rfl

theorem mem_range_smulHom {n : ℕ} {x : A} : x ∈ (smulHom A n).range ↔ ∃ a, n • a = x := by
  rw [AddMonoidHom.mem_range]; rfl

/-- Every `A[l^k]` is finite. -/
theorem finite_torsion_pow {l : ℕ} (hfin : {x : A | l • x = 0}.Finite) (k : ℕ) :
    {x : A | l ^ k • x = 0}.Finite := by
  induction k with
  | zero => exact Set.Finite.subset (Set.finite_singleton 0) (fun x hx => by simpa using hx)
  | succ k ih =>
    have hpre : {x : A | l ^ (k + 1) • x = 0} = (fun x : A => l • x) ⁻¹' {x : A | l ^ k • x = 0} := by
      ext x; simp only [Set.mem_setOf_eq, Set.mem_preimage, pow_succ, mul_smul]
    rw [hpre]
    refine Set.Finite.preimage' ih (fun b _ => ?_)
    rcases (((fun x : A => l • x) ⁻¹' {b}).eq_empty_or_nonempty) with h | ⟨x0, hx0⟩
    · rw [h]; exact Set.finite_empty
    · refine Set.Finite.subset (hfin.image (fun t => x0 + t)) (fun x hx => ⟨x - x0, ?_, by abel⟩)
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx hx0
      simp only [Set.mem_setOf_eq, smul_sub, hx, hx0, sub_self]

/-- The chain `A[l] ∩ l^k A` stabilizes. -/
theorem exists_stable_torsion {l : ℕ} (hfin : {x : A | l • x = 0}.Finite) :
    ∃ k0 : ℕ, ∀ j : ℕ, ∀ y : A, l • y = 0 → (∃ a, l ^ k0 • a = y) → ∃ b, l ^ (k0 + j) • b = y := by
  let S : ℕ → Set A := fun k => {y | l • y = 0} ∩ {y | ∃ a, l ^ k • a = y}
  have hSfin : ∀ k, (S k).Finite := fun k => hfin.subset Set.inter_subset_left
  have hanti : ∀ k j, S (k + j) ⊆ S k := fun k j y ⟨hy, a, ha⟩ =>
    ⟨hy, l ^ j • a, by rw [← ha, smul_smul, ← pow_add, add_comm]⟩
  obtain ⟨k0, hk0⟩ : ∃ k0, (S k0).ncard = sInf (Set.range fun k => (S k).ncard) :=
    Nat.sInf_mem (Set.range_nonempty _)
  refine ⟨k0, fun j y hy hya => ?_⟩
  have hle : (S k0).ncard ≤ (S (k0 + j)).ncard := by
    rw [hk0]; exact Nat.sInf_le ⟨k0 + j, rfl⟩
  have heq := Set.eq_of_subset_of_ncard_le (hanti k0 j) hle (hSfin k0)
  have hmem : y ∈ S (k0 + j) := by rw [heq]; exact ⟨hy, hya⟩
  exact hmem.2

/-- `pi` maps `l^k A` into itself. -/
theorem map_mem_range_smulHom (pi : A →+ A) {n : ℕ} {x : A} (hx : x ∈ (smulHom A n).range) :
    pi x ∈ (smulHom A n).range := by
  obtain ⟨a, rfl⟩ := mem_range_smulHom.mp hx
  exact mem_range_smulHom.mpr ⟨pi a, (map_nsmul pi n a).symm⟩

section Stable

variable {l k0 : ℕ}
  (hk0 : ∀ j : ℕ, ∀ y : A, l • y = 0 → (∃ a, l ^ k0 • a = y) → ∃ b, l ^ (k0 + j) • b = y)
include hk0

/-- `l^k0 A ⊆ l^(k0+1) A` on elements killed by `l^m`. -/
theorem range_subset_succ (m : ℕ) : ∀ x : A, l ^ m • x = 0 → (∃ a, l ^ k0 • a = x) →
    ∃ b, l ^ (k0 + 1) • b = x := by
  induction m with
  | zero =>
    intro x hx _
    refine ⟨0, ?_⟩
    rw [pow_zero, one_smul] at hx
    rw [hx, smul_zero]
  | succ m ih =>
    intro x hx ⟨a, ha⟩
    have hy : l • (l ^ m • x) = 0 := by rw [smul_smul, ← pow_succ']; exact hx
    obtain ⟨c, hc⟩ := hk0 (m + 1) (l ^ m • x) hy ⟨l ^ m • a, by rw [← ha, smul_smul, smul_smul, mul_comm]⟩
    obtain ⟨b, hb⟩ := ih (x - l ^ (k0 + 1) • c)
      (by rw [smul_sub, smul_smul, ← pow_add, show m + (k0 + 1) = k0 + (m + 1) by ring, hc, sub_self])
      ⟨a - l • c, by rw [smul_sub, smul_smul, ← pow_succ, ha]⟩
    exact ⟨b + c, by rw [smul_add, hb, sub_add_cancel]⟩

variable (htors : ∀ x : A, ∃ k, l ^ k • x = 0)
include htors

theorem range_subset_add (j : ℕ) (x : A) (hx : ∃ a, l ^ k0 • a = x) : ∃ b, l ^ (k0 + j) • b = x := by
  induction j with
  | zero => simpa using hx
  | succ j ih =>
    obtain ⟨b, hb⟩ := ih
    obtain ⟨m, hm⟩ := htors (l ^ k0 • b)
    obtain ⟨c, hc⟩ := range_subset_succ hk0 m (l ^ k0 • b) hm ⟨b, rfl⟩
    refine ⟨c, ?_⟩
    rw [← hb, show k0 + (j + 1) = j + (k0 + 1) by ring, pow_add, mul_smul, hc, ← mul_smul, ← pow_add,
      show j + k0 = k0 + j by ring]

/-- `D = l^k0 A` is divisible (by every `l^m`). -/
theorem divisible (m : ℕ) (y : A) (hy : y ∈ (smulHom A (l ^ k0)).range) :
    ∃ z ∈ (smulHom A (l ^ k0)).range, l ^ m • z = y := by
  obtain ⟨c, hc⟩ := range_subset_add hk0 htors m y (mem_range_smulHom.mp hy)
  exact ⟨l ^ k0 • c, mem_range_smulHom.mpr ⟨c, rfl⟩, by
    rw [← hc, smul_smul, ← pow_add, show m + k0 = k0 + m by ring]⟩

/-- `A = A[l^k0] + D`. -/
theorem decomp (x : A) : ∃ t d, l ^ k0 • t = 0 ∧ d ∈ (smulHom A (l ^ k0)).range ∧ x = t + d := by
  obtain ⟨c, hc⟩ := range_subset_add hk0 htors k0 (l ^ k0 • x) ⟨x, rfl⟩
  exact ⟨x - l ^ k0 • c, l ^ k0 • c, by rw [smul_sub, smul_smul, ← pow_add, hc, sub_self],
    mem_range_smulHom.mpr ⟨c, rfl⟩, (sub_add_cancel _ _).symm⟩

/-- `A ⧸ D` is finite. -/
theorem finite_quotient (hfin : {x : A | l • x = 0}.Finite) : Finite (A ⧸ (smulHom A (l ^ k0)).range) := by
  have : Finite {x : A | l ^ k0 • x = 0} := (finite_torsion_pow hfin k0).to_subtype
  refine Finite.of_surjective
    (fun t : {x : A | l ^ k0 • x = 0} => (QuotientAddGroup.mk (t : A) : A ⧸ (smulHom A (l ^ k0)).range)) ?_
  intro q
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
  obtain ⟨t, d, ht, hd, rfl⟩ := decomp hk0 htors x
  exact ⟨⟨t, ht⟩, QuotientAddGroup.eq.mpr (by rwa [neg_add_cancel_left])⟩

/-- `A[l] ⊆ D` forces `D = A`. -/
theorem mem_of_torsion_le (hsub : ∀ x : A, l • x = 0 → x ∈ (smulHom A (l ^ k0)).range) (x : A) :
    x ∈ (smulHom A (l ^ k0)).range := by
  obtain ⟨m, hm⟩ := htors x
  induction m generalizing x with
  | zero =>
    rw [pow_zero, one_smul] at hm
    rw [hm]; exact AddSubgroup.zero_mem _
  | succ m ih =>
    have h1 : l • (l ^ m • x) = 0 := by rw [smul_smul, ← pow_succ']; exact hm
    obtain ⟨z, hz, hzx⟩ := divisible hk0 htors m (l ^ m • x) (hsub _ h1)
    have hxz := ih (x - z) (by rw [smul_sub, hzx, sub_self])
    have hx : x = (x - z) + z := (sub_add_cancel x z).symm
    rw [hx]
    exact AddSubgroup.add_mem _ hxz hz

end Stable

end RamanujanPetersson.CoreA


end

-- ===== S4.Def_RP_CoreA_Basis =====
section

/-!
# S4-CoreA part S2a: compatible bases of `G[l^N]` for a divisible `l`-primary group

`G` divisible by `l` with `#G[l] = l ^ s`. A basis `b1` of `G[l]` (integer coordinates) lifts to compatible
families `tateBasis N` (`l • tateBasis (N+1) = tateBasis N`, `tateBasis 0 = 0`, `tateBasis 1 = b1`), and
`c ↦ ∑ c i • tateBasis N i` maps `ℤ ^ s` onto `G[l^N]` with kernel `l^N ℤ ^ s`. Also: compatible integer
sequences have `l`-adic limits.
-/

set_option autoImplicit false

namespace RamanujanPetersson.CoreA

section Lift

variable {l : ℕ} [hl : Fact l.Prime]

/-- A compatible integer sequence has an `l`-adic limit. -/
theorem exists_padicInt_compat (a : ℕ → ℤ) (ha : ∀ N, ((l ^ N : ℕ) : ℤ) ∣ a (N + 1) - a N) :
    ∃ z : ℤ_[l], ∀ N, PadicInt.toZModPow N z = (a N : ZMod (l ^ N)) := by
  have hchain : ∀ k j, ((l ^ k : ℕ) : ℤ) ∣ a (k + j) - a k := by
    intro k j
    induction j with
    | zero => simp
    | succ j ih =>
      have h1 : ((l ^ k : ℕ) : ℤ) ∣ ((l ^ (k + j) : ℕ) : ℤ) := by
        exact_mod_cast pow_dvd_pow l (Nat.le_add_right k j)
      have e : a (k + (j + 1)) - a k = (a (k + j) - a k) + (a (k + j + 1) - a (k + j)) := by
        rw [show k + (j + 1) = k + j + 1 by ring]; ring
      rw [e]
      exact dvd_add ih (h1.trans (ha (k + j)))
  let f : ∀ k : ℕ, Polynomial ℤ →+* ZMod (l ^ k) := fun k =>
    Polynomial.eval₂RingHom (Int.castRingHom _) (a k : ZMod (l ^ k))
  have hf : ∀ (k1 k2 : ℕ) (hk : k1 ≤ k2),
      (ZMod.castHom (pow_dvd_pow l hk) (ZMod (l ^ k1))).comp (f k2) = f k1 := by
    intro k1 k2 hk
    apply Polynomial.ringHom_ext
    · intro c
      exact RingHom.congr_fun (RingHom.ext_int
        (((ZMod.castHom (pow_dvd_pow l hk) (ZMod (l ^ k1))).comp (f k2)).comp Polynomial.C)
        ((f k1).comp Polynomial.C)) c
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
      rw [RingHom.comp_apply, ZMod.castHom_apply]
      simp only [f, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
      rw [ZMod.cast_intCast (pow_dvd_pow l hk)]
      exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr (dvd_sub_comm.mp (hchain k1 j))
  refine ⟨PadicInt.lift hf Polynomial.X, fun N => ?_⟩
  have := congrArg (fun g => g Polynomial.X) (PadicInt.lift_spec hf N)
  simpa [f] using this

end Lift

variable {G : Type*} [AddCommGroup G] {l : ℕ}

/-- Compatible lifts of a family `b1` along multiplication by `l`. -/
noncomputable def tateBasis (hdiv : ∀ y : G, ∃ z, l • z = y) {s : ℕ} (b1 : Fin s → G) : ℕ → Fin s → G
  | 0 => 0
  | 1 => b1
  | (N + 2) => fun i => Classical.choose (hdiv (tateBasis hdiv b1 (N + 1) i))

section Basis

variable (hdiv : ∀ y : G, ∃ z, l • z = y) {s : ℕ} (b1 : Fin s → G)

theorem tateBasis_one : tateBasis hdiv b1 1 = b1 := rfl

theorem tateBasis_succ (hb1 : ∀ i, l • b1 i = 0) (N : ℕ) (i : Fin s) :
    l • tateBasis hdiv b1 (N + 1) i = tateBasis hdiv b1 N i := by
  cases N with
  | zero => exact hb1 i
  | succ N =>
    show l • Classical.choose (hdiv (tateBasis hdiv b1 (N + 1) i)) = _
    exact Classical.choose_spec (hdiv _)

theorem tateBasis_pow_smul (hb1 : ∀ i, l • b1 i = 0) (N k : ℕ) (i : Fin s) :
    l ^ N • tateBasis hdiv b1 (N + k) i = tateBasis hdiv b1 k i := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show N + 1 + k = (N + k) + 1 by ring, pow_succ, mul_smul, tateBasis_succ hdiv b1 hb1, ih]

theorem tateBasis_pow_smul_self (hb1 : ∀ i, l • b1 i = 0) (N : ℕ) (i : Fin s) :
    l ^ N • tateBasis hdiv b1 N i = 0 := by
  have := tateBasis_pow_smul hdiv b1 hb1 N 0 i
  rw [add_zero] at this
  rw [this]; rfl

variable (hb1 : ∀ i, l • b1 i = 0)
  (h1inj : ∀ d : Fin s → ℤ, ∑ i, d i • b1 i = 0 → ∀ i, (l : ℤ) ∣ d i)
  (h1span : ∀ x : G, l • x = 0 → ∃ d : Fin s → ℤ, ∑ i, d i • b1 i = x)

include hb1 in
theorem smul_sum_tateBasis_succ (N : ℕ) (c : Fin s → ℤ) :
    l • ∑ i, c i • tateBasis hdiv b1 (N + 1) i = ∑ i, c i • tateBasis hdiv b1 N i := by
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [smul_comm, tateBasis_succ hdiv b1 hb1]

include hb1 h1inj in
/-- Kernel of the integer coordinates at level `N` is `l^N ℤ^s`. -/
theorem dvd_of_sum_tateBasis_eq_zero (N : ℕ) (c : Fin s → ℤ)
    (hc : ∑ i, c i • tateBasis hdiv b1 N i = 0) (i : Fin s) : ((l ^ N : ℕ) : ℤ) ∣ c i := by
  induction N generalizing c i with
  | zero => simp
  | succ N ih =>
    have h0 : ∑ i, c i • tateBasis hdiv b1 N i = 0 := by
      rw [← smul_sum_tateBasis_succ hdiv b1 hb1, hc, smul_zero]
    have hd : ∀ j, ∃ d : ℤ, c j = ((l ^ N : ℕ) : ℤ) * d := fun j => ih c h0 j
    choose d hd using hd
    have h1 : ∑ i, d i • b1 i = 0 := by
      rw [← hc]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [hd j, mul_comm, mul_smul, natCast_zsmul, show N + 1 = N + 1 from rfl,
        tateBasis_pow_smul hdiv b1 hb1 N 1 j, tateBasis_one]
    obtain ⟨e, he⟩ := h1inj d h1 i
    rw [hd i, he, pow_succ]
    exact ⟨e, by push_cast; ring⟩

include hb1 h1span in
/-- The integer coordinates at level `N` reach all of `G[l^N]`. -/
theorem exists_sum_tateBasis_eq (N : ℕ) (x : G) (hx : l ^ N • x = 0) :
    ∃ c : Fin s → ℤ, ∑ i, c i • tateBasis hdiv b1 N i = x := by
  induction N generalizing x with
  | zero =>
    rw [pow_zero, one_smul] at hx
    exact ⟨0, by simp [hx]⟩
  | succ N ih =>
    obtain ⟨c, hc⟩ := ih (l • x) (by rw [smul_smul, ← pow_succ]; exact hx)
    obtain ⟨d, hd⟩ := h1span (x - ∑ i, c i • tateBasis hdiv b1 (N + 1) i)
      (by rw [smul_sub, smul_sum_tateBasis_succ hdiv b1 hb1, hc, sub_self])
    refine ⟨fun i => c i + ((l ^ N : ℕ) : ℤ) * d i, ?_⟩
    have e : ∀ i, (c i + ((l ^ N : ℕ) : ℤ) * d i) • tateBasis hdiv b1 (N + 1) i =
        c i • tateBasis hdiv b1 (N + 1) i + d i • b1 i := by
      intro i
      rw [add_smul, mul_comm, mul_smul, natCast_zsmul, tateBasis_pow_smul hdiv b1 hb1 N 1 i, tateBasis_one]
    simp only [e, Finset.sum_add_distrib, hd]
    abel

end Basis

/-- An elementary abelian `l`-group of order `l ^ s` has an integer-coordinate basis. -/
theorem exists_basis_aux [hl : Fact l.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod l) V] [Finite V] {s : ℕ}
    (hs : Nat.card V = l ^ s) :
    ∃ b : Fin s → V, (∀ d : Fin s → ℤ, ∑ i, d i • b i = 0 → ∀ i, (l : ℤ) ∣ d i) ∧
      (∀ x : V, ∃ d : Fin s → ℤ, ∑ i, d i • b i = x) := by
  classical
  have : Module.Finite (ZMod l) V := Module.Finite.of_finite
  have hfr : Module.finrank (ZMod l) V = s := by
    let _ : Fintype V := Fintype.ofFinite V
    have hc : Fintype.card V = Fintype.card (ZMod l) ^ Module.finrank (ZMod l) V := Module.card_eq_pow_finrank
    rw [← Nat.card_eq_fintype_card, hs, ZMod.card] at hc
    exact (Nat.pow_right_injective hl.out.two_le hc).symm
  let B := Module.finBasisOfFinrankEq (ZMod l) V hfr
  have hz : ∀ d : Fin s → ℤ, ∑ i, ((d i : ZMod l)) • B i = ∑ i, d i • B i := fun d =>
    Finset.sum_congr rfl (fun i _ => Int.cast_smul_eq_zsmul _ _ _)
  refine ⟨fun i => B i, fun d hd i => ?_, fun x => ?_⟩
  · have h0 : ∑ i, ((d i : ZMod l)) • B i = 0 := by rw [hz]; exact hd
    have := Fintype.linearIndependent_iff.mp B.linearIndependent (fun i => (d i : ZMod l)) h0 i
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp this
  · refine ⟨fun i => ((B.repr x i).val : ℤ), ?_⟩
    rw [← hz]
    refine (Finset.sum_congr rfl (fun i _ => ?_)).trans (B.sum_repr x)
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]

/-- A basis of `G[l]` in integer coordinates. -/
theorem exists_level_one_basis [hl : Fact l.Prime] {s : ℕ} (hs : Nat.card (smulHom G l).ker = l ^ s) :
    ∃ b1 : Fin s → G, (∀ i, l • b1 i = 0) ∧
      (∀ d : Fin s → ℤ, ∑ i, d i • b1 i = 0 → ∀ i, (l : ℤ) ∣ d i) ∧
      (∀ x : G, l • x = 0 → ∃ d : Fin s → ℤ, ∑ i, d i • b1 i = x) := by
  classical
  have hmemT : ∀ x : G, x ∈ (smulHom G l).ker ↔ l • x = 0 := fun x => by
    rw [AddMonoidHom.mem_ker, smulHom_apply]
  have hT : ∀ x : (smulHom G l).ker, l • x = 0 := fun x => Subtype.ext (by
    rw [AddSubgroup.coe_nsmul, AddSubgroup.coe_zero]; exact (hmemT _).mp x.2)
  have : Finite (smulHom G l).ker :=
    Nat.finite_of_card_ne_zero (by rw [hs]; exact pow_ne_zero _ hl.out.ne_zero)
  let _ : Module (ZMod l) (smulHom G l).ker := AddCommGroup.zmodModule hT
  obtain ⟨b, hinj, hspan⟩ := exists_basis_aux hs
  have hcoe : ∀ d : Fin s → ℤ, ((∑ i, d i • b i : (smulHom G l).ker) : G) = ∑ i, d i • (b i : G) := by
    intro d
    rw [AddSubgroup.val_finsetSum]
    exact Finset.sum_congr rfl (fun i _ => AddSubgroup.coe_zsmul _ _ _)
  refine ⟨fun i => (b i : G), fun i => (hmemT _).mp (b i).2, fun d hd i => ?_, fun x hx => ?_⟩
  · exact hinj d (Subtype.ext (by rw [hcoe]; exact hd)) i
  · obtain ⟨d, hd⟩ := hspan ⟨x, (hmemT x).mpr hx⟩
    exact ⟨d, by rw [← hcoe, hd]⟩

end RamanujanPetersson.CoreA


end

-- ===== S4.Def_RP_CoreA_Tate =====
section

/-!
# S4-CoreA part S2b: the Tate module coordinates and the matrix of an endomorphism

With `tateBasis` from S2a, `tateMap N : (Fin s → ZMod (l^N)) →+ G` is injective with range `G[l^N]`.
Every additive endomorphism `φ` of `G` has a unique matrix `M` over `ℤ_[l]` with
`φ (tateMap N c) = tateMap N (M.map (toZModPow N) *ᵥ c)` for all `N` (`IsTateMat`); this is compatible with
`1`, products, differences and powers.
-/

set_option autoImplicit false

open scoped Matrix

namespace RamanujanPetersson.CoreA

variable {G : Type*} [AddCommGroup G] {l : ℕ}

section Tate

variable (hdiv : ∀ y : G, ∃ z, l • z = y) {s : ℕ} (b1 : Fin s → G) (hb1 : ∀ i, l • b1 i = 0)

/-- Coordinates at level `N`: `c ↦ ∑ c i • tateBasis N i`. -/
noncomputable def tateMap (N : ℕ) : (Fin s → ZMod (l ^ N)) →+ G :=
  ∑ i, (ZMod.lift (l ^ N) ⟨zmultiplesHom G (tateBasis hdiv b1 N i), by
      rw [zmultiplesHom_apply, natCast_zsmul, tateBasis_pow_smul_self hdiv b1 hb1 N i]⟩).comp
    (Pi.evalAddMonoidHom (fun _ : Fin s => ZMod (l ^ N)) i)

theorem tateMap_intCast (N : ℕ) (c : Fin s → ℤ) :
    tateMap hdiv b1 hb1 N (fun i => (c i : ZMod (l ^ N))) = ∑ i, c i • tateBasis hdiv b1 N i := by
  simp [tateMap, AddMonoidHom.finsetSum_apply]

theorem exists_intCast {N : ℕ} (cb : Fin s → ZMod (l ^ N)) :
    ∃ c : Fin s → ℤ, cb = fun i => (c i : ZMod (l ^ N)) :=
  ⟨fun i => (cb i).cast, funext fun i => (ZMod.intCast_zmod_cast _).symm⟩

theorem tateMap_smul_eq_zero (N : ℕ) (cb : Fin s → ZMod (l ^ N)) : l ^ N • tateMap hdiv b1 hb1 N cb = 0 := by
  obtain ⟨c, rfl⟩ := exists_intCast cb
  rw [tateMap_intCast, Finset.smul_sum]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [smul_comm, tateBasis_pow_smul_self hdiv b1 hb1, smul_zero]

variable (h1inj : ∀ d : Fin s → ℤ, ∑ i, d i • b1 i = 0 → ∀ i, (l : ℤ) ∣ d i)
  (h1span : ∀ x : G, l • x = 0 → ∃ d : Fin s → ℤ, ∑ i, d i • b1 i = x)

include h1inj in
theorem tateMap_injective (N : ℕ) : Function.Injective (tateMap hdiv b1 hb1 N) := by
  refine (injective_iff_map_eq_zero _).mpr (fun cb hcb => ?_)
  obtain ⟨c, rfl⟩ := exists_intCast cb
  rw [tateMap_intCast] at hcb
  funext i
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (dvd_of_sum_tateBasis_eq_zero hdiv b1 hb1 h1inj N c hcb i)

include h1span in
theorem exists_tateMap_eq (N : ℕ) (x : G) (hx : l ^ N • x = 0) : ∃ cb, tateMap hdiv b1 hb1 N cb = x := by
  obtain ⟨c, hc⟩ := exists_sum_tateBasis_eq hdiv b1 hb1 h1span N x hx
  exact ⟨fun i => (c i : ZMod (l ^ N)), by rw [tateMap_intCast, hc]⟩

variable [Fact l.Prime]

/-- `M` is the matrix of `φ` on the Tate module. -/
def IsTateMat (φ : AddMonoid.End G) (M : Matrix (Fin s) (Fin s) ℤ_[l]) : Prop :=
  ∀ N (cb : Fin s → ZMod (l ^ N)),
    φ (tateMap hdiv b1 hb1 N cb) = tateMap hdiv b1 hb1 N (M.map (PadicInt.toZModPow N) *ᵥ cb)

include h1inj h1span in
theorem exists_isTateMat (φ : AddMonoid.End G) :
    ∃ M : Matrix (Fin s) (Fin s) ℤ_[l], IsTateMat hdiv b1 hb1 φ M := by
  have hφ : ∀ N j, l ^ N • φ (tateBasis hdiv b1 N j) = 0 := fun N j => by
    rw [← map_nsmul, tateBasis_pow_smul_self hdiv b1 hb1, map_zero]
  choose col hcol using fun N j => exists_sum_tateBasis_eq hdiv b1 hb1 h1span N _ (hφ N j)
  have hcompat : ∀ i j N, ((l ^ N : ℕ) : ℤ) ∣ col (N + 1) j i - col N j i := by
    intro i j N
    have h0 : ∑ i, (col (N + 1) j i - col N j i) • tateBasis hdiv b1 N i = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib]
      rw [← smul_sum_tateBasis_succ hdiv b1 hb1 N (col (N + 1) j), hcol (N + 1) j, hcol N j, ← map_nsmul,
        tateBasis_succ hdiv b1 hb1, sub_self]
    exact dvd_of_sum_tateBasis_eq_zero hdiv b1 hb1 h1inj N _ h0 i
  choose M hM using fun i j => exists_padicInt_compat (l := l) (fun N => col N j i) (hcompat i j)
  refine ⟨Matrix.of M, fun N cb => ?_⟩
  obtain ⟨c, rfl⟩ := exists_intCast cb
  have hv : (Matrix.of M).map (PadicInt.toZModPow N) *ᵥ (fun j => (c j : ZMod (l ^ N))) =
      fun i => ((∑ j, col N j i * c j : ℤ) : ZMod (l ^ N)) := by
    ext i
    simp [Matrix.mulVec, dotProduct, hM]
  rw [hv, tateMap_intCast, tateMap_intCast, map_sum]
  simp only [map_zsmul, ← hcol N, Finset.smul_sum, Finset.sum_smul, smul_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by rw [mul_comm]))

theorem isTateMat_one : IsTateMat hdiv b1 hb1 (1 : AddMonoid.End G) (1 : Matrix (Fin s) (Fin s) ℤ_[l]) := by
  intro N cb
  have e : (1 : Matrix (Fin s) (Fin s) ℤ_[l]).map (PadicInt.toZModPow N) = 1 :=
    (PadicInt.toZModPow (p := l) N).mapMatrix.map_one
  rw [e, Matrix.one_mulVec]
  rfl

theorem IsTateMat.mul {φ χ : AddMonoid.End G} {M M' : Matrix (Fin s) (Fin s) ℤ_[l]}
    (h : IsTateMat hdiv b1 hb1 φ M) (h' : IsTateMat hdiv b1 hb1 χ M') :
    IsTateMat hdiv b1 hb1 (φ * χ) (M * M') := by
  intro N cb
  show φ (χ _) = _
  rw [h', h, Matrix.mulVec_mulVec, Matrix.map_mul]

theorem IsTateMat.sub {φ χ : AddMonoid.End G} {M M' : Matrix (Fin s) (Fin s) ℤ_[l]}
    (h : IsTateMat hdiv b1 hb1 φ M) (h' : IsTateMat hdiv b1 hb1 χ M') :
    IsTateMat hdiv b1 hb1 (φ - χ) (M - M') := by
  intro N cb
  have e : (M - M').map (PadicInt.toZModPow N) = M.map (PadicInt.toZModPow N) - M'.map (PadicInt.toZModPow N) :=
    (PadicInt.toZModPow (p := l) N).mapMatrix.map_sub M M'
  show φ _ - χ _ = _
  rw [h, h', e, Matrix.sub_mulVec, map_sub]

theorem IsTateMat.pow {φ : AddMonoid.End G} {M : Matrix (Fin s) (Fin s) ℤ_[l]}
    (h : IsTateMat hdiv b1 hb1 φ M) (n : ℕ) : IsTateMat hdiv b1 hb1 (φ ^ n) (M ^ n) := by
  induction n with
  | zero => simpa using isTateMat_one hdiv b1 hb1
  | succ n ih => simpa [pow_succ] using ih.mul hdiv b1 hb1 h

theorem IsTateMat.one_sub_pow {φ : AddMonoid.End G} {M : Matrix (Fin s) (Fin s) ℤ_[l]}
    (h : IsTateMat hdiv b1 hb1 φ M) (n : ℕ) : IsTateMat hdiv b1 hb1 (1 - φ ^ n) (1 - M ^ n) :=
  (isTateMat_one hdiv b1 hb1).sub hdiv b1 hb1 (h.pow hdiv b1 hb1 n)

end Tate

end RamanujanPetersson.CoreA


end

-- ===== S4.Def_RP_JacAlg_Kernel =====
section

/-!
# Core B algebra, part 6: the kernel count (unit S4-JacAlg, lemma L3 = route A2)

* `card_quotient_range` (K1): for `f` an endomorphism of a free finite `ℤ_l`-module with `det f ≠ 0`,
  `#(M ⧸ f M) = l ^ v_l(det f)` (Smith normal form over the PID `ℤ_l`).
* `card_ker_mod` (K2): for a matrix `B` over `ℤ_l` with `det B ≠ 0` and `N ≥ v_l(det B)`, the kernel of
  `B mod l^N` on `(ℤ/l^N)^n` has `l ^ v_l(det B)` elements. With `A[l^N] ≅ (ℤ/l^N)^n` this is
  `#Ker(b on A[l^∞]) = |det T_l b|_l⁻¹` (Milne p.52).
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacAlg

open Matrix Module

variable {l : ℕ} [hl : Fact l.Prime]

theorem card_quot_span_pow (n : ℕ) :
    Nat.card (ℤ_[l] ⧸ Ideal.span {(l : ℤ_[l]) ^ n}) = l ^ n := by
  rw [← PadicInt.ker_toZModPow, Nat.card_congr
    (RingHom.quotientKerEquivOfSurjective (ZMod.ringHom_surjective (PadicInt.toZModPow n))).toEquiv,
    Nat.card_zmod]

theorem card_quot_span (x : ℤ_[l]) (hx : x ≠ 0) :
    Nat.card (ℤ_[l] ⧸ Ideal.span {x}) = l ^ x.valuation := by
  have e := PadicInt.unitCoeff_spec hx
  have : Ideal.span {x} = Ideal.span {(l : ℤ_[l]) ^ x.valuation} :=
    (congrArg (fun y => Ideal.span {y}) e).trans
      (Ideal.span_singleton_mul_left_unit (PadicInt.unitCoeff hx).isUnit _)
  rw [this, card_quot_span_pow]

theorem valuation_prod {ι : Type*} (s : Finset ι) (a : ι → ℤ_[l]) (ha : ∀ i ∈ s, a i ≠ 0) :
    (∏ i ∈ s, a i).valuation = ∑ i ∈ s, (a i).valuation := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj, PadicInt.valuation_mul (ha j (by simp))
      (Finset.prod_ne_zero_iff.mpr fun i hi => ha i (by simp [hi])),
      ih fun i hi => ha i (by simp [hi])]

variable {M : Type*} [AddCommGroup M] [Module ℤ_[l] M] [Module.Free ℤ_[l] M] [Module.Finite ℤ_[l] M]

theorem injective_of_det_ne_zero (f : M →ₗ[ℤ_[l]] M) (hf : LinearMap.det f ≠ 0) :
    Function.Injective f := by
  classical
  let b := Module.Free.chooseBasis ℤ_[l] M
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  by_contra hne
  have hv : (⇑(b.repr x) : _ → ℤ_[l]) ≠ 0 := fun h =>
    hne (b.repr.map_eq_zero_iff.mp (Finsupp.coe_eq_zero.mp h))
  have h1 : (LinearMap.toMatrix b b f) *ᵥ (b.repr x) = 0 := by
    rw [LinearMap.toMatrix_mulVec_repr, hx, map_zero, Finsupp.coe_zero]
  have h2 := Matrix.exists_mulVec_eq_zero_iff.mp ⟨_, hv, h1⟩
  rw [LinearMap.det_toMatrix] at h2
  exact hf h2

/-- K1: `#(M ⧸ f M) = l ^ v_l(det f)`. -/
theorem card_quotient_range (f : M →ₗ[ℤ_[l]] M) (hf : LinearMap.det f ≠ 0) :
    Nat.card (M ⧸ LinearMap.range f) = l ^ (LinearMap.det f).valuation := by
  classical
  set N := LinearMap.range f
  let b := Module.Free.chooseBasis ℤ_[l] M
  have hinj := injective_of_det_ne_zero f hf
  have h : Module.finrank ℤ_[l] N = Module.finrank ℤ_[l] M := LinearMap.finrank_range_of_inj hinj
  let a := Submodule.smithNormalFormCoeffs b h
  let b' := Submodule.smithNormalFormTopBasis b h
  let ab := Submodule.smithNormalFormBotBasis b h
  have ab_eq := Submodule.smithNormalFormBotBasis_def b h
  let e' : M ≃ₗ[ℤ_[l]] N := b'.equiv ab (Equiv.refl _)
  have ha : ∀ i, (N.subtype ∘ₗ (e' : M →ₗ[ℤ_[l]] N)) (b' i) = a i • b' i := by
    intro i
    change (N.subtype (b'.equiv ab (Equiv.refl _) (b' i))) = _
    rw [b'.equiv_apply, Equiv.refl_apply]
    exact ab_eq i
  have hdet' : LinearMap.det (N.subtype ∘ₗ (e' : M →ₗ[ℤ_[l]] N)) = ∏ i, a i := by
    rw [← LinearMap.det_toMatrix b', ← Matrix.det_diagonal]
    congr 1; ext i j
    rw [LinearMap.toMatrix_apply, ha, map_smul, Basis.repr_self, Finsupp.smul_single, smul_eq_mul,
      mul_one]
    by_cases hij : i = j
    · rw [hij, Matrix.diagonal_apply_eq, Finsupp.single_eq_same]
    · rw [Matrix.diagonal_apply_ne _ hij, Finsupp.single_eq_of_ne hij]
  have hassoc : Associated (LinearMap.det f) (∏ i, a i) := by
    rw [← hdet']
    have hf' : f = N.subtype ∘ₗ ((LinearEquiv.ofInjective f hinj : M ≃ₗ[ℤ_[l]] N) : M →ₗ[ℤ_[l]] N) := by
      ext x; rfl
    rw [hf']
    exact LinearMap.associated_det_comp_equiv N.subtype _ _
  have ha0 : ∀ i, a i ≠ 0 := Submodule.smithNormalFormCoeffs_ne_zero b h
  have hp0 : ∏ i, a i ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => ha0 i
  calc Nat.card (M ⧸ N) = ∏ i, Nat.card (ℤ_[l] ⧸ Ideal.span {a i}) := by
        rw [Nat.card_congr (Submodule.quotientEquivPiSpan N b h).toEquiv, Nat.card_pi]
    _ = ∏ i, l ^ (a i).valuation := Finset.prod_congr rfl fun i _ => card_quot_span _ (ha0 i)
    _ = l ^ (∑ i, (a i).valuation) := Finset.prod_pow_eq_pow_sum _ _ _
    _ = l ^ (∏ i, a i).valuation := by rw [valuation_prod _ _ fun i _ => ha0 i]
    _ = l ^ (LinearMap.det f).valuation := by
        rw [← card_quot_span _ hp0, ← card_quot_span _ hf,
          Ideal.span_singleton_eq_span_singleton.mpr hassoc]

/-- K2: `#Ker(B mod l^N on (ℤ/l^N)^n) = l ^ v_l(det B)` for `N ≥ v_l(det B)`. -/
theorem card_ker_mod {n : Type*} [Fintype n] [DecidableEq n] (B : Matrix n n ℤ_[l]) (hB : B.det ≠ 0)
    (N : ℕ) (hN : B.det.valuation ≤ N) :
    Nat.card {x : n → ZMod (l ^ N) // (B.map (PadicInt.toZModPow N)) *ᵥ x = 0} =
      l ^ B.det.valuation := by
  classical
  set Bb := B.map (PadicInt.toZModPow N)
  let φ : (n → ZMod (l ^ N)) →+ (n → ZMod (l ^ N)) := (Matrix.toLin' Bb).toAddMonoidHom
  let π : (n → ℤ_[l]) →+ (n → ZMod (l ^ N)) :=
    { toFun := fun v i => PadicInt.toZModPow N (v i)
      map_zero' := by ext; simp
      map_add' := by intros; ext; simp }
  have hπ : Function.Surjective π := fun y =>
    ⟨fun i => (ZMod.ringHom_surjective (PadicInt.toZModPow N) (y i)).choose,
      funext fun i => (ZMod.ringHom_surjective (PadicInt.toZModPow N) (y i)).choose_spec⟩
  have hπB : ∀ v, π (B *ᵥ v) = Bb *ᵥ π v := fun v => by
    ext i; simp [π, Bb, Matrix.mulVec, dotProduct, map_sum]
  -- `l^N` is a multiple of `det B`
  obtain ⟨t, ht⟩ : B.det ∣ (l : ℤ_[l]) ^ N := by
    conv_lhs => rw [PadicInt.unitCoeff_spec hB]
    rw [← Nat.add_sub_cancel' hN, pow_add]
    rw [mul_comm]
    exact mul_dvd_mul_left _ (Units.isUnit _).dvd
  let R : AddSubgroup (n → ℤ_[l]) := (LinearMap.range (Matrix.toLin' B)).toAddSubgroup
  have hker : ((QuotientAddGroup.mk' φ.range).comp π).ker = R := by
    ext w
    simp only [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, QuotientAddGroup.mk'_apply,
      QuotientAddGroup.eq_zero_iff, AddMonoidHom.mem_range, R, Submodule.mem_toAddSubgroup,
      LinearMap.mem_range, Matrix.toLin'_apply, φ, LinearMap.toAddMonoidHom_coe]
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨v, rfl⟩ := hπ y
      have hz : ∀ i, (w - B *ᵥ v) i ∈ Ideal.span {(l : ℤ_[l]) ^ N} := fun i => by
        rw [← PadicInt.ker_toZModPow, RingHom.mem_ker]
        have := congrFun (show π (w - B *ᵥ v) = 0 by rw [map_sub, hπB, hy, sub_self]) i
        simpa [π] using this
      choose c hc using fun i => Ideal.mem_span_singleton'.mp (hz i)
      refine ⟨v + Matrix.adjugate B *ᵥ (t • c), ?_⟩
      rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec,
        Matrix.one_mulVec, smul_smul, ← ht]
      ext i; simp [hc, mul_comm]
    · rintro ⟨v, rfl⟩
      exact ⟨π v, (hπB v).symm⟩
  have hcoker : Nat.card ((n → ZMod (l ^ N)) ⧸ φ.range) = l ^ B.det.valuation := by
    have hs : Function.Surjective ((QuotientAddGroup.mk' φ.range).comp π) :=
      (QuotientAddGroup.mk'_surjective _).comp hπ
    rw [← Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective _ hs).toEquiv, hker]
    have := card_quotient_range (Matrix.toLin' B) (by rwa [LinearMap.det_toLin'])
    rw [LinearMap.det_toLin'] at this
    exact this
  have e1 := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup φ.ker
  have e2 := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup φ.range
  rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivRange φ).toEquiv] at e1
  have hr : 0 < Nat.card φ.range := Nat.card_pos
  have hk : Nat.card φ.ker = Nat.card ((n → ZMod (l ^ N)) ⧸ φ.range) :=
    Nat.eq_of_mul_eq_mul_left hr (by rw [← e1, e2, mul_comm])
  rw [← hcoker, ← hk]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x => by
    simp [φ, AddMonoidHom.mem_ker, Matrix.toLin'_apply])

end RamanujanPetersson.JacAlg


end

-- ===== S4.Def_RP_CoreA_Det =====
section

/-!
# S4-CoreA part S3: kernels of endomorphisms of the divisible group through the Tate matrix

For `φ` with Tate matrix `B` (`IsTateMat`), on an `l`-primary divisible `G`:
* `det B ≠ 0` ⇒ the kernel of `φ` is killed by `l ^ v(det B)` and has `l ^ v(det B)` elements;
* a finite kernel forces `det B ≠ 0`.
-/

set_option autoImplicit false

open scoped Matrix

namespace RamanujanPetersson.CoreA

variable {G : Type*} [AddCommGroup G] {l : ℕ} [Fact l.Prime]

section Det

variable (hdiv : ∀ y : G, ∃ z, l • z = y) {s : ℕ} (b1 : Fin s → G) (hb1 : ∀ i, l • b1 i = 0)
  (h1inj : ∀ d : Fin s → ℤ, ∑ i, d i • b1 i = 0 → ∀ i, (l : ℤ) ∣ d i)
  (h1span : ∀ x : G, l • x = 0 → ∃ d : Fin s → ℤ, ∑ i, d i • b1 i = x)

include h1inj h1span in
theorem IsTateMat.smul_eq_zero_of_map_eq_zero (htors : ∀ x : G, ∃ k, l ^ k • x = 0)
    {φ : AddMonoid.End G} {B : Matrix (Fin s) (Fin s) ℤ_[l]} (h : IsTateMat hdiv b1 hb1 φ B)
    (hdet : B.det ≠ 0) (x : G) (hx : φ x = 0) : l ^ B.det.valuation • x = 0 := by
  obtain ⟨K, hK⟩ := htors x
  obtain ⟨cb, rfl⟩ := exists_tateMap_eq hdiv b1 hb1 h1span K x hK
  have h0 : B.map (PadicInt.toZModPow K) *ᵥ cb = 0 := by
    apply tateMap_injective hdiv b1 hb1 h1inj K
    rw [← h K cb, hx, map_zero]
  have h1 : (B.map (PadicInt.toZModPow K)).det • cb = 0 := by
    have := congrArg (fun A => A *ᵥ cb) (Matrix.adjugate_mul (B.map (PadicInt.toZModPow K)))
    simp only [← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero, Matrix.smul_mulVec, Matrix.one_mulVec] at this
    exact this.symm
  have hdB : (B.map (PadicInt.toZModPow K)).det = PadicInt.toZModPow K (PadicInt.unitCoeff hdet : ℤ_[l]) *
      ((l : ZMod (l ^ K)) ^ B.det.valuation) := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    conv_lhs => rw [PadicInt.unitCoeff_spec hdet]
    rw [map_mul, map_pow, map_natCast]
  have hu : PadicInt.toZModPow K (↑(PadicInt.unitCoeff hdet)⁻¹ : ℤ_[l]) *
      PadicInt.toZModPow K (PadicInt.unitCoeff hdet : ℤ_[l]) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have h2 : ((l : ZMod (l ^ K)) ^ B.det.valuation) • cb = 0 := by
    rw [hdB, mul_smul] at h1
    have := congrArg (fun v => PadicInt.toZModPow K (↑(PadicInt.unitCoeff hdet)⁻¹ : ℤ_[l]) • v) h1
    simpa only [smul_zero, smul_smul, ← mul_assoc, hu, one_mul] using this
  rw [← map_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod (l ^ K)), Nat.cast_pow, h2, map_zero]

include h1inj h1span in
/-- Kernel count: `#ker φ = l ^ v(det B)`. -/
theorem IsTateMat.card_ker (htors : ∀ x : G, ∃ k, l ^ k • x = 0)
    {φ : AddMonoid.End G} {B : Matrix (Fin s) (Fin s) ℤ_[l]} (h : IsTateMat hdiv b1 hb1 φ B)
    (hdet : B.det ≠ 0) : Nat.card {x : G // φ x = 0} = l ^ B.det.valuation := by
  rw [← JacAlg.card_ker_mod B hdet B.det.valuation le_rfl]
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun cb => ⟨tateMap hdiv b1 hb1 _ cb.1, by rw [h, cb.2, map_zero]⟩) ⟨?_, ?_⟩)
  · intro a b hab
    exact Subtype.ext (tateMap_injective hdiv b1 hb1 h1inj _ (congrArg Subtype.val hab))
  · rintro ⟨x, hx⟩
    obtain ⟨cb, hcb⟩ := exists_tateMap_eq hdiv b1 hb1 h1span _ x
      (h.smul_eq_zero_of_map_eq_zero hdiv b1 hb1 h1inj h1span htors hdet x hx)
    refine ⟨⟨cb, ?_⟩, Subtype.ext hcb⟩
    apply tateMap_injective hdiv b1 hb1 h1inj
    rw [← h, hcb, hx, map_zero]

include h1inj in
/-- A finite kernel forces a nonzero determinant. -/
theorem IsTateMat.det_ne_zero {φ : AddMonoid.End G} {B : Matrix (Fin s) (Fin s) ℤ_[l]}
    (h : IsTateMat hdiv b1 hb1 φ B) (hfin : Finite {x : G // φ x = 0}) : B.det ≠ 0 := by
  intro hdet
  haveI := hfin
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  obtain ⟨i0, hi0⟩ : ∃ i, v i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hv0 (funext hcon)
  have hHfin : Finite (AddMonoidHom.ker (φ : G →+ G)) :=
    Finite.of_equiv {x : G // φ x = 0}
      (Equiv.subtypeEquivRight (fun x => (AddMonoidHom.mem_ker (f := (φ : G →+ G))).symm))
  have hm0 : Nat.card (AddMonoidHom.ker (φ : G →+ G)) ≠ 0 := Nat.card_pos.ne'
  have hz : ((Nat.card (AddMonoidHom.ker (φ : G →+ G)) : ℤ_[l]) * v i0) ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.mpr hm0) hi0
  obtain ⟨N, hN⟩ : ∃ N, N = ((Nat.card (AddMonoidHom.ker (φ : G →+ G)) : ℤ_[l]) * v i0).valuation + 1 :=
    ⟨_, rfl⟩
  have hcb : B.map (PadicInt.toZModPow N) *ᵥ (PadicInt.toZModPow N ∘ v) = 0 := by
    ext i
    rw [← RingHom.map_mulVec, hv]
    simp
  have hx : φ (tateMap hdiv b1 hb1 N (PadicInt.toZModPow N ∘ v)) = 0 := by rw [h, hcb, map_zero]
  have hmx : Nat.card (AddMonoidHom.ker (φ : G →+ G)) • tateMap hdiv b1 hb1 N (PadicInt.toZModPow N ∘ v) = 0 := by
    have := congrArg Subtype.val
      (card_nsmul_eq_zero' (G := AddMonoidHom.ker (φ : G →+ G)) (x := ⟨_, AddMonoidHom.mem_ker.mpr hx⟩))
    exact this
  rw [← map_nsmul] at hmx
  have h3 := congrFun (tateMap_injective hdiv b1 hb1 h1inj N (hmx.trans (map_zero _).symm)) i0
  have h4 : PadicInt.toZModPow N ((Nat.card (AddMonoidHom.ker (φ : G →+ G)) : ℤ_[l]) * v i0) = 0 := by
    simpa [nsmul_eq_mul] using h3
  have h5 := (PadicInt.mem_span_pow_iff_le_valuation _ hz N).mp
    (by rw [← PadicInt.ker_toZModPow]; exact RingHom.mem_ker.mpr h4)
  omega

end Det

end RamanujanPetersson.CoreA


end

-- ===== S4.Def_RP_CoreA_Ord =====
section

/-!
# S4-CoreA part O1: the l-part of the order of an automorphism of an elementary abelian l-group

`V` finite with `l • V = 0`, `T` bijective additive, `#V = l ^ D`. Then some `N ≥ 1` has `T^[N] = id` and
`v_l(N) ≤ ⌈log_l D⌉` (`Nat.clog l D`).
-/

set_option autoImplicit false

namespace RamanujanPetersson.CoreA

open Polynomial

theorem exists_pow_eq_one_padicValNat_le {l : ℕ} [hl : Fact l.Prime] {V : Type*} [AddCommGroup V]
    [Module (ZMod l) V] [Finite V] [Nontrivial V] (f : Module.End (ZMod l) V) (hT : Function.Bijective f) {D : ℕ}
    (hD : Nat.card V = l ^ D) :
    ∃ N : ℕ, 0 < N ∧ f ^ N = 1 ∧ padicValNat l N ≤ Nat.clog l D := by
  classical
  have hfu : IsUnit f := (Module.End.isUnit_iff f).mpr hT
  have : Finite (Module.End (ZMod l) V) :=
    Finite.of_injective (fun g : Module.End (ZMod l) V => (g : V → V)) DFunLike.coe_injective
  have : Finite (Module.End (ZMod l) V)ˣ := Finite.of_injective Units.val Units.val_injective
  have : CharP (Module.End (ZMod l) V) l := charP_of_injective_algebraMap' (ZMod l) l
  set u := hfu.unit with hu
  set n := Nat.card (Module.End (ZMod l) V)ˣ with hn
  have hn0 : n ≠ 0 := Nat.card_pos.ne'
  obtain ⟨a, M, hM, hnM⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 l hl.out.ne_one
  have hM0 : M ≠ 0 := by rintro rfl; exact hM (dvd_zero l)
  have hun : u ^ n = 1 := pow_card_eq_one'
  set U : Module.End (ZMod l) V := f ^ M with hU
  have hUa : U ^ (l ^ a) = 1 := by
    have h1 : ((u ^ n : (Module.End (ZMod l) V)ˣ) : Module.End (ZMod l) V) = 1 := by rw [hun]; rfl
    rw [Units.val_pow_eq_pow_val, hnM] at h1
    rw [hU, ← pow_mul, mul_comm]
    simpa [hu] using h1
  have hnil : IsNilpotent (U - 1) := by
    refine ⟨l ^ a, ?_⟩
    rw [sub_pow_char_pow_of_commute l a (Commute.one_right U), hUa, one_pow, sub_self]
  have : Module.Finite (ZMod l) V := Module.Finite.of_finite
  have hfin : Module.finrank (ZMod l) V = D := by
    let _ : Fintype V := Fintype.ofFinite V
    have hc : Fintype.card V = Fintype.card (ZMod l) ^ Module.finrank (ZMod l) V := Module.card_eq_pow_finrank
    rw [← Nat.card_eq_fintype_card, hD, ZMod.card] at hc
    exact (Nat.pow_right_injective hl.out.two_le hc).symm
  have hzero : (U - 1) ^ D = 0 := by
    have hch := IsNilpotent.charpoly_eq_X_pow_finrank hnil
    have hcay := LinearMap.aeval_self_charpoly (U - 1)
    rw [hch, hfin, map_pow, aeval_X] at hcay
    exact hcay
  set k := Nat.clog l D with hk
  have hDk : D ≤ l ^ k := Nat.le_pow_clog hl.out.one_lt D
  have hUk : U ^ (l ^ k) = 1 := by
    have h0 : (U - 1) ^ (l ^ k) = 0 := pow_eq_zero_of_le hDk hzero
    rw [sub_pow_char_pow_of_commute l k (Commute.one_right U), one_pow] at h0
    exact sub_eq_zero.mp h0
  refine ⟨M * l ^ k, Nat.mul_pos (Nat.pos_of_ne_zero hM0) (pow_pos hl.out.pos k), ?_, ?_⟩
  · rw [pow_mul, ← hU, hUk]
  · rw [padicValNat.mul hM0 (pow_ne_zero _ hl.out.ne_zero), padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd hM, zero_add]

/-- **O1.** `V` finite with `l • V = 0`, `T` bijective additive, `#V = l ^ D`: some `N ≥ 1` has `T^[N] = id` and
`v_l(N) ≤ ⌈log_l D⌉`. -/
theorem exists_iterate_eq_id_padicValNat_le {l : ℕ} [hl : Fact l.Prime] {V : Type*} [AddCommGroup V] [Finite V]
    (hV : ∀ x : V, l • x = 0) (T : V →+ V) (hT : Function.Bijective T) {D : ℕ} (hD : Nat.card V = l ^ D) :
    ∃ N : ℕ, 0 < N ∧ (∀ x, T^[N] x = x) ∧ padicValNat l N ≤ Nat.clog l D := by
  rcases subsingleton_or_nontrivial V with hs | hnt
  · exact ⟨1, Nat.one_pos, fun x => Subsingleton.elim _ _, by simp⟩
  let _ : Module (ZMod l) V := AddCommGroup.zmodModule hV
  obtain ⟨N, hN, hpow, hval⟩ := exists_pow_eq_one_padicValNat_le (T.toZModLinearMap l) hT hD
  refine ⟨N, hN, fun x => ?_, hval⟩
  have h := LinearMap.congr_fun hpow x
  rw [Module.End.pow_apply, Module.End.one_apply] at h
  exact h

end RamanujanPetersson.CoreA


end

-- ===== S4.Def_RP_CoreA_Fin =====
section

/-!
# S4-CoreA part F1: `A[l]` is finite

`pi : A →+ A` with every point periodic, `#Fix(pi^m) = l ^ nu m` for `m ≥ 1`, and
`nu m ≤ C + e * v_l(m)`. Then `A[l]` is finite (with an explicit bound).
-/

set_option autoImplicit false

namespace RamanujanPetersson.CoreA

/-- Growth helper: `t * t ≤ 4 * 2 ^ t`. -/
theorem sq_le_four_mul_two_pow (t : ℕ) : t * t ≤ 4 * 2 ^ t := by
  induction t with
  | zero => simp
  | succ n ih =>
    rcases Nat.lt_or_ge n 3 with h | h
    · interval_cases n <;> norm_num
    · rw [pow_succ]
      nlinarith

/-- Absorption: `D ≤ C + e * ⌈log_l D⌉` forces `D ≤ C + e * (8 * (C + e) + 2)`. -/
theorem le_of_le_add_mul_clog {l : ℕ} (hl : 2 ≤ l) {C e D : ℕ} (h : D ≤ C + e * Nat.clog l D) :
    D ≤ C + e * (8 * (C + e) + 2) := by
  set k := Nat.clog l D with hk
  suffices hk' : k ≤ 8 * (C + e) + 2 by
    calc D ≤ C + e * k := h
      _ ≤ C + e * (8 * (C + e) + 2) := by gcongr
  rcases Nat.lt_or_ge k 2 with h2 | h2
  · omega
  have hD : 1 < D := by
    by_contra hD
    have : k = 0 := Nat.clog_of_right_le_one (by omega) l
    omega
  have hlt : l ^ (k - 1) < D := by
    have := Nat.pow_pred_clog_lt_self (b := l) (by omega) hD
    rwa [← hk, Nat.pred_eq_sub_one] at this
  have h2l : 2 ^ (k - 1) ≤ l ^ (k - 1) := Nat.pow_le_pow_left hl _
  have hsq := sq_le_four_mul_two_pow (k - 1)
  clear_value k
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hlt h2l hsq
  by_contra hcon
  rw [not_le] at hcon
  nlinarith

variable {A : Type*} [AddCommGroup A]

/-- Finite sets of `l`-torsion points have bounded size. -/
theorem card_le_of_torsion {l : ℕ} [hl : Fact l.Prime] (pi : A →+ A) (nu : ℕ → ℕ) (C e : ℕ)
    (hper : ∀ x : A, ∃ m, 0 < m ∧ pi^[m] x = x)
    (hfix : ∀ m, 0 < m → Nat.card {x : A // pi^[m] x = x} = l ^ nu m)
    (hnu : ∀ m, 0 < m → nu m ≤ C + e * padicValNat l m) (S : Finset A) (hS : ∀ x ∈ S, l • x = 0) :
    S.card ≤ l ^ (C + e * (8 * (C + e) + 2)) := by
  classical
  choose m hm0 hm using hper
  set N0 := ∏ x ∈ S, m x with hN0
  have hN0pos : 0 < N0 := Finset.prod_pos fun x _ => hm0 x
  have hSfix : ∀ x ∈ S, pi^[N0] x = x := fun x hx =>
    Function.IsPeriodicPt.trans_dvd (f := pi) (hm x) (Finset.dvd_prod_of_mem m hx)
  let V : AddSubgroup A :=
    { carrier := {v | l • v = 0 ∧ pi^[N0] v = v}
      add_mem' := fun {a b} ha hb =>
        ⟨by rw [smul_add, ha.1, hb.1, add_zero], by rw [iterate_map_add, ha.2, hb.2]⟩
      zero_mem' := ⟨smul_zero _, iterate_map_zero pi N0⟩
      neg_mem' := fun {a} ha => by
        refine ⟨by rw [smul_neg, ha.1, neg_zero], ?_⟩
        have h0 : pi^[N0] (-a) + pi^[N0] a = 0 := by
          rw [← iterate_map_add, neg_add_cancel, iterate_map_zero]
        rw [ha.2] at h0
        exact eq_neg_of_add_eq_zero_left h0 }
  have hmemV : ∀ v, v ∈ V ↔ l • v = 0 ∧ pi^[N0] v = v := fun v => Iff.rfl
  have hVpi : ∀ v ∈ V, pi v ∈ V := fun v hv => by
    rw [hmemV] at hv ⊢
    refine ⟨by rw [← map_nsmul, hv.1, map_zero], ?_⟩
    rw [← Function.iterate_succ_apply, Function.iterate_succ_apply', hv.2]
  let T : V →+ V := (pi.comp V.subtype).codRestrict V (fun v => hVpi v.1 v.2)
  have hTcoe : ∀ (n : ℕ) (v : V), ((T^[n] v : V) : A) = pi^[n] (v : A) := by
    intro n
    induction n with
    | zero => intro v; rfl
    | succ n ih =>
      intro v
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
      rfl
  have hTN0 : ∀ v : V, T^[N0] v = v := fun v => Subtype.ext (by rw [hTcoe]; exact v.2.2)
  have hTbij : Function.Bijective T := by
    obtain ⟨n, hn⟩ : ∃ n, N0 = n + 1 := ⟨N0 - 1, by omega⟩
    refine ⟨fun a b hab => ?_, fun v => ⟨T^[n] v, ?_⟩⟩
    · have := congrArg (T^[n]) hab
      rwa [← Function.iterate_succ_apply, ← Function.iterate_succ_apply, Nat.succ_eq_add_one, ← hn, hTN0,
        hTN0] at this
    · rw [← Function.iterate_succ_apply' T n v, Nat.succ_eq_add_one, ← hn, hTN0]
  have hfixN0 : Nat.card {x : A // pi^[N0] x = x} ≠ 0 := by
    rw [hfix N0 hN0pos]; exact pow_ne_zero _ hl.out.ne_zero
  have : Finite {x : A // pi^[N0] x = x} := Nat.finite_of_card_ne_zero hfixN0
  have : Finite V := Finite.of_injective (fun v : V => (⟨v.1, v.2.2⟩ : {x : A // pi^[N0] x = x}))
    (fun a b h => Subtype.ext (Subtype.mk.inj h))
  have hVl : ∀ v : V, l • v = 0 := fun v => Subtype.ext (by simpa using v.2.1)
  let _ : Module (ZMod l) V := AddCommGroup.zmodModule hVl
  have : Module.Finite (ZMod l) V := Module.Finite.of_finite
  set D := Module.finrank (ZMod l) V with hDdef
  have hcardV : Nat.card V = l ^ D := by
    let _ : Fintype V := Fintype.ofFinite V
    have hc : Fintype.card V = Fintype.card (ZMod l) ^ Module.finrank (ZMod l) V := Module.card_eq_pow_finrank
    rw [← Nat.card_eq_fintype_card, ZMod.card] at hc
    exact hc
  obtain ⟨N, hN, hTN, hval⟩ := exists_iterate_eq_id_padicValNat_le hVl T hTbij hcardV
  have hfixN : Nat.card {x : A // pi^[N] x = x} ≠ 0 := by
    rw [hfix N hN]; exact pow_ne_zero _ hl.out.ne_zero
  have : Finite {x : A // pi^[N] x = x} := Nat.finite_of_card_ne_zero hfixN
  have hVle : Nat.card V ≤ Nat.card {x : A // pi^[N] x = x} :=
    Nat.card_le_card_of_injective (fun v : V => (⟨v.1, by rw [← hTcoe, hTN]⟩ : {x : A // pi^[N] x = x}))
      (fun a b h => Subtype.ext (Subtype.mk.inj h))
  rw [hcardV, hfix N hN] at hVle
  have hDnu : D ≤ nu N := (Nat.pow_le_pow_iff_right hl.out.one_lt).mp hVle
  have hDb : D ≤ C + e * (8 * (C + e) + 2) := by
    refine le_of_le_add_mul_clog hl.out.two_le ?_
    calc D ≤ nu N := hDnu
      _ ≤ C + e * padicValNat l N := hnu N hN
      _ ≤ C + e * Nat.clog l D := by gcongr
  have hSV : S.card ≤ Nat.card V := by
    rw [← Nat.card_eq_finsetCard]
    exact Nat.card_le_card_of_injective (fun x : S => (⟨x.1, (hmemV _).mpr ⟨hS x.1 x.2, hSfix x.1 x.2⟩⟩ : V))
      (fun a b h => Subtype.ext (Subtype.mk.inj h))
  calc S.card ≤ Nat.card V := hSV
    _ = l ^ D := hcardV
    _ ≤ l ^ (C + e * (8 * (C + e) + 2)) := Nat.pow_le_pow_right hl.out.pos hDb

/-- **F1.** Under periodicity, the fixed-point counts `l ^ nu m` and the bound `nu m ≤ C + e v_l(m)`,
the `l`-torsion `A[l]` is finite. -/
theorem finite_torsion_of_fix_card {l : ℕ} [hl : Fact l.Prime] (pi : A →+ A) (nu : ℕ → ℕ) (C e : ℕ)
    (hper : ∀ x : A, ∃ m, 0 < m ∧ pi^[m] x = x)
    (hfix : ∀ m, 0 < m → Nat.card {x : A // pi^[m] x = x} = l ^ nu m)
    (hnu : ∀ m, 0 < m → nu m ≤ C + e * padicValNat l m) :
    {x : A | l • x = 0}.Finite := by
  by_contra hinf
  obtain ⟨t, hts, htc⟩ := Set.Infinite.exists_subset_card_eq hinf (l ^ (C + e * (8 * (C + e) + 2)) + 1)
  have := card_le_of_torsion pi nu C e hper hfix hnu t (fun x hx => hts hx)
  omega

end RamanujanPetersson.CoreA


end

-- ===== S4.Def_RP_CoreA_Grow =====
section

/-!
# S4-CoreA part S4: growth of `det (1 - X ^ (l ^ j))` for `X ≡ 1 mod l ^ 2`

In any ring, `X = 1 + l^2 • F` gives `X ^ (l^j) - 1 = (l^j • (1 + l • U)) * (X - 1)` (geometric sums only, no
binomial theorem). For matrices over `ℤ_[l]` this yields
`v det (1 - X ^ (l^j)) = v det (1 - X) + s * j`.
-/

set_option autoImplicit false

open scoped Matrix

open Finset

namespace RamanujanPetersson.CoreA

section Ring

variable {R : Type*} [Ring R] (l : ℕ)

theorem pow_eq_one_add_nsmul {a : ℕ} {Y F : R} (hY : Y = 1 + (l ^ a) • F) (k : ℕ) :
    ∃ Fk : R, Y ^ k = 1 + (l ^ a) • Fk := by
  induction k with
  | zero => exact ⟨0, by simp⟩
  | succ k ih =>
    obtain ⟨Fk, hk⟩ := ih
    refine ⟨F + Fk + Fk * ((l ^ a) • F), ?_⟩
    rw [pow_succ, hk, hY]
    simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, smul_add]
    abel

theorem geom_sum_eq_nsmul {a : ℕ} {Y F : R} (hY : Y = 1 + (l ^ (a + 2)) • F) :
    ∃ U : R, ∑ k ∈ range l, Y ^ k = l • (1 + l • U) := by
  choose Fk hFk using pow_eq_one_add_nsmul l hY
  refine ⟨l ^ a • ∑ k ∈ range l, Fk k, ?_⟩
  rw [sum_congr rfl (fun k _ => hFk k), sum_add_distrib, sum_const, card_range, ← smul_sum,
    smul_add, smul_smul, smul_smul]
  congr 2
  ring

theorem pow_prime_pow_sub_one {X F : R} (hX : X = 1 + (l ^ 2) • F) (j : ℕ) :
    ∃ U : R, X ^ (l ^ j) - 1 = (l ^ j • (1 + l • U)) * (X - 1) ∧
      ∃ Fj : R, X ^ (l ^ j) = 1 + l ^ (j + 2) • Fj := by
  induction j with
  | zero => exact ⟨0, by simp, F, by simpa using hX⟩
  | succ j ih =>
    obtain ⟨U, hU, Fj, hFj⟩ := ih
    obtain ⟨U', hU'⟩ := geom_sum_eq_nsmul l hFj
    have hpow : X ^ (l ^ (j + 1)) = (X ^ (l ^ j)) ^ l := by rw [pow_succ, pow_mul]
    have key : (1 + l • U') * (1 + l • U) = 1 + l • (U + U' + U' * (l • U)) := by
      simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, smul_add]
      abel
    have key2 : (l • (1 + l • U')) * (l ^ j • (1 + l • U)) =
        l ^ (j + 1) • (1 + l • (U + U' + U' * (l • U))) := by
      rw [smul_mul_assoc, mul_smul_comm, smul_smul, key, pow_succ, mul_comm (l ^ j) l]
    refine ⟨U + U' + U' * (l • U), ?_, (1 + l • U') * Fj, ?_⟩
    · rw [hpow, ← geom_sum_mul, hU', hU, ← mul_assoc, key2]
    · have h1 : (X ^ l ^ j) ^ l - 1 = l ^ (j + 1 + 2) • ((1 + l • U') * Fj) := by
        rw [← geom_sum_mul, hU', hFj, add_sub_cancel_left, smul_mul_assoc, mul_smul_comm, smul_smul]
        congr 1
        ring
      rw [hpow, ← h1]
      abel

end Ring

section Matrix

variable (l : ℕ) [hl : Fact l.Prime] {s : ℕ}

theorem det_one_add_nsmul (U : Matrix (Fin s) (Fin s) ℤ_[l]) :
    (1 + l • U).det ≠ 0 ∧ (1 + l • U).det.valuation = 0 := by
  have hl0 : (l : ZMod (l ^ 1)) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr (by rw [pow_one])
  haveI : Fact (1 < l ^ 1) := ⟨by rw [pow_one]; exact hl.out.one_lt⟩
  have h0 : ∀ V : Matrix (Fin s) (Fin s) (ZMod (l ^ 1)), l • V = 0 := by
    intro V
    ext i j
    simp [nsmul_eq_mul, hl0]
  have hmap : PadicInt.toZModPow 1 (1 + l • U).det = 1 := by
    rw [RingHom.map_det, map_add, map_one, map_nsmul, h0, add_zero, Matrix.det_one]
  have hne : (1 + l • U).det ≠ 0 := by
    intro h
    rw [h, map_zero] at hmap
    exact zero_ne_one hmap
  refine ⟨hne, ?_⟩
  by_contra hv
  have hmem := (PadicInt.mem_span_pow_iff_le_valuation _ hne 1).mpr (by omega)
  rw [← PadicInt.ker_toZModPow, RingHom.mem_ker] at hmem
  rw [hmem] at hmap
  exact zero_ne_one hmap

/-- Growth along `l`-power multiples: `v det (1 - X^(l^j)) = v det (1 - X) + s j`. -/
theorem det_one_sub_pow_prime_pow {X F : Matrix (Fin s) (Fin s) ℤ_[l]} (hX : X = 1 + (l ^ 2) • F)
    (hdet : (1 - X).det ≠ 0) (j : ℕ) :
    (1 - X ^ (l ^ j)).det ≠ 0 ∧ (1 - X ^ (l ^ j)).det.valuation = (1 - X).det.valuation + s * j := by
  obtain ⟨U, hU, -⟩ := pow_prime_pow_sub_one l hX j
  have e : 1 - X ^ (l ^ j) = (((l ^ j : ℕ) : ℤ_[l]) • (1 + l • U)) * (1 - X) := by
    rw [Nat.cast_smul_eq_nsmul, ← neg_sub X 1, ← neg_sub (X ^ l ^ j) 1, hU, mul_neg]
  have hdet_e : (1 - X ^ (l ^ j)).det = ((l : ℤ_[l]) ^ j) ^ s * ((1 + l • U).det * (1 - X).det) := by
    rw [e, Matrix.det_mul, Matrix.det_smul, Fintype.card_fin, Nat.cast_pow, mul_assoc]
  obtain ⟨hne, hv0⟩ := det_one_add_nsmul l U
  have hlj : ((l : ℤ_[l]) ^ j) ^ s ≠ 0 := pow_ne_zero _ (pow_ne_zero _ (Nat.cast_ne_zero.mpr hl.out.ne_zero))
  refine ⟨?_, ?_⟩
  · rw [hdet_e]
    exact mul_ne_zero hlj (mul_ne_zero hne hdet)
  · rw [hdet_e, PadicInt.valuation_mul hlj (mul_ne_zero hne hdet), PadicInt.valuation_mul hne hdet, hv0,
      ← pow_mul, PadicInt.valuation_pow, PadicInt.valuation_p]
    ring

/-- A matrix that is `1` modulo `l ^ k` has the form `1 + l^k • F`. -/
theorem exists_eq_one_add_nsmul (A : Matrix (Fin s) (Fin s) ℤ_[l]) (k : ℕ)
    (hA : A.map (PadicInt.toZModPow k) = 1) : ∃ F : Matrix (Fin s) (Fin s) ℤ_[l], A = 1 + (l ^ k) • F := by
  have h : ∀ i j, ∃ f : ℤ_[l], (A - 1) i j = (l : ℤ_[l]) ^ k * f := by
    intro i j
    have hmem : (A - 1) i j ∈ RingHom.ker (PadicInt.toZModPow (p := l) k) := by
      rw [RingHom.mem_ker, Matrix.sub_apply, map_sub]
      have h1 := congrFun (congrFun hA i) j
      rw [Matrix.map_apply] at h1
      rw [h1, Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at hmem
    exact hmem
  choose F hF using h
  refine ⟨Matrix.of F, ?_⟩
  ext i j
  have := hF i j
  rw [Matrix.sub_apply] at this
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, nsmul_eq_mul, Nat.cast_pow, ← this]
  abel

end Matrix

end RamanujanPetersson.CoreA


end

-- ===== S4.Def_RP_CoreA_Rank =====
section

/-!
# S4-CoreA part Rank: helpers for the main assembly

`D = n • A` with the restriction `endD pi n` of `pi`; fixed points of `pi ^ m` on `D` versus `A`
(`#Fix_D ≤ #Fix_A ≤ #Fix_D * #A[n]`); the `l`-rank of an elementary abelian group; a common period
killing `A[l^k]`; and the rank identity `s = e` from the growth of fixed-point counts.
-/

set_option autoImplicit false

open scoped Matrix

namespace RamanujanPetersson.CoreA

variable {A : Type*} [AddCommGroup A]

/-- `pi` restricted to `n • A`. -/
def endD (pi : A →+ A) (n : ℕ) : AddMonoid.End (smulHom A n).range :=
  (pi.comp (smulHom A n).range.subtype).codRestrict _ (fun x => map_mem_range_smulHom pi x.2)

theorem endD_pow_apply (pi : A →+ A) (n m : ℕ) (x : (smulHom A n).range) :
    ((endD pi n ^ m) x : A) = pi^[m] (x : A) := by
  induction m generalizing x with
  | zero => rfl
  | succ m ih =>
    rw [pow_succ, Function.iterate_succ_apply]
    exact ih (endD pi n x)

theorem endD_fix_iff (pi : A →+ A) (n m : ℕ) (x : (smulHom A n).range) :
    (1 - endD pi n ^ m) x = 0 ↔ pi^[m] (x : A) = x := by
  show x - (endD pi n ^ m) x = 0 ↔ pi^[m] (x : A) = x
  rw [sub_eq_zero, eq_comm, Subtype.ext_iff, endD_pow_apply]

theorem iterate_nsmul (pi : A →+ A) (m k : ℕ) (x : A) : pi^[m] (k • x) = k • pi^[m] x := by
  induction m generalizing x with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, map_nsmul, ih]

/-- Fixed points on `D` are fixed points on `A`. -/
def fixVal (pi : A →+ A) (n m : ℕ) (x : {y : (smulHom A n).range // (1 - endD pi n ^ m) y = 0}) :
    {y : A // pi^[m] y = y} :=
  ⟨x.1, (endD_fix_iff pi n m x.1).mp x.2⟩

theorem fixVal_injective (pi : A →+ A) (n m : ℕ) : Function.Injective (fixVal pi n m) := by
  intro a b h
  have h' := congrArg Subtype.val h
  exact Subtype.ext (Subtype.ext h')

theorem card_fix_le (pi : A →+ A) (n m : ℕ) [Finite {x : A // pi^[m] x = x}] :
    Finite {x : (smulHom A n).range // (1 - endD pi n ^ m) x = 0} ∧
    Nat.card {x : (smulHom A n).range // (1 - endD pi n ^ m) x = 0} ≤ Nat.card {x : A // pi^[m] x = x} :=
  ⟨Finite.of_injective _ (fixVal_injective pi n m), Nat.card_le_card_of_injective _ (fixVal_injective pi n m)⟩

/-- `x ↦ n • x` from fixed points on `A` to fixed points on `n • A`. -/
def fixSmul (pi : A →+ A) (n m : ℕ) (x : {y : A // pi^[m] y = y}) :
    {y : (smulHom A n).range // (1 - endD pi n ^ m) y = 0} :=
  ⟨⟨n • x.1, mem_range_smulHom.mpr ⟨x.1, rfl⟩⟩, (endD_fix_iff pi n m _).mpr (by
    show pi^[m] (n • x.1) = n • x.1
    rw [iterate_nsmul, x.2])⟩

theorem fixSmul_val (pi : A →+ A) (n m : ℕ) (x : {y : A // pi^[m] y = y}) :
    ((fixSmul pi n m x).1 : A) = n • x.1 := rfl

theorem card_fix_le_mul (pi : A →+ A) (n m : ℕ)
    [Finite {x : (smulHom A n).range // (1 - endD pi n ^ m) x = 0}] [Finite {x : A // n • x = 0}] :
    Nat.card {x : A // pi^[m] x = x} ≤
      Nat.card {x : (smulHom A n).range // (1 - endD pi n ^ m) x = 0} * Nat.card {x : A // n • x = 0} := by
  have : Nonempty {x : A // pi^[m] x = x} := ⟨⟨0, Function.iterate_fixed (map_zero pi) m⟩⟩
  obtain ⟨σ, hσ⟩ : ∃ σ : {y : (smulHom A n).range // (1 - endD pi n ^ m) y = 0} → {x : A // pi^[m] x = x},
      ∀ x, fixSmul pi n m (σ (fixSmul pi n m x)) = fixSmul pi n m x :=
    ⟨Function.invFun _, fun x => Function.invFun_eq ⟨x, rfl⟩⟩
  have hker : ∀ x : {x : A // pi^[m] x = x}, n • (x.1 - (σ (fixSmul pi n m x)).1) = 0 := by
    intro x
    have h := congrArg (fun y => ((y.1 : (smulHom A n).range) : A)) (hσ x)
    simp only [fixSmul_val] at h
    rw [smul_sub, h, sub_self]
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_injective
    (fun x => (fixSmul pi n m x, (⟨x.1 - (σ (fixSmul pi n m x)).1, hker x⟩ : {x : A // n • x = 0}))) ?_
  intro x y hxy
  simp only [Prod.mk.injEq, Subtype.mk.injEq] at hxy
  obtain ⟨h1, h2⟩ := hxy
  rw [h1] at h2
  exact Subtype.ext (sub_left_inj.mp h2)

/-- An elementary abelian `l`-group has order a power of `l`. -/
theorem exists_card_eq_pow_aux {l : ℕ} [Fact l.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod l) V]
    [Finite V] : ∃ s, Nat.card V = l ^ s := by
  have : Module.Finite (ZMod l) V := Module.Finite.of_finite
  let _ : Fintype V := Fintype.ofFinite V
  have hc : Fintype.card V = Fintype.card (ZMod l) ^ Module.finrank (ZMod l) V := Module.card_eq_pow_finrank
  exact ⟨Module.finrank (ZMod l) V, by rw [Nat.card_eq_fintype_card, hc, ZMod.card]⟩

theorem exists_card_eq_pow {l : ℕ} [Fact l.Prime] {V : Type*} [AddCommGroup V] [Finite V]
    (hV : ∀ x : V, l • x = 0) : ∃ s, Nat.card V = l ^ s := by
  let _ : Module (ZMod l) V := AddCommGroup.zmodModule hV
  exact exists_card_eq_pow_aux

/-- `D[l] → A[l]`. -/
def kerToTors (n l : ℕ) (x : (smulHom (smulHom A n).range l).ker) : {y : A // l • y = 0} :=
  ⟨((x : (smulHom A n).range) : A), by
    have h := x.2
    rw [AddMonoidHom.mem_ker, smulHom_apply] at h
    rw [← AddSubgroup.coe_nsmul, h, AddSubgroup.coe_zero]⟩

theorem kerToTors_injective (n l : ℕ) : Function.Injective (kerToTors (A := A) n l) := by
  intro a b h
  have h' := congrArg Subtype.val h
  exact Subtype.ext (Subtype.ext h')

theorem exists_card_ker_eq_pow {l : ℕ} [Fact l.Prime] (hfin : {x : A | l • x = 0}.Finite) (n : ℕ) :
    Finite (smulHom (smulHom A n).range l).ker ∧ ∃ s, Nat.card (smulHom (smulHom A n).range l).ker = l ^ s := by
  have : Finite {y : A // l • y = 0} := hfin.to_subtype
  have hK : Finite (smulHom (smulHom A n).range l).ker := Finite.of_injective _ (kerToTors_injective n l)
  refine ⟨hK, exists_card_eq_pow (fun x => Subtype.ext ?_)⟩
  have h := x.2
  rw [AddMonoidHom.mem_ker, smulHom_apply] at h
  rw [AddSubgroup.coe_nsmul, h, AddSubgroup.coe_zero]

/-- A common period of `pi` on the finite set `A[l^k]`. -/
theorem exists_period_torsion {l : ℕ} (pi : A →+ A) (hper : ∀ x : A, ∃ m, 0 < m ∧ pi^[m] x = x) (k : ℕ)
    (hfin : {x : A | l ^ k • x = 0}.Finite) : ∃ m0, 0 < m0 ∧ ∀ x : A, l ^ k • x = 0 → pi^[m0] x = x := by
  classical
  choose per hper0 hper1 using hper
  refine ⟨∏ x ∈ hfin.toFinset, per x, Finset.prod_pos (fun x _ => hper0 x), fun x hx => ?_⟩
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem per (hfin.mem_toFinset.mpr hx)
  rw [hc]
  exact Function.IsPeriodicPt.mul_const (f := pi) (hper1 x) c

section Mat

variable {G : Type*} [AddCommGroup G] {l : ℕ} (hdiv : ∀ y : G, ∃ z, l • z = y) {s : ℕ} (b1 : Fin s → G)
  (hb1 : ∀ i, l • b1 i = 0) (h1inj : ∀ d : Fin s → ℤ, ∑ i, d i • b1 i = 0 → ∀ i, (l : ℤ) ∣ d i) [Fact l.Prime]

include h1inj in
/-- If `φ` is the identity on `G[l^k]`, its Tate matrix is `1` modulo `l^k`. -/
theorem IsTateMat.map_eq_one {φ : AddMonoid.End G} {M : Matrix (Fin s) (Fin s) ℤ_[l]}
    (h : IsTateMat hdiv b1 hb1 φ M) (k : ℕ) (hφ : ∀ x : G, l ^ k • x = 0 → φ x = x) :
    M.map (PadicInt.toZModPow k) = 1 := by
  have hc : ∀ cb : Fin s → ZMod (l ^ k), M.map (PadicInt.toZModPow k) *ᵥ cb = cb := fun cb =>
    tateMap_injective hdiv b1 hb1 h1inj k ((h k cb).symm.trans (hφ _ (tateMap_smul_eq_zero hdiv b1 hb1 k cb)))
  ext i j
  have := congrFun (hc (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one, Matrix.one_apply, Pi.single_apply] using this

end Mat

/-- **Rank identity.** Two-sided control `w n ≤ nu n ≤ w n + K0` of the fixed-point exponents by
`w n = v det (1 - M^n)`, together with linear growth `nu (d l^j) = C' + e j`, forces `s = e`. -/
theorem rank_eq_of_growth {l : ℕ} [hl : Fact l.Prime] {s : ℕ} (M F : Matrix (Fin s) (Fin s) ℤ_[l]) (m0 : ℕ)
    (hm0 : 0 < m0) (hM : M ^ m0 = 1 + (l ^ 2) • F) (nu : ℕ → ℕ) (e K0 : ℕ)
    (hw : ∀ n, 0 < n → (1 - M ^ n).det ≠ 0 ∧ (1 - M ^ n).det.valuation ≤ nu n ∧
      nu n ≤ (1 - M ^ n).det.valuation + K0)
    (hgrow : ∃ d0, 0 < d0 ∧ ∀ d, 0 < d → d0 ∣ d → ∃ C', ∀ j, nu (d * l ^ j) = C' + e * j) : s = e := by
  obtain ⟨d0, hd0, hg⟩ := hgrow
  obtain ⟨C', hC'⟩ := hg (d0 * m0) (Nat.mul_pos hd0 hm0) (dvd_mul_right d0 m0)
  obtain ⟨Fk, hFk⟩ := pow_eq_one_add_nsmul l hM d0
  have hX : M ^ (d0 * m0) = 1 + (l ^ 2) • Fk := by
    rw [show d0 * m0 = m0 * d0 from mul_comm _ _, pow_mul, hFk]
  have hdet := (hw (d0 * m0) (Nat.mul_pos hd0 hm0)).1
  have key : ∀ j, (1 - M ^ (d0 * m0 * l ^ j)).det.valuation = (1 - M ^ (d0 * m0)).det.valuation + s * j := by
    intro j
    rw [show M ^ (d0 * m0 * l ^ j) = (M ^ (d0 * m0)) ^ (l ^ j) from pow_mul M (d0 * m0) (l ^ j)]
    exact (det_one_sub_pow_prime_pow l hX hdet j).2
  have hb : ∀ j, (1 - M ^ (d0 * m0)).det.valuation + s * j ≤ C' + e * j ∧
      C' + e * j ≤ (1 - M ^ (d0 * m0)).det.valuation + s * j + K0 := by
    intro j
    have hpos : 0 < d0 * m0 * l ^ j := Nat.mul_pos (Nat.mul_pos hd0 hm0) (pow_pos hl.out.pos j)
    obtain ⟨-, h1, h2⟩ := hw _ hpos
    rw [key, hC'] at h1 h2
    exact ⟨h1, h2⟩
  obtain ⟨h0a, h0b⟩ := hb 0
  obtain ⟨h1a, h1b⟩ := hb (K0 + 1)
  rcases lt_trichotomy s e with h | h | h
  · have h2 : (s + 1) * (K0 + 1) ≤ e * (K0 + 1) := by gcongr; omega
    nlinarith
  · exact h
  · have h2 : (e + 1) * (K0 + 1) ≤ s * (K0 + 1) := by gcongr; omega
    nlinarith

end RamanujanPetersson.CoreA


end

-- ===== S4.Def_RP_CoreA_Main =====
section

/-!
# S4-CoreA part Main: the Tate module of an `l`-primary group with a Frobenius

Abstract form of Core A. `A` is `l`-primary torsion, `pi : A →+ A` has finite orbits, the fixed points of
`pi ^ m` number `l ^ nu m`, `nu m ≤ C + e v_l(m)`, and `nu (d l^j) = C' + e j` along `d0 ∣ d`. Then
`D = l^k0 A` is divisible with `A ⧸ D` finite (the part `Phi`), `T_l D` is free of rank `e` over `ℤ_[l]`
(coordinates `tateMap`, Frobenius matrix `M`), `v det (1 - M^n)` equals `nu n` up to the bounded `Phi`
contribution and exactly when `Phi = 0`, and `Phi = 0` iff `A` is `l`-divisible iff `#A[l] = l ^ e`.
-/

set_option autoImplicit false

open scoped Matrix

namespace RamanujanPetersson.CoreA

variable {A : Type*} [AddCommGroup A]

theorem torsD {l : ℕ} (htors : ∀ x : A, ∃ k, l ^ k • x = 0) (n : ℕ) :
    ∀ x : (smulHom A n).range, ∃ k, l ^ k • x = 0 := fun x => by
  obtain ⟨k, hk⟩ := htors x
  exact ⟨k, Subtype.ext (by rw [AddSubgroup.coe_nsmul, hk, AddSubgroup.coe_zero])⟩

/-- On `D = n • A` every fixed point of `pi ^ m` on `A` is one on `D` when `D = A`. -/
theorem card_fix_eq_of_top (pi : A →+ A) (n m : ℕ) (htop : (smulHom A n).range = ⊤) :
    Nat.card {x : (smulHom A n).range // (1 - endD pi n ^ m) x = 0} = Nat.card {x : A // pi^[m] x = x} := by
  refine Nat.card_congr (Equiv.ofBijective _ ⟨fixVal_injective pi n m, fun y => ?_⟩)
  have hy : y.1 ∈ (smulHom A n).range := by rw [htop]; exact AddSubgroup.mem_top _
  exact ⟨⟨⟨y.1, hy⟩, (endD_fix_iff pi n m _).mpr y.2⟩, rfl⟩

section Top

variable {l k0 : ℕ}
  (hk0 : ∀ j : ℕ, ∀ y : A, l • y = 0 → (∃ a, l ^ k0 • a = y) → ∃ b, l ^ (k0 + j) • b = y)
  (htors : ∀ x : A, ∃ k, l ^ k • x = 0)
include hk0 htors

theorem divD : ∀ y : (smulHom A (l ^ k0)).range, ∃ z, l • z = y := by
  intro y
  obtain ⟨z, hz, hzy⟩ := divisible hk0 htors 1 y y.2
  exact ⟨⟨z, hz⟩, Subtype.ext (by rw [AddSubgroup.coe_nsmul, ← hzy, pow_one])⟩

/-- `Phi = 0` (that is, `D = A`) iff `A` is `l`-divisible. -/
theorem range_eq_top_iff_divisible : (smulHom A (l ^ k0)).range = ⊤ ↔ ∀ y : A, ∃ z, l • z = y := by
  constructor
  · intro htop y
    obtain ⟨z, -, hz⟩ := divisible hk0 htors 1 y (by rw [htop]; exact AddSubgroup.mem_top y)
    exact ⟨z, by rw [← hz, pow_one]⟩
  · intro hd
    have hpow : ∀ k (y : A), ∃ z, l ^ k • z = y := by
      intro k
      induction k with
      | zero => exact fun y => ⟨y, by rw [pow_zero, one_smul]⟩
      | succ k ih =>
        intro y
        obtain ⟨z, hz⟩ := hd y
        obtain ⟨w, hw⟩ := ih z
        exact ⟨w, by rw [pow_succ', mul_smul, hw, hz]⟩
    exact (AddSubgroup.eq_top_iff' _).mpr fun x => mem_range_smulHom.mpr (hpow k0 x)

/-- `Phi = 0` iff `#A[l] = l ^ s`, where `#D[l] = l ^ s`. -/
theorem card_tors_iff [Fact l.Prime] (hfin : {x : A | l • x = 0}.Finite) {s : ℕ}
    (hs : Nat.card (smulHom (smulHom A (l ^ k0)).range l).ker = l ^ s) :
    Nat.card {x : A // l • x = 0} = l ^ s ↔ (smulHom A (l ^ k0)).range = ⊤ := by
  have : Finite {y : A // l • y = 0} := hfin.to_subtype
  constructor
  · intro hc
    have hbij := (kerToTors_injective (A := A) (l ^ k0) l).bijective_of_nat_card_le (by rw [hc, hs])
    rw [AddSubgroup.eq_top_iff']
    refine mem_of_torsion_le hk0 htors (fun x hx => ?_)
    obtain ⟨y, hy⟩ := hbij.2 ⟨x, hx⟩
    have hyx : ((y : (smulHom A (l ^ k0)).range) : A) = x := congrArg Subtype.val hy
    rw [← hyx]
    exact (y : (smulHom A (l ^ k0)).range).2
  · intro htop
    rw [← hs]
    refine (Nat.card_congr (Equiv.ofBijective _ ⟨kerToTors_injective (l ^ k0) l, fun y => ?_⟩)).symm
    have hy : y.1 ∈ (smulHom A (l ^ k0)).range := by rw [htop]; exact AddSubgroup.mem_top _
    refine ⟨⟨⟨y.1, hy⟩, ?_⟩, rfl⟩
    rw [AddMonoidHom.mem_ker, smulHom_apply]
    exact Subtype.ext (by rw [AddSubgroup.coe_nsmul, AddSubgroup.coe_zero]; exact y.2)

end Top

/-- **Core A (abstract form).** See the module docstring. -/
theorem tate_rank {l : ℕ} [hl : Fact l.Prime] (pi : A →+ A) (nu : ℕ → ℕ) (C e : ℕ)
    (htors : ∀ x : A, ∃ k, l ^ k • x = 0)
    (hper : ∀ x : A, ∃ m, 0 < m ∧ pi^[m] x = x)
    (hfix : ∀ m, 0 < m → Nat.card {x : A // pi^[m] x = x} = l ^ nu m)
    (hnu : ∀ m, 0 < m → nu m ≤ C + e * padicValNat l m)
    (hgrow : ∃ d0, 0 < d0 ∧ ∀ d, 0 < d → d0 ∣ d → ∃ C', ∀ j, nu (d * l ^ j) = C' + e * j) :
    ∃ (k0 : ℕ) (hdiv : ∀ y : (smulHom A (l ^ k0)).range, ∃ z, l • z = y)
      (b1 : Fin e → (smulHom A (l ^ k0)).range) (hb1 : ∀ i, l • b1 i = 0) (M : Matrix (Fin e) (Fin e) ℤ_[l]),
      (∀ d : Fin e → ℤ, ∑ i, d i • b1 i = 0 → ∀ i, (l : ℤ) ∣ d i) ∧
      (∀ x : (smulHom A (l ^ k0)).range, l • x = 0 → ∃ d : Fin e → ℤ, ∑ i, d i • b1 i = x) ∧
      IsTateMat hdiv b1 hb1 (endD pi (l ^ k0)) M ∧
      Finite (A ⧸ (smulHom A (l ^ k0)).range) ∧
      (∃ K0, ∀ n, 0 < n → (1 - M ^ n).det ≠ 0 ∧ (1 - M ^ n).det.valuation ≤ nu n ∧
        nu n ≤ (1 - M ^ n).det.valuation + K0) ∧
      ((smulHom A (l ^ k0)).range = ⊤ ↔ ∀ y : A, ∃ z, l • z = y) ∧
      (Nat.card {x : A // l • x = 0} = l ^ e ↔ (smulHom A (l ^ k0)).range = ⊤) ∧
      ((smulHom A (l ^ k0)).range = ⊤ → ∀ n, 0 < n → (1 - M ^ n).det.valuation = nu n) := by
  have hfin := finite_torsion_of_fix_card pi nu C e hper hfix hnu
  obtain ⟨k0, hk0⟩ := exists_stable_torsion hfin
  obtain ⟨-, s, hs⟩ := exists_card_ker_eq_pow hfin (l ^ k0)
  obtain ⟨b1, hb1, h1inj, h1span⟩ := exists_level_one_basis hs
  have hdiv := divD hk0 htors
  obtain ⟨M, hM⟩ := exists_isTateMat hdiv b1 hb1 h1inj h1span (endD pi (l ^ k0))
  have htorsD := torsD htors (l ^ k0)
  have : Finite {x : A // l ^ k0 • x = 0} := (finite_torsion_pow hfin k0).to_subtype
  obtain ⟨K0, hw⟩ : ∃ K0, ∀ n, 0 < n → (1 - M ^ n).det ≠ 0 ∧ (1 - M ^ n).det.valuation ≤ nu n ∧
      nu n ≤ (1 - M ^ n).det.valuation + K0 := by
    refine ⟨Nat.card {x : A // l ^ k0 • x = 0}, fun n hn => ?_⟩
    have hA := hfix n hn
    have : Finite {x : A // pi^[n] x = x} :=
      Nat.finite_of_card_ne_zero (by rw [hA]; exact pow_ne_zero _ hl.out.ne_zero)
    obtain ⟨hDfin, hDle⟩ := card_fix_le pi (l ^ k0) n
    have hdet := (hM.one_sub_pow hdiv b1 hb1 n).det_ne_zero hdiv b1 hb1 h1inj hDfin
    have hcard := (hM.one_sub_pow hdiv b1 hb1 n).card_ker hdiv b1 hb1 h1inj h1span htorsD hdet
    have hup := card_fix_le_mul pi (l ^ k0) n
    rw [hcard, hA] at hup
    rw [hcard, hA] at hDle
    refine ⟨hdet, (Nat.pow_le_pow_iff_right hl.out.one_lt).mp hDle, ?_⟩
    refine (Nat.pow_le_pow_iff_right hl.out.one_lt).mp (hup.trans ?_)
    rw [pow_add]
    exact Nat.mul_le_mul le_rfl (Nat.lt_pow_self hl.out.one_lt).le
  obtain ⟨m0, hm0, hm0x⟩ := exists_period_torsion pi hper 2 (finite_torsion_pow hfin 2)
  have hmap := (hM.pow hdiv b1 hb1 m0).map_eq_one hdiv b1 hb1 h1inj 2 (fun x hx => Subtype.ext (by
    rw [endD_pow_apply]
    exact hm0x _ (by rw [← AddSubgroup.coe_nsmul, hx, AddSubgroup.coe_zero])))
  obtain ⟨F, hF⟩ := exists_eq_one_add_nsmul l (M ^ m0) 2 hmap
  have hse : s = e := rank_eq_of_growth M F m0 hm0 hF nu e K0 hw hgrow
  subst hse
  refine ⟨k0, hdiv, b1, hb1, M, h1inj, h1span, hM, finite_quotient hk0 htors hfin, ⟨K0, hw⟩,
    range_eq_top_iff_divisible hk0 htors, card_tors_iff hk0 htors hfin hs, fun htop n hn => ?_⟩
  have hcard := (hM.one_sub_pow hdiv b1 hb1 n).card_ker hdiv b1 hb1 h1inj h1span htorsD (hw n hn).1
  rw [card_fix_eq_of_top pi (l ^ k0) n htop, hfix n hn] at hcard
  exact (Nat.pow_right_injective hl.out.two_le hcard).symm

end RamanujanPetersson.CoreA


end

-- ===== S4.Def_RP_CoreA_Val =====
section

/-!
# S4-CoreA part V1: norms of `x ^ n - 1` in an ultrametric normed field

`K` a normed field with an ultrametric norm, `l` prime with `0 < ‖l‖ < 1`.
* `norm_pow_sub_one_eq`: `‖x - 1‖ < ‖n‖ → ‖x ^ n - 1‖ = ‖n‖ ‖x - 1‖`.
* `exists_norm_pow_sub_one_eq`: for `β` with no `β ^ N = 1` (`N ≥ 1`) and some `‖β ^ M - 1‖ < 1`, there are
  `d0 ≥ 1`, `r > 0` with `‖β ^ (d0 n) - 1‖ = r ‖n‖` for all `n ≥ 1` and `r ‖N‖ ≤ ‖β ^ N - 1‖` for all `N ≥ 1`.
-/

set_option autoImplicit false

namespace RamanujanPetersson.CoreA

open Finset

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

theorem norm_eq_one_of_norm_sub_one_lt_one {x : K} (h : ‖x - 1‖ < 1) : ‖x‖ = 1 := by
  have hx : x = (x - 1) + 1 := by ring
  have hne : ‖x - 1‖ ≠ ‖(1 : K)‖ := by rw [norm_one]; exact h.ne
  rw [hx, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, norm_one, max_eq_right h.le]

theorem norm_geom_sum_le_one {x : K} (hx : ‖x‖ = 1) (n : ℕ) : ‖∑ i ∈ range n, x ^ i‖ ≤ 1 :=
  IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one
    (fun i _ => by rw [norm_pow, hx, one_pow])

theorem norm_pow_sub_one_le {x : K} (hx : ‖x‖ = 1) (n : ℕ) : ‖x ^ n - 1‖ ≤ ‖x - 1‖ := by
  rw [← geom_sum_mul, norm_mul]
  calc ‖∑ i ∈ range n, x ^ i‖ * ‖x - 1‖ ≤ 1 * ‖x - 1‖ :=
        mul_le_mul_of_nonneg_right (norm_geom_sum_le_one hx n) (norm_nonneg _)
    _ = ‖x - 1‖ := one_mul _

omit [IsUltrametricDist K] in
theorem geom_sum_eq_natCast_add (x : K) (n : ℕ) :
    ∑ i ∈ range n, x ^ i = (n : K) + ∑ i ∈ range n, (x ^ i - 1) := by
  rw [sum_sub_distrib]; simp

theorem norm_geom_sum_sub_le {x : K} (hx : ‖x‖ = 1) (n : ℕ) :
    ‖∑ i ∈ range n, (x ^ i - 1)‖ ≤ ‖x - 1‖ :=
  IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _)
    (fun i _ => norm_pow_sub_one_le hx i)

/-- `‖x - 1‖ < ‖n‖` gives `‖x ^ n - 1‖ = ‖n‖ ‖x - 1‖`. -/
theorem norm_pow_sub_one_eq {x : K} {n : ℕ} (h : ‖x - 1‖ < ‖(n : K)‖) :
    ‖x ^ n - 1‖ = ‖(n : K)‖ * ‖x - 1‖ := by
  have hn1 : ‖(n : K)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one K n
  have hx : ‖x‖ = 1 := norm_eq_one_of_norm_sub_one_lt_one (lt_of_lt_of_le h hn1)
  have hT := lt_of_le_of_lt (norm_geom_sum_sub_le hx n) h
  have hS : ‖∑ i ∈ range n, x ^ i‖ = ‖(n : K)‖ := by
    rw [geom_sum_eq_natCast_add, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hT.ne',
      max_eq_left hT.le]
  rw [← geom_sum_mul, norm_mul, hS]

theorem norm_pow_sub_one_le_mul_max {x : K} (h : ‖x - 1‖ < 1) (n : ℕ) :
    ‖x ^ n - 1‖ ≤ ‖x - 1‖ * max ‖(n : K)‖ ‖x - 1‖ := by
  have hx := norm_eq_one_of_norm_sub_one_lt_one h
  rw [← geom_sum_mul, norm_mul, mul_comm, geom_sum_eq_natCast_add]
  exact mul_le_mul_of_nonneg_left
    ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max le_rfl (norm_geom_sum_sub_le hx n)))
    (norm_nonneg _)

theorem norm_natCast_eq_one_of_not_dvd {l : ℕ} (hl : l.Prime) (hl1 : ‖(l : K)‖ < 1) {n : ℕ}
    (hn : ¬ l ∣ n) : ‖(n : K)‖ = 1 := by
  refine le_antisymm (IsUltrametricDist.norm_natCast_le_one K n) (not_lt.mp fun hlt => ?_)
  obtain ⟨u, v, huv⟩ : IsCoprime (l : ℤ) (n : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr (hl.coprime_iff_not_dvd.mpr hn)
  have h1 : (u : K) * (l : K) + (v : K) * (n : K) = 1 := by
    have := congrArg (Int.cast : ℤ → K) huv
    push_cast at this
    exact this
  have hlt1 : ‖(u : K) * (l : K) + (v : K) * (n : K)‖ < 1 := by
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)
    · rw [norm_mul]
      exact mul_lt_one_of_nonneg_of_lt_one_right (IsUltrametricDist.norm_intCast_le_one K u)
        (norm_nonneg _) hl1
    · rw [norm_mul]
      exact mul_lt_one_of_nonneg_of_lt_one_right (IsUltrametricDist.norm_intCast_le_one K v)
        (norm_nonneg _) hlt
  rw [h1, norm_one] at hlt1
  exact lt_irrefl _ hlt1

theorem norm_natCast_eq_pow_padicValNat {l : ℕ} (hl : l.Prime) (hl1 : ‖(l : K)‖ < 1) {N : ℕ} (hN : N ≠ 0) :
    ‖(N : K)‖ = ‖(l : K)‖ ^ padicValNat l N := by
  have := Fact.mk hl
  obtain ⟨a, n', hn', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN l hl.ne_one
  have hn0 : n' ≠ 0 := by rintro rfl; exact hn' (dvd_zero l)
  rw [padicValNat.mul (pow_ne_zero _ hl.ne_zero) hn0, padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd hn', add_zero, Nat.cast_mul, Nat.cast_pow, norm_mul, norm_pow,
    norm_natCast_eq_one_of_not_dvd hl hl1 hn', mul_one]

theorem norm_pow_prime_pow_sub_one {l : ℕ} {z : K} (hz : ‖z - 1‖ < ‖(l : K)‖) (a : ℕ) :
    ‖z ^ (l ^ a) - 1‖ = ‖(l : K)‖ ^ a * ‖z - 1‖ := by
  have hl1 : ‖(l : K)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one K l
  induction a with
  | zero => simp
  | succ a ih =>
    have hlt : ‖z ^ (l ^ a) - 1‖ < ‖(l : K)‖ := by
      rw [ih]
      calc ‖(l : K)‖ ^ a * ‖z - 1‖ ≤ 1 * ‖z - 1‖ :=
            mul_le_mul_of_nonneg_right (pow_le_one₀ (norm_nonneg _) hl1) (norm_nonneg _)
        _ < ‖(l : K)‖ := by rw [one_mul]; exact hz
    rw [pow_succ l a, pow_mul, norm_pow_sub_one_eq hlt, ih, pow_succ ‖(l : K)‖ a]
    ring

/-- **V1.** -/
theorem exists_norm_pow_sub_one_eq {l : ℕ} (hl : l.Prime) (hl0 : (l : K) ≠ 0) (hl1 : ‖(l : K)‖ < 1) {β : K}
    (hβ : ∀ N : ℕ, 0 < N → β ^ N ≠ 1) {M : ℕ} (hM : 0 < M) (hM1 : ‖β ^ M - 1‖ < 1) :
    ∃ d0 : ℕ, 0 < d0 ∧ ∃ r : ℝ, 0 < r ∧ (∀ n : ℕ, 0 < n → ‖β ^ (d0 * n) - 1‖ = r * ‖(n : K)‖) ∧
      (∀ N : ℕ, 0 < N → r * ‖(N : K)‖ ≤ ‖β ^ N - 1‖) := by
  obtain ⟨x, hx⟩ : ∃ x, x = β ^ M := ⟨_, rfl⟩
  rw [← hx] at hM1
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ρ = max ‖(l : K)‖ ‖x - 1‖ := ⟨_, rfl⟩
  have hρ1 : ρ < 1 := hρ ▸ max_lt hl1 hM1
  have hρ0 : 0 ≤ ρ := hρ ▸ le_max_of_le_left (norm_nonneg _)
  have hrj : ∀ j : ℕ, ‖x ^ (l ^ j) - 1‖ ≤ ρ ^ j * ‖x - 1‖ := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hle : ‖x ^ (l ^ j) - 1‖ ≤ ‖x - 1‖ :=
        ih.trans (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hρ0 hρ1.le))
      have hlt1 : ‖x ^ (l ^ j) - 1‖ < 1 := lt_of_le_of_lt hle hM1
      calc ‖x ^ (l ^ (j + 1)) - 1‖ = ‖(x ^ (l ^ j)) ^ l - 1‖ := by rw [pow_succ l j, pow_mul]
        _ ≤ ‖x ^ (l ^ j) - 1‖ * max ‖(l : K)‖ ‖x ^ (l ^ j) - 1‖ := norm_pow_sub_one_le_mul_max hlt1 l
        _ ≤ (ρ ^ j * ‖x - 1‖) * ρ :=
            mul_le_mul ih (hρ ▸ max_le_max le_rfl hle) (le_max_of_le_left (norm_nonneg _))
              (mul_nonneg (pow_nonneg hρ0 j) (norm_nonneg _))
        _ = ρ ^ (j + 1) * ‖x - 1‖ := by ring
  obtain ⟨J, hJ⟩ := exists_pow_lt_of_lt_one (norm_pos_iff.mpr hl0) hρ1
  obtain ⟨d0, hd0def⟩ : ∃ d0, d0 = M * l ^ J := ⟨_, rfl⟩
  have hd0 : 0 < d0 := hd0def ▸ Nat.mul_pos hM (pow_pos hl.pos J)
  have hz : β ^ d0 = x ^ (l ^ J) := by rw [hd0def, pow_mul, hx]
  have hzlt : ‖β ^ d0 - 1‖ < ‖(l : K)‖ := by
    rw [hz]
    calc ‖x ^ (l ^ J) - 1‖ ≤ ρ ^ J * ‖x - 1‖ := hrj J
      _ ≤ ρ ^ J := mul_le_of_le_one_right (pow_nonneg hρ0 J) hM1.le
      _ < ‖(l : K)‖ := hJ
  have hzpos : 0 < ‖β ^ d0 - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (hβ d0 hd0))
  have key : ∀ n : ℕ, 0 < n → ‖(β ^ d0) ^ n - 1‖ = ‖β ^ d0 - 1‖ * ‖(n : K)‖ := by
    intro n hn
    obtain ⟨a, n', hn', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' l hl.ne_one
    have hn'1 : ‖(n' : K)‖ = 1 := norm_natCast_eq_one_of_not_dvd hl hl1 hn'
    have ha := norm_pow_prime_pow_sub_one hzlt a
    have hlt : ‖(β ^ d0) ^ (l ^ a) - 1‖ < ‖(n' : K)‖ := by
      rw [ha, hn'1]
      calc ‖(l : K)‖ ^ a * ‖β ^ d0 - 1‖ ≤ 1 * ‖β ^ d0 - 1‖ :=
            mul_le_mul_of_nonneg_right (pow_le_one₀ (norm_nonneg _) hl1.le) (norm_nonneg _)
        _ < 1 := by rw [one_mul]; exact hzlt.trans hl1
    rw [pow_mul, norm_pow_sub_one_eq hlt, ha, hn'1, Nat.cast_mul, Nat.cast_pow, norm_mul, norm_pow, hn'1]
    ring
  have hβ1 : ‖β‖ = 1 := by
    have h1 : ‖β ^ M‖ = 1 := norm_eq_one_of_norm_sub_one_lt_one (hx ▸ hM1)
    rw [norm_pow] at h1
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hM.ne').mp h1
  refine ⟨d0, hd0, ‖β ^ d0 - 1‖, hzpos, fun n hn => by rw [pow_mul]; exact key n hn, fun N hN => ?_⟩
  have e1 : (β ^ N) ^ d0 = (β ^ d0) ^ N := by rw [← pow_mul, ← pow_mul, mul_comm]
  calc ‖β ^ d0 - 1‖ * ‖(N : K)‖ = ‖(β ^ N) ^ d0 - 1‖ := by rw [e1, key N hN]
    _ ≤ ‖β ^ N - 1‖ := norm_pow_sub_one_le (by rw [norm_pow, hβ1, one_pow]) d0

end RamanujanPetersson.CoreA


end

-- ===== S4.Def_RP_CoreA_ValZ =====
section

/-!
# S4-CoreA part V2: `l`-adic growth of `h_N = Π_i (1 - c_i ^ N)`

`K` an algebraically closed ultrametric normed field of characteristic `0` with `‖l‖ < 1` (e.g. `PadicAlgCl l`).
`c ⊆ ℂ` a multiset with `Π_i c_i = Q` (`l ∤ Q`) and `Π_i (1 - c_i X)` the image of an integer polynomial `L`.
Let `P := reflect (#c) L`, so `P ↦ Π_i (X - c_i)` in `ℂ[X]`; `P` is monic over `ℤ`. Its roots `β_i` in `K` satisfy
`‖β_i‖ = 1`, `‖β_i ^ M - 1‖ < 1` for some `M ≥ 1` (pigeonhole on `X ^ k %ₘ P` mod `l`), and
`Π_i (1 - β_i ^ N) = Res(P, 1 - X ^ N) = Π_i (1 - c_i ^ N)` (resultant transfer).
* **`valuation_growth`**: for `h : ℕ → ℕ` with `h N = Π_i (1 - c_i ^ N) ≠ 0` (`N ≥ 1`):
  `v_l(h N) ≤ C₀ + #c v_l(N)`, and `v_l(h (d l^j)) = C' + #c j` for all `d` divisible by some `d0 ≥ 1`.
* `valuation_growth_padic`: the same with `K = PadicAlgCl l` and `Q = q ^ g`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson.CoreA

open Polynomial

section Ultra

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

theorem norm_aeval_int_le_one (S : ℤ[X]) {x : K} (hx : ‖x‖ ≤ 1) : ‖aeval x S‖ ≤ 1 := by
  rw [aeval_eq_sum_range]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one (fun i _ => ?_)
  rw [zsmul_eq_mul, norm_mul, norm_pow]
  exact mul_le_one₀ (IsUltrametricDist.norm_intCast_le_one K _) (by positivity)
    (pow_le_one₀ (norm_nonneg _) hx)

theorem norm_le_one_of_monic {P : ℤ[X]} (hP : P.Monic) {x : K} (hx : aeval x P = 0) : ‖x‖ ≤ 1 := by
  by_contra h
  rw [not_le] at h
  have hsum : x ^ P.natDegree = -∑ i ∈ Finset.range P.natDegree, (P.coeff i : K) * x ^ i := by
    have h1 := hx
    rw [hP.as_sum] at h1
    simp only [map_add, map_pow, aeval_X, map_sum, map_mul, aeval_C, algebraMap_int_eq,
      Int.coe_castRingHom] at h1
    exact eq_neg_of_add_eq_zero_left h1
  rcases Nat.eq_zero_or_pos P.natDegree with h0 | h0
  · rw [h0] at hsum
    simp at hsum
  obtain ⟨n, hn⟩ : ∃ n, P.natDegree = n + 1 := ⟨P.natDegree - 1, by omega⟩
  have hle : ‖x ^ P.natDegree‖ ≤ ‖x‖ ^ n := by
    rw [hsum, norm_neg]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) (fun i hi => ?_)
    rw [norm_mul, norm_pow]
    have hi' : i ≤ n := by rw [Finset.mem_range] at hi; omega
    calc ‖(P.coeff i : K)‖ * ‖x‖ ^ i ≤ 1 * ‖x‖ ^ n :=
          mul_le_mul (IsUltrametricDist.norm_intCast_le_one K _) (pow_le_pow_right₀ h.le hi')
            (by positivity) zero_le_one
      _ = ‖x‖ ^ n := one_mul _
  rw [norm_pow, hn, pow_succ] at hle
  have hpos : 0 < ‖x‖ ^ n := pow_pos (by linarith) n
  nlinarith

/-- Pigeonhole on the remainders `X ^ k %ₘ P` modulo `l`. -/
theorem exists_norm_pow_sub_one_lt {l : ℕ} (hl : l.Prime) (hl1 : ‖(l : K)‖ < 1) {P : ℤ[X]} (hP : P.Monic)
    {x : K} (hx : aeval x P = 0) (hx1 : ‖x‖ = 1) : ∃ M, 0 < M ∧ ‖x ^ M - 1‖ < 1 := by
  have : NeZero l := ⟨hl.ne_zero⟩
  obtain ⟨a, b, hab, hfab⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun (k : ℕ) (i : Fin P.natDegree) => (((X ^ k %ₘ P).coeff i : ℤ) : ZMod l))
  have key : ∀ a b : ℕ, a < b → (∀ i : Fin P.natDegree,
      (((X ^ a %ₘ P).coeff i : ℤ) : ZMod l) = (((X ^ b %ₘ P).coeff i : ℤ) : ZMod l)) →
      ‖x ^ (b - a) - 1‖ < 1 := by
    intro a b hab hfab
    have hdvd : ∀ i, (l : ℤ) ∣ (X ^ b %ₘ P - X ^ a %ₘ P).coeff i := by
      intro i
      rw [coeff_sub]
      by_cases hi : i < P.natDegree
      · exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp (hfab ⟨i, hi⟩)
      · have hz : ∀ k : ℕ, (X ^ k %ₘ P).coeff i = 0 := fun k =>
          coeff_eq_zero_of_degree_lt (lt_of_lt_of_le (degree_modByMonic_lt _ hP)
            (by rw [degree_eq_natDegree hP.ne_zero]; exact_mod_cast not_lt.mp hi))
        rw [hz, hz, sub_zero]
        exact dvd_zero _
    obtain ⟨S, hS⟩ := (C_dvd_iff_dvd_coeff _ _).mpr hdvd
    have heval : x ^ b - x ^ a = (l : K) * aeval x S := by
      have h1 := congrArg (aeval x) hS
      rw [map_sub, aeval_modByMonic_eq_self_of_root hx, aeval_modByMonic_eq_self_of_root hx] at h1
      simp only [map_pow, aeval_X, map_mul, aeval_C] at h1
      rw [h1]
      simp
    have hxa : x ^ b - x ^ a = x ^ a * (x ^ (b - a) - 1) := by
      rw [mul_sub, ← pow_add, Nat.add_sub_cancel' hab.le, mul_one]
    have hnorm : ‖x ^ b - x ^ a‖ < 1 := by
      rw [heval, norm_mul]
      calc ‖(l : K)‖ * ‖aeval x S‖ ≤ ‖(l : K)‖ * 1 :=
            mul_le_mul_of_nonneg_left (norm_aeval_int_le_one S hx1.le) (norm_nonneg _)
        _ < 1 := by rwa [mul_one]
    rwa [hxa, norm_mul, norm_pow, hx1, one_pow, one_mul] at hnorm
  rcases lt_or_gt_of_ne hab with h | h
  · exact ⟨b - a, by omega, key a b h (fun i => congrFun hfab i)⟩
  · exact ⟨a - b, by omega, key b a h (fun i => (congrFun hfab i).symm)⟩

end Ultra

section Res

end Res

section Main

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [IsAlgClosed K] [CharZero K]

end Main

end RamanujanPetersson.CoreA


end

-- ===== S4.Def_RP_PicDescent_C2 =====
section

/-!
# S4-PicDescent, part C2: class numbers of the constant field extensions, `h_n = L_n(1)`

`F_n = Fc Fq F Ω n` over `L_n = Lc Fq Ω n` (`Ω` algebraically closed, `#L_n = q ^ n`).
* `numPoints_Fc`: `N_k(F_n) = N_{nk}(F)`.
* `classNumber_Fc`: for any multiset `c` with `N_m(F) = 1 + q^m - Σ c_i^m` (`m ≥ 1`),
  `#Pic⁰(F_n) = Π (1 - c_i ^ n)`.
* `Lpoly c n = Π (1 - c_i^n t)`, the `L`-polynomial of `F_n`; `classNumber_Fc_zeta`: with the zeta multiset of
  `F` (`|c_i| ≤ √q`, at most `2g` roots), `h_n = #Pic⁰(F_n) = L_n(1) = Π (1 - c_i ^ n)` for every `n ≥ 1`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Polynomial

namespace RamanujanPetersson.PicDescent

open Polynomial

/-- `L_n(t) = Π_i (1 - c_i^n t)`. -/
noncomputable def Lpoly (c : Multiset ℂ) (n : ℕ) : ℂ[X] := (c.map fun z => 1 - C (z ^ n) * X).prod

section ClassNumber

variable (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (F : Type*) [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable (Ω : Type*) [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω] [IsAlgClosed Ω]

variable {Fq F}

end ClassNumber

end RamanujanPetersson.PicDescent


end


