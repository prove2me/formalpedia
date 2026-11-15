-- Prove2me | Definitions.Def_RPLib_S4_GalCover
-- name    : RPLib_S4_GalCover
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T10:19:09.285543+00:00
-- url     : https://prove2.me/theorems/7b6135c8-1a13-44bf-bfdf-e6348bfe7e59
-- title:
--   Galois covers of $\mathrm{Spec}\,A$ and Frobenius elements
-- statement:
--   Finite Galois extensions of the fraction field of a Dedekind-type ring $A$ unramified over $A$, presented as Galois covers: the Frobenius element at a prime with finite residue field (unique, conjugation behaviour), constants and geometric Galois group, maps of covers, and the profinite group they assemble into.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (elliptic-curve layer). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   J. S. Milne, Etale Cohomology, Princeton Univ. Press 1980, Chapter I; SGA 1, Expose V

import Mathlib
import Definitions.Def_RPLib_S3_PlacesA

/-!
# S4-GalCover draft v1: Galois etale covers and Frobenius (S4_DESIGN section 1)
-/

set_option autoImplicit false

open scoped Pointwise

namespace RamanujanPetersson

/-- A connected finite Galois etale cover `Spec B → Spec A` with group `G`: `A = B^G` with `G` acting
faithfully (`IsGaloisGroup`), `B` a finite `A`-algebra and a domain, and every inertia group trivial
(for Galois covers this is equivalent to `A → B` etale, SGA 1 V 2.6). -/
structure GalCover (A : Type) [CommRing A] [IsDomain A] where
  B : Type
  [ring : CommRing B]
  [dom : IsDomain B]
  [alg : Algebra A B]
  [inj : FaithfulSMul A B]
  [fin : Module.Finite A B]
  G : Type
  [grp : Group G]
  [fG : Finite G]
  [act : MulSemiringAction G B]
  [gal : IsGaloisGroup G A B]
  unramified : ∀ Q : Ideal B, Q.IsPrime → Q.inertia G = ⊥

attribute [local instance] GalCover.ring GalCover.dom GalCover.alg GalCover.inj GalCover.fin
  GalCover.grp GalCover.fG GalCover.act GalCover.gal

namespace GalCover

variable {A : Type} [CommRing A] [IsDomain A] (C : GalCover A)

theorem inertia_eq_bot (Q : Ideal C.B) [hQ : Q.IsPrime] : Q.inertia C.G = ⊥ := C.unramified Q hQ

/-- The (arithmetic) Frobenius of the cover at a prime `Q` with finite residue field. -/
noncomputable def frobAt (Q : Ideal C.B) [Q.IsPrime] [Finite (C.B ⧸ Q)] : C.G :=
  arithFrobAt A C.G Q

theorem isArithFrobAt_frobAt (Q : Ideal C.B) [Q.IsPrime] [Finite (C.B ⧸ Q)] :
    IsArithFrobAt A (C.frobAt Q) Q :=
  IsArithFrobAt.arithFrobAt A C.G Q

/-- Frobenius is unique (the cover is unramified). -/
theorem eq_frobAt_of_isArithFrobAt (Q : Ideal C.B) [Q.IsPrime] [Finite (C.B ⧸ Q)] {σ : C.G}
    (hσ : IsArithFrobAt A σ Q) : σ = C.frobAt Q := by
  have h := hσ.mul_inv_mem_inertia (C.isArithFrobAt_frobAt Q)
  rw [C.inertia_eq_bot Q, Subgroup.mem_bot, mul_inv_eq_one] at h
  exact h

theorem isArithFrobAt_iff (Q : Ideal C.B) [Q.IsPrime] [Finite (C.B ⧸ Q)] (σ : C.G) :
    IsArithFrobAt A σ Q ↔ σ = C.frobAt Q :=
  ⟨C.eq_frobAt_of_isArithFrobAt Q, fun h => h ▸ C.isArithFrobAt_frobAt Q⟩

theorem frobAt_smul (Q : Ideal C.B) [Q.IsPrime] [Finite (C.B ⧸ Q)] (τ : C.G) [(τ • Q).IsPrime]
    [Finite (C.B ⧸ τ • Q)] : C.frobAt (τ • Q) = τ * C.frobAt Q * τ⁻¹ :=
  (C.eq_frobAt_of_isArithFrobAt (τ • Q) ((C.isArithFrobAt_frobAt Q).conj τ)).symm

theorem isConj_frobAt (Q Q' : Ideal C.B) [Q.IsPrime] [Finite (C.B ⧸ Q)] [Q'.IsPrime]
    [Finite (C.B ⧸ Q')] (h : Q.under A = Q'.under A) : IsConj (C.frobAt Q) (C.frobAt Q') :=
  isConj_arithFrobAt A C.G Q Q' h

/-- The Frobenius conjugacy class at `Q` (it depends only on `Q.under A`). -/
noncomputable def frobClass (Q : Ideal C.B) [Q.IsPrime] [Finite (C.B ⧸ Q)] : ConjClasses C.G :=
  ConjClasses.mk (C.frobAt Q)

theorem frobClass_eq (Q Q' : Ideal C.B) [Q.IsPrime] [Finite (C.B ⧸ Q)] [Q'.IsPrime]
    [Finite (C.B ⧸ Q')] (h : Q.under A = Q'.under A) : C.frobClass Q = C.frobClass Q' :=
  ConjClasses.mk_eq_mk_iff_isConj.mpr (C.isConj_frobAt Q Q' h)

/-- The intermediate cover `Spec B → Spec B^H` (pullback of `C` to the subcover fixed by `H`). -/
noncomputable def restrict (H : Subgroup C.G) : GalCover (FixedPoints.subalgebra A C.B H) where
  B := C.B
  G := H
  fin := Module.Finite.of_restrictScalars_finite A _ C.B
  unramified Q hQ := by
    have h := C.unramified Q hQ
    rw [eq_bot_iff] at h ⊢
    intro σ hσ
    have hσ' : (σ : C.G) ∈ Q.inertia C.G := fun x => hσ x
    have := h hσ'
    rw [Subgroup.mem_bot] at this ⊢
    exact Subtype.ext this

omit [IsDomain A] in
private theorem algEquiv_self_subsingleton : Subsingleton (A ≃ₐ[A] A) :=
  ⟨fun f g => AlgEquiv.ext fun x => by
    rw [show x = algebraMap A A x from rfl, f.commutes, g.commutes]⟩

/-- The trivial cover `A = A` with the trivial group. -/
noncomputable def trivial (A : Type) [CommRing A] [IsDomain A] : GalCover A where
  B := A
  G := A ≃ₐ[A] A
  fG := @Finite.of_subsingleton _ algEquiv_self_subsingleton
  gal := { faithful := inferInstance, commutes := inferInstance,
           isInvariant := ⟨fun b _ => ⟨b, rfl⟩⟩ }
  unramified Q _ := by
    rw [eq_bot_iff]
    intro σ _
    rw [Subgroup.mem_bot]
    exact @Subsingleton.elim _ algEquiv_self_subsingleton _ _

/-- Sanity: every Frobenius of the trivial cover is `1`. -/
theorem trivial_frobAt (Q : Ideal (trivial A).B) [Q.IsPrime] [Finite ((trivial A).B ⧸ Q)] :
    (trivial A).frobAt Q = 1 :=
  @Subsingleton.elim _ algEquiv_self_subsingleton _ _


/-! ## Constants, the geometric subgroup, Frobenius on constants -/

section Constants

variable (Fq : Type) [Field Fq] [Algebra Fq A] [Algebra Fq C.B] [IsScalarTower Fq A C.B]

theorem smulCommClass_const : SMulCommClass C.G Fq C.B :=
  ⟨fun g a b => by
    rw [← algebraMap_smul A a b, ← algebraMap_smul A a (g • b), smul_comm]⟩

attribute [local instance] smulCommClass_const

/-- The constant field of the cover: the algebraic closure of `Fq` in `B`. -/
noncomputable abbrev constField : Subalgebra Fq C.B := integralClosure Fq C.B

/-- The action of the cover group on the constants. -/
noncomputable def toConstAut : C.G →* (integralClosure Fq C.B ≃ₐ[Fq] integralClosure Fq C.B) :=
  MulSemiringAction.toAlgAut C.G Fq (integralClosure Fq C.B)

/-- The geometric subgroup `G^geo`: elements acting trivially on the constants. -/
noncomputable def geo : Subgroup C.G := (C.toConstAut Fq).ker

instance geo_normal : (C.geo Fq).Normal := MonoidHom.normal_ker _

theorem mem_geo_iff (g : C.G) : g ∈ C.geo Fq ↔ ∀ c ∈ integralClosure Fq C.B, g • c = c := by
  rw [geo, MonoidHom.mem_ker]
  constructor
  · intro h c hc
    have := congrArg (fun e : integralClosure Fq C.B ≃ₐ[Fq] integralClosure Fq C.B => (e ⟨c, hc⟩ : C.B)) h
    simpa [toConstAut] using this
  · intro h
    ext c
    simpa [toConstAut] using h c c.2

/-- The constant field is a field. -/
theorem isField_constField : IsField (integralClosure Fq C.B) :=
  (Algebra.IsIntegral.isField_iff_isField (R := Fq) (S := integralClosure Fq C.B)
    (algebraMap Fq _).injective).mp (Field.toIsField Fq)

/-- `G / G^geo` is cyclic (it embeds in the Galois group of the finite constant field). -/
theorem isCyclic_quotient_geo [Finite (integralClosure Fq C.B)] : IsCyclic (C.G ⧸ C.geo Fq) := by
  let _ : Field (integralClosure Fq C.B) := (C.isField_constField Fq).toField
  have : IsCyclic (integralClosure Fq C.B ≃ₐ[Fq] integralClosure Fq C.B) := inferInstance
  exact isCyclic_of_injective (QuotientGroup.kerLift (C.toConstAut Fq))
    (QuotientGroup.kerLift_injective _)

/-- Frobenius acts on the constants by the `N(P)`-th power map (constants embed in `B ⧸ Q`). -/
theorem frobAt_smul_const (Q : Ideal C.B) [Q.IsPrime] [Finite (C.B ⧸ Q)] (c : C.B)
    (hc : c ∈ integralClosure Fq C.B) :
    C.frobAt Q • c = c ^ Nat.card (A ⧸ Q.under A) := by
  set k := integralClosure Fq C.B
  have hmemQ : C.frobAt Q • c - c ^ Nat.card (A ⧸ Q.under A) ∈ Q := by
    have := C.isArithFrobAt_frobAt Q c
    simpa using this
  have hmemk : C.frobAt Q • c - c ^ Nat.card (A ⧸ Q.under A) ∈ k := by
    refine sub_mem ?_ (pow_mem hc _)
    have h := (C.frobAt Q • (⟨c, hc⟩ : k)).2
    rw [integralClosure.coe_smul] at h
    exact h
  by_contra hne
  obtain ⟨b, hb⟩ := (C.isField_constField Fq).mul_inv_cancel
    (a := ⟨_, hmemk⟩) (fun h => hne (sub_eq_zero.mp (by simpa using congrArg Subtype.val h)))
  have h1 : (1 : C.B) ∈ Q := by
    have := Q.mul_mem_right (b : C.B) hmemQ
    have hb' := congrArg Subtype.val hb
    simp only [MulMemClass.coe_mul, OneMemClass.coe_one] at hb'
    rwa [hb'] at this
  exact (inferInstance : Q.IsPrime).ne_top ((Ideal.eq_top_iff_one Q).mpr h1)

end Constants

/-! ## Morphisms of covers -/

/-- A morphism of covers `C' → C` over `A` (a tower `B ⊆ B'`) with the surjection of groups. -/
structure CoverHom (C C' : GalCover A) where
  ringHom : C.B →ₐ[A] C'.B
  grpHom : C'.G →* C.G
  surj : Function.Surjective grpHom
  equivariant : ∀ (g : C'.G) (b : C.B), ringHom (grpHom g • b) = g • ringHom b

/-- Frobenius is compatible with cover maps (equality, since covers are unramified). -/
theorem CoverHom.frobAt_map {C C' : GalCover A} (f : CoverHom C C') (Q' : Ideal C'.B) [Q'.IsPrime]
    [Finite (C'.B ⧸ Q')] [Finite (C.B ⧸ Q'.comap f.ringHom)] :
    f.grpHom (C'.frobAt Q') = C.frobAt (Q'.comap f.ringHom) := by
  apply C.eq_frobAt_of_isArithFrobAt
  have hu : (Q'.comap f.ringHom).under A = Q'.under A := by
    ext a
    simp only [Ideal.under, Ideal.mem_comap, AlgHom.commutes]
  intro x
  have h := C'.isArithFrobAt_frobAt Q' (f.ringHom x)
  rw [hu, Ideal.mem_comap]
  simpa [map_sub, map_pow, f.equivariant] using h


/-! ## Etale Galois extensions have trivial inertia (bridge `ofEtale`) -/

section Etale

variable {B G : Type} [CommRing B] [IsDomain B] [Algebra A B] [Group G] [Finite G]
  [MulSemiringAction G B] [IsGaloisGroup G A B]

/-- If `A → B` is (formally) unramified, Galois with group `G`, and `B` is Noetherian, the inertia group of every
prime with finite residue field is trivial (Frobenius is unique: `IsArithFrobAt.eq_of_isUnramifiedAt`). -/
theorem inertia_eq_bot_of_formallyUnramified [Algebra.FormallyUnramified A B] [IsNoetherianRing B]
    (Q : Ideal B) [Q.IsPrime] [Finite (B ⧸ Q)] : Q.inertia G = ⊥ := by
  have hfaith : FaithfulSMul G B := (‹IsGaloisGroup G A B›).faithful
  rw [eq_bot_iff]
  intro σ hσ
  rw [Subgroup.mem_bot]
  have hφ : IsArithFrobAt A (arithFrobAt A G Q) Q := IsArithFrobAt.arithFrobAt A G Q
  have hσφ : IsArithFrobAt A (σ * arithFrobAt A G Q) Q := fun x => by
    have h := Q.add_mem (hσ (arithFrobAt A G Q • x)) (hφ x)
    simpa [mul_smul] using h
  have hQ : Q.primeCompl ≤ nonZeroDivisors B := fun x hx =>
    mem_nonZeroDivisors_of_ne_zero fun h => hx (h ▸ Q.zero_mem)
  have heq := hσφ.eq_of_isUnramifiedAt hφ hQ
  have h2 : σ * arithFrobAt A G Q = arithFrobAt A G Q := eq_of_smul_eq_smul fun x => by
    simpa using DFunLike.congr_fun heq x
  simpa using h2

omit [IsDomain B] [Finite G] [IsGaloisGroup G A B] in
/-- The zero ideal has trivial inertia (the action is faithful). -/
theorem inertia_bot_eq_bot [FaithfulSMul G B] : (⊥ : Ideal B).inertia G = ⊥ := by
  rw [eq_bot_iff]
  intro σ hσ
  rw [Subgroup.mem_bot]
  refine eq_of_smul_eq_smul fun x : B => ?_
  have h : σ • x - x ∈ (⊥ : Ideal B) := hσ x
  rw [Ideal.mem_bot, sub_eq_zero] at h
  simpa using h

/-- An etale Galois extension `A → B` of Noetherian domains whose nonzero primes have finite residue fields
(e.g. a finite etale Galois cover of a smooth affine curve over a finite field) is a `GalCover`. -/
noncomputable def ofEtale (A : Type) [CommRing A] [IsDomain A] (B G : Type) [CommRing B] [IsDomain B]
    [Algebra A B] [FaithfulSMul A B] [Module.Finite A B] [Group G] [Finite G] [MulSemiringAction G B]
    [IsGaloisGroup G A B] [Algebra.Etale A B] [IsNoetherianRing B]
    (hfin : ∀ Q : Ideal B, Q.IsPrime → Q ≠ ⊥ → Finite (B ⧸ Q)) : GalCover A where
  B := B
  G := G
  unramified Q hQ := by
    by_cases h : Q = ⊥
    · subst h
      have : FaithfulSMul G B := (‹IsGaloisGroup G A B›).faithful
      exact inertia_bot_eq_bot
    · have := hfin Q hQ h
      exact inertia_eq_bot_of_formallyUnramified (A := A) Q

end Etale

end GalCover

/-! ## The etale fundamental group and the finite-quotient bridge -/

section Pi1

variable (A K : Type) [CommRing A] [Field K] [Algebra A K]

/-- Galois groups over `K` commute with scalars from `A` (which act through `K`). -/
instance algEquiv_smulCommClass (L : Type) [Field L] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] : SMulCommClass (L ≃ₐ[K] L) A L :=
  ⟨fun σ a x => by
    show σ (a • x) = a • σ x
    rw [← algebraMap_smul K a x, ← algebraMap_smul K a (σ x), map_smul]⟩

/-- A subextension `L` of `K̄/K` is unramified over `A`: every inertia group of `Gal(L/K)` acting on the
integral closure of `A` in `L` is trivial. -/
def IsUnramifiedSub (L : IntermediateField K (AlgebraicClosure K)) : Prop :=
  ∀ Q : Ideal (integralClosure A L), Q.IsPrime → Q.inertia (L ≃ₐ[K] L) = ⊥

/-- The finite Galois subextensions of `K̄/K` that are unramified over `A`. -/
def unramSet : Set (IntermediateField K (AlgebraicClosure K)) :=
  {L | FiniteDimensional K L ∧ IsGalois K L ∧ IsUnramifiedSub A K L}

/-- The maximal extension `K_U` of `K` unramified over `U = Spec A`. -/
noncomputable def maxUnram : IntermediateField K (AlgebraicClosure K) :=
  ⨆ L : unramSet A K, (L : IntermediateField K (AlgebraicClosure K))

/-- The etale fundamental group `π₁(U) = Gal(K_U/K)` (Krull topology). -/
noncomputable abbrev Pi1 : Type := maxUnram A K ≃ₐ[K] maxUnram A K

noncomputable example : TopologicalSpace (Pi1 A K) := inferInstance
example : IsTopologicalGroup (Pi1 A K) := inferInstance

instance unramSet_isGalois (L : unramSet A K) :
    IsGalois K (L : IntermediateField K (AlgebraicClosure K)) := L.2.2.1

instance maxUnram_isGalois : IsGalois K (maxUnram A K) := by
  unfold maxUnram
  exact ⟨⟩

theorem bot_mem_unramSet : (⊥ : IntermediateField K (AlgebraicClosure K)) ∈ unramSet A K := by
  refine ⟨inferInstance, inferInstance, fun Q _ => ?_⟩
  rw [eq_bot_iff]
  intro σ _
  rw [Subgroup.mem_bot]
  ext x
  obtain ⟨k, hk⟩ := IntermediateField.mem_bot.mp x.2
  have hx : x = algebraMap K _ k := Subtype.ext hk.symm
  rw [hx, AlgEquiv.commutes]
  rfl

/-- Restriction of an `A`-integral element of `L₁ ⊆ L₂` (as an `A`-algebra map of integral closures). -/
noncomputable def incl {L₁ L₂ : IntermediateField K (AlgebraicClosure K)} (h : L₁ ≤ L₂) :
    integralClosure A L₁ →ₐ[A] integralClosure A L₂ :=
  ((IntermediateField.inclusion h).restrictScalars A).mapIntegralClosure

theorem incl_val {L₁ L₂ : IntermediateField K (AlgebraicClosure K)} (h : L₁ ≤ L₂)
    (y : integralClosure A L₁) : (((incl A K h y : L₂) : AlgebraicClosure K)) = ((y : L₁) : AlgebraicClosure K) :=
  rfl

/-- Unramified finite Galois subextensions are closed under composita. -/
theorem sup_mem_unramSet {L₁ L₂ : IntermediateField K (AlgebraicClosure K)} (h₁ : L₁ ∈ unramSet A K)
    (h₂ : L₂ ∈ unramSet A K) : L₁ ⊔ L₂ ∈ unramSet A K := by
  obtain ⟨f₁, g₁, u₁⟩ := h₁
  obtain ⟨f₂, g₂, u₂⟩ := h₂
  refine ⟨inferInstance, inferInstance, fun Q hQ => ?_⟩
  have := hQ
  rw [eq_bot_iff]
  intro τ hτ
  rw [Subgroup.mem_bot]
  obtain ⟨σ, hσ⟩ : ∃ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, ∀ y : ↥(L₁ ⊔ L₂),
      σ (y : AlgebraicClosure K) = ((τ y : ↥(L₁ ⊔ L₂)) : AlgebraicClosure K) :=
    ⟨τ.liftNormal (AlgebraicClosure K), fun y => τ.liftNormal_commutes (AlgebraicClosure K) y⟩
  -- `σ` fixes each `Lᵢ`: its restriction lies in the inertia of the contracted prime
  have key : ∀ (L : IntermediateField K (AlgebraicClosure K)) (hle : L ≤ L₁ ⊔ L₂) [IsGalois K L],
      IsUnramifiedSub A K L → σ ∈ L.fixingSubgroup := by
    intro L hle _ uL
    have hP : (Q.comap (incl A K hle)).IsPrime := Ideal.IsPrime.comap _
    have hin : AlgEquiv.restrictNormalHom L σ ∈ (Q.comap (incl A K hle)).inertia (L ≃ₐ[K] L) := by
      intro y
      show (incl A K hle) (AlgEquiv.restrictNormalHom L σ • y - y) ∈ Q
      have h : τ • incl A K hle y - incl A K hle y ∈ Q := hτ (incl A K hle y)
      convert h using 2
      apply Subtype.ext; apply Subtype.ext
      show ((AlgEquiv.restrictNormalHom L σ (y : L) : L) : AlgebraicClosure K) - ((y : L) : AlgebraicClosure K)
        = ((τ (incl A K hle y : ↥(L₁ ⊔ L₂)) : ↥(L₁ ⊔ L₂)) : AlgebraicClosure K) - ((y : L) : AlgebraicClosure K)
      rw [AlgEquiv.restrictNormalHom_apply, ← hσ]
      rfl
    have h1 := uL _ hP
    rw [h1, Subgroup.mem_bot] at hin
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have := congrArg (fun e : L ≃ₐ[K] L => ((e ⟨x, hx⟩ : L) : AlgebraicClosure K)) hin
    simpa [AlgEquiv.restrictNormalHom_apply] using this
  have hfix : σ ∈ (L₁ ⊔ L₂).fixingSubgroup := by
    rw [IntermediateField.fixingSubgroup_sup]
    exact ⟨key L₁ le_sup_left u₁, key L₂ le_sup_right u₂⟩
  ext y
  rw [AlgEquiv.one_apply, ← hσ]
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp hfix y y.2

theorem directedOn_unramSet : DirectedOn (· ≤ ·) (unramSet A K) := fun L₁ h₁ L₂ h₂ =>
  ⟨L₁ ⊔ L₂, sup_mem_unramSet A K h₁ h₂, le_sup_left, le_sup_right⟩

theorem maxUnram_eq_sSup : maxUnram A K = sSup (unramSet A K) := by
  rw [maxUnram, sSup_eq_iSup']

/-- Every finitely generated subextension of `K_U` lies in one unramified finite Galois `L`. -/
theorem exists_unramSet_of_finite (s : Finset (AlgebraicClosure K))
    (hs : ∀ x ∈ s, x ∈ maxUnram A K) :
    ∃ L ∈ unramSet A K, IntermediateField.adjoin K (s : Set (AlgebraicClosure K)) ≤ L := by
  have hc := IntermediateField.adjoin_finset_isCompactElement (F := K) s
  rw [CompleteLattice.isCompactElement_iff_le_of_directed_sSup_le] at hc
  refine hc (unramSet A K) ⟨⊥, bot_mem_unramSet A K⟩ (directedOn_unramSet A K) ?_
  rw [← maxUnram_eq_sSup, IntermediateField.adjoin_le_iff]
  exact fun x hx => hs x hx

section Bridge

variable [IsDomain A] [IsFractionRing A K] [IsIntegrallyClosed A] [IsNoetherianRing A]

/-- The Galois cover of `Spec A` given by an unramified finite Galois subextension `L` of `K̄/K`:
`B` = integral closure of `A` in `L`, `G = Gal(L/K)`. -/
noncomputable def coverOf (L : IntermediateField K (AlgebraicClosure K)) (hL : L ∈ unramSet A K) :
    GalCover A :=
  haveI := hL.1
  haveI := hL.2.1
  haveI : IsFractionRing (integralClosure A L) L :=
    integralClosure.isFractionRing_of_finite_extension (A := A) K L
  { B := integralClosure A L
    G := L ≃ₐ[K] L
    inj := (faithfulSMul_iff_algebraMap_injective A (integralClosure A L)).mpr fun a b h => by
      have hinj : Function.Injective (algebraMap A L) := by
        rw [IsScalarTower.algebraMap_eq A K L]
        exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)
      exact hinj (by simpa using congrArg Subtype.val h)
    fin := IsIntegralClosure.finite A K L (integralClosure A L)
    gal := IsGaloisGroup.of_isFractionRing (L ≃ₐ[K] L) A (integralClosure A L) K L
    unramified := hL.2.2 }

theorem coverOf_G (L : IntermediateField K (AlgebraicClosure K)) (hL : L ∈ unramSet A K) :
    (coverOf A K L hL).G = (L ≃ₐ[K] L) := rfl

/-- **Finite-quotient bridge.** Every open subgroup `N` of `π₁(U)` contains the kernel of a surjection
`π₁(U) ↠ G` onto the group of a finite Galois etale cover of `U`. So a continuous representation of `π₁(U)` with
open kernel factors through (and is studied as) a representation of a `GalCover`. -/
theorem exists_cover_of_isOpen (N : Subgroup (Pi1 A K)) (hN : IsOpen (N : Set (Pi1 A K))) :
    ∃ (C : GalCover A) (π : Pi1 A K →* C.G), Function.Surjective π ∧ π.ker ≤ N := by
  classical
  obtain ⟨E, hE, hEN⟩ :=
    (krullTopology_mem_nhds_one_iff K (maxUnram A K) N).mp (hN.mem_nhds N.one_mem)
  have hfg : E.FG := by
    apply IntermediateField.fg_of_fg_toSubalgebra
    apply Subalgebra.fg_of_fg_toSubmodule
    exact (Submodule.fg_iff_finiteDimensional _).mpr hE
  obtain ⟨t, htfin, hadj⟩ := IntermediateField.fg_def.mp hfg
  obtain ⟨L, hL, hle⟩ := exists_unramSet_of_finite A K
    (htfin.toFinset.image (fun x : maxUnram A K => (x : AlgebraicClosure K))) (by
      intro x hx
      obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hx
      exact y.2)
  have hLU : L ≤ maxUnram A K := by
    rw [maxUnram_eq_sSup]
    exact le_sSup hL
  haveI := hL.2.1
  letI : Algebra L (maxUnram A K) := (IntermediateField.inclusion hLU).toAlgebra
  haveI : IsScalarTower K L (maxUnram A K) := IsScalarTower.of_algHom (IntermediateField.inclusion hLU)
  refine ⟨coverOf A K L hL, AlgEquiv.restrictNormalHom L,
    AlgEquiv.restrictNormalHom_surjective (maxUnram A K), ?_⟩
  intro σ hσ
  have hσ' : AlgEquiv.restrictNormalHom L σ = 1 := hσ
  apply hEN
  -- `σ` fixes every generator of `E`, hence `E`
  have hgen : ∀ x ∈ t, σ x = x := by
    intro x hx
    have hxL : (x : AlgebraicClosure K) ∈ L := by
      apply hle
      apply IntermediateField.subset_adjoin
      exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨x, htfin.mem_toFinset.mpr hx, rfl⟩)
    have hx' : x = algebraMap L (maxUnram A K) ⟨x, hxL⟩ := Subtype.ext rfl
    rw [hx', ← AlgEquiv.restrictNormal_commutes]
    change algebraMap L (maxUnram A K) ((AlgEquiv.restrictNormalHom L σ) ⟨x, hxL⟩) = _
    rw [hσ', AlgEquiv.one_apply]
  have hEfix : E ≤ IntermediateField.fixedField (Subgroup.zpowers σ) := by
    rw [← hadj, IntermediateField.adjoin_le_iff]
    intro x hx
    rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
    intro g hg
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    induction n using Int.induction_on with
    | zero => simp
    | succ n ih => rw [zpow_add_one, AlgEquiv.mul_apply, hgen x hx, ih (Subgroup.zpow_mem_zpowers σ _)]
    | pred n ih =>
      have hinv : σ⁻¹ x = x := by
        conv_lhs => rw [← hgen x hx]
        rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
      rw [zpow_sub_one, AlgEquiv.mul_apply, hinv, ih (Subgroup.zpow_mem_zpowers σ _)]
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  exact (IntermediateField.mem_fixedField_iff _ _).mp (hEfix hx) σ (Subgroup.mem_zpowers σ)

/-- Bridge, quotient form: for an open normal subgroup `N`, `π₁(U)/N` is a quotient of the group of a cover. -/
theorem exists_cover_surj_quotient (N : Subgroup (Pi1 A K)) [N.Normal] (hN : IsOpen (N : Set (Pi1 A K))) :
    ∃ (C : GalCover A) (f : C.G →* Pi1 A K ⧸ N), Function.Surjective f := by
  obtain ⟨C, π, hs, hk⟩ := exists_cover_of_isOpen A K N hN
  refine ⟨C, (QuotientGroup.map π.ker N (MonoidHom.id _) fun x hx => hk hx).comp
    (QuotientGroup.quotientKerEquivOfSurjective π hs).symm.toMonoidHom, ?_⟩
  intro q
  obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective q
  refine ⟨π σ, ?_⟩
  have h : (QuotientGroup.quotientKerEquivOfSurjective π hs).symm (π σ) = (σ : Pi1 A K ⧸ π.ker) :=
    (MulEquiv.symm_apply_eq _).mpr rfl
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h]
  rfl

end Bridge

end Pi1

/-! ## Charts over other base rings: the infinity chart and boundary places (review R5) -/

namespace GalCover

section Charts

variable {A : Type} [CommRing A] [IsDomain A] (C : GalCover A)
variable (K L : Type) [Field K] [Field L] [Algebra A K] [IsFractionRing A K] [Algebra C.B L]
  [IsFractionRing C.B L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A C.B L]
  [MulSemiringAction C.G L] [SMulDistribClass C.G C.B L]

/-- The cover group is a Galois group of the function-field extension `L/K`. -/
theorem isGaloisGroup_frac : IsGaloisGroup C.G K L := IsGaloisGroup.to_isFractionRing C.G A C.B K L

include C in
theorem finiteDimensional_frac : FiniteDimensional K L :=
  haveI := C.isGaloisGroup_frac K L
  IsGaloisGroup.finiteDimensional C.G K L

variable (R0 : Type) [CommRing R0] [IsDomain R0] [IsIntegrallyClosed R0] [Algebra R0 K]
  [IsFractionRing R0 K] [Algebra R0 L] [IsScalarTower R0 K L]

include K in
theorem smulCommClass_chart : SMulCommClass C.G R0 L := by
  haveI := C.isGaloisGroup_frac K L
  exact ⟨fun g r x => by rw [← algebraMap_smul K r x, ← algebraMap_smul K r (g • x), smul_comm]⟩

/-- The action of the cover group on the chart `integralClosure R0 L` (the cover over the base chart `Spec R0`). -/
noncomputable def chartAction : MulSemiringAction C.G (integralClosure R0 L) :=
  haveI := C.smulCommClass_chart K L R0
  inferInstance

/-- Over any integrally closed `R0` with fraction field `K`, the chart is Galois with group `C.G`. -/
theorem isGaloisGroup_chart :
    letI := C.chartAction K L R0
    IsGaloisGroup C.G R0 (integralClosure R0 L) := by
  haveI := C.isGaloisGroup_frac K L
  haveI := C.smulCommClass_chart K L R0
  haveI := C.finiteDimensional_frac K L
  haveI : IsFractionRing (integralClosure R0 L) L :=
    integralClosure.isFractionRing_of_finite_extension (A := R0) K L
  exact IsGaloisGroup.of_isFractionRing C.G R0 (integralClosure R0 L) K L

/-- The inertia group of the chart at a prime `P` (nontrivial exactly at ramified boundary places). -/
noncomputable def chartInertia (P : Ideal (integralClosure R0 L)) : Subgroup C.G :=
  letI := C.chartAction K L R0
  P.inertia C.G

/-- A Frobenius element of the chart at `P` (well defined modulo `chartInertia`). -/
noncomputable def chartFrob (P : Ideal (integralClosure R0 L)) [P.IsPrime]
    [Finite (integralClosure R0 L ⧸ P)] : C.G :=
  letI := C.chartAction K L R0
  haveI := C.isGaloisGroup_chart K L R0
  arithFrobAt R0 C.G P

theorem chartFrob_spec (P : Ideal (integralClosure R0 L)) [P.IsPrime]
    [Finite (integralClosure R0 L ⧸ P)] :
    letI := C.chartAction K L R0
    haveI := C.isGaloisGroup_chart K L R0
    IsArithFrobAt R0 (C.chartFrob K L R0 P) P := by
  letI := C.chartAction K L R0
  haveI := C.isGaloisGroup_chart K L R0
  exact IsArithFrobAt.arithFrobAt R0 C.G P

/-- Frobenius at a boundary place is well defined modulo inertia. -/
theorem chartFrob_mul_inv_mem (P : Ideal (integralClosure R0 L)) [P.IsPrime]
    [Finite (integralClosure R0 L ⧸ P)] (σ : C.G)
    (hσ : letI := C.chartAction K L R0; haveI := C.isGaloisGroup_chart K L R0; IsArithFrobAt R0 σ P) :
    σ * (C.chartFrob K L R0 P)⁻¹ ∈ C.chartInertia K L R0 P := by
  letI := C.chartAction K L R0
  haveI := C.isGaloisGroup_chart K L R0
  exact hσ.mul_inv_mem_inertia (C.chartFrob_spec K L R0 P)

/-- Chart Frobenius elements at primes over the same prime of `R0` are conjugate. -/
theorem isConj_chartFrob (P P' : Ideal (integralClosure R0 L)) [P.IsPrime]
    [Finite (integralClosure R0 L ⧸ P)] [P'.IsPrime] [Finite (integralClosure R0 L ⧸ P')]
    (h : P.under R0 = P'.under R0) : IsConj (C.chartFrob K L R0 P) (C.chartFrob K L R0 P') := by
  letI := C.chartAction K L R0
  haveI := C.isGaloisGroup_chart K L R0
  exact isConj_arithFrobAt R0 C.G P P' h

/-- Sanity: the zero prime of a chart has trivial inertia. -/
theorem chartInertia_bot : C.chartInertia K L R0 ⊥ = ⊥ := by
  letI := C.chartAction K L R0
  haveI := C.isGaloisGroup_chart K L R0
  haveI : FaithfulSMul C.G (integralClosure R0 L) :=
    (‹IsGaloisGroup C.G R0 (integralClosure R0 L)›).faithful
  exact inertia_bot_eq_bot

end Charts

/-! ### The two charts of a base curve inside `𝔸¹`: finite (`Fq[X]`) and infinity (`O_∞`) -/

section CurveCharts

open Polynomial

variable {A : Type} [CommRing A] [IsDomain A] (C : GalCover A)
variable (Fq : Type) [Field Fq] [DecidableEq (RatFunc Fq)] [Algebra A (RatFunc Fq)]
  [IsFractionRing A (RatFunc Fq)]
variable (L : Type) [Field L] [Algebra C.B L] [IsFractionRing C.B L] [Algebra (RatFunc Fq) L]
  [Algebra A L] [IsScalarTower A (RatFunc Fq) L] [IsScalarTower A C.B L] [MulSemiringAction C.G L]
  [SMulDistribClass C.G C.B L]

/-- The infinity chart: the integral closure in `L` of the valuation ring `O_∞ ⊆ Fq(X)` at `x = ∞`. Its nonzero
primes are the places of the cover over `∞`. -/
noncomputable abbrev infChart : Subalgebra (Places.Oinf Fq) L := integralClosure (Places.Oinf Fq) L

/-- A boundary place at infinity: a nonzero prime of the infinity chart. -/
def IsInfBoundary (P : Ideal (infChart Fq L)) : Prop := P.IsPrime ∧ P ≠ ⊥

/-- The inertia group at a place over `∞`. -/
noncomputable def infInertia (P : Ideal (infChart Fq L)) : Subgroup C.G :=
  C.chartInertia (RatFunc Fq) L (Places.Oinf Fq) P

/-- A Frobenius at a place over `∞` (well defined modulo `infInertia`). -/
noncomputable def infFrob (P : Ideal (infChart Fq L)) [P.IsPrime] [Finite (infChart Fq L ⧸ P)] : C.G :=
  C.chartFrob (RatFunc Fq) L (Places.Oinf Fq) P

theorem infFrob_mul_inv_mem (P : Ideal (infChart Fq L)) [P.IsPrime] [Finite (infChart Fq L ⧸ P)] (σ : C.G)
    (hσ : letI := C.chartAction (RatFunc Fq) L (Places.Oinf Fq)
      haveI := C.isGaloisGroup_chart (RatFunc Fq) L (Places.Oinf Fq)
      IsArithFrobAt (Places.Oinf Fq) σ P) :
    σ * (C.infFrob Fq L P)⁻¹ ∈ C.infInertia Fq L P :=
  C.chartFrob_mul_inv_mem (RatFunc Fq) L (Places.Oinf Fq) P σ hσ

variable [Algebra Fq[X] L] [IsScalarTower Fq[X] (RatFunc Fq) L]

/-- The finite chart: the integral closure of `Fq[X]` in `L`. -/
noncomputable abbrev finChart : Subalgebra Fq[X] L := integralClosure Fq[X] L

/-- A finite boundary place of `U = Spec A ⊆ 𝔸¹`: a prime of the finite chart lying over a prime of `Fq[X]`
that becomes the unit ideal in `A` (a point of `𝔸¹` removed from `U`). -/
def IsFinBoundary [Algebra Fq[X] A] (P : Ideal (finChart Fq L)) : Prop :=
  P.IsPrime ∧ P ≠ ⊥ ∧ (P.under Fq[X]).map (algebraMap Fq[X] A) = ⊤

/-- The inertia group at a finite place of the finite chart. -/
noncomputable def finInertia (P : Ideal (finChart Fq L)) : Subgroup C.G :=
  C.chartInertia (RatFunc Fq) L Fq[X] P

/-- A Frobenius at a finite place of the finite chart (well defined modulo `finInertia`). -/
noncomputable def finFrob (P : Ideal (finChart Fq L)) [P.IsPrime] [Finite (finChart Fq L ⧸ P)] : C.G :=
  C.chartFrob (RatFunc Fq) L Fq[X] P

end CurveCharts

end GalCover

end RamanujanPetersson


