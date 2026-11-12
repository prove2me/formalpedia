-- Prove2me | Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_Clifford
-- name    : OddOrder_GroupTheory_RepresentationTheory_Clifford
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:07:52.795858+00:00
-- url     : https://prove2.me/theorems/c7b8f48a-9e9b-47bb-bacf-7b0ae5fef61c
-- title:
--   Clifford's theorem on irreducible characters of a normal subgroup
-- statement:
--   Formalizes Clifford's theorem (Isaacs, *Character Theory of Finite Groups*, Thm 6.5). For $H\trianglelefteq G$ and $\chi\in\mathrm{Irr}\,G$, every irreducible constituent $\theta$ of $\mathrm{Res}^G_H\chi$ is a $G$-conjugate of every other, all with the same multiplicity, and $\mathrm{Res}^G_H\chi=e_\chi(\theta^{g_1}+\dots+\theta^{g_t})$ where $g_i$ run over a transversal of the inertia subgroup $I_G(\theta)$ in $G$.
--
--   Main definitions: `restrictRep` (restriction of a representation to a subgroup), `conjBySimpleRingHom` (the ring automorphism of $\mathbb{C}[H]$ induced by conjugation), `conjBySimpleSemilinear` (the map $\rho(g)$ as a semilinear bijection) and `restrictionMultiplicity` (the normalized inner-product multiplicity of $\theta$ in $\mathrm{Res}\,\chi$).
--
--   The bundle also proves 29 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/RepresentationTheory/Clifford.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/RepresentationTheory/Clifford.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_Inertia
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_InducedCharacter
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_IrrIndexing
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.RingTheory.SimpleModule.Basic

namespace OddOrder.RepresentationTheory

open scoped BigOperators

variable {G : Type*} [Group G]

namespace Representation

variable {k : Type*} [Field k]

variable {V : Type*} [AddCommGroup V] [Module k V]

/-- Pulling a representation back along a group automorphism preserves irreducibility. -/
theorem IsIrreducible.comp_mulEquiv
    (ρ : Representation k G V) [Representation.IsIrreducible ρ] (e : G ≃* G) :
    Representation.IsIrreducible (ρ.comp e.toMonoidHom) := by
  change IsSimpleOrder (Subrepresentation (ρ.comp e.toMonoidHom))
  refine { toNontrivial := ?_, eq_bot_or_eq_top := ?_ }
  · refine ⟨⟨⊥, ⊤, ?_⟩⟩
    intro hbot
    have hsub :
        ((⊥ : Subrepresentation (ρ.comp e.toMonoidHom)).toSubmodule) =
          ((⊤ : Subrepresentation (ρ.comp e.toMonoidHom)).toSubmodule) :=
      congrArg Subrepresentation.toSubmodule hbot
    have hρbot : (⊥ : Subrepresentation ρ) = ⊤ := by
      apply Subrepresentation.toSubmodule_injective
      -- `(⊥/⊤ : Subrepresentation _).toSubmodule` is `⊥/⊤ : Submodule k V` by `rfl` for
      -- both `ρ` and `ρ.comp e.toMonoidHom`, so `hsub` closes the goal definitionally.
      exact hsub
    exact IsSimpleOrder.bot_ne_top hρbot
  · intro W
    let Wρ : Subrepresentation ρ := {
      toSubmodule := W.toSubmodule
      apply_mem_toSubmodule h {v} hv := by
        rcases e.surjective h with ⟨h', rfl⟩
        exact W.apply_mem_toSubmodule h' hv }
    rcases IsSimpleOrder.eq_bot_or_eq_top Wρ with hbot | htop
    · left
      apply Subrepresentation.toSubmodule_injective
      -- `Wρ.toSubmodule = W.toSubmodule` and `(⊥ : Subrepresentation _).toSubmodule = ⊥`
      -- both hold by `rfl`, so the `congrArg` proof closes the goal definitionally.
      exact congrArg (fun X : Subrepresentation ρ => X.toSubmodule) hbot
    · right
      apply Subrepresentation.toSubmodule_injective
      exact congrArg (fun X : Subrepresentation ρ => X.toSubmodule) htop

end Representation

namespace Representation

open scoped MonoidAlgebra

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

section ConjBySimple

variable (ρ : Representation ℂ G V) (H : Subgroup G) [hH : H.Normal]

/-- The restriction `Res^G_H ρ` of `ρ` to a subgroup `H`, packaged as a
`Representation ℂ ↥H V` (rather than the bare `MonoidHom` `ρ.comp H.subtype`) so that
its `ℂ[H]`-module `asModule` and `asModuleEquiv` are available by dot notation.

This is a reducible abbreviation so that the `ℂ[H]`-module instance on
`(restrictRep ρ H).asModule` is found by unfolding to `(ρ.comp H.subtype).asModule`. -/
abbrev restrictRep : Representation ℂ ↥H V := ρ.comp H.subtype

omit hH in
@[simp] theorem restrictRep_apply (h : ↥H) : restrictRep ρ H h = ρ (h : G) := rfl

variable {H}

/-- The ring automorphism of `ℂ[H]` induced by conjugation `h ↦ g h g⁻¹` on the normal
subgroup `H`.  On generators it sends `single h c` to `single (g h g⁻¹) c`. -/
noncomputable def conjBySimpleRingHom (g : G) : ℂ[↥H] →+* ℂ[↥H] :=
  MonoidAlgebra.mapDomainRingHom ℂ
    (ClassFunction.conjByMulEquiv (G := G) (H := H) g).toMonoidHom

theorem conjBySimpleRingHom_single (g : G) (h : ↥H) (c : ℂ) :
    conjBySimpleRingHom (H := H) g (MonoidAlgebra.single h c) =
      MonoidAlgebra.single
        (ClassFunction.conjByMulEquiv (G := G) (H := H) g h) c := by
  simp [conjBySimpleRingHom]

theorem conjBySimpleRingHom_surjective (g : G) :
    Function.Surjective (conjBySimpleRingHom (H := H) g) :=
  (MonoidAlgebra.mapDomainRingEquiv ℂ
    (ClassFunction.conjByMulEquiv (G := G) (H := H) g)).surjective

instance conjBySimpleRingHom_isSurjective (g : G) :
    RingHomSurjective (conjBySimpleRingHom (H := H) g) :=
  ⟨conjBySimpleRingHom_surjective (H := H) g⟩

set_option backward.isDefEq.respectTransparency false in
/-- The `ℂ`-linear bijection `ρ g`, packaged as a `conjBySimpleRingHom g`-semilinear
endomorphism of the restricted module `(restrictRep ρ H).asModule`.

This is the module-theoretic incarnation of normality: for `h ∈ H`, the standard
`ℂ[H]`-action on the image satisfies `h • (ρ g v) = ρ g (ρ (g⁻¹ h g) v)`, i.e. `ρ g`
intertwines the `H`-action up to the conjugation twist `conjBySimpleRingHom g`. -/
noncomputable def conjBySimpleSemilinear (g : G) :
    (restrictRep ρ H).asModule →ₛₗ[conjBySimpleRingHom (H := H) g]
      (restrictRep ρ H).asModule where
  toFun v := (show (restrictRep ρ H).asModule from ρ g v)
  map_add' v w := by simp
  map_smul' s v := by
    induction s using MonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy =>
        change ρ g ((x + y) • v) = _
        rw [add_smul, map_add, map_add, add_smul]
        exact congrArg₂ (· + ·) hx hy
    | single h c =>
        have hHh : (ClassFunction.conjByMulEquiv (G := G) (H := H) g h : G) =
            g * (h : G) * g⁻¹ := rfl
        rw [conjBySimpleRingHom_single]
        change ρ g (MonoidAlgebra.single h c • v) =
          MonoidAlgebra.single (ClassFunction.conjByMulEquiv (G := G) (H := H) g h) c •
            (show (restrictRep ρ H).asModule from ρ g v)
        rw [Representation.single_smul, Representation.single_smul, restrictRep_apply,
          restrictRep_apply, map_smul]
        congr 1
        change ρ g (ρ (h : G) v) = ρ ((ClassFunction.conjByMulEquiv
          (G := G) (H := H) g h : G)) (ρ g v)
        rw [hHh, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
        congr 2
        group

@[simp] theorem conjBySimpleSemilinear_apply (g : G) (v : (restrictRep ρ H).asModule) :
    conjBySimpleSemilinear (H := H) ρ g v = (show (restrictRep ρ H).asModule from ρ g v) :=
  rfl

end ConjBySimple

end Representation

namespace ClassFunction

variable (H : Subgroup G) [Fintype H] [Invertible (Nat.card H : ℂ)]

/-- The normalized inner-product multiplicity of `θ` in `Res^G_H χ`.

For irreducible characters this is the usual constituent multiplicity.  It is
kept as a complex scalar here because the integral/nonnegative-integer
multiplicity theorem is part of the later Clifford proof core. -/
def restrictionMultiplicity (χ : ClassFunction G ℂ) (θ : ClassFunction H ℂ) : ℂ :=
  inner (restrict H χ) θ

@[simp] theorem restrictionMultiplicity_def
    (χ : ClassFunction G ℂ) (θ : ClassFunction H ℂ) :
    restrictionMultiplicity H χ θ = inner (restrict H χ) θ :=
  rfl

@[simp] theorem restrictionMultiplicity_zero_left (θ : ClassFunction H ℂ) :
    restrictionMultiplicity H (0 : ClassFunction G ℂ) θ = 0 := by
  simp [restrictionMultiplicity]

@[simp] theorem restrictionMultiplicity_zero_right (χ : ClassFunction G ℂ) :
    restrictionMultiplicity H χ (0 : ClassFunction H ℂ) = 0 := by
  simp [restrictionMultiplicity]

theorem restrictionMultiplicity_conjBy_right [H.Normal]
    (χ : ClassFunction G ℂ) (θ : ClassFunction H ℂ) (g : G) :
    restrictionMultiplicity H χ (conjBy (G := G) (H := H) g θ) =
      restrictionMultiplicity H χ θ := by
  change inner (restrict H χ) (conjBy (G := G) (H := H) g θ) =
    inner (restrict H χ) θ
  calc
    inner (restrict H χ) (conjBy (G := G) (H := H) g θ) =
        inner (conjBy (G := G) (H := H) g (restrict H χ))
          (conjBy (G := G) (H := H) g θ) := by
          rw [conjBy_restrict (G := G) (H := H) g χ]
    _ = inner (restrict H χ) θ :=
        inner_conjBy_conjBy (G := G) (H := H) g (restrict H χ) θ

/-- **Integrality of the restriction multiplicity.** When the inducing class function
`χ` and the constituent `θ` are both virtual characters, the normalized inner-product
multiplicity `⟨Res^G_H χ, θ⟩` is an integer.

This resolves the integer part of Clifford's multiplicity statement ([Is] Thm 6.5): the
multiplicity `e_χ = ⟨Res χ, θ⟩` is `ℤ`-valued.  The proof combines `restrict_mem_ZIrr`
(restriction maps `ℤ[Irr G]` into `ℤ[Irr H]`, Peterfalvi (2.6.b)) with the integrality of
inner products of virtual characters (`inner_mem_ZIrr_int`).  Non-negativity of the
multiplicity for a *genuine* character is a separate fact that needs the module-theoretic
decomposition of `Res^G_H ρ` (see `issues/0026-peterfalvi-clifford-core.md`). -/
theorem restrictionMultiplicity_int [Finite G]
    {χ : ClassFunction G ℂ} (hχ : χ ∈ ZIrr G)
    {θ : ClassFunction H ℂ} (hθ : θ ∈ ZIrr H) :
    ∃ m : ℤ, restrictionMultiplicity H χ θ = (m : ℂ) :=
  inner_mem_ZIrr_int (restrict_mem_ZIrr H hχ) hθ

/-- **Hom-dimension formula for the restriction multiplicity.** When `χ = χ_ρ` is the
character of a finite-dimensional `ℂ`-representation `ρ` of `G` and `θ = χ_σ` is the
character of a finite-dimensional `ℂ`-representation `σ` of `H`, the normalized
inner-product multiplicity `⟨Res^G_H χ, θ⟩` equals the `ℂ`-dimension of the space of
`H`-equivariant maps `σ ⟶ Res^G_H ρ`:

  `⟨Res^G_H χ, θ⟩ = dim_ℂ Hom_{ℂ[H]}(σ, ρ|_H)`.

This is the module-theoretic identification of the multiplicity: it is the number of
copies (counted with `Hom`-dimension) of the simple `σ` inside the genuine `H`-module
`ρ|_H`.  The proof rewrites the inner sum into the `σ.character g⁻¹` form using
`character_inv` and then applies mathlib's
`Representation.card_inv_mul_sum_char_mul_char_eq_finrank`. -/
theorem restrictionMultiplicity_eq_finrank_intertwiningMap
    {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V)
    {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (σ : Representation ℂ ↥H W)
    {χ : ClassFunction G ℂ} (hχ : (χ : G → ℂ) = ρ.character)
    {θ : ClassFunction H ℂ} (hθ : (θ : ↥H → ℂ) = σ.character) :
    restrictionMultiplicity H χ θ =
      (Module.finrank ℂ
        (Representation.IntertwiningMap σ (ρ.comp H.subtype :
          Representation ℂ ↥H V)) : ℂ) := by
  classical
  have : Finite ↥H := Finite.of_fintype _
  set ρ' : Representation ℂ ↥H V := ρ.comp H.subtype with hρ'
  rw [restrictionMultiplicity, inner_eq_inv_card_mul_innerSum, innerSum]
  have hcharρ' : ∀ h : ↥H, χ (h : G) = ρ'.character h := fun h => by
    rw [congrFun hχ (h : G)]
    rfl
  have hsum :
      ∑ h : ↥H, (restrict H χ) h * star (θ h)
        = ∑ h : ↥H, ρ'.character h * σ.character h⁻¹ := by
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [restrict_apply, hcharρ' h, congrFun hθ h, ← character_inv σ h]
  rw [hsum, invOf_eq_inv,
    ← Representation.card_inv_mul_sum_char_mul_char_eq_finrank σ ρ']

open scoped ComplexOrder in
/-- **Non-negativity of the restriction multiplicity** (nonneg half of Clifford's
multiplicity statement, [Is] Thm 6.5).  For irreducible characters `χ` of `G` and `θ` of
`H`, the normalized inner-product multiplicity `⟨Res^G_H χ, θ⟩` is `≥ 0`.

Together with `restrictionMultiplicity_int` (its integrality), this shows the multiplicity
is a non-negative integer, as required by Clifford's theorem.  The non-negativity is the
genuine-character fact: the constituent multiplicity is a count, never negative.  The proof
realizes `χ` and `θ` by representations `ρ`, `σ` and identifies the multiplicity with the
`ℂ`-dimension `dim_ℂ Hom_{ℂ[H]}(σ, ρ|_H)` via
`restrictionMultiplicity_eq_finrank_intertwiningMap`; a dimension is a cast natural number,
hence `0 ≤`.

Only the genuine-character provenance of `χ`, `θ` is used (not irreducibility): the same
proof gives `0 ≤ ⟨Res^G_H χ, θ⟩` whenever `χ` and `θ` are characters of finite-dimensional
representations.  Note this routes through mathlib's Hom-dimension characterization of the
character scalar product, *not* through an explicit Maschke isotype decomposition. -/
theorem restrictionMultiplicity_nonneg
    {χ : ClassFunction G ℂ} (hχ : IsIrreducibleCharacter χ)
    {θ : ClassFunction H ℂ} (hθ : IsIrreducibleCharacter θ) :
    0 ≤ restrictionMultiplicity H χ θ := by
  obtain ⟨V, _, _, _, ρ, _, hχρ⟩ := hχ
  obtain ⟨W, _, _, _, σ, _, hθσ⟩ := hθ
  rw [restrictionMultiplicity_eq_finrank_intertwiningMap H ρ σ hχρ hθσ]
  exact Nat.cast_nonneg _

open scoped ComplexOrder in
/-- **The restriction multiplicity is a non-negative integer** (the full multiplicity
statement of Clifford's theorem, [Is] Thm 6.5).  For irreducible characters `χ` of `G`
and `θ` of `H`, the normalized inner-product multiplicity `⟨Res^G_H χ, θ⟩ = (k : ℂ)` for
some `k : ℕ`.

This combines the two halves established separately: the integrality
`restrictionMultiplicity_int` (`⟨Res χ, θ⟩ = m` for some `m : ℤ`, via the virtual-character
inner product) and the non-negativity `restrictionMultiplicity_nonneg`
(`0 ≤ ⟨Res χ, θ⟩`, via the `Hom`-dimension formula).  A non-negative integer is a natural
number (`m ≥ 0` from `0 ≤ (m : ℂ)`, then `k = m.toNat`).  This is the form Clifford's
theorem consumes: the constituent multiplicity `e_χ` is the *count* of copies of `θ` in
`Res^G_H χ`, a non-negative integer. -/
theorem restrictionMultiplicity_natCast [Finite G]
    {χ : ClassFunction G ℂ} (hχ : IsIrreducibleCharacter χ)
    {θ : ClassFunction H ℂ} (hθ : IsIrreducibleCharacter θ) :
    ∃ k : ℕ, restrictionMultiplicity H χ θ = (k : ℂ) := by
  obtain ⟨m, hm⟩ := restrictionMultiplicity_int H hχ.mem_ZIrr hθ.mem_ZIrr
  have hnn : (0 : ℂ) ≤ (m : ℂ) := hm ▸ restrictionMultiplicity_nonneg H hχ hθ
  have hm0 : 0 ≤ m := by exact_mod_cast hnn
  refine ⟨m.toNat, ?_⟩
  rw [hm]
  exact_mod_cast (Int.toNat_of_nonneg hm0).symm

omit [Fintype H] [Invertible (Nat.card H : ℂ)] in
theorem IsIrreducibleCharacter.conjBy [H.Normal]
    {θ : ClassFunction H ℂ} (hθ : IsIrreducibleCharacter θ) (g : G) :
    IsIrreducibleCharacter (conjBy (G := G) (H := H) g θ) := by
  rcases hθ with ⟨V, hVAdd, hVModule, hVFinite, ρ, hρ, hchar⟩
  let : AddCommGroup V := hVAdd
  let : Module ℂ V := hVModule
  let : FiniteDimensional ℂ V := hVFinite
  let ρg : Representation ℂ H V :=
    ρ.comp (conjByMulEquiv (G := G) (H := H) g).toMonoidHom
  refine ⟨V, inferInstance, inferInstance, inferInstance, ρg, ?_, ?_⟩
  · exact Representation.IsIrreducible.comp_mulEquiv ρ
      (conjByMulEquiv (G := G) (H := H) g)
  · funext h
    change θ (conjByMulEquiv (G := G) (H := H) g h) = ρg.character h
    rw [hchar]
    rfl

section InduceConjBy

omit [Fintype H] [Invertible (Nat.card H : ℂ)] in
/-- Conjugating the inducing class function by an ambient `g : G` does not change the
unscaled induced class function on a normal subgroup: `Ind_H^G (θ^g) = Ind_H^G θ`. -/
theorem induceSum_conjBy_eq [Fintype G] [hH : H.Normal] (g : G) (θ : ClassFunction ↥H ℂ) :
    induceSum H (conjBy (G := G) (H := H) g θ) = induceSum H θ := by
  ext g₀
  classical
  simp only [induceSum_apply]
  refine (Fintype.sum_equiv (Equiv.mulRight g)
    (fun x' => induceTerm H θ x' g₀)
    (fun x => induceTerm H (conjBy (G := G) (H := H) g θ) x g₀) ?_).symm
  intro x'
  change induceTerm H θ x' g₀ = induceTerm H (conjBy (G := G) (H := H) g θ) (x' * g) g₀
  unfold induceTerm
  by_cases hx : x'⁻¹ * g₀ * x' ∈ H
  · have hxg : (x' * g)⁻¹ * g₀ * (x' * g) ∈ H := by
      have hmem : g⁻¹ * (x'⁻¹ * g₀ * x') * g⁻¹⁻¹ ∈ H := hH.conj_mem _ hx g⁻¹
      have heq : g⁻¹ * (x'⁻¹ * g₀ * x') * g⁻¹⁻¹ = (x' * g)⁻¹ * g₀ * (x' * g) := by group
      rwa [heq] at hmem
    rw [dif_pos hx, dif_pos hxg, conjBy_apply]
    refine congrArg (θ : ↥H → ℂ) (Subtype.ext ?_)
    change (x'⁻¹ * g₀ * x' : G) = g * ((x' * g)⁻¹ * g₀ * (x' * g)) * g⁻¹
    group
  · have hxg : (x' * g)⁻¹ * g₀ * (x' * g) ∉ H := by
      intro hxg
      apply hx
      have hmem : g * ((x' * g)⁻¹ * g₀ * (x' * g)) * g⁻¹ ∈ H := hH.conj_mem _ hxg g
      have heq : g * ((x' * g)⁻¹ * g₀ * (x' * g)) * g⁻¹ = x'⁻¹ * g₀ * x' := by group
      rwa [heq] at hmem
    rw [dif_neg hx, dif_neg hxg]

omit [Fintype H] in
/-- Conjugating the inducing class function by an ambient `g : G` does not change the
normalized induced character on a normal subgroup: `Ind_H^G (θ^g) = Ind_H^G θ`.

This is Peterfalvi (1.5)(a) at the class-function level: the induced character is
invariant under `G`-conjugation of the inducing character. -/
theorem induce_conjBy_eq [Fintype G] [H.Normal] (g : G) (θ : ClassFunction ↥H ℂ) :
    induce H (conjBy (G := G) (H := H) g θ) = induce H θ := by
  rw [induce, induce, induceSum_conjBy_eq]

end InduceConjBy

end ClassFunction

namespace IrreducibleCharacter

variable (H : Subgroup G) [Fintype H] [Invertible (Nat.card H : ℂ)]

/-- An irreducible character `χ` of `G` **lies over** an irreducible character
`θ` of `H` if `θ` occurs in `Res^G_H χ` with nonzero multiplicity. -/
def LiesOver (χ : IrreducibleCharacter G) (θ : IrreducibleCharacter H) : Prop :=
  ClassFunction.restrictionMultiplicity H (χ : ClassFunction G ℂ)
      (θ : ClassFunction H ℂ) ≠ 0

theorem liesOver_iff (χ : IrreducibleCharacter G) (θ : IrreducibleCharacter H) :
    LiesOver H χ θ ↔
      ClassFunction.restrictionMultiplicity H (χ : ClassFunction G ℂ)
          (θ : ClassFunction H ℂ) ≠ 0 :=
  Iff.rfl

/-- **Constituent-of-induction ⟺ lies-over bridge** (Frobenius reciprocity at the
constituent level).  For `θ ∈ Irr H` and `χ ∈ Irr G`, the irreducible `χ` is a constituent
of the induced character `Ind_H^G θ` — i.e. `⟨Ind_H^G θ, χ⟩ ≠ 0` — exactly when `χ` lies over
`θ`.

This packages numerical Frobenius reciprocity
(`ClassFunction.inner_induce_eq_inner_restrict`: `⟨Ind θ, χ⟩ = ⟨θ, Res χ⟩`) into the
constituent/`LiesOver` language: the constituent multiplicity `⟨θ, Res χ⟩` is the conjugate of
the restriction multiplicity `⟨Res χ, θ⟩ = restrictionMultiplicity H χ θ`, so the two
non-vanishing conditions agree.  This is the bridge that Peterfalvi (6.6) needs to pass between
"`χ` is a constituent of `Ind_K^L θ`" and "`χ` lies over `θ`". -/
theorem inner_induce_ne_zero_iff_liesOver [Fintype G] [Invertible (Nat.card G : ℂ)]
    (χ : IrreducibleCharacter G) (θ : IrreducibleCharacter H) :
    ClassFunction.inner (ClassFunction.induce H (θ : ClassFunction H ℂ))
        (χ : ClassFunction G ℂ) ≠ 0 ↔ LiesOver H χ θ := by
  rw [ClassFunction.inner_induce_eq_inner_restrict, liesOver_iff,
    ClassFunction.restrictionMultiplicity_def,
    inner_conj_symm (ClassFunction.restrict H (χ : ClassFunction G ℂ))
      (θ : ClassFunction H ℂ)]
  exact star_ne_zero

/-- **The constituent multiplicity of an irreducible character is a non-negative integer**
(the full multiplicity statement of Clifford's theorem, [Is] Thm 6.5).  For irreducible
characters `χ` of `G` and `θ` of `H`, the normalized inner product
`⟨Res^G_H χ, θ⟩ = (k : ℂ)` for some `k : ℕ`.  This is the irreducible-character
specialization of `ClassFunction.restrictionMultiplicity_natCast`: the constituent
multiplicity `e_χ` is the count of copies of `θ` in `Res^G_H χ`. -/
theorem restrictionMultiplicity_natCast [Finite G]
    (χ : IrreducibleCharacter G) (θ : IrreducibleCharacter H) :
    ∃ k : ℕ, ClassFunction.restrictionMultiplicity H (χ : ClassFunction G ℂ)
        (θ : ClassFunction H ℂ) = (k : ℂ) :=
  ClassFunction.restrictionMultiplicity_natCast H χ.isIrreducible θ.isIrreducible

/-- **Lies-over existence.**  For any subgroup `H` and any irreducible character `χ` of `G`,
there is an irreducible character `θ` of `H` over which `χ` lies — i.e. `θ` occurs in the
restriction `Res^G_H χ` with nonzero multiplicity.

This is elementary completeness: the restriction `Res^G_H χ` is nonzero (its value at `1` is
`χ(1)`, the positive character degree), so it cannot be orthogonal to *every* irreducible
character of `H` (`classFunction_eq_zero_of_orthogonal`), and any irreducible `θ` with nonzero
inner product is one `χ` lies over.  (Normality of `H` is not needed for existence.)  Together
with `inner_induce_ne_zero_iff_liesOver`, this is the input the case-B `X`-characterization
needs: each constituent has an irreducible to lie over. -/
theorem exists_liesOver [Finite G]
    (χ : IrreducibleCharacter G) :
    ∃ θ : IrreducibleCharacter H, LiesOver H χ θ := by
  classical
  have : Finite H := Subtype.finite
  -- The restricted character is nonzero: its value at `1` is the positive degree `χ(1)`.
  have hne : ClassFunction.restrict H (χ : ClassFunction G ℂ) ≠ 0 := by
    obtain ⟨n, hpos, hval, _⟩ :=
      χ.isIrreducible.exists_natDegree_charValue_one_dvd_card
    intro hzero
    have h1 : ClassFunction.restrict H (χ : ClassFunction G ℂ) (1 : ↥H) = 0 := by
      rw [hzero]; rfl
    rw [ClassFunction.restrict_apply, Subgroup.coe_one, hval] at h1
    exact (Nat.cast_ne_zero.mpr hpos.ne') h1
  -- Completeness: a nonzero class function is not orthogonal to all irreducibles.
  by_contra hcon
  refine hne (classFunction_eq_zero_of_orthogonal
    (ClassFunction.restrict H (χ : ClassFunction G ℂ)) fun θ => ?_)
  by_contra hθ
  exact hcon ⟨θ, by rw [liesOver_iff, ClassFunction.restrictionMultiplicity_def]; exact hθ⟩

end IrreducibleCharacter

variable {H : Subgroup G} [hH : H.Normal]

namespace IrreducibleCharacter

/-- Conjugate an irreducible character of `H` by an ambient element of `G`.

The underlying class function is `ClassFunction.conjBy`; irreducibility is preserved by
pulling the representing module back along the induced automorphism of `H`. -/
def conjBy (g : G) (θ : IrreducibleCharacter H) : IrreducibleCharacter H :=
  ⟨ClassFunction.conjBy (G := G) (H := H) g (θ : ClassFunction H ℂ),
    ClassFunction.IsIrreducibleCharacter.conjBy (H := H) θ.isIrreducible g⟩

@[simp] theorem coe_conjBy (g : G) (θ : IrreducibleCharacter H) :
    (conjBy (G := G) (H := H) g θ : ClassFunction H ℂ) =
      ClassFunction.conjBy (G := G) (H := H) g (θ : ClassFunction H ℂ) :=
  rfl

@[simp] theorem conjBy_one (θ : IrreducibleCharacter H) :
    conjBy (G := G) (H := H) (1 : G) θ = θ := by
  apply IrreducibleCharacter.ext
  simp

theorem conjBy_mul (g₁ g₂ : G) (θ : IrreducibleCharacter H) :
    conjBy (G := G) (H := H) (g₁ * g₂) θ =
      conjBy (G := G) (H := H) g₂ (conjBy (G := G) (H := H) g₁ θ) := by
  apply IrreducibleCharacter.ext
  exact ClassFunction.conjBy_mul (G := G) (H := H) g₁ g₂ (θ : ClassFunction H ℂ)

@[simp] theorem conjBy_inv_conjBy (g : G) (θ : IrreducibleCharacter H) :
    conjBy (G := G) (H := H) g⁻¹ (conjBy (G := G) (H := H) g θ) = θ := by
  apply IrreducibleCharacter.ext
  simp

@[simp] theorem conjBy_conjBy_inv (g : G) (θ : IrreducibleCharacter H) :
    conjBy (G := G) (H := H) g (conjBy (G := G) (H := H) g⁻¹ θ) = θ := by
  apply IrreducibleCharacter.ext
  simp

/-- The inertia subgroup of an irreducible character, viewed at the
irreducible-character level. -/
abbrev inertia (θ : IrreducibleCharacter H) : Subgroup G :=
  ClassFunction.inertia (G := G) (H := H) (θ : ClassFunction H ℂ)

@[simp] theorem mem_inertia {θ : IrreducibleCharacter H} {g : G} :
    g ∈ inertia (G := G) (H := H) θ ↔
      conjBy (G := G) (H := H) g θ = θ := by
  change ClassFunction.conjBy (G := G) (H := H) g (θ : ClassFunction H ℂ) =
      (θ : ClassFunction H ℂ) ↔
        conjBy (G := G) (H := H) g θ = θ
  constructor
  · intro h
    exact IrreducibleCharacter.ext h
  · intro h
    exact congrArg (fun η : IrreducibleCharacter H => (η : ClassFunction H ℂ)) h

theorem subgroup_le_inertia (θ : IrreducibleCharacter H) :
    H ≤ inertia (G := G) (H := H) θ :=
  ClassFunction.subgroup_le_inertia (θ : ClassFunction H ℂ)

theorem conjBy_eq_conjBy_iff_mul_inv_mem_inertia
    (θ : IrreducibleCharacter H) (g h : G) :
    conjBy (G := G) (H := H) g θ = conjBy (G := G) (H := H) h θ ↔
      g * h⁻¹ ∈ inertia (G := G) (H := H) θ := by
  constructor
  · intro hgh
    rw [mem_inertia]
    calc
      conjBy (G := G) (H := H) (g * h⁻¹) θ =
          conjBy (G := G) (H := H) h⁻¹ (conjBy (G := G) (H := H) g θ) :=
            conjBy_mul (G := G) (H := H) g h⁻¹ θ
      _ = conjBy (G := G) (H := H) h⁻¹ (conjBy (G := G) (H := H) h θ) := by
            rw [hgh]
      _ = θ := conjBy_inv_conjBy (G := G) (H := H) h θ
  · intro hmem
    rw [mem_inertia] at hmem
    have hcalc :
        conjBy (G := G) (H := H) h⁻¹ (conjBy (G := G) (H := H) g θ) = θ := by
      rwa [← conjBy_mul (G := G) (H := H) g h⁻¹ θ]
    calc
      conjBy (G := G) (H := H) g θ =
          conjBy (G := G) (H := H) h
            (conjBy (G := G) (H := H) h⁻¹ (conjBy (G := G) (H := H) g θ)) := by
            exact (conjBy_conjBy_inv (G := G) (H := H) h
              (conjBy (G := G) (H := H) g θ)).symm
      _ = conjBy (G := G) (H := H) h θ := by
            rw [hcalc]

/-- The ambient `G`-orbit of an irreducible character of a normal subgroup. -/
def conjByOrbit (θ : IrreducibleCharacter H) : Set (IrreducibleCharacter H) :=
  Set.range fun g : G => conjBy (G := G) (H := H) g θ

@[simp] theorem mem_conjByOrbit {θ η : IrreducibleCharacter H} :
    η ∈ conjByOrbit (G := G) (H := H) θ ↔
      ∃ g : G, conjBy (G := G) (H := H) g θ = η :=
  Iff.rfl

theorem conjBy_mem_conjByOrbit (θ : IrreducibleCharacter H) (g : G) :
    conjBy (G := G) (H := H) g θ ∈ conjByOrbit (G := G) (H := H) θ :=
  ⟨g, rfl⟩

/-- The orbit of `θ` is parametrized by right cosets of its inertia subgroup.

The right-coset convention matches `conjBy_eq_conjBy_iff_mul_inv_mem_inertia`,
which identifies `θ^g` and `θ^h` exactly when `g * h⁻¹ ∈ I_G(θ)`. -/
noncomputable def conjByOrbitEquivRightCosets (θ : IrreducibleCharacter H) :
    Quotient (QuotientGroup.rightRel (inertia (G := G) (H := H) θ)) ≃
      {η : IrreducibleCharacter H // η ∈ conjByOrbit (G := G) (H := H) θ} where
  toFun :=
    Quotient.lift
      (fun g : G =>
        ⟨conjBy (G := G) (H := H) g θ, conjBy_mem_conjByOrbit (G := G) (H := H) θ g⟩)
      (by
        intro g h hgh
        apply Subtype.ext
        have hmem : h * g⁻¹ ∈ inertia (G := G) (H := H) θ :=
          QuotientGroup.rightRel_apply.mp hgh
        have hchg :
            conjBy (G := G) (H := H) h θ =
              conjBy (G := G) (H := H) g θ :=
          Iff.mpr (conjBy_eq_conjBy_iff_mul_inv_mem_inertia
            (G := G) (H := H) θ h g) hmem
        exact hchg.symm)
  invFun η := Quotient.mk'' (Classical.choose η.property)
  left_inv := by
    intro q
    refine Quotient.inductionOn' q ?_
    intro g
    dsimp
    have hchoose :
        conjBy (G := G) (H := H) (Classical.choose
          (conjBy_mem_conjByOrbit (G := G) (H := H) θ g)) θ =
            conjBy (G := G) (H := H) g θ :=
      Classical.choose_spec (conjBy_mem_conjByOrbit (G := G) (H := H) θ g)
    apply Quotient.sound'
    rw [QuotientGroup.rightRel_apply]
    exact Iff.mp (conjBy_eq_conjBy_iff_mul_inv_mem_inertia
      (G := G) (H := H) θ g
      (Classical.choose (conjBy_mem_conjByOrbit (G := G) (H := H) θ g)))
        hchoose.symm
  right_inv := by
    intro η
    apply Subtype.ext
    exact Classical.choose_spec η.property

/-- The same orbit parametrization, expressed with mathlib's standard left-coset
quotient notation `G ⧸ I_G(θ)`. -/
noncomputable def conjByOrbitEquivLeftCosets (θ : IrreducibleCharacter H) :
    G ⧸ inertia (G := G) (H := H) θ ≃
      {η : IrreducibleCharacter H // η ∈ conjByOrbit (G := G) (H := H) θ} :=
  (QuotientGroup.quotientRightRelEquivQuotientLeftRel
    (inertia (G := G) (H := H) θ)).symm.trans
      (conjByOrbitEquivRightCosets (G := G) (H := H) θ)

variable [Fintype H] [Invertible (Nat.card H : ℂ)]

/-- Predicate form of the Clifford conclusion that all irreducible constituents
of `Res^G_H χ` lie in one `G`-conjugation orbit. -/
def RestrictionConstituentsSingleOrbit (χ : IrreducibleCharacter G) : Prop :=
  ∀ θ η : IrreducibleCharacter H,
    LiesOver H χ θ → LiesOver H χ η →
      ∃ g : G, conjBy (G := G) (H := H) g θ = η

/-- Predicate form of the Clifford conclusion that all constituents of
`Res^G_H χ` occur with a common normalized inner-product multiplicity. -/
def HasCommonRestrictionMultiplicity (χ : IrreducibleCharacter G) : Prop :=
  ∃ e : ℂ, ∀ θ : IrreducibleCharacter H, LiesOver H χ θ →
    ClassFunction.restrictionMultiplicity H (χ : ClassFunction G ℂ)
      (θ : ClassFunction H ℂ) = e

theorem RestrictionConstituentsSingleOrbit.exists_conj
    {χ : IrreducibleCharacter G}
    (hχ : RestrictionConstituentsSingleOrbit (H := H) χ)
    {θ η : IrreducibleCharacter H}
    (hθ : LiesOver H χ θ) (hη : LiesOver H χ η) :
    ∃ g : G, conjBy (G := G) (H := H) g θ = η :=
  hχ θ η hθ hη

theorem liesOver_conjBy
    {χ : IrreducibleCharacter G} {θ : IrreducibleCharacter H}
    (hθ : LiesOver H χ θ) (g : G) :
    LiesOver H χ (conjBy (G := G) (H := H) g θ) := by
  change ClassFunction.restrictionMultiplicity H (χ : ClassFunction G ℂ)
      (ClassFunction.conjBy (G := G) (H := H) g (θ : ClassFunction H ℂ)) ≠ 0
  rw [ClassFunction.restrictionMultiplicity_conjBy_right
    (H := H) (χ : ClassFunction G ℂ) (θ : ClassFunction H ℂ) g]
  exact hθ

theorem liesOver_conjBy_iff
    (χ : IrreducibleCharacter G) (θ : IrreducibleCharacter H) (g : G) :
    LiesOver H χ (conjBy (G := G) (H := H) g θ) ↔ LiesOver H χ θ := by
  constructor
  · intro hθ
    have hθ' := liesOver_conjBy (H := H) hθ g⁻¹
    simpa using hθ'
  · intro hθ
    exact liesOver_conjBy (H := H) hθ g

omit hH in
theorem HasCommonRestrictionMultiplicity.eq_of_liesOver
    {χ : IrreducibleCharacter G}
    (hχ : HasCommonRestrictionMultiplicity (H := H) χ)
    {θ η : IrreducibleCharacter H}
    (hθ : LiesOver H χ θ) (hη : LiesOver H χ η) :
    ClassFunction.restrictionMultiplicity H (χ : ClassFunction G ℂ)
        (θ : ClassFunction H ℂ) =
      ClassFunction.restrictionMultiplicity H (χ : ClassFunction G ℂ)
        (η : ClassFunction H ℂ) := by
  rcases hχ with ⟨e, he⟩
  rw [he θ hθ, he η hη]

/-- **Clifford common-multiplicity step** ([Is] Thm 6.5, second clause): once the
irreducible constituents of `Res^G_H χ` form a single `G`-conjugation orbit, they all
occur with the same normalized multiplicity.

This is the orbit-transitivity ⇒ common-multiplicity implication of Clifford's theorem.
The common value is `⟨Res χ, θ₀⟩` at any constituent `θ₀`; for any other constituent `η`,
single-orbit transitivity provides `g` with `θ₀^g = η`, and
`restrictionMultiplicity_conjBy_right` shows conjugation preserves the multiplicity. -/
theorem hasCommonRestrictionMultiplicity_of_singleOrbit
    {χ : IrreducibleCharacter G}
    (hχ : RestrictionConstituentsSingleOrbit (H := H) χ) :
    HasCommonRestrictionMultiplicity (H := H) χ := by
  classical
  by_cases hex : ∃ θ₀ : IrreducibleCharacter H, LiesOver H χ θ₀
  · obtain ⟨θ₀, hθ₀⟩ := hex
    refine ⟨ClassFunction.restrictionMultiplicity H (χ : ClassFunction G ℂ)
      (θ₀ : ClassFunction H ℂ), fun η hη => ?_⟩
    obtain ⟨g, hg⟩ := hχ θ₀ η hθ₀ hη
    rw [← hg, coe_conjBy,
      ClassFunction.restrictionMultiplicity_conjBy_right
        (H := H) (χ : ClassFunction G ℂ) (θ₀ : ClassFunction H ℂ) g]
  · -- No constituent: the universally quantified condition is vacuously satisfiable.
    refine ⟨0, fun θ hθ => ?_⟩
    exact absurd ⟨θ, hθ⟩ hex

end IrreducibleCharacter

section GenuineDecomposition

variable [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]

omit [Fintype G] [Invertible (Nat.card G : ℂ)] in
/-- A genuine character is a virtual character: `IsCharacter χ ⟹ χ ∈ ZIrr G`.  Immediate
from `character_mem_ZIrr` once `χ` is identified with the canonical class function of its
witnessing representation. -/
theorem IsCharacter.mem_ZIrr {χ : ClassFunction G ℂ} (hχ : IsCharacter χ) : χ ∈ ZIrr G := by
  obtain ⟨V, _, _, _, ρ, hρ⟩ := hχ
  have hχeq : χ = (⟨ρ.character, fun g h => ρ.char_conj g h⟩ : ClassFunction G ℂ) :=
    ClassFunction.ext fun g => congrFun hρ g
  rw [hχeq]
  exact character_mem_ZIrr ρ

open scoped ComplexOrder in
/-- **The Fourier coefficient of a genuine character at an irreducible character is a
non-negative integer.**  For `χ = χ_ρ` a genuine character and `ψ = χ_σ` irreducible, the
multiplicity `⟨χ, ψ⟩` equals `dim_ℂ Hom_{ℂ[G]}(σ, ρ)`, a cast natural number.

This is the `G`-level analogue of `restrictionMultiplicity_natCast` (which proves the same
non-negativity for the *restriction* multiplicity `⟨Res^G_H χ, θ⟩`): the constituent
multiplicity of `ψ` in the genuine module `ρ` is a count, never negative.  The proof realizes
`ψ` by an irreducible `σ`, rewrites the inner sum through `χ_σ(g⁻¹) = star (χ_σ(g))`
(`character_inv`), and applies mathlib's Hom-dimension characterization of the character
scalar product. -/
theorem IsCharacter.exists_natCast_inner_irreducible {χ : ClassFunction G ℂ}
    (hχ : IsCharacter χ) {ψ : ClassFunction G ℂ} (hψ : IsIrreducibleCharacter ψ) :
    ∃ k : ℕ, ClassFunction.inner χ ψ = (k : ℂ) := by
  classical
  obtain ⟨V, _, _, _, ρ, hρ⟩ := hχ
  obtain ⟨W, _, _, _, σ, _, hσcoe⟩ := hψ
  refine ⟨Module.finrank ℂ (Representation.IntertwiningMap σ ρ), ?_⟩
  rw [ClassFunction.inner_eq_inv_card_mul_innerSum, ClassFunction.innerSum, invOf_eq_inv]
  have hsum : ∀ g : G, χ g * star (ψ g) = ρ.character g * σ.character g⁻¹ := fun g => by
    rw [congrFun hρ g, congrFun hσcoe g, ← character_inv σ g]
  rw [Finset.sum_congr rfl (fun g _ => hsum g),
    ← Representation.card_inv_mul_sum_char_mul_char_eq_finrank σ ρ]

open scoped ComplexOrder in
/-- The Fourier coefficient of a genuine character at an irreducible character is `≥ 0`.
Non-negativity half of `IsCharacter.exists_natCast_inner_irreducible`. -/
theorem IsCharacter.inner_irreducible_nonneg {χ : ClassFunction G ℂ}
    (hχ : IsCharacter χ) {ψ : ClassFunction G ℂ} (hψ : IsIrreducibleCharacter ψ) :
    0 ≤ ClassFunction.inner χ ψ := by
  obtain ⟨k, hk⟩ := hχ.exists_natCast_inner_irreducible hψ
  rw [hk]; exact Nat.cast_nonneg _

open scoped ComplexOrder in
/-- **A genuine character decomposes as a non-negative-integer combination of irreducibles.**

For `IsCharacter χ` there is a `Finsupp` `m : ClassFunction G ℂ →₀ ℕ` supported on
`Irr(G)` with
* `χ = ∑_{ψ ∈ supp m} (m ψ : ℂ) • ψ` (the decomposition), and
* `(m ψ : ℂ) = ⟨χ, ψ⟩` for every irreducible `ψ` (the coefficients are the Fourier
  multiplicities).

This is Peterfalvi's "`χ = ∑ mᵢ ψᵢ` with `mᵢ = ⟨χ, ψᵢ⟩ ∈ ℕ`" — the genuine-character
`ℕ`-decomposition consumed by the (6.6) coherence-of-`X` equality case (Round-19 residual).
The proof takes the `ℤ`-decomposition of `χ ∈ ZIrr G` (`mem_ZIrr_repr`), identifies each
integer coefficient with the Fourier coefficient `⟨χ, ψ⟩` (`inner_eq_coeff_of_repr`), which
is `≥ 0` for a genuine character (`inner_irreducible_nonneg`), and pushes the coefficients
through `Int.toNat` (no support is lost: every coefficient on the support is positive). -/
theorem IsCharacter.exists_natFinsupp_eq_sum {χ : ClassFunction G ℂ} (hχ : IsCharacter χ) :
    ∃ m : ClassFunction G ℂ →₀ ℕ, (↑m.support ⊆ irreducibleCharacters G) ∧
      χ = ∑ a ∈ m.support, (m a : ℂ) • a ∧
      ∀ ψ : ClassFunction G ℂ, IsIrreducibleCharacter ψ →
        (m ψ : ℂ) = ClassFunction.inner χ ψ := by
  classical
  obtain ⟨c, hsupp, hsum⟩ := mem_ZIrr_repr hχ.mem_ZIrr
  -- Every integer coefficient is the Fourier coefficient `⟨χ, ψ⟩`, hence `≥ 0`.
  have hcoeff : ∀ ψ : ClassFunction G ℂ, (hψ : ψ ∈ irreducibleCharacters G) →
      (c ψ : ℂ) = ClassFunction.inner χ ψ := by
    intro ψ hψ
    have := inner_eq_coeff_of_repr (⟨ψ, hψ⟩ : IrreducibleCharacter G) hsupp
    rw [show ((⟨ψ, hψ⟩ : IrreducibleCharacter G) : ClassFunction G ℂ) = ψ from rfl] at this
    rw [← this, hsum]
  have hcnn : ∀ ψ : ClassFunction G ℂ, ψ ∈ c.support → 0 ≤ c ψ := by
    intro ψ hψsupp
    have hψ : ψ ∈ irreducibleCharacters G := hsupp (Finset.mem_coe.mpr hψsupp)
    have : (0 : ℂ) ≤ (c ψ : ℂ) := by
      rw [hcoeff ψ hψ]; exact hχ.inner_irreducible_nonneg hψ
    exact_mod_cast this
  -- Push coefficients through `Int.toNat`; the support is unchanged.
  refine ⟨Finsupp.mapRange Int.toNat Int.toNat_zero c, ?_, ?_, ?_⟩
  · -- support of the `ℕ`-Finsupp is contained in that of `c`, hence in `Irr G`.
    refine subset_trans ?_ hsupp
    intro ψ hψ
    exact Finset.mem_coe.mpr (Finsupp.support_mapRange (Finset.mem_coe.mp hψ))
  · -- The decomposition: cast `Int.toNat (c a) = c a` on the support.
    have hsupp_eq : (Finsupp.mapRange Int.toNat Int.toNat_zero c).support = c.support := by
      apply Finset.Subset.antisymm Finsupp.support_mapRange
      intro a ha
      rw [Finsupp.mem_support_iff, Finsupp.mapRange_apply]
      have : 0 < c a := lt_of_le_of_ne (hcnn a ha) (Ne.symm (Finsupp.mem_support_iff.mp ha))
      omega
    rw [hsum, hsupp_eq]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [Finsupp.mapRange_apply]
    have : 0 < c a := lt_of_le_of_ne (hcnn a ha) (Ne.symm (Finsupp.mem_support_iff.mp ha))
    rw [← Int.cast_natCast (R := ℂ) (Int.toNat (c a)), Int.toNat_of_nonneg (le_of_lt this)]
  · -- The coefficient equals the Fourier multiplicity.
    intro ψ hψ
    rw [Finsupp.mapRange_apply, ← hcoeff ψ hψ]
    have hnn : 0 ≤ c ψ := by
      by_cases hsupp_mem : ψ ∈ c.support
      · exact hcnn ψ hsupp_mem
      · rw [Finsupp.notMem_support_iff.mp hsupp_mem]
    rw [← Int.cast_natCast (R := ℂ) (Int.toNat (c ψ)), Int.toNat_of_nonneg hnn]

/-- **Constituent degree bound.**  If `χ` is a genuine character and `θ` is an irreducible
constituent of `χ` (`⟨χ, θ⟩ ≠ 0`), then the degree of `θ` is at most the degree of `χ`:
`(θ 1).re ≤ (χ 1).re`.

Decompose `χ = ∑_{a ∈ Irr} m_a · a` (`exists_natFinsupp_eq_sum`) with `m_a = ⟨χ, a⟩ ∈ ℕ` and
each `a(1)` a positive integer (`irreducibleCharacter_apply_one_eq_pos_natCast`).  Evaluating at
`1`, every summand `m_a · a(1)` has non-negative real part, and the `θ`-summand alone
(multiplicity `m_θ ≥ 1`) already dominates `θ(1)`.  This is the degree half of the
Frobenius-reciprocity route to the Peterfalvi `(6.2)` `θ`-bound (`θ(1) ≤ |K:C|·φ(1)`). -/
theorem IsCharacter.apply_one_re_le_of_inner_ne_zero {χ : ClassFunction G ℂ}
    (hχ : IsCharacter χ) {θ : ClassFunction G ℂ} (hθ : IsIrreducibleCharacter θ)
    (hinner : ClassFunction.inner χ θ ≠ 0) :
    (θ 1).re ≤ (χ 1).re := by
  classical
  obtain ⟨m, hsupp, hsum, hcoeff⟩ := hχ.exists_natFinsupp_eq_sum
  -- evaluation of a finite sum of class functions at a point
  have hsum_apply : ∀ (s : Finset (ClassFunction G ℂ)) (F : ClassFunction G ℂ → ClassFunction G ℂ),
      (∑ a ∈ s, F a) 1 = ∑ a ∈ s, (F a) 1 := by
    intro s F
    induction s using Finset.cons_induction with
    | empty => simp
    | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, ClassFunction.add_apply, ih]
  -- the real-part decomposition of `χ(1)`
  have hχ1 : (χ 1).re = ∑ a ∈ m.support, (m a : ℝ) * (a 1).re := by
    have hval : χ 1 = ∑ a ∈ m.support, (m a : ℂ) * (a 1) := by
      rw [hsum, hsum_apply]
      exact Finset.sum_congr rfl fun a _ => ClassFunction.smul_apply _ _ _
    rw [hval, Complex.re_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
  -- each irreducible degree `(a 1).re` is non-negative
  have hdeg_nonneg : ∀ a ∈ m.support, (0 : ℝ) ≤ (a 1).re := by
    intro a ha
    have ha_mem : a ∈ irreducibleCharacters G := hsupp (Finset.mem_coe.mpr ha)
    obtain ⟨d, _, hd1⟩ :=
      irreducibleCharacter_apply_one_eq_pos_natCast (⟨a, ha_mem⟩ : IrreducibleCharacter G)
    have hd1' : a (1 : G) = (d : ℂ) := hd1
    rw [hd1', Complex.natCast_re]
    exact Nat.cast_nonneg d
  -- hence each summand is non-negative
  have hterm_nonneg : ∀ a ∈ m.support, (0 : ℝ) ≤ (m a : ℝ) * (a 1).re := fun a ha =>
    mul_nonneg (Nat.cast_nonneg _) (hdeg_nonneg a ha)
  -- `θ` lies in the support (its multiplicity is the nonzero Fourier coefficient)
  have hmθ : m θ ≠ 0 := fun h0 => hinner (by rw [← hcoeff θ hθ, h0, Nat.cast_zero])
  have hθsupp : θ ∈ m.support := Finsupp.mem_support_iff.mpr hmθ
  -- the `θ`-summand dominates `θ(1)`, and the whole sum dominates the `θ`-summand
  have hθterm : (θ 1).re ≤ (m θ : ℝ) * (θ 1).re :=
    le_mul_of_one_le_left (hdeg_nonneg θ hθsupp)
      (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hmθ)
  rw [hχ1]
  exact hθterm.trans (Finset.single_le_sum hterm_nonneg hθsupp)

omit [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)] in
/-- The zero class function is a genuine character (the character of the `0`-dimensional
representation on `PUnit`). -/
theorem IsCharacter.zero : IsCharacter (0 : ClassFunction G ℂ) := by
  refine ⟨PUnit, inferInstance, inferInstance, inferInstance, 1, ?_⟩
  funext g
  change (0 : ℂ) = LinearMap.trace ℂ PUnit ((1 : Representation ℂ G PUnit) g)
  rw [Subsingleton.elim ((1 : Representation ℂ G PUnit) g) 0, map_zero]

omit [Finite G] in
omit [Fintype G] [Invertible (Nat.card G : ℂ)] in
/-- Genuine characters are closed under addition: the direct sum (`Representation.prod`) of the
witnessing representations has character `χ + ψ`. -/
theorem IsCharacter.add {χ ψ : ClassFunction G ℂ} (hχ : IsCharacter χ) (hψ : IsCharacter ψ) :
    IsCharacter (χ + ψ) := by
  obtain ⟨V, _, _, _, ρ, hρ⟩ := hχ
  obtain ⟨W, _, _, _, σ, hσ⟩ := hψ
  refine ⟨V × W, inferInstance, inferInstance, inferInstance, ρ.prod σ, ?_⟩
  funext g
  have hprod : (ρ.prod σ).character g = ρ.character g + σ.character g := by
    change LinearMap.trace ℂ (V × W) ((ρ g).prodMap (σ g))
        = LinearMap.trace ℂ V (ρ g) + LinearMap.trace ℂ W (σ g)
    exact LinearMap.trace_prodMap' (ρ g) (σ g)
  rw [hprod, ClassFunction.add_apply, congrFun hρ g, congrFun hσ g]

omit [Finite G] in
omit [Fintype G] [Invertible (Nat.card G : ℂ)] in
/-- Genuine characters are closed under `ℕ`-scalar multiples. -/
theorem IsCharacter.nsmul {χ : ClassFunction G ℂ} (hχ : IsCharacter χ) (n : ℕ) :
    IsCharacter (n • χ) := by
  induction n with
  | zero => simpa using IsCharacter.zero
  | succ k ih => rw [succ_nsmul]; exact ih.add hχ

omit [Finite G] in
omit [Fintype G] [Invertible (Nat.card G : ℂ)] in
/-- Genuine characters are closed under finite sums. -/
theorem IsCharacter.sum {ι : Type*} {s : Finset ι} {f : ι → ClassFunction G ℂ}
    (h : ∀ i ∈ s, IsCharacter (f i)) : IsCharacter (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simpa using IsCharacter.zero
  | cons a s ha ih =>
      rw [Finset.sum_cons]
      exact (h a (Finset.mem_cons_self a s)).add (ih fun i hi => h i (Finset.mem_cons_of_mem hi))

omit [Finite G] in
omit [Fintype G] [Invertible (Nat.card G : ℂ)] in
set_option linter.unusedFintypeInType false in
/-- **Reverse decomposition.**  A non-negative-integer combination of irreducible characters is a
genuine character.  This is the converse of `exists_natFinsupp_eq_sum` and the engine behind
`IsCharacter (Ind θ)`. -/
theorem isCharacter_of_natFinsupp_eq_sum {χ : ClassFunction G ℂ}
    (m : ClassFunction G ℂ →₀ ℕ) (hsupp : (↑m.support : Set (ClassFunction G ℂ)) ⊆
      irreducibleCharacters G) (hsum : χ = ∑ a ∈ m.support, (m a : ℂ) • a) :
    IsCharacter χ := by
  rw [hsum]
  refine IsCharacter.sum fun a ha => ?_
  have ha_irr : IsIrreducibleCharacter a :=
    mem_irreducibleCharacters.mp (hsupp (Finset.mem_coe.mpr ha))
  rw [Nat.cast_smul_eq_nsmul]
  exact ha_irr.isCharacter.nsmul (m a)

end GenuineDecomposition

end OddOrder.RepresentationTheory


