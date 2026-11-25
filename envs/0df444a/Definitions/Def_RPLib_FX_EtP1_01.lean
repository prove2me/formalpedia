-- Prove2me | Definitions.Def_RPLib_FX_EtP1_01
-- name    : RPLib_FX_EtP1_01
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T00:59:43.463934+00:00
-- url     : https://prove2.me/theorems/0b34f06d-c5cb-4b14-b047-6980d9f79b9d
-- title:
--   Étale cohomology of the projective line, library file 01 of 34
-- statement:
--   File 01 of 34 of the étale cohomology library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_CurveCoh_Pair`: S4-CurveCoh, part 1: cohomology of a pair `(Γ, {I_s})` in the `π₁` model (generic algebra)
--   * `S4.Def_RP_GalCover`: S4-GalCover draft v1: Galois etale covers and Frobenius (S4_DESIGN section 1)
--   * `S4.Def_RP_EtCompact_P1`: S4-EtCompact, part 11: the projective line `P^1_K = Proj K[X₀, X₁]` (O6, explicit compactifications)
--   * `S4.Def_RP_EtSheaves_Stalk`: S4-EtSheaves, part 1: etale sheaves of `Λ`-modules, geometric points and stalks
--   * `S4.Def_RP_EtSheaves_Pull`: S4-EtSheaves, part 2: base change of the small etale site and pullback of etale sheaves
--   * `S4.Def_RP_EtSheaves_Const`: S4-EtSheaves, part 3: constant, locally constant and lisse etale sheaves
--   * `S4.Def_RP_EtSheaves_PullComp`: S4-EtSheaves, part 4: pullback along a composite; pullback preserves (locally) constant sheaves
--   * `S4.Def_RP_EtSheaves_Tensor`: S4-EtSheaves, part 5: tensor products of etale sheaves
--   * `S4.Def_RP_EtSheaves_Res`: S4-EtSheaves, part 6: restriction along an etale map
--   * `S4.Def_RP_EtSheaves_Lsh`: S4-EtSheaves, part 12: extension by zero `j_!`
--   * `S4.Def_RP_EtSheaves_Hom`: S4-EtSheaves, part 7: the internal Hom of etale sheaves
--   * `S4.Def_RP_EtSheaves_HomLoc`: S4-EtSheaves, part 10: the internal Hom is local
--   * `S4.Def_RP_EtSheaves_LshFF`: S4-EtSheaves, part 13: `j_!` is fully faithful for a monomorphism `j`
--   * `S4.Def_RP_EtSheaves_CutSet`: S4-EtSheaves, part 21: `F_S` for a subset `S`
--   * `S4.Def_RP_EtCompact_CutMap`: S4-EtCompact, part 4: maps between cut sheaves
--   * `S4.Def_RP_EtSheaves_Closed`: S4-EtSheaves, part 14: `i_*` vanishes off `Z`
--   * `S4.Def_RP_EtCompact_Exact`: S4-EtCompact, part 2: exactness of `f^*`, `i_*` (closed) and `j_!` (open)
--   * `S4.Def_RP_EtCompact_Coh`: S4-EtCompact, part 3: etale cohomology as `Ext` from the constant sheaf
--   * `S4.Def_RP_EtCompact_Pres`: S4-EtCompact, part 8: presentations and the set-indexed `H^*_c`
--   * `S4.Def_RP_EtCompact_CutFun`: S4-EtCompact, part 6: `F ↦ F_{W ∩ Vᶜ}` is exact; long exact sequence in the sheaf variable
--   * `S4.Def_RP_EtCompact_A1`: S4-EtCompact, part 12: the affine line inside `P^1` (O6, explicit compactifications)
--   * `S4.Def_RP_EtCompact_P1Pts`: S4-EtCompact, part 27: points of `P^1_K` (O8a, file 1)
--   * `S4.Def_RP_EtSheaves_GalAct`: S4-EtSheaves, part 23: the Galois action on stalks
--   * `S4.Def_RP_EtCompact_A1Hc`: S4-EtCompact, part 29: `H^*_c(A^1, Λ)` inside `P^1` (O8a, file 3)
--   * `S4.Def_RP_EtSheaves_TorSec`: S4-EtSheaves, part O10d-2(i): sections over `T ×_X Y` for a Galois cover
--   * `S4.Def_RP_EtSheaves_GenBr`: S4-EtSheaves, part O10b: the generic Galois group maps onto `π₁(Spec A)`
--   * `S4.Def_RP_EtSheaves_GalFV`: S4-EtSheaves, part O10d-2(iv-c): the Galois representation on `(F_V)_x̄` is `ρ ∘ galFV`
--   * `S4.Def_RP_EtCompact_RepExt`: S4-EtCompact, O9b part 2: extensions of `Λ` by a representation and 1-cocycles (pure algebra)
--
--   **Formalization note.** One file of a library formalizing the étale cohomology of the projective line $\mathbf P^1_k = \operatorname{Proj} k[X_0, X_1]$ over an algebraically closed field $k$ with coefficients in sheaves of $\Lambda$-modules on the small étale site ($H^n = \operatorname{Ext}^n(\Lambda, -)$): $H^1(\mathbf P^1, \Lambda) = 0$, $H^2(\mathbf P^1, \Lambda) \cong \Lambda$ and $H^{n+3}(\mathbf P^1, F) = 0$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §1 (cohomology of curves) and Chapter III, §2 (Kummer theory); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Arcata », Chapter IV (cohomology of curves, Tsen's theorem)

import Mathlib

/-!
# Étale cohomology of the projective line, library file 01 of 34

Declarations of the formalization of the étale cohomology of the projective line over an algebraically
closed field (H¹ = 0, H² ≅ Λ, vanishing in degrees ≥ 3), re-hosted declaration by declaration from the
library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_CurveCoh_Pair`: S4-CurveCoh, part 1: cohomology of a pair `(Γ, {I_s})` in the `π₁` model (generic algebra)
* `S4.Def_RP_GalCover`: S4-GalCover draft v1: Galois etale covers and Frobenius (S4_DESIGN section 1)
* `S4.Def_RP_EtCompact_P1`: S4-EtCompact, part 11: the projective line `P^1_K = Proj K[X₀, X₁]` (O6, explicit compactifications)
* `S4.Def_RP_EtSheaves_Stalk`: S4-EtSheaves, part 1: etale sheaves of `Λ`-modules, geometric points and stalks
* `S4.Def_RP_EtSheaves_Pull`: S4-EtSheaves, part 2: base change of the small etale site and pullback of etale sheaves
* `S4.Def_RP_EtSheaves_Const`: S4-EtSheaves, part 3: constant, locally constant and lisse etale sheaves
* `S4.Def_RP_EtSheaves_PullComp`: S4-EtSheaves, part 4: pullback along a composite; pullback preserves (locally) constant sheaves
* `S4.Def_RP_EtSheaves_Tensor`: S4-EtSheaves, part 5: tensor products of etale sheaves
* `S4.Def_RP_EtSheaves_Res`: S4-EtSheaves, part 6: restriction along an etale map
* `S4.Def_RP_EtSheaves_Lsh`: S4-EtSheaves, part 12: extension by zero `j_!`
* `S4.Def_RP_EtSheaves_Hom`: S4-EtSheaves, part 7: the internal Hom of etale sheaves
* `S4.Def_RP_EtSheaves_HomLoc`: S4-EtSheaves, part 10: the internal Hom is local
* `S4.Def_RP_EtSheaves_LshFF`: S4-EtSheaves, part 13: `j_!` is fully faithful for a monomorphism `j`
* `S4.Def_RP_EtSheaves_CutSet`: S4-EtSheaves, part 21: `F_S` for a subset `S`
* `S4.Def_RP_EtCompact_CutMap`: S4-EtCompact, part 4: maps between cut sheaves
* `S4.Def_RP_EtSheaves_Closed`: S4-EtSheaves, part 14: `i_*` vanishes off `Z`
* `S4.Def_RP_EtCompact_Exact`: S4-EtCompact, part 2: exactness of `f^*`, `i_*` (closed) and `j_!` (open)
* `S4.Def_RP_EtCompact_Coh`: S4-EtCompact, part 3: etale cohomology as `Ext` from the constant sheaf
* `S4.Def_RP_EtCompact_Pres`: S4-EtCompact, part 8: presentations and the set-indexed `H^*_c`
* `S4.Def_RP_EtCompact_CutFun`: S4-EtCompact, part 6: `F ↦ F_{W ∩ Vᶜ}` is exact; long exact sequence in the sheaf variable
* `S4.Def_RP_EtCompact_A1`: S4-EtCompact, part 12: the affine line inside `P^1` (O6, explicit compactifications)
* `S4.Def_RP_EtCompact_P1Pts`: S4-EtCompact, part 27: points of `P^1_K` (O8a, file 1)
* `S4.Def_RP_EtSheaves_GalAct`: S4-EtSheaves, part 23: the Galois action on stalks
* `S4.Def_RP_EtCompact_A1Hc`: S4-EtCompact, part 29: `H^*_c(A^1, Λ)` inside `P^1` (O8a, file 3)
* `S4.Def_RP_EtSheaves_TorSec`: S4-EtSheaves, part O10d-2(i): sections over `T ×_X Y` for a Galois cover
* `S4.Def_RP_EtSheaves_GenBr`: S4-EtSheaves, part O10b: the generic Galois group maps onto `π₁(Spec A)`
* `S4.Def_RP_EtSheaves_GalFV`: S4-EtSheaves, part O10d-2(iv-c): the Galois representation on `(F_V)_x̄` is `ρ ∘ galFV`
* `S4.Def_RP_EtCompact_RepExt`: S4-EtCompact, O9b part 2: extensions of `Λ` by a representation and 1-cocycles (pure algebra)
-/

set_option autoImplicit false

-- ===== S4.Def_RP_CurveCoh_Pair =====
section

/-!
# S4-CurveCoh, part 1: cohomology of a pair `(Γ, {I_s})` in the `π₁` model (generic algebra)

Setting (S4_DESIGN section 3, reviews R2/R5/R19):
* a topological group `G` (later `π₁(U)`), a normal subgroup `Γ` (later `π₁(U ⊗ F̄)`, the geometric fundamental
  group), a representation `ρ` of `G` on `M` over ANY commutative ring `k` (review END-2, decision R19), and a family
  `I : S → Subgroup G` (later the inertia groups at the geometric boundary points `s ∈ X̄ \ Ū`, review R5).

Definitions:
* `H0 = M^Γ`;
* `H1` = LOCALLY CONSTANT (continuous, `M` discrete) 1-cocycles on `Γ` modulo coboundaries; part 2 shows it is the
  colimit of the finite-level `H¹` over open normal subgroups (covers);
* `H1c` = `H¹` of the mapping cone of `C^*(Γ, M) → ⊕_s C^*(I_s ∩ Γ, M)`: pairs `(c, b)` of a cocycle `c` and boundary
  trivialisations `b_s` with `c g = g • b_s - b_s` on `I_s ∩ Γ`, modulo `(d m, (m)_s)`;
* `H2c` = the coinvariants `M_Γ` (definition kept by review R2; the Tate twist `(-1)` enters the Frobenius as a scalar);
* the exact sequence `0 → H⁰ → ⊕_s M^{I_s} → H¹_c → H¹_par → 0`, `H¹_par = ker (H¹ → ⊕_s H¹(I_s ∩ Γ))`;
* the operators `T_ψ` (`ψ ∈ G`): `(T_ψ c)(g) = ρ(ψ) c(ψ⁻¹ g ψ)`. The GEOMETRIC Frobenius is `F = T_{φ⁻¹}` for an
  arithmetic Frobenius lift `φ`; on `H2c` it is `q • ρ(φ⁻¹)` (geometric Frobenius acts on `ℤ/lⁿ(-1)` by `q`).
  All operators commute with the maps of the exact sequence.
-/

set_option autoImplicit false

namespace RamanujanPetersson
namespace CurveCoh

noncomputable section

variable {k : Type} [CommRing k] {G : Type} [Group G] [TopologicalSpace G]
  {M : Type} [AddCommGroup M] [Module k M] (ρ : Representation k G M) (Γ : Subgroup G)

/-! ## Degree 0 and degree 1 -/

/-- Locally constant (= continuous for discrete `M`) inhomogeneous 1-cocycles `Γ → M`. -/
def Z1 : Submodule k (Γ → M) where
  carrier := {c | IsLocallyConstant c ∧ ∀ g h : Γ, c (g * h) = c g + ρ g (c h)}
  add_mem' := by
    rintro c d ⟨hc, hc'⟩ ⟨hd, hd'⟩
    refine ⟨hc.add hd, fun g h => ?_⟩
    simp only [Pi.add_apply, hc', hd', map_add]
    abel
  zero_mem' := ⟨IsLocallyConstant.zero, fun g h => by simp⟩
  smul_mem' := by
    rintro a c ⟨hc, hc'⟩
    refine ⟨hc.comp (a • ·), fun g h => ?_⟩
    simp only [Pi.smul_apply, hc', smul_add, map_smul]

theorem mem_Z1 (c : Γ → M) :
    c ∈ Z1 ρ Γ ↔ IsLocallyConstant c ∧ ∀ g h : Γ, c (g * h) = c g + ρ g (c h) := Iff.rfl

/-- 1-coboundaries `g ↦ g • m - m` that are locally constant. -/
def B1 : Submodule k (Γ → M) where
  carrier := {c | c ∈ Z1 ρ Γ ∧ ∃ m : M, ∀ g : Γ, c g = ρ g m - m}
  add_mem' := by
    rintro c d ⟨hc, m, hm⟩ ⟨hd, n, hn⟩
    refine ⟨(Z1 ρ Γ).add_mem hc hd, m + n, fun g => ?_⟩
    simp only [Pi.add_apply, hm, hn, map_add]
    abel
  zero_mem' := ⟨(Z1 ρ Γ).zero_mem, 0, fun g => by simp⟩
  smul_mem' := by
    rintro a c ⟨hc, m, hm⟩
    exact ⟨(Z1 ρ Γ).smul_mem a hc, a • m, fun g => by simp [hm, smul_sub]⟩

theorem mem_B1 (c : Γ → M) : c ∈ B1 ρ Γ ↔ c ∈ Z1 ρ Γ ∧ ∃ m : M, ∀ g : Γ, c g = ρ g m - m := Iff.rfl

/-- `H¹(Γ, M)` with continuous (locally constant) cochains. -/
abbrev H1 : Type := ↥(Z1 ρ Γ) ⧸ (B1 ρ Γ).comap (Z1 ρ Γ).subtype

/-- The class of a cocycle. -/
noncomputable def H1.mk : Z1 ρ Γ →ₗ[k] H1 ρ Γ := Submodule.mkQ _

/-! ## The cone: compactly supported `H¹` -/

variable {S : Type} (I : S → Subgroup G)

/-! ## The maps of the exact sequence `0 → H⁰ → ⊕_s M^{I_s} → H¹_c → H¹_par → 0` -/

/-! ## Frobenius operators -/

section Frob

variable [IsTopologicalGroup G] [hΓ : Γ.Normal]

variable {S : Type} (I : S → Subgroup G)

/-! ### Frobenius commutes with the exact sequence -/

end Frob

/-! ## Sanity: constant coefficients -/

section Constant

variable (I : S → Subgroup G)

end Constant

end

end CurveCoh
end RamanujanPetersson


end

-- ===== S4.Def_RP_GalCover =====
section

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

attribute [local instance] GalCover.ring GalCover.dom GalCover.alg GalCover.inj GalCover.fin GalCover.grp GalCover.fG GalCover.act GalCover.gal

namespace GalCover

variable {A : Type} [CommRing A] [IsDomain A] (C : GalCover A)

theorem inertia_eq_bot (Q : Ideal C.B) [hQ : Q.IsPrime] : Q.inertia C.G = ⊥ := C.unramified Q hQ

/-! ## Constants, the geometric subgroup, Frobenius on constants -/

section Constants

variable (Fq : Type) [Field Fq] [Algebra Fq A] [Algebra Fq C.B] [IsScalarTower Fq A C.B]

end Constants

/-! ## Morphisms of covers -/

/-! ## Etale Galois extensions have trivial inertia (bridge `ofEtale`) -/

section Etale

variable {B G : Type} [CommRing B] [IsDomain B] [Algebra A B] [Group G] [Finite G]
  [MulSemiringAction G B] [IsGaloisGroup G A B]

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

end Bridge

end Pi1

/-! ## Charts over other base rings: the infinity chart and boundary places (review R5) -/

namespace GalCover

section Charts

variable {A : Type} [CommRing A] [IsDomain A] (C : GalCover A)
variable (K L : Type) [Field K] [Field L] [Algebra A K] [IsFractionRing A K] [Algebra C.B L]
  [IsFractionRing C.B L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A C.B L]
  [MulSemiringAction C.G L] [SMulDistribClass C.G C.B L]

variable (R0 : Type) [CommRing R0] [IsDomain R0] [IsIntegrallyClosed R0] [Algebra R0 K]
  [IsFractionRing R0 K] [Algebra R0 L] [IsScalarTower R0 K L]

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

variable [Algebra Fq[X] L] [IsScalarTower Fq[X] (RatFunc Fq) L]

end CurveCharts

end GalCover

end RamanujanPetersson


end

-- ===== S4.Def_RP_EtCompact_P1 =====
section

/-!
# S4-EtCompact, part 11: the projective line `P^1_K = Proj K[X₀, X₁]` (O6, explicit compactifications)

`P1 K := Proj (homogeneousSubmodule (Fin 2) K)` with the standard grading of `MvPolynomial (Fin 2) K`.
The degree-0 part is `K` (`bij0`), the structure map `P1 K ⟶ Spec K` is proper (`P1.toSpecK`), and the
standard chart `D₊(X₀) = Spec (K[X₀, X₁]_(X₀)) ⟶ P1 K` is an open immersion (`P1.chart0`).
-/

set_option autoImplicit false

open AlgebraicGeometry MvPolynomial CategoryTheory

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace RamanujanPetersson.EtCompact

universe u

variable (K : Type u) [Field K]

/-- The projective line `Proj K[X₀, X₁]`. -/
abbrev P1 : Scheme.{u} := Proj (homogeneousSubmodule (Fin 2) K)

instance P1.scalarTower0 :
    IsScalarTower K (homogeneousSubmodule (Fin 2) K 0) (MvPolynomial (Fin 2) K) :=
  IsScalarTower.of_algebraMap_eq (R := K) (S := ↥(homogeneousSubmodule (Fin 2) K 0))
    (A := MvPolynomial (Fin 2) K) (fun _ => rfl)

instance P1.finiteType0 :
    Algebra.FiniteType (homogeneousSubmodule (Fin 2) K 0) (MvPolynomial (Fin 2) K) :=
  Algebra.FiniteType.of_restrictScalars_finiteType K _ _

instance P1.isProper_toSpecZero : IsProper (Proj.toSpecZero (homogeneousSubmodule (Fin 2) K)) :=
  inferInstance

theorem P1.X_mem (i : Fin 2) : (X i : MvPolynomial (Fin 2) K) ∈ homogeneousSubmodule (Fin 2) K 1 :=
  isHomogeneous_X K i

/-- The standard affine chart `D₊(X₀) ⟶ P^1_K`, an open immersion. -/
def P1.chart0 :
    Spec (CommRingCat.of (HomogeneousLocalization.Away (homogeneousSubmodule (Fin 2) K)
      (X 0 : MvPolynomial (Fin 2) K))) ⟶ P1 K :=
  Proj.awayι (homogeneousSubmodule (Fin 2) K) (X 0) (P1.X_mem K 0) one_pos

instance P1.isOpenImmersion_chart0 : IsOpenImmersion (P1.chart0 K) := by
  unfold P1.chart0
  infer_instance

end RamanujanPetersson.EtCompact

end

end

-- ===== S4.Def_RP_EtSheaves_Stalk =====
section

/-!
# S4-EtSheaves, part 1: etale sheaves of `Λ`-modules, geometric points and stalks

`EtSh Λ X` is the category of sheaves of `Λ`-modules on Mathlib's small etale site of `X`
(abelian, Grothendieck, with sheafification: `Mathlib/AlgebraicGeometry/Sites/AffineEtale.lean`).
A geometric point is a morphism `Spec Ω ⟶ X` with `Ω` separably closed; it is a point of the site
(`Scheme.pointSmallEtale`), and the stalk functor is its fibre functor. Stalks are exact and the
geometric points `geomPtAt x` (one over each `x : X`, `Ω` a separable closure of `κ(x)`) form a
conservative family, so isomorphisms, zero objects and exactness are detected on stalks.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtSheaves

universe u

/-- Sheaves of `Λ`-modules on the small etale site of `X`. -/
abbrev EtSh (Λ : Type u) [CommRing Λ] (X : Scheme.{u}) :=
  Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)

/-- A geometric point of `X`: a separably closed field `Ω` and a morphism `Spec Ω ⟶ X`. -/
structure GeomPt (X : Scheme.{u}) where
  Ω : Type u
  [fld : Field Ω]
  [sep : IsSepClosed Ω]
  pt : Spec (CommRingCat.of Ω) ⟶ X

attribute [instance] GeomPt.fld GeomPt.sep

namespace GeomPt

variable {X : Scheme.{u}} (s : GeomPt X)

/-- The point of `X` under the geometric point. -/
def center : X := s.pt default

/-- The point of the small etale site defined by `s`. -/
def point : (Scheme.smallEtaleTopology X).Point := Scheme.pointSmallEtale s.pt

variable (Λ : Type u) [CommRing Λ]

/-- The stalk functor `F ↦ F_s`. -/
def stalkF : EtSh Λ X ⥤ ModuleCat.{u} Λ := s.point.sheafFiber

instance : PreservesFiniteLimits (s.stalkF Λ) := by
  dsimp [stalkF]; infer_instance

instance : (s.stalkF Λ).IsLeftAdjoint := by
  dsimp [stalkF]; infer_instance

instance : PreservesColimits (s.stalkF Λ) := by
  dsimp [stalkF]; infer_instance

instance : PreservesFiniteColimits (s.stalkF Λ) := by
  dsimp [stalkF]; infer_instance

instance : (s.stalkF Λ).PreservesZeroMorphisms := by
  dsimp [stalkF]; infer_instance

end GeomPt

/-- The geometric point over `x` given by a separable closure of the residue field `κ(x)`. -/
def geomPtAt {X : Scheme.{u}} (x : X) : GeomPt X where
  Ω := SeparableClosure (X.residueField x)
  pt := (Scheme.SpecToEquivOfField (SeparableClosure (X.residueField x)) X).2
      ⟨x, CommRingCat.ofHom (algebraMap (X.residueField x) _)⟩

theorem center_geomPtAt {X : Scheme.{u}} (x : X) : (geomPtAt x).center = x := by
  simp only [GeomPt.center, geomPtAt, Scheme.SpecToEquivOfField]
  exact Scheme.fromSpecResidueField_apply x _

variable (Λ : Type u) [CommRing Λ] {X : Scheme.{u}}

/-- The stalk `F_x̄` at the geometric point `geomPtAt x`. -/
abbrev stalk (F : EtSh Λ X) (x : X) : ModuleCat.{u} Λ := ((geomPtAt x).stalkF Λ).obj F

/-- The points `geomPtAt x` form a conservative family. -/
theorem conservative (X : Scheme.{u}) :
    (ObjectProperty.ofObj (fun x : X => (geomPtAt x).point)).IsConservativeFamilyOfPoints :=
  Scheme.isConservativeFamilyOfPoints_pointSmallEtale' X

/-- A morphism of etale sheaves is an isomorphism iff it is so on all stalks. -/
theorem isIso_iff_stalk {F G : EtSh Λ X} (φ : F ⟶ G) :
    IsIso φ ↔ ∀ x : X, IsIso (((geomPtAt x).stalkF Λ).map φ) := by
  constructor
  · intro _ x; infer_instance
  · intro h
    have : ∀ i : (ObjectProperty.ofObj (fun x : X => (geomPtAt x).point)).FullSubcategory,
        IsIso ((i.obj.sheafFiber (A := ModuleCat.{u} Λ)).map φ) := by
      rintro ⟨Φ, hΦ⟩
      cases hΦ with
      | mk x => exact h x
    exact ((conservative X).jointlyReflectIsomorphisms (ModuleCat.{u} Λ)).isIso φ

/-- Morphisms of etale sheaves are determined by their stalks. -/
theorem hom_ext_stalk {F G : EtSh Λ X} {φ ψ : F ⟶ G}
    (h : ∀ x : X, ((geomPtAt x).stalkF Λ).map φ = ((geomPtAt x).stalkF Λ).map ψ) : φ = ψ := by
  refine ((conservative X).jointlyFaithful (ModuleCat.{u} Λ)).map_injective ?_
  rintro ⟨Φ, hΦ⟩
  cases hΦ with
  | mk x => exact h x

/-- A sheaf is zero iff all its stalks are zero. -/
theorem isZero_iff_stalk (F : EtSh Λ X) :
    IsZero F ↔ ∀ x : X, IsZero (stalk Λ F x) := by
  constructor
  · intro hF x; exact Functor.map_isZero _ hF
  · intro h
    rw [IsZero.iff_id_eq_zero]
    refine hom_ext_stalk Λ (fun x => ?_)
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero]
    exact (h x).eq_of_src _ _

/-- A short complex of etale sheaves is exact iff it is exact on all stalks. -/
theorem exact_iff_stalk (S : ShortComplex (EtSh Λ X)) :
    S.Exact ↔ ∀ x : X, (S.map ((geomPtAt x).stalkF Λ)).Exact := by
  constructor
  · intro hS x; exact hS.map _
  · intro h
    rw [S.exact_iff_isZero_homology, isZero_iff_stalk]
    intro x
    exact ((ShortComplex.exact_iff_isZero_homology _).1 (h x)).of_iso (S.mapHomologyIso _).symm

/-- Monomorphisms are detected on stalks. -/
theorem mono_iff_stalk {F G : EtSh Λ X} (φ : F ⟶ G) :
    Mono φ ↔ ∀ x : X, Mono (((geomPtAt x).stalkF Λ).map φ) := by
  constructor
  · intro _ x; infer_instance
  · intro h
    have : ∀ i : (ObjectProperty.ofObj (fun x : X => (geomPtAt x).point)).FullSubcategory,
        Mono ((i.obj.sheafFiber (A := ModuleCat.{u} Λ)).map φ) := by
      rintro ⟨Φ, hΦ⟩
      cases hΦ with
      | mk x => exact h x
    exact ((conservative X).jointlyReflectMonomorphisms (ModuleCat.{u} Λ)).mono φ

/-- Epimorphisms are detected on stalks. -/
theorem epi_iff_stalk {F G : EtSh Λ X} (φ : F ⟶ G) :
    Epi φ ↔ ∀ x : X, Epi (((geomPtAt x).stalkF Λ).map φ) := by
  constructor
  · intro _ x; infer_instance
  · intro h
    have : ∀ i : (ObjectProperty.ofObj (fun x : X => (geomPtAt x).point)).FullSubcategory,
        Epi ((i.obj.sheafFiber (A := ModuleCat.{u} Λ)).map φ) := by
      rintro ⟨Φ, hΦ⟩
      cases hΦ with
      | mk x => exact h x
    exact ((conservative X).jointlyReflectEpimorphisms (ModuleCat.{u} Λ)).epi φ

end RamanujanPetersson.EtSheaves

end

end

-- ===== S4.Def_RP_EtSheaves_Pull =====
section

/-!
# S4-EtSheaves, part 2: base change of the small etale site and pullback of etale sheaves

For `f : X ⟶ Y`, `etPull f : Y.Etale ⥤ X.Etale` sends `V → Y` to `V ×_Y X → X`. It preserves finite
limits (hence is representably flat) and preserves covers, so it is continuous for the small etale
topologies. The pushforward `push f` has a left adjoint `pull f` (`f^*`): Kan extension along the
essentially small affine etale site of `Y`. The stalk of `f^*F` at a geometric point `s` of `X` is
the stalk of `F` at `s ≫ f`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtSheaves

universe u

/-- Pointwise description of the covering sieves of the small etale site. -/
theorem mem_smallEtale_iff {Z : Scheme.{u}} (V : Z.Etale) (R : Sieve V) :
    R ∈ Z.smallEtaleTopology V ↔
      ∀ x : V.left, ∃ (W : Z.Etale) (g : W ⟶ V) (w : W.left), R g ∧ g.left w = x := by
  have e := Scheme.smallGrothendieckTopology_eq_toGrothendieck_smallPretopology
    (P := @Etale) (Q := @Etale) Z le_rfl
  change R ∈ Z.smallGrothendieckTopology (P := @Etale) V ↔ _
  rw [e]
  refine (Scheme.mem_toGrothendieck_smallPretopology (P := @Etale) (Q := @Etale) V R).trans ?_
  constructor
  · intro h x
    obtain ⟨W, g, w, hg, -, hw⟩ := h x
    exact ⟨W, g, w, hg, hw⟩
  · intro h x
    obtain ⟨W, g, w, hg, hw⟩ := h x
    exact ⟨W, g, w, hg, inferInstance, hw⟩

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Base change of etale `Y`-schemes along `f : X ⟶ Y`. -/
def etPull : Y.Etale ⥤ X.Etale := MorphismProperty.Over.pullback (P := @Etale) (Q := ⊤) f

@[simp] theorem etPull_obj_left (V : Y.Etale) : ((etPull f).obj V).left = pullback V.hom f := rfl

@[simp] theorem etPull_obj_hom (V : Y.Etale) :
    ((etPull f).obj V).hom = pullback.snd V.hom f := rfl

@[simp] theorem etPull_map_left {V W : Y.Etale} (g : V ⟶ W) :
    ((etPull f).map g).left = pullback.lift (pullback.fst V.hom f ≫ g.left)
      (pullback.snd V.hom f) (by simp [pullback.condition]) := rfl

/-- `etPull f` lies over base change of `Y`-schemes. -/
def etPullForgetIso :
    etPull f ⋙ Scheme.Etale.forget X ≅ Scheme.Etale.forget Y ⋙ CategoryTheory.Over.pullback f :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro V W g
    exact (Category.comp_id _).trans (Category.id_comp _).symm)

instance : PreservesFiniteLimits (etPull f) := by
  have : PreservesFiniteLimits (etPull f ⋙ Scheme.Etale.forget X) :=
    preservesFiniteLimits_of_natIso (etPullForgetIso f).symm
  exact preservesFiniteLimits_of_reflects_of_preserves (etPull f) (Scheme.Etale.forget X)

instance : RepresentablyFlat (etPull f) := flat_of_preservesFiniteLimits _

set_option backward.isDefEq.respectTransparency false in
/-- A point of `V ×_Y X` lying over a point of `V` hit by `g : W ⟶ V` comes from `W ×_Y X`. -/
theorem etPull_exists_preimage {V W : Y.Etale} (g : W ⟶ V) (w : W.left)
    (z : ((etPull f).obj V).left) (h : g.left w = pullback.fst V.hom f z) :
    ∃ t : ((etPull f).obj W).left, ((etPull f).map g).left t = z := by
  obtain ⟨t, -, ht2⟩ := Scheme.Pullback.exists_preimage_pullback w z h
  have hgw : g.left ≫ V.hom = W.hom := MorphismProperty.Over.w g
  obtain ⟨p, hp1, hp2⟩ : ∃ p : pullback g.left (pullback.fst V.hom f) ⟶ pullback W.hom f,
      p ≫ pullback.fst W.hom f = pullback.fst _ _ ∧
        p ≫ pullback.snd W.hom f = pullback.snd _ _ ≫ pullback.snd V.hom f :=
    ⟨pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ pullback.snd V.hom f) (by
      rw [← hgw, ← Category.assoc, pullback.condition, Category.assoc, pullback.condition,
        Category.assoc]), pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hp : p ≫ ((etPull f).map g).left = pullback.snd _ _ := by
    rw [etPull_map_left]
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, hp1, pullback.condition]
    · rw [Category.assoc, pullback.lift_snd, hp2]
  refine ⟨p t, (Scheme.Hom.comp_apply p _ t).symm.trans ?_⟩
  exact (congrArg (fun φ : pullback g.left (pullback.fst V.hom f) ⟶ pullback V.hom f => φ t) hp).trans
    ht2

theorem etPull_coverPreserving :
    CoverPreserving Y.smallEtaleTopology X.smallEtaleTopology (etPull f) where
  cover_preserve {V} {R} hR := by
    rw [mem_smallEtale_iff] at hR ⊢
    intro z
    obtain ⟨W, g, w, hg, hw⟩ := hR (pullback.fst V.hom f z)
    obtain ⟨t, ht⟩ := etPull_exists_preimage f g w z hw
    exact ⟨_, (etPull f).map g, t, R.image_mem_functorPushforward (etPull f) hg, ht⟩

instance : (etPull f).IsContinuous Y.smallEtaleTopology X.smallEtaleTopology := by
  rw [Functor.isContinuous_iff_coverPreserving]
  exact etPull_coverPreserving f

section Sheaves

variable (Λ : Type u) [CommRing Λ]

/-- `etPull f` restricted to affine etale `Y`-schemes. -/
def affPull : Y.AffineEtale ⥤ X.Etale := Scheme.AffineEtale.Spec Y ⋙ etPull f

instance : (affPull f).IsContinuous (Scheme.AffineEtale.topology Y) X.smallEtaleTopology :=
  Functor.isContinuous_comp _ _ _ Y.smallEtaleTopology _

instance (V : (X.Etale)ᵒᵖ) :
    HasColimitsOfShape (CostructuredArrow (affPull f).op V) (ModuleCat.{u} Λ) :=
  hasColimitsOfShape_of_essentiallySmall.{u} _ _

instance (F : (Y.AffineEtale)ᵒᵖ ⥤ ModuleCat.{u} Λ) : (affPull f).op.HasLeftKanExtension F := by
  have : (affPull f).op.HasPointwiseLeftKanExtension F := fun _ => inferInstance
  infer_instance

/-- Pushforward `f_*` of etale sheaves of `Λ`-modules. -/
abbrev push : EtSh Λ X ⥤ EtSh Λ Y :=
  (etPull f).sheafPushforwardContinuous (ModuleCat.{u} Λ) Y.smallEtaleTopology X.smallEtaleTopology

instance : (push f Λ).IsRightAdjoint := by
  have h1 : ((affPull f).sheafPushforwardContinuous (ModuleCat.{u} Λ)
      (Scheme.AffineEtale.topology Y) X.smallEtaleTopology).IsRightAdjoint := inferInstance
  have h2 : (push f Λ ⋙ (Scheme.AffineEtale.Spec Y).sheafPushforwardContinuous (ModuleCat.{u} Λ)
      (Scheme.AffineEtale.topology Y) Y.smallEtaleTopology).IsRightAdjoint := h1
  exact (Functor.isRightAdjoint_comp_iff_left _ _).1 h2

/-- Pullback `f^*` of etale sheaves of `Λ`-modules: the left adjoint of `f_*`. -/
abbrev pull : EtSh Λ Y ⥤ EtSh Λ X :=
  (etPull f).sheafPullback (ModuleCat.{u} Λ) Y.smallEtaleTopology X.smallEtaleTopology

/-- `f^* ⊣ f_*`. -/
def pullAdj : pull f Λ ⊣ push f Λ := Functor.sheafAdjunctionContinuous _ _ _ _

end Sheaves

section Stalks

/-- The composite geometric point `s ≫ f` of `Y`. -/
def GeomPt.map (s : GeomPt X) : GeomPt Y where
  Ω := s.Ω
  pt := s.pt ≫ f

/-- The fibre functor of `s ≫ f` is the fibre functor of `s` composed with base change. -/
def fiberMapIso (s : GeomPt X) :
    (s.map f).point.fiber ≅ etPull f ⋙ s.point.fiber :=
  Functor.isoWhiskerLeft (Scheme.Etale.forget Y)
      ((Adjunction.compCoyonedaIso (CategoryTheory.Over.mapPullbackAdj f)).app
        (op (CategoryTheory.Over.mk s.pt))) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (etPullForgetIso f).symm _ ≪≫ Functor.associator _ _ _

instance (s : GeomPt X) : InitiallySmall.{u} (etPull f ⋙ s.point.fiber).Elements := by
  let e : (s.map f).point.fiber.Elements ≌ (etPull f ⋙ s.point.fiber).Elements :=
    (CategoryOfElements.structuredArrowEquivalence _).trans
      ((StructuredArrow.mapNatIso (fiberMapIso f s)).trans
        (CategoryOfElements.structuredArrowEquivalence _).symm)
  have : InitiallySmall.{u} (s.map f).point.fiber.Elements := (s.map f).point.initiallySmall
  exact initiallySmall_of_initial_of_initiallySmall e.functor

/-- The point of `Y`'s site obtained from `s` through `etPull f`. -/
abbrev comapPt (s : GeomPt X) : (Y.smallEtaleTopology).Point :=
  s.point.comap (etPull f) (etPull_coverPreserving f)

/-- The two points of `Y`'s site at `s ≫ f` agree. -/
def comapPtIso (s : GeomPt X) : (s.map f).point ≅ comapPt f s where
  hom := ⟨(fiberMapIso f s).inv⟩
  inv := ⟨(fiberMapIso f s).hom⟩
  hom_inv_id := by ext : 1; exact (fiberMapIso f s).hom_inv_id
  inv_hom_id := by ext : 1; exact (fiberMapIso f s).inv_hom_id

variable (Λ : Type u) [CommRing Λ]

/-- An isomorphism of points gives an isomorphism of the fibre functors on sheaves. -/
def ptIsoSheafFiber {Z : Scheme.{u}} {Φ₁ Φ₂ : (Z.smallEtaleTopology).Point} (e : Φ₁ ≅ Φ₂) :
    Φ₂.sheafFiber (A := ModuleCat.{u} Λ) ≅ Φ₁.sheafFiber where
  hom := e.hom.sheafFiber
  inv := e.inv.sheafFiber
  hom_inv_id := by
    rw [← GrothendieckTopology.Point.Hom.sheafFiber_comp, e.inv_hom_id,
      GrothendieckTopology.Point.Hom.sheafFiber_id]
  inv_hom_id := by
    rw [← GrothendieckTopology.Point.Hom.sheafFiber_comp, e.hom_inv_id,
      GrothendieckTopology.Point.Hom.sheafFiber_id]

/-- **Stalks of a pullback**: `(f^*F)_s ≅ F_(s ≫ f)`, naturally in `F`. -/
def pullStalkIso (s : GeomPt X) : pull f Λ ⋙ s.stalkF Λ ≅ (s.map f).stalkF Λ :=
  (s.point.sheafFiberComapIso (etPull f) (etPull_coverPreserving f) (ModuleCat.{u} Λ)).symm ≪≫
    ptIsoSheafFiber Λ (comapPtIso f s)

end Stalks

end RamanujanPetersson.EtSheaves

end

end

-- ===== S4.Def_RP_EtSheaves_Const =====
section

/-!
# S4-EtSheaves, part 3: constant, locally constant and lisse etale sheaves

`constSh Λ X M` is the constant sheaf with value `M` (Mathlib's `constantSheaf`: sheafification of the
constant presheaf), `unitSh Λ X = Λ_X`. Its stalk at every geometric point is `M` (`constStalkIso`), and
`f^*` of a constant sheaf is constant (`pullConstIso`: both are left adjoint to global sections).
`F` is locally constant (`IsLocConst`) if every point of `X` is in the image of an etale `U → X` with
`F|_U` constant; lisse (`IsLisse`, = locally constant constructible) if moreover the values are finite
`Λ`-modules. A lisse sheaf has finite stalks, and conversely a locally constant sheaf with finite stalks
is lisse (`isLisse_iff`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtSheaves

universe u

variable (Λ : Type u) [CommRing Λ]

/-- The constant etale sheaf with value `M`. -/
abbrev constSh (X : Scheme.{u}) (M : ModuleCat.{u} Λ) : EtSh Λ X :=
  (constantSheaf X.smallEtaleTopology (ModuleCat.{u} Λ)).obj M

/-- The unit sheaf `Λ_X`. -/
abbrev unitSh (X : Scheme.{u}) : EtSh Λ X := constSh Λ X (ModuleCat.of Λ Λ)

attribute [local instance] IsFiltered.isConnected in
/-- **Stalks of a constant sheaf**: `(M_X)_s ≅ M` at every geometric point `s`. -/
def constStalkIso {X : Scheme.{u}} (s : GeomPt X) (M : ModuleCat.{u} Λ) :
    (s.stalkF Λ).obj (constSh Λ X M) ≅ M :=
  (s.point.presheafToSheafCompSheafFiberIso (ModuleCat.{u} Λ)).app ((Functor.const _).obj M) ≪≫
    IsColimit.coconePointUniqueUpToIso
      (s.point.isColimitPresheafFiberCocone ((Functor.const X.Etaleᵒᵖ).obj M))
      (isColimitConstCocone _ M)

section PullConst

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **`f^*` of a constant sheaf is constant**, naturally in the value: both `constantSheaf ⋙ f^*`
and `constantSheaf` are left adjoint to global sections over `X = X ×_Y Y`. -/
def pullConstIso :
    constantSheaf Y.smallEtaleTopology (ModuleCat.{u} Λ) ⋙ pull f Λ ≅
      constantSheaf X.smallEtaleTopology (ModuleCat.{u} Λ) :=
  ((constantSheafAdj _ _ (terminalIsTerminal (C := Y.Etale))).comp (pullAdj f Λ)).leftAdjointUniq
    ((constantSheafAdj _ _ ((terminalIsTerminal (C := Y.Etale)).isTerminalObj (etPull f))).ofNatIsoRight
      (Iso.refl _))

/-- `f^* M_Y ≅ M_X`. -/
def pullConst (M : ModuleCat.{u} Λ) : (pull f Λ).obj (constSh Λ Y M) ≅ constSh Λ X M :=
  (pullConstIso Λ f).app M

end PullConst

variable {X : Scheme.{u}}

/-- `F` is locally constant: every point lies in the image of an etale `U → X` with `F|_U` constant. -/
def IsLocConst (F : EtSh Λ X) : Prop :=
  ∀ x : X, ∃ (U : X.Etale) (v : U.left), U.hom v = x ∧
    ∃ M : ModuleCat.{u} Λ, Nonempty ((pull U.hom Λ).obj F ≅ constSh Λ U.left M)

/-- `F` is lisse (locally constant constructible): locally constant with finite values. -/
def IsLisse (F : EtSh Λ X) : Prop :=
  ∀ x : X, ∃ (U : X.Etale) (v : U.left), U.hom v = x ∧
    ∃ M : ModuleCat.{u} Λ, Module.Finite Λ M ∧ Nonempty ((pull U.hom Λ).obj F ≅ constSh Λ U.left M)

variable {Λ}

theorem IsLisse.isLocConst {F : EtSh Λ X} (hF : IsLisse Λ F) : IsLocConst Λ F := fun x => by
  obtain ⟨U, v, hv, M, -, e⟩ := hF x
  exact ⟨U, v, hv, M, e⟩

/-- The identity of `X` as an etale `X`-scheme. -/
def etId (X : Scheme.{u}) : X.Etale := MorphismProperty.Over.mk ⊤ (𝟙 X) (by infer_instance)

/-- A constant sheaf with finite value is lisse. -/
theorem isLisse_constSh (M : ModuleCat.{u} Λ) [Module.Finite Λ M] : IsLisse Λ (constSh Λ X M) :=
  fun x => ⟨etId X, x, rfl, M, inferInstance, ⟨pullConst Λ (𝟙 X) M⟩⟩

theorem isLisse_unitSh : IsLisse Λ (unitSh Λ X) := isLisse_constSh _

/-- If `F|_U ≅ M_U` and `U → X` hits the centre of `s`, then `F_s ≅ M`. -/
theorem nonempty_stalk_iso {F : EtSh Λ X} (U : X.Etale) (v : U.left) (M : ModuleCat.{u} Λ)
    (e : (pull U.hom Λ).obj F ≅ constSh Λ U.left M) (s : GeomPt X) (hv : U.hom v = s.center) :
    Nonempty ((s.stalkF Λ).obj F ≅ M) := by
  have : Etale U.hom := U.prop
  obtain ⟨Ω, pt⟩ := s
  obtain ⟨l, hl, -⟩ := Scheme.exists_fac_of_etale_of_isSepClosed U.hom pt v hv
  let t : GeomPt U.left := ⟨Ω, l⟩
  have ht : t.map U.hom = ⟨Ω, pt⟩ := by rw [← hl]; rfl
  rw [← ht]
  exact ⟨((pullStalkIso U.hom Λ t).app F).symm ≪≫ (t.stalkF Λ).mapIso e ≪≫ constStalkIso Λ t M⟩

/-- **Stalks of a lisse sheaf are finite**, at every geometric point. -/
theorem IsLisse.finite_stalkF {F : EtSh Λ X} (hF : IsLisse Λ F) (s : GeomPt X) :
    Module.Finite Λ ((s.stalkF Λ).obj F) := by
  obtain ⟨U, v, hv, M, hM, ⟨e⟩⟩ := hF s.center
  obtain ⟨e'⟩ := nonempty_stalk_iso U v M e s hv
  exact Module.Finite.equiv e'.toLinearEquiv.symm

end RamanujanPetersson.EtSheaves

end

end

-- ===== S4.Def_RP_EtSheaves_PullComp =====
section

/-!
# S4-EtSheaves, part 4: pullback along a composite; pullback preserves (locally) constant sheaves

`pullCompIso g f : (g ≫ f)^* ≅ f^* ⋙ g^*` (from base change along a composite and uniqueness of left
adjoints), `pullCongr` (equal maps give isomorphic pullbacks). Consequently `f^*` preserves locally
constant and lisse sheaves (`IsLocConst.pull`, `IsLisse.pull`): if `F|_U` is constant then
`(f^*F)|_(U ×_Y X)` is constant.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtSheaves

universe u

variable (Λ : Type u) [CommRing Λ]

section Comp

variable {W X Y : Scheme.{u}} (g : W ⟶ X) (f : X ⟶ Y)

/-- Base change along a composite: `etPull (g ≫ f) ≅ etPull f ⋙ etPull g`. -/
def etPullCompIso : etPull (g ≫ f) ≅ etPull f ⋙ etPull g :=
  MorphismProperty.Over.pullbackComp g f

/-- `f_*` along a composite: `g_* ⋙ f_* ≅ (g ≫ f)_*`. -/
def pushCompIso : push g Λ ⋙ push f Λ ≅ push (g ≫ f) Λ :=
  Functor.sheafPushforwardContinuousComp' (etPullCompIso g f).symm (ModuleCat.{u} Λ)
    Y.smallEtaleTopology X.smallEtaleTopology W.smallEtaleTopology

/-- **Pullback along a composite**: `(g ≫ f)^* ≅ f^* ⋙ g^*`. -/
def pullCompIso : pull (g ≫ f) Λ ≅ pull f Λ ⋙ pull g Λ :=
  (pullAdj (g ≫ f) Λ).leftAdjointUniq
    (((pullAdj f Λ).comp (pullAdj g Λ)).ofNatIsoRight (pushCompIso Λ g f))

end Comp

/-- Equal morphisms have isomorphic pullback functors. -/
def pullCongr {X Y : Scheme.{u}} {f f' : X ⟶ Y} (h : f = f') : pull f Λ ≅ pull f' Λ :=
  eqToIso (by rw [h])

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {Λ}

/-- If `F|_U ≅ M_U` for `U` etale over `Y`, then `(f^*F)|_(U ×_Y X) ≅ M`. -/
def pullLocalIso {F : EtSh Λ Y} (U : Y.Etale) (M : ModuleCat.{u} Λ)
    (e : (pull U.hom Λ).obj F ≅ constSh Λ U.left M) :
    (pull ((etPull f).obj U).hom Λ).obj ((pull f Λ).obj F) ≅ constSh Λ ((etPull f).obj U).left M :=
  ((pullCompIso Λ (pullback.snd U.hom f) f).app F).symm ≪≫
    (pullCongr Λ (pullback.condition (f := U.hom) (g := f)).symm).app F ≪≫
    (pullCompIso Λ (pullback.fst U.hom f) U.hom).app F ≪≫
    (pull (pullback.fst U.hom f) Λ).mapIso e ≪≫ pullConst Λ (pullback.fst U.hom f) M

/-- **`f^*` preserves locally constant sheaves.** -/
theorem IsLocConst.pull {F : EtSh Λ Y} (hF : IsLocConst Λ F) :
    IsLocConst Λ ((EtSheaves.pull f Λ).obj F) := by
  intro x
  obtain ⟨U, v, hv, M, ⟨e⟩⟩ := hF (f x)
  obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback v x hv
  exact ⟨(etPull f).obj U, z, hz, M, ⟨pullLocalIso f U M e⟩⟩

end RamanujanPetersson.EtSheaves

end

end

-- ===== S4.Def_RP_EtSheaves_Tensor =====
section

/-!
# S4-EtSheaves, part 5: tensor products of etale sheaves

`EtSh Λ X` carries Mathlib's monoidal structure on sheaves (localisation of the pointwise tensor
product of presheaves; the small etale site has enough points, so sheafification is monoidal).
* stalks: `(F ⊗ G)_s ≅ F_s ⊗ G_s` (`stalkTensIso`);
* constant sheaves: `M_X ⊗ N_X ≅ (M ⊗ N)_X` (`constTensIso`);
* for an etale `g : U ⟶ X`, `g^*` is restriction along `etComp g : U.Etale ⥤ X.Etale`
  (`sheafifyPullIso`: `g^* ∘ sheafify ≅ sheafify ∘ restriction`, from uniqueness of left adjoints),
  hence `g^*(F ⊗ G) ≅ g^*F ⊗ g^*G` (`pullTensIso`);
* `IsLisse.tens`: lisse ⊗ lisse is lisse; `IsLocConst.tens` likewise.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Limits Opposite MonoidalCategory

noncomputable section

namespace RamanujanPetersson.EtSheaves

universe u

variable (Λ : Type u) [CommRing Λ]

section Etale

variable {U X : Scheme.{u}} (g : U ⟶ X) [Etale g]

/-- Composition with an etale `g : U ⟶ X`: etale `U`-schemes are etale `X`-schemes. -/
def etComp : U.Etale ⥤ X.Etale := MorphismProperty.Over.map (P := @Etale) ⊤ (inferInstance : Etale g)

/-- `etComp g ⊣ etPull g`. -/
def etCompAdj : etComp g ⊣ etPull g :=
  MorphismProperty.Over.mapPullbackAdj (P := @Etale) (Q := ⊤) g (inferInstance : Etale g) trivial

end Etale

variable {X : Scheme.{u}} {Λ}

/-- If `F|_U ≅ M` then `F|_T ≅ M` for every `T ⟶ U`. -/
def restrictLocalIso {F : EtSh Λ X} (U : X.Etale) (M : ModuleCat.{u} Λ)
    (e : (pull U.hom Λ).obj F ≅ constSh Λ U.left M) {T : Scheme.{u}} (h : T ⟶ U.left) :
    (pull (h ≫ U.hom) Λ).obj F ≅ constSh Λ T M :=
  (pullCompIso Λ h U.hom).app F ≪≫ (pull h Λ).mapIso e ≪≫ pullConst Λ h M

/-- A common etale refinement of two etale neighbourhoods `U`, `V` of `x`. -/
theorem exists_common_refinement (U V : X.Etale) (u : U.left) (v : V.left)
    (h : V.hom v = U.hom u) :
    ∃ (W : X.Etale) (w : W.left), W.hom w = U.hom u ∧
      ∃ (a : W.left ⟶ U.left) (b : W.left ⟶ V.left), W.hom = a ≫ U.hom ∧ W.hom = b ≫ V.hom := by
  obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback v u h
  refine ⟨(etComp U.hom).obj ((etPull U.hom).obj V), z, ?_, pullback.snd V.hom U.hom,
    pullback.fst V.hom U.hom, rfl, (pullback.condition (f := V.hom) (g := U.hom)).symm⟩
  change U.hom (pullback.snd V.hom U.hom z) = _
  rw [hz2]

end RamanujanPetersson.EtSheaves

end

end

-- ===== S4.Def_RP_EtSheaves_Res =====
section

/-!
# S4-EtSheaves, part 6: restriction along an etale map

For an etale `g : U ⟶ X`, `etComp g : U.Etale ⥤ X.Etale` (composition with `g`) is continuous, so
restriction `res g` (precomposition with `etComp g`) maps sheaves to sheaves. It is left adjoint to
`g_*`, hence `g^* ≅ res g` (`pullIsoRes`): the sections of `g^*F` over `W` are `F(W → U → X)`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtSheaves

universe u

variable {U X : Scheme.{u}} (g : U ⟶ X) [Etale g]

@[simp] theorem etComp_obj_left (W : U.Etale) : ((etComp g).obj W).left = W.left := rfl

@[simp] theorem etComp_obj_hom (W : U.Etale) : ((etComp g).obj W).hom = W.hom ≫ g := rfl

@[simp] theorem etComp_map_left {W W' : U.Etale} (φ : W ⟶ W') : ((etComp g).map φ).left = φ.left :=
  rfl

/-- An etale `X`-scheme `T` with a map `a : T ⟶ W` (over `X`) to `etComp g W` is etale over `U`. -/
def etLift {W : U.Etale} (T : X.Etale) (a : T.left ⟶ W.left) (ha : a ≫ W.hom ≫ g = T.hom) : U.Etale :=
  MorphismProperty.Over.mk ⊤ (a ≫ W.hom) (by
    have h1 : Etale ((a ≫ W.hom) ≫ g) := by
      rw [Category.assoc, ha]
      exact T.prop
    exact MorphismProperty.of_postcomp (W := @Etale) (W' := @Etale) (a ≫ W.hom) g
      (inferInstance : Etale g) h1)

/-- `etComp g` preserves covers. -/
theorem etComp_coverPreserving :
    CoverPreserving U.smallEtaleTopology X.smallEtaleTopology (etComp g) where
  cover_preserve {V} {R} hR := by
    rw [mem_smallEtale_iff] at hR ⊢
    intro z
    obtain ⟨W, φ, w, hφ, hw⟩ := hR z
    exact ⟨_, (etComp g).map φ, w, R.image_mem_functorPushforward (etComp g) hφ, hw⟩

set_option backward.isDefEq.respectTransparency false in
/-- `etComp g` preserves compatible families (as `Over.map` does in Mathlib's `Sites/Over`). -/
theorem etComp_compatiblePreserving :
    CompatiblePreserving X.smallEtaleTopology (etComp g) where
  compatible {F Z _ x hx Y₁ Y₂ T f₁ f₂ g₁ g₂ hg₁ hg₂ h} := by
    have h1 : f₁.left ≫ Y₁.hom ≫ g = T.hom := MorphismProperty.Over.w f₁
    have hl : f₁.left ≫ g₁.left = f₂.left ≫ g₂.left := by
      have := congrArg (fun φ : T ⟶ (etComp g).obj Z => φ.left) h
      exact this
    have h2 : f₂.left ≫ Y₂.hom = f₁.left ≫ Y₁.hom := by
      rw [← MorphismProperty.Over.w g₂, ← Category.assoc, ← hl, Category.assoc,
        MorphismProperty.Over.w g₁]
    let W' : U.Etale := etLift g (W := Y₁) T f₁.left h1
    let g₁' : W' ⟶ Y₁ := MorphismProperty.Over.homMk f₁.left rfl trivial
    let g₂' : W' ⟶ Y₂ := MorphismProperty.Over.homMk f₂.left h2 trivial
    let e : (etComp g).obj W' ≅ T := MorphismProperty.Over.isoMk (Iso.refl _)
      (by simpa [W', etLift] using h1.symm)
    have e1 : f₁ = e.inv ≫ (etComp g).map g₁' :=
      MorphismProperty.Over.Hom.ext (Category.id_comp f₁.left).symm
    have e2 : f₂ = e.inv ≫ (etComp g).map g₂' :=
      MorphismProperty.Over.Hom.ext (Category.id_comp f₂.left).symm
    have hc := hx g₁' g₂' hg₁ hg₂ (MorphismProperty.Over.Hom.ext hl)
    rw [e1, e2, op_comp, op_comp, F.obj.map_comp, F.obj.map_comp, types_comp_apply,
      types_comp_apply]
    exact congrArg (F.obj.map e.inv.op) hc

instance : (etComp g).IsContinuous U.smallEtaleTopology X.smallEtaleTopology :=
  Functor.isContinuous_of_coverPreserving (etComp_compatiblePreserving g) (etComp_coverPreserving g)

variable (Λ : Type u) [CommRing Λ]

/-- Restriction of etale sheaves along an etale `g`: `(res g F)(W) = F(W → U → X)`. -/
abbrev res : EtSh Λ X ⥤ EtSh Λ U :=
  (etComp g).sheafPushforwardContinuous (ModuleCat.{u} Λ) U.smallEtaleTopology X.smallEtaleTopology

/-- `res g ⊣ g_*`. -/
def resAdj : res g Λ ⊣ push g Λ :=
  (etCompAdj g).sheafPushforwardContinuous (E := ModuleCat.{u} Λ) U.smallEtaleTopology
    X.smallEtaleTopology

/-- **For etale `g`, `g^*` is restriction**: `g^* ≅ res g`. -/
def pullIsoRes : pull g Λ ≅ res g Λ := (pullAdj g Λ).leftAdjointUniq (resAdj g Λ)

end RamanujanPetersson.EtSheaves

end

end

-- ===== S4.Def_RP_EtSheaves_Lsh =====
section

/-!
# S4-EtSheaves, part 12: extension by zero `j_!`

For an etale `j : U ⟶ X`, `lsh j Λ = j_!` is the left adjoint of restriction `res j ≅ j^*`
(`Functor.sheafPullback` along `etComp j`, with the universe trick used for `push`).
Stalks: `(j_! G)_(t ≫ j) ≅ G_t` when `j` is a monomorphism (an open immersion), and
`(j_! G)_s = 0` when the centre of `s` is not in the image of `j`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtSheaves

universe u

variable {U X : Scheme.{u}} (j : U ⟶ X) [Etale j]

section Lsh

variable (Λ : Type u) [CommRing Λ]

/-- `etComp j` restricted to affine etale `U`-schemes. -/
def affComp : U.AffineEtale ⥤ X.Etale := Scheme.AffineEtale.Spec U ⋙ etComp j

instance : (affComp j).IsContinuous (Scheme.AffineEtale.topology U) X.smallEtaleTopology :=
  Functor.isContinuous_comp _ _ _ U.smallEtaleTopology _

instance (V : (X.Etale)ᵒᵖ) :
    HasColimitsOfShape (CostructuredArrow (affComp j).op V) (ModuleCat.{u} Λ) :=
  hasColimitsOfShape_of_essentiallySmall.{u} _ _

instance (F : (U.AffineEtale)ᵒᵖ ⥤ ModuleCat.{u} Λ) : (affComp j).op.HasLeftKanExtension F := by
  have : (affComp j).op.HasPointwiseLeftKanExtension F := fun _ => inferInstance
  infer_instance

instance : (res j Λ).IsRightAdjoint := by
  have h1 : ((affComp j).sheafPushforwardContinuous (ModuleCat.{u} Λ)
      (Scheme.AffineEtale.topology U) X.smallEtaleTopology).IsRightAdjoint := inferInstance
  have h2 : (res j Λ ⋙ (Scheme.AffineEtale.Spec U).sheafPushforwardContinuous (ModuleCat.{u} Λ)
      (Scheme.AffineEtale.topology U) U.smallEtaleTopology).IsRightAdjoint := h1
  exact (Functor.isRightAdjoint_comp_iff_left _ _).1 h2

/-- **Extension by zero** `j_!`: the left adjoint of restriction along the etale `j`. -/
abbrev lsh : EtSh Λ U ⥤ EtSh Λ X :=
  (etComp j).sheafPullback (ModuleCat.{u} Λ) U.smallEtaleTopology X.smallEtaleTopology

/-- `j_! ⊣ res j`. -/
def lshAdj : lsh j Λ ⊣ res j Λ := Functor.sheafAdjunctionContinuous _ _ _ _

end Lsh

section Stalks

/-- For a monomorphism `j`, `X`-maps `Spec Ω ⟶ W` (with `W` over `U`) are the `U`-maps. -/
def lshFiberIso [Mono j] (t : GeomPt U) :
    t.point.fiber ≅ etComp j ⋙ (t.map j).point.fiber :=
  NatIso.ofComponents (fun W => Equiv.toIso
    { toFun := fun (a : Over.mk t.pt ⟶ (Scheme.Etale.forget U).obj W) =>
        (Over.homMk a.left ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ j) (Over.w a))) :
          Over.mk (t.pt ≫ j) ⟶ (Scheme.Etale.forget X).obj ((etComp j).obj W))
      invFun := fun (b : Over.mk (t.pt ≫ j) ⟶ (Scheme.Etale.forget X).obj ((etComp j).obj W)) =>
        (Over.homMk b.left ((cancel_mono j).1 ((Category.assoc _ _ _).trans (Over.w b))) :
          Over.mk t.pt ⟶ (Scheme.Etale.forget U).obj W)
      left_inv := fun _ => Over.OverMorphism.ext rfl
      right_inv := fun _ => Over.OverMorphism.ext rfl })
    (fun _ => ConcreteCategory.hom_ext _ _ fun _ => Over.OverMorphism.ext rfl)

/-- The categories of elements of the two fibre functors agree. -/
def lshElemEquiv [Mono j] (t : GeomPt U) :
    t.point.fiber.Elements ≌ (etComp j ⋙ (t.map j).point.fiber).Elements :=
  (CategoryOfElements.structuredArrowEquivalence _).trans
    ((StructuredArrow.mapNatIso (lshFiberIso j t)).trans
      (CategoryOfElements.structuredArrowEquivalence _).symm)

/-- The point of `U`'s site with fibre `etComp j ⋙ (t ≫ j).fiber`, for `j` mono. -/
def lshPt [Mono j] (t : GeomPt U) : (U.smallEtaleTopology).Point where
  fiber := etComp j ⋙ (t.map j).point.fiber
  isCofiltered := IsCofiltered.of_equivalence (lshElemEquiv j t)
  initiallySmall := by
    have : InitiallySmall.{u} t.point.fiber.Elements := t.point.initiallySmall
    exact initiallySmall_of_initial_of_initiallySmall (lshElemEquiv j t).functor
  jointly_surjective {W} R hR x := by
    obtain ⟨Y, f, hf, y, hy⟩ := t.point.jointly_surjective R hR ((lshFiberIso j t).inv.app W x)
    refine ⟨Y, f, hf, (lshFiberIso j t).hom.app Y y, ?_⟩
    calc (etComp j ⋙ (t.map j).point.fiber).map f ((lshFiberIso j t).hom.app Y y)
        = (lshFiberIso j t).hom.app W (t.point.fiber.map f y) :=
          (types_congr_hom ((lshFiberIso j t).hom.naturality f) y).symm
      _ = (lshFiberIso j t).hom.app W ((lshFiberIso j t).inv.app W x) := by rw [hy]
      _ = x := types_congr_hom ((lshFiberIso j t).inv_hom_id_app W) x

/-- `t` and `lshPt j t` are isomorphic points. -/
def lshPtIso [Mono j] (t : GeomPt U) : t.point ≅ lshPt j t where
  hom := ⟨(lshFiberIso j t).inv⟩
  inv := ⟨(lshFiberIso j t).hom⟩
  hom_inv_id := by ext : 1; exact (lshFiberIso j t).hom_inv_id
  inv_hom_id := by ext : 1; exact (lshFiberIso j t).inv_hom_id

variable (Λ : Type u) [CommRing Λ]

/-- **Stalks of `j_!` on `U`** (`j` mono, e.g. an open immersion): `(j_! G)_(t ≫ j) ≅ G_t`. -/
def lshStalkIso [Mono j] (t : GeomPt U) :
    lsh j Λ ⋙ (t.map j).stalkF Λ ≅ t.stalkF Λ :=
  ((conjugateIsoEquiv
      ((lshAdj j Λ).comp ((t.map j).point.skyscraperSheafAdjunction (A := ModuleCat.{u} Λ)))
      ((lshPt j t).skyscraperSheafAdjunction (A := ModuleCat.{u} Λ))).symm (Iso.refl _)).symm ≪≫
    ptIsoSheafFiber Λ (lshPtIso j t)

/-- **Stalks of `j_!` off the image of `j`** vanish. -/
theorem lsh_stalk_isZero (s : GeomPt X) (hs : s.center ∉ Set.range j) (G : EtSh Λ U) :
    IsZero ((s.stalkF Λ).obj ((lsh j Λ).obj G)) := by
  let adj := (lshAdj j Λ).comp (s.point.skyscraperSheafAdjunction (A := ModuleCat.{u} Λ))
  have hE : ∀ W : U.Etale, IsEmpty (s.point.fiber.obj ((etComp j).obj W)) := fun W =>
    ⟨fun (b : Over.mk s.pt ⟶ (Scheme.Etale.forget X).obj ((etComp j).obj W)) => hs
      ⟨(b.left ≫ W.hom : Spec (CommRingCat.of s.Ω) ⟶ U) default, by
        have hw : (b.left ≫ W.hom) ≫ j = s.pt := (Category.assoc _ _ _).trans (Over.w b)
        rw [← Scheme.Hom.comp_apply, hw]; rfl⟩⟩
  have hsub : ∀ f g : G ⟶ (s.point.skyscraperSheafFunctor ⋙ res j Λ).obj
      ((s.stalkF Λ).obj ((lsh j Λ).obj G)), f = g := by
    intro f g
    refine Sheaf.hom_ext (NatTrans.ext (funext fun W => ?_))
    exact Pi.hom_ext _ _ (fun i => (hE W.unop).elim i)
  rw [IsZero.iff_id_eq_zero]
  exact (adj.homEquiv G _).injective (hsub _ _)

end Stalks

end RamanujanPetersson.EtSheaves

end

end

-- ===== S4.Def_RP_EtSheaves_Hom =====
section

/-!
# S4-EtSheaves, part 7: the internal Hom of etale sheaves

For etale sheaves `F`, `G` of `Λ`-modules on `X`, `homSh F G` is the sheaf `V ↦ Hom(F|_V, G|_V)`
(Mathlib's `presheafHom`: morphisms of the restrictions to `Over V`), shrunk to `Type u`. These hom
sets are small because `Over V ≌ V.left.Etale` (`overOf`) and etale sheaves on `V.left` form a
Grothendieck abelian category. `dualSh F = Hom(F, Λ_X)`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtSheaves

universe u

/-- Whiskering along an equivalence `Φ : D ⥤ Over V` identifies `Hom(P|_V, Q|_V)` with natural
transformations between the restrictions along `Φ ⋙ Over.forget V`. -/
def presheafHomEquiv {C D A : Type*} [Category* C] [Category* D] [Category* A] (P Q : Cᵒᵖ ⥤ A)
    {V : C} (Φ : D ⥤ Over V) [Φ.IsEquivalence] :
    ((Over.forget V).op ⋙ P ⟶ (Over.forget V).op ⋙ Q) ≃
      ((Φ ⋙ Over.forget V).op ⋙ P ⟶ (Φ ⋙ Over.forget V).op ⋙ Q) :=
  (Φ.asEquivalence.op.congrLeft (E := A)).fullyFaithfulInverse.homEquiv

variable {X : Scheme.{u}}

instance etaleHom (V : X.Etale) : Etale V.hom := V.prop

/-- An etale `V.left`-scheme, viewed as an object of `X.Etale` over `V`. -/
def overOf (V : X.Etale) : V.left.Etale ⥤ Over V where
  obj W := Over.mk (MorphismProperty.Over.homMk W.hom rfl trivial : (etComp V.hom).obj W ⟶ V)
  map φ := Over.homMk ((etComp V.hom).map φ)
    (MorphismProperty.Over.Hom.ext (MorphismProperty.Over.w φ))
  map_id W := Over.OverMorphism.ext ((etComp V.hom).map_id W)
  map_comp φ ψ := Over.OverMorphism.ext ((etComp V.hom).map_comp φ ψ)

instance (V : X.Etale) : (overOf V).Faithful where
  map_injective {_ _} _ _ h := MorphismProperty.Over.Hom.ext (congrArg (fun f => f.left.left) h)

instance (V : X.Etale) : (overOf V).Full where
  map_surjective {_ _} ψ := ⟨MorphismProperty.Over.homMk ψ.left.left
    (congrArg (fun f => f.left) (Over.w ψ)) trivial,
    Over.OverMorphism.ext (MorphismProperty.Over.Hom.ext rfl)⟩

instance (V : X.Etale) : (overOf V).EssSurj where
  mem_essImage T := by
    have h : T.hom.left ≫ (etId V.left).hom ≫ V.hom = T.left.hom := by
      change T.hom.left ≫ 𝟙 V.left ≫ V.hom = T.left.hom
      rw [Category.id_comp]
      exact MorphismProperty.Over.w T.hom
    refine ⟨etLift V.hom (W := etId V.left) T.left T.hom.left h, ⟨Over.isoMk
      (MorphismProperty.Over.isoMk (Iso.refl _) ?_) ?_⟩⟩
    · exact (Category.id_comp _).trans h.symm
    · exact MorphismProperty.Over.Hom.ext ((Category.id_comp _).trans (Category.comp_id _).symm)

instance (V : X.Etale) : (overOf V).IsEquivalence where

variable {Λ : Type u} [CommRing Λ] (F G : EtSh Λ X)

/-- Sections of `Hom(F, G)` over `V`: morphisms of the restrictions of `F`, `G` to `Over V`. -/
abbrev HomOver (V : X.Etale) := (Over.forget V).op ⋙ F.obj ⟶ (Over.forget V).op ⋙ G.obj

set_option backward.isDefEq.respectTransparency false in
/-- `HomOver F G V ≃ Hom(F|_V, G|_V)`, morphisms of etale sheaves on `V.left`. -/
def homOverEquiv (V : X.Etale) :
    HomOver F G V ≃ ((res V.hom Λ).obj F ⟶ (res V.hom Λ).obj G) :=
  (presheafHomEquiv F.obj G.obj (overOf V)).trans
    { toFun := fun α => ⟨α⟩
      invFun := fun β => β.hom
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

instance (V : X.Etale) : Small.{u} (HomOver F G V) := by
  have h : IsGrothendieckAbelian.{u} (EtSh Λ V.left) :=
    Scheme.isGrothendieckAbelian_sheaf_smallEtaleTopology V.left (ModuleCat.{u} Λ)
  have : LocallySmall.{u} (EtSh Λ V.left) := h.locallySmall
  exact (small_congr (homOverEquiv F G V)).2 (@LocallySmall.hom_small _ _ this _ _)

/-- `forget ⋙ uliftFunctor` reflects limits indexed by large categories (`Type (u+1)`): such a
limit of `Λ`-modules exists once its sections are `u`-small, which a limit cone in `Type (u+1)`
guarantees. This replaces `isSheaf_iff_isSheaf_forget` on the large etale site. -/
instance reflectsLimit_forgetUlift {J : Type (u + 1)} [Category.{u} J] (K : J ⥤ ModuleCat.{u} Λ) :
    ReflectsLimit K (forget (ModuleCat.{u} Λ) ⋙ uliftFunctor.{u + 1, u}) where
  reflects {c} hc := by
    have hp : Small.{u} ((forget (ModuleCat.{u} Λ) ⋙ uliftFunctor.{u + 1, u}).mapCone c).pt :=
      small_ulift _
    have : Small.{u} (K ⋙ forget (ModuleCat.{u} Λ)).sections :=
      @small_map _ _ hp ((Types.sectionsEquiv (K ⋙ forget (ModuleCat.{u} Λ))).trans
        (Types.isLimitEquivSections hc).symm)
    have : PreservesLimit K (forget (ModuleCat.{u} Λ)) :=
      preservesLimit_of_preserves_limit_cone (ModuleCat.HasLimits.limitConeIsLimit K)
        (Types.Small.limitConeIsLimit (K ⋙ forget _))
    have := reflectsLimit_of_reflectsIsomorphisms K
      (forget (ModuleCat.{u} Λ) ⋙ uliftFunctor.{u + 1, u})
    exact ⟨isLimitOfReflects _ hc⟩

instance reflectsLimitsOfShape_forgetUlift (J : Type (u + 1)) [Category.{u} J] :
    ReflectsLimitsOfShape J (forget (ModuleCat.{u} Λ) ⋙ uliftFunctor.{u + 1, u}) where

instance reflectsLimitsOfSize_forgetUlift :
    ReflectsLimitsOfSize.{u, u + 1} (forget (ModuleCat.{u} Λ) ⋙ uliftFunctor.{u + 1, u}) where

end RamanujanPetersson.EtSheaves

end

end

-- ===== S4.Def_RP_EtSheaves_HomLoc =====
section

/-!
# S4-EtSheaves, part 10: the internal Hom is local

For an etale `g : U ⟶ X`, `Over.post (etComp g) : Over V ⥤ Over (etComp g V)` is an equivalence, so
restricting `Hom(F, G)` to `U` gives `Hom(F|_U, G|_U)` (`resHomIso`, `pullHomIso`); in particular
`g^*(F^∨) ≅ (g^*F)^∨` (`pullDualIso`). `homShCongr` transports `Hom(-, -)` along isomorphisms.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtSheaves

universe u

section Post

variable {U X : Scheme.{u}} (g : U ⟶ X) [Etale g]

instance etComp_faithful : (etComp g).Faithful where
  map_injective {_ _} _ _ h := MorphismProperty.Over.Hom.ext (congrArg (fun f => f.left) h)

instance (V : U.Etale) : (Over.post (X := V) (etComp g)).Full where
  map_surjective {A B} ψ := by
    have h2 : ψ.left.left ≫ B.hom.left = A.hom.left := congrArg (fun f => f.left) (Over.w ψ)
    have h1 : ψ.left.left ≫ B.left.hom = A.left.hom :=
      calc ψ.left.left ≫ B.left.hom = ψ.left.left ≫ (B.hom.left ≫ V.hom) :=
            congrArg (ψ.left.left ≫ ·) (MorphismProperty.Over.w B.hom).symm
        _ = (ψ.left.left ≫ B.hom.left) ≫ V.hom := (Category.assoc _ _ _).symm
        _ = A.hom.left ≫ V.hom := congrArg (· ≫ V.hom) h2
        _ = A.left.hom := MorphismProperty.Over.w A.hom
    exact ⟨Over.homMk (MorphismProperty.Over.homMk ψ.left.left h1 trivial)
      (MorphismProperty.Over.Hom.ext h2), Over.OverMorphism.ext (MorphismProperty.Over.Hom.ext rfl)⟩

instance (V : U.Etale) : (Over.post (X := V) (etComp g)).EssSurj where
  mem_essImage T := by
    have ha : T.hom.left ≫ V.hom ≫ g = T.left.hom := MorphismProperty.Over.w T.hom
    refine ⟨Over.mk (MorphismProperty.Over.homMk T.hom.left rfl trivial :
      etLift g (W := V) T.left T.hom.left ha ⟶ V), ⟨Over.isoMk
        (MorphismProperty.Over.isoMk (Iso.refl _) ?_) ?_⟩⟩
    · exact (Category.id_comp _).trans ((Category.assoc _ _ _).trans ha).symm
    · exact MorphismProperty.Over.Hom.ext (Category.id_comp _)

instance (V : U.Etale) : (Over.post (X := V) (etComp g)).IsEquivalence where

variable {Λ : Type u} [CommRing Λ] (F G : EtSh Λ X)

end Post

section Congr

variable {X : Scheme.{u}} {Λ : Type u} [CommRing Λ] {F F' G G' : EtSh Λ X} (e : F ≅ F') (e' : G ≅ G')

end Congr

variable {U X : Scheme.{u}} (g : U ⟶ X) [Etale g] {Λ : Type u} [CommRing Λ] (F G : EtSh Λ X)

end RamanujanPetersson.EtSheaves

end

end

-- ===== S4.Def_RP_EtSheaves_LshFF =====
section

/-!
# S4-EtSheaves, part 13: `j_!` is fully faithful for a monomorphism `j`

For an etale monomorphism `j : U ⟶ X` (an open immersion), `etComp j` is fully faithful, so the
counit of `res j ⊣ j_*` is an isomorphism; by the adjoint triple `j_! ⊣ j^* ⊣ j_*` the unit
`G ⟶ j^* j_! G` is an isomorphism. Hence `j^*` of the counit `j_! j^* F ⟶ F` is an isomorphism,
and so is its stalk at every geometric point over `U`; the counit is a monomorphism when `j` is
an open immersion (its stalks off `U` vanish).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtSheaves

universe u

variable {U X : Scheme.{u}} (j : U ⟶ X) [Etale j]

section Mono

variable [Mono j]

instance etComp_full : (etComp j).Full where
  map_surjective {W W'} φ := by
    have h : (φ.left ≫ W'.hom) ≫ j = W.hom ≫ j :=
      (Category.assoc _ _ _).trans (MorphismProperty.Over.w φ)
    exact ⟨MorphismProperty.Over.homMk φ.left ((cancel_mono j).1 h) trivial,
      MorphismProperty.Over.Hom.ext rfl⟩

variable (Λ : Type u) [CommRing Λ]

instance isIso_resAdj_counit : IsIso (resAdj j Λ).counit := by
  have := Functor.isContinuous_comp (etComp j) (etPull j) U.smallEtaleTopology
    X.smallEtaleTopology U.smallEtaleTopology
  exact (resAdj j Λ).isIso_counit_of_iso
    (Functor.sheafPushforwardContinuousId' (asIso (etCompAdj j).unit).symm (ModuleCat.{u} Λ)
      U.smallEtaleTopology)

/-- The adjoint triple `j_! ⊣ j^* ⊣ j_*` (with `j^* = res j`). -/
def lshTriple : Adjunction.Triple (lsh j Λ) (res j Λ) (push j Λ) := ⟨lshAdj j Λ, resAdj j Λ⟩

instance isIso_lshAdj_unit : IsIso (lshAdj j Λ).unit :=
  (lshTriple j Λ).isIso_unit_iff_isIso_counit.2 (isIso_resAdj_counit j Λ)

theorem isIso_res_counit (F : EtSh Λ X) :
    IsIso ((res j Λ).map ((lshAdj j Λ).counit.app F)) := by
  have h := (lshAdj j Λ).right_triangle_components F
  have : IsIso ((lshAdj j Λ).unit.app ((res j Λ).obj F) ≫
      (res j Λ).map ((lshAdj j Λ).counit.app F)) := by
    rw [h]; exact IsIso.id _
  exact IsIso.of_isIso_comp_left ((lshAdj j Λ).unit.app ((res j Λ).obj F)) _

/-- Stalks of restriction: `(res j F)_t ≅ F_(t ≫ j)`, naturally in `F`. -/
def resStalkIso (t : GeomPt U) : res j Λ ⋙ t.stalkF Λ ≅ (t.map j).stalkF Λ :=
  Functor.isoWhiskerRight (pullIsoRes j Λ).symm _ ≪≫ pullStalkIso j Λ t

/-- **The counit `j_! j^* F ⟶ F` is an isomorphism on stalks over `U`.** -/
theorem isIso_stalk_counit (t : GeomPt U) (F : EtSh Λ X) :
    IsIso (((t.map j).stalkF Λ).map ((lshAdj j Λ).counit.app F)) := by
  have := isIso_res_counit j Λ F
  have : IsIso ((res j Λ ⋙ t.stalkF Λ).map ((lshAdj j Λ).counit.app F)) :=
    Functor.map_isIso (t.stalkF Λ) ((res j Λ).map ((lshAdj j Λ).counit.app F))
  exact (NatIso.isIso_map_iff (resStalkIso j Λ t) _).1 this

end Mono

section OpenImm

variable [IsOpenImmersion j]

/-- A geometric point whose centre lies in the open `U` comes from `U`. -/
theorem exists_map_eq (s : GeomPt X) (hs : s.center ∈ Set.range j) :
    ∃ t : GeomPt U, t.map j = s := by
  obtain ⟨Ω, pt⟩ := s
  have h : Set.range pt ⊆ Set.range j := by
    rintro _ ⟨a, rfl⟩
    rwa [Subsingleton.elim a default]
  exact ⟨⟨Ω, IsOpenImmersion.lift j pt h⟩, by
    simp only [GeomPt.map, IsOpenImmersion.lift_fac]⟩

variable (Λ : Type u) [CommRing Λ]

/-- Stalks of the counit `j_! j^* F ⟶ F` are monomorphisms (isomorphisms over `U`, zero source off `U`). -/
theorem mono_stalk_counit (F : EtSh Λ X) (s : GeomPt X) :
    Mono ((s.stalkF Λ).map ((lshAdj j Λ).counit.app F)) := by
  rcases em (s.center ∈ Set.range j) with hs | hs
  · obtain ⟨t, rfl⟩ := exists_map_eq j s hs
    have := isIso_stalk_counit j Λ t F
    exact IsIso.mono_of_iso _
  · exact ⟨fun _ _ _ => (lsh_stalk_isZero j Λ s hs ((res j Λ).obj F)).eq_of_tgt _ _⟩

/-- **`j_! j^* F ⟶ F` is a monomorphism** for an open immersion `j`. -/
theorem mono_lshAdj_counit (F : EtSh Λ X) : Mono ((lshAdj j Λ).counit.app F) :=
  (mono_iff_stalk Λ ((lshAdj j Λ).counit.app F)).2 (fun x => mono_stalk_counit j Λ F (geomPtAt x))

end OpenImm

end RamanujanPetersson.EtSheaves

end

end

-- ===== S4.Def_RP_EtSheaves_CutSet =====
section

/-!
# S4-EtSheaves, part 21: `F_S` for a subset `S`

For an open `W`: `openCut W F = j_! j^* F` with `openCutι : F_W ⟶ F`. For the closed complement of an open `V`:
`quotCut V F = coker (F_V ⟶ F)` (`= i_* i^* F`, part 19). For any `S`: `cut S F = (F_{closure S})_O` with
`O = interior (coborder S)` (`= coborder S`, open, when `S` is locally closed). For `S` locally closed the stalk of
`cut S F` is `F_s` over `S` (`cutStalkIso`) and zero elsewhere (`isZero_stalk_cut`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Limits Topology

noncomputable section

namespace RamanujanPetersson.EtSheaves

universe u

variable (Λ : Type u) [CommRing Λ] {X : Scheme.{u}}

/-- `F_W = j_! j^* F` for an open `W`. -/
abbrev openCut (W : X.Opens) (F : EtSh Λ X) : EtSh Λ X := (lsh W.ι Λ).obj ((res W.ι Λ).obj F)

/-- The inclusion `F_W ⟶ F`. -/
abbrev openCutι (W : X.Opens) (F : EtSh Λ X) : openCut Λ W F ⟶ F := (lshAdj W.ι Λ).counit.app F

/-- `F_Z = F / F_V` for the closed complement `Z` of an open `V`. -/
abbrev quotCut (V : X.Opens) (F : EtSh Λ X) : EtSh Λ X := cokernel (openCutι Λ V F)

/-- The projection `F ⟶ F_Z`. -/
abbrev quotCutπ (V : X.Opens) (F : EtSh Λ X) : F ⟶ quotCut Λ V F := cokernel.π (openCutι Λ V F)

variable {Λ}

theorem isIso_stalk_openCutι (W : X.Opens) (F : EtSh Λ X) (s : GeomPt X) (hs : s.center ∈ W) :
    IsIso ((s.stalkF Λ).map (openCutι Λ W F)) := by
  obtain ⟨t, rfl⟩ := exists_map_eq W.ι s (by rw [W.range_ι]; exact hs)
  exact isIso_stalk_counit W.ι Λ t F

theorem isZero_stalk_openCut (W : X.Opens) (F : EtSh Λ X) (s : GeomPt X) (hs : s.center ∉ W) :
    IsZero ((s.stalkF Λ).obj (openCut Λ W F)) :=
  lsh_stalk_isZero W.ι Λ s (by rw [W.range_ι]; exact hs) _

theorem isZero_stalk_quotCut (V : X.Opens) (F : EtSh Λ X) (s : GeomPt X) (hs : s.center ∈ V) :
    IsZero ((s.stalkF Λ).obj (quotCut Λ V F)) := by
  have := isIso_stalk_openCutι V F s hs
  have he : Epi ((s.stalkF Λ).map (openCutι Λ V F)) := IsIso.epi_of_iso _
  exact (isZero_cokernel_of_epi (C := ModuleCat.{u} Λ) ((s.stalkF Λ).map (openCutι Λ V F))).of_iso
    (PreservesCokernel.iso (s.stalkF Λ) (openCutι Λ V F))

end RamanujanPetersson.EtSheaves

end

end

-- ===== S4.Def_RP_EtCompact_CutMap =====
section

/-!
# S4-EtCompact, part 4: maps between cut sheaves

For opens `W' ≤ W` the inclusion `j_{W'!} G|_{W'} ⟶ j_{W!} G|_W` (`openCutLe`, the lift of
`openCutι W'` through the monomorphism `openCutι W`), for opens `V ≤ V'` the quotient map
`G / j_{V!} ⟶ G / j_{V'!}` (`quotCutLe`), functoriality `openCutMap`, and their stalks.
`cutWV W V F := j_{W!}(F / j_{V!} F|_V)|_W` is `F` cut to `W ∩ Vᶜ`; its stalks are
`F_x` for `x ∈ W \ V` and `0` otherwise.
All identities are checked on stalks at the points `geomPtAt x`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits

noncomputable section

namespace RamanujanPetersson.EtCompact

open RamanujanPetersson.EtSheaves

universe u

variable {Λ : Type u} [CommRing Λ] {X : Scheme.{u}}

/-- A morphism of etale sheaves whose stalk maps at all `geomPtAt x` vanish is zero. -/
theorem eq_zero_of_stalk {F G : EtSh Λ X} (φ : F ⟶ G)
    (h : ∀ x : X, ((geomPtAt x).stalkF Λ).map φ = 0) : φ = 0 :=
  hom_ext_stalk Λ (fun x => by rw [h x, Functor.map_zero])

theorem mem_center_geomPtAt {x : X} {W : Set X} (hx : x ∈ W) : (geomPtAt x).center ∈ W := by
  rw [center_geomPtAt]; exact hx

theorem not_mem_center_geomPtAt {x : X} {W : Set X} (hx : x ∉ W) : (geomPtAt x).center ∉ W := by
  rw [center_geomPtAt]; exact hx

instance mono_openCutι (W : X.Opens) (G : EtSh Λ X) : Mono (openCutι Λ W G) :=
  mono_lshAdj_counit W.ι Λ G

/-- `openCutι W' G ≫ (G ⟶ G / j_{W!}) = 0` for `W' ≤ W`. -/
theorem openCutι_comp_quotCutπ {W W' : X.Opens} (h : W' ≤ W) (G : EtSh Λ X) :
    openCutι Λ W' G ≫ quotCutπ Λ W G = 0 := by
  refine eq_zero_of_stalk _ (fun x => ?_)
  by_cases hx : x ∈ W'
  · exact (isZero_stalk_quotCut W G _ (mem_center_geomPtAt (h hx))).eq_of_tgt _ _
  · exact (isZero_stalk_openCut W' G _ (not_mem_center_geomPtAt hx)).eq_of_src _ _

section OpenLe

variable {W W' : X.Opens} (h : W' ≤ W)

/-- The inclusion `j_{W'!} G|_{W'} ⟶ j_{W!} G|_W` for opens `W' ≤ W`. -/
def openCutLe (G : EtSh Λ X) : openCut Λ W' G ⟶ openCut Λ W G :=
  Abelian.monoLift (openCutι Λ W G) (openCutι Λ W' G) (openCutι_comp_quotCutπ h G)

@[reassoc (attr := simp)]
theorem openCutLe_comp (G : EtSh Λ X) : openCutLe h G ≫ openCutι Λ W G = openCutι Λ W' G :=
  Abelian.monoLift_comp _ _ _

end OpenLe

section QuotLe

variable {V V' : X.Opens} (h : V ≤ V')

end QuotLe

section OpenMap

variable (W : X.Opens)

end OpenMap

end RamanujanPetersson.EtCompact

end

end

-- ===== S4.Def_RP_EtSheaves_Closed =====
section

/-!
# S4-EtSheaves, part 14: `i_*` vanishes off `Z`

For `i : Z ⟶ X` and an etale `j : U ⟶ X` whose image misses the image of `i`, the restriction
`j^* i_* G` is the zero sheaf: its values are those of `G` on the empty schemes `W ×_X Z`.
Hence the stalks of `i_* G` vanish at geometric points outside the (closed) image of `i`, every
map `j_! G' ⟶ i_* G` is zero, and `j_! j^* F ⟶ F ⟶ i_* i^* F` is a complex.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtSheaves

universe u

variable (Λ : Type u) [CommRing Λ]

/-- On an etale scheme with empty underlying space, every sheaf has zero value. -/
theorem isZero_obj_of_isEmpty {Y : Scheme.{u}} (G : EtSh Λ Y) (V : Y.Etale)
    (hV : IsEmpty V.left) : IsZero (G.obj.obj (op V)) := by
  have h : (⊥ : Sieve V) ∈ Y.smallEtaleTopology V :=
    (mem_smallEtale_iff V ⊥).2 (fun x => (hV.false x).elim)
  exact (IsZero.iff_id_eq_zero _).2 ((Sheaf.isTerminalOfBotCover G V h).hom_ext _ _)

variable {Z U X : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X) [Etale j]

end RamanujanPetersson.EtSheaves

end

end

-- ===== S4.Def_RP_EtCompact_Exact =====
section

/-!
# S4-EtCompact, part 2: exactness of `f^*`, `i_*` (closed) and `j_!` (open)

Exactness is detected on stalks (`exact_iff_stalk`, `exact_of_family`):
* `f^*` for every `f`: `(f^*F)_s ≅ F_(s ≫ f)` (`pullStalkIso`);
* `i_*` for a closed immersion `i`: at points of `Z`, `i_* ⋙ (t ≫ i)-stalk ≅ t-stalk` (counit iso),
  off `Z` the stalks vanish;
* `j_!` for an open immersion `j`: `lshStalkIso` on the image, zero stalks off it.
Each functor is additive and preserves homology, hence preserves finite limits and colimits.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits

noncomputable section

namespace RamanujanPetersson.EtCompact

open RamanujanPetersson.EtSheaves

universe u

variable (Λ : Type u) [CommRing Λ]

/-- If `G ⋙ s-stalk ≅ t-stalk`, then `G` maps exact complexes to complexes exact at `s`. -/
theorem exact_stalk_of_natIso {X Y : Scheme.{u}} {G : EtSh Λ Y ⥤ EtSh Λ X}
    [G.PreservesZeroMorphisms] (s : GeomPt X) (t : GeomPt Y) (e : G ⋙ s.stalkF Λ ≅ t.stalkF Λ)
    (S : ShortComplex (EtSh Λ Y)) (hS : S.Exact) : ((S.map G).map (s.stalkF Λ)).Exact := by
  rw [← ShortComplex.map_comp]
  exact (ShortComplex.exact_iff_of_iso (S.mapNatIso e)).2 (hS.map _)

/-- If all `s`-stalks of objects in the image of `G` vanish, the image complexes are exact at `s`. -/
theorem exact_stalk_of_isZero {X Y : Scheme.{u}} {G : EtSh Λ Y ⥤ EtSh Λ X}
    [G.PreservesZeroMorphisms] (s : GeomPt X) (h : ∀ F, IsZero ((s.stalkF Λ).obj (G.obj F)))
    (S : ShortComplex (EtSh Λ Y)) : ((S.map G).map (s.stalkF Λ)).Exact :=
  ShortComplex.exact_of_isZero_X₂ _ (h S.X₂)

section Pull

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

instance push_additive' : (push f Λ).Additive where
  map_add {_ _ _ _} := Sheaf.hom_ext (NatTrans.ext (funext fun _ => rfl))

instance pull_additive : (pull f Λ).Additive := (pullAdj f Λ).left_adjoint_additive

/-- `f^*` is exact. -/
theorem pull_map_exact (S : ShortComplex (EtSh Λ Y)) (hS : S.Exact) :
    (S.map (pull f Λ)).Exact := by
  rw [exact_iff_stalk]
  intro x
  exact exact_stalk_of_natIso Λ (geomPtAt x) ((geomPtAt x).map f) (pullStalkIso f Λ (geomPtAt x)) S hS

instance pull_preservesHomology : (pull f Λ).PreservesHomology :=
  Functor.preservesHomology_of_map_exact _ (pull_map_exact Λ f)

instance pull_preservesFiniteLimits : PreservesFiniteLimits (pull f Λ) :=
  Functor.preservesFiniteLimits_of_preservesHomology _

end Pull

section Closed

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

end Closed

section Open

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

instance res_additive : (res j Λ).Additive where
  map_add {_ _ _ _} := Sheaf.hom_ext (NatTrans.ext (funext fun _ => rfl))

instance res_isLeftAdjoint : (res j Λ).IsLeftAdjoint := (resAdj j Λ).isLeftAdjoint

instance lsh_additive : (lsh j Λ).Additive := (lshAdj j Λ).left_adjoint_additive

/-- `j_!` is exact for an open immersion `j`. -/
theorem lsh_map_exact (S : ShortComplex (EtSh Λ U)) (hS : S.Exact) :
    (S.map (lsh j Λ)).Exact := by
  rw [exact_iff_stalk]
  intro x
  by_cases hx : (geomPtAt x).center ∈ Set.range j
  · obtain ⟨t, ht⟩ := exists_map_eq j (geomPtAt x) hx
    rw [← ht]
    exact exact_stalk_of_natIso Λ _ _ (lshStalkIso j Λ t) S hS
  · exact exact_stalk_of_isZero Λ _ (fun G => lsh_stalk_isZero j Λ (geomPtAt x) hx G) S

instance lsh_preservesHomology : (lsh j Λ).PreservesHomology :=
  Functor.preservesHomology_of_map_exact _ (lsh_map_exact Λ j)

instance lsh_preservesFiniteLimits : PreservesFiniteLimits (lsh j Λ) :=
  Functor.preservesFiniteLimits_of_preservesHomology _

instance res_preservesFiniteColimits : PreservesFiniteColimits (res j Λ) := inferInstance

end Open

end RamanujanPetersson.EtCompact

end

end

-- ===== S4.Def_RP_EtCompact_Coh =====
section

/-!
# S4-EtCompact, part 3: etale cohomology as `Ext` from the constant sheaf

`H Λ F n := Ext^n(Λ_X, F)` in `EtSh Λ X` (a Grothendieck abelian category, so `Ext` exists and
there are enough injectives). Long exact sequences in `F` are Mathlib's
`Ext.covariant_sequence_exact₁/₂/₃` (E0Probe amendment A7).

Comparisons (via `extAdjEquiv`):
* `closedH`: for a closed immersion `i : Z ⟶ X`, `H^n(X, i_* G) ≃ H^n(Z, G)`;
* `openH`: for an open immersion `j : U ⟶ X`, `Ext^n_X(j_! Λ_U, F) ≃ H^n(U, F|_U)`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Abelian

noncomputable section

namespace RamanujanPetersson.EtCompact

open RamanujanPetersson.EtSheaves

universe w v u

section ExtIso

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/-- Precomposition with an isomorphism `A ≅ A'` identifies `Ext A' B n` with `Ext A B n`. -/
def extIsoLeft {A A' : C} (e : A ≅ A') (B : C) (n : ℕ) : Ext A' B n ≃+ Ext A B n where
  toFun x := (Ext.mk₀ e.hom).comp x (zero_add n)
  invFun x := (Ext.mk₀ e.inv).comp x (zero_add n)
  left_inv x := by simp [Ext.mk₀_id_comp]
  right_inv x := by simp [Ext.mk₀_id_comp]
  map_add' x y := by simp [Ext.comp_add]

theorem extIsoLeft_apply {A A' : C} (e : A ≅ A') (B : C) (n : ℕ) (x : Ext A' B n) :
    extIsoLeft e B n x = (Ext.mk₀ e.hom).comp x (zero_add n) :=
  rfl

/-- Postcomposition with an isomorphism `B ≅ B'` identifies `Ext A B n` with `Ext A B' n`. -/
def extIsoRight (A : C) {B B' : C} (e : B ≅ B') (n : ℕ) : Ext A B n ≃+ Ext A B' n where
  toFun x := x.comp (Ext.mk₀ e.hom) (add_zero n)
  invFun x := x.comp (Ext.mk₀ e.inv) (add_zero n)
  left_inv x := by
    dsimp only
    rw [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, e.hom_inv_id, Ext.comp_mk₀_id]
  right_inv x := by
    dsimp only
    rw [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, e.inv_hom_id, Ext.comp_mk₀_id]
  map_add' x y := by simp [Ext.add_comp]

theorem extIsoRight_apply (A : C) {B B' : C} (e : B ≅ B') (n : ℕ) (x : Ext A B n) :
    extIsoRight A e n x = x.comp (Ext.mk₀ e.hom) (add_zero n) :=
  rfl

end ExtIso

variable (Λ : Type u) [CommRing Λ]

/-- **Etale cohomology** `H^n(X, F) := Ext^n(Λ_X, F)` in sheaves of `Λ`-modules. -/
abbrev H {X : Scheme.{u}} (F : EtSh Λ X) (n : ℕ) : Type u := Ext (unitSh Λ X) F n

section Closed

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

end Closed

section Open

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

end Open

end RamanujanPetersson.EtCompact

end

end

-- ===== S4.Def_RP_EtCompact_Pres =====
section

/-!
# S4-EtCompact, part 8: presentations and the set-indexed `H^*_c`

`cutWV W V F` only depends on the locally closed set `W ∩ Vᶜ` (up to a canonical chain of stalkwise
isomorphisms). So `HcSet S F n := H^n(X, cut S F)` (`cut` from `Def_RP_EtSheaves_CutSet`, which is
`cutWV (cutOpen S) (cutCompl S)`) is computed by any presentation `S = W ∩ Vᶜ`, and the excision
long exact sequence holds for every locally closed `S` and open `O`:
`… → H^n_c(S ∩ O) → H^n_c(S) → H^n_c(S \ O) → H^(n+1)_c(S ∩ O) → …` (E0Probe P2 in subset form).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Abelian TopologicalSpace

noncomputable section

namespace RamanujanPetersson.EtCompact

open RamanujanPetersson.EtSheaves

universe u

variable {Λ : Type u} [CommRing Λ] {X : Scheme.{u}}

theorem isIso_of_zero_zero {C : Type*} [Category C] {A B : C} (f : A ⟶ B) (hA : IsZero A)
    (hB : IsZero B) : IsIso f :=
  ⟨⟨hB.to_ A, hA.eq_of_src _ _, hB.eq_of_src _ _⟩⟩

section Pres

variable (F : EtSh Λ X)

variable {W₁ V₁ W₂ V₂ : X.Opens}

end Pres

section HcSet

variable (F : EtSh Λ X)

end HcSet

section SetExc

variable (F : EtSh Λ X) {S : Set X} (hS : IsLocallyClosed S) (O : X.Opens)

end SetExc

end RamanujanPetersson.EtCompact

end

end

-- ===== S4.Def_RP_EtCompact_CutFun =====
section

/-!
# S4-EtCompact, part 6: `F ↦ F_{W ∩ Vᶜ}` is exact; long exact sequence in the sheaf variable

`quotFunctor V : F ↦ F / j_{V!} F|_V` and `cutWVFunctor W V = quotFunctor V ⋙ res ⋙ lsh` (whose
value at `F` is `cutWV W V F` by definition) are exact: `quotFunctor` is checked on stalks, the
other two factors are exact by `Def_RP_EtCompact_Exact`. Hence a short exact sequence
`0 → F' → F → F'' → 0` gives the long exact sequence
`… → H^n_c(S, F') → H^n_c(S, F) → H^n_c(S, F'') → H^(n+1)_c(S, F') → …`
(E0Probe amendment A7).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Abelian

noncomputable section

namespace RamanujanPetersson.EtCompact

open RamanujanPetersson.EtSheaves

universe u

variable {Λ : Type u} [CommRing Λ] {X : Scheme.{u}}

section Quot

variable (V : X.Opens)

end Quot

instance lsh_isLeftAdjoint' {U Y : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j] :
    (lsh j Λ).IsLeftAdjoint :=
  (lshAdj j Λ).isLeftAdjoint

section SheafLES

variable (W V : X.Opens) {S : ShortComplex (EtSh Λ X)} (hS : S.ShortExact)

include hS

end SheafLES

end RamanujanPetersson.EtCompact

end

end

-- ===== S4.Def_RP_EtCompact_A1 =====
section

/-!
# S4-EtCompact, part 12: the affine line inside `P^1` (O6, explicit compactifications)

Mathlib has no dehomogenization, so we build `K[X₀, X₁]_(X₀) ≃+* K[t]` by hand: `dehom` (`X₀ ↦ 1`,
`X₁ ↦ t`) is injective on each homogeneous component (`eq_zero_of_dehom`), so the induced map
`awayDehom : Away 𝒜 X₀ →+* K[t]` is bijective (`awayEquivPoly`). Hence `chartA1 : A^1_K ⟶ P^1_K` is an open
immersion over `K` (`chartA1_toSpecK`), and `A1.cpt K : Cpt (A1.toSpecK K)` is the compactification
`A^1 ⊆ P^1 → Spec K` (closure `Z = P^1`).
-/

set_option autoImplicit false

open AlgebraicGeometry MvPolynomial CategoryTheory HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace RamanujanPetersson.EtCompact

universe u

variable {K : Type u} [Field K]

/-- Dehomogenization `X₀ ↦ 1`, `X₁ ↦ t`. -/
abbrev dehom : MvPolynomial (Fin 2) K →ₐ[K] Polynomial K := aeval ![1, Polynomial.X]

theorem dehom_eq_sum (a : MvPolynomial (Fin 2) K) :
    dehom a = ∑ d ∈ a.support, Polynomial.C (coeff d a) * Polynomial.X ^ (d 1) := by
  rw [aeval_def, eval₂_eq']
  refine Finset.sum_congr rfl (fun d _ => ?_)
  simp [Fin.prod_univ_two]

theorem degree_two_of_mem_support {n : ℕ} {a : MvPolynomial (Fin 2) K} (ha : a.IsHomogeneous n)
    {d : Fin 2 →₀ ℕ} (hd : d ∈ a.support) : d 0 + d 1 = n := by
  have h := ha (mem_support_iff.1 hd)
  simpa [Finsupp.weight_apply, Finsupp.sum_fintype, Fin.sum_univ_two] using h

/-- The coefficient of `t^(m 1)` in the dehomogenization of a homogeneous `a`. -/
theorem coeff_dehom {n : ℕ} {a : MvPolynomial (Fin 2) K} (ha : a.IsHomogeneous n)
    {m : Fin 2 →₀ ℕ} (hm : m 0 + m 1 = n) : (dehom a).coeff (m 1) = coeff m a := by
  rw [dehom_eq_sum, Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single m]
  · rw [Polynomial.coeff_C_mul_X_pow, if_pos rfl]
  · intro d hd hdm
    rw [Polynomial.coeff_C_mul_X_pow, if_neg]
    intro h1
    apply hdm
    have hd' := degree_two_of_mem_support ha hd
    ext i
    fin_cases i
    · show d 0 = m 0
      omega
    · exact h1.symm
  · intro hm'
    rw [Polynomial.coeff_C_mul_X_pow, if_pos rfl]
    exact notMem_support_iff.1 hm'

/-- **Dehomogenization is injective on homogeneous polynomials.** -/
theorem eq_zero_of_dehom {n : ℕ} {a : MvPolynomial (Fin 2) K} (ha : a.IsHomogeneous n)
    (h0 : dehom a = 0) : a = 0 := by
  ext m
  rw [coeff_zero]
  by_cases hm : m ∈ a.support
  · rw [← coeff_dehom ha (degree_two_of_mem_support ha hm), h0, Polynomial.coeff_zero]
  · exact notMem_support_iff.1 hm

theorem dehom_X0 : dehom (X 0 : MvPolynomial (Fin 2) K) = 1 := by
  simp [dehom]

theorem dehom_X1 : dehom (X 1 : MvPolynomial (Fin 2) K) = Polynomial.X := by
  simp [dehom]

theorem isUnit_dehom_X0 :
    IsUnit (((dehom : MvPolynomial (Fin 2) K →ₐ[K] Polynomial K) : MvPolynomial (Fin 2) K →+* Polynomial K)
      (X 0)) := by
  rw [AlgHom.coe_toRingHom, dehom_X0]
  exact isUnit_one

/-- `K[X₀, X₁]_(X₀) → K[t]`, induced by `dehom`. -/
def awayDehom : Away (homogeneousSubmodule (Fin 2) K) (X 0 : MvPolynomial (Fin 2) K) →+* Polynomial K :=
  (Localization.awayLift ((dehom : MvPolynomial (Fin 2) K →ₐ[K] Polynomial K) :
      MvPolynomial (Fin 2) K →+* Polynomial K) (X 0) isUnit_dehom_X0).comp
    (algebraMap (Away (homogeneousSubmodule (Fin 2) K) (X 0 : MvPolynomial (Fin 2) K))
      (Localization.Away (X 0 : MvPolynomial (Fin 2) K)))

theorem awayDehom_mk (n : ℕ) (a : MvPolynomial (Fin 2) K)
    (ha : a ∈ homogeneousSubmodule (Fin 2) K (n • 1)) :
    awayDehom (Away.mk (homogeneousSubmodule (Fin 2) K) (P1.X_mem K 0) n a ha) = dehom a := by
  rw [awayDehom, RingHom.comp_apply]
  change Localization.awayLift _ _ _
    (Away.mk (homogeneousSubmodule (Fin 2) K) (P1.X_mem K 0) n a ha).val = _
  rw [Away.val_mk, Localization.awayLift_mk _ (X 0) a 1 (by rw [AlgHom.coe_toRingHom, dehom_X0, one_mul]) n]
  simp

theorem awayDehom_injective : Function.Injective (awayDehom (K := K)) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective (homogeneousSubmodule (Fin 2) K) (P1.X_mem K 0) x
  rw [awayDehom_mk] at hx
  have ha' : a.IsHomogeneous n := by simpa [mem_homogeneousSubmodule] using ha
  obtain rfl := eq_zero_of_dehom ha' hx
  ext
  rw [Away.val_mk, val_zero]
  exact Localization.mk_zero _

theorem awayDehom_surjective : Function.Surjective (awayDehom (K := K)) := by
  intro p
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨x, rfl⟩ := hp
    obtain ⟨y, rfl⟩ := hq
    exact ⟨x + y, map_add _ _ _⟩
  | monomial n c =>
    have hmem : (C c * X 1 ^ n : MvPolynomial (Fin 2) K) ∈ homogeneousSubmodule (Fin 2) K (n • 1) := by
      rw [smul_eq_mul, mul_one, mem_homogeneousSubmodule]
      exact isHomogeneous_C_mul_X_pow c 1 n
    refine ⟨Away.mk (homogeneousSubmodule (Fin 2) K) (P1.X_mem K 0) n _ hmem, ?_⟩
    rw [awayDehom_mk, map_mul, map_pow, dehom_X1, ← Polynomial.C_mul_X_pow_eq_monomial]
    simp [dehom]

/-- **`K[X₀, X₁]_(X₀) ≃+* K[t]`.** -/
def awayEquivPoly : Away (homogeneousSubmodule (Fin 2) K) (X 0 : MvPolynomial (Fin 2) K) ≃+* Polynomial K :=
  RingEquiv.ofBijective awayDehom ⟨awayDehom_injective, awayDehom_surjective⟩

variable (K) in
/-- The affine line `A^1_K = Spec K[t]`. -/
abbrev A1 : Scheme.{u} := Spec (CommRingCat.of (Polynomial K))

instance isIso_ofHom_awayDehom : IsIso (CommRingCat.ofHom (awayDehom (K := K))) :=
  (RingEquiv.toCommRingCatIso (awayEquivPoly (K := K))).isIso_hom

variable (K) in
/-- **The chart `A^1_K ⟶ P^1_K`** (`t ↦ [1 : t]`). -/
def chartA1 : A1 K ⟶ P1 K :=
  Spec.map (CommRingCat.ofHom (awayDehom (K := K))) ≫ P1.chart0 K

instance isOpenImmersion_chartA1 : IsOpenImmersion (chartA1 K) := by
  unfold chartA1
  infer_instance

end RamanujanPetersson.EtCompact

end

end

-- ===== S4.Def_RP_EtCompact_P1Pts =====
section

/-!
# S4-EtCompact, part 27: points of `P^1_K` (O8a, file 1)

* `P1.genPt K`: the generic point `(0)`; `closure {genPt} = univ`, so `P^1_K` is irreducible (hence connected).
* `P1.infPt K`: the point `∞ = (X₀)`; every point whose ideal contains `X₀` is `∞` (`P1.eq_infPt_of_X0_mem`).
* The image of the chart `chartA1 : A^1_K ⟶ P^1_K` is `D₊(X₀)`, its complement is `{∞}`, so `{∞}` is closed and
  `Spec κ(∞) ⟶ P^1_K` is a closed immersion; for algebraically closed `K`, `κ(∞) ≅ K` is algebraically closed.
-/

set_option autoImplicit false

open AlgebraicGeometry MvPolynomial CategoryTheory

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace RamanujanPetersson.EtCompact

universe u

variable (K : Type u) [Field K]

theorem P1.X_ne_zero (i : Fin 2) : (X i : MvPolynomial (Fin 2) K) ≠ 0 :=
  (MvPolynomial.X_prime (σ := Fin 2) (R := K) (i := i)).ne_zero

theorem P1.X_mem_irrelevant (i : Fin 2) :
    (X i : MvPolynomial (Fin 2) K) ∈ HomogeneousIdeal.irrelevant (homogeneousSubmodule (Fin 2) K) :=
  HomogeneousIdeal.mem_irrelevant_of_mem _ one_pos (P1.X_mem K i)

/-! ### The generic point -/

/-- The generic point `(0)` of `P^1_K`. -/
def P1.genPt : P1 K :=
  (⟨⊥, by rw [HomogeneousIdeal.toIdeal_bot]; exact Ideal.isPrime_bot, fun h => by
      have h0 := h (P1.X_mem_irrelevant K 0)
      rw [← HomogeneousIdeal.mem_iff, HomogeneousIdeal.toIdeal_bot, Ideal.mem_bot] at h0
      exact P1.X_ne_zero K 0 h0⟩ : ProjectiveSpectrum (homogeneousSubmodule (Fin 2) K))

theorem P1.genPt_ideal : (P1.genPt K).asHomogeneousIdeal = ⊥ := rfl

theorem P1.closure_genPt : closure ({P1.genPt K} : Set (P1 K)) = Set.univ := by
  refine Set.eq_univ_of_forall fun y => ?_
  have h := (ProjectiveSpectrum.le_iff_mem_closure (𝒜 := homogeneousSubmodule (Fin 2) K)
    (P1.genPt K) y).mp ((ProjectiveSpectrum.as_ideal_le_as_ideal _ _ _).mp bot_le)
  exact h

/-- **`P^1_K` is irreducible** (so also connected). -/
instance P1.irreducibleSpace : IrreducibleSpace (P1 K) := by
  rw [irreducibleSpace_def, Set.top_eq_univ, ← P1.closure_genPt K]
  exact isIrreducible_singleton.closure

/-! ### The point at infinity -/

/-- The homogeneous prime `(X₀)`. -/
def P1.infIdeal : HomogeneousIdeal (homogeneousSubmodule (Fin 2) K) :=
  ⟨Ideal.span {X 0}, Ideal.homogeneous_span _ _ (by
    rintro _ rfl
    exact ⟨1, P1.X_mem K 0⟩)⟩

theorem P1.infIdeal_toIdeal : (P1.infIdeal K).toIdeal = Ideal.span {X 0} := rfl

/-- The point `∞ = (X₀)` of `P^1_K`. -/
def P1.infPt : P1 K :=
  (⟨P1.infIdeal K, by
      rw [P1.infIdeal_toIdeal, Ideal.span_singleton_prime (P1.X_ne_zero K 0)]
      exact MvPolynomial.X_prime, fun h => by
      have h1 := h (P1.X_mem_irrelevant K 1)
      rw [← HomogeneousIdeal.mem_iff, P1.infIdeal_toIdeal, Ideal.mem_span_singleton,
        MvPolynomial.X_dvd_X] at h1
      exact absurd h1 (by decide)⟩ : ProjectiveSpectrum (homogeneousSubmodule (Fin 2) K))

theorem P1.infPt_ideal : (P1.infPt K).asHomogeneousIdeal = P1.infIdeal K := rfl

theorem P1.X0_mem_infPt : (X 0 : MvPolynomial (Fin 2) K) ∈ (P1.infPt K).asHomogeneousIdeal := by
  rw [← HomogeneousIdeal.mem_iff, P1.infPt_ideal, P1.infIdeal_toIdeal]
  exact Ideal.subset_span rfl

/-- A homogeneous polynomial of degree `d` is `c X₁^d` modulo `X₀`. -/
theorem P1.sub_monomial_mem_span_X0 {d : ℕ} {f : MvPolynomial (Fin 2) K} (hf : f.IsHomogeneous d) :
    f - monomial (Finsupp.single 1 d) (coeff (Finsupp.single 1 d) f) ∈
      Ideal.span ({X 0} : Set (MvPolynomial (Fin 2) K)) := by
  have hs : ({X 0} : Set (MvPolynomial (Fin 2) K)) = X '' {0} := Set.image_singleton.symm
  rw [hs, mem_ideal_span_X_image]
  intro m hm
  refine ⟨0, rfl, fun h0 => ?_⟩
  rw [mem_support_iff, coeff_sub, coeff_monomial] at hm
  by_cases hmd : Finsupp.single 1 d = m
  · rw [if_pos hmd, hmd, sub_self] at hm
    exact hm rfl
  · rw [if_neg hmd, sub_zero] at hm
    apply hmd
    have hdeg : m.degree = d := by
      by_contra h
      exact hm (hf.coeff_eq_zero h)
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_two, h0, zero_add] at hdeg
    ext j
    fin_cases j
    · simp [h0]
    · simp [hdeg]

/-- Every homogeneous polynomial of positive degree lies in `(X₀, X₁)`. -/
theorem P1.mem_span_X_of_pos {d : ℕ} (hd : 0 < d) {f : MvPolynomial (Fin 2) K} (hf : f.IsHomogeneous d) :
    f ∈ Ideal.span (X '' (Set.univ : Set (Fin 2)) : Set (MvPolynomial (Fin 2) K)) := by
  rw [mem_ideal_span_X_image]
  intro m hm
  by_contra hne
  simp only [not_exists, not_and, not_not] at hne
  have hm0 : m = 0 := Finsupp.ext fun j => hne j (Set.mem_univ j)
  have hdeg : m.degree = d := by
    by_contra h
    exact (mem_support_iff.mp hm) (hf.coeff_eq_zero h)
  rw [hm0, Finsupp.degree_eq_sum, Fin.sum_univ_two] at hdeg
  simp only [Finsupp.coe_zero, Pi.zero_apply, add_zero] at hdeg
  omega

theorem P1.X1_not_mem (x : P1 K) (h0 : (X 0 : MvPolynomial (Fin 2) K) ∈ x.asHomogeneousIdeal) :
    (X 1 : MvPolynomial (Fin 2) K) ∉ x.asHomogeneousIdeal := by
  intro h1
  apply x.not_irrelevant_le
  rw [HomogeneousIdeal.irrelevant_le]
  intro i hi a ha
  have ha' : a.IsHomogeneous i := (mem_homogeneousSubmodule i a).mp ha
  have hsp : Ideal.span (X '' (Set.univ : Set (Fin 2)) : Set (MvPolynomial (Fin 2) K)) ≤
      x.asHomogeneousIdeal.toIdeal := by
    rw [Ideal.span_le]
    rintro _ ⟨j, -, rfl⟩
    fin_cases j
    · exact h0
    · exact h1
  exact hsp (P1.mem_span_X_of_pos K hi ha')

theorem P1.le_span_X0 (x : P1 K) (h0 : (X 0 : MvPolynomial (Fin 2) K) ∈ x.asHomogeneousIdeal) :
    x.asHomogeneousIdeal.toIdeal ≤ Ideal.span {X 0} := by
  have hX1 := P1.X1_not_mem K x h0
  have hspan : Ideal.span ({X 0} : Set (MvPolynomial (Fin 2) K)) ≤ x.asHomogeneousIdeal.toIdeal := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact h0
  have hH : (Ideal.span ({X 0} : Set (MvPolynomial (Fin 2) K))).IsHomogeneous
      (homogeneousSubmodule (Fin 2) K) := (P1.infIdeal K).isHomogeneous
  intro r hr
  rw [Ideal.IsHomogeneous.mem_iff (homogeneousSubmodule (Fin 2) K) hH]
  intro i
  set c : MvPolynomial (Fin 2) K := (DirectSum.decompose (homogeneousSubmodule (Fin 2) K) r i :
    MvPolynomial (Fin 2) K) with hc
  have hci : c ∈ x.asHomogeneousIdeal.toIdeal := x.asHomogeneousIdeal.isHomogeneous i hr
  have hch : c.IsHomogeneous i :=
    (mem_homogeneousSubmodule i c).mp (DirectSum.decompose (homogeneousSubmodule (Fin 2) K) r i).2
  have hsub := P1.sub_monomial_mem_span_X0 K hch
  have hmon : monomial (Finsupp.single 1 i) (coeff (Finsupp.single 1 i) c) ∈
      x.asHomogeneousIdeal.toIdeal := by
    have := Ideal.sub_mem _ hci (hspan hsub)
    rwa [sub_sub_cancel] at this
  have hcoef : coeff (Finsupp.single 1 i) c = 0 := by
    by_contra hne
    rw [← C_mul_X_pow_eq_monomial] at hmon
    have hu : IsUnit (C (coeff (Finsupp.single 1 i) c) : MvPolynomial (Fin 2) K) :=
      (isUnit_iff_ne_zero.mpr hne).map C
    rw [Ideal.unit_mul_mem_iff_mem _ hu] at hmon
    exact hX1 (x.isPrime.mem_of_pow_mem i hmon)
  rw [hcoef, monomial_zero, sub_zero] at hsub
  exact hsub

/-- **The only point whose ideal contains `X₀` is `∞`.** -/
theorem P1.eq_infPt_of_X0_mem (x : P1 K) (h0 : (X 0 : MvPolynomial (Fin 2) K) ∈ x.asHomogeneousIdeal) :
    x = P1.infPt K := by
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.toIdeal_injective
  rw [P1.infPt_ideal, P1.infIdeal_toIdeal]
  refine le_antisymm (P1.le_span_X0 K x h0) ?_
  rw [Ideal.span_le, Set.singleton_subset_iff]
  exact h0

/-! ### The chart `A^1_K ⊆ P^1_K` and its complement `{∞}` -/

theorem P1.opensRange_chartA1 :
    (chartA1 K).opensRange = Proj.basicOpen (homogeneousSubmodule (Fin 2) K) (X 0) :=
  (Scheme.Hom.opensRange_comp_of_isIso (Spec.map (CommRingCat.ofHom (awayDehom (K := K))))
    (P1.chart0 K)).trans (Proj.opensRange_awayι ..)

theorem P1.mem_range_chartA1_iff (x : P1 K) : x ∈ (chartA1 K).opensRange ↔ x ≠ P1.infPt K := by
  rw [P1.opensRange_chartA1, Proj.mem_basicOpen]
  constructor
  · rintro h rfl
    exact h (P1.X0_mem_infPt K)
  · intro h h0
    exact h (P1.eq_infPt_of_X0_mem K x h0)

theorem P1.genPt_mem_range : P1.genPt K ∈ (chartA1 K).opensRange := by
  rw [P1.opensRange_chartA1, Proj.mem_basicOpen, P1.genPt_ideal, ← HomogeneousIdeal.mem_iff,
    HomogeneousIdeal.toIdeal_bot, Ideal.mem_bot]
  exact P1.X_ne_zero K 0

end RamanujanPetersson.EtCompact

end

end

-- ===== S4.Def_RP_EtSheaves_GalAct =====
section

/-!
# S4-EtSheaves, part 23: the Galois action on stalks

An automorphism `τ` of `Spec Ω` over `X` is an endomorphism of the point `s` of the small etale site (lifts
`a ↦ τ ≫ a`), so it acts on the stalk functor (`stalkAut`, contravariantly in `τ`). At the geometric point
`geomPtAt x` (`Ω` a separable closure of `κ(x)`) every `σ ∈ Gal(Ω/κ(x))` gives `Spec σ` over `X`, and
`σ ↦ (Spec σ)^*` is a representation `galRep F x` of `Gal(Ω/κ(x))` on `F_x̄`, natural in `F`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtSheaves

universe u

namespace GeomPt

variable {X : Scheme.{u}} (s : GeomPt X)

/-- An automorphism `τ` of `Spec Ω` over `X` as an endomorphism of the point `s` (lifts `a ↦ τ ≫ a`). -/
def autHom (τ : Spec (CommRingCat.of s.Ω) ⟶ Spec (CommRingCat.of s.Ω)) (hτ : τ ≫ s.pt = s.pt) :
    s.point ⟶ s.point :=
  ⟨Functor.whiskerLeft (Scheme.Etale.forget X)
    (coyoneda.map (Over.homMk τ hτ : CategoryTheory.Over.mk s.pt ⟶ CategoryTheory.Over.mk s.pt).op)⟩

theorem autHom_id (h : 𝟙 (Spec (CommRingCat.of s.Ω)) ≫ s.pt = s.pt) : s.autHom (𝟙 _) h = 𝟙 _ := by
  apply GrothendieckTopology.Point.hom_ext
  ext U a
  change Over.homMk (𝟙 _) h ≫ a = a
  rw [← Category.id_comp a]
  congr 1

theorem autHom_comp {τ₁ τ₂ : Spec (CommRingCat.of s.Ω) ⟶ Spec (CommRingCat.of s.Ω)}
    (h₁ : τ₁ ≫ s.pt = s.pt) (h₂ : τ₂ ≫ s.pt = s.pt) (h : (τ₁ ≫ τ₂) ≫ s.pt = s.pt) :
    s.autHom (τ₁ ≫ τ₂) h = s.autHom τ₁ h₁ ≫ s.autHom τ₂ h₂ := by
  have key := Over.homMk_comp (U := CategoryTheory.Over.mk s.pt) (V := CategoryTheory.Over.mk s.pt)
    (W := CategoryTheory.Over.mk s.pt) τ₁ τ₂ h₁ h₂
  apply GrothendieckTopology.Point.hom_ext
  ext U a
  change Over.homMk (τ₁ ≫ τ₂) h ≫ a =
    (Over.homMk τ₁ h₁ : CategoryTheory.Over.mk s.pt ⟶ CategoryTheory.Over.mk s.pt) ≫
      (Over.homMk τ₂ h₂ : CategoryTheory.Over.mk s.pt ⟶ CategoryTheory.Over.mk s.pt) ≫ a
  rw [key]
  exact Category.assoc _ _ _

variable (Λ : Type u) [CommRing Λ]

/-- The action of `τ` on stalks. -/
def stalkAut (τ : Spec (CommRingCat.of s.Ω) ⟶ Spec (CommRingCat.of s.Ω)) (hτ : τ ≫ s.pt = s.pt) :
    s.stalkF Λ ⟶ s.stalkF Λ :=
  GrothendieckTopology.Point.Hom.sheafFiber (A := ModuleCat.{u} Λ) (s.autHom τ hτ)

theorem stalkAut_id {τ : Spec (CommRingCat.of s.Ω) ⟶ Spec (CommRingCat.of s.Ω)} (hτ : τ ≫ s.pt = s.pt)
    (e : τ = 𝟙 _) : s.stalkAut Λ τ hτ = 𝟙 _ := by
  subst e
  simp only [stalkAut, autHom_id]
  exact GrothendieckTopology.Point.Hom.sheafFiber_id _

theorem stalkAut_comp {τ₁ τ₂ τ : Spec (CommRingCat.of s.Ω) ⟶ Spec (CommRingCat.of s.Ω)}
    (h₁ : τ₁ ≫ s.pt = s.pt) (h₂ : τ₂ ≫ s.pt = s.pt) (hτ : τ ≫ s.pt = s.pt) (e : τ = τ₁ ≫ τ₂) :
    s.stalkAut Λ τ hτ = s.stalkAut Λ τ₂ h₂ ≫ s.stalkAut Λ τ₁ h₁ := by
  subst e
  simp only [stalkAut, autHom_comp s h₁ h₂]
  exact GrothendieckTopology.Point.Hom.sheafFiber_comp _ _

end GeomPt

variable {X : Scheme.{u}}

/-- The Galois group `Gal(Ω/κ(x))` of the geometric point `geomPtAt x`. -/
abbrev Gal (x : X) := SeparableClosure (X.residueField x) ≃ₐ[X.residueField x] SeparableClosure (X.residueField x)

/-- `σ ∈ Gal(Ω/κ(x))` as an automorphism of `Spec Ω`. -/
def galSpec (x : X) (σ : Gal x) :
    Spec (CommRingCat.of (SeparableClosure (X.residueField x))) ⟶
      Spec (CommRingCat.of (SeparableClosure (X.residueField x))) :=
  Spec.map (CommRingCat.ofHom (σ : SeparableClosure (X.residueField x) →+* SeparableClosure (X.residueField x)))

theorem galSpec_one (x : X) : galSpec x 1 = 𝟙 _ := by
  rw [galSpec, ← Spec.map_id]
  congr 1

variable (Λ : Type u) [CommRing Λ]

end RamanujanPetersson.EtSheaves

end

end

-- ===== S4.Def_RP_EtCompact_A1Hc =====
section

/-!
# S4-EtCompact, part 29: `H^*_c(A^1, Λ)` inside `P^1` (O8a, file 3)

* `lshResIso j G : j_! j^* G ≅ openCut (range j) G` for any open immersion `j` (stalkwise, via `Abelian.monoLift`).
* `cutOpenIso O F : cut (univ ∩ O) F ≅ openCut O F`.
* `A1.hcEquiv : H^n_c(A^1, Λ) ≃+ H^n_c(univ ∩ A^1 ⊆ P^1, Λ_{P^1})` (the compactification `A1.cpt`).
* The comparison `A1.toP1 n : H^n_c(A^1, Λ) →+ H^n(P^1, Λ)` (extension by zero) is injective for `n = 0`, surjective
  for `n = 1` and bijective for `n ≥ 2` (`K` algebraically closed); `A1.hcEquivP1 : H^(n+2)_c(A^1, Λ) ≃+ H^(n+2)(P^1, Λ)`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Abelian TopologicalSpace

noncomputable section

namespace RamanujanPetersson.EtCompact

open RamanujanPetersson.EtSheaves

universe u

section OpenIm

variable {Λ : Type u} [CommRing Λ] {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

theorem center_mem_opensRange {x : X} (hx : x ∈ Set.range j) : (geomPtAt x).center ∈ j.opensRange := by
  rw [← SetLike.mem_coe, Scheme.Hom.coe_opensRange]
  exact mem_center_geomPtAt hx

theorem center_not_mem_opensRange {x : X} (hx : x ∉ Set.range j) : (geomPtAt x).center ∉ j.opensRange := by
  rw [← SetLike.mem_coe, Scheme.Hom.coe_opensRange]
  exact not_mem_center_geomPtAt hx

theorem lsh_counit_comp_quotCutπ (G : EtSh Λ X) :
    (lshAdj j Λ).counit.app G ≫ quotCutπ Λ j.opensRange G = 0 := by
  refine eq_zero_of_stalk _ (fun x => ?_)
  by_cases hx : x ∈ Set.range j
  · exact (isZero_stalk_quotCut j.opensRange G _ (center_mem_opensRange j hx)).eq_of_tgt _ _
  · exact (lsh_stalk_isZero j Λ _ (not_mem_center_geomPtAt hx) _).eq_of_src _ _

/-- The counit `j_! j^* G ⟶ G` lands in `openCut (range j) G`. -/
def lshToOpenCut (G : EtSh Λ X) : (lsh j Λ).obj ((res j Λ).obj G) ⟶ openCut Λ j.opensRange G :=
  Abelian.monoLift (openCutι Λ j.opensRange G) ((lshAdj j Λ).counit.app G) (lsh_counit_comp_quotCutπ j G)

end OpenIm

section OpenCut

variable {Λ : Type u} [CommRing Λ] {X : Scheme.{u}}

end OpenCut

section A1

variable (K : Type u) [Field K] (Λ : Type u) [CommRing Λ]

variable [IsAlgClosed K]

end A1

end RamanujanPetersson.EtCompact

end

end

-- ===== S4.Def_RP_EtSheaves_TorSec =====
section

/-!
# S4-EtSheaves, part O10d-2(i): sections over `T ×_X Y` for a Galois cover

For a Galois cover `C : GalCover A`, `π : Y = Spec B → X = Spec A` and `T` etale over `Y`, the maps
`ι σ : T → T ×_X Y`, `t ↦ (t, σ_Y t)` (`σ ∈ G`, `σ_Y = Spec σ`) cover `T ×_X Y` by pairwise disjoint sections, so for
every etale sheaf `F` on `X`, restriction is a bijection `F(T ×_X Y) ≅ Π_G F(T)` (`secEquiv`).

* `existsUnique_glue`: gluing for sheaves of modules along a covering family of arrows.
* `exists_eq_comp`: two maps `B → K` to a field that agree on `A` differ by some `σ ∈ G` (from `B ⊗_A B ≅ Π_G B`).
* `eq_of_comp_eq`: `φ ∘ σ = φ ∘ τ` for `φ : B → K` forces `σ = τ` (trivial inertia).
* `sec_cover`, `isEmpty_of_sec`, `existsUnique_sec`, `secEquiv`, `sec_naturality`, `pr_surjective`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtSheaves

section Glue

universe u

variable {Λ : Type u} [CommRing Λ] {Z : Scheme.{u}}

/-- The element `m` as a map `Λ ⟶ M`. -/
abbrev elt {M : ModuleCat.{u} Λ} (m : M) : ModuleCat.of Λ Λ ⟶ M :=
  ModuleCat.ofHom (LinearMap.toSpanSingleton Λ M m)

theorem elt_one {M : ModuleCat.{u} Λ} (m : M) : (elt m).hom 1 = m := by
  simp [elt]

theorem elt_comp {M N : ModuleCat.{u} Λ} (m : M) (f : M ⟶ N) : elt m ≫ f = elt (f.hom m) := by
  ext
  simp [elt]

end Glue

namespace TorSec

attribute [local instance] GalCover.ring GalCover.dom GalCover.alg GalCover.inj GalCover.fin GalCover.grp GalCover.fG GalCover.act GalCover.gal

variable {A : Type} [CommRing A] [IsDomain A] (C : GalCover A)

/-- `σ` as a ring endomorphism of `B`. -/
abbrev rh (σ : C.G) : C.B →+* C.B := MulSemiringAction.toRingHom C.G C.B σ

/-- `X = Spec A`. -/
abbrev SX (A : Type) [CommRing A] : Scheme := Spec (CommRingCat.of A)

/-- `Y = Spec B`. -/
abbrev SY : Scheme := Spec (CommRingCat.of C.B)

/-- The cover `π : Y → X`. -/
abbrev pr : SY C ⟶ SX A := Spec.map (CommRingCat.ofHom (algebraMap A C.B))

/-- `σ_Y = Spec σ : Y → Y`. -/
def act (σ : C.G) : SY C ⟶ SY C := Spec.map (CommRingCat.ofHom (rh C σ))

theorem act_one : act C 1 = 𝟙 _ := by
  rw [act, ← Spec.map_id]
  congr 1
  ext b
  simp

/-- `π` is surjective (lying over). -/
theorem pr_surjective : Function.Surjective (pr C) := by
  intro x
  let x' : PrimeSpectrum A := x
  have := x'.isPrime
  obtain ⟨Q, -, hQ, hQx⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := C.B) x'.asIdeal ⊥
    (Ideal.comap_bot_le_of_injective _ (FaithfulSMul.algebraMap_injective A C.B))
  exact ⟨(⟨Q, hQ⟩ : PrimeSpectrum C.B), PrimeSpectrum.ext hQx⟩

variable {C}

/-- `T ×_X Y` as a scheme. -/
abbrev tpL (T : (SY C).Etale) : Scheme := pullback (T.hom ≫ pr C) (pr C)

variable (Λ : Type) [CommRing Λ]

end TorSec

end RamanujanPetersson.EtSheaves

end

end

-- ===== S4.Def_RP_EtSheaves_GenBr =====
section

/-!
# S4-EtSheaves, part O10b: the generic Galois group maps onto `π₁(Spec A)`

For a field `K` (a fraction field of `A`), a field `κ` with `K → κ`, and a separably closed `Ω/κ`, the maximal
unramified extension `K_U = maxUnram A K` embeds into `Ω` over `K` (`emb`), and restriction along this embedding is a
continuous group homomorphism `toPi1 : Gal(Ω/κ) →* Pi1 A K` (`emb_toPi1`), surjective when `K → κ` is onto
(`toPi1_surjective`), with kernel the automorphisms fixing `emb(K_U)` (`toPi1_eq_one_iff`).

Specialised to the generic point `η = ⊥` of `Spec A` (`κ(η) ≅ K`, `fracIso`), this is the bridge
`genToPi1 : Gal η →* Pi1 A K` from the Galois group acting on stalks at `η̄` (`galRep`) to `GalCover`'s `π₁`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory

noncomputable section

namespace RamanujanPetersson.EtSheaves

namespace GenBr

section Abstract

variable (A K : Type) [CommRing A] [Field K] [Algebra A K]
variable (Ω : Type) [Field Ω] [Algebra K Ω] [IsSepClosed Ω]

/-- `K_U = maxUnram A K` embeds into the separably closed field `Ω` over `K`. -/
def emb : maxUnram A K →ₐ[K] Ω := IsSepClosed.lift

/-- `Ω` as a `K_U`-algebra through `emb`. -/
def embAlg : Algebra (maxUnram A K) Ω := (emb A K Ω).toRingHom.toAlgebra

attribute [local instance] embAlg

variable (κ : Type) [Field κ] [Algebra K κ] [Algebra κ Ω] [IsScalarTower K κ Ω]

end Abstract

section Generic

variable (A K : Type) [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]

/-- The generic point `η = ⊥` of `Spec A`. -/
abbrev genPt : Spec (CommRingCat.of A) := (⊥ : PrimeSpectrum A)

theorem genPt_eq : genPt A = genericPoint (Spec (CommRingCat.of A)) := by
  haveI : IsDomain (CommRingCat.of A) := ‹IsDomain A›
  exact (genericPoint_eq_bot_of_affine (CommRingCat.of A)).symm

/-- The residue field `κ(η)` of `Spec A` at its generic point. -/
abbrev genField : Type := (Spec (CommRingCat.of A)).residueField (genPt A)

/-- `K ≅ κ(η)`: both are fraction fields of `A`. -/
def fracIso : K ≃+* genField A :=
  (IsLocalization.algEquiv (nonZeroDivisors A) K (⊥ : Ideal A).ResidueField).toRingEquiv.trans
    (Scheme.Spec.residueFieldIso (CommRingCat.of A) (genPt A)).commRingCatIsoToRingEquiv.symm

/-- `κ(η)` as a `K`-algebra through `fracIso`. -/
def genAlg : Algebra K (genField A) := (fracIso A K).toRingHom.toAlgebra

attribute [local instance] genAlg

/-- `κ(η)^sep` as a `K`-algebra. -/
def genAlgSep : Algebra K (SeparableClosure (genField A)) :=
  ((algebraMap (genField A) (SeparableClosure (genField A))).comp (algebraMap K (genField A))).toAlgebra

attribute [local instance] genAlgSep

theorem genTower : IsScalarTower K (genField A) (SeparableClosure (genField A)) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

attribute [local instance] genTower

end Generic

end GenBr

end RamanujanPetersson.EtSheaves

end

end

-- ===== S4.Def_RP_EtSheaves_GalFV =====
section

/-!
# S4-EtSheaves, part O10d-2(iv-c): the Galois representation on `(F_V)_x̄` is `ρ ∘ galFV`

Every geometric point `s` of `X = Spec A` lifts to `Y = Spec B` (`exists_lift`); for a lift `l`, the stalk of `F_V`
at `s` is `V` (`stalkFVAt`), an automorphism `τ` of `Spec Ω` over `X` moves `l` by a unique `actOfL τ ∈ G`
(`actOfL_eq_iff`, multiplicative: `actOfL_comp`) and acts on the stalk by `ρ (actOfL τ)` (`stalkAut_stalkFVAt`).
At `x̄ = geomPtAt x` this gives a hom `galFV : Gal(κ(x)^sep/κ(x)) →* G` with open kernel (`isOpen_ker_galFV`, via
the regular representation and discreteness of stalks), and the Galois representation on `(F_V)_x̄` is
`ρ ∘ galFV` (`galRep_FV`, `stalkFVAt_galRep`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtSheaves.TorSec

attribute [local instance] GalCover.ring GalCover.dom GalCover.alg GalCover.inj GalCover.fin GalCover.grp GalCover.fG GalCover.act GalCover.gal

variable {A : Type} [CommRing A] [IsDomain A] {C : GalCover A}

/-- The geometric point of `Y` given by a lift `l` of a geometric point `s` of `X`. -/
def liftPt (s : GeomPt (SX A)) (l : Spec (CommRingCat.of s.Ω) ⟶ SY C) : GeomPt (SY C) where
  Ω := s.Ω
  pt := l

theorem liftPt_map (s : GeomPt (SX A)) (l : Spec (CommRingCat.of s.Ω) ⟶ SY C) (hl : l ≫ pr C = s.pt) :
    (liftPt s l).map (pr C) = s := by
  show GeomPt.mk s.Ω (l ≫ pr C) = s
  rw [hl]

section Act

variable (s : GeomPt (SX A)) (l : Spec (CommRingCat.of s.Ω) ⟶ SY C)

theorem liftPt_comp (hl : l ≫ pr C = s.pt) (τ : Spec (CommRingCat.of s.Ω) ⟶ Spec (CommRingCat.of s.Ω)) (hτ : τ ≫ s.pt = s.pt) :
    τ ≫ ((liftPt s l).map (pr C)).pt = ((liftPt s l).map (pr C)).pt :=
  (by rw [hl]; exact hτ : τ ≫ l ≫ pr C = l ≫ pr C)

end Act

variable (Λ : Type) [CommRing Λ] {V : Type} [AddCommGroup V] [Module Λ V] (ρ : Representation Λ C.G V)

theorem iso_inv_hom_apply {M N : ModuleCat Λ} (e : M ≅ N) (u : N) : e.hom.hom (e.inv.hom u) = u :=
  congrArg (fun φ => φ.hom u) e.inv_hom_id

theorem iso_hom_inv_apply {M N : ModuleCat Λ} (e : M ≅ N) (w : M) : e.inv.hom (e.hom.hom w) = w :=
  congrArg (fun φ => φ.hom w) e.hom_inv_id

theorem iso_conj {M N : ModuleCat Λ} (e : M ≅ N) (f : M → M) (g : N → N)
    (h : ∀ u, f (e.inv.hom u) = e.inv.hom (g u)) (w : M) : e.hom.hom (f w) = g (e.hom.hom w) := by
  calc e.hom.hom (f w) = e.hom.hom (f (e.inv.hom (e.hom.hom w))) := by rw [iso_hom_inv_apply Λ e w]
    _ = e.hom.hom (e.inv.hom (g (e.hom.hom w))) := by rw [h]
    _ = g (e.hom.hom w) := iso_inv_hom_apply Λ e _

end RamanujanPetersson.EtSheaves.TorSec

end

end

-- ===== S4.Def_RP_EtCompact_RepExt =====
section

/-!
# S4-EtCompact, O9b part 2: extensions of `Λ` by a representation and 1-cocycles (pure algebra)

For `ρ : Representation Λ G M` and a 1-cocycle `c` (`IsCocycle ρ c`):
* `extRep ρ c hc` on `M × Λ`: `g • (m, a) = (ρ g m + a • c g, a)`; `M → M × Λ → Λ` is equivariant
  (`extRep_inl`, `extRep_snd`); `isOpen_ker_extRep`: open kernel if `ρ` has open kernel and `c` is locally constant;
* `exists_retraction_iff`: an equivariant retraction of `M → M × Λ` exists iff `c` is a coboundary;
* for an extension `0 → M →ⁱ E →ᵖ Λ → 0` of representations and `w ∈ E` with `p w = 1`: `extCocycle` is a cocycle
  (`isCocycle_extCocycle`), and `extIso : E ≃ₗ M × Λ` intertwines `ρE` with `extRep` (`extIso_equivariant`).
-/

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EtCompact

section RepExt

variable {Λ : Type*} [CommRing Λ] {G : Type*} [Group G] {M : Type*} [AddCommGroup M] [Module Λ M]
  (ρ : Representation Λ G M)

/-- The (inhomogeneous) 1-cocycle condition. -/
def IsCocycle (c : G → M) : Prop := ∀ g h : G, c (g * h) = c g + ρ g (c h)

variable {ρ}

variable (ρ) (c : G → M)

/-- `(m, a) ↦ (ρ g m + a • c g, a)`. -/
def extRepFun (g : G) : (M × Λ) →ₗ[Λ] (M × Λ) :=
  LinearMap.prod (ρ g ∘ₗ LinearMap.fst Λ M Λ + LinearMap.smulRight (LinearMap.snd Λ M Λ) (c g))
    (LinearMap.snd Λ M Λ)

theorem extRepFun_apply (g : G) (v : M × Λ) : extRepFun ρ c g v = (ρ g v.1 + v.2 • c g, v.2) := rfl

variable {c}

end RepExt

section FromExt

variable {Λ : Type*} [CommRing Λ] {G : Type*} [Group G] {M : Type*} [AddCommGroup M] [Module Λ M]
  {ρ : Representation Λ G M} {E : Type*} [AddCommGroup E] [Module Λ E] {ρE : Representation Λ G E}
  {i : M →ₗ[Λ] E} {p : E →ₗ[Λ] Λ}

variable (w : E) (hw : p w = 1)

end FromExt

end RamanujanPetersson.EtCompact

end

end


