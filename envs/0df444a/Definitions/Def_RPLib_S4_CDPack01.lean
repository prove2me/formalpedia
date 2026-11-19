-- Prove2me | Definitions.Def_RPLib_S4_CDPack01
-- name    : RPLib_S4_CDPack01
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T06:11:48.921397+00:00
-- url     : https://prove2.me/theorems/8f543e0e-8bb8-4dfc-98f3-e8f21908cf2c
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 1 of 71
-- statement:
--   Part 1 of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_CupDuality_Alg`: S4-CurveDuality O1: block-triangular perfect pairings and the residue pairing
--   * `Def_RP_HattoriStallings_Core`: Hattori–Stallings traces over `R[G]` (unit S4-HattoriStallings, part A: core)
--   * `Def_RP_PerfectCx_CxAlg`: S4-PD (5), E3 algebra: products, coinvariants of products, and the right regular module
--   * `Def_RP_CdOne_Lc`: S4-PD (3), group layer part 1: locally constant cochains and the index lemma
--   * `Def_RP_CdOne_Grp`: S4-PD (3), group layer part 2: Sylow reduction and `ℤ/l` coefficients
--   * `Def_RP_CdOne_Dev`: S4-PD (3), group layer part 3: dévissage and `H²(P, A) = 0`
--   * `Def_RP_CdOne_Wrap`: S4-PD (3), group layer part 4: wrappers for `cd_l ≤ 1`
--   * `Def_RP_PerfectCx_Z1Ex`: S4-PD (5), E2.1: locally constant 1-cocycles are exact under `H² = 0`
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_CdOneCoh
import Definitions.Def_RPLib_S4_CurveCohPair

/-!
# Curve-duality library package, part 1 of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_CupDuality_Alg`: S4-CurveDuality O1: block-triangular perfect pairings and the residue pairing
* `Def_RP_HattoriStallings_Core`: Hattori–Stallings traces over `R[G]` (unit S4-HattoriStallings, part A: core)
* `Def_RP_PerfectCx_CxAlg`: S4-PD (5), E3 algebra: products, coinvariants of products, and the right regular module
* `Def_RP_CdOne_Lc`: S4-PD (3), group layer part 1: locally constant cochains and the index lemma
* `Def_RP_CdOne_Grp`: S4-PD (3), group layer part 2: Sylow reduction and `ℤ/l` coefficients
* `Def_RP_CdOne_Dev`: S4-PD (3), group layer part 3: dévissage and `H²(P, A) = 0`
* `Def_RP_CdOne_Wrap`: S4-PD (3), group layer part 4: wrappers for `cd_l ≤ 1`
* `Def_RP_PerfectCx_Z1Ex`: S4-PD (5), E2.1: locally constant 1-cocycles are exact under `H² = 0`
-/

set_option autoImplicit false

-- ===== S4.Def_RP_CupDuality_Alg =====
section

/-!
# S4-CurveDuality O1: block-triangular perfect pairings and the residue pairing

* `pairSubQuot`, `pairQuotSub`: for `P : M × N → Λ` and submodules `M₁ ≤ M`, `N₁ ≤ N` with `P(M₁, N₁) = 0`, the
  induced pairings `M₁ × N/N₁ → Λ` and `M/M₁ × N₁ → Λ`.
* `bijective_of_block`, `isPerfPair_of_block`: if both induced pairings are perfect, so is `P` (any `Λ`).
* `dotL`, `constSub`, `sumKer`, `resPair`: the residue pairing `(S → Λ)/Λ × ker(Σ) → Λ`, `(m, r) ↦ Σ m_s r_s`;
  `resPair_isPerfPair` (any finite `S`, any `Λ`).
-/

set_option autoImplicit false

namespace RamanujanPetersson
namespace CupDuality

open Function Module

section Block

variable {Λ M N : Type*} [CommRing Λ] [AddCommGroup M] [AddCommGroup N] [Module Λ M] [Module Λ N]
  (P : M →ₗ[Λ] N →ₗ[Λ] Λ) (M₁ : Submodule Λ M) (N₁ : Submodule Λ N)

/-- The pairing `M₁ × N/N₁ → Λ` induced by `P` when `P(M₁, N₁) = 0`. -/
def pairSubQuot (h0 : ∀ m ∈ M₁, ∀ n ∈ N₁, P m n = 0) : M₁ →ₗ[Λ] (N ⧸ N₁) →ₗ[Λ] Λ :=
  (N₁.liftQ (P.flip.compl₂ M₁.subtype) (fun n hn => by
    rw [LinearMap.mem_ker]; ext m; simpa using h0 m m.2 n hn)).flip

/-- The pairing `M/M₁ × N₁ → Λ` induced by `P` when `P(M₁, N₁) = 0`. -/
def pairQuotSub (h0 : ∀ m ∈ M₁, ∀ n ∈ N₁, P m n = 0) : (M ⧸ M₁) →ₗ[Λ] N₁ →ₗ[Λ] Λ :=
  M₁.liftQ (P.compl₂ N₁.subtype) (fun m hm => by
    rw [LinearMap.mem_ker]; ext n; simpa using h0 m hm n n.2)

variable {P M₁ N₁}

@[simp] theorem pairSubQuot_apply (h0 : ∀ m ∈ M₁, ∀ n ∈ N₁, P m n = 0) (m : M₁) (n : N) :
    pairSubQuot P M₁ N₁ h0 m (Submodule.Quotient.mk n) = P m n := rfl

@[simp] theorem pairQuotSub_apply (h0 : ∀ m ∈ M₁, ∀ n ∈ N₁, P m n = 0) (m : M) (n : N₁) :
    pairQuotSub P M₁ N₁ h0 (Submodule.Quotient.mk m) n = P m n := rfl

/-- If both induced pairings are left-bijective, so is `P`. -/
theorem bijective_of_block (h0 : ∀ m ∈ M₁, ∀ n ∈ N₁, P m n = 0)
    (hA : Bijective (pairSubQuot P M₁ N₁ h0)) (hB : Bijective (pairQuotSub P M₁ N₁ h0)) :
    Bijective P := by
  refine ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro m hm
    have h1 : m ∈ M₁ := by
      have hz : pairQuotSub P M₁ N₁ h0 (Submodule.Quotient.mk m) = pairQuotSub P M₁ N₁ h0 0 := by
        rw [map_zero]; ext n; simp [hm]
      have := hB.1 hz
      rwa [Submodule.Quotient.mk_eq_zero] at this
    have hz : pairSubQuot P M₁ N₁ h0 ⟨m, h1⟩ = pairSubQuot P M₁ N₁ h0 0 := by
      rw [map_zero]; ext n; simp [hm]
    exact congrArg Subtype.val (hA.1 hz)
  · intro φ
    obtain ⟨q, hq⟩ := hB.2 (φ.comp N₁.subtype)
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective M₁ q
    have hv : N₁ ≤ LinearMap.ker (φ - P m) := fun n hn => by
      have := LinearMap.congr_fun hq ⟨n, hn⟩
      simp only [pairQuotSub_apply, LinearMap.coe_comp, Submodule.coe_subtype, comp_apply] at this
      simp [this]
    obtain ⟨m₁, hm₁⟩ := hA.2 (N₁.liftQ (φ - P m) hv)
    refine ⟨m + m₁, ?_⟩
    ext n
    have := LinearMap.congr_fun hm₁ (Submodule.Quotient.mk n)
    simp only [pairSubQuot_apply, Submodule.liftQ_apply, LinearMap.sub_apply] at this
    simp [this]

/-- Block-triangular perfect pairings: if `P(M₁, N₁) = 0` and the induced pairings `M₁ × N/N₁ → Λ` and
`M/M₁ × N₁ → Λ` are perfect, then `P` is perfect. -/
theorem isPerfPair_of_block (h0 : ∀ m ∈ M₁, ∀ n ∈ N₁, P m n = 0)
    [hA : (pairSubQuot P M₁ N₁ h0).IsPerfPair] [hB : (pairQuotSub P M₁ N₁ h0).IsPerfPair] :
    P.IsPerfPair := by
  have h0' : ∀ n ∈ N₁, ∀ m ∈ M₁, P.flip n m = 0 := fun n hn m hm => by
    simpa using h0 m hm n hn
  have eA : pairSubQuot P.flip N₁ M₁ h0' = (pairQuotSub P M₁ N₁ h0).flip :=
    LinearMap.ext fun n => Submodule.linearMap_qext _ (LinearMap.ext fun m => rfl)
  have eB : pairQuotSub P.flip N₁ M₁ h0' = (pairSubQuot P M₁ N₁ h0).flip :=
    Submodule.linearMap_qext _ (LinearMap.ext fun n => LinearMap.ext fun m => rfl)
  refine ⟨bijective_of_block h0 (LinearMap.IsPerfPair.bijective_left _)
    (LinearMap.IsPerfPair.bijective_left _), ?_⟩
  refine bijective_of_block h0' ?_ ?_
  · rw [eA]; exact LinearMap.IsPerfPair.bijective_right _
  · rw [eB]; exact LinearMap.IsPerfPair.bijective_right _

end Block

section Residue

variable (S Λ : Type*) [Fintype S] [CommRing Λ]

/-- `Σ_s m_s r_s` as a bilinear form on `S → Λ`. -/
def dotL : (S → Λ) →ₗ[Λ] (S → Λ) →ₗ[Λ] Λ :=
  LinearMap.mk₂ Λ (fun m r => m ⬝ᵥ r) (fun _ _ _ => add_dotProduct _ _ _)
    (fun _ _ _ => smul_dotProduct _ _ _) (fun _ _ _ => dotProduct_add _ _ _)
    (fun _ _ _ => dotProduct_smul _ _ _)

/-- The constant functions `S → Λ`. -/
def constSub : Submodule Λ (S → Λ) := Submodule.span Λ {1}

/-- The functions `S → Λ` of sum `0`. -/
def sumKer : Submodule Λ (S → Λ) := LinearMap.ker (dotL S Λ 1)

/-- The residue pairing `(S → Λ)/Λ × ker(Σ) → Λ`. -/
def resPair : ((S → Λ) ⧸ constSub S Λ) →ₗ[Λ] sumKer S Λ →ₗ[Λ] Λ :=
  pairQuotSub (dotL S Λ) (constSub S Λ) (sumKer S Λ) (fun m hm r hr => by
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hm
    have hr' : (1 : S → Λ) ⬝ᵥ (r : S → Λ) = 0 := hr
    change (c • (1 : S → Λ)) ⬝ᵥ r = 0
    rw [smul_dotProduct, hr', smul_zero])

variable {S Λ}

@[simp] theorem dotL_apply (m r : S → Λ) : dotL S Λ m r = ∑ s, m s * r s := rfl

theorem mem_sumKer (r : S → Λ) : r ∈ sumKer S Λ ↔ ∑ s, r s = 0 := by
  simp [sumKer, dotL_apply]

omit [Fintype S] in
theorem mem_constSub (m : S → Λ) : m ∈ constSub S Λ ↔ ∃ c : Λ, ∀ s, m s = c := by
  rw [constSub, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c, rfl⟩; exact ⟨c, fun s => by simp⟩
  · rintro ⟨c, hc⟩; exact ⟨c, funext fun s => by simp [hc s]⟩

@[simp] theorem resPair_mk (m : S → Λ) (r : sumKer S Λ) :
    resPair S Λ (Submodule.Quotient.mk m) r = ∑ s, m s * (r : S → Λ) s := rfl

theorem dotProductEquiv_symm_dot [DecidableEq S] (ψ : Dual Λ (S → Λ)) (r : S → Λ) :
    (dotProductEquiv Λ S).symm ψ ⬝ᵥ r = ψ r := by
  have h := LinearMap.congr_fun (LinearEquiv.apply_symm_apply (dotProductEquiv Λ S) ψ) r
  exact h

/-- The residue pairing is perfect. -/
theorem resPair_isPerfPair : (resPair S Λ).IsPerfPair := by
  classical
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [injective_iff_map_eq_zero]
    intro q hq
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [Submodule.Quotient.mk_eq_zero, mem_constSub]
    rcases isEmpty_or_nonempty S with hS | ⟨⟨s0⟩⟩
    · exact ⟨0, fun s => isEmptyElim s⟩
    · refine ⟨m s0, fun s => ?_⟩
      have hr : (Pi.single s 1 - Pi.single s0 1 : S → Λ) ∈ sumKer S Λ := by
        change (1 : S → Λ) ⬝ᵥ (Pi.single s 1 - Pi.single s0 1) = 0
        simp [dotProduct_sub, dotProduct_single]
      have := LinearMap.congr_fun hq ⟨_, hr⟩
      change m ⬝ᵥ (Pi.single s 1 - Pi.single s0 1) = 0 at this
      simp only [dotProduct_sub, dotProduct_single, mul_one] at this
      exact sub_eq_zero.1 this
  · intro φ
    rcases isEmpty_or_nonempty S with hS | ⟨⟨s0⟩⟩
    · refine ⟨0, ?_⟩
      ext ⟨r, hr⟩
      have : (⟨r, hr⟩ : sumKer S Λ) = 0 := Subtype.ext (funext fun s => isEmptyElim s)
      rw [this]; simp
    · let pr : (S → Λ) →ₗ[Λ] (S → Λ) :=
        LinearMap.id - (dotL S Λ 1).smulRight (Pi.single s0 1 : S → Λ)
      have hpr : ∀ r, pr r ∈ sumKer S Λ := fun r => by
        change (1 : S → Λ) ⬝ᵥ (r - ((1 : S → Λ) ⬝ᵥ r) • Pi.single s0 1) = 0
        simp [dotProduct_sub, dotProduct_smul, dotProduct_single]
      let ψ : Dual Λ (S → Λ) := φ.comp (LinearMap.codRestrict (sumKer S Λ) pr hpr)
      refine ⟨Submodule.Quotient.mk ((dotProductEquiv Λ S).symm ψ), ?_⟩
      ext ⟨r, hr⟩
      have hr' : (1 : S → Λ) ⬝ᵥ r = 0 := hr
      change (dotProductEquiv Λ S).symm ψ ⬝ᵥ r = φ ⟨r, hr⟩
      rw [dotProductEquiv_symm_dot]
      change φ ⟨pr r, hpr r⟩ = φ ⟨r, hr⟩
      congr 1
      apply Subtype.ext
      change r - ((1 : S → Λ) ⬝ᵥ r) • Pi.single s0 1 = r
      rw [hr', zero_smul, sub_zero]
  · rw [injective_iff_map_eq_zero]
    rintro ⟨r, hr⟩ hq
    apply Subtype.ext
    funext s
    have := LinearMap.congr_fun hq (Submodule.Quotient.mk (Pi.single s 1))
    change Pi.single s 1 ⬝ᵥ r = 0 at this
    simpa [single_dotProduct] using this
  · intro ψ
    let ψ' : Dual Λ (S → Λ) := ψ.comp (constSub S Λ).mkQ
    let r := (dotProductEquiv Λ S).symm ψ'
    have hr : r ∈ sumKer S Λ := by
      change (1 : S → Λ) ⬝ᵥ r = 0
      rw [dotProduct_comm, dotProductEquiv_symm_dot]
      change ψ (Submodule.Quotient.mk 1) = 0
      have h1 : (Submodule.Quotient.mk (1 : S → Λ) : (S → Λ) ⧸ constSub S Λ) = 0 :=
        (Submodule.Quotient.mk_eq_zero _).2 (Submodule.mem_span_singleton_self _)
      rw [h1, map_zero]
    refine ⟨⟨r, hr⟩, ?_⟩
    refine Submodule.linearMap_qext _ (LinearMap.ext fun m => ?_)
    change m ⬝ᵥ r = ψ (Submodule.Quotient.mk m)
    rw [dotProduct_comm, dotProductEquiv_symm_dot]
    rfl

end Residue

end CupDuality
end RamanujanPetersson

end

-- ===== S4.Def_RP_HattoriStallings_Core =====
section

/-!
# Hattori–Stallings traces over `R[G]` (unit S4-HattoriStallings, part A: core)

A `R[G]`-module is a representation `ρ : Representation R G P` on a free finite `R`-module `P`.
Projectivity over `R[G]` is expressed by Higman's criterion (`IsHigman ρ E`:
`∑ h, ρ h ∘ E ∘ ρ h⁻¹ = id`). The Hattori–Stallings trace of an equivariant `φ` is the class function
`hs ρ φ c = ∑_{g ∈ c} Tr_R (ρ g⁻¹ ∘ φ ∘ E)`; it is independent of `E` and is the vector of class-sum
coordinates of the classical HS trace in `R[G]/[R[G], R[G]]`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson.HattoriStallings

open LinearMap

section ClassSum

variable {R : Type*} [CommRing R] {G : Type*} [Group G] [Fintype G]

open Classical in
/-- Class sums: `classSum a c = ∑_{g ∈ c} a g`. -/
noncomputable def classSum : (G → R) →ₗ[R] (ConjClasses G → R) where
  toFun a c := ∑ g : G, if ConjClasses.mk g = c then a g else 0
  map_add' a b := by
    funext c
    simp only [Pi.add_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun g _ => ?_
    split_ifs <;> simp
  map_smul' r a := by
    funext c
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    split_ifs <;> simp

open Classical in
lemma classSum_apply (a : G → R) (c : ConjClasses G) :
    classSum a c = ∑ g : G, if ConjClasses.mk g = c then a g else 0 := rfl

lemma mk_conj (h g : G) : ConjClasses.mk (h * g * h⁻¹) = ConjClasses.mk g :=
  (ConjClasses.mk_eq_mk_iff_isConj.2 (isConj_iff.2 ⟨h, rfl⟩)).symm

lemma classSum_conj (a : G → R) (h : G) : classSum (fun g => a (h * g * h⁻¹)) = classSum a := by
  funext c
  rw [classSum_apply, classSum_apply]
  refine Fintype.sum_equiv (MulAut.conj h).toEquiv _ _ (fun g => ?_)
  by_cases hg : ConjClasses.mk g = c
  · rw [if_pos hg]
    exact (if_pos (show ConjClasses.mk ((MulAut.conj h).toEquiv g) = c from
      (mk_conj h g).trans hg)).symm
  · rw [if_neg hg]
    exact (if_neg (show ¬ ConjClasses.mk ((MulAut.conj h).toEquiv g) = c from
      fun h' => hg ((mk_conj h g).symm.trans h'))).symm

/-- Pairing a function with a class function through class sums. -/
lemma sum_mul_eq_sum_classSum (a b : G → R) (χ : ConjClasses G → R)
    (hχ : ∀ g, χ (ConjClasses.mk g) = b g) [Fintype (ConjClasses G)] :
    ∑ g, a g * b g = ∑ c, classSum a c * χ c := by
  classical
  simp only [classSum_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Finset.sum_eq_single (ConjClasses.mk g)]
  · simp [hχ]
  · intro c _ hc; simp [Ne.symm hc]
  · simp

end ClassSum

section Higman

variable {R : Type*} [CommRing R] {G : Type*} [Group G] [Fintype G]
variable {P : Type*} [AddCommGroup P] [Module R P] {Q : Type*} [AddCommGroup Q] [Module R Q]
variable {T : Type*} [AddCommGroup T] [Module R T]

/-- Higman datum: `∑ h, ρ h ∘ E ∘ ρ h⁻¹ = id`. -/
def IsHigman (ρ : Representation R G P) (E : P →ₗ[R] P) : Prop :=
  ∑ h : G, ρ h ∘ₗ E ∘ₗ ρ h⁻¹ = LinearMap.id

/-- Projective over `R[G]` (Higman's criterion). -/
def IsProj (ρ : Representation R G P) : Prop := ∃ E : P →ₗ[R] P, IsHigman ρ E

/-- `G`-equivariant linear maps. -/
def IsEquivariant (ρ : Representation R G P) (σ : Representation R G Q) (f : P →ₗ[R] Q) : Prop :=
  ∀ g : G, f ∘ₗ ρ g = σ g ∘ₗ f

variable {ρ : Representation R G P} {σ : Representation R G Q} {τ : Representation R G T}

lemma IsEquivariant.apply {f : P →ₗ[R] Q} (hf : IsEquivariant ρ σ f) (g : G) (x : P) :
    f (ρ g x) = σ g (f x) := LinearMap.congr_fun (hf g) x

lemma isEquivariant_iff {f : P →ₗ[R] Q} :
    IsEquivariant ρ σ f ↔ ∀ g x, f (ρ g x) = σ g (f x) :=
  ⟨fun h => h.apply, fun h g => LinearMap.ext fun x => h g x⟩

lemma isEquivariant_id : IsEquivariant ρ ρ LinearMap.id := fun _ => by
  rw [LinearMap.id_comp, LinearMap.comp_id]

lemma IsEquivariant.comp {f : P →ₗ[R] Q} {g : Q →ₗ[R] T} (hg : IsEquivariant σ τ g)
    (hf : IsEquivariant ρ σ f) : IsEquivariant ρ τ (g ∘ₗ f) :=
  isEquivariant_iff.2 fun x v => by simp [hf.apply, hg.apply]

lemma IsEquivariant.add {f f' : P →ₗ[R] Q} (hf : IsEquivariant ρ σ f) (hf' : IsEquivariant ρ σ f') :
    IsEquivariant ρ σ (f + f') :=
  isEquivariant_iff.2 fun x v => by simp [hf.apply, hf'.apply]

lemma IsEquivariant.neg {f : P →ₗ[R] Q} (hf : IsEquivariant ρ σ f) : IsEquivariant ρ σ (-f) :=
  isEquivariant_iff.2 fun x v => by simp [hf.apply]

lemma IsEquivariant.sub {f f' : P →ₗ[R] Q} (hf : IsEquivariant ρ σ f) (hf' : IsEquivariant ρ σ f') :
    IsEquivariant ρ σ (f - f') :=
  isEquivariant_iff.2 fun x v => by simp [hf.apply, hf'.apply]

lemma IsEquivariant.smul {f : P →ₗ[R] Q} (r : R) (hf : IsEquivariant ρ σ f) :
    IsEquivariant ρ σ (r • f) :=
  isEquivariant_iff.2 fun x v => by simp [hf.apply]

lemma isEquivariant_zero : IsEquivariant ρ σ (0 : P →ₗ[R] Q) :=
  isEquivariant_iff.2 fun x v => by simp

lemma rep_apply_apply (ρ : Representation R G P) (a b : G) (x : P) :
    ρ a (ρ b x) = ρ (a * b) x := by
  rw [map_mul]; rfl

lemma rep_inv_apply_apply (ρ : Representation R G P) (a : G) (x : P) : ρ a⁻¹ (ρ a x) = x := by
  rw [rep_apply_apply, inv_mul_cancel, map_one]; rfl

lemma rep_apply_inv_apply (ρ : Representation R G P) (a : G) (x : P) : ρ a (ρ a⁻¹ x) = x := by
  rw [rep_apply_apply, mul_inv_cancel, map_one]; rfl

lemma IsHigman.apply {E : P →ₗ[R] P} (hE : IsHigman ρ E) (x : P) :
    ∑ h : G, ρ h (E (ρ h⁻¹ x)) = x := by
  have := LinearMap.congr_fun hE x
  simpa [LinearMap.sum_apply] using this

lemma IsHigman.apply_inv {E : P →ₗ[R] P} (hE : IsHigman ρ E) (x : P) :
    ∑ h : G, ρ h⁻¹ (E (ρ h x)) = x := by
  conv_rhs => rw [← hE.apply x]
  exact Fintype.sum_equiv (Equiv.inv G) _ _ (fun h => by simp)

/-- The HS density `g ↦ Tr_R (ρ g⁻¹ ∘ φ ∘ E)`. -/
noncomputable def hsFun (ρ : Representation R G P) (E φ : P →ₗ[R] P) (g : G) : R :=
  LinearMap.trace R P (ρ g⁻¹ ∘ₗ φ ∘ₗ E)

lemma hsFun_add (E φ ψ : P →ₗ[R] P) : hsFun ρ E (φ + ψ) = hsFun ρ E φ + hsFun ρ E ψ := by
  funext g; simp [hsFun, LinearMap.comp_add, LinearMap.add_comp]

lemma hsFun_smul (E φ : P →ₗ[R] P) (r : R) : hsFun ρ E (r • φ) = r • hsFun ρ E φ := by
  funext g; simp [hsFun, LinearMap.comp_smul, LinearMap.smul_comp]

lemma hsFun_neg (E φ : P →ₗ[R] P) : hsFun ρ E (-φ) = -hsFun ρ E φ := by
  funext g; simp [hsFun, LinearMap.comp_neg, LinearMap.neg_comp]

variable [Module.Free R P] [Module.Finite R P] [Module.Free R Q] [Module.Finite R Q]

/-- The cross trace property, the heart of the theory. -/
theorem classSum_hsFun_comp_comm {EP : P →ₗ[R] P} {EQ : Q →ₗ[R] Q}
    (hP : IsHigman ρ EP) (hQ : IsHigman σ EQ) (f : P →ₗ[R] Q) (g : Q →ₗ[R] P)
    (hf : IsEquivariant ρ σ f) (hg : IsEquivariant σ ρ g) :
    classSum (hsFun ρ EP (g ∘ₗ f)) = classSum (hsFun σ EQ (f ∘ₗ g)) := by
  set F : G → G → R := fun h y =>
    LinearMap.trace R Q (f ∘ₗ (ρ h⁻¹ ∘ₗ EP ∘ₗ ρ h) ∘ₗ ρ y⁻¹ ∘ₗ g ∘ₗ EQ) with hF
  have step1 : ∀ x : G, hsFun ρ EP (g ∘ₗ f) x = ∑ h : G, F h (h⁻¹ * x * h) := by
    intro x
    have hsplit : ρ x⁻¹ ∘ₗ (g ∘ₗ f) ∘ₗ EP
        = ∑ h : G, (ρ x⁻¹ ∘ₗ g ∘ₗ σ h ∘ₗ EQ) ∘ₗ (σ h⁻¹ ∘ₗ f ∘ₗ EP) := by
      ext v
      have := hQ.apply (f (EP v))
      simp only [LinearMap.comp_apply, LinearMap.sum_apply]
      conv_lhs => rw [← this]
      simp [map_sum]
    simp only [hsFun]
    rw [hsplit, map_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [LinearMap.trace_comp_comm']
    simp only [hF]
    congr 1
    ext v
    simp only [LinearMap.comp_apply]
    rw [← hf.apply, hg.apply, rep_apply_apply, rep_apply_apply,
      show h * (h⁻¹ * x * h)⁻¹ = x⁻¹ * h by group]
  have step2 : classSum (hsFun ρ EP (g ∘ₗ f)) = ∑ h : G, classSum (F h) := by
    have e : hsFun ρ EP (g ∘ₗ f) = ∑ h : G, (fun x => F h (h⁻¹ * x * h)) := by
      funext x; rw [step1 x, Finset.sum_apply]
    rw [e, map_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    have := classSum_conj (F h) h⁻¹
    simpa [inv_inv] using this
  have step3 : ∀ y, ∑ h : G, F h y = hsFun σ EQ (f ∘ₗ g) y := by
    intro y
    simp only [hF, hsFun]
    rw [← map_sum]
    congr 1
    ext v
    have := hP.apply_inv (ρ y⁻¹ (g (EQ v)))
    simp only [LinearMap.sum_apply, LinearMap.comp_apply]
    rw [← map_sum f, this, hf.apply]
  rw [step2, ← map_sum]
  congr 1
  funext y
  rw [Finset.sum_apply]
  exact step3 y

open Classical in
/-- The Hattori–Stallings trace (class-sum coordinates), `0` if `ρ` is not projective. -/
noncomputable def hs (ρ : Representation R G P) (φ : P →ₗ[R] P) : ConjClasses G → R :=
  if h : IsProj ρ then classSum (hsFun ρ h.choose φ) else 0

/-- `hs` is computed by ANY Higman datum. -/
theorem hs_eq {E : P →ₗ[R] P} (hE : IsHigman ρ E) {φ : P →ₗ[R] P} (hφ : IsEquivariant ρ ρ φ) :
    hs ρ φ = classSum (hsFun ρ E φ) := by
  have hp : IsProj ρ := ⟨E, hE⟩
  rw [hs, dif_pos hp]
  have := classSum_hsFun_comp_comm hp.choose_spec hE LinearMap.id φ isEquivariant_id hφ
  simpa using this

/-- Trace property across two projective representations. -/
theorem hs_comp_comm (hρ : IsProj ρ) (hσ : IsProj σ) (f : P →ₗ[R] Q) (g : Q →ₗ[R] P)
    (hf : IsEquivariant ρ σ f) (hg : IsEquivariant σ ρ g) :
    hs ρ (g ∘ₗ f) = hs σ (f ∘ₗ g) := by
  obtain ⟨EP, hP⟩ := hρ
  obtain ⟨EQ, hQ⟩ := hσ
  rw [hs_eq hP (hg.comp hf), hs_eq hQ (hf.comp hg)]
  exact classSum_hsFun_comp_comm hP hQ f g hf hg

theorem hs_add (hρ : IsProj ρ) {φ ψ : P →ₗ[R] P} (hφ : IsEquivariant ρ ρ φ)
    (hψ : IsEquivariant ρ ρ ψ) : hs ρ (φ + ψ) = hs ρ φ + hs ρ ψ := by
  obtain ⟨E, hE⟩ := hρ
  rw [hs_eq hE (hφ.add hψ), hs_eq hE hφ, hs_eq hE hψ, hsFun_add, map_add]

theorem hs_smul (hρ : IsProj ρ) {φ : P →ₗ[R] P} (hφ : IsEquivariant ρ ρ φ) (r : R) :
    hs ρ (r • φ) = r • hs ρ φ := by
  obtain ⟨E, hE⟩ := hρ
  rw [hs_eq hE (hφ.smul r), hs_eq hE hφ, hsFun_smul, map_smul]

theorem hs_neg (hρ : IsProj ρ) {φ : P →ₗ[R] P} (hφ : IsEquivariant ρ ρ φ) :
    hs ρ (-φ) = -hs ρ φ := by
  obtain ⟨E, hE⟩ := hρ
  rw [hs_eq hE hφ.neg, hs_eq hE hφ, hsFun_neg, map_neg]

theorem hs_sub (hρ : IsProj ρ) {φ ψ : P →ₗ[R] P} (hφ : IsEquivariant ρ ρ φ)
    (hψ : IsEquivariant ρ ρ ψ) : hs ρ (φ - ψ) = hs ρ φ - hs ρ ψ := by
  rw [sub_eq_add_neg, hs_add hρ hφ hψ.neg, hs_neg hρ hψ, ← sub_eq_add_neg]

theorem hs_zero (hρ : IsProj ρ) : hs ρ (0 : P →ₗ[R] P) = 0 := by
  have := hs_smul hρ (isEquivariant_id (ρ := ρ)) 0
  simpa using this

end Higman

end RamanujanPetersson.HattoriStallings

end

-- ===== S4.Def_RP_PerfectCx_CxAlg =====
section

/-!
# S4-PD (5), E3 algebra: products, coinvariants of products, and the right regular module

* `repPi`: the pointwise representation on a dependent product; `isProj_prod`, `isProj_pi`;
* `coinvProd`, `coinvPi`: `((P × Q) ⊗ M)_G ≃ (P ⊗ M)_G × (Q ⊗ M)_G` and the same for finite products;
* `rRep`: `Gf` acting on `k[Gf]` by right multiplication by `h⁻¹`; `isProj_rRep`; balancedness `mk_mul_tmul`;
  `coinvA : (k[Gf] ⊗ M)_{Gf} ≃ M`, `⟦a ⊗ m⟧ ↦ a · m`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace PerfectCx

open MonoidAlgebra TensorProduct HattoriStallings Representation

noncomputable section

section Gen

variable {k : Type} [CommRing k] {Gf : Type} [Group Gf]

/-- The pointwise representation on a dependent product. -/
def repPi {ι : Type} {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
    (σ : ∀ i, Representation k Gf (V i)) : Representation k Gf (∀ i, V i) where
  toFun g := LinearMap.piMap fun i => σ i g
  map_one' := by
    refine LinearMap.ext fun f => funext fun i => ?_
    show σ i 1 (f i) = f i
    rw [map_one, Module.End.one_apply]
  map_mul' x y := by
    refine LinearMap.ext fun f => funext fun i => ?_
    show σ i (x * y) (f i) = σ i x (σ i y (f i))
    rw [map_mul, Module.End.mul_apply]

theorem repPi_apply {ι : Type} {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
    (σ : ∀ i, Representation k Gf (V i)) (g : Gf) (f : ∀ i, V i) (i : ι) :
    repPi σ g f i = σ i g (f i) := rfl

theorem isProj_pi [Fintype Gf] {ι : Type} {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
    {σ : ∀ i, Representation k Gf (V i)} (h : ∀ i, IsProj (σ i)) : IsProj (repPi σ) := by
  have h' : ∀ i, ∃ E : V i →ₗ[k] V i, IsHigman (σ i) E := h
  choose E hE using h'
  refine ⟨LinearMap.piMap E, LinearMap.ext fun f => funext fun i => ?_⟩
  rw [LinearMap.sum_apply, Finset.sum_apply]
  exact (hE i).apply (f i)

theorem isProj_prod [Fintype Gf] {P Q : Type} [AddCommGroup P] [Module k P] [AddCommGroup Q] [Module k Q]
    {ρ : Representation k Gf P} {σ : Representation k Gf Q} (hρ : IsProj ρ) (hσ : IsProj σ) :
    IsProj (ρ.prod σ) := by
  obtain ⟨E, hE⟩ := hρ
  obtain ⟨F, hF⟩ := hσ
  refine ⟨E.prodMap F, LinearMap.ext fun x => ?_⟩
  rw [LinearMap.sum_apply]
  refine Prod.ext ?_ ?_
  · rw [Prod.fst_sum]; exact hE.apply x.1
  · rw [Prod.snd_sum]; exact hF.apply x.2

variable {M : Type} [AddCommGroup M] [Module k M] (τ : Representation k Gf M)

section Prod

variable {P Q : Type} [AddCommGroup P] [Module k P] [AddCommGroup Q] [Module k Q]
  (ρ : Representation k Gf P) (σ : Representation k Gf Q)

theorem inl_apply' (x : P) : IntertwiningMap.inl k ρ σ x = (x, 0) := rfl

theorem inr_apply' (y : Q) : IntertwiningMap.inr k ρ σ y = (0, y) := rfl

/-- `((P × Q) ⊗ M)_G ≃ (P ⊗ M)_G × (Q ⊗ M)_G`. -/
def coinvProd : Coinvariants ((ρ.prod σ).tprod τ) ≃ₗ[k] Coinvariants (ρ.tprod τ) × Coinvariants (σ.tprod τ) :=
  LinearEquiv.ofLinearMap
    ((Coinvariants.map _ _ ((IntertwiningMap.fst k ρ σ).rTensor τ)).prod
      (Coinvariants.map _ _ ((IntertwiningMap.snd k ρ σ).rTensor τ)))
    ((Coinvariants.map _ _ ((IntertwiningMap.inl k ρ σ).rTensor τ)).coprod
      (Coinvariants.map _ _ ((IntertwiningMap.inr k ρ σ).rTensor τ)))
    (LinearMap.prod_ext
      (Coinvariants.hom_ext (TensorProduct.ext' fun x m => by
        simp only [LinearMap.comp_apply, LinearMap.inl_apply, LinearMap.coprod_apply, map_zero, add_zero,
          LinearMap.prod_apply, Function.prod_apply, Coinvariants.map_mk, IntertwiningMap.rTensor_apply, inl_apply',
          IntertwiningMap.fst_apply, IntertwiningMap.snd_apply, zero_tmul, LinearMap.id_apply]))
      (Coinvariants.hom_ext (TensorProduct.ext' fun x m => by
        simp only [LinearMap.comp_apply, LinearMap.inr_apply, LinearMap.coprod_apply, map_zero, zero_add,
          LinearMap.prod_apply, Function.prod_apply, Coinvariants.map_mk, IntertwiningMap.rTensor_apply, inr_apply',
          IntertwiningMap.fst_apply, IntertwiningMap.snd_apply, zero_tmul, LinearMap.id_apply])))
    (Coinvariants.hom_ext (TensorProduct.ext' fun x m => by
      simp only [LinearMap.comp_apply, LinearMap.coprod_apply, LinearMap.prod_apply, Function.prod_apply, Coinvariants.map_mk,
        IntertwiningMap.rTensor_apply, IntertwiningMap.fst_apply, IntertwiningMap.snd_apply, inl_apply',
        inr_apply', LinearMap.id_apply]
      rw [← map_add, ← add_tmul, Prod.mk_add_mk, add_zero, zero_add]))

theorem coinvProd_mk_tmul (x : P × Q) (m : M) :
    coinvProd τ ρ σ (Coinvariants.mk _ (x ⊗ₜ m)) =
      (Coinvariants.mk _ (x.1 ⊗ₜ m), Coinvariants.mk _ (x.2 ⊗ₜ m)) := rfl

end Prod

section Pi

variable {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
  (σ : ∀ i, Representation k Gf (V i))

/-- The `i`-th projection as an intertwining map. -/
def projI (i : ι) : IntertwiningMap (repPi σ) (σ i) :=
  ⟨LinearMap.proj i, fun _ => LinearMap.ext fun _ => rfl⟩

/-- The `i`-th inclusion as an intertwining map. -/
def singleI (i : ι) : IntertwiningMap (σ i) (repPi σ) :=
  ⟨LinearMap.single k V i, fun g => LinearMap.ext fun v => funext fun j => by
    by_cases h : j = i
    · subst h
      simp [repPi_apply]
    · simp [repPi_apply, Pi.single_eq_of_ne h]⟩

theorem projI_apply (i : ι) (f : ∀ i, V i) : projI σ i f = f i := rfl

theorem singleI_apply (i : ι) (v : V i) : singleI σ i v = Pi.single i v := rfl

/-- Forward map of `coinvPi`. -/
def piFwd : Coinvariants ((repPi σ).tprod τ) →ₗ[k] ∀ i, Coinvariants ((σ i).tprod τ) :=
  LinearMap.pi fun i => Coinvariants.map _ _ ((projI σ i).rTensor τ)

/-- Inverse map of `coinvPi`. -/
def piInv : (∀ i, Coinvariants ((σ i).tprod τ)) →ₗ[k] Coinvariants ((repPi σ).tprod τ) :=
  ∑ i, Coinvariants.map _ _ ((singleI σ i).rTensor τ) ∘ₗ LinearMap.proj i

theorem piFwd_mk (x : ∀ i, V i) (m : M) (j : ι) :
    piFwd τ σ (Coinvariants.mk _ (x ⊗ₜ m)) j = Coinvariants.mk _ (x j ⊗ₜ m) := rfl

theorem piInv_apply (y : ∀ i, Coinvariants ((σ i).tprod τ)) :
    piInv τ σ y = ∑ i, Coinvariants.map _ _ ((singleI σ i).rTensor τ) (y i) := by
  simp only [piInv, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]

theorem piInv_single (i : ι) (y : Coinvariants ((σ i).tprod τ)) :
    piInv τ σ (Pi.single i y) = Coinvariants.map _ _ ((singleI σ i).rTensor τ) y := by
  rw [piInv_apply, Finset.sum_eq_single i (fun l _ hl => by rw [Pi.single_eq_of_ne hl, map_zero])
    (fun hi => absurd (Finset.mem_univ i) hi), Pi.single_eq_same]

/-- `((Π_i V_i) ⊗ M)_G ≃ Π_i (V_i ⊗ M)_G` for finite `ι`. -/
def coinvPi : Coinvariants ((repPi σ).tprod τ) ≃ₗ[k] ∀ i, Coinvariants ((σ i).tprod τ) :=
  LinearEquiv.ofLinearMap (piFwd τ σ) (piInv τ σ)
    (LinearMap.pi_ext' fun i => Coinvariants.hom_ext (TensorProduct.ext' fun v m => funext fun j => by
      show piFwd τ σ (piInv τ σ (Pi.single i (Coinvariants.mk _ (v ⊗ₜ m)))) j =
        Pi.single (M := fun i => Coinvariants ((σ i).tprod τ)) i (Coinvariants.mk _ (v ⊗ₜ m)) j
      rw [piInv_single, Coinvariants.map_mk, IntertwiningMap.rTensor_apply, singleI_apply, piFwd_mk]
      by_cases h : j = i
      · subst h
        rw [Pi.single_eq_same, Pi.single_eq_same]
      · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, zero_tmul, map_zero]))
    (Coinvariants.hom_ext (TensorProduct.ext' fun x m => by
      show piInv τ σ (piFwd τ σ (Coinvariants.mk _ (x ⊗ₜ m))) = Coinvariants.mk _ (x ⊗ₜ m)
      rw [piInv_apply]
      simp only [piFwd_mk, Coinvariants.map_mk, IntertwiningMap.rTensor_apply, singleI_apply]
      rw [← map_sum, ← TensorProduct.sum_tmul, Finset.univ_sum_single]))

theorem coinvPi_mk_tmul (x : ∀ i, V i) (m : M) (i : ι) :
    coinvPi τ σ (Coinvariants.mk _ (x ⊗ₜ m)) i = Coinvariants.mk _ (x i ⊗ₜ m) := rfl

end Pi

end Gen

section Right

variable (k : Type) [CommRing k] (Gf : Type) [Group Gf]

/-- `Gf` acting on `k[Gf]` by right multiplication by `h⁻¹`. -/
def rRep : Representation k Gf (MonoidAlgebra k Gf) where
  toFun h := LinearMap.mulRight k (single h⁻¹ 1)
  map_one' := by
    refine LinearMap.ext fun a => ?_
    show a * single 1⁻¹ 1 = a
    rw [inv_one, ← one_def, mul_one]
  map_mul' x y := by
    refine LinearMap.ext fun a => ?_
    show a * single (x * y)⁻¹ 1 = a * single y⁻¹ 1 * single x⁻¹ 1
    rw [mul_assoc, single_mul_single, mul_inv_rev, one_mul]

variable {k Gf}

theorem rRep_apply (h : Gf) (a : MonoidAlgebra k Gf) : rRep k Gf h a = a * single h⁻¹ 1 := rfl

/-- `a ↦ a(1) · 1`. -/
def e1 : MonoidAlgebra k Gf →ₗ[k] MonoidAlgebra k Gf where
  toFun a := single 1 (a.coeff 1)
  map_add' a b := by rw [coeff_add, Finsupp.add_apply, single_add]
  map_smul' r a := by simp only [coeff_smul_apply, smul_single, RingHom.id_apply]

theorem e1_apply (a : MonoidAlgebra k Gf) : e1 a = single 1 (a.coeff 1) := rfl

/-- The free rank-one module `k[Gf]` is projective. -/
theorem isProj_rRep [Fintype Gf] : IsProj (rRep k Gf) := by
  classical
  refine ⟨e1, LinearMap.ext fun a => ?_⟩
  rw [LinearMap.sum_apply]
  ext y
  have hterm : ∀ h : Gf, (rRep k Gf h (e1 (rRep k Gf h⁻¹ a))).coeff y =
      if h⁻¹ = y then a.coeff h⁻¹ else 0 := fun h => by
    simp only [rRep_apply, e1_apply, inv_inv, coeff_mul_single_apply, one_mul, mul_one, single_mul_single,
      coeff_single, Finsupp.single_apply]
  have h0 : ∀ h ∈ (Finset.univ : Finset Gf), h ≠ y⁻¹ → (rRep k Gf h (e1 (rRep k Gf h⁻¹ a))).coeff y = 0 :=
    fun h _ hh => by rw [hterm, if_neg fun h' => hh (by rw [← h', inv_inv])]
  simp only [LinearMap.comp_apply, LinearMap.id_apply, coeff_sum, Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single y⁻¹ h0 (fun hh => absurd (Finset.mem_univ _) hh), hterm, inv_inv, if_pos rfl]

variable {M : Type} [AddCommGroup M] [Module k M] (τ : Representation k Gf M)

/-- Balancedness: `⟦(b a) ⊗ m⟧ = ⟦b ⊗ (a · m)⟧` in `(k[Gf] ⊗ M)_{Gf}`. -/
theorem mk_mul_tmul (b a : MonoidAlgebra k Gf) (m : M) :
    Coinvariants.mk ((rRep k Gf).tprod τ) ((b * a) ⊗ₜ m) =
      Coinvariants.mk ((rRep k Gf).tprod τ) (b ⊗ₜ τ.asAlgebraHom a m) := by
  induction a using MonoidAlgebra.induction_on with
  | of x =>
    rw [Representation.asAlgebraHom_of, of_apply]
    have hb : b * single x 1 = rRep k Gf x⁻¹ b := by rw [rRep_apply, inv_inv]
    rw [hb, Coinvariants.mk_inv_tmul]
  | add a a' ha ha' => simp only [mul_add, add_tmul, map_add, ha, ha', LinearMap.add_apply, tmul_add]
  | smul r a ha => simp only [mul_smul_comm, ← smul_tmul', map_smul, ha, LinearMap.smul_apply, tmul_smul]

theorem lift_rRep_inv (h : Gf) :
    TensorProduct.lift τ.asAlgebraHom.toLinearMap ∘ₗ ((rRep k Gf).tprod τ) h =
      TensorProduct.lift τ.asAlgebraHom.toLinearMap := by
  refine TensorProduct.ext' fun a m => ?_
  have hinv : τ h⁻¹ (τ h m) = m := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  rw [LinearMap.comp_apply, Representation.tprod_apply, TensorProduct.map_tmul, TensorProduct.lift.tmul,
    TensorProduct.lift.tmul, AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply, rRep_apply, map_mul,
    Module.End.mul_apply, Representation.asAlgebraHom_single_one, hinv]

/-- `(k[Gf] ⊗ M)_{Gf} ≃ M`, `⟦a ⊗ m⟧ ↦ a · m`. -/
def coinvA : Coinvariants ((rRep k Gf).tprod τ) ≃ₗ[k] M :=
  LinearEquiv.ofLinearMap
    (Coinvariants.lift _ (TensorProduct.lift τ.asAlgebraHom.toLinearMap) (lift_rRep_inv τ))
    (Coinvariants.mk _ ∘ₗ TensorProduct.mk k (MonoidAlgebra k Gf) M 1)
    (LinearMap.ext fun m => by
      show τ.asAlgebraHom 1 m = m
      rw [map_one, Module.End.one_apply])
    (Coinvariants.hom_ext (TensorProduct.ext' fun a m => by
      show Coinvariants.mk _ ((1 : MonoidAlgebra k Gf) ⊗ₜ τ.asAlgebraHom a m) = Coinvariants.mk _ (a ⊗ₜ m)
      rw [← mk_mul_tmul, one_mul]))

theorem coinvA_mk_tmul (a : MonoidAlgebra k Gf) (m : M) :
    coinvA τ (Coinvariants.mk _ (a ⊗ₜ m)) = τ.asAlgebraHom a m := rfl

theorem coinvA_symm_apply (m : M) :
    (coinvA τ).symm m = Coinvariants.mk _ ((1 : MonoidAlgebra k Gf) ⊗ₜ m) := rfl

end Right

end

end PerfectCx
end RamanujanPetersson

end

-- ===== S4.Def_RP_CdOne_Lc =====
section

/-!
# S4-PD (3), group layer part 1: locally constant cochains and the index lemma

For a compact topological group `P` acting on `A` (locally constant action, `LcAct`):
* `lc_dite`, `lc_sum`, `lc_d₁`: closure properties of locally constant cochains;
* `exists_open_inv`: a locally constant function on `P × P` is invariant under right multiplication by an open
  subgroup in each variable (finite level); `exists_openNormal_le`, `actKer`, `isOpen_actKer`;
* `index_lemma`: for an open subgroup `H` whose index is invertible on `A`, a locally constant 2-cocycle whose
  restriction to `H × H` is the coboundary of a locally constant cochain is a locally constant coboundary on `P`
  (normalise to `f(g, n) = 0` for `n ∈ H`, then average over the left cosets `P ⧸ H`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson.CdOne

open groupCohomology Filter Topology

section LcBasic

variable {X : Type*} [TopologicalSpace X]

/-- Extension by zero from a clopen set is locally constant. -/
theorem lc_dite {S : Set X} [DecidablePred (· ∈ S)] (hS : IsClopen S) {Z : Type*} [Zero Z] (u : S → Z)
    (hu : IsLocallyConstant u) :
    IsLocallyConstant (fun x => if h : x ∈ S then u ⟨x, h⟩ else 0) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  by_cases hx : x ∈ S
  · have h1 : ∀ᶠ y in 𝓝 x, y ∈ S := hS.isOpen.mem_nhds hx
    have h2 : ∀ᶠ (y' : S) in 𝓝 ⟨x, hx⟩, ∀ h : y'.1 ∈ S, u ⟨y'.1, h⟩ = u ⟨x, hx⟩ := by
      filter_upwards [(IsLocallyConstant.iff_eventually_eq u).1 hu ⟨x, hx⟩] with y' hy' h
      exact hy'
    have h3 : ∀ᶠ y in 𝓝 x, ∀ h : y ∈ S, u ⟨y, h⟩ = u ⟨x, hx⟩ := by
      rw [← (hS.isOpen.isOpenEmbedding_subtypeVal).map_nhds_eq ⟨x, hx⟩]
      exact Filter.eventually_map.2 h2
    filter_upwards [h1, h3] with y hy hq
    rw [dif_pos hy, dif_pos hx]
    exact hq hy
  · have h1 : ∀ᶠ y in 𝓝 x, y ∉ S := hS.isClosed.isOpen_compl.mem_nhds hx
    filter_upwards [h1] with y hy
    rw [dif_neg hy, dif_neg hx]

/-- Finite sums of locally constant functions are locally constant. -/
theorem lc_sum {ι : Type*} [Fintype ι] {B : Type*} [AddCommMonoid B] (u : ι → X → B)
    (hu : ∀ i, IsLocallyConstant (u i)) : IsLocallyConstant (fun x => ∑ i, u i x) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have : ∀ᶠ y in 𝓝 x, ∀ i, u i y = u i x :=
    Filter.eventually_all.2 (fun i => (IsLocallyConstant.iff_eventually_eq _).1 (hu i) x)
  filter_upwards [this] with y hy
  exact Finset.sum_congr rfl (fun i _ => hy i)

end LcBasic

variable {P : Type*} [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
  {A : Type*} [AddCommGroup A] [DistribMulAction P A]

/-- `P` acts locally constantly on `A` (a continuous action on a discrete module). -/
def LcAct (P A : Type*) [Group P] [TopologicalSpace P] [AddCommGroup A] [DistribMulAction P A] : Prop :=
  ∀ a : A, IsLocallyConstant fun g : P => g • a

/-- `f` is the coboundary of a locally constant 1-cochain. -/
def IsLcCob (f : P × P → A) : Prop :=
  ∃ b : P → A, IsLocallyConstant b ∧ ∀ g h : P, f (g, h) = d₁ b (g, h)

theorem smul_zsmul' (g : P) (x : ℤ) (a : A) : g • (x • a) = x • (g • a) :=
  map_zsmul (DistribSMul.toAddMonoidHom A g) x a

theorem lc_smul_comp (hact : LcAct P A) {b : P → A} (hb : IsLocallyConstant b) :
    IsLocallyConstant fun p : P × P => p.1 • b p.2 := by
  rw [IsLocallyConstant.iff_eventually_eq]
  rintro ⟨g, h⟩
  have h1 := (IsLocallyConstant.iff_eventually_eq _).1 (hact (b h)) g
  have h2 := (IsLocallyConstant.iff_eventually_eq _).1 hb h
  rw [nhds_prod_eq]
  filter_upwards [h1.prod_mk h2] with p hp
  rw [hp.2, hp.1]

theorem lc_d₁ (hact : LcAct P A) {b : P → A} (hb : IsLocallyConstant b) : IsLocallyConstant (d₁ b) := by
  have h1 := lc_smul_comp hact hb
  have h2 : IsLocallyConstant fun p : P × P => b (p.1 * p.2) := hb.comp_continuous continuous_mul
  have h3 : IsLocallyConstant fun p : P × P => b p.1 := hb.comp_continuous continuous_fst
  exact (h1.sub h2).add h3

/-- Finite level: a locally constant function on `P × P` (`P` compact) is invariant under right multiplication
by an open subgroup in each variable. -/
theorem exists_open_inv [CompactSpace P] {X : Type*} {f : P × P → X} (hf : IsLocallyConstant f) :
    ∃ W : Subgroup P, IsOpen (W : Set P) ∧
      ∀ x ∈ W, ∀ g h : P, f (g * x, h) = f (g, h) ∧ f (g, h * x) = f (g, h) := by
  let W : Subgroup P :=
    { carrier := {x | ∀ g h : P, f (g * x, h) = f (g, h) ∧ f (g, h * x) = f (g, h)}
      one_mem' := by intro g h; simp
      mul_mem' := fun {x y} hx hy g h => by
        refine ⟨?_, ?_⟩
        · rw [← mul_assoc, (hy (g * x) h).1, (hx g h).1]
        · rw [← mul_assoc, (hy g (h * x)).2, (hx g h).2]
      inv_mem' := fun {x} hx g h => by
        refine ⟨?_, ?_⟩
        · have := (hx (g * x⁻¹) h).1
          rw [inv_mul_cancel_right] at this
          exact this.symm
        · have := (hx g (h * x⁻¹)).2
          rw [inv_mul_cancel_right] at this
          exact this.symm }
  refine ⟨W, W.isOpen_of_mem_nhds (g := 1) ?_, fun x hx => hx⟩
  have hK := (isCompact_univ : IsCompact (Set.univ : Set (P × P))).eventually_forall_of_forall_eventually
    (x₀ := (1 : P)) (P := fun x y => f (y.1 * x, y.2) = f y ∧ f (y.1, y.2 * x) = f y) ?_
  · filter_upwards [hK] with x hx
    exact fun g h => hx (g, h) (Set.mem_univ _)
  · rintro ⟨g, h⟩ -
    have hf' := (IsLocallyConstant.iff_eventually_eq f).1 hf (g, h)
    have c1 : Continuous fun z : P × (P × P) => (z.2.1 * z.1, z.2.2) := by fun_prop
    have c2 : Continuous fun z : P × (P × P) => (z.2.1, z.2.2 * z.1) := by fun_prop
    have e1 := (c1.tendsto' ((1 : P), (g, h)) (g, h) (by simp)).eventually hf'
    have e2 := (c2.tendsto' ((1 : P), (g, h)) (g, h) (by simp)).eventually hf'
    have e0 := (continuous_snd.tendsto' ((1 : P), (g, h)) (g, h) rfl).eventually hf'
    filter_upwards [e1, e2, e0] with z h1 h2 h0
    exact ⟨h1.trans h0.symm, h2.trans h0.symm⟩

/-- An open subgroup of a compact group contains an open normal subgroup. -/
theorem exists_openNormal_le [CompactSpace P] (W : Subgroup P) (hW : IsOpen (W : Set P)) :
    ∃ N : Subgroup P, N.Normal ∧ IsOpen (N : Set P) ∧ N ≤ W := by
  obtain ⟨N, hN⟩ := IsTopologicalGroup.exist_openNormalSubgroup_sub_clopen_nhds_of_one
    ⟨W.isClosed_of_isOpen hW, hW⟩ W.one_mem
  exact ⟨N.toSubgroup, N.isNormal', N.isOpen', fun x hx => hN hx⟩

/-- The kernel of the action. -/
def actKer (P A : Type*) [Group P] [AddCommGroup A] [DistribMulAction P A] : Subgroup P where
  carrier := {x | ∀ a : A, x • a = a}
  one_mem' := fun a => one_smul P a
  mul_mem' := fun {x y} hx hy a => by rw [mul_smul, hy, hx]
  inv_mem' := fun {x} hx a => by rw [inv_smul_eq_iff, hx]

theorem mem_actKer {x : P} : x ∈ actKer P A ↔ ∀ a : A, x • a = a := Iff.rfl

theorem isOpen_actKer [Finite A] (hact : LcAct P A) : IsOpen (actKer P A : Set P) := by
  refine (actKer P A).isOpen_of_mem_nhds (g := 1) ?_
  have : ∀ᶠ x in 𝓝 (1 : P), ∀ a : A, x • a = a := Filter.eventually_all.2 fun a => by
    filter_upwards [(IsLocallyConstant.iff_eventually_eq _).1 (hact a) 1] with x hx
    rw [hx, one_smul]
  exact this

/-! ## Coset representatives for a (not necessarily normal) subgroup -/

/-- A representative of the left coset `g H`. -/
noncomputable def crep (H : Subgroup P) (g : P) : P := (QuotientGroup.mk g : P ⧸ H).out

theorem crep_inv_mul_mem (H : Subgroup P) (g : P) : (crep H g)⁻¹ * g ∈ H :=
  QuotientGroup.eq.mp (QuotientGroup.out_eq' _)

theorem crep_eq_of_mem (H : Subgroup P) {g g' : P} (h : g⁻¹ * g' ∈ H) : crep H g = crep H g' := by
  unfold crep; rw [QuotientGroup.eq.mpr h]

theorem crep_mul_mem (H : Subgroup P) (g : P) {n : P} (hn : n ∈ H) : crep H (g * n) = crep H g :=
  crep_eq_of_mem H (by simpa [mul_assoc] using H.inv_mem hn)

theorem crep_mem_of_mem (H : Subgroup P) {n : P} (hn : n ∈ H) : crep H n ∈ H := by
  have h := H.mul_mem (crep_inv_mul_mem H n) (H.inv_mem hn)
  rw [mul_inv_cancel_right] at h
  simpa using H.inv_mem h

theorem lc_mk {H : Subgroup P} (hH : IsOpen (H : Set P)) :
    IsLocallyConstant (QuotientGroup.mk : P → P ⧸ H) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g
  have hc : Continuous fun y : P => g⁻¹ * y := continuous_const.mul continuous_id
  have : ∀ᶠ y in 𝓝 g, g⁻¹ * y ∈ H :=
    hc.continuousAt.eventually_mem (by rw [inv_mul_cancel]; exact hH.mem_nhds H.one_mem)
  filter_upwards [this] with y hy
  exact (QuotientGroup.eq.mpr hy).symm

theorem lc_crep {H : Subgroup P} (hH : IsOpen (H : Set P)) : IsLocallyConstant (crep H) :=
  (lc_mk hH).comp (fun q : P ⧸ H => q.out)

/-! ## The index lemma -/

theorem zero_right_aux (H : Subgroup P) {f : P × P → A} (hf : IsCocycle₂ f)
    (h0 : ∀ n ∈ H, ∀ n' ∈ H, f (n, n') = 0) :
    ∀ g, ∀ n ∈ H, (f - d₁ (fun g => -f (crep H g, (crep H g)⁻¹ * g))) (g, n) = 0 := by
  intro g n hn
  have hbn : f (crep H n, (crep H n)⁻¹ * n) = 0 :=
    h0 _ (crep_mem_of_mem H hn) _ (crep_inv_mul_mem H n)
  have hgn : crep H (g * n) = crep H g := crep_mul_mem H g hn
  have hc := hf (crep H g) ((crep H g)⁻¹ * g) n
  rw [mul_inv_cancel_left, h0 _ (crep_inv_mul_mem H g) _ hn, smul_zero, zero_add,
    mul_assoc ((crep H g)⁻¹) g n] at hc
  simp only [Pi.sub_apply, d₁_apply, hgn, hbn, neg_zero, smul_zero]
  rw [← hc]; abel

theorem right_inv (H : Subgroup P) {F : P × P → A} (hF : IsCocycle₂ F) (h0 : ∀ g, ∀ n ∈ H, F (g, n) = 0)
    (g x : P) {n : P} (hn : n ∈ H) : F (g, x * n) = F (g, x) := by
  have := hF g x n
  have e1 := h0 (g * x) n hn
  have e2 := h0 x n hn
  rw [e1, e2, smul_zero, zero_add, zero_add] at this
  exact this.symm

/-- **Index lemma.** `H` open of index invertible on `A`; if `f|H×H = d₁ β` with `β` locally constant, then `f` is
a locally constant coboundary on `P`. -/
theorem index_lemma [CompactSpace P] (hact : LcAct P A) (H : Subgroup P) (hH : IsOpen (H : Set P))
    (x : ℤ) (hx : ∀ a : A, (x * (H.index : ℤ)) • a = a)
    {f : P × P → A} (hf : IsLocallyConstant f) (hc : IsCocycle₂ f)
    (β : P → A) (hβ : IsLocallyConstant β) (hβH : ∀ h ∈ H, ∀ h' ∈ H, f (h, h') = d₁ β (h, h')) :
    IsLcCob f := by
  classical
  have : Finite (P ⧸ H) := H.quotient_finite_of_isOpen hH
  let _ : Fintype (P ⧸ H) := Fintype.ofFinite _
  obtain ⟨f₁, hf₁⟩ : ∃ f₁, f₁ = f - d₁ β := ⟨_, rfl⟩
  have hc₁ : IsCocycle₂ f₁ := by rw [hf₁]; exact isCocycle₂_sub_d₁ hc β
  have hl₁ : IsLocallyConstant f₁ := by rw [hf₁]; exact hf.sub (lc_d₁ hact hβ)
  have h0₁ : ∀ n ∈ H, ∀ n' ∈ H, f₁ (n, n') = 0 := fun n hn n' hn' => by
    rw [hf₁, Pi.sub_apply, hβH n hn n' hn', sub_self]
  obtain ⟨b₁, hb₁⟩ : ∃ b₁ : P → A, b₁ = fun g => -f₁ (crep H g, (crep H g)⁻¹ * g) := ⟨_, rfl⟩
  have hlb₁ : IsLocallyConstant b₁ := by
    rw [hb₁]
    have hcont : Continuous fun g : P => (crep H g, (crep H g)⁻¹ * g) :=
      (lc_crep hH).continuous.prodMk ((lc_crep hH).continuous.inv.mul continuous_id)
    exact (hl₁.comp_continuous hcont).comp (fun a => -a)
  obtain ⟨f₂, hf₂⟩ : ∃ f₂, f₂ = f₁ - d₁ b₁ := ⟨_, rfl⟩
  have hc₂ : IsCocycle₂ f₂ := by rw [hf₂]; exact isCocycle₂_sub_d₁ hc₁ b₁
  have h0₂ : ∀ g, ∀ n ∈ H, f₂ (g, n) = 0 := by rw [hf₂, hb₁]; exact zero_right_aux H hc₁ h0₁
  have hl₂ : IsLocallyConstant f₂ := by rw [hf₂]; exact hl₁.sub (lc_d₁ hact hlb₁)
  obtain ⟨F, hF⟩ : ∃ F : P → A, F = fun g => ∑ y : P ⧸ H, f₂ (g, y.out) := ⟨_, rfl⟩
  have hFg : ∀ g, ∑ y : P ⧸ H, f₂ (g, y.out) = F g := fun g => by rw [hF]
  have hlF : IsLocallyConstant F := by
    rw [hF]
    exact lc_sum (fun (y : P ⧸ H) (g : P) => f₂ (g, y.out))
      (fun y => hl₂.comp_continuous (continuous_id.prodMk continuous_const))
  have hperm : ∀ g h : P, ∑ y : P ⧸ H, f₂ (g, h * y.out) = F g := by
    intro g h
    rw [← hFg]
    have hstep : ∀ y : P ⧸ H, f₂ (g, h * y.out) = f₂ (g, (h • y).out) := by
      intro y
      have e : (QuotientGroup.mk (h * y.out) : P ⧸ H) = QuotientGroup.mk ((h • y).out) := by
        rw [QuotientGroup.out_eq', ← smul_eq_mul, ← MulAction.Quotient.smul_mk, QuotientGroup.out_eq']
      have hm := QuotientGroup.eq.mp e
      have := right_inv H hc₂ h0₂ g (h * y.out) hm
      rw [mul_inv_cancel_left] at this
      exact this.symm
    rw [Finset.sum_congr rfl (fun y _ => hstep y)]
    exact Fintype.sum_equiv (MulAction.toPerm h) _ _ (fun y => rfl)
  have key : ∀ g h : P, (H.index : ℤ) • f₂ (g, h) = g • F h - F (g * h) + F g := by
    intro g h
    have hs := Finset.sum_congr (rfl : (Finset.univ : Finset (P ⧸ H)) = Finset.univ)
      (fun y _ => hc₂ g h y.out)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.smul_sum, Finset.sum_const,
      Finset.card_univ, hperm, hFg, hFg] at hs
    rw [H.index_eq_card, Nat.card_eq_fintype_card, natCast_zsmul]
    exact eq_of_sub_eq hs (by abel)
  refine ⟨β + b₁ + x • F, ?_, fun g h => ?_⟩
  · have h3 : IsLocallyConstant (x • F) := hlF.comp (fun a : A => x • a)
    exact (hβ.add hlb₁).add h3
  · have e1 : f (g, h) = f₁ (g, h) + d₁ β (g, h) := by rw [hf₁, Pi.sub_apply, sub_add_cancel]
    have e2 : f₁ (g, h) = f₂ (g, h) + d₁ b₁ (g, h) := by rw [hf₂, Pi.sub_apply, sub_add_cancel]
    have e3 : f₂ (g, h) = x • (g • F h - F (g * h) + F g) := by
      rw [← key, ← mul_smul, hx]
    rw [e1, e2, e3, d₁_add, d₁_add]
    simp only [Pi.add_apply, d₁_apply, Pi.smul_apply, smul_add, smul_sub, smul_zsmul']
    abel

end RamanujanPetersson.CdOne

end

-- ===== S4.Def_RP_CdOne_Grp =====
section

/-!
# S4-PD (3), group layer part 2: Sylow reduction and `ℤ/l` coefficients

* `exists_inv_index`: an index prime to `l` is invertible on an `l`-primary module;
* `exists_sylow_open`: the preimage `H` of an `l`-Sylow of the finite quotient `P ⧸ N`;
* `HypL l P`: the hypothesis (Hl) supplied by the field layer (central embedding problems): `ℤ/l`-valued 2-cocycles
  with trivial action on an open subgroup `Q`, factoring through an `l`-group quotient `Q/N`, are locally constant
  coboundaries on `Q`;
* `trivial_coeff`: under `HypL`, every locally constant `ℤ/l`-valued 2-cocycle (trivial action) on `P` is a locally
  constant coboundary (finite level, Sylow, `index_lemma`);
* `hypL_subgroup`: `HypL` passes to open subgroups.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson.CdOne

open groupCohomology Filter Topology

theorem exists_inv_index {A : Type*} [AddCommGroup A] {l e m : ℕ} (hl : l.Prime) (hm : ¬ l ∣ m)
    (hA : ∀ a : A, (l ^ e) • a = 0) : ∃ x : ℤ, ∀ a : A, (x * m) • a = a := by
  have hcop : Nat.Coprime m (l ^ e) :=
    Nat.Coprime.pow_right e (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hl).mpr hm))
  obtain ⟨u, v, huv⟩ := Nat.Coprime.isCoprime hcop
  refine ⟨u, fun a => ?_⟩
  have h1 : (u * m : ℤ) = 1 - v * ((l ^ e : ℕ) : ℤ) := by rw [← huv]; ring
  rw [h1, sub_smul, one_smul, mul_smul, natCast_zsmul, hA, smul_zero, sub_zero]

/-- The trivial action (used only as a local instance). -/
def trivAct (P B : Type*) [Monoid P] [AddMonoid B] : DistribMulAction P B where
  smul _ a := a
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl

variable {P : Type*} [Group P] [TopologicalSpace P] [IsTopologicalGroup P]

/-- The preimage of an `l`-Sylow subgroup of the finite quotient `P ⧸ N`. -/
theorem exists_sylow_open [CompactSpace P] (l : ℕ) [Fact l.Prime] (N : Subgroup P) [N.Normal]
    (hN : IsOpen (N : Set P)) :
    ∃ H : Subgroup P, N ≤ H ∧ IsOpen (H : Set P) ∧ ¬ l ∣ H.index ∧ ∀ q ∈ H, ∃ k : ℕ, q ^ (l ^ k) ∈ N := by
  have : Finite (P ⧸ N) := N.quotient_finite_of_isOpen hN
  obtain ⟨S⟩ := (Sylow.nonempty : Nonempty (Sylow l (P ⧸ N)))
  have hNH : N ≤ (S : Subgroup (P ⧸ N)).comap (QuotientGroup.mk' N) := by
    intro n hn
    rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff n).mpr hn]
    exact one_mem _
  refine ⟨_, hNH, Subgroup.isOpen_mono hNH hN, ?_, ?_⟩
  · rw [Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective N)]
    exact S.not_dvd_index
  · intro q hq
    obtain ⟨k, hk⟩ := S.isPGroup' ⟨_, hq⟩
    refine ⟨k, (QuotientGroup.eq_one_iff _).mp ?_⟩
    have := congrArg Subtype.val hk
    simpa using this

/-- **(Hl)**: `ℤ/l`-valued 2-cocycles (trivial action) on an open subgroup `Q` that factor through an `l`-group
quotient `Q/N` are locally constant coboundaries on `Q`. Supplied by the field layer (Kummer theory over a C1 field). -/
def HypL (l : ℕ) (P : Type*) [Group P] [TopologicalSpace P] : Prop :=
  ∀ Q N : Subgroup P, IsOpen (Q : Set P) → IsOpen (N : Set P) → N ≤ Q →
    (∀ q ∈ Q, ∀ n ∈ N, q * n * q⁻¹ ∈ N) → (∀ q ∈ Q, ∃ k : ℕ, q ^ (l ^ k) ∈ N) →
    ∀ f : P × P → ZMod l, IsLocallyConstant f →
    (∀ g ∈ Q, ∀ h ∈ Q, ∀ j ∈ Q, f (g * h, j) + f (g, h) = f (h, j) + f (g, h * j)) →
    (∀ g ∈ Q, ∀ h ∈ Q, ∀ n ∈ N, ∀ n' ∈ N, f (g * n, h * n') = f (g, h)) →
    ∃ γ : P → ZMod l, IsLocallyConstant γ ∧ ∀ g ∈ Q, ∀ h ∈ Q, f (g, h) = γ h - γ (g * h) + γ g

/-- Under `HypL`, every locally constant `ℤ/l`-valued 2-cocycle with trivial action is a locally constant
coboundary. -/
theorem trivial_coeff [CompactSpace P] (l : ℕ) [hl : Fact l.Prime] (hL : HypL l P) {f : P × P → ZMod l}
    (hf : IsLocallyConstant f) (hc : ∀ g h j : P, f (g * h, j) + f (g, h) = f (h, j) + f (g, h * j)) :
    ∃ γ : P → ZMod l, IsLocallyConstant γ ∧ ∀ g h : P, f (g, h) = γ h - γ (g * h) + γ g := by
  obtain ⟨W, hWo, hW⟩ := exists_open_inv hf
  obtain ⟨N, hNn, hNo, hNW⟩ := exists_openNormal_le W hWo
  have := hNn
  obtain ⟨H, hNH, hHo, hl', hH⟩ := exists_sylow_open l N hNo
  obtain ⟨γ, hγ, hγH⟩ := hL H N hHo hNo hNH (fun q _ n hn => hNn.conj_mem n hn q) hH f hf
    (fun g _ h _ j _ => hc g h j)
    (fun g _ h _ n hn n' hn' => by rw [(hW n (hNW hn) g (h * n')).1, (hW n' (hNW hn') g h).2])
  letI : DistribMulAction P (ZMod l) := trivAct P (ZMod l)
  obtain ⟨x, hx⟩ := exists_inv_index (A := ZMod l) (e := 1) hl.out hl' (fun a => by simp)
  obtain ⟨b, hb, hfb⟩ := index_lemma (fun a => IsLocallyConstant.const a) H hHo x hx hf
    (fun g h j => hc g h j) γ hγ (fun h hh h' hh' => hγH h hh h' hh')
  exact ⟨b, hb, fun g h => hfb g h⟩

/-- `HypL` passes to open subgroups. -/
theorem hypL_subgroup (l : ℕ) (hL : HypL l P) (H : Subgroup P) (hH : IsOpen (H : Set P)) : HypL l H := by
  classical
  intro Q₁ N₁ hQ₁ hN₁ hNQ₁ hnorm hlg f₁ hf₁ hc₁ hinv₁
  have hemb := hH.isOpenEmbedding_subtypeVal
  have hopen : ∀ K : Subgroup H, IsOpen (K : Set H) → IsOpen ((K.map H.subtype : Subgroup P) : Set P) := by
    intro K hK
    rw [Subgroup.coe_map]
    exact hemb.isOpenMap _ hK
  let f : P × P → ZMod l := fun p =>
    if hp : p ∈ (H : Set P) ×ˢ (H : Set P) then f₁ (⟨p.1, hp.1⟩, ⟨p.2, hp.2⟩) else 0
  have hfv : ∀ a b : H, f ((a : P), (b : P)) = f₁ (a, b) := fun a b => by
    simp only [f, dif_pos (Set.mk_mem_prod a.2 b.2)]
  have hlf : IsLocallyConstant f := by
    have hc : IsClopen (H : Set P) := ⟨H.isClosed_of_isOpen hH, hH⟩
    refine lc_dite (hc.prod hc) (fun p => f₁ (⟨p.1.1, p.2.1⟩, ⟨p.1.2, p.2.2⟩)) ?_
    exact hf₁.comp_continuous
      (((continuous_fst.comp continuous_subtype_val).subtype_mk _).prodMk
        ((continuous_snd.comp continuous_subtype_val).subtype_mk _))
  have hnorm' : ∀ q ∈ Q₁.map H.subtype, ∀ n ∈ N₁.map H.subtype, q * n * q⁻¹ ∈ N₁.map H.subtype := by
    rintro _ ⟨q, hq, rfl⟩ _ ⟨n, hn, rfl⟩
    exact ⟨q * n * q⁻¹, hnorm q hq n hn, by simp⟩
  have hlg' : ∀ q ∈ Q₁.map H.subtype, ∃ k : ℕ, q ^ (l ^ k) ∈ N₁.map H.subtype := by
    rintro _ ⟨q, hq, rfl⟩
    obtain ⟨k, hk⟩ := hlg q hq
    exact ⟨k, ⟨_, hk, by simp⟩⟩
  have hcoc : ∀ g ∈ Q₁.map H.subtype, ∀ h ∈ Q₁.map H.subtype, ∀ j ∈ Q₁.map H.subtype,
      f (g * h, j) + f (g, h) = f (h, j) + f (g, h * j) := by
    rintro _ ⟨g, hg, rfl⟩ _ ⟨h, hh, rfl⟩ _ ⟨j, hj, rfl⟩
    simp only [Subgroup.coe_subtype]
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, hfv, hfv, hfv, hfv]
    exact hc₁ g hg h hh j hj
  have hinv : ∀ g ∈ Q₁.map H.subtype, ∀ h ∈ Q₁.map H.subtype, ∀ n ∈ N₁.map H.subtype,
      ∀ n' ∈ N₁.map H.subtype, f (g * n, h * n') = f (g, h) := by
    rintro _ ⟨g, hg, rfl⟩ _ ⟨h, hh, rfl⟩ _ ⟨n, hn, rfl⟩ _ ⟨n', hn', rfl⟩
    simp only [Subgroup.coe_subtype]
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, hfv, hfv]
    exact hinv₁ g hg h hh n hn n' hn'
  obtain ⟨γ, hγ, hγQ⟩ := hL (Q₁.map H.subtype) (N₁.map H.subtype) (hopen Q₁ hQ₁) (hopen N₁ hN₁)
    (Subgroup.map_mono hNQ₁) hnorm' hlg' f hlf hcoc hinv
  refine ⟨γ ∘ Subtype.val, hγ.comp_continuous continuous_subtype_val, fun g hg h hh => ?_⟩
  have := hγQ g ⟨g, hg, rfl⟩ h ⟨h, hh, rfl⟩
  rw [hfv] at this
  exact this

end RamanujanPetersson.CdOne

end

-- ===== S4.Def_RP_CdOne_Dev =====
section

/-!
# S4-PD (3), group layer part 3: dévissage and `H²(P, A) = 0`

* `exists_fixed_order_l`: an `l`-group action on a finite module of order divisible by `l` fixes an element of
  order `l` (fixed points of the image in `Perm A`, an `l`-group);
* `quotAct`: the action on `A ⧸ M` for a stable subgroup `M`;
* `lgroup_case`: under `HypL`, if `P` acts on `A` (`|A| = lᵉ`) through an `l`-group, every locally constant
  2-cocycle is a locally constant coboundary (induction on `e`, `trivial_coeff` on `⟨m⟩ ≅ ℤ/l`);
* `cd_le_one`: the same for any finite module of order `lᵉ` with locally constant action (Sylow + `index_lemma`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u

namespace RamanujanPetersson.CdOne

open groupCohomology

variable {P : Type*} [Group P] [TopologicalSpace P] [IsTopologicalGroup P]

section Fixed

variable {A : Type*} [AddCommGroup A] [DistribMulAction P A]

/-- The `P`-fixed vectors. -/
def fixAdd (P A : Type*) [Group P] [AddCommGroup A] [DistribMulAction P A] : AddSubgroup A where
  carrier := {a | ∀ g : P, g • a = a}
  zero_mem' := fun g => smul_zero g
  add_mem' := fun {a b} ha hb g => by rw [smul_add, ha g, hb g]
  neg_mem' := fun {a} ha g => by rw [smul_neg, ha g]

theorem exists_fixed_order_l [Finite A] (l : ℕ) [hl : Fact l.Prime] (hdvd : l ∣ Nat.card A)
    (hp : ∀ g : P, ∃ k : ℕ, ∀ a : A, g ^ (l ^ k) • a = a) :
    ∃ m : A, addOrderOf m = l ∧ ∀ g : P, g • m = m := by
  classical
  let G := (MulAction.toPermHom P A).range
  have hG : IsPGroup l G := by
    rintro ⟨_, g, rfl⟩
    obtain ⟨k, hk⟩ := hp g
    refine ⟨k, Subtype.ext ?_⟩
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← map_pow]
    ext a
    simp [hk]
  have hmod := hG.card_modEq_card_fixedPoints A
  have hset : MulAction.fixedPoints G A = (fixAdd P A : Set A) := by
    ext a
    constructor
    · intro h g
      exact h ⟨MulAction.toPermHom P A g, g, rfl⟩
    · rintro h ⟨_, g, rfl⟩
      exact h g
  have hcard : l ∣ Nat.card (fixAdd P A) := by
    have h1 : Nat.card (MulAction.fixedPoints G A) = Nat.card (fixAdd P A) := by
      rw [hset]; rfl
    rw [← h1]
    exact Nat.modEq_zero_iff_dvd.mp (hmod.symm.trans (Nat.modEq_zero_iff_dvd.mpr hdvd))
  let _ : Fintype (fixAdd P A) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card] at hcard
  obtain ⟨m, hm⟩ := exists_prime_addOrderOf_dvd_card l hcard
  exact ⟨m, by rw [AddSubgroup.addOrderOf_coe, hm], m.2⟩

end Fixed

section Quot

variable {A : Type*} [AddCommGroup A] [DistribMulAction P A] (M : AddSubgroup A)
  (hM : ∀ g : P, ∀ a ∈ M, g • a ∈ M)

/-- `g` acting on `A ⧸ M`. -/
def qsmul (g : P) : A ⧸ M →+ A ⧸ M :=
  QuotientAddGroup.map M M (DistribSMul.toAddMonoidHom A g) (fun a ha => hM g a ha)

theorem qsmul_mk (g : P) (a : A) : qsmul M hM g (a : A ⧸ M) = ((g • a : A) : A ⧸ M) := rfl

/-- The action on `A ⧸ M` (local instance). -/
def quotAct : DistribMulAction P (A ⧸ M) where
  smul g q := qsmul M hM g q
  one_smul q := by
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective q
    exact (qsmul_mk M hM 1 a).trans (congrArg (fun x : A => (x : A ⧸ M)) (one_smul P a))
  mul_smul g h q := by
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective q
    exact (qsmul_mk M hM _ a).trans (congrArg (fun x : A => (x : A ⧸ M)) (mul_smul g h a))
  smul_zero g := map_zero (qsmul M hM g)
  smul_add g := map_add (qsmul M hM g)

end Quot

/-- Under `HypL`: actions through an `l`-group on modules of order `lᵉ` have no locally constant `H²`. -/
theorem lgroup_case [CompactSpace P] (l : ℕ) [hl : Fact l.Prime] (hL : HypL l P) (e : ℕ) :
    ∀ (A : Type u) [AddCommGroup A] [DistribMulAction P A] [Finite A], Nat.card A = l ^ e → LcAct P A →
    (∀ g : P, ∃ k : ℕ, ∀ a : A, g ^ (l ^ k) • a = a) →
    ∀ f : P × P → A, IsLocallyConstant f → IsCocycle₂ f → IsLcCob f := by
  induction e with
  | zero =>
    intro A _ _ _ hcard _ _ f _ _
    have : Subsingleton A := Finite.card_le_one_iff_subsingleton.mp (by rw [hcard, pow_zero])
    exact ⟨0, IsLocallyConstant.const 0, fun g h => Subsingleton.elim _ _⟩
  | succ e ih =>
    intro A _ _ _ hcard hact hp f hf hc
    obtain ⟨m, hm, hmfix⟩ :=
      exists_fixed_order_l l (by rw [hcard]; exact dvd_pow_self l (Nat.succ_ne_zero e)) hp
    have hMfix : ∀ a ∈ AddSubgroup.zmultiples m, ∀ g : P, g • a = a := by
      intro a ha g
      obtain ⟨z, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp ha
      rw [smul_zsmul', hmfix g]
    have hM : ∀ g : P, ∀ a ∈ AddSubgroup.zmultiples m, g • a ∈ AddSubgroup.zmultiples m :=
      fun g a ha => by rw [hMfix a ha g]; exact ha
    letI : DistribMulAction P (A ⧸ AddSubgroup.zmultiples m) := quotAct _ hM
    have hcard' : Nat.card (A ⧸ AddSubgroup.zmultiples m) = l ^ e := by
      have h1 := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (AddSubgroup.zmultiples m)
      rw [Nat.card_zmultiples, hm, hcard, pow_succ] at h1
      exact (Nat.eq_of_mul_eq_mul_right hl.out.pos h1).symm
    have hactq : LcAct P (A ⧸ AddSubgroup.zmultiples m) := by
      intro q
      obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective q
      exact (hact a).comp (fun x : A => (x : A ⧸ AddSubgroup.zmultiples m))
    have hpq : ∀ g : P, ∃ k : ℕ, ∀ q : A ⧸ AddSubgroup.zmultiples m, g ^ (l ^ k) • q = q := by
      intro g
      obtain ⟨k, hk⟩ := hp g
      refine ⟨k, fun q => ?_⟩
      obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective q
      exact congrArg (fun x : A => (x : A ⧸ AddSubgroup.zmultiples m)) (hk a)
    have hcq : IsCocycle₂ (fun p => (f p : A ⧸ AddSubgroup.zmultiples m)) := by
      intro g h j
      have := congrArg (fun x : A => (x : A ⧸ AddSubgroup.zmultiples m)) (hc g h j)
      rw [QuotientAddGroup.mk_add, QuotientAddGroup.mk_add] at this
      exact this
    obtain ⟨b'', hb'', hfb''⟩ := ih (A ⧸ AddSubgroup.zmultiples m) hcard' hactq hpq _
      (hf.comp (fun x : A => (x : A ⧸ AddSubgroup.zmultiples m))) hcq
    obtain ⟨b, hb⟩ : ∃ b : P → A, b = fun g => (b'' g).out := ⟨_, rfl⟩
    have hlb : IsLocallyConstant b := by rw [hb]; exact hb''.comp _
    have e1 : ∀ x : P, ((b x : A) : A ⧸ AddSubgroup.zmultiples m) = b'' x := fun x => by
      rw [hb]; exact QuotientAddGroup.out_eq' _
    have hFM : ∀ g h : P, (f - d₁ b) (g, h) ∈ AddSubgroup.zmultiples m := by
      intro g h
      rw [← QuotientAddGroup.eq_zero_iff]
      have hq : ((f (g, h) : A) : A ⧸ AddSubgroup.zmultiples m) = d₁ b'' (g, h) := hfb'' g h
      have e2 : ((g • b h : A) : A ⧸ AddSubgroup.zmultiples m) = g • b'' h :=
        (qsmul_mk _ hM g (b h)).symm.trans (congrArg (qsmul _ hM g) (e1 h))
      rw [Pi.sub_apply, QuotientAddGroup.mk_sub, hq, d₁_apply, d₁_apply, QuotientAddGroup.mk_add,
        QuotientAddGroup.mk_sub, e2, e1, e1, sub_self]
    have hml : (l : ℤ) • m = 0 := by rw [natCast_zsmul, ← hm]; exact addOrderOf_nsmul_eq_zero m
    let E : ZMod l →+ A := ZMod.lift l ⟨zmultiplesHom A m, by simpa using hml⟩
    have hE : ∀ z : ℤ, E (z : ZMod l) = z • m := fun z => by
      simp only [E, ZMod.lift_coe, zmultiplesHom_apply]
    have hEinj : Function.Injective E := by
      rw [injective_iff_map_eq_zero]
      intro k hk
      obtain ⟨z, rfl⟩ := ZMod.intCast_surjective k
      rw [hE, ← addOrderOf_dvd_iff_zsmul_eq_zero, hm] at hk
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd z l).mpr hk
    have hEmem : ∀ k : ZMod l, E k ∈ AddSubgroup.zmultiples m := fun k => by
      obtain ⟨z, rfl⟩ := ZMod.intCast_surjective k
      rw [hE]
      exact AddSubgroup.mem_zmultiples_iff.mpr ⟨z, rfl⟩
    have hErange : ∀ a ∈ AddSubgroup.zmultiples m, ∃ k, E k = a := by
      intro a ha
      obtain ⟨z, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp ha
      exact ⟨z, hE z⟩
    obtain ⟨c, hcdef⟩ : ∃ c : P × P → ZMod l, c = fun p => Function.invFun E ((f - d₁ b) p) :=
      ⟨_, rfl⟩
    have hEc : ∀ p, E (c p) = (f - d₁ b) p := fun p => by
      rw [hcdef]
      obtain ⟨k, hk⟩ := hErange _ (hFM p.1 p.2)
      exact Function.invFun_eq ⟨k, hk⟩
    have hlF : IsLocallyConstant (f - d₁ b) := hf.sub (lc_d₁ hact hlb)
    have hlc : IsLocallyConstant c := by rw [hcdef]; exact hlF.comp (Function.invFun E)
    have hcF : IsCocycle₂ (f - d₁ b) := isCocycle₂_sub_d₁ hc b
    have hcc : ∀ g h j : P, c (g * h, j) + c (g, h) = c (h, j) + c (g, h * j) := by
      intro g h j
      apply hEinj
      rw [map_add, map_add, hEc, hEc, hEc, hEc, hcF g h j, hMfix _ (hFM h j) g]
    obtain ⟨γ, hγ, hcγ⟩ := trivial_coeff l hL hlc hcc
    refine ⟨b + E ∘ γ, hlb.add (hγ.comp E), fun g h => ?_⟩
    have h1 : f (g, h) = (f - d₁ b) (g, h) + d₁ b (g, h) := by rw [Pi.sub_apply, sub_add_cancel]
    rw [h1, ← hEc, hcγ g h, d₁_add]
    simp only [Pi.add_apply, d₁_apply, Function.comp_apply, map_add, map_sub]
    rw [hMfix _ (hEmem (γ h)) g]
    abel

/-- **`cd_l ≤ 1`, group form.** Under `HypL`, for a compact group `P` and a finite module `A` of order `lᵉ` with
locally constant action, every locally constant 2-cocycle is a locally constant coboundary. -/
theorem cd_le_one [CompactSpace P] (l : ℕ) [hl : Fact l.Prime] (hL : HypL l P) (e : ℕ) (A : Type u)
    [AddCommGroup A] [DistribMulAction P A] [Finite A] (hcard : Nat.card A = l ^ e) (hact : LcAct P A)
    {f : P × P → A} (hf : IsLocallyConstant f) (hc : IsCocycle₂ f) : IsLcCob f := by
  classical
  obtain ⟨N, hNn, hNo, hNK⟩ := exists_openNormal_le (actKer P A) (isOpen_actKer hact)
  have := hNn
  obtain ⟨H, hNH, hHo, hl', hH⟩ := exists_sylow_open l N hNo
  have : CompactSpace H := isCompact_iff_compactSpace.mp (H.isClosed_of_isOpen hHo).isCompact
  have hLH : HypL l H := hypL_subgroup l hL H hHo
  have hactH : LcAct H A := fun a => (hact a).comp_continuous continuous_subtype_val
  have hpH : ∀ g : H, ∃ k : ℕ, ∀ a : A, g ^ (l ^ k) • a = a := by
    intro g
    obtain ⟨k, hk⟩ := hH g g.2
    exact ⟨k, fun a => (mem_actKer.mp (hNK hk)) a⟩
  obtain ⟨β₀, hβ₀, hfβ₀⟩ := lgroup_case l hLH e A hcard hactH hpH (fun p : H × H => f (p.1, p.2))
    (hf.comp_continuous (continuous_subtype_val.prodMap continuous_subtype_val)) (fun g h j => hc g h j)
  obtain ⟨x, hx⟩ := exists_inv_index (A := A) (e := e) hl.out hl'
    (fun a => by rw [← hcard]; exact card_nsmul_eq_zero')
  refine index_lemma hact H hHo x hx hf hc (fun g => if h : g ∈ H then β₀ ⟨g, h⟩ else 0)
    (lc_dite (S := (H : Set P)) ⟨H.isClosed_of_isOpen hHo, hHo⟩ β₀ hβ₀) (fun h hh h' hh' => ?_)
  simp only [d₁_apply, dif_pos hh, dif_pos hh', dif_pos (H.mul_mem hh hh')]
  exact hfβ₀ ⟨h, hh⟩ ⟨h', hh'⟩

end RamanujanPetersson.CdOne

end

-- ===== S4.Def_RP_CdOne_Wrap =====
section

/-!
# S4-PD (3), group layer part 4: wrappers for `cd_l ≤ 1`

* `card_eq_pow_of_nsmul`: a finite abelian group killed by `lⁿ` has order a power of `l` (Cauchy);
* `cd_le_one_of_nsmul`: `cd_le_one` for modules killed by `lⁿ`;
* `repAct`, `h2_eq_zero`: the statement for a closed (compact) subgroup `Γ` of a topological group `G` acting on
  `M` through a representation `ρ` with open kernel (the `S4-CurveCoh` convention: cochains on `Γ`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u

namespace RamanujanPetersson.CdOne

open groupCohomology Topology

/-- A finite abelian group killed by `lⁿ` has order a power of `l`. -/
theorem card_eq_pow_of_nsmul (A : Type*) [AddCommGroup A] [Finite A] (l : ℕ) [hl : Fact l.Prime] (n : ℕ)
    (hA : ∀ a : A, (l ^ n) • a = 0) : ∃ e : ℕ, Nat.card A = l ^ e := by
  refine ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' (fun {d} hd hdvd => ?_)⟩
  have := Fact.mk hd
  obtain ⟨a, ha⟩ := exists_prime_addOrderOf_dvd_card' d hdvd
  have h1 : addOrderOf a ∣ l ^ n := addOrderOf_dvd_of_nsmul_eq_zero (hA a)
  rw [ha] at h1
  exact (Nat.prime_dvd_prime_iff_eq hd hl.out).mp (hd.dvd_of_dvd_pow h1)

/-- **`cd_l ≤ 1`** for finite modules killed by `lⁿ` with locally constant action. -/
theorem cd_le_one_of_nsmul {P : Type*} [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [CompactSpace P]
    (l : ℕ) [Fact l.Prime] (hL : HypL l P) (n : ℕ) (A : Type u) [AddCommGroup A] [DistribMulAction P A]
    [Finite A] (hA : ∀ a : A, (l ^ n) • a = 0) (hact : LcAct P A) {f : P × P → A} (hf : IsLocallyConstant f)
    (hc : IsCocycle₂ f) : IsLcCob f := by
  obtain ⟨e, he⟩ := card_eq_pow_of_nsmul A l n hA
  exact cd_le_one l hL e A he hact hf hc

section Rep

variable {k : Type*} [CommRing k] {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type u} [AddCommGroup M] [Module k M]

/-- The action of a subgroup `Γ` on `M` through `ρ`. -/
def repAct (ρ : Representation k G M) (Γ : Subgroup G) : DistribMulAction Γ M where
  smul g m := ρ g m
  one_smul m := by
    show ρ ((1 : Γ) : G) m = m
    simp
  mul_smul g h m := by
    show ρ ((g * h : Γ) : G) m = ρ g (ρ h m)
    simp
  smul_zero g := map_zero (ρ g)
  smul_add g a b := map_add (ρ g) a b

theorem repAct_lc (ρ : Representation k G M) (Γ : Subgroup G) (hρ : IsOpen (ρ.ker : Set G)) (m : M) :
    IsLocallyConstant fun g : Γ => ρ g m := by
  have hH : IsOpen (((ρ.ker).comap Γ.subtype : Subgroup Γ) : Set Γ) := hρ.preimage continuous_subtype_val
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g
  have h1 : (((ρ.ker).comap Γ.subtype : Subgroup Γ) : Set Γ) ∈ 𝓝 (1 : Γ) :=
    hH.mem_nhds (Subgroup.one_mem _)
  have h2 : Filter.Tendsto (fun x : Γ => g⁻¹ * x) (𝓝 g) (𝓝 1) := by
    have := (continuous_mul_left g⁻¹).tendsto g
    rwa [inv_mul_cancel] at this
  filter_upwards [h2 h1] with x hx
  have hx' : ρ ((g⁻¹ * x : Γ) : G) = 1 := MonoidHom.mem_ker.mp (Subgroup.mem_comap.mp hx)
  have hxg : x = g * (g⁻¹ * x) := (mul_inv_cancel_left g x).symm
  calc ρ (x : G) m = ρ ((g * (g⁻¹ * x) : Γ) : G) m := by rw [← hxg]
    _ = ρ g (ρ ((g⁻¹ * x : Γ) : G) m) := by simp only [Subgroup.coe_mul, map_mul, Module.End.mul_apply]
    _ = ρ g m := by rw [hx']; rfl

/-- **`H²(Γ, M) = 0`** (locally constant cochains on `Γ`, action through `ρ`), for a compact subgroup `Γ`
satisfying `HypL`, a finite `M` killed by `lⁿ` and `ρ` with open kernel. -/
theorem h2_eq_zero (ρ : Representation k G M) (Γ : Subgroup G) [CompactSpace Γ] (l : ℕ) [Fact l.Prime]
    (hL : HypL l Γ) (n : ℕ) [Finite M] (hM : ∀ m : M, (l ^ n) • m = 0) (hρ : IsOpen (ρ.ker : Set G))
    {f : Γ × Γ → M} (hf : IsLocallyConstant f)
    (hc : ∀ g h j : Γ, f (g * h, j) + f (g, h) = ρ g (f (h, j)) + f (g, h * j)) :
    ∃ b : Γ → M, IsLocallyConstant b ∧ ∀ g h : Γ, f (g, h) = ρ g (b h) - b (g * h) + b g := by
  letI := repAct ρ Γ
  obtain ⟨b, hb, hfb⟩ := cd_le_one_of_nsmul l hL n M hM (fun m => repAct_lc ρ Γ hρ m) hf
    (fun g h j => hc g h j)
  exact ⟨b, hb, fun g h => hfb g h⟩

end Rep

end RamanujanPetersson.CdOne

end

-- ===== S4.Def_RP_PerfectCx_Z1Ex =====
section

/-!
# S4-PD (5), E2.1: locally constant 1-cocycles are exact under `H² = 0`

For a subgroup `Γ` of a topological group `G` and representations `ρ`, `σ` of `G`, an equivariant linear map
`q : M → N` induces `z1Map : Z¹(Γ, M) → Z¹(Γ, N)` (locally constant cocycles, the `S4-CurveCoh` convention).

* `H2Van ρ Γ K`: locally constant 2-cocycles with values in the submodule `K` are coboundaries of locally constant
  `K`-valued cochains (cochains on `Γ`, the `h2_eq_zero` shape);
* `z1Map_surjective`: if `q` is surjective and `H2Van` holds for `ker q`, then `z1Map` is surjective
  (lift a cocycle along a set-theoretic section, its coboundary lies in `ker q`, correct by a `ker q`-valued cochain);
* `H2All k G Γ l n`: `H² = 0` for every finite `lⁿ`-torsion representation with open kernel (the output shape of
  `h2_pi1geo_eq_zero` / `h2_closed_eq_zero`); `h2Van_of_all` passes it to subrepresentations, and
  `z1Map_surjective_of_all` is the exactness statement used for `E_Γ = Z¹(Γ; A)` and `E_s = Z¹(I_s; A)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace PerfectCx

open CurveCoh

noncomputable section

variable {k : Type} [CommRing k] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type} [AddCommGroup M] [Module k M] {N : Type} [AddCommGroup N] [Module k N]
  (ρ : Representation k G M) (σ : Representation k G N) (Γ : Subgroup G)

/-- `H²(Γ, K) = 0` for a submodule `K ≤ M`, phrased on `M`-valued cochains with values in `K`. -/
def H2Van (K : Submodule k M) : Prop :=
  ∀ f : Γ × Γ → M, IsLocallyConstant f → (∀ x, f x ∈ K) →
    (∀ g h j : Γ, f (g * h, j) + f (g, h) = ρ g (f (h, j)) + f (g, h * j)) →
    ∃ b : Γ → M, IsLocallyConstant b ∧ (∀ g, b g ∈ K) ∧
      ∀ g h : Γ, f (g, h) = ρ g (b h) - b (g * h) + b g

/-- `Γ` acts locally constantly on `M` through `ρ`. -/
def LcRep : Prop := ∀ m : M, IsLocallyConstant fun g : Γ => ρ g m

theorem lcRep_of_isOpen (hρ : IsOpen (ρ.ker : Set G)) : LcRep ρ Γ :=
  fun m => CdOne.repAct_lc ρ Γ hρ m

theorem lc_act_comp (hact : LcRep ρ Γ) {c : Γ → M} (hc : IsLocallyConstant c) :
    IsLocallyConstant fun p : Γ × Γ => ρ p.1 (c p.2) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  rintro ⟨g, h⟩
  have h1 := (IsLocallyConstant.iff_eventually_eq _).1 (hact (c h)) g
  have h2 := (IsLocallyConstant.iff_eventually_eq _).1 hc h
  rw [nhds_prod_eq]
  filter_upwards [h1.prod_mk h2] with p hp
  rw [hp.2, hp.1]

/-- The coboundary of a locally constant 1-cochain is locally constant. -/
theorem lc_cob (hact : LcRep ρ Γ) {c : Γ → M} (hc : IsLocallyConstant c) :
    IsLocallyConstant fun p : Γ × Γ => ρ p.1 (c p.2) - c (p.1 * p.2) + c p.1 :=
  ((lc_act_comp ρ Γ hact hc).sub (hc.comp_continuous continuous_mul)).add
    (hc.comp_continuous continuous_fst)

/-- The map on locally constant 1-cocycles induced by an equivariant linear map. -/
def z1Map (q : M →ₗ[k] N) (hq : ∀ (g : G) (m : M), q (ρ g m) = σ g (q m)) : Z1 ρ Γ →ₗ[k] Z1 σ Γ where
  toFun c := ⟨q ∘ c, (mem_Z1 σ Γ _).2 ⟨((mem_Z1 ρ Γ _).1 c.2).1.comp q, fun g h => by
    simp only [Function.comp_apply, ((mem_Z1 ρ Γ _).1 c.2).2 g h, map_add, hq]⟩⟩
  map_add' c d := by
    refine Subtype.ext (funext fun g => ?_)
    simp
  map_smul' a c := by
    refine Subtype.ext (funext fun g => ?_)
    simp

theorem z1Map_apply (q : M →ₗ[k] N) (hq : ∀ (g : G) (m : M), q (ρ g m) = σ g (q m)) (c : Z1 ρ Γ) (g : Γ) :
    (z1Map ρ σ Γ q hq c : Γ → N) g = q ((c : Γ → M) g) := rfl

/-- **Exactness of `Z¹(Γ; -)`**: if `H²(Γ, ker q) = 0`, cocycles lift along a surjective equivariant `q`. -/
theorem z1Map_surjective (hact : LcRep ρ Γ) (q : M →ₗ[k] N) (hq : ∀ (g : G) (m : M), q (ρ g m) = σ g (q m))
    (hsurj : Function.Surjective q) (hH2 : H2Van ρ Γ (LinearMap.ker q)) :
    Function.Surjective (z1Map ρ σ Γ q hq) := by
  rintro ⟨c'', hc''⟩
  obtain ⟨hlc'', hco''⟩ := (mem_Z1 σ Γ c'').1 hc''
  have hqs : ∀ y, q (Function.surjInv hsurj y) = y := Function.surjInv_eq hsurj
  obtain ⟨c, hcdef⟩ : ∃ c : Γ → M, c = Function.surjInv hsurj ∘ c'' := ⟨_, rfl⟩
  have hc : IsLocallyConstant c := by
    rw [hcdef]
    exact hlc''.comp _
  have hqc : ∀ g, q (c g) = c'' g := fun g => by
    rw [hcdef, Function.comp_apply, hqs]
  obtain ⟨b, hb, hbK, hfb⟩ := hH2 (fun p => ρ p.1 (c p.2) - c (p.1 * p.2) + c p.1) (lc_cob ρ Γ hact hc)
    (fun p => by
      rw [LinearMap.mem_ker]
      simp only [map_add, map_sub, hq, hqc]
      rw [hco'']
      abel)
    (fun g h j => by
      dsimp only
      simp only [Subgroup.coe_mul, map_mul, Module.End.mul_apply, map_sub, map_add, mul_assoc]
      abel)
  refine ⟨⟨c - b, (mem_Z1 ρ Γ _).2 ⟨hc.sub hb, fun g h => ?_⟩⟩, ?_⟩
  · have e := hfb g h
    dsimp only at e
    have e' : c (g * h) = ρ g (c h) + c g - (ρ g (b h) - b (g * h) + b g) := by
      rw [← e]
      abel
    simp only [Pi.sub_apply, map_sub]
    rw [e']
    abel
  · refine Subtype.ext (funext fun g => ?_)
    show q (c g - b g) = c'' g
    rw [map_sub, LinearMap.mem_ker.1 (hbK g), sub_zero, hqc]

/-- The kernel of an equivariant map, as a subrepresentation. -/
def kerRep (q : M →ₗ[k] N) (hq : ∀ (g : G) (m : M), q (ρ g m) = σ g (q m)) : Subrepresentation ρ where
  toSubmodule := LinearMap.ker q
  apply_mem_toSubmodule g v hv := by
    rw [LinearMap.mem_ker] at hv ⊢
    rw [hq, hv, map_zero]

theorem toRep_val (K : Subrepresentation ρ) (g : G) (v : K.toSubmodule) :
    ((K.toRepresentation g v : K.toSubmodule) : M) = ρ g v := rfl

/-- `H²(Γ, -) = 0` for all finite `lⁿ`-torsion representations of `G` over `k` with open kernel. -/
def H2All (k G : Type) [CommRing k] [Group G] [TopologicalSpace G] (Γ : Subgroup G) (l n : ℕ) : Prop :=
  ∀ (M : Type) [AddCommGroup M] [Module k M] (ρ : Representation k G M) [Finite M],
    (∀ m : M, (l ^ n) • m = 0) → IsOpen (ρ.ker : Set G) → ∀ f : Γ × Γ → M, IsLocallyConstant f →
    (∀ g h j : Γ, f (g * h, j) + f (g, h) = ρ g (f (h, j)) + f (g, h * j)) →
    ∃ b : Γ → M, IsLocallyConstant b ∧ ∀ g h : Γ, f (g, h) = ρ g (b h) - b (g * h) + b g

theorem h2Van_of_all {l n : ℕ} (hall : H2All k G Γ l n) [Finite M] (hM : ∀ m : M, (l ^ n) • m = 0)
    (hρ : IsOpen (ρ.ker : Set G)) (K : Subrepresentation ρ) : H2Van ρ Γ K.toSubmodule := by
  intro f hf hfK hc
  have hker : ρ.ker ≤ K.toRepresentation.ker := fun g hg => by
    rw [MonoidHom.mem_ker] at hg ⊢
    refine LinearMap.ext fun v => Subtype.ext ?_
    show ρ g v = v
    rw [hg]
    rfl
  obtain ⟨b, hb, hfb⟩ := hall K.toSubmodule K.toRepresentation
    (fun m => Subtype.ext (by simp [hM])) (Subgroup.isOpen_mono hker hρ)
    (fun x => ⟨f x, hfK x⟩) (IsLocallyConstant.desc _ Subtype.val hf Subtype.val_injective)
    (fun g h j => Subtype.ext (by simpa [toRep_val] using hc g h j))
  refine ⟨fun g => b g, hb.comp Subtype.val, fun g => (b g).2, fun g h => ?_⟩
  have := congrArg Subtype.val (hfb g h)
  simpa [toRep_val] using this

/-- **Exactness of `Z¹(Γ; -)` on finite `lⁿ`-torsion modules** given `H2All` (e.g. `Γ = π₁^geo` or a closed
subgroup of it). -/
theorem z1Map_surjective_of_all {l n : ℕ} (hall : H2All k G Γ l n) [Finite M] (hM : ∀ m : M, (l ^ n) • m = 0)
    (hρ : IsOpen (ρ.ker : Set G)) (q : M →ₗ[k] N) (hq : ∀ (g : G) (m : M), q (ρ g m) = σ g (q m))
    (hsurj : Function.Surjective q) : Function.Surjective (z1Map ρ σ Γ q hq) :=
  z1Map_surjective ρ σ Γ (lcRep_of_isOpen ρ Γ hρ) q hq hsurj
    (h2Van_of_all ρ Γ hall hM hρ (kerRep ρ σ q hq))

end

end PerfectCx
end RamanujanPetersson

end


