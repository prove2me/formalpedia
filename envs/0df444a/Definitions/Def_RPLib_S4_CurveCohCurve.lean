-- Prove2me | Definitions.Def_RPLib_S4_CurveCohCurve
-- name    : RPLib_S4_CurveCohCurve
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-15T05:07:28.912644+00:00
-- url     : https://prove2.me/theorems/6dde4dd1-a644-4d9c-8d11-be48af79ab99
-- title:
--   The fundamental group of an affine curve over a finite field, its boundary inertia, and curve cohomology
-- statement:
--   For a domain $A$ with fraction field $K$ (an affine curve $U = \operatorname{Spec} A$ over $\mathbb{F}_q$) let $\pi_1(U) = \operatorname{Gal}(K_U/K)$ with its Krull topology, $K_U$ the maximal extension unramified over $A$. The file defines the constants (elements of $\mathbb{F}_{q^n}$), the geometric fundamental group $\pi_1(U \otimes \overline{\mathbb{F}}_q)$ of automorphisms fixing all constants (closed, normal, compact), arithmetic Frobenius lifts $\varphi$ ($\varphi(x) = x^q$ on constants; two lifts differ by the geometric group), the pro-chart $\operatorname{integralClosure}(R_0, K_U)$ of a boundary chart ring $R_0$ with its $\pi_1(U)$-action, and the inertia groups $$I(Q) = \{\sigma : \sigma b - b \in Q \ \forall b\}$$ of its nonzero primes $Q$, with $I(\psi Q) = \psi I(Q) \psi^{-1}$. It specialises the relative cohomology $H^0, H^1, H^1_c, H^2_c$ to $\pi_1$ of the curve and its boundary inertia, with the geometric Frobenius action.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (etale fundamental groups, Kummer theory and tame ramification on affine curves over finite fields). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   J. S. Milne, Etale Cohomology, Princeton University Press (1980), Chapter I, Section 5 and Chapter V, Section 2; A. Grothendieck, Revetements etales et groupe fondamental (SGA 1), Lecture Notes in Math. 224, Springer (1971), Expose XIII

import Mathlib
import Definitions.Def_RPLib_S4_CurveCohConst
import Definitions.Def_RPLib_S4_CurveCohInf
import Definitions.Def_RPLib_S4_GalCover

/-!
# S4-CurveCoh, part 7: the curve instance

`U = Spec A` with function field `K` (for the project's curves `K = 𝔽_q(X)`), `π₁(U) = Gal(K_U/K)`
(`Pi1 A K`, S4-GalCover, Krull topology, compact).

* Constants: `IsConst q x` (`x ∈ 𝔽_{qⁿ}` for some `n ≥ 1`); the geometric fundamental group
  `pi1geo A K q = π₁(U ⊗ 𝔽̄_q)`, the automorphisms fixing every constant: closed (`pi1geo_isClosed`), normal,
  compact (`pi1geo_compactSpace`, used by the colimit description `curveH1_exists_finite_level`).
* Frobenius lifts `IsFrobLift A K q φ` (`φ x = x^q` on constants): two lifts differ by `π₁^geo`
  (`IsFrobLift.inv_mul_mem`). The EXISTENCE of a lift (the constant-field extensions are unramified, so lie in `K_U`)
  is not proved here: every statement takes the lift `φ` as an argument (supplied by S4-Kummer / CP4a).
* Boundary: for a chart ring `R0` with fraction field `K` (for `∞`: `R0 = O_∞`, S3-Places `Places.Oinf`), the
  pro-chart `proChart A K R0 = integralClosure R0 K_U` with its `π₁(U)`-action; `BdryData` chooses representatives
  `P s` of the `π₁^geo`-orbits of the boundary points (a `π₁(U)`-stable predicate `B`, for `∞` the nonzero primes);
  `I s = BdryData.inertia s` is the inertia group (review R5). `conj_mem_inertia_smul`: inertia is transported by
  conjugation, so every `ψ` permutes the boundary (`BdryData.exists_compat`, giving the data of `frobH1c`).
  Two boundary families (e.g. `∞` and finite removed points) combine with `bdryCompat_sum`.
* Curve cohomology (any commutative coefficient ring `Λ`, review R19): `curveH0/H1/H1c/H1par/H2c` and the
  GEOMETRIC Frobenius `geomFrobH0/H1/H1c/Bdry/H2c` (`F = T_{φ⁻¹}`, `q` on `H²_c`), the exact sequence `curve_les`,
  Frobenius compatibility `geomFrob_les`.
* Lisse coefficients `IsLisse ρ` (open kernel): they factor through a finite Galois etale cover
  (`IsLisse.exists_cover`, via S4-GalCover `exists_cover_of_isOpen`).
* Sanity: `curveH0_trivialEquiv` (`H⁰(Λ) = Λ`, e.g. `Λ = ℤ/lⁿ`), `curveH2c_trivialEquiv` with
  `geomFrobH2c_trivial` (`F = q` on `H²_c(Λ) = Λ(-1)`), `finrank_curveH1c_trivial` (rank of `H¹_c(Λ)` is
  `#boundary - 1` when `H¹_par = 0`, e.g. on `U_j` where S4-Kummer gives `Pic(Ū_j) = 0`).
-/

set_option autoImplicit false

open scoped Pointwise

namespace RamanujanPetersson
namespace CurveCoh

noncomputable section

/-! ## Constants and the geometric fundamental group -/

/-- `x` is a constant of level `q`: `x ∈ 𝔽_{qⁿ}` for some `n ≥ 1`. -/
def IsConst {L : Type} [Field L] (q : ℕ) (x : L) : Prop := ∃ n : ℕ, 0 < n ∧ x ^ q ^ n = x

theorem IsConst.map {L L' F : Type} [Field L] [Field L'] [FunLike F L L'] [RingHomClass F L L'] (f : F)
    {q : ℕ} {x : L} (hx : IsConst q x) : IsConst q (f x) := by
  obtain ⟨n, hn, h⟩ := hx
  exact ⟨n, hn, by rw [← map_pow, h]⟩

section Geo

variable (A K : Type) [CommRing A] [Field K] [Algebra A K] (q : ℕ)

/-- The geometric fundamental group `π₁(U ⊗ 𝔽̄_q) = Gal(K_U / K_U ∩ K𝔽̄_q) ⊆ π₁(U)`: the automorphisms of `K_U`
fixing every constant. -/
def pi1geo : Subgroup (Pi1 A K) where
  carrier := {σ | ∀ x : maxUnram A K, IsConst q x → σ x = x}
  one_mem' := fun _ _ => rfl
  mul_mem' := fun {σ τ} hσ hτ x hx => by
    show σ (τ x) = x
    rw [hτ x hx, hσ x hx]
  inv_mem' := fun {σ} hσ x hx => by
    show σ.symm x = x
    rw [AlgEquiv.symm_apply_eq]
    exact (hσ x hx).symm

theorem mem_pi1geo (σ : Pi1 A K) : σ ∈ pi1geo A K q ↔ ∀ x : maxUnram A K, IsConst q x → σ x = x := Iff.rfl

instance pi1geo_normal : (pi1geo A K q).Normal where
  conj_mem σ hσ τ := by
    refine (mem_pi1geo A K q _).2 fun x hx => ?_
    have h1 : σ (τ.symm x) = τ.symm x := hσ _ (hx.map τ.symm)
    show τ (σ (τ.symm x)) = x
    rw [h1, AlgEquiv.apply_symm_apply]

/-- The stabilizer of one element of `K_U`. -/
def fixElt (x : maxUnram A K) : Subgroup (Pi1 A K) where
  carrier := {σ | σ x = x}
  one_mem' := rfl
  mul_mem' := fun {σ τ} (hσ : σ x = x) (hτ : τ x = x) => show σ (τ x) = x by rw [hτ, hσ]
  inv_mem' := fun {σ} (hσ : σ x = x) => show σ.symm x = x by rw [AlgEquiv.symm_apply_eq, hσ]

/-- Stabilizers are open: they contain `Gal(K_U/K(x))` with `K(x)/K` finite. -/
theorem fixElt_isOpen (x : maxUnram A K) : IsOpen (fixElt A K x : Set (Pi1 A K)) := by
  have hx : IsIntegral K x := (Algebra.IsSeparable.isSeparable K x).isIntegral
  haveI : FiniteDimensional K (IntermediateField.adjoin K {x}) := IntermediateField.adjoin.finiteDimensional hx
  refine Subgroup.isOpen_mono (H₁ := (IntermediateField.adjoin K {x}).fixingSubgroup) ?_
    (IntermediateField.fixingSubgroup_isOpen _)
  intro σ hσ
  rw [IntermediateField.mem_fixingSubgroup_iff] at hσ
  exact hσ x (IntermediateField.subset_adjoin K {x} (Set.mem_singleton x))

theorem pi1geo_isClosed : IsClosed (pi1geo A K q : Set (Pi1 A K)) := by
  have h : (pi1geo A K q : Set (Pi1 A K)) =
      ⋂ (x : maxUnram A K) (_ : IsConst q x), (fixElt A K x : Set (Pi1 A K)) := by
    ext σ
    simp only [Set.mem_iInter, SetLike.mem_coe]
    rfl
  rw [h]
  exact isClosed_iInter fun x => isClosed_iInter fun _ => Subgroup.isClosed_of_isOpen _ (fixElt_isOpen A K x)

instance pi1geo_compactSpace : CompactSpace (pi1geo A K q) :=
  isCompact_iff_compactSpace.mp (pi1geo_isClosed A K q).isCompact

/-- `φ ∈ π₁(U)` is an (arithmetic) Frobenius lift: `φ x = x^q` on constants. -/
def IsFrobLift (φ : Pi1 A K) : Prop := ∀ x : maxUnram A K, IsConst q x → φ x = x ^ q

/-- Two Frobenius lifts differ by an element of `π₁^geo`. -/
theorem IsFrobLift.inv_mul_mem {φ₁ φ₂ : Pi1 A K} (h₁ : IsFrobLift A K q φ₁) (h₂ : IsFrobLift A K q φ₂) :
    φ₁⁻¹ * φ₂ ∈ pi1geo A K q := by
  refine (mem_pi1geo A K q _).2 fun x hx => ?_
  show φ₁.symm (φ₂ x) = x
  rw [h₂ x hx, AlgEquiv.symm_apply_eq, h₁ x hx]

theorem IsFrobLift.mul_mem {φ g : Pi1 A K} (hφ : IsFrobLift A K q φ) (hg : g ∈ pi1geo A K q) :
    IsFrobLift A K q (φ * g) := by
  intro x hx
  show φ (g x) = x ^ q
  rw [(mem_pi1geo A K q g).1 hg x hx, hφ x hx]

/-! ## Boundary points and their inertia -/

section Boundary

variable (R0 : Type) [CommRing R0] [Algebra R0 K] [Algebra R0 (maxUnram A K)]
  [IsScalarTower R0 K (maxUnram A K)]

/-- The pro-chart over `Spec R0`: the integral closure of `R0` in `K_U`, acted on by `π₁(U)`. -/
abbrev proChart : Type := integralClosure R0 (maxUnram A K)

example : MulSemiringAction (Pi1 A K) (proChart A K R0) := inferInstance

/-- A nonzero prime of the pro-chart. For `R0 = O_∞` these are the boundary points over `∞`. -/
def IsBdryPrime (Q : Ideal (proChart A K R0)) : Prop := Q.IsPrime ∧ Q ≠ ⊥

theorem isBdryPrime_smul (σ : Pi1 A K) {Q : Ideal (proChart A K R0)} (hQ : IsBdryPrime A K R0 Q) :
    IsBdryPrime A K R0 (σ • Q) := by
  haveI := hQ.1
  refine ⟨Ideal.IsPrime.smul σ, ?_⟩
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hQ.2
  exact (Submodule.ne_bot_iff _).2 ⟨σ • x, Ideal.smul_mem_pointwise_smul σ x Q hx, (smul_ne_zero_iff_ne σ).2 hx0⟩

/-- Inertia is transported by conjugation: `σ I(Q) σ⁻¹ = I(σ Q)`. -/
theorem conj_mem_inertia_smul (σ : Pi1 A K) {Q : Ideal (proChart A K R0)} {g : Pi1 A K}
    (hg : g ∈ Q.inertia (Pi1 A K)) : σ * g * σ⁻¹ ∈ (σ • Q).inertia (Pi1 A K) := by
  refine AddSubgroup.mem_inertia.2 fun x => ?_
  have hx : g • (σ⁻¹ • x) - σ⁻¹ • x ∈ Q := AddSubgroup.mem_inertia.1 hg (σ⁻¹ • x)
  show (σ * g * σ⁻¹) • x - x ∈ σ • Q
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, smul_sub, mul_smul, mul_smul, inv_smul_smul]
  exact hx

/-- The inverse transport: if `Q = σ Q'` then `σ⁻¹ I(Q) σ ⊆ I(Q')`. -/
theorem inv_conj_mem_inertia {σ : Pi1 A K} {Q Q' : Ideal (proChart A K R0)} (hQ : Q = σ • Q') {g : Pi1 A K}
    (hg : g ∈ Q.inertia (Pi1 A K)) : σ⁻¹ * g * σ ∈ Q'.inertia (Pi1 A K) := by
  subst hQ
  refine AddSubgroup.mem_inertia.2 fun x => ?_
  have hx : g • (σ • x) - σ • x ∈ σ • Q' := AddSubgroup.mem_inertia.1 hg (σ • x)
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, smul_sub, inv_smul_smul] at hx
  show (σ⁻¹ * g * σ) • x - x ∈ Q'
  rw [mul_smul, mul_smul]
  exact hx

/-- Boundary data at the chart `R0`: a `π₁(U)`-stable set `B` of boundary points of the pro-chart and
representatives `P s` of its `π₁^geo`-orbits (the geometric boundary points `s ∈ X̄ \ Ū` over this chart). -/
structure BdryData (S : Type) where
  B : Ideal (proChart A K R0) → Prop
  B_smul : ∀ (σ : Pi1 A K) (Q : Ideal (proChart A K R0)), B Q → B (σ • Q)
  P : S → Ideal (proChart A K R0)
  mem : ∀ s, B (P s)
  cover : ∀ Q, B Q → ∃ s, ∃ g ∈ pi1geo A K q, Q = g • P s
  disj : ∀ s t, ∀ g ∈ pi1geo A K q, P t = g • P s → s = t

variable {A K q R0} {S : Type} (D : BdryData A K q R0 S)

/-- The inertia group `I_s ⊆ π₁(U)` at the boundary point `P s` (review R5). -/
def BdryData.inertia (s : S) : Subgroup (Pi1 A K) := (D.P s).inertia (Pi1 A K)

/-- Every `ψ ∈ π₁(U)` permutes the geometric boundary points compatibly with inertia. -/
theorem BdryData.exists_compat (ψ : Pi1 A K) :
    ∃ (τ : S → S) (h : S → pi1geo A K q), BdryCompat (pi1geo A K q) D.inertia ψ τ h := by
  have key : ∀ s, ∃ t, ∃ g ∈ pi1geo A K q, ψ⁻¹ • D.P s = g • D.P t := fun s =>
    D.cover _ (D.B_smul ψ⁻¹ _ (D.mem s))
  choose τ g hg hτ using key
  refine ⟨τ, fun s => ⟨g s, hg s⟩, fun s x hx => ?_⟩
  have hx' : (x : Pi1 A K) ∈ (D.P s).inertia (Pi1 A K) := hx
  have h1 := conj_mem_inertia_smul A K R0 ψ⁻¹ hx'
  rw [inv_inv] at h1
  exact inv_conj_mem_inertia A K R0 (hτ s) h1

/-- A chosen boundary permutation for `ψ`. -/
def BdryData.frobTau (ψ : Pi1 A K) : S → S := (D.exists_compat ψ).choose

/-- The chosen correcting elements `h_s ∈ π₁^geo` for `ψ`. -/
def BdryData.frobH (ψ : Pi1 A K) : S → pi1geo A K q := (D.exists_compat ψ).choose_spec.choose

theorem BdryData.frob_compat (ψ : Pi1 A K) :
    BdryCompat (pi1geo A K q) D.inertia ψ (D.frobTau ψ) (D.frobH ψ) :=
  (D.exists_compat ψ).choose_spec.choose_spec

end Boundary

/-- Combining two boundary families (e.g. the points over `∞` and finitely many removed finite points). -/
theorem bdryCompat_sum {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (Γ : Subgroup G)
    [Γ.Normal] {S T : Type} {I : S → Subgroup G} {J : T → Subgroup G} {ψ : G} {τ : S → S} {τ' : T → T}
    {h : S → Γ} {h' : T → Γ} (hI : BdryCompat Γ I ψ τ h) (hJ : BdryCompat Γ J ψ τ' h') :
    BdryCompat Γ (Sum.elim I J) ψ (Sum.map τ τ') (Sum.elim h h') := by
  rintro (s | t) g hg
  · exact hI s g hg
  · exact hJ t g hg

/-! ## Curve cohomology and the geometric Frobenius -/

section Cohomology

variable {A K} {R0 : Type} [CommRing R0] [Algebra R0 K] [Algebra R0 (maxUnram A K)]
  [IsScalarTower R0 K (maxUnram A K)] {S : Type}
  {Λ : Type} [CommRing Λ] {M : Type} [AddCommGroup M] [Module Λ M] (ρ : Representation Λ (Pi1 A K) M)

/-- `H⁰(U ⊗ 𝔽̄_q, M)`. -/
abbrev curveH0 : Submodule Λ M := H0 ρ (pi1geo A K q)

/-- `H¹(U ⊗ 𝔽̄_q, M)` (continuous cohomology of `π₁^geo`). -/
abbrev curveH1 : Type := H1 ρ (pi1geo A K q)

/-- `H¹_c(U ⊗ 𝔽̄_q, M)`: the cone over the boundary inertia groups of `D`. -/
abbrev curveH1c (D : BdryData A K q R0 S) : Type := H1c ρ (pi1geo A K q) D.inertia

/-- `H¹_par = image (H¹_c → H¹)`. -/
abbrev curveH1par (D : BdryData A K q R0 S) : Submodule Λ (curveH1 q ρ) := H1par ρ (pi1geo A K q) D.inertia

/-- `H²_c(U ⊗ 𝔽̄_q, M) := M_{π₁^geo}` (review R2; the twist `(-1)` is carried by the Frobenius). -/
abbrev curveH2c : Type := H2c ρ (pi1geo A K q)

/-- GEOMETRIC Frobenius on `H⁰`: `F = T_{φ⁻¹}` for an arithmetic Frobenius lift `φ`. -/
def geomFrobH0 (φ : Pi1 A K) : curveH0 q ρ →ₗ[Λ] curveH0 q ρ := frobH0 ρ (pi1geo A K q) φ⁻¹

/-- GEOMETRIC Frobenius on `H¹`. -/
def geomFrobH1 (φ : Pi1 A K) : curveH1 q ρ →ₗ[Λ] curveH1 q ρ := frobH1 ρ (pi1geo A K q) φ⁻¹

/-- GEOMETRIC Frobenius on `⊕_s M^{I_s}`. -/
def geomFrobBdry (D : BdryData A K q R0 S) (φ : Pi1 A K) :
    bdryInv ρ (pi1geo A K q) D.inertia →ₗ[Λ] bdryInv ρ (pi1geo A K q) D.inertia :=
  frobBdry ρ (pi1geo A K q) D.inertia φ⁻¹ (D.frobTau φ⁻¹) (D.frobH φ⁻¹) (D.frob_compat φ⁻¹)

/-- GEOMETRIC Frobenius on `H¹_c`. -/
def geomFrobH1c (D : BdryData A K q R0 S) (φ : Pi1 A K) : curveH1c q ρ D →ₗ[Λ] curveH1c q ρ D :=
  frobH1c ρ (pi1geo A K q) D.inertia φ⁻¹ (D.frobTau φ⁻¹) (D.frobH φ⁻¹) (D.frob_compat φ⁻¹)

/-- GEOMETRIC Frobenius on `H²_c = M_{π₁^geo}(-1)`: `q • ρ(φ⁻¹)`. -/
def geomFrobH2c (φ : Pi1 A K) : curveH2c q ρ →ₗ[Λ] curveH2c q ρ := frobH2c ρ (pi1geo A K q) φ⁻¹ (q : Λ)

/-- The exact sequence `0 → H⁰ → ⊕_s M^{I_s} → H¹_c → H¹_par → 0`. -/
theorem curve_les [Nonempty S] (D : BdryData A K q R0 S) :
    Function.Injective (h0ToBdry ρ (pi1geo A K q) D.inertia) ∧
    Function.Exact (h0ToBdry ρ (pi1geo A K q) D.inertia) (bdryToH1c ρ (pi1geo A K q) D.inertia) ∧
    Function.Exact (bdryToH1c ρ (pi1geo A K q) D.inertia) (h1cToH1 ρ (pi1geo A K q) D.inertia) ∧
    LinearMap.range (h1cToH1 ρ (pi1geo A K q) D.inertia) = curveH1par q ρ D :=
  ⟨h0ToBdry_injective _ _ _, exact_h0ToBdry_bdryToH1c _ _ _, exact_bdryToH1c_h1cToH1 _ _ _, range_h1cToH1 _ _ _⟩

/-- The geometric Frobenius commutes with the maps of the exact sequence. -/
theorem geomFrob_les (D : BdryData A K q R0 S) (φ : Pi1 A K) :
    (∀ m, geomFrobBdry q ρ D φ (h0ToBdry ρ (pi1geo A K q) D.inertia m) =
      h0ToBdry ρ (pi1geo A K q) D.inertia (geomFrobH0 q ρ φ m)) ∧
    (∀ b, geomFrobH1c q ρ D φ (bdryToH1c ρ (pi1geo A K q) D.inertia b) =
      bdryToH1c ρ (pi1geo A K q) D.inertia (geomFrobBdry q ρ D φ b)) ∧
    (∀ x, h1cToH1 ρ (pi1geo A K q) D.inertia (geomFrobH1c q ρ D φ x) =
      geomFrobH1 q ρ φ (h1cToH1 ρ (pi1geo A K q) D.inertia x)) :=
  ⟨frobBdry_h0ToBdry ρ (pi1geo A K q) D.inertia φ⁻¹ (D.frobTau φ⁻¹) (D.frobH φ⁻¹) (D.frob_compat φ⁻¹),
    frobH1c_bdryToH1c ρ (pi1geo A K q) D.inertia φ⁻¹ (D.frobTau φ⁻¹) (D.frobH φ⁻¹) (D.frob_compat φ⁻¹),
    h1cToH1_frobH1c ρ (pi1geo A K q) D.inertia φ⁻¹ (D.frobTau φ⁻¹) (D.frobH φ⁻¹) (D.frob_compat φ⁻¹)⟩

/-! ## Lisse coefficients -/

/-- A lisse sheaf on `U` in the `π₁` model: a representation of `π₁(U)` with open kernel. -/
def IsLisse : Prop := IsOpen (ρ.ker : Set (Pi1 A K))

theorem IsLisse.isOpen_ker_geo (hρ : IsLisse ρ) :
    IsOpen ((ρ.comp (pi1geo A K q).subtype).ker : Set (pi1geo A K q)) :=
  hρ.preimage continuous_subtype_val

/-- `H¹` of a lisse sheaf is the colimit of finite-level group cohomology (every class comes from a finite
quotient of `π₁^geo`, and inflation is injective, `inflZ1_eq_zero_iff`). -/
theorem curveH1_exists_finite_level (hρ : IsLisse ρ) (x : curveH1 q ρ) :
    ∃ (N : Subgroup (pi1geo A K q)) (_ : N.Normal) (hNo : IsOpen (N : Set (pi1geo A K q)))
      (hN : N ≤ (ρ.comp (pi1geo A K q).subtype).ker)
      (f : groupCohomology.cocycles₁ (Rep.of (repQ ρ (pi1geo A K q) N hN))),
      H1.mk ρ (pi1geo A K q) (inflZ1 ρ (pi1geo A K q) N hN hNo f) = x :=
  exists_finite_level ρ (pi1geo A K q) (IsLisse.isOpen_ker_geo q ρ hρ) x

theorem rho_eq_of_ker_le {H : Type} [Group H] (π : Pi1 A K →* H) (hker : π.ker ≤ ρ.ker) {a b : Pi1 A K}
    (hab : π a = π b) : ρ a = ρ b := by
  have hm : a⁻¹ * b ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hab, inv_mul_cancel]
  have h1 : ρ (a⁻¹ * b) = 1 := hker hm
  calc ρ a = ρ a * ρ (a⁻¹ * b) := by rw [h1, mul_one]
    _ = ρ b := by rw [← map_mul, mul_inv_cancel_left]

/-- The representation of a quotient `π : π₁(U) ↠ H` through which `ρ` factors. -/
def descRep {H : Type} [Group H] (π : Pi1 A K →* H) (hπ : Function.Surjective π) (hker : π.ker ≤ ρ.ker) :
    Representation Λ H M where
  toFun x := ρ (Function.surjInv hπ x)
  map_one' := by
    show ρ (Function.surjInv hπ 1) = 1
    rw [rho_eq_of_ker_le ρ π hker ((Function.surjInv_eq hπ 1).trans π.map_one.symm), map_one]
  map_mul' x y := by
    show ρ (Function.surjInv hπ (x * y)) = ρ (Function.surjInv hπ x) * ρ (Function.surjInv hπ y)
    rw [← map_mul]
    exact rho_eq_of_ker_le ρ π hker (by
      rw [map_mul, Function.surjInv_eq hπ, Function.surjInv_eq hπ, Function.surjInv_eq hπ])

theorem descRep_comp {H : Type} [Group H] (π : Pi1 A K →* H) (hπ : Function.Surjective π)
    (hker : π.ker ≤ ρ.ker) : (descRep ρ π hπ hker).comp π = ρ :=
  MonoidHom.ext fun g => rho_eq_of_ker_le ρ π hker (Function.surjInv_eq hπ (π g))

attribute [local instance] GalCover.grp in
/-- A lisse sheaf comes from a representation of the group of a finite Galois etale cover of `U`. -/
theorem IsLisse.exists_cover [IsDomain A] [IsFractionRing A K] [IsIntegrallyClosed A] [IsNoetherianRing A]
    (hρ : IsLisse ρ) :
    ∃ (C : GalCover A) (π : Pi1 A K →* C.G) (σ : Representation Λ C.G M),
      Function.Surjective π ∧ σ.comp π = ρ := by
  obtain ⟨C, π, hπ, hker⟩ := exists_cover_of_isOpen A K ρ.ker hρ
  exact ⟨C, π, descRep ρ π hπ hker, hπ, descRep_comp ρ π hπ hker⟩

end Cohomology

/-! ## Sanity checks for the constant sheaf -/

section Sanity

variable {R0 : Type} [CommRing R0] [Algebra R0 K] [Algebra R0 (maxUnram A K)]
  [IsScalarTower R0 K (maxUnram A K)] {S : Type} (Λ : Type) [CommRing Λ]

/-- `H⁰(U ⊗ 𝔽̄_q, Λ) = Λ` (for `Λ = ℤ/lⁿ`: `H⁰ = ℤ/lⁿ`). -/
def curveH0_trivialEquiv : curveH0 q (Representation.trivial Λ (Pi1 A K) Λ) ≃ₗ[Λ] Λ :=
  h0ConstEquiv (Representation.trivial Λ (Pi1 A K) Λ) (pi1geo A K q) (fun _ => rfl)

/-- `H²_c(U ⊗ 𝔽̄_q, Λ) = Λ`. -/
def curveH2c_trivialEquiv : curveH2c q (Representation.trivial Λ (Pi1 A K) Λ) ≃ₗ[Λ] Λ :=
  h2cConstEquiv (Representation.trivial Λ (Pi1 A K) Λ) (pi1geo A K q) (fun _ => rfl)

/-- The geometric Frobenius acts on `H²_c(Λ) = Λ(-1)` by `q`. -/
theorem geomFrobH2c_trivial (φ : Pi1 A K) (x : curveH2c q (Representation.trivial Λ (Pi1 A K) Λ)) :
    geomFrobH2c q (Representation.trivial Λ (Pi1 A K) Λ) φ x = (q : Λ) • x := by
  obtain ⟨y, rfl⟩ := Representation.Coinvariants.mk_surjective _ x
  exact frobH2c_mk _ _ _ _ _

/-- `H¹_c(U ⊗ 𝔽̄_q, Λ)` is free of rank `#boundary - 1` when `H¹_par = 0` (for `U_j`: S4-Kummer). -/
theorem finrank_curveH1c_trivial [Nontrivial Λ] [Fintype S] [DecidableEq S] [Nonempty S]
    (D : BdryData A K q R0 S)
    (hpar : curveH1par q (Representation.trivial Λ (Pi1 A K) Λ) D = ⊥) :
    Module.finrank Λ (curveH1c q (Representation.trivial Λ (Pi1 A K) Λ) D) = Fintype.card S - 1 :=
  finrank_H1c_const (Γ := pi1geo A K q) (I := D.inertia) (ρ' := Representation.trivial Λ (Pi1 A K) Λ)
    (htriv := fun _ => rfl) (hpar := hpar)

end Sanity

end Geo

/-! ## The boundary at infinity (S3-Places) -/

section Infinity

variable (Fq : Type) [Field Fq] [DecidableEq (RatFunc Fq)] (A : Type) [CommRing A] [Algebra A (RatFunc Fq)]

/-- The pro-chart at infinity: the integral closure of `O_∞` (S3-Places) in `K_U`. -/
abbrev infProChart : Type := proChart A (RatFunc Fq) (Places.Oinf Fq)

example : MulSemiringAction (Pi1 A (RatFunc Fq)) (infProChart Fq A) := inferInstance

/-- Boundary data at infinity: the `π₁^geo`-orbits of the nonzero primes of the infinity pro-chart. -/
structure InfBdry [Fintype Fq] (S : Type) where
  P : S → Ideal (infProChart Fq A)
  mem : ∀ s, IsBdryPrime A (RatFunc Fq) (Places.Oinf Fq) (P s)
  cover : ∀ Q, IsBdryPrime A (RatFunc Fq) (Places.Oinf Fq) Q →
    ∃ s, ∃ g ∈ pi1geo A (RatFunc Fq) (Fintype.card Fq), Q = g • P s
  disj : ∀ s t, ∀ g ∈ pi1geo A (RatFunc Fq) (Fintype.card Fq), P t = g • P s → s = t

/-- The infinity boundary as `BdryData` (its `B` is "nonzero prime", stable by `isBdryPrime_smul`). -/
def InfBdry.toBdryData [Fintype Fq] {S : Type} (D : InfBdry Fq A S) :
    BdryData A (RatFunc Fq) (Fintype.card Fq) (Places.Oinf Fq) S where
  B := IsBdryPrime A (RatFunc Fq) (Places.Oinf Fq)
  B_smul σ _ hQ := isBdryPrime_smul A (RatFunc Fq) (Places.Oinf Fq) σ hQ
  P := D.P
  mem := D.mem
  cover := D.cover
  disj := D.disj

end Infinity

end

end CurveCoh
end RamanujanPetersson


