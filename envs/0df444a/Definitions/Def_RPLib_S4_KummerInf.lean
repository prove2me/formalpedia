-- Prove2me | Definitions.Def_RPLib_S4_KummerInf
-- name    : RPLib_S4_KummerInf
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-15T05:39:16.98412+00:00
-- url     : https://prove2.me/theorems/758bafa9-266a-4996-ba4c-7638c4d51717
-- title:
--   Kummer classes at the boundary of an affine curve
-- statement:
--   Let $R_0$ be a chart ring of the boundary of $U = \operatorname{Spec} A$ (for curves: the ring at infinity) and consider the pro-chart, the integral closure of $R_0$ in $K_U$. The file proves that with trivial coefficients $\mathbb{Z}/N$ a Kummer class $[\kappa_\alpha]$ is parabolic iff $\alpha$ is fixed by the geometric boundary inertia $I_s \cap \pi_1^{geo}$; that a pro-chart inertia element fixing a finite level $M$ fixes every $N$-th root of $a \in M$ with $I^N (a) = (1)$ over $R_0$; that boundary inertia fixes the constants ($I \le \pi_1^{geo}$); and, assuming inertia groups lift along restriction, that an element of $K_U$ fixed by all boundary inertia lies in the maximal extension unramified over $R_0$.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (etale fundamental groups, Kummer theory and tame ramification on affine curves over finite fields). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   J. S. Milne, Etale Cohomology, Princeton University Press (1980), Chapter I, Section 5 and Chapter V, Section 2; J.-P. Serre, Local Fields, GTM 67, Springer (1979), Chapter I, Section 7

import Mathlib
import Definitions.Def_RPLib_S4_KummerLev

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


