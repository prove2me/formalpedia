-- Prove2me | Definitions.Def_OAIE3v2B132
-- name    : OAIE3v2B132
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:53:32.758516+00:00
-- url     : https://prove2.me/theorems/75f906f3-9dc2-4de5-a9f4-7b4d3780c253
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 134 of 311
-- statement:
--   Definitions bundle 134 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B114`, `OAIE3v2B115`, `OAIE3v2B117`, `OAIE3v2B118`, `OAIE3v2B119`, `OAIE3v2B120` of this split.
--
--   Modules: `Estimates/BoundedSubmoduleIntersection.lean`, `Estimates/CommonSubspaceFamily.lean`, `Estimates/FixedObservableCorrelation.lean`, `Estimates/LowerStepSquare.lean`, `Estimates/NativeCentralSeed.lean`, `Estimates/NativeRationalRepresentatives.lean`, `Fourier/HomogeneousGradedProjectionFrequency.lean`, `Fourier/ProductFrequencyKernel.lean`, `Fourier/RationalFrequencyHeight.lean`, `Fourier/VerticalFrequencyIdentification.lean`, `Linear/FixedAdaptedSymbolFactorizationBasis.lean`, `Linear/NativeRankBudget.lean`, `Nilpotent/NiltestVerticalBounds.lean`, `Sampling/ControlledIntegralGrid.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B114
import Definitions.Def_OAIE3v2B115
import Definitions.Def_OAIE3v2B117
import Definitions.Def_OAIE3v2B118
import Definitions.Def_OAIE3v2B119
import Definitions.Def_OAIE3v2B120

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LowerStepSquare
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup CircleFourier

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (Γ : Subgroup F.Group)

noncomputable def squareObservable (ε : F.Group) (u : F.Group ⧸ Γ → ℂ)
    (x : F.squareFiltration.Group ⧸ F.squareLattice Γ) : ℂ :=
  u (ε • cosetMap (F.squareLattice Γ) Γ F.squareFstHom (F.squareLattice_le_fst Γ) x) *
    star (u (cosetMap (F.squareLattice Γ) Γ F.squareSndHom (F.squareLattice_le_snd Γ) x))

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.HomogeneousGradedProjectionFrequency
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

include hF in
theorem basisGradeProjection_top (x : F.layer s) : basisGradeProjection b ω s (x : L) = x := by
  have he : {i | ω i = s} = {i | s ≤ ω i} := by
    ext i
    exact ⟨fun h => h.ge, fun h => le_antisymm (F.adaptedBasis_weight_le_step b ω hF i) h⟩
  change basisCoordinateProjection b {i | ω i = s} (x : L) = x
  rw [he]
  exact basisCoordinateProjection_eq_self b _ _ ((hF s) ▸ x.property)

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeCentralSeed
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct BigOperators

variable {L : Type*} [AddCommGroup L] [Module ℚ L]

theorem basisFrequency_basis {ι : Type*} (b : Basis ι ℚ L) (S : Set ι)
    [Fintype S] (N : ℕ) (n : S → ℤ) (j : S) :
    basisFrequency b S N n (b j) = (n j : ℚ) / (N : ℚ) := by
  classical
  rw [basisFrequency_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    have hval : (j : ι) ≠ i := fun h => hij (Subtype.ext h.symm)
    simp [Basis.repr_self, hval]
  · simp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.VerticalFrequencyIdentification
namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped TensorProduct

variable {L X ι : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  [MulAction (NilpotentLieBCHGroup L s hnil) X]

theorem central_span_character (u : ι → L) (hu : ∀ i (w : L), ⁅u i, w⁆ = 0)
    (η : L →ₗ[ℝ] ℝ) (f : X → ℂ)
    (hf : ∀ i (r : ℝ) x, f (realBCHLine (hnil := hnil) (u i) r • x) =
      CircleFourier.character ((r * η (u i) : ℝ) : CircleFourier.Circle) * f x)
    {v : L} (hv : v ∈ Submodule.span ℝ (Set.range u)) (x : X) :
    f ((⟨v⟩ : NilpotentLieBCHGroup L s hnil) • x) =
      CircleFourier.character ((η v : ℝ) : CircleFourier.Circle) * f x := by
  have h : (∀ w : L, ⁅v, w⁆ = 0) ∧ ∀ (r : ℝ) x,
      f (realBCHLine (hnil := hnil) v r • x) =
        CircleFourier.character ((r * η v : ℝ) : CircleFourier.Circle) * f x := by
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨i, rfl⟩ := hv
      exact ⟨hu i, hf i⟩
    | zero =>
      refine ⟨fun w => zero_lie w, ?_⟩
      intro r x
      have he : realBCHLine (hnil := hnil) (0 : L) r = 1 := by
        apply ext
        exact smul_zero r
      simp [he]
    | @add v w hv hw ihv ihw =>
      refine ⟨fun z => by rw [add_lie, ihv.1, ihw.1, add_zero], ?_⟩
      intro r x
      have he : realBCHLine (hnil := hnil) (v + w) r =
          realBCHLine v r * realBCHLine w r := by
        apply ext
        change r • (v + w) = lieBCH s (r • v) (r • w)
        rw [lieBCH_eq_add_of_lie_eq_zero hnil (by rw [smul_lie, ihv.1, smul_zero]), smul_add]
      rw [he, mul_smul, ihv.2, ihw.2, map_add, mul_add,
        AddCircle.coe_add, CircleFourier.character_add, mul_assoc]
    | @smul a v hv ih =>
      refine ⟨fun w => by rw [smul_lie, ih.1, smul_zero], ?_⟩
      intro r x
      have he : realBCHLine (hnil := hnil) (a • v) r = realBCHLine v (r * a) := by
        apply ext
        exact (mul_smul r a v).symm
      rw [he, ih.2, map_smul, smul_eq_mul, mul_assoc]
  simpa only [realBCHLine_one, one_mul] using h.2 1 x

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3

open NilpotentLieBCHGroup CircleFourier
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)
  (Γ : Subgroup F.realification.Group)

theorem vertical_frequency_integral_on_lattice (η : L →ₗ[ℚ] ℚ)
    (f : F.realification.Group ⧸ Γ → ℂ)
    (hf : ∀ z : F.realification.Group, z ∈ F.realification.subgroup s → ∀ x,
      f (z • x) = character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * f x)
    (hne : ∃ x, f x ≠ 0) (z : F.realification.Group)
    (hz : z ∈ F.realification.subgroup s) (hΓ : z ∈ Γ) :
    ∃ n : ℤ, realifyFunctional η z.coord = n := by
  obtain ⟨x, hx⟩ := hne
  have hc : ∀ a : F.realification.Group, Commute z a := by
    intro a
    exact commute_of_lie_eq_zero z a (F.realification.top_layer_central hz a.coord)
  have he : character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) = 1 := by
    apply mul_right_cancel₀ hx
    calc
      _ = f (z • x) := (hf z hz x).symm
      _ = f x := by rw [central_smul_eq_self_of_mem Γ hΓ hc x]
      _ = 1 * f x := (one_mul _).symm
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp ((character_eq_one_iff _).mp he)
  exact ⟨n, by simpa only [zsmul_eq_mul, mul_one] using hn.symm⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BoundedSubmoduleIntersection
namespace OAI

section

namespace Erdos3

open Module

variable {ι L : Type*} [Fintype ι] [AddCommGroup L] [Module ℚ L]
  (b : Basis ι ℚ L)

noncomputable def coordinateArraySpan (m : ℕ) (c : Fin m × ι → ℚ) : Submodule ℚ L :=
  Submodule.span ℚ (Set.range fun a : Fin m => b.equivFun.symm (fun i => c (a, i)))

noncomputable def heightBoundedSubspaces (m H : ℕ) : Set (Submodule ℚ L) :=
  coordinateArraySpan b m '' {c : Fin m × ι → ℚ | ∀ z, RationalHeightLE (c z) H}

theorem mem_heightBoundedSubspaces (m H : ℕ) (U : Submodule ℚ L) :
    U ∈ heightBoundedSubspaces b m H ↔
      ∃ v : Fin m → L, Submodule.span ℚ (Set.range v) = U ∧
        ∀ a i, RationalHeightLE (b.repr (v a) i) H := by
  constructor
  · rintro ⟨c, hc, rfl⟩
    refine ⟨fun a => b.equivFun.symm (fun i => c (a, i)), rfl, ?_⟩
    intro a i
    simpa only [← Basis.equivFun_apply, LinearEquiv.apply_symm_apply] using hc (a, i)
  · rintro ⟨v, hv, hh⟩
    refine ⟨fun z => b.repr (v z.1) z.2, (fun z => hh z.1 z.2), ?_⟩
    have he : (fun a : Fin m => b.equivFun.symm (fun i => b.repr (v a) i)) = v := by
      funext a
      apply b.equivFun.injective
      simp only [LinearEquiv.apply_symm_apply, Basis.equivFun_apply]
    change Submodule.span ℚ (Set.range (fun a : Fin m => b.equivFun.symm (fun i => b.repr (v a) i))) = U
    rw [he, hv]

theorem finite_card_heightBoundedSubspaces (m H : ℕ) :
    (heightBoundedSubspaces b m H).Finite ∧
      (heightBoundedSubspaces b m H).ncard ≤ ((2 * H + 1) * (H + 1)) ^ (m * Fintype.card ι) := by
  let S : Set (Fin m × ι → ℚ) := {c | ∀ z, RationalHeightLE (c z) H}
  obtain ⟨hfin, hcard⟩ := finite_card_bounded_height_arrays S H (fun _ hc => hc)
  refine ⟨hfin.image (coordinateArraySpan b m), ?_⟩
  have hh := (Set.ncard_image_le (f := coordinateArraySpan b m) hfin).trans hcard
  rw [Fintype.card_prod, Fintype.card_fin] at hh
  exact hh

end Erdos3

end

section

namespace Erdos3

open Module

variable {ι η L : Type*} [Fintype ι] [AddCommGroup L] [Module ℚ L]
  (e : Basis ι ℚ L) (K : Submodule ℚ L)

theorem exists_bounded_submodule_ambient_spanning (v : η → L)
    (hspan : Submodule.span ℚ (Set.range v) = K) {H : ℕ} (hH : 1 ≤ H)
    (hv : ∀ a i, RationalHeightLE (e.repr (v a) i) H) :
    ∃ w : Fin (Fintype.card ι) → L,
      Submodule.span ℚ (Set.range w) = K ∧
        ∀ a i, RationalHeightLE (e.repr (w a) i) H := by
  classical
  let : FiniteDimensional ℚ L := e.finiteDimensional_of_finite
  obtain ⟨b, hb⟩ := exists_bounded_submodule_basis_from_spanning e K v hspan hv
  have hr : finrank ℚ K ≤ Fintype.card ι := by
    simpa only [finrank_eq_card_basis e] using K.finrank_le
  let w : Fin (Fintype.card ι) → L := fun a =>
    if ha : a.val < finrank ℚ K then (b ⟨a.val, ha⟩ : L) else 0
  have hw (i : Fin (finrank ℚ K)) :
      w ⟨i.val, lt_of_lt_of_le i.isLt hr⟩ = (b i : L) := by
    simp only [w, dif_pos i.isLt]
  refine ⟨w, ?_, ?_⟩
  · apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro x ⟨a, rfl⟩
      dsimp only [w]
      split_ifs with ha
      · exact (b ⟨a.val, ha⟩).property
      · exact K.zero_mem
    · have htop : (⊤ : Submodule ℚ K) ≤
          (Submodule.span ℚ (Set.range w)).comap K.subtype := by
        rw [← b.span_eq]
        apply Submodule.span_le.mpr
        rintro y ⟨i, rfl⟩
        change (b i : L) ∈ Submodule.span ℚ (Set.range w)
        rw [← hw i]
        exact Submodule.subset_span ⟨_, rfl⟩
      intro x hx
      exact htop (show (⟨x, hx⟩ : K) ∈ (⊤ : Submodule ℚ K) by trivial)
  · intro a i
    dsimp only [w]
    split_ifs with ha
    · exact hb ⟨a.val, ha⟩ i
    · simpa only [map_zero, Finsupp.zero_apply] using rationalHeightLE_zero hH

theorem bounded_submodule_spanning_mem_candidates (v : η → L)
    (hspan : Submodule.span ℚ (Set.range v) = K) {H : ℕ} (hH : 1 ≤ H)
    (hv : ∀ a i, RationalHeightLE (e.repr (v a) i) H) :
    K ∈ heightBoundedSubspaces e (Fintype.card ι) H := by
  obtain ⟨w, hw, hh⟩ := exists_bounded_submodule_ambient_spanning e K v hspan hH hv
  exact (mem_heightBoundedSubspaces e (Fintype.card ι) H K).mpr ⟨w, hw, hh⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonSubspaceFamily
namespace OAI

section

namespace Erdos3

open Module

theorem heightBoundedSubspaces_ncard_exp_bound
    {ι L : Type*} [Fintype ι] [AddCommGroup L] [Module ℚ L]
    (e : Basis ι ℚ L) (m : ℕ) {A : ℝ} (hA : 0 ≤ A) :
    ((heightBoundedSubspaces e m ⌈Real.exp A⌉₊).ncard : ℝ) ≤
      Real.exp (3 * (m : ℝ) * Fintype.card ι * (A + 2)) := by
  have hc := (finite_card_heightBoundedSubspaces e m ⌈Real.exp A⌉₊).2
  have he := rational_log_height_count_exp_bound (m * Fintype.card ι) hA
  have hr := (Nat.cast_le.mpr hc).trans he
  simpa only [Nat.cast_mul, mul_assoc] using hr

theorem exists_common_height_bounded_subspace_family
    {α ι κ L : Type*} [Fintype ι] [Fintype κ] [AddCommGroup L] [Module ℚ L]
    (e : Basis ι ℚ L) (S : Finset α) (hS : S.Nonempty)
    (K : α → κ → Submodule ℚ L) (m : ℕ) {A : ℝ} (hA : 0 ≤ A)
    (hK : ∀ a ∈ S, ∀ k, K a k ∈ heightBoundedSubspaces e m ⌈Real.exp A⌉₊) :
    ∃ a₀ ∈ S, ∃ T : Finset α, T ⊆ S ∧ a₀ ∈ T ∧ (∀ a ∈ T, K a = K a₀) ∧
      Real.exp (-(3 * (m : ℝ) * Fintype.card ι * (A + 2)) * Fintype.card κ) * S.card ≤
        (T.card : ℝ) := by
  classical
  let C := heightBoundedSubspaces e m ⌈Real.exp A⌉₊
  let : Fintype C := (finite_card_heightBoundedSubspaces e m ⌈Real.exp A⌉₊).1.fintype
  have hcard : Fintype.card C = C.ncard := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  have hcount : (Fintype.card C : ℝ) ≤ Real.exp (3 * (m : ℝ) * Fintype.card ι * (A + 2)) := by
    rw [hcard]
    exact heightBoundedSubspaces_ncard_exp_bound e m hA
  obtain ⟨labels, T, hsub, hnonempty, hsize, hconst⟩ := exists_large_fixed_choices S hS
    (fun a k (u : C) => K a k = u.val)
    (fun a ha k => ⟨⟨K a k, hK a ha k⟩, rfl⟩) hcount
  obtain ⟨a₀, ha₀⟩ := hnonempty
  refine ⟨a₀, hsub ha₀, T, hsub, ha₀, ?_, hsize⟩
  intro a ha
  funext k
  exact (hconst a ha k).trans (hconst a₀ ha₀ k).symm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeRationalRepresentatives
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_native_rational_representatives (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type*} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L s d) (p : ℝ),
      0 ≤ p → D.GeometryComplexityLE p → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∀ g : D.RealGroup, (D.basis.baseChange ℝ).equivFun g.coord ∈ realDenominatorGrid q →
          (∃ r : D.RealGroup,
            (∀ i, |(D.basis.baseChange ℝ).repr r.coord i| ≤ Real.exp ((p + C) ^ C)) ∧
            (D.basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid m ∧
            ∃ γ ∈ D.realLattice, g = r * γ) ∧
          (∃ r : D.RealGroup,
            (∀ i, |(D.basis.baseChange ℝ).repr r.coord i| ≤ Real.exp ((p + C) ^ C)) ∧
            (D.basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid m ∧
            ∃ γ ∈ D.realLattice, g = γ * r) := by
  obtain ⟨a, _, hrep⟩ := exists_realification_representatives_exp_bound s
  obtain ⟨b, _, hclosure⟩ := exists_real_bch_rational_closure s
  let X : Polynomial ℕ := Polynomial.X
  let P := (2 * X + 1 + Polynomial.C a) ^ a + (2 * X + 1 + Polynomial.C b) ^ b
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro L _ _ _ _ _ _ d D p hp hD q hq hqp
  let t := 2 * p + 1
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hpt : p ≤ t := by dsimp [t]; linarith
  let H := ⌈Real.exp p⌉₊
  have hH : (H : ℝ) ≤ Real.exp t := (ceil_exp_le_exp_add_one hp).trans
    (Real.exp_le_exp.mpr (by dsimp [t]; linarith))
  have hd : (Fintype.card (Fin d) : ℝ) ≤ t := by
    simpa only [Fintype.card_fin] using hD.1.trans hpt
  have hc : ∀ i j k, RationalHeightLE (lieStructureConstants D.basis i j k) H :=
    fun i j k => rationalHeightLE_ceil_exp (hD.2.2.1 i j k)
  have hprod : ((q * D.grid : ℕ) : ℝ) ≤ Real.exp t := by
    rw [Nat.cast_mul]
    calc
      _ ≤ Real.exp p * Real.exp p := mul_le_mul hqp hD.2.1 (Nat.cast_nonneg _) (Real.exp_pos _).le
      _ = Real.exp (2 * p) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by dsimp [t]; linarith)
  obtain ⟨m, hm, hmb, _, hmul, _⟩ := hclosure D.basis H t
    D.filtration.lowerCentralSeries_eq_bot ht hd hH hc (q * D.grid)
    (Nat.mul_pos hq D.grid_pos) hprod
  have hsum : (t + a) ^ a + (t + b) ^ b ≤ (p + C) ^ C := by
    simpa [P, X, t, Polynomial.eval₂_pow] using hbudget p hp
  have haC : (t + a) ^ a ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (pow_nonneg (add_nonneg ht (Nat.cast_nonneg b)) _)).trans hsum
  have hbC : (t + b) ^ b ≤ (p + C) ^ C :=
    (le_add_of_nonneg_left (pow_nonneg (add_nonneg ht (Nat.cast_nonneg a)) _)).trans hsum
  have hright (g : D.RealGroup) (hg : (D.basis.baseChange ℝ).equivFun g.coord ∈ realDenominatorGrid q) :
      ∃ r : D.RealGroup,
        (∀ i, |(D.basis.baseChange ℝ).repr r.coord i| ≤ Real.exp ((p + C) ^ C)) ∧
        (D.basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid m ∧
        ∃ γ ∈ D.realLattice, g = r * γ := by
    obtain ⟨r, hr, γ, hγ, heq⟩ := hrep D.basis D.filtration.lowerCentralSeries_eq_bot
      D.lattice D.grid H t D.grid_pos D.inner_grid hc ht hd hH
      (hD.2.1.trans (Real.exp_le_exp.mpr hpt)) g
    have hγgrid := realification_subgroup_grid D.basis D.lattice D.grid D.outer_grid
      γ⁻¹ (D.realLattice.inv_mem hγ)
    have hrgrid : (D.basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid m := by
      have h := hmul g γ⁻¹
        (realDenominatorGrid_subset_of_dvd hq (dvd_mul_right q D.grid) hg)
        (realDenominatorGrid_subset_of_dvd D.grid_pos (dvd_mul_left D.grid q) hγgrid)
      simpa only [heq, mul_inv_cancel_right] using h
    exact ⟨r, fun i => (hr i).trans (Real.exp_le_exp.mpr haC), hrgrid, γ, hγ, heq⟩
  refine ⟨m, hm, hmb.trans (Real.exp_le_exp.mpr hbC), ?_⟩
  intro g hg
  refine ⟨hright g hg, ?_⟩
  have hginv : (D.basis.baseChange ℝ).equivFun g⁻¹.coord ∈ realDenominatorGrid q := by
    change (D.basis.baseChange ℝ).equivFun (-g.coord) ∈ _
    rw [map_neg]
    exact realDenominatorGrid_neg q hg
  obtain ⟨r, hr, hrgrid, γ, hγ, heq⟩ := hright g⁻¹ hginv
  refine ⟨r⁻¹, ?_, ?_, γ⁻¹, D.realLattice.inv_mem hγ, ?_⟩
  · intro i
    simpa only [coord_inv, map_neg, Finsupp.neg_apply, abs_neg] using hr i
  · change (D.basis.baseChange ℝ).equivFun (-r.coord) ∈ _
    rw [map_neg]
    exact realDenominatorGrid_neg m hrgrid
  · have h := congrArg (fun z : D.RealGroup => z⁻¹) heq
    simpa only [inv_inv, mul_inv_rev] using h

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FixedObservableCorrelation
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_native_quotient_parameter_cover (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type*} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {d : ℕ}
      (D : RationalFilteredNilmanifold L s d) {p ε : ℝ},
      0 ≤ p → D.GeometryComplexityLE p → 0 < ε → 1 / ε ≤ Real.exp p →
      ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ ∃ centers : Fin n → D.Space,
        letI := D.metricSpace
        ∀ x : D.Space, ∃ j, dist x (centers j) ≤ ε := by
  obtain ⟨A, hA, hrep⟩ := exists_realification_representatives_exp_bound s
  obtain ⟨C₀, _, hsize⟩ := exists_bchBoxCover_count_budget s A
  refine ⟨(A + 1) + C₀ + 2, by omega, ?_⟩
  intro L _ _ _ _ _ _ d D p ε hp hD hε hεinv
  let H := ⌈Real.exp p⌉₊
  let B : ℝ≥0 := ⟨Real.exp (((p + 1) + A) ^ A), (Real.exp_pos _).le⟩
  have hB : 1 ≤ B := Real.one_le_exp (pow_nonneg (by positivity) _)
  have hh : ∀ i j k, RationalHeightLE (lieStructureConstants D.basis i j k) H :=
    fun i j k => rationalHeightLE_ceil_exp (hD.2.2.1 i j k)
  have hr := hrep D.basis D.filtration.lowerCentralSeries_eq_bot D.lattice D.grid H (p + 1)
    D.grid_pos D.inner_grid hh (by linarith)
    (by simpa only [Fintype.card_fin] using hD.1.trans (show p ≤ p + 1 by linarith))
    (ceil_exp_le_exp_add_one hp) (hD.2.1.trans (Real.exp_le_exp.mpr (by linarith)))
  obtain ⟨c, hc⟩ := D.exists_native_coordinateBox_cover hh B hB hε
  let t := p + (A + 1 : ℕ)
  have hpt : p ≤ t := le_add_of_nonneg_right (Nat.cast_nonneg _)
  have hp1t : p + 1 ≤ t := by dsimp [t]; push_cast; linarith
  have hBt : (B : ℝ) ≤ Real.exp ((t + 2) ^ A) := by
    apply Real.exp_le_exp.mpr
    apply pow_le_pow_left₀ (by positivity)
    dsimp [t]
    push_cast
    linarith
  have hcount := hsize d H B (p := t) (hp.trans hpt) (hD.1.trans hpt)
    ((ceil_exp_le_exp_add_one hp).trans (Real.exp_le_exp.mpr hp1t)) hBt hε
    (hεinv.trans (Real.exp_le_exp.mpr hpt))
  have hshift : (t + C₀) ^ C₀ ≤ (p + ((A + 1) + C₀ + 2 : ℕ)) ^ ((A + 1) + C₀ + 2) :=
    shifted_center_power_bound (A + 1) C₀ hp
  refine ⟨_, by positivity, hcount.trans (Real.exp_le_exp.mpr hshift),
    fun j => QuotientGroup.mk (c j).val, ?_⟩
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
    (D.basis.baseChange ℝ)
  let := D.metricSpace
  have hproj : LipschitzWith 1 (QuotientGroup.mk : D.RealGroup → D.Space) :=
    quotientMetricSpace_lipschitz_mk (D.basis.baseChange ℝ) D.realLattice D.realLattice_closed_discrete.1
  intro x
  induction x using Quotient.inductionOn with
  | h g =>
    obtain ⟨r, hr, γ, hγ, hg⟩ := hr g
    obtain ⟨j, hj⟩ := hc ⟨r, hr⟩
    refine ⟨j, ?_⟩
    change dist (QuotientGroup.mk g : D.Space) (QuotientGroup.mk (c j).val) ≤ ε
    have heq : (QuotientGroup.mk g : D.Space) = QuotientGroup.mk r := by
      rw [hg]
      exact QuotientGroup.mk_mul_of_mem r (show γ ∈ D.realLattice from hγ)
    rw [heq]
    have hdist : dist (QuotientGroup.mk r : D.Space) (QuotientGroup.mk (c j).val) ≤ dist r (c j).val := by
      simpa only [NNReal.coe_one, one_mul] using hproj.dist_le_mul r (c j).val
    exact hdist.trans hj

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct NNReal

theorem exists_native_positive_partition (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type*} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {d : ℕ}
      (D : RationalFilteredNilmanifold L s d) {p ρ : ℝ},
      0 ≤ p → D.GeometryComplexityLE p → 0 < ρ →
      1 / ρ ≤ Real.exp ((p + 2) ^ a) →
      letI := D.metricSpace
      ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ K : ℝ≥0, (K : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ ψ : Fin n → D.Space → ℝ,
          (∀ i x, 0 ≤ ψ i x ∧ ψ i x ≤ 1) ∧
          (∀ x, ∑ i, ψ i x = 1) ∧
          (∀ i, LipschitzWith K (ψ i)) ∧
          ∀ i x y, 0 < ψ i x → 0 < ψ i y → dist x y ≤ ρ := by
  obtain ⟨A, _, hcover⟩ := exists_native_quotient_parameter_cover s
  let X : Polynomial ℕ := Polynomial.X
  let T := X + (X + 2) ^ a + 4
  let B := T + (T + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (2 * B + 2)
  refine ⟨C, hC, ?_⟩
  intro L _ _ _ _ _ _ d D p ρ hp hD hρ hρinv
  let t := p + (p + 2) ^ a + 4
  have hpt : p ≤ t := by dsimp [t]; linarith [pow_nonneg (show 0 ≤ p + 2 by linarith) a]
  have ht : 0 ≤ t := hp.trans hpt
  let r : ℝ≥0 := ⟨ρ / 4, (div_pos hρ (by norm_num)).le⟩
  have hr : 0 < r := div_pos hρ (by norm_num)
  have hrinv : 1 / (r : ℝ) ≤ Real.exp t := by
    calc
      _ = 4 * (1 / ρ) := by change 1 / (ρ / 4) = 4 * (1 / ρ); ring
      _ ≤ Real.exp 4 * Real.exp ((p + 2) ^ a) :=
        mul_le_mul (by linarith [Real.add_one_le_exp (4 : ℝ)]) hρinv
          (by positivity) (Real.exp_pos _).le
      _ = Real.exp (4 + (p + 2) ^ a) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by dsimp [t]; linarith)
  obtain ⟨n, hn, hnb, c, hc⟩ := hcover D ht (hD.mono D hpt) (show 0 < (r : ℝ) from hr) hrinv
  let b := t + (t + A) ^ A
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have htb : t ≤ b := le_add_of_nonneg_right (pow_nonneg (by positivity) _)
  have hAb : (t + A) ^ A ≤ b := le_add_of_nonneg_left ht
  have hcost : 2 * b + 2 ≤ (p + C) ^ C := by
    simpa [B, T, X, b, t, Polynomial.eval₂_pow] using hbudget p hp
  have hbC : b ≤ (p + C) ^ C := by linarith
  let K : ℝ≥0 := (2 * n + 1) / r
  have hK : (K : ℝ) ≤ Real.exp ((p + C) ^ C) :=
    (metricPartition_constant_le_exp n r hb
      (hnb.trans (Real.exp_le_exp.mpr hAb))
      (hrinv.trans (Real.exp_le_exp.mpr htb))).trans (Real.exp_le_exp.mpr hcost)
  let := D.metricSpace
  let ψ := metricTentPartition c r
  refine ⟨n, hn, hnb.trans (Real.exp_le_exp.mpr (hAb.trans hbC)), K, hK, ψ,
    fun i x => ⟨metricTentPartition_nonneg c r i x, metricTentPartition_le_one c hr hc i x⟩,
    sum_metricTentPartition c hr hc, fun i => ?_, ?_⟩
  · simpa only [Fintype.card_fin] using lipschitz_metricTentPartition c hr hc i
  · intro i x y hx hy
    have hxc : dist x (c i) < 2 * (r : ℝ) := by
      by_contra h
      have hz := metricTentPartition_zero_of_far c r i x (le_of_not_gt h)
      change 0 < metricTentPartition c r i x at hx
      linarith
    have hyc : dist y (c i) < 2 * (r : ℝ) := by
      by_contra h
      have hz := metricTentPartition_zero_of_far c r i y (le_of_not_gt h)
      change 0 < metricTentPartition c r i y at hy
      linarith
    have htri := dist_triangle x (c i) y
    rw [dist_comm (c i) y] at htri
    change dist x (c i) < 2 * (ρ / 4) at hxc
    change dist y (c i) < 2 * (ρ / 4) at hyc
    linarith

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.ProductFrequencyKernel
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct BigOperators

variable {ι : Type*} [Fintype ι] {L : ι → Type*}
    [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]

theorem realify_piFrequency (eta : ∀ i, L i →ₗ[ℚ] ℚ) (x : ℝ ⊗[ℚ] (∀ i, L i)) :
    realifyFunctional (piFrequency eta) x =
      ∑ i, realifyFunctional (eta i) (realificationLieHom (liePiEval i) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    simp only [realifyFunctional_tmul, piFrequency_apply, Rat.cast_sum,
      realificationLieHom_tmul, liePiEval_apply, Finset.mul_sum]
  | add x y hx hy => simp only [map_add, hx, hy, Finset.sum_add_distrib]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.RationalFrequencyHeight
namespace OAI

section

namespace Erdos3

open Module
open scoped BigOperators

variable {L ι κ : Type*} [AddCommGroup L] [Module ℚ L]

theorem basisFrequency_logHeight_le (e : Basis κ ℚ L) (b : Basis ι ℚ L)
    (S : Set ι) [Fintype S] (N : ℕ) (hN : 0 < N) (n : S → ℤ)
    {p : ℝ} (hp : 0 ≤ p) (hd : (Fintype.card S : ℝ) ≤ p)
    (hNp : (N : ℝ) ≤ Real.exp p) (hn : ∀ j, (|n j| : ℝ) ≤ Real.exp p)
    (hb : ∀ i j, rationalLogHeight (b.repr (e i) j) ≤ p) (i : κ) :
    rationalLogHeight (basisFrequency b S N n (e i)) ≤ (p + 2) ^ 4 := by
  classical
  let H := ⌈Real.exp p⌉₊
  have hH : (H : ℝ) ≤ Real.exp (p + 1) := ceil_exp_le_exp_add_one hp
  have hfrac (j : S) : RationalHeightLE ((n j : ℚ) / (N : ℚ)) H := by
    have ha : (n j).natAbs ≤ H := by
      apply (Nat.cast_le (α := ℝ)).mp
      simpa only [Nat.cast_natAbs, Int.cast_abs] using (hn j).trans (Nat.le_ceil (Real.exp p))
    have hbN : (N : ℤ).natAbs ≤ H := by
      simpa only [Int.natAbs_natCast] using
        (Nat.cast_le.mp (hNp.trans (Nat.le_ceil (Real.exp p))) : N ≤ H)
    simpa only [Int.cast_natCast] using
      rationalHeightLE_fraction (n j) (N : ℤ) (by exact_mod_cast hN.ne') ha hbN
  have hterms (j : S) :
      RationalHeightLE (((n j : ℚ) / (N : ℚ)) * b.repr (e i) j) (H * H) :=
    (hfrac j).mul (rationalHeightLE_ceil_exp (hb i j))
  have hHH : ((H * H : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 2) := by
    rw [Nat.cast_mul]
    calc
      _ ≤ Real.exp (p + 1) * Real.exp (p + 1) := by gcongr
      _ = Real.exp (2 * p + 2) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [sq_nonneg p])
  rw [basisFrequency_apply]
  apply (rationalLogHeight_le_iff _ _).mpr
  simpa only [show (2 + 1 + 1 : ℕ) = 4 from rfl] using
    rational_sum_exp_height _ hterms hp 2 1 hHH (by simpa using hd.trans (by linarith : p ≤ p + 2))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NiltestVerticalBounds
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L s d)

theorem exists_controlled_adapted_basis {p : ℝ} (hp : 0 ≤ p) (hD : D.GeometryComplexityLE p) :
    ∃ (b : Basis (Fin (finrank ℚ L)) ℚ L) (w : Fin (finrank ℚ L) → ℕ) (N : ℕ),
      Monotone w ∧ IsCentralLieBasis b ∧
      (∀ i, D.filtration.layer i = Submodule.span ℚ (b '' {j | i ≤ w j})) ∧
      (∀ j i, rationalLogHeight (D.basis.repr (b j) i) ≤ p + 1) ∧
      (∀ i j, rationalLogHeight (b.repr (D.basis i) j) ≤ (p + 3) ^ 5) ∧
      (∀ i j k, rationalLogHeight (lieStructureConstants b i j k) ≤ (p + 3) ^ 11) ∧
      0 < N ∧ (N : ℝ) ≤ Real.exp ((p + 3) ^ 9) ∧
      scaledIntegerGrid N ⊆ bchSubgroupCoordinates b D.lattice ∧
      bchSubgroupCoordinates b D.lattice ⊆ denominatorGrid N := by
  let H := ⌈Real.exp p⌉₊
  have hH : 1 ≤ H := one_le_ceil_exp p
  have hHp : (H : ℝ) ≤ Real.exp (p + 1) := ceil_exp_le_exp_add_one hp
  have hp1 : 0 ≤ p + 1 := by linarith
  have hdp : (Fintype.card (Fin d) : ℝ) ≤ p + 1 := by
    simpa only [Fintype.card_fin] using hD.1.trans (show p ≤ p + 1 by linarith)
  have hlp : (D.grid : ℝ) ≤ Real.exp (p + 1) :=
    hD.2.1.trans (Real.exp_le_exp.mpr (by linarith))
  obtain ⟨b, w, N, hw, hc, hlayers, hb, hbinv, hbracket, hN, hNp, hin, hout⟩ :=
    D.filtration.exists_adapted_basis_and_grid D.basis (fun i => D.layerBasis i)
      (fun i => (D.layerBasis i).span_eq) D.lattice hH D.grid_pos
      (fun i j k => rationalHeightLE_ceil_exp (hD.2.2.2 i j k))
      (fun i j k => rationalHeightLE_ceil_exp (hD.2.2.1 i j k))
      D.inner_grid D.outer_grid hp1 hdp hHp hlp
  have hdr : (finrank ℚ L : ℝ) ≤ p + 1 := by
    simpa only [finrank_eq_card_basis D.basis] using hdp
  have hshift : p + 1 + 2 = p + 3 := by ring
  have hinvBudget : (rationalSolveHeight (finrank ℚ L) H : ℝ) ≤ Real.exp ((p + 3) ^ 5) := by
    simpa only [hshift] using rationalSolveHeight_le_budget (finrank ℚ L) H hp1 hdr hHp
  refine ⟨b, w, N, hw, hc, hlayers, ?_, ?_, ?_, hN, ?_, hin, hout⟩
  · exact fun j i => rationalLogHeight_le_of_height (hb j i) hHp
  · exact fun i j => rationalLogHeight_le_of_height (hbinv i j) hinvBudget
  · intro i j k
    apply (rationalLogHeight_le_iff _ _).mpr
    simpa only [hshift] using hbracket i j k
  · simpa only [hshift] using hNp

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L s d)
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

theorem exists_controlled_central_actions {p : ℝ} (hp : 0 ≤ p) (hD : D.GeometryComplexityLE p) :
    letI := D.metricSpace
    ∃ (b : Basis (Fin (finrank ℚ L)) ℚ L) (w : Fin (finrank ℚ L) → ℕ) (N : ℕ),
      (∀ i, D.filtration.layer i = Submodule.span ℚ (b '' {j | i ≤ w j})) ∧
      (∀ j i, rationalLogHeight (D.basis.repr (b j) i) ≤ p + 1) ∧
      (∀ i j, rationalLogHeight (b.repr (D.basis i) j) ≤ (p + 3) ^ 5) ∧
      0 < N ∧ (N : ℝ) ≤ Real.exp ((p + 3) ^ 9) ∧
      scaledIntegerGrid N ⊆ bchSubgroupCoordinates b D.lattice ∧
      bchSubgroupCoordinates b D.lattice ⊆ denominatorGrid N ∧
      ∃ A : {j // s ≤ w j} → CircleFourier.IsometricCircleAction D.Space,
        (∀ i j, (A i).Commutes (A j)) ∧
        (∀ j (t : CircleFourier.Circle) x,
          dist ((A j).act t x) x ≤ Real.exp ((p + 3) ^ 9 + 2 * p + 2) * ‖t‖) ∧
        ∀ j (r : ℝ) x, (A j).act (r : CircleFourier.Circle) x =
          realBCHLine (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
            ((N : ℝ) • (b.baseChange ℝ) j) r • x := by
  let := D.metricSpace
  obtain ⟨b, w, N, _, _, hlayers, hb, hbinv, _, hN, hNb, hin, hout⟩ :=
    D.exists_controlled_adapted_basis hp hD
  have hcentral (j : {j // s ≤ w j}) (z : L) : ⁅b j, z⁆ = 0 := by
    apply D.filtration.top_layer_central
    rw [hlayers s]
    exact Submodule.subset_span ⟨j, j.property, rfl⟩
  let A : {j // s ≤ w j} → CircleFourier.IsometricCircleAction D.Space := fun j =>
    realifiedCentralBasisAction D.basis b D.lattice D.grid D.grid_pos D.outer_grid N hin j (hcentral j)
  have hbabs (j : Fin (finrank ℚ L)) (i : Fin d) :
      |(D.basis.repr (b j) i : ℝ)| ≤ Real.exp (p + 2) := by
    have hh := (rationalHeightLE_ceil_exp (hb j i)).abs_real_le
    have hceil := ceil_exp_le_exp_add_one (show 0 ≤ p + 1 by linarith)
    exact hh.trans (by simpa only [show p + 1 + 1 = p + 2 by ring] using hceil)
  have hcost : ((d : ℝ) + 1) * ((N : ℝ) * Real.exp (p + 2)) ≤
      Real.exp ((p + 3) ^ 9 + 2 * p + 2) := by
    have hd : (d : ℝ) + 1 ≤ Real.exp p :=
      (by linarith [hD.1] : (d : ℝ) + 1 ≤ p + 1).trans (Real.add_one_le_exp p)
    calc
      _ ≤ Real.exp p * (Real.exp ((p + 3) ^ 9) * Real.exp (p + 2)) := by gcongr
      _ = _ := by simp only [← Real.exp_add]; congr 1; ring
  refine ⟨b, w, N, hlayers, hb, hbinv, hN, hNb, hin, hout, A, ?_, ?_, ?_⟩
  · intro i j
    exact realifiedCentralBasisAction_commutes D.basis b D.lattice D.grid D.grid_pos D.outer_grid
      N hin i j (hcentral i) (hcentral j)
  · intro j t x
    have hh := realifiedCentralBasisAction_displacement D.basis b D.lattice D.grid D.grid_pos D.outer_grid
      N hin j (hcentral j) (Real.exp_nonneg (p + 2)) (hbabs j) t x
    simp only [Fintype.card_fin] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right hcost (norm_nonneg t))
  · intro j r x
    exact realifiedCentralBasisAction_act_coe D.basis b D.lattice D.grid D.grid_pos D.outer_grid
      N hin j (hcentral j) r x

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.FixedAdaptedSymbolFactorizationBasis
namespace OAI

section

namespace Erdos3

open Module

theorem rational_basis_coordinates_logHeight
    {ι κ V : Type*} [Fintype ι] [AddCommGroup V] [Module ℚ V]
    (b : Basis ι ℚ V) (c : Basis κ ℚ V) {H : ℕ} {p : ℝ}
    (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p)
    (hentries : ∀ i j, RationalHeightLE (c.repr (b i) j) H)
    (x : V) (hx : ∀ i, rationalLogHeight (b.repr x i) ≤ p) (j : κ) :
    rationalLogHeight (c.repr x j) ≤ (p + 2) ^ 4 := by
  classical
  let K := ⌈Real.exp p⌉₊
  have hK : (K : ℝ) ≤ Real.exp (p + 1) := ceil_exp_le_exp_add_one hp
  have hKH : ((K * H : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 2) := by
    rw [Nat.cast_mul]
    calc
      _ ≤ Real.exp (p + 1) * Real.exp p :=
        mul_le_mul hK hH (Nat.cast_nonneg H) (Real.exp_nonneg _)
      _ = Real.exp (2 * p + 1) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [sq_nonneg p])
  have hcoord := linearMap_coordinate_height b c (LinearMap.id : V →ₗ[ℚ] V)
    hentries x (fun i => rationalHeightLE_ceil_exp (hx i)) j
  have hcost := rational_sum_cost_le_exp (Fintype.card ι) (K * H) hp 2 1 hKH
    (by simpa only [pow_one] using hι.trans (show p ≤ p + 2 by linarith))
  exact rationalLogHeight_le_of_height hcoord hcost

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.NativeRankBudget
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

theorem exists_canonical_rank_basis_budget (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type*} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      (D : RationalFilteredNilmanifold L s d) {p : ℝ},
      0 ≤ p → D.GeometryComplexityLE p → ∀ i r : ℕ, i ≤ s →
      ∃ b : Basis (Fin (finrank ℚ (D.filtration.rankLayer i r))) ℚ (D.filtration.rankLayer i r),
        (finrank ℚ (D.filtration.rankLayer i r) : ℝ) ≤ p ∧
        ∀ j k, rationalLogHeight (D.basis.repr (b j : L) k) ≤ (p + C) ^ C := by
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((Polynomial.X + 3 : Polynomial ℕ) ^ (6 * s + 2))
  refine ⟨C, hC, ?_⟩
  intro L _ _ d D p hp hD i r hi
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  have hcost : (p + 3) ^ (6 * s + 2) ≤ (p + C) ^ C := by
    simpa [Polynomial.eval₂_pow] using hbudget p hp
  have htree : (lieTreeHeight d ⌈Real.exp p⌉₊ s : ℝ) ≤ Real.exp ((p + 3) ^ (6 * s + 2)) := by
    simpa only [add_assoc, show (1 : ℝ) + 2 = 3 by norm_num] using
      lieTreeHeight_le_exp d ⌈Real.exp p⌉₊ s (p := p + 1) (by linarith)
        (hD.1.trans (by linarith)) (ceil_exp_le_exp_add_one hp)
  obtain ⟨b, hb⟩ := D.exists_rankLayer_basis_height
    (fun a b c => rationalHeightLE_ceil_exp (hD.2.2.1 a b c))
    (fun a b c => rationalHeightLE_ceil_exp (hD.2.2.2 a b c)) i r hi
  refine ⟨b, ?_, fun j k => rationalLogHeight_le_of_height (hb j k)
    (htree.trans (Real.exp_le_exp.mpr hcost))⟩
  have hdim : finrank ℚ (D.filtration.rankLayer i r) ≤ d := by
    simpa only [finrank_eq_card_basis D.basis, Fintype.card_fin] using
      (D.filtration.rankLayer i r).finrank_le
  exact (Nat.cast_le.mpr hdim).trans hD.1

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ControlledIntegralGrid
namespace OAI

section

namespace Erdos3

open Module

theorem exists_controlled_integral_grid (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (L ι : Type*) [LieRing L] [LieAlgebra ℚ L] [Fintype ι]
      (e : Basis ι ℚ L) (_hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
      (l : ℕ), 0 < l → ∀ (p : ℝ), 0 ≤ p → (Fintype.card ι : ℝ) ≤ p →
      (l : ℝ) ≤ Real.exp p →
      (∀ i j k, rationalLogHeight (lieStructureConstants e i j k) ≤ p) →
      p ≤ (p + C) ^ C ∧ ∃ B : ℕ, 0 < B ∧ l ∣ B ∧ (B : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∀ x ∈ coordinateGridModule e B, ∀ y ∈ coordinateGridModule e B,
          lieBCH s x y ∈ coordinateGridModule e B := by
  let K := bchIntegralDenominatorBound s
  let Q : Polynomial ℕ := Polynomial.C K + (Polynomial.X + 1) * Polynomial.X ^ 3 + Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (Q + Polynomial.X)
  refine ⟨C, hC, ?_⟩
  intro L ι _ _ _ e hnil l hl p hp hd hlp hc
  let H := ⌈Real.exp p⌉₊
  let E := (K : ℝ) + (p + 1) * p ^ 3 + p
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have htotal : E + p ≤ (p + C) ^ C := by
    simpa [Q, E, Polynomial.eval₂_pow] using hbudget p hp
  have hpC : p ≤ (p + C) ^ C := (le_add_of_nonneg_left hE).trans htotal
  have hEC : E ≤ (p + C) ^ C := (le_add_of_nonneg_right hp).trans htotal
  have hH : (H : ℝ) ≤ Real.exp (p + 1) := ceil_exp_le_exp_add_one hp
  have hn3 : ((Fintype.card ι ^ 3 : ℕ) : ℝ) ≤ p ^ 3 := by
    rw [Nat.cast_pow]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) hd _
  have hHpow : (H : ℝ) ^ (Fintype.card ι ^ 3) ≤ Real.exp ((p + 1) * p ^ 3) := by
    apply (pow_le_pow_left₀ (Nat.cast_nonneg H) hH _).trans
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    exact (mul_le_mul_of_nonneg_right hn3 (by linarith)).trans_eq (mul_comm _ _)
  have hK : (K : ℝ) ≤ Real.exp (K : ℝ) :=
    (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _)
  obtain ⟨B, hB, hdiv, hbound, hstable⟩ := exists_bch_stable_integral_grid e hnil l hl
    (fun i j k => rationalHeightLE_ceil_exp (hc i j k))
  have hBexp : (B : ℝ) ≤ Real.exp E := by
    calc
      _ ≤ (K : ℝ) * (H : ℝ) ^ (Fintype.card ι ^ 3) * (l : ℝ) := by exact_mod_cast hbound
      _ ≤ Real.exp (K : ℝ) * Real.exp ((p + 1) * p ^ 3) * Real.exp p :=
        mul_le_mul (mul_le_mul hK hHpow (by positivity) (Real.exp_nonneg _)) hlp
          (Nat.cast_nonneg l) (by positivity)
      _ = Real.exp E := by rw [← Real.exp_add, ← Real.exp_add]
  exact ⟨hpC, B, hB, hdiv, hBexp.trans (Real.exp_le_exp.mpr hEC), hstable⟩

end Erdos3

end

end OAI
end


