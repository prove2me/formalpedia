-- Prove2me | solution 1 for Algebra.PatchingDatum.nonempty_of_exists_presentation_of_free
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/101e52f3-4da6-54e9-961c-34594fc518f0

import Definitions.Def_Algebra_PatchingDatum
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.Algebra.Ring.GeomSum
import Theorems.Thm_MvPowerSeries_exists_algHom_apply_X_eq
import Theorems.Thm_MvPowerSeries_isAdicComplete_maximalIdeal
import Theorems.Thm_MvPowerSeries_exists_coords_of_quotient_span_finite_free
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_PatchingDatum_nonempty_of_exists_presentation_of_free

universe u

namespace FrobDictPTAUT

open IsLocalRing

section Trivial

variable {𝒪 : Type} [CommRing 𝒪] (ℓ r : ℕ) (R : Type) [CommRing R] [Algebra 𝒪 R]
  (M : Type) [AddCommGroup M] [Module R M]

noncomputable def trivialLevel [Subsingleton R] (J : Ideal (MvPowerSeries (Fin r) 𝒪)) : Algebra.PatchingLevel 𝒪 r R M J where
  N := PUnit
  φ := AlgHom.id 𝒪 _
  ψ :=
    { toFun := fun _ => 0
      map_one' := Subsingleton.elim _ _
      map_mul' := fun _ _ => Subsingleton.elim _ _
      map_zero' := rfl
      map_add' := fun _ _ => (zero_add _).symm
      commutes' := fun _ => Subsingleton.elim _ _ }
  ψ_surjective := fun x => ⟨0, Subsingleton.elim _ _⟩
  ψ_φ_X := fun _ => rfl
  π := 0
  π_smul := fun _ _ => by
    haveI : Subsingleton M := Module.subsingleton R M
    exact Subsingleton.elim _ _
  π_surjective := fun x => ⟨PUnit.unit, by
    haveI : Subsingleton M := Module.subsingleton R M
    exact Subsingleton.elim _ _⟩
  ker_π := fun x => by
    haveI : Subsingleton M := Module.subsingleton R M
    refine ⟨fun _ => ?_, fun _ => Subsingleton.elim _ _⟩
    rw [Subsingleton.elim x 0]
    exact Submodule.zero_mem _
  d := 0
  b := Fin.elim0
  b_span := fun x => ⟨Fin.elim0, Subsingleton.elim _ _⟩
  b_rel := fun c => ⟨fun _ i => i.elim0, fun _ => Subsingleton.elim _ _⟩

end Trivial

section Main

variable {𝒪 : Type} [CommRing 𝒪] {r : ℕ} {R : Type} [CommRing R] [Algebra 𝒪 R]

local notation "B" => MvPowerSeries (Fin r) 𝒪

structure Pres (𝒪 : Type) [CommRing 𝒪] (r : ℕ) (R : Type) [CommRing R] [Algebra 𝒪 R] where
  f : Fin r → MvPowerSeries (Fin r) 𝒪
  φ : MvPowerSeries (Fin r) 𝒪 →ₐ[𝒪] MvPowerSeries (Fin r) 𝒪
  hφ : ∀ i, φ (MvPowerSeries.X i) = f i
  ψ : MvPowerSeries (Fin r) 𝒪 →ₐ[𝒪] R
  ψ_surjective : Function.Surjective ψ
  ψ_eq_zero_iff : ∀ x, ψ x = 0 ↔ x ∈ Ideal.span (Set.range f)
  e : ℕ
  β : Fin e → MvPowerSeries (Fin r) 𝒪
  hspan : ∀ x : MvPowerSeries (Fin r) 𝒪, ∃ c : Fin e → MvPowerSeries (Fin r) 𝒪, x = ∑ j, φ (c j) * β j
  hrel : ∀ c : Fin e → MvPowerSeries (Fin r) 𝒪, ∑ j, φ (c j) * β j = 0 → ∀ j, c j = 0

namespace Pres

variable (P : Pres 𝒪 r R)

theorem coords_unique {c c' : Fin P.e → B} (h : ∑ j, P.φ (c j) * P.β j = ∑ j, P.φ (c' j) * P.β j) : c = c' := by
  funext j
  have h0 : ∑ j, P.φ ((c - c') j) * P.β j = 0 := by
    simp only [Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib, h, sub_self]
  exact sub_eq_zero.mp (P.hrel _ h0 j)

def coordIdeal (J : Ideal B) : Ideal B where
  carrier := {y | ∀ c : Fin P.e → B, y = ∑ j, P.φ (c j) * P.β j → ∀ j, c j ∈ J}
  zero_mem' := fun c hc j => by
    have := P.hrel c hc.symm j
    rw [this]; exact J.zero_mem
  add_mem' := by
    intro y₁ y₂ h₁ h₂ c hc j
    obtain ⟨c₁, hc₁⟩ := P.hspan y₁
    obtain ⟨c₂, hc₂⟩ := P.hspan y₂
    have hsum : ∑ j, P.φ ((c₁ + c₂) j) * P.β j = ∑ j, P.φ (c j) * P.β j := by
      rw [← hc]
      simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib, hc₁, hc₂]
    have := P.coords_unique hsum
    rw [← this]
    exact J.add_mem (h₁ c₁ hc₁ j) (h₂ c₂ hc₂ j)
  smul_mem' := by
    intro b y hy c hc l
    obtain ⟨c₀, hc₀⟩ := P.hspan y
    have hc₀J : ∀ j, c₀ j ∈ J := hy c₀ hc₀
    choose d hd using fun j => P.hspan (b * P.β j)

    have hexp : ∑ l, P.φ ((fun l => ∑ j, c₀ j * d j l) l) * P.β l = ∑ l, P.φ (c l) * P.β l := by
      rw [← hc]
      change (∑ l, P.φ (∑ j, c₀ j * d j l) * P.β l) = b * y
      rw [hc₀, Finset.mul_sum]
      simp only [map_sum, map_mul, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_left_comm, hd j, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      ring
    have := P.coords_unique hexp
    rw [← this]
    exact Ideal.sum_mem _ fun j _ => J.mul_mem_right _ (hc₀J j)

theorem sum_mem_map_iff (J : Ideal B) (c : Fin P.e → B) :
    ∑ j, P.φ (c j) * P.β j ∈ J.map (P.φ : B →+* B) ↔ ∀ j, c j ∈ J := by
  constructor
  · intro h
    have hle : J.map (P.φ : B →+* B) ≤ P.coordIdeal J := by
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      rw [Ideal.mem_comap]
      intro c' hc' j
      obtain ⟨u, hu⟩ := P.hspan 1
      have h1 : ∑ j, P.φ ((fun j => a * u j) j) * P.β j = ∑ j, P.φ (c' j) * P.β j := by
        rw [← hc']
        change (∑ j, P.φ (a * u j) * P.β j) = P.φ a
        simp only [map_mul, mul_assoc, ← Finset.mul_sum, ← hu, mul_one]
      have := P.coords_unique h1
      rw [← this]
      exact J.mul_mem_right _ ha
    exact hle h c rfl
  · intro h
    exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (h j))

theorem map_le_span {J : Ideal B} (hJ : J ≤ Ideal.span (Set.range (MvPowerSeries.X : Fin r → B))) :
    J.map (P.φ : B →+* B) ≤ Ideal.span (Set.range P.f) := by
  refine (Ideal.map_mono hJ).trans ?_
  rw [Ideal.map_span, Ideal.span_le]
  rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
  change P.φ (MvPowerSeries.X i) ∈ Ideal.span (Set.range P.f)
  rw [P.hφ]
  exact Ideal.subset_span ⟨i, rfl⟩

end Pres

end Main

section Level

variable {𝒪 : Type} [CommRing 𝒪] {r : ℕ} {R : Type} [CommRing R] [Algebra 𝒪 R]
  {M : Type} [AddCommGroup M] [Module R M]

local notation "B" => MvPowerSeries (Fin r) 𝒪
local notation "J₀" => Ideal.span (Set.range (MvPowerSeries.X : Fin r → MvPowerSeries (Fin r) 𝒪))

namespace Pres

variable (P : Pres 𝒪 r R)

noncomputable abbrev K (J : Ideal (MvPowerSeries (Fin r) 𝒪)) : Ideal (MvPowerSeries (Fin r) 𝒪) :=
  J.map (P.φ : MvPowerSeries (Fin r) 𝒪 →+* MvPowerSeries (Fin r) 𝒪)

theorem ψ_eq_zero_of_mem_K {J : Ideal B} (hJ : J ≤ J₀) {x : B} (hx : x ∈ P.K J) : P.ψ x = 0 :=
  (P.ψ_eq_zero_iff x).mpr (P.map_le_span hJ hx)

noncomputable def ψbar (J : Ideal B) (hJ : J ≤ J₀) : B ⧸ P.K J →+* R :=
  Ideal.Quotient.lift (P.K J) (P.ψ : B →+* R) fun _ hx => P.ψ_eq_zero_of_mem_K hJ hx

@[scoped simp] theorem ψbar_mk (J : Ideal B) (hJ : J ≤ J₀) (x : B) :
    P.ψbar J hJ (Ideal.Quotient.mk _ x) = P.ψ x := rfl

theorem ψbar_smul (J : Ideal B) (hJ : J ≤ J₀) (g : B) (q : B ⧸ P.K J) :
    P.ψbar J hJ (g • q) = P.ψ g * P.ψbar J hJ q := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
  change P.ψbar J hJ (Ideal.Quotient.mk _ (g * x)) = P.ψ g * P.ψbar J hJ (Ideal.Quotient.mk _ x)
  rw [ψbar_mk, ψbar_mk, map_mul]

theorem ψbar_eq_zero_iff (J : Ideal B) (hJ : J ≤ J₀) (q : B ⧸ P.K J) :
    P.ψbar J hJ q = 0 ↔ q ∈ (Ideal.span (Set.range P.f) • (⊤ : Submodule B (B ⧸ P.K J))) := by
  constructor
  · intro h
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
    rw [ψbar_mk, P.ψ_eq_zero_iff x] at h
    have hx1 : (Ideal.Quotient.mk (P.K J) x : B ⧸ P.K J) = x • (Ideal.Quotient.mk (P.K J) 1) := by
      rw [← Ideal.Quotient.mk_eq_mk, ← Ideal.Quotient.mk_eq_mk, ← Submodule.Quotient.mk_smul, smul_eq_mul,
        mul_one]
    rw [hx1]
    exact Submodule.smul_mem_smul h Submodule.mem_top
  · intro hq
    refine Submodule.smul_induction_on hq (fun a ha n _ => ?_) (fun y z hy hz => ?_)
    · rw [ψbar_smul, (P.ψ_eq_zero_iff a).mpr ha, zero_mul]
    · rw [map_add, hy, hz, add_zero]

variable {m : ℕ} (bm : Module.Basis (Fin m) R M)

noncomputable def πLevel (J : Ideal B) (hJ : J ≤ J₀) : (Fin m → B ⧸ P.K J) →+ M where
  toFun v := ∑ i, P.ψbar J hJ (v i) • bm i
  map_zero' := by simp
  map_add' v w := by simp [add_smul, Finset.sum_add_distrib]

theorem πLevel_apply (J : Ideal B) (hJ : J ≤ J₀) (v : Fin m → B ⧸ P.K J) :
    P.πLevel bm J hJ v = ∑ i, P.ψbar J hJ (v i) • bm i := rfl

theorem πLevel_smul (J : Ideal B) (hJ : J ≤ J₀) (g : B) (v : Fin m → B ⧸ P.K J) :
    P.πLevel bm J hJ (g • v) = P.ψ g • P.πLevel bm J hJ v := by
  simp only [πLevel_apply, Pi.smul_apply, ψbar_smul, Finset.smul_sum, mul_smul]

theorem πLevel_surjective (J : Ideal B) (hJ : J ≤ J₀) : Function.Surjective (P.πLevel bm J hJ) := by
  intro y
  choose lift hlift using P.ψ_surjective
  refine ⟨fun i => Ideal.Quotient.mk _ (lift (bm.repr y i)), ?_⟩
  simp only [πLevel_apply, ψbar_mk, hlift]
  exact bm.sum_repr y

theorem πLevel_eq_zero_iff (J : Ideal B) (hJ : J ≤ J₀) (v : Fin m → B ⧸ P.K J) :
    P.πLevel bm J hJ v = 0 ↔
      v ∈ (Ideal.span (Set.range P.f) • (⊤ : Submodule B (Fin m → B ⧸ P.K J))) := by
  constructor
  · intro hv
    rw [πLevel_apply] at hv
    have hcoord : ∀ i, P.ψbar J hJ (v i) = 0 := by
      have hli := bm.linearIndependent
      rw [Fintype.linearIndependent_iff] at hli
      exact hli _ hv
    rw [← Finset.univ_sum_single v]
    refine Submodule.sum_mem _ fun i _ => ?_
    have hi : v i ∈ (Ideal.span (Set.range P.f) • (⊤ : Submodule B (B ⧸ P.K J))) :=
      (P.ψbar_eq_zero_iff J hJ (v i)).mp (hcoord i)
    have hmap := Submodule.mem_map_of_mem (f := LinearMap.single B (fun _ : Fin m => B ⧸ P.K J) i) hi
    rw [Submodule.map_smul''] at hmap
    exact Submodule.smul_mono le_rfl le_top hmap
  · intro hv
    refine Submodule.smul_induction_on hv (fun a ha n _ => ?_) (fun y z hy hz => ?_)
    · rw [πLevel_smul, (P.ψ_eq_zero_iff a).mpr ha, zero_smul]
    · rw [map_add, hy, hz, add_zero]

noncomputable def bLevel (J : Ideal B) (p : Fin (P.e * m)) : Fin m → B ⧸ P.K J :=
  Pi.single (finProdFinEquiv.symm p).2 (Ideal.Quotient.mk (P.K J) (P.β (finProdFinEquiv.symm p).1))

theorem sum_smul_bLevel (J : Ideal B) (c : Fin (P.e * m) → B) :
    (∑ p, P.φ (c p) • P.bLevel (m := m) J p) =
      fun i => Ideal.Quotient.mk (P.K J) (∑ j, P.φ (c (finProdFinEquiv (j, i))) * P.β j) := by
  rw [← (finProdFinEquiv (m := P.e) (n := m)).sum_comp]
  simp only [bLevel, Equiv.symm_apply_apply]
  rw [Fintype.sum_prod_type]
  funext i
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_ite, smul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul]
  rfl

theorem bLevel_span (J : Ideal B) (x : Fin m → B ⧸ P.K J) :
    ∃ c : Fin (P.e * m) → B, x = ∑ p, P.φ (c p) • P.bLevel (m := m) J p := by
  choose y hy using fun i => Ideal.Quotient.mk_surjective (I := P.K J) (x i)
  choose c hc using fun i => P.hspan (y i)
  refine ⟨fun p => c (finProdFinEquiv.symm p).2 (finProdFinEquiv.symm p).1, ?_⟩
  rw [sum_smul_bLevel]
  funext i
  simp only [Equiv.symm_apply_apply]
  rw [← hc i, hy i]

theorem bLevel_rel (J : Ideal B) (c : Fin (P.e * m) → B) :
    (∑ p, P.φ (c p) • P.bLevel (m := m) J p) = 0 ↔ ∀ p, c p ∈ J := by
  rw [sum_smul_bLevel, funext_iff]
  simp only [Pi.zero_apply, Ideal.Quotient.eq_zero_iff_mem, sum_mem_map_iff]
  constructor
  · intro h p
    have := h (finProdFinEquiv.symm p).2 (finProdFinEquiv.symm p).1
    rwa [Prod.mk.eta, Equiv.apply_symm_apply] at this
  · intro h i j
    exact h _

noncomputable def level (J : Ideal B) (hJ : J ≤ J₀) : Algebra.PatchingLevel 𝒪 r R M J where
  N := Fin m → B ⧸ P.K J
  φ := P.φ
  ψ := P.ψ
  ψ_surjective := P.ψ_surjective
  ψ_φ_X := fun i => by
    rw [P.hφ]
    exact (P.ψ_eq_zero_iff _).mpr (Ideal.subset_span ⟨i, rfl⟩)
  π := P.πLevel bm J hJ
  π_smul := P.πLevel_smul bm J hJ
  π_surjective := P.πLevel_surjective bm J hJ
  ker_π := fun v => by
    have hr : (Set.range fun i => P.φ (MvPowerSeries.X i)) = Set.range P.f := by
      simp only [P.hφ]
    rw [hr]
    exact P.πLevel_eq_zero_iff bm J hJ v
  d := P.e * m
  b := P.bLevel J
  b_span := P.bLevel_span J
  b_rel := P.bLevel_rel J

end Pres
p2m_reactivate "P2MW.S_Algebra_PatchingDatum_nonempty_of_exists_presentation_of_free.FrobDictPTAUT.Pres"

end Level
p2m_reactivate "P2MW.S_Algebra_PatchingDatum_nonempty_of_exists_presentation_of_free.FrobDictPTAUT.Pres"

section MainThm

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [IsAdicComplete (maximalIdeal 𝒪) 𝒪]

omit [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [IsAdicComplete (maximalIdeal 𝒪) 𝒪] in

theorem span_pow_sub_one_le (r ℓ n : ℕ) :
    Ideal.span (Set.range fun j : Fin r => ((1 + MvPowerSeries.X j) ^ (ℓ ^ n) - 1 : (MvPowerSeries (Fin r) 𝒪))) ≤
      Ideal.span (Set.range (MvPowerSeries.X : Fin r → (MvPowerSeries (Fin r) 𝒪))) := by
  rw [Ideal.span_le]
  rintro _ ⟨j, rfl⟩
  have h : (MvPowerSeries.X j : (MvPowerSeries (Fin r) 𝒪)) ∣ (1 + MvPowerSeries.X j) ^ (ℓ ^ n) - 1 := by
    have h0 := sub_dvd_pow_sub_pow (1 + MvPowerSeries.X j : MvPowerSeries (Fin r) 𝒪) 1 (ℓ ^ n)
    rwa [add_sub_cancel_left, one_pow] at h0
  change ((1 + MvPowerSeries.X j) ^ (ℓ ^ n) - 1 : (MvPowerSeries (Fin r) 𝒪)) ∈
    Ideal.span (Set.range (MvPowerSeries.X : Fin r → (MvPowerSeries (Fin r) 𝒪)))
  obtain ⟨t, ht⟩ := h
  rw [ht]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨j, rfl⟩)

omit [IsAdicComplete (maximalIdeal 𝒪) 𝒪] in
theorem mem_maximalIdeal_of_nontrivial_quotient {r : ℕ} (f : Fin r → (MvPowerSeries (Fin r) 𝒪)) [Nontrivial (MvPowerSeries (Fin r) 𝒪 ⧸ Ideal.span (Set.range f))]
    (i : Fin r) : f i ∈ maximalIdeal (MvPowerSeries (Fin r) 𝒪) := by
  by_contra h
  have hu : IsUnit (f i) := by simpa [mem_nonunits_iff] using h
  have htop : Ideal.span (Set.range f) = ⊤ := Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨i, rfl⟩) hu
  exact not_subsingleton (MvPowerSeries (Fin r) 𝒪 ⧸ Ideal.span (Set.range f)) (Ideal.Quotient.subsingleton_iff.mpr htop)

theorem nonempty_patchingDatum (ℓ r : ℕ) (R : Type) [CommRing R] [Algebra 𝒪 R] [Module.Finite 𝒪 R]
    [Module.Free 𝒪 R]
    (hCI : ∃ f : Fin r → MvPowerSeries (Fin r) 𝒪,
      Nonempty ((MvPowerSeries (Fin r) 𝒪 ⧸ Ideal.span (Set.range f)) ≃ₐ[𝒪] R))
    (M : Type) [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M] :
    Nonempty (Algebra.PatchingDatum 𝒪 ℓ r R M) := by
  classical
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact ⟨⟨fun _ => trivialLevel r R M _⟩⟩
  obtain ⟨f, ⟨ε⟩⟩ := hCI
  haveI : Module.Finite 𝒪 (MvPowerSeries (Fin r) 𝒪 ⧸ Ideal.span (Set.range f)) := Module.Finite.equiv ε.symm.toLinearEquiv
  haveI : Module.Free 𝒪 (MvPowerSeries (Fin r) 𝒪 ⧸ Ideal.span (Set.range f)) := Module.Free.of_equiv ε.symm.toLinearEquiv
  haveI : Nontrivial (MvPowerSeries (Fin r) 𝒪 ⧸ Ideal.span (Set.range f)) := ε.toEquiv.nontrivial
  haveI : IsAdicComplete (maximalIdeal (MvPowerSeries (Fin r) 𝒪)) (MvPowerSeries (Fin r) 𝒪) := MvPowerSeries.isAdicComplete_maximalIdeal
  obtain ⟨φ, hφ⟩ := MvPowerSeries.exists_algHom_apply_X_eq (𝒪 := 𝒪) (maximalIdeal (MvPowerSeries (Fin r) 𝒪)) f
    (mem_maximalIdeal_of_nontrivial_quotient f)
  obtain ⟨e, β, hspan, hrel⟩ := MvPowerSeries.exists_coords_of_quotient_span_finite_free f φ hφ
  let P : Pres 𝒪 r R :=
    { f := f
      φ := φ
      hφ := hφ
      ψ := ε.toAlgHom.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span (Set.range f)))
      ψ_surjective := ε.surjective.comp (Ideal.Quotient.mkₐ_surjective 𝒪 _)
      ψ_eq_zero_iff := fun x => by
        change ε (Ideal.Quotient.mk _ x) = 0 ↔ _
        rw [map_eq_zero_iff ε ε.injective, Ideal.Quotient.eq_zero_iff_mem]
      e := e
      β := β
      hspan := hspan
      hrel := hrel }
  let bm : Module.Basis (Fin (Fintype.card (Module.Free.ChooseBasisIndex R M))) R M :=
    (Module.Free.chooseBasis R M).reindex (Fintype.equivFin _)
  exact ⟨⟨fun n => P.level bm _ (span_pow_sub_one_le r ℓ n)⟩⟩

end MainThm
p2m_reactivate "P2MW.S_Algebra_PatchingDatum_nonempty_of_exists_presentation_of_free.FrobDictPTAUT.Pres"

end FrobDictPTAUT
p2m_reactivate "P2MW.S_Algebra_PatchingDatum_nonempty_of_exists_presentation_of_free.FrobDictPTAUT.Pres P2MW.S_Algebra_PatchingDatum_nonempty_of_exists_presentation_of_free.FrobDictPTAUT"

theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    (ℓ : ℕ) {r : ℕ} {R : Type} [CommRing R] [Algebra 𝒪 R] [Module.Finite 𝒪 R] [Module.Free 𝒪 R]
    (hCI : ∃ f : Fin r → MvPowerSeries (Fin r) 𝒪,
      Nonempty ((MvPowerSeries (Fin r) 𝒪 ⧸ Ideal.span (Set.range f)) ≃ₐ[𝒪] R))
    (M : Type) [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M] :
    Nonempty (Algebra.PatchingDatum 𝒪 ℓ r R M) :=
  FrobDictPTAUT.nonempty_patchingDatum ℓ r R hCI M

end S_Algebra_PatchingDatum_nonempty_of_exists_presentation_of_free
end P2MW
export P2MW.S_Algebra_PatchingDatum_nonempty_of_exists_presentation_of_free (solution)
