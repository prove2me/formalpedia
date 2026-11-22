-- Prove2me | Definitions.Def_AlpoGeB002
-- name    : AlpoGeB002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-21T16:22:08.318942+00:00
-- url     : https://prove2.me/theorems/0144e66e-38a5-4b2b-8c30-7a6ae8eb803b
-- title:
--   Definitions bundle AlpoGeB002 of the alpo.ge GRH release, first cut (Row0b, IsRecT)
-- statement:
--   A definitions bundle of the first cut of L. Alpöge's Lean proof of GRH for Dirichlet $L$-functions (released 20 November 2026, written with Claude; announcement [alpo.ge/remark.pdf](https://alpo.ge/remark.pdf)). The declarations and their proofs are the release's, carved mechanically for this platform: the carve reorders them, restates the namespaces and `open`s each needs, and writes a few declarations from their elaborated form. Two patches are recorded in the carve: an anonymous instance is given its original generated name, and an additive structure that a `to_additive` attribute names is restored beside the structure that names it. The release builds with `maxHeartbeats 4000000` and `maxSynthPendingDepth 3` as project options (and `synthInstance.maxHeartbeats 400000` for its local and global field libraries); since the verifier sets none of these, each carved module section states them as `set_option` lines. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   The first cut publishes the two inputs from which the release concludes its main theorem: `AlpoGe.galoisLocalGlobalStrong_recParameter` (the release's `UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter`) and `AlpoGe.everyCharacter_of_row` (the release's `UpperTheory.FinalTheorems.everyCharacter_of_row`). These bundles hold the definitions their statements need, with the theorems those definitions use.
--
--   **Contents.** It holds 272 declarations of the release's Lean: 98 definitions, 8 inductive types or structures, 14 instances and 152 theorems. The definitions and types are `GlobalTheory.CuspRep.SmIrr`, `GlobalTheory.GLp.inc`, `GlobalTheory.GLp.red`, `GlobalTheory.GLq.Gn`, `GlobalTheory.GLq.InPar`, `GlobalTheory.GLq.IsIrr`, `GlobalTheory.GLq.Mt`, `GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.infiniteAdeleMap`, `GlobalTheory.InfAdeleCM.ext`, `GlobalTheory.IsAEOrbitSection`, `GlobalTheory.LocGL.IrrGL`, `GlobalTheory.LocGL.IrrGL.IsCusp`, `GlobalTheory.LocGL.IrrGL.of`, `GlobalTheory.LocGL.IrrGL.ofChar`, `GlobalTheory.LocGL.IrrGL.rep`, `GlobalTheory.LocGL.IsCosocle`, `GlobalTheory.LocalData.complRel`, `GlobalTheory.LvT.LocF`, `GlobalTheory.LvT.LocF.Raw`, `GlobalTheory.Mem.Vol.IsCMFam`, `GlobalTheory.PRep.IsSmooth`, `GlobalTheory.PRep.Jacquet`, `GlobalTheory.PRep.TwJacquet`, `GlobalTheory.PRep.eig`, `GlobalTheory.PRep.fixed`, `GlobalTheory.PRep.indSpace`, `GlobalTheory.PRep.smoothPart`, `GlobalTheory.PRep.twKer`, `GlobalTheory.Pst.Letter`, `GlobalTheory.Pst.letterKer`, `GlobalTheory.Pst.letterMap`, `GlobalTheory.Pst.letterMk`, `GlobalTheory.Pst.letterQ`, `GlobalTheory.Published.IsRegularChar`, `GlobalTheory.SerSys.TameGen.Inflates`, `GlobalTheory.SmGL.HasCentralChar`, `GlobalTheory.SmGL.IrrCl`, `GlobalTheory.SmGL.IrrCl.rep`, `GlobalTheory.SmGL.IrrRep`, `GlobalTheory.SmGL.IrrRep.cl`, `GlobalTheory.SmGL.IrrRep.det`, `GlobalTheory.SmGL.IrrRep.ofChar`, `GlobalTheory.SmGL.IsCuspidal`, `GlobalTheory.SmGL.IsSmoothChar`, `GlobalTheory.SmGL.IsSpherical`, `GlobalTheory.SmGL.IsSphericalFor`, `GlobalTheory.SmGL.IsSubquotient`, `GlobalTheory.SmGL.Levi`, `GlobalTheory.SmGL.Segment`, `GlobalTheory.SmGL.Two`, `GlobalTheory.SmGL.absPow`, `GlobalTheory.SmGL.blk`, `GlobalTheory.SmGL.deltaHalf`, `GlobalTheory.SmGL.detChar`, `GlobalTheory.SmGL.diagBlock`, `GlobalTheory.SmGL.leviProj`, `GlobalTheory.SmGL.leviProjLower`, `GlobalTheory.SmGL.modExp`, `GlobalTheory.SmGL.ofChar`, `GlobalTheory.SmGL.opp`, and 46 more.
-- source:
--   L. Alpöge, working with Claude, Lean formalization of the Riemann hypothesis and of GRH for Dirichlet L-functions, released 20 November 2026 (announcement https://alpo.ge/remark.pdf; Lean archive https://alpo.ge/lean.tar.gz.part01 to part14, joined tarball sha256 9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc)

import Mathlib

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.BlockTheory.AdelicCMFields.UnitaryHeckeCharacterIdele
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter
open scoped RestrictedProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele

section Extension

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

instance liesOver_comap (w : InfinitePlace L) : w.LiesOver (w.comap (algebraMap K L)) :=
  ⟨rfl⟩

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter in
open scoped RestrictedProduct in
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under :
    Tendsto (fun w : HeightOneSpectrum (𝓞 L) => w.under (𝓞 K)) cofinite cofinite := by
  intro s hs
  rw [mem_cofinite] at hs
  rw [mem_map, mem_cofinite]
  rw [← Set.preimage_compl]
  refine hs.preimage' fun v _ => ?_
  refine ((IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 L)).preimage
    (fun a _ b _ h => HeightOneSpectrum.ext h)).subset ?_
  rintro w rfl
  exact ⟨w.isPrime, ⟨rfl⟩⟩

def infiniteAdeleMap : InfiniteAdeleRing K →+* InfiniteAdeleRing L :=
  Pi.ringHom fun w : InfinitePlace L =>
    (LiesOver.completionMap (v := w.comap (algebraMap K L)) (w := w)).comp
      (Pi.evalRingHom (fun v : InfinitePlace K => v.Completion) (w.comap (algebraMap K L)))

end Extension

end GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele
end
end

section
-- module Solutions.AlpoGe.ReciprocityTheory.GaloisValuations.GlobalA
attribute [-instance] _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open NumberField IsDedekindDomain Pointwise

namespace ReciprocityTheory.Gal

section krull

variable {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] [Algebra.IsIntegral F Ω]

theorem isOpen_setOf_apply (x : Ω) (P : Ω → Prop) : IsOpen {τ : Ω ≃ₐ[F] Ω | P (τ x)} := by
  have hx : IsIntegral F x := Algebra.IsIntegral.isIntegral x
  haveI : FiniteDimensional F (IntermediateField.adjoin F {x}) :=
    IntermediateField.adjoin.finiteDimensional hx
  have hH : IsOpen ((IntermediateField.adjoin F {x}).fixingSubgroup : Set (Ω ≃ₐ[F] Ω)) :=
    IntermediateField.fixingSubgroup_isOpen _
  rw [isOpen_iff_forall_mem_open]
  intro τ hτ
  refine ⟨(fun σ => τ⁻¹ * σ) ⁻¹' ((IntermediateField.adjoin F {x}).fixingSubgroup : Set (Ω ≃ₐ[F] Ω)),
    ?_, ?_, ?_⟩
  · intro σ hσ
    have hσ' : τ⁻¹ * σ ∈ (IntermediateField.adjoin F {x}).fixingSubgroup := hσ
    rw [IntermediateField.mem_fixingSubgroup_iff] at hσ'
    have h1 := hσ' x (IntermediateField.mem_adjoin_simple_self F x)
    have h2 : σ x = τ x := by
      calc σ x = (τ * (τ⁻¹ * σ)) x := by rw [mul_inv_cancel_left]
        _ = τ ((τ⁻¹ * σ) x) := by rw [AlgEquiv.mul_apply]
        _ = τ x := by rw [h1]
    show P (σ x)
    rw [h2]
    exact hτ
  · exact hH.preimage (continuous_const.mul continuous_id)
  · show τ⁻¹ * τ ∈ (IntermediateField.adjoin F {x}).fixingSubgroup
    rw [inv_mul_cancel]
    exact one_mem _

end krull

section roots

variable {Ω : Type*} [Field Ω]

theorem eq_one_of_pow_eq_one (A : ValuationSubring Ω) {N : ℕ} (hN : ¬ A.valuation (N : Ω) < 1)
    {ξ : Ω} (hξ : ξ ^ N = 1) (h : A.valuation (ξ - 1) < 1) : ξ = 1 := by
  have hξ1 : A.valuation ξ ≤ 1 := by
    have h2 := Valuation.map_add A.valuation (ξ - 1) 1
    rw [sub_add_cancel, Valuation.map_one] at h2
    exact h2.trans (max_le h.le le_rfl)
  have hpow : ∀ j : ℕ, A.valuation (ξ ^ j) ≤ 1 := fun j => by
    rw [Valuation.map_pow]
    exact pow_le_one' hξ1 j
  have hgeom : ∀ i : ℕ, A.valuation (ξ ^ i - 1) < 1 := by
    intro i
    rw [← geom_sum_mul, Valuation.map_mul]
    refine lt_of_le_of_lt (mul_le_of_le_one_left' ?_) h
    exact Valuation.map_sum_le _ (fun j _ => hpow j)
  by_contra hne
  have h3 := geom_sum_mul ξ N
  rw [hξ, sub_self] at h3
  have hS := (mul_eq_zero.1 h3).resolve_right (fun h4 => hne (sub_eq_zero.1 h4))
  have h5 := Valuation.map_sum_lt A.valuation (s := Finset.range N) (f := fun i => ξ ^ i - 1)
    one_ne_zero (fun i _ => hgeom i)
  rw [Finset.sum_sub_distrib, hS] at h5
  apply hN
  simpa using h5

theorem valuation_eq_one_of_pow_eq_one (A : ValuationSubring Ω) {N : ℕ} (hN0 : N ≠ 0) {b : Ω}
    (hb : b ^ N = 1) : A.valuation b = 1 := by
  have h1 : A.valuation b ^ N = 1 := by rw [← Valuation.map_pow, hb, Valuation.map_one]
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := Nat.exists_eq_succ_of_ne_zero hN0
  rw [pow_succ] at h1
  rcases lt_trichotomy (A.valuation b) 1 with hlt | heq | hgt
  · exfalso
    have h2 : A.valuation b ^ M * A.valuation b ≤ A.valuation b :=
      mul_le_of_le_one_left' (pow_le_one' hlt.le M)
    rw [h1] at h2
    exact absurd hlt (not_lt.2 h2)
  · exact heq
  · exfalso
    have h2 : A.valuation b ≤ A.valuation b ^ M * A.valuation b :=
      le_mul_of_one_le_left' (one_le_pow_of_one_le' hgt.le M)
    rw [h1] at h2
    exact absurd hgt (not_lt.2 h2)

theorem eq_of_pow_eq_one (A : ValuationSubring Ω) {N : ℕ} (hN : ¬ A.valuation (N : Ω) < 1)
    {a b : Ω} (ha : a ^ N = 1) (hb : b ^ N = 1) (h : A.valuation (a - b) < 1) : a = b := by
  have hN0 : N ≠ 0 := by
    rintro rfl
    apply hN
    simp
  have hb0 : b ≠ 0 := by
    rintro rfl
    simp [hN0] at hb
  have hvb := valuation_eq_one_of_pow_eq_one A hN0 hb
  have hξ : (a / b) ^ N = 1 := by rw [div_pow, ha, hb, div_one]
  have hξ1 : A.valuation (a / b - 1) < 1 := by
    rw [div_sub_one hb0, Valuation.map_div, hvb, div_one]
    exact h
  have h2 := eq_one_of_pow_eq_one A hN hξ hξ1
  rwa [div_eq_one_iff_eq hb0] at h2

end roots

end ReciprocityTheory.Gal
end
end

section
-- module Solutions.AlpoGe.ReciprocityTheory.GaloisValuations.GlobalB
attribute [-instance] _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

set_option linter.style.haveILetI false

noncomputable section

open NumberField IsDedekindDomain Pointwise
open scoped nonZeroDivisors

namespace ReciprocityTheory.Gal

section den

variable {Ω : Type*} [Field Ω]

theorem isIntegral_int_of_isIntegral {F : Type*} [Field F] [NumberField F] [Algebra F Ω] {b : Ω} (hb : IsIntegral (𝓞 F) b) : IsIntegral ℤ b :=
  isIntegral_trans b hb

theorem mem_of_isIntegral_int (A : ValuationSubring Ω) {b : Ω} (hb : IsIntegral ℤ b) : b ∈ A := by
  have h1 : IsIntegral A b := hb.tower_top
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := Ω)).mp h1
  rw [← hy]
  exact y.2

theorem exists_den (F : Type*) [Field F] [NumberField F] [Algebra F Ω] [IsAlgClosure F Ω]
    (A : ValuationSubring Ω) {x : Ω} (hx : A.valuation x ≤ 1) :
    ∃ s t : Ω, IsIntegral ℤ s ∧ IsIntegral ℤ t ∧ A.valuation s = 1 ∧ s * x = t := by
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have hxF : IsIntegral F x := Algebra.IsIntegral.isIntegral x
  have hxQ : IsIntegral ℚ x := isIntegral_trans x hxF
  let E := IntermediateField.adjoin ℚ ({x} : Set Ω)
  have : FiniteDimensional ℚ E := IntermediateField.adjoin.finiteDimensional hxQ
  have : NumberField E := ⟨⟩
  let x' : E := ⟨x, IntermediateField.mem_adjoin_simple_self ℚ x⟩
  let M : FractionalIdeal (𝓞 E)⁰ E := 1 + FractionalIdeal.spanSingleton _ x'
  have h1M : (1 : E) ∈ M := by
    have hle1 : (1 : FractionalIdeal (𝓞 E)⁰ E) ≤ M := by
      simp only [M, ← FractionalIdeal.sup_eq_add]; exact le_sup_left
    exact hle1 (FractionalIdeal.one_mem_one _)
  have hxM : x' ∈ M := by
    have hle1 : FractionalIdeal.spanSingleton (𝓞 E)⁰ x' ≤ M := by
      simp only [M, ← FractionalIdeal.sup_eq_add]; exact le_sup_right
    exact hle1 (FractionalIdeal.mem_spanSingleton_self _ _)
  have hM : M ≠ 0 := by
    intro h
    rw [h] at h1M
    exact one_ne_zero ((FractionalIdeal.mem_zero_iff _).mp h1M)
  have hMM : M * M⁻¹ = 1 := mul_inv_cancel₀ hM
  obtain ⟨α, hα, β, hβ, e⟩ : ∃ α ∈ M⁻¹, ∃ β ∈ M⁻¹, α + x' * β = 1 := by
    have h1 : (1 : E) ∈ M * M⁻¹ := by rw [hMM]; exact FractionalIdeal.one_mem_one _
    have e2 : M * M⁻¹ = M⁻¹ ⊔ FractionalIdeal.spanSingleton _ x' * M⁻¹ := by
      simp only [M, add_mul, one_mul, FractionalIdeal.sup_eq_add]
    rw [e2, ← FractionalIdeal.mem_coe, FractionalIdeal.coe_sup, Submodule.mem_sup] at h1
    obtain ⟨α, hα, z, hz, e⟩ := h1
    obtain ⟨β, hβ, rfl⟩ := FractionalIdeal.mem_singleton_mul.mp hz
    exact ⟨α, hα, β, hβ, e⟩
  have hint : ∀ γ ∈ M⁻¹, IsIntegral ℤ (γ : Ω) ∧ IsIntegral ℤ ((γ * x' : E) : Ω) := by
    intro γ hγ
    rw [FractionalIdeal.mem_inv_iff hM] at hγ
    have key : ∀ z : E, z ∈ (1 : FractionalIdeal (𝓞 E)⁰ E) → IsIntegral ℤ (z : Ω) := by
      intro z hz
      obtain ⟨z', rfl⟩ := (FractionalIdeal.mem_one_iff _).mp hz
      have : IsIntegral ℤ (algebraMap (𝓞 E) E z') := z'.2
      exact this.map (IsScalarTower.toAlgHom ℤ E Ω)
    exact ⟨by simpa using key _ (hγ 1 h1M), key _ (hγ x' hxM)⟩
  have hle : ∀ γ ∈ M⁻¹, A.valuation (γ : Ω) ≤ 1 := fun γ hγ =>
    (A.valuation_le_one_iff _).mpr (mem_of_isIntegral_int A (hint γ hγ).1)
  by_cases ha : A.valuation (α : Ω) = 1
  · exact ⟨α, _, (hint α hα).1, (hint α hα).2, ha, by simp [x']⟩
  by_cases hb : A.valuation (β : Ω) = 1
  · exact ⟨β, _, (hint β hβ).1, (hint β hβ).2, hb, by simp [x', mul_comm]⟩
  exfalso
  have ha' : A.valuation (α : Ω) < 1 := lt_of_le_of_ne (hle α hα) ha
  have hb' : A.valuation (β : Ω) < 1 := lt_of_le_of_ne (hle β hβ) hb
  have e' : (α : Ω) + x * (β : Ω) = 1 := by
    have := congrArg (fun z : E => (z : Ω)) e
    simpa [x'] using this
  have : A.valuation ((α : Ω) + x * (β : Ω)) < 1 := by
    refine Valuation.map_add_lt _ ha' ?_
    rw [Valuation.map_mul]
    calc A.valuation x * A.valuation (β : Ω) ≤ 1 * A.valuation (β : Ω) := mul_le_mul_left hx _
      _ < 1 := by rw [one_mul]; exact hb'
  rw [e', Valuation.map_one] at this
  exact lt_irrefl _ this

theorem le_of_valuation_lt_one_iff (F : Type*) [Field F] [NumberField F] [Algebra F Ω]
    [IsAlgClosure F Ω] {A A' : ValuationSubring Ω}
    (h : ∀ b : Ω, IsIntegral ℤ b → (A.valuation b < 1 ↔ A'.valuation b < 1)) : A ≤ A' := by
  intro x hx
  have hx' : A.valuation x ≤ 1 := (A.valuation_le_one_iff x).mpr hx
  obtain ⟨s, t, hs, ht, hs1, e⟩ := exists_den F A hx'
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs1
  have hs1' : A'.valuation s = 1 := by
    refine le_antisymm ((A'.valuation_le_one_iff s).mpr (mem_of_isIntegral_int A' hs)) ?_
    rw [← not_lt, ← h s hs, hs1]
    exact lt_irrefl 1
  have hxt : x = t * s⁻¹ := by rw [← e]; field_simp
  rw [← A'.valuation_le_one_iff, hxt, Valuation.map_mul, map_inv₀, hs1', inv_one, mul_one,
    A'.valuation_le_one_iff]
  exact mem_of_isIntegral_int A' ht

theorem eq_of_valuation_lt_one_iff (F : Type*) [Field F] [NumberField F] [Algebra F Ω]
    [IsAlgClosure F Ω] {A A' : ValuationSubring Ω}
    (h : ∀ b : Ω, IsIntegral ℤ b → (A.valuation b < 1 ↔ A'.valuation b < 1)) : A = A' :=
  le_antisymm (le_of_valuation_lt_one_iff F h)
    (le_of_valuation_lt_one_iff F fun b hb => (h b hb).symm)

end den

section places

variable {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]

theorem smul_valuation_lt_one_iff (g : Ω ≃ₐ[F] Ω) (A : ValuationSubring Ω) (y : Ω) :
    (g • A).valuation y < 1 ↔ A.valuation ((g⁻¹ : Ω ≃ₐ[F] Ω) y) < 1 := by
  rw [← ValuationSubring.mem_nonunits_iff, ← ValuationSubring.mem_nonunits_iff,
    ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, map_inv₀,
    map_eq_zero_iff _ (g⁻¹ : Ω ≃ₐ[F] Ω).injective]

variable (F Ω) in

abbrev IntCl := integralClosure (𝓞 F) Ω

theorem valuation_le_one_intCl (A : ValuationSubring Ω) (b : IntCl F Ω) :
    A.valuation (b : Ω) ≤ 1 :=
  (A.valuation_le_one_iff _).mpr (mem_of_isIntegral_int A (isIntegral_int_of_isIntegral b.2))

def primeBelow (A : ValuationSubring Ω) : Ideal (IntCl F Ω) where
  carrier := {b | A.valuation (b : Ω) < 1}
  add_mem' {a b} ha hb := by
    show A.valuation ((a : Ω) + b) < 1
    exact Valuation.map_add_lt _ ha hb
  zero_mem' := by show A.valuation ((0 : IntCl F Ω) : Ω) < 1; simp
  smul_mem' c b hb := by
    show A.valuation ((c : Ω) * b) < 1
    rw [Valuation.map_mul]
    calc A.valuation (c : Ω) * A.valuation (b : Ω) ≤ 1 * A.valuation (b : Ω) :=
          mul_le_mul_left (valuation_le_one_intCl A c) _
      _ < 1 := by rw [one_mul]; exact hb

theorem mem_primeBelow {A : ValuationSubring Ω} {b : IntCl F Ω} :
    b ∈ primeBelow A ↔ A.valuation (b : Ω) < 1 := Iff.rfl

instance isPrime_primeBelow (A : ValuationSubring Ω) : (primeBelow (F := F) A).IsPrime where
  ne_top' h := by
    have : (1 : IntCl F Ω) ∈ primeBelow A := h ▸ Submodule.mem_top
    rw [mem_primeBelow] at this
    simp at this
  mem_or_mem' {a b} hab := by
    rw [mem_primeBelow, mem_primeBelow]
    rw [mem_primeBelow] at hab
    by_contra hn
    simp only [not_or, not_lt] at hn
    have ha : A.valuation (a : Ω) = 1 := le_antisymm (valuation_le_one_intCl A a) hn.1
    have hb : A.valuation (b : Ω) = 1 := le_antisymm (valuation_le_one_intCl A b) hn.2
    have : A.valuation ((a * b : IntCl F Ω) : Ω) = 1 := by
      rw [MulMemClass.coe_mul, Valuation.map_mul, ha, hb, one_mul]
    rw [this] at hab
    exact lt_irrefl _ hab

theorem under_primeBelow {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)}
    (hA : ∀ x : 𝓞 F, A.valuation (algebraMap F Ω (x : F)) < 1 ↔ x ∈ v.asIdeal) :
    (primeBelow (F := F) A).under (𝓞 F) = v.asIdeal := by
  ext x
  rw [Ideal.under, Ideal.mem_comap, mem_primeBelow, ← hA x]
  rfl

theorem primeBelow_smul (g : Ω ≃ₐ[F] Ω) (A : ValuationSubring Ω) :
    primeBelow (F := F) (g • A) = g • primeBelow (F := F) A := by
  ext b
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, mem_primeBelow, mem_primeBelow,
    smul_valuation_lt_one_iff]
  rfl

end places

section profinite

variable {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]

variable (F Ω) in

theorem continuousSMul_intCl :
    @ContinuousSMul (Ω ≃ₐ[F] Ω) (IntCl F Ω) _ _ ⊥ := by
  letI : TopologicalSpace (IntCl F Ω) := ⊥
  haveI : DiscreteTopology (IntCl F Ω) := ⟨rfl⟩
  refine ⟨continuous_discrete_rng.mpr fun c => ?_⟩
  rw [isOpen_iff_forall_mem_open]
  rintro ⟨g₀, b₀⟩ h
  refine ⟨{g : Ω ≃ₐ[F] Ω | g (b₀ : Ω) = g₀ (b₀ : Ω)} ×ˢ {b₀}, ?_,
    (isOpen_setOf_apply (F := F) (b₀ : Ω) (· = g₀ (b₀ : Ω))).prod (isOpen_discrete _), ⟨rfl, rfl⟩⟩
  rintro ⟨g, b⟩ ⟨hg, hb⟩
  simp only [Set.mem_singleton_iff] at hb
  subst hb
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at h ⊢
  rw [← h]
  exact Subtype.ext hg

variable (F Ω) in

theorem isInvariant_intCl : Algebra.IsInvariant (𝓞 F) (IntCl F Ω) (Ω ≃ₐ[F] Ω) := by
  refine ⟨fun b hb => ?_⟩
  have hfix : ∀ σ : Ω ≃ₐ[F] Ω, σ (b : Ω) = b := fun σ => congrArg Subtype.val (hb σ)
  have hbot := (InfiniteGalois.mem_bot_iff_fixed (b : Ω)).mpr hfix
  obtain ⟨c, hc⟩ := IntermediateField.mem_bot.mp hbot
  have hcint : IsIntegral (𝓞 F) c := by
    have : IsIntegral (𝓞 F) (algebraMap F Ω c) := hc ▸ b.2
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom (𝓞 F) F Ω)
      (algebraMap F Ω).injective).mp this
  obtain ⟨a, ha⟩ := (IsIntegrallyClosed.isIntegral_iff (R := 𝓞 F) (K := F)).mp hcint
  refine ⟨a, Subtype.ext ?_⟩
  rw [← hc, ← ha]
  rfl

theorem exists_frob_over {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)}
    (hA : ∀ x : 𝓞 F, A.valuation (algebraMap F Ω (x : F)) < 1 ↔ x ∈ v.asIdeal) :
    ∃ σ : Ω ≃ₐ[F] Ω, σ • A = A ∧ ∀ x, A.valuation x ≤ 1 →
      A.valuation (σ x - x ^ Nat.card (𝓞 F ⧸ v.asIdeal)) < 1 := by
  letI : TopologicalSpace (IntCl F Ω) := ⊥
  haveI : DiscreteTopology (IntCl F Ω) := ⟨rfl⟩
  haveI := continuousSMul_intCl F Ω
  haveI := isInvariant_intCl F Ω
  set Q := primeBelow (F := F) A with hQ
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  haveI : Q.LiesOver v.asIdeal := ⟨(under_primeBelow hA).symm⟩
  haveI : Q.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := 𝓞 F) Q
    (by rw [show Ideal.comap (algebraMap (𝓞 F) (IntCl F Ω)) Q = v.asIdeal from
      under_primeBelow hA]; exact v.isMaximal)
  letI : Field (IntCl F Ω ⧸ Q) := Ideal.Quotient.field Q
  letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  letI : Fintype (𝓞 F ⧸ v.asIdeal) := Fintype.ofFinite _
  haveI hBi : Algebra.IsIntegral (𝓞 F) (IntCl F Ω) := inferInstance
  haveI : Algebra.IsIntegral (𝓞 F ⧸ v.asIdeal) (IntCl F Ω ⧸ Q) :=
    Ideal.Quotient.algebra_isIntegral_of_liesOver Q v.asIdeal
  haveI : Algebra.IsAlgebraic (𝓞 F ⧸ v.asIdeal) (IntCl F Ω ⧸ Q) := Algebra.IsIntegral.isAlgebraic
  let φ : (IntCl F Ω ⧸ Q) ≃ₐ[𝓞 F ⧸ v.asIdeal] (IntCl F Ω ⧸ Q) :=
    FiniteField.frobeniusAlgEquivOfAlgebraic (𝓞 F ⧸ v.asIdeal) (IntCl F Ω ⧸ Q)
  obtain ⟨⟨σ, hσQ⟩, hσ⟩ := Ideal.Quotient.stabilizerHom_surjective_of_profinite
    (G := Ω ≃ₐ[F] Ω) v.asIdeal Q φ
  have hσQ' : σ • Q = Q := hσQ
  set q := Nat.card (𝓞 F ⧸ v.asIdeal) with hq
  have hqc : Fintype.card (𝓞 F ⧸ v.asIdeal) = q := Fintype.card_eq_nat_card
  have hcong : ∀ b : IntCl F Ω, A.valuation (σ (b : Ω) - (b : Ω) ^ q) < 1 := by
    intro b
    have h1 : Ideal.Quotient.mk Q (σ • b) =
        Ideal.Quotient.mk Q b ^ Fintype.card (𝓞 F ⧸ v.asIdeal) :=
      DFunLike.congr_fun hσ (Ideal.Quotient.mk Q b)
    have h2 : σ • b - b ^ q ∈ Q := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, h1, hqc, sub_self]
    exact h2
  have hdec : σ • A = A := by
    refine eq_of_valuation_lt_one_iff F fun b hb => ?_
    let b' : IntCl F Ω := ⟨b, hb.tower_top⟩
    change b' ∈ primeBelow (F := F) (σ • A) ↔ b' ∈ Q
    rw [primeBelow_smul, hσQ']
  refine ⟨σ, hdec, fun x hx => ?_⟩
  obtain ⟨s, t, hs, ht, hs1, e⟩ := exists_den F A hx
  have hcs := hcong ⟨s, hs.tower_top⟩
  have hct := hcong ⟨t, ht.tower_top⟩
  have hvt : A.valuation t ≤ 1 := (A.valuation_le_one_iff _).mpr (mem_of_isIntegral_int A ht)
  have hσs : A.valuation (σ s) = 1 := by
    refine le_antisymm ((A.valuation_le_one_iff _).mpr (mem_of_isIntegral_int A
      (hs.map ((σ : Ω ≃ₐ[F] Ω).toAlgHom.restrictScalars ℤ)))) ?_
    have h3 : ¬ (σ • A).valuation (σ s) < 1 := by
      rw [smul_valuation_lt_one_iff]
      have : (σ⁻¹ : Ω ≃ₐ[F] Ω) (σ s) = s := by
        show (σ⁻¹ * σ) s = s
        simp
      rw [this, hs1]
      exact lt_irrefl 1
    rw [hdec] at h3
    exact not_lt.mp h3
  have he' : σ s * σ x = σ t := by rw [← map_mul, e]
  have key : s ^ q * σ s * (σ x - x ^ q) = s ^ q * (σ t - t ^ q) + t ^ q * (s ^ q - σ s) := by
    rw [← he', ← e]; ring
  have hv : A.valuation (s ^ q * σ s * (σ x - x ^ q)) < 1 := by
    rw [key]
    apply Valuation.map_add_lt
    · rw [Valuation.map_mul, Valuation.map_pow, hs1, one_pow, one_mul]
      exact hct
    · rw [Valuation.map_mul, Valuation.map_sub_swap]
      calc A.valuation (t ^ q) * A.valuation (σ s - s ^ q) ≤ 1 * A.valuation (σ s - s ^ q) :=
            mul_le_mul_left (by rw [Valuation.map_pow]; exact pow_le_one' hvt q) _
        _ < 1 := by rw [one_mul]; exact hcs
  rw [Valuation.map_mul, Valuation.map_mul, Valuation.map_pow, hs1, hσs, one_pow, one_mul,
    one_mul] at hv
  exact hv

end profinite

end ReciprocityTheory.Gal
end
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
attribute [-instance] _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Gal

namespace GlobalTheory.WeilDeligne

variable {E Ω : Type*} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]

section Cong

variable {A : ValuationSubring Ω}

theorem cong_symm {x y : Ω} (h : A.valuation (x - y) < 1) : A.valuation (y - x) < 1 := by
  rwa [Valuation.map_sub_swap]

theorem cong_trans {x y z : Ω} (h : A.valuation (x - y) < 1) (h' : A.valuation (y - z) < 1) :
    A.valuation (x - z) < 1 := by
  have e : x - z = (x - y) + (y - z) := by ring
  rw [e]; exact Valuation.map_add_lt _ h h'

theorem val_pow_le_one {x : Ω} (hx : A.valuation x ≤ 1) (n : ℕ) : A.valuation (x ^ n) ≤ 1 := by
  rw [map_pow]; exact pow_le_one₀ zero_le hx

theorem cong_pow {x y : Ω} (hx : A.valuation x ≤ 1) (hy : A.valuation y ≤ 1)
    (h : A.valuation (x - y) < 1) (n : ℕ) : A.valuation (x ^ n - y ^ n) < 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : x ^ (n + 1) - y ^ (n + 1) = x * (x ^ n - y ^ n) + y ^ n * (x - y) := by ring
    rw [e]
    refine Valuation.map_add_lt _ ?_ ?_
    · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' hx) ih
    · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (val_pow_le_one hy n)) h

theorem exists_not_cong_pow [IsAlgClosed Ω] {m n : ℕ} (hn : 0 < n) (hmn : n < m) :
    ∃ x : Ω, A.valuation x ≤ 1 ∧ ¬ A.valuation (x ^ m - x ^ n) < 1 := by
  have hdeg : (Polynomial.X ^ m - (Polynomial.X ^ n + 1) : Polynomial Ω).degree = m := by
    rw [Polynomial.degree_sub_eq_left_of_degree_lt, Polynomial.degree_X_pow]
    rw [Polynomial.degree_X_pow, ← Polynomial.C_1, Polynomial.degree_X_pow_add_C hn]
    exact_mod_cast hmn
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root
    (Polynomial.X ^ m - (Polynomial.X ^ n + 1) : Polynomial Ω)
    (by rw [hdeg]; exact_mod_cast (hn.trans hmn).ne')
  have hx' : x ^ m = x ^ n + 1 := by
    have := hx
    simp only [Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_one] at this
    exact sub_eq_zero.mp this
  refine ⟨x, ?_, ?_⟩
  · by_contra hc
    have h1 : 1 < A.valuation x := not_le.mp hc
    have h2 : A.valuation (x ^ n + 1) < A.valuation x ^ m := by
      refine Valuation.map_add_lt _ ?_ ?_
      · rw [map_pow]; exact pow_lt_pow_right₀ h1 hmn
      · rw [map_one]; exact one_lt_pow₀ h1 (hn.trans hmn).ne'
    rw [← hx', map_pow] at h2
    exact lt_irrefl _ h2
  · rw [hx', add_sub_cancel_left, map_one]; exact lt_irrefl _

end Cong

end GlobalTheory.WeilDeligne
end
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsSemisimpleOfISupEigenspace
attribute [-instance] _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open Polynomial TensorProduct Module

namespace GlobalTheory.WeilDeligne

section Lin

variable {V V' : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']

theorem isSemisimple_map [FiniteDimensional ℂ V] (φ : End ℂ V →ₐ[ℂ] End ℂ V') {f : End ℂ V}
    (hf : f.IsSemisimple) : (φ f).IsSemisimple :=
  End.isSemisimple_of_squarefree_aeval_eq_zero hf.minpoly_squarefree (by
    rw [aeval_algHom_apply, minpoly.aeval, map_zero])

theorem isSemisimple_of_iSup_eigenspace [FiniteDimensional ℂ V] {f : End ℂ V}
    (hf : ⨆ α, f.eigenspace α = ⊤) : f.IsSemisimple := by
  classical
  have hfin : Set.Finite {α : ℂ | f.HasEigenvalue α} := Module.End.finite_hasEigenvalue f
  refine End.isSemisimple_of_squarefree_aeval_eq_zero (p := ∏ α ∈ hfin.toFinset, (X - C α))
    (separable_prod_X_sub_C_iff'.mpr fun _ _ _ _ h => h).squarefree ?_
  rw [← LinearMap.ker_eq_top, eq_top_iff, ← hf]
  refine iSup_le fun α v hv => ?_
  by_cases hα : f.HasEigenvalue α
  · rw [LinearMap.mem_ker, ← Finset.prod_erase_mul _ _ (hfin.mem_toFinset.mpr hα), map_mul,
      End.mul_apply]
    have : aeval f (X - C α) v = 0 := by
      simp [End.mem_eigenspace_iff.mp hv]
    rw [this, map_zero]
  · rw [End.hasEigenvalue_iff, not_not] at hα
    rw [hα, Submodule.mem_bot] at hv
    rw [hv]; exact zero_mem _

theorem isSemisimple_prodMap [FiniteDimensional ℂ V] [FiniteDimensional ℂ V'] {f : End ℂ V}
    {g : End ℂ V'} (hf : f.IsSemisimple) (hg : g.IsSemisimple) :
    End.IsSemisimple (f.prodMap g : End ℂ (V × V')) := by
  refine isSemisimple_of_iSup_eigenspace ?_
  rw [eq_top_iff, ← Submodule.prod_top, ← hf.iSup_eigenspace_eq_top, ← hg.iSup_eigenspace_eq_top,
    LinearMap.prod_eq_sup_map, Submodule.map_iSup, Submodule.map_iSup]
  refine sup_le (iSup_mono fun α => ?_) (iSup_mono fun α => ?_)
  · rintro _ ⟨v, hv, rfl⟩
    simpa [End.mem_eigenspace_iff] using hv
  · rintro _ ⟨v, hv, rfl⟩
    simpa [End.mem_eigenspace_iff] using hv

theorem isSemisimple_tensorMap [FiniteDimensional ℂ V] [FiniteDimensional ℂ V'] {f : End ℂ V}
    {g : End ℂ V'} (hf : f.IsSemisimple) (hg : g.IsSemisimple) :
    End.IsSemisimple (TensorProduct.map f g : End ℂ (V ⊗[ℂ] V')) := by
  have h1 : End.IsSemisimple (f.rTensor V' : End ℂ (V ⊗[ℂ] V')) :=
    isSemisimple_map (End.rTensorAlgHom ℂ V V') hf
  have h2 : End.IsSemisimple (g.lTensor V : End ℂ (V ⊗[ℂ] V')) :=
    isSemisimple_map (End.lTensorAlgHom ℂ V' V) hg
  have e : (TensorProduct.map f g : End ℂ (V ⊗[ℂ] V')) = f.rTensor V' * g.lTensor V := by
    ext; simp
  rw [e]
  refine End.IsSemisimple.mul_of_commute ?_ h1 h2
  show _ = _
  ext; simp

theorem aeval_dualMap (f : End ℂ V) (p : ℂ[X]) :
    aeval (f.dualMap : End ℂ (Dual ℂ V)) p = (aeval f p : End ℂ V).dualMap := by
  have hp : ∀ n : ℕ, (f.dualMap : End ℂ (Dual ℂ V)) ^ n = (f ^ n : End ℂ V).dualMap := by
    intro n
    induction n with
    | zero => ext; simp
    | succ n ih => rw [pow_succ, ih, pow_succ']; ext; simp
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, hp, hq]; ext; simp
  | monomial n a => rw [aeval_monomial, aeval_monomial, hp]; ext; simp

theorem isSemisimple_dualMap [FiniteDimensional ℂ V] {f : End ℂ V} (hf : f.IsSemisimple) :
    End.IsSemisimple (f.dualMap : End ℂ (Dual ℂ V)) :=
  End.isSemisimple_of_squarefree_aeval_eq_zero hf.minpoly_squarefree (by
    rw [aeval_dualMap, minpoly.aeval]; ext; simp)

def diagEnd {ι : Type*} (c : ι → ℂ) : End ℂ (ι → ℂ) where
  toFun v i := c i * v i
  map_add' v v' := by ext; simp [mul_add]
  map_smul' a v := by ext; simp [mul_left_comm]

@[simp] theorem diagEnd_apply {ι : Type*} (c v : ι → ℂ) (i : ι) : diagEnd c v i = c i * v i := rfl

theorem isSemisimple_diagEnd {ι : Type*} [Finite ι] (c : ι → ℂ) : (diagEnd c).IsSemisimple := by
  classical
  have := Fintype.ofFinite ι
  refine isSemisimple_of_iSup_eigenspace (eq_top_iff.mpr fun v _ => ?_)
  rw [← Finset.univ_sum_single v]
  refine Submodule.sum_mem _ fun i _ => Submodule.mem_iSup_of_mem (c i) ?_
  rw [End.mem_eigenspace_iff]
  ext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [hj]

def shiftEnd (n : ℕ) : End ℂ (Fin n → ℂ) where
  toFun v i := if 1 ≤ (i : ℕ) then v ⟨i - 1, by omega⟩ else 0
  map_add' v v' := by ext i; by_cases hi : 1 ≤ (i : ℕ) <;> simp [hi]
  map_smul' a v := by ext i; by_cases hi : 1 ≤ (i : ℕ) <;> simp [hi]

theorem shiftEnd_apply {n : ℕ} (v : Fin n → ℂ) (i : Fin n) :
    shiftEnd n v i = if 1 ≤ (i : ℕ) then v ⟨i - 1, by omega⟩ else 0 := rfl

theorem shiftEnd_pow_apply {n : ℕ} (k : ℕ) (v : Fin n → ℂ) (i : Fin n) :
    (shiftEnd n ^ k) v i = if k ≤ (i : ℕ) then v ⟨i - k, by omega⟩ else 0 := by
  induction k generalizing i with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', End.mul_apply, shiftEnd_apply]
    by_cases h1 : 1 ≤ (i : ℕ)
    · rw [if_pos h1, ih]
      by_cases h2 : k + 1 ≤ (i : ℕ)
      · rw [if_pos h2, if_pos (by simp only; omega)]
        congr 2
        simp only; omega
      · rw [if_neg h2, if_neg (by simp only; omega)]
    · rw [if_neg h1, if_neg (by omega)]

theorem isNilpotent_shiftEnd (n : ℕ) : IsNilpotent (shiftEnd n) :=
  ⟨n, LinearMap.ext fun v => funext fun i => by
    rw [shiftEnd_pow_apply, if_neg (by omega)]; rfl⟩

end Lin

end GlobalTheory.WeilDeligne
end
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAlgEquivRootOfUnityEqPow
attribute [-instance] _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

namespace GlobalTheory.MemLoc

open IsLocalRing

theorem exists_algEquiv_rootOfUnity_eq_pow (V K : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K]
    (hfin : Finite (V ⧸ maximalIdeal V)) (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    [Algebra V Ω] [IsScalarTower V K Ω] :
    ∃ φ : Ω ≃ₐ[K] Ω, ∀ (x : Ω) (m : ℕ), (m : V) ∉ maximalIdeal V → x ^ m = 1 →
      φ x = x ^ Nat.card (V ⧸ maximalIdeal V) := by
  have : IsGalois K Ω := {}
  have hc : SMulCommClass (Ω ≃ₐ[K] Ω) V Ω := ⟨fun g v x => by
    rw [← IsScalarTower.algebraMap_smul K v x, ← IsScalarTower.algebraMap_smul K v (g • x)]
    exact map_smul g _ _⟩
  let : TopologicalSpace (integralClosure V Ω) := ⊥
  have : DiscreteTopology (integralClosure V Ω) := ⟨rfl⟩
  have : ContinuousSMul (Ω ≃ₐ[K] Ω) (integralClosure V Ω) := by
    rw [continuousSMul_iff_stabilizer_isOpen]
    intro x
    have := stabilizer_isOpen_of_isIntegral (K := K) (x : Ω)
    convert this using 1
    ext g
    simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
    exact Subtype.ext_iff
  have : Algebra.IsInvariant V (integralClosure V Ω) (Ω ≃ₐ[K] Ω) := by
    constructor
    intro b hb
    obtain ⟨k, hk⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := K) (b : Ω)).2
      fun g => congrArg Subtype.val (hb g)
    have hint : IsIntegral V k := by
      have h2 : IsIntegral V (algebraMap K Ω k) := hk ▸ b.2
      exact (isIntegral_algebraMap_iff (algebraMap K Ω).injective).1 h2
    obtain ⟨v, hv⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
    refine ⟨v, Subtype.ext ?_⟩
    rw [← hk, ← hv, ← IsScalarTower.algebraMap_apply]
    rfl
  have hinj : Function.Injective (algebraMap V Ω) := by
    rw [IsScalarTower.algebraMap_eq V K Ω]
    exact (algebraMap K Ω).injective.comp (IsFractionRing.injective V K)
  have : FaithfulSMul V (integralClosure V Ω) := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro a b hab
    exact hinj (congrArg Subtype.val hab)
  obtain ⟨Q, hQ, hQo⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral
    (S := integralClosure V Ω) (maximalIdeal V)
  let : Field (V ⧸ maximalIdeal V) := Ideal.Quotient.field _
  let : Field (integralClosure V Ω ⧸ Q) := Ideal.Quotient.field _
  let : Fintype (V ⧸ maximalIdeal V) := Fintype.ofFinite _
  have : Algebra.IsAlgebraic (V ⧸ maximalIdeal V) (integralClosure V Ω ⧸ Q) := by
    have hi : Algebra.IsIntegral (V ⧸ maximalIdeal V) (integralClosure V Ω ⧸ Q) :=
      Ideal.Quotient.algebra_isIntegral_of_liesOver _ _
    exact hi.isAlgebraic
  obtain ⟨σ, hσ⟩ := Ideal.Quotient.stabilizerHom_surjective_of_profinite (G := Ω ≃ₐ[K] Ω)
    (maximalIdeal V) Q
    (FiniteField.frobeniusAlgEquivOfAlgebraic (V ⧸ maximalIdeal V) _)
  have hu : Q.under V = maximalIdeal V := hQo.over.symm
  have hF : IsArithFrobAt V σ.1 Q := by
    intro x
    have h := DFunLike.congr_fun hσ (Ideal.Quotient.mk _ x)
    rw [← Ideal.Quotient.eq, map_pow, hu, Nat.card_eq_fintype_card]
    exact h
  refine ⟨σ.1, fun x m hm hx => ?_⟩
  have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; exact hm (by simp))
  have hxi : IsIntegral V x := IsIntegral.of_pow hm0 (by rw [hx]; exact isIntegral_one)
  have hmQ : ((m : ℕ) : integralClosure V Ω) ∉ Q := by
    intro h
    apply hm
    rw [← hu, Ideal.under_def, Ideal.mem_comap, map_natCast]
    exact h
  have h := AlgHom.IsArithFrobAt.apply_of_pow_eq_one hF (ζ := ⟨x, hxi⟩) (m := m)
    (Subtype.ext hx) hmQ
  rw [hu] at h
  exact congrArg Subtype.val h

end GlobalTheory.MemLoc
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilGroupIsSemisimpleOfSemisimpleFrob
attribute [-instance] _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

open NumberField IsDedekindDomain ReciprocityTheory.Gal Polynomial Module GlobalTheory.WeilDeligne

namespace GlobalTheory.WeilDeligne

open NumberField IsDedekindDomain Polynomial Module in
theorem isSemisimple_of_mul_eq_one' {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] {f g : End ℂ V} (hf : f.IsSemisimple) (hgf : g * f = 1) :
    g.IsSemisimple := by
  apply _root_.GlobalTheory.WeilDeligne.isSemisimple_of_iSup_eigenspace
  have htop : ⨆ α, f.eigenspace α = ⊤ :=
    hf.iSup_maxGenEigenspace_eq_top_iff.1 (Module.End.iSup_maxGenEigenspace_eq_top f)
  rw [eq_top_iff, ← htop]
  refine iSup_le fun α => le_trans ?_ (le_iSup _ α⁻¹)
  intro v hv
  rw [Module.End.mem_eigenspace_iff] at hv ⊢
  have h1 : v = α • g v := by
    have := congrArg g hv
    rwa [← Module.End.mul_apply, hgf, Module.End.one_apply, map_smul] at this
  by_cases hα : α = 0
  · subst hα
    rw [zero_smul] at h1
    simp [h1]
  · conv_rhs => rw [h1]
    rw [smul_smul, inv_mul_cancel₀ hα, one_smul]

open NumberField IsDedekindDomain Polynomial Module in
theorem isSemisimple_of_isUnit_of_pow_isSemisimple {V : Type*} [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] {f : End ℂ V} (hf : IsUnit f) {m : ℕ} (hm : 0 < m)
    (hfm : (f ^ m).IsSemisimple) : f.IsSemisimple := by
  have hint : IsIntegral ℂ (f ^ m) := Algebra.IsIntegral.isIntegral _
  have hX : ¬ X ∣ minpoly ℂ (f ^ m) := by
    rintro ⟨q, hq⟩
    have h0 : aeval (f ^ m) q = 0 := by
      have h1 := minpoly.aeval ℂ (f ^ m)
      rw [hq, map_mul, aeval_X] at h1
      exact (hf.pow m).mul_right_eq_zero.1 h1
    have hq0 : q ≠ 0 := by
      rintro rfl
      exact minpoly.ne_zero hint (by simpa using hq)
    have hdeg := natDegree_le_of_dvd (minpoly.dvd ℂ (f ^ m) h0) hq0
    rw [hq, natDegree_mul X_ne_zero hq0, natDegree_X] at hdeg
    omega
  have hsep : (minpoly ℂ (f ^ m)).Separable :=
    PerfectField.separable_iff_squarefree.2 hfm.minpoly_squarefree
  have hXe : ¬ X ∣ expand ℂ m (minpoly ℂ (f ^ m)) := by
    rw [X_dvd_iff, coeff_expand hm]
    rw [X_dvd_iff] at hX
    simpa using hX
  have hunit : IsUnit ((m : ℂ[X])) := by
    rw [← map_natCast C]
    exact isUnit_C.2 (Ne.isUnit (by exact_mod_cast hm.ne'))
  have hP : (expand ℂ m (minpoly ℂ (f ^ m))).Separable := by
    rw [separable_def, derivative_expand]
    refine IsCoprime.mul_right
      (((separable_def _).1 hsep).map (expand ℂ m).toRingHom) (IsCoprime.mul_right ?_ ?_)
    · exact isCoprime_one_right.of_isCoprime_of_dvd_right (hunit.dvd)
    · exact IsCoprime.pow_right ((Irreducible.coprime_iff_not_dvd irreducible_X).2 hXe).symm
  apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero hP.squarefree
  rw [expand_aeval]
  exact minpoly.aeval ℂ (f ^ m)

end GlobalTheory.WeilDeligne
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFrobeniusSemisimplification
attribute [-instance] _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

open NumberField IsDedekindDomain ReciprocityTheory.Gal Polynomial Module GlobalTheory.WeilDeligne

namespace GlobalTheory.WeilDeligne

section Lin

variable {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

theorem semisimplePart_mul_eq {f s N : End ℂ V} {c : ℂ} (hc : Commute f s) (hs : s.IsSemisimple)
    (hn : IsNilpotent (f - s)) (h : f * N = c • (N * f)) : s * N = c • (N * s) := by
  have key : ∀ (μ : ℂ) (k : ℕ), (f - (c * μ) • (1 : End ℂ V)) ^ k * N =
      c ^ k • (N * (f - μ • (1 : End ℂ V)) ^ k) := by
    intro μ k
    have h1 : (f - (c * μ) • (1 : End ℂ V)) * N = c • (N * (f - μ • (1 : End ℂ V))) := by
      rw [sub_mul, h, mul_sub, smul_sub]
      simp [smul_smul]
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', mul_assoc, ih, mul_smul_comm, ← mul_assoc, h1, smul_mul_assoc, smul_smul,
        mul_assoc, ← pow_succ', ← pow_succ]
  refine LinearMap.ext fun v => ?_
  have hv : v ∈ ⨆ μ, f.maxGenEigenspace μ := by
    rw [End.iSup_maxGenEigenspace_eq_top]; trivial
  induction hv using Submodule.iSup_induction' with
  | mem μ v hv =>
    have h1 := End.apply_eq_of_mem_of_comm_of_isFinitelySemisimple_of_isNil hv hc
      hs.isFinitelySemisimple hn
    have h2 : N v ∈ f.maxGenEigenspace (c * μ) := by
      rw [End.mem_maxGenEigenspace] at hv ⊢
      obtain ⟨k, hk⟩ := hv
      refine ⟨k, ?_⟩
      have := LinearMap.congr_fun (key μ k) v
      simpa [hk] using this
    have h3 := End.apply_eq_of_mem_of_comm_of_isFinitelySemisimple_of_isNil h2 hc
      hs.isFinitelySemisimple hn
    simp [h1, h3, smul_smul]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy]

end Lin

theorem isNilpotent_pow_sub_one {R : Type*} [Ring R] {u : R} (hu : IsNilpotent (u - 1)) (k : ℕ) :
    IsNilpotent (u ^ k - 1) := by
  rw [← mul_geom_sum]
  refine Commute.isNilpotent_mul_right ?_ hu
  exact Commute.sum_right _ _ _ fun i _ =>
    ((Commute.refl u).pow_right i).sub_left (Commute.one_left _)

theorem commute_of_commute_pow {R : Type*} [Ring R] [Algebra ℂ R] {u : Rˣ} {T : R} {m : ℕ}
    (hm : 0 < m) (hu : IsNilpotent ((u : R) - 1)) (h : Commute ((u : R) ^ m) T) :
    Commute (u : R) T := by
  set L : End ℂ R := LinearMap.mulLeft ℂ (u : R) with hL
  set M : End ℂ R := LinearMap.mulRight ℂ ((u⁻¹ : Rˣ) : R) with hM
  have hLM : Commute L M := LinearMap.commute_mulLeft_right _ _
  have hu' : IsNilpotent (((u⁻¹ : Rˣ) : R) - 1) := by
    have : ((u⁻¹ : Rˣ) : R) - 1 = -(((u : R) - 1) * (u⁻¹ : Rˣ)) := by simp [sub_mul]
    rw [this]
    refine (Commute.isNilpotent_mul_right ?_ hu).neg
    exact (Commute.refl (u : R)).units_inv_right.sub_left (Commute.one_left _)
  have hL1 : IsNilpotent (L - 1) := by
    have : L - 1 = LinearMap.mulLeft ℂ ((u : R) - 1) := by ext; simp [hL, sub_mul]
    rw [this]; exact (LinearMap.isNilpotent_mulLeft_iff _ _).mpr hu
  have hM1 : IsNilpotent (M - 1) := by
    have : M - 1 = LinearMap.mulRight ℂ (((u⁻¹ : Rˣ) : R) - 1) := by ext; simp [hM, mul_sub]
    rw [this]; exact (LinearMap.isNilpotent_mulRight_iff _ _).mpr hu'
  have hU : IsNilpotent (L * M - 1) := by
    have : L * M - 1 = (L - 1) * M + (M - 1) := by noncomm_ring
    rw [this]
    have c1 : Commute (L - 1) M := hLM.sub_left (Commute.one_left _)
    refine Commute.isNilpotent_add ?_ (c1.isNilpotent_mul_right hL1) hM1
    exact (c1.mul_left (Commute.refl M)).sub_right (Commute.one_right _)
  set U := L * M with hUdef
  have hsum : IsUnit (∑ i ∈ Finset.range m, U ^ i) := by
    have e : ∑ i ∈ Finset.range m, U ^ i =
        algebraMap ℂ (End ℂ R) (m : ℂ) + ∑ i ∈ Finset.range m, (U ^ i - 1) := by
      simp [Finset.sum_sub_distrib]
    rw [e]
    refine IsNilpotent.isUnit_add_left_of_commute ?_ ?_ ?_
    · refine Commute.isNilpotent_sum (fun i _ => isNilpotent_pow_sub_one hU i) fun i j _ _ => ?_
      exact (((Commute.refl U).pow_pow i j).sub_left (Commute.one_left _)).sub_right
        (Commute.one_right _)
    · exact (IsUnit.mk0 (m : ℂ) (by exact_mod_cast hm.ne')).map _
    · exact Algebra.commute_algebraMap_right _ _
  have h1 : (U ^ m - 1) T = 0 := by
    rw [hUdef, hLM.mul_pow, hL, hM, LinearMap.pow_mulLeft, LinearMap.pow_mulRight]
    simp only [LinearMap.sub_apply, End.mul_apply, LinearMap.mulLeft_apply,
      LinearMap.mulRight_apply, End.one_apply]
    rw [← mul_assoc, h.eq, mul_assoc, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val,
      ← Units.val_mul, inv_pow]
    simp
  rw [← geom_sum_mul, End.mul_apply] at h1
  have h2 : (U - 1) T = 0 := by
    have := ((End.isUnit_iff _).mp hsum).1
    exact this (by rw [h1, map_zero])
  have h3 : (u : R) * (T * (u⁻¹ : Rˣ)) = T := by
    simpa [hUdef, hL, hM, sub_eq_zero] using h2
  calc (u : R) * T = (u : R) * (T * (u⁻¹ : Rˣ)) * u := by simp [mul_assoc]
    _ = T * u := by rw [h3]

end GlobalTheory.WeilDeligne
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanMkQOneTmul
attribute [-instance] _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

namespace GlobalTheory.SpanQuotientTensor

theorem span_mkQ_one_tmul {K D : Type} [Field K] [AddCommGroup D] [Module K D]
    (F : Type) [Field F] [Algebra K F] (N : Submodule F (TensorProduct K F D)) :
    Submodule.span F (Set.range (fun x : D => N.mkQ ((1 : F) ⊗ₜ[K] x))) = ⊤ := by
  rw [eq_top_iff]
  rintro q -
  obtain ⟨y, rfl⟩ := N.mkQ_surjective q
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    have h : (a ⊗ₜ[K] x : TensorProduct K F D) = a • ((1 : F) ⊗ₜ[K] x) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [h, map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)
  | add y z hy hz =>
    rw [map_add]
    exact Submodule.add_mem _ hy hz

theorem main : (let d1 : {LL U D : Type} → [inst : Field LL] → [inst_1 : Field U] → [inst_2 : AddCommGroup D] → [inst_3 : Module LL D] → (U →+* Module.End LL D) → (F : Type) → [inst_4 : Field F] → [inst_5 : Algebra LL F] → (U →+* F) → Submodule F (TensorProduct LL F D) := @(fun {LL U D : Type} [Field LL] [Field U] [AddCommGroup D] [Module LL D] (m : U →+* Module.End LL D) (F : Type) [Field F] [Algebra LL F] (τ : U →+* F) ↦ ⨆ (c : U), LinearMap.range (LinearMap.baseChange F ((m : U → Module.End LL D) c) - (τ : U → F) c • LinearMap.id)); let d2 : {LL U D : Type} → [inst : Field LL] → [inst_1 : Field U] → [inst_2 : AddCommGroup D] → [inst_3 : Module LL D] → (U →+* Module.End LL D) → (F : Type) → [inst_4 : Field F] → [Algebra LL F] → (U →+* F) → Type := @(fun {LL U D : Type} [Field LL] [Field U] [AddCommGroup D] [Module LL D] (m : U →+* Module.End LL D) (F : Type) [Field F] [Algebra LL F] (τ : U →+* F) ↦ TensorProduct LL F D ⧸ d1 m F τ); let d3 : {LL U D : Type} → [inst : Field LL] → [inst_1 : Field U] → [inst_2 : AddCommGroup D] → [inst_3 : Module LL D] → (m : U →+* Module.End LL D) → (F : Type) → [inst_4 : Field F] → [inst_5 : Algebra LL F] → (τ : U →+* F) → TensorProduct LL F D →ₗ[F] d2 m F τ := @(fun {LL U D : Type} [Field LL] [Field U] [AddCommGroup D] [Module LL D] (m : U →+* Module.End LL D) (F : Type) [Field F] [Algebra LL F] (τ : U →+* F) ↦ Submodule.mkQ (d1 m F τ)); let d4 : {LL U D : Type} → [inst : Field LL] → [inst_1 : Field U] → [inst_2 : AddCommGroup D] → [inst_3 : Module LL D] → (m : U →+* Module.End LL D) → (F : Type) → [inst_4 : Field F] → [inst_5 : Algebra LL F] → (τ : U →+* F) → D → d2 m F τ := @(fun {LL U D : Type} [Field LL] [Field U] [AddCommGroup D] [Module LL D] (m : U →+* Module.End LL D) (F : Type) [Field F] [Algebra LL F] (τ : U →+* F) (x : D) ↦ (d3 m F τ : TensorProduct LL F D → d2 m F τ) ((1 : F) ⊗ₜ[LL] x)); ∀ {LL U D : Type} [inst : Field LL] [inst_1 : Field U] [inst_2 : AddCommGroup D] [inst_3 : Module LL D] (m : U →+* Module.End LL D) (F : Type) [inst_4 : Field F] [inst_5 : Algebra LL F] (τ : U →+* F), Submodule.span F (Set.range (d4 m F τ)) = ⊤) := by
  intro d1 d2 d3 d4 LL U D _ _ _ _ m F _ _ τ
  exact span_mkQ_one_tmul F (d1 m F τ)

end GlobalTheory.SpanQuotientTensor
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalLetter
attribute [-instance] _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open Polynomial TensorProduct Module
open NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.WeilDeligne

namespace GlobalTheory.Pst

section Letter

variable {LL U D : Type} [Field LL] [Field U] [AddCommGroup D] [Module LL D] (m : U →+* End LL D)
  (F : Type) [Field F] [Algebra LL F] (τ : U →+* F)

def letterKer : Submodule F (F ⊗[LL] D) :=
  ⨆ c : U, LinearMap.range ((m c).baseChange F - τ c • LinearMap.id)

def Letter : Type := (F ⊗[LL] D) ⧸ letterKer m F τ

instance instAddCommGroupLetter : AddCommGroup (Letter m F τ) := inferInstanceAs (AddCommGroup (_ ⧸ letterKer m F τ))

instance instModuleLetter : Module F (Letter m F τ) := inferInstanceAs (Module F (_ ⧸ letterKer m F τ))

def letterQ : F ⊗[LL] D →ₗ[F] Letter m F τ := (letterKer m F τ).mkQ

theorem ker_letterQ : LinearMap.ker (letterQ m F τ) = letterKer m F τ := Submodule.ker_mkQ _

def letterMk (x : D) : Letter m F τ := letterQ m F τ (1 ⊗ₜ x)

@[simp] theorem letterMk_zero : letterMk m F τ 0 = 0 := by simp [letterMk]

theorem letterMk_smul (a : LL) (x : D) :
    letterMk m F τ (a • x) = algebraMap LL F a • letterMk m F τ x := by
  rw [letterMk, letterMk, ← map_smul, tmul_smul, algebraMap_smul]

theorem letterMk_mul (c : U) (x : D) : letterMk m F τ (m c x) = τ c • letterMk m F τ x := by
  rw [letterMk, letterMk, ← map_smul, ← sub_eq_zero, ← map_sub, ← LinearMap.mem_ker, ker_letterQ]
  exact Submodule.mem_iSup_of_mem c ⟨1 ⊗ₜ x, rfl⟩

theorem span_letterMk : Submodule.span F (Set.range (letterMk m F τ)) = ⊤ := by
  first
  | exact @_root_.GlobalTheory.SpanQuotientTensor.main
  | exact _root_.GlobalTheory.SpanQuotientTensor.main
  | (apply _root_.GlobalTheory.SpanQuotientTensor.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.SpanQuotientTensor.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SpanQuotientTensor.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SpanQuotientTensor.main ..)

def letterMap (T : End LL D) (hT : ∀ c, T * m c = m c * T) : End F (Letter m F τ) :=
  Submodule.mapQ _ _ (T.baseChange F) (iSup_le fun c => by
    rintro _ ⟨y, rfl⟩
    refine Submodule.mem_iSup_of_mem c ⟨T.baseChange F y, ?_⟩
    have := LinearMap.congr_fun (congrArg (LinearMap.baseChange F) (hT c)) y
    rw [LinearMap.baseChange_mul, LinearMap.baseChange_mul, End.mul_apply, End.mul_apply] at this
    simp [this])

@[simp] theorem letterMap_mk (T : End LL D) (hT : ∀ c, T * m c = m c * T) (x : D) :
    letterMap m F τ T hT (letterMk m F τ x) = letterMk m F τ (T x) := rfl

theorem finiteDimensional_letter {ι : Type} [Fintype ι] (b : ι → D)
    (hb : ∀ x, ∃ c : ι → U, x = ∑ i, m (c i) (b i)) : FiniteDimensional F (Letter m F τ) := by
  refine ⟨⟨(Set.finite_range fun i => letterMk m F τ (b i)).toFinset, eq_top_iff.mpr ?_⟩⟩
  rw [← span_letterMk, Submodule.span_le, Set.Finite.coe_toFinset]
  rintro _ ⟨x, rfl⟩
  obtain ⟨c, rfl⟩ := hb x
  rw [letterMk, tmul_sum, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  have := letterMk_mul m F τ (c i) (b i)
  rw [letterMk] at this
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end Letter

end GlobalTheory.Pst
end
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
attribute [-instance] _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

namespace GlobalTheory.PRep

variable {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V]

def eig (ρ : Representation k G V) (H : Subgroup G) (χ : H →* kˣ) : Submodule k V where
  carrier := {v | ∀ h : H, ρ (h : G) v = (χ h : k) • v}
  add_mem' := by
    intro a b ha hb h
    rw [map_add, ha h, hb h, smul_add]
  zero_mem' := by intro h; simp
  smul_mem' := by
    intro c v hv h
    rw [map_smul, hv h, smul_comm]

def fixed (ρ : Representation k G V) (H : Subgroup G) : Submodule k V := eig ρ H 1

def twKer (ρ : Representation k G V) (N : Subgroup G) (ψ : N →* kˣ) : Submodule k V :=
  Submodule.span k {w | ∃ (n : N) (v : V), w = ρ (n : G) v - (ψ n : k) • v}

abbrev TwJacquet (ρ : Representation k G V) (N : Subgroup G) (ψ : N →* kˣ) : Type := V ⧸ twKer ρ N ψ

abbrev Jacquet (ρ : Representation k G V) (N : Subgroup G) : Type := TwJacquet ρ N 1

section Top
variable [TopologicalSpace G]

def IsSmooth (ρ : Representation k G V) : Prop := ∀ v : V, IsOpen {g : G | ρ g v = v}

end Top

variable {W : Type} [AddCommGroup W] [Module k W]

def indSpace (H : Subgroup G) (σ : Representation k H W) : Submodule k (G → W) where
  carrier := {f | ∀ (h : H) (g : G), f (h * g) = σ h (f g)}
  add_mem' := by
    intro a b ha hb h g
    simp [ha h g, hb h g]
  zero_mem' := by intro h g; simp
  smul_mem' := by
    intro c f hf h g
    simp [hf h g]

section Top2
variable [TopologicalSpace G] [IsTopologicalGroup G]

def smoothPart (ρ : Representation k G V) : Submodule k V where
  carrier := {v | IsOpen {g : G | ρ g v = v}}
  add_mem' := by
    intro a b ha hb
    let T : Subgroup G :=
      { carrier := {g | ρ g (a + b) = a + b}
        mul_mem' := by intro x y hx hy; simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *; rw [hy, hx]
        one_mem' := by simp
        inv_mem' := by
          intro x hx
          simp only [Set.mem_setOf_eq] at *
          conv_lhs => rw [← hx]
          rw [← Module.End.mul_apply, ← map_mul]; simp }
    refine T.isOpen_of_mem_nhds (g := 1) (Filter.mem_of_superset ((ha.inter hb).mem_nhds (by simp)) ?_)
    rintro g ⟨h1, h2⟩
    show ρ g (a + b) = a + b
    rw [map_add, h1, h2]
  zero_mem' := by simp
  smul_mem' := by
    intro c v hv
    by_cases hc : c = 0
    · simp [hc]
    · have : {g : G | ρ g (c • v) = c • v} = {g : G | ρ g v = v} := by
        ext g; simp [smul_right_inj hc]
      show IsOpen {g : G | ρ g (c • v) = c • v}
      rw [this]; exact hv

theorem smoothPart_stable (ρ : Representation k G V) (g : G) (v : V) (hv : v ∈ smoothPart ρ) :
    ρ g v ∈ smoothPart ρ := by
  have : {x : G | ρ x (ρ g v) = ρ g v} = (fun x => g⁻¹ * x * g) ⁻¹' {x : G | ρ x v = v} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, map_mul, Module.End.mul_apply]
    constructor
    · intro h; rw [h, ← Module.End.mul_apply, ← map_mul]; simp
    · intro h
      have := congrArg (ρ g) h
      rwa [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at this
  show IsOpen {x : G | ρ x (ρ g v) = ρ g v}
  rw [this]
  exact IsOpen.preimage (by fun_prop) hv

end Top2

end GlobalTheory.PRep
end
end

section
-- module Solutions.AlpoGe.Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsOpenStabilizer
attribute [-instance] _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

theorem UpperTheory.Reformulated.B.IsOpenStabilizer.isOpen_stab_of_mem_nhds :
    ∀ {G : Type} [inst : Group G] [inst_1 : TopologicalSpace G] [IsTopologicalGroup G] {V : Type} [inst_3 : AddCommGroup V]
      [inst_4 : _root_.Module ℂ V] (ρ : Representation ℂ G V) (v : V),
      {g : G | ((ρ : G → V →ₗ[ℂ] V) g : V → V) v = v} ∈ nhds (1 : G) →
        IsOpen {g : G | ((ρ : G → V →ₗ[ℂ] V) g : V → V) v = v} := by
  intro G _ _ _ V _ _ ρ v h
  let H : Subgroup G :=
    { carrier := {g : G | ρ g v = v}
      one_mem' := by simp
      mul_mem' := by
        intro a b ha hb
        have ha' : ρ a v = v := ha
        have hb' : ρ b v = v := hb
        change ρ (a * b) v = v
        rw [map_mul, Module.End.mul_apply, hb', ha']
      inv_mem' := by
        intro a ha
        have ha' : ρ a v = v := ha
        change ρ a⁻¹ v = v
        calc ρ a⁻¹ v = ρ a⁻¹ (ρ a v) := by rw [ha']
          _ = ρ (a⁻¹ * a) v := by rw [map_mul, Module.End.mul_apply]
          _ = v := by simp }
  exact H.isOpen_of_mem_nhds (g := 1) h
end

section
-- module Solutions.AlpoGe.Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
attribute [-instance] _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open Matrix

namespace GlobalTheory.CuspRep

theorem isOpen_stab_of_mem_nhds {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : G →* Module.End ℂ V) (v : V)
    (h : {g : G | ρ g v = v} ∈ nhds (1 : G)) : IsOpen {g : G | ρ g v = v} :=
  UpperTheory.Reformulated.B.IsOpenStabilizer.isOpen_stab_of_mem_nhds ρ v h

end GlobalTheory.CuspRep
end
end

section
-- module Solutions.AlpoGe.Development.AutomorphicArithmetic.IntegralCasts.AlgebraicInfinityType.InfinityType
attribute [-instance] _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

namespace Reformulated.AlgebraicInfinityType

open NumberField

@[ext]
structure InfinityType (F : Type*) [Field F] (n : ℕ) where

  pairs : (F →+* ℂ) → Multiset (ℂ × ℂ)
  card_pairs : ∀ σ, Multiset.card (pairs σ) = n
  sub_int : ∀ σ, ∀ p ∈ pairs σ, ∃ m : ℤ, p.1 - p.2 = m
  pairs_conjugate : ∀ σ, pairs (ComplexEmbedding.conjugate σ) = (pairs σ).map Prod.swap

namespace InfinityType

variable {F : Type*} [Field F] {n : ℕ}

def exponents (t : InfinityType F n) (σ : F →+* ℂ) : Multiset ℂ :=
  (t.pairs σ).map Prod.fst

def IsAlgebraic (t : InfinityType F n) : Prop :=
  ∀ σ, ∀ a ∈ t.exponents σ, ∃ m : ℤ, a = ((n : ℂ) - 1) / 2 + m

def IsRegular (t : InfinityType F n) : Prop :=
  ∀ σ, (t.exponents σ).Nodup

def IsRegularAlgebraic (t : InfinityType F n) : Prop :=
  t.IsAlgebraic ∧ t.IsRegular

end InfinityType

end Reformulated.AlgebraicInfinityType
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsIrreducibleIff
attribute [-instance] _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open Topology

namespace GlobalTheory.CuspRep

variable {G : Type} [Group G]

variable [TopologicalSpace G]

variable (G) in

structure SmIrr where

  V : Type
  [acg : AddCommGroup V]
  [mod : Module ℂ V]

  ρ : Representation ℂ G V
  smooth : GlobalTheory.PRep.IsSmooth ρ
  irred : ρ.IsIrreducible

attribute [instance] SmIrr.acg SmIrr.mod

variable (G) in

instance SmIrr.setoid : Setoid (SmIrr G) where
  r σ σ' := Nonempty (σ.ρ.Equiv σ'.ρ)
  iseqv := ⟨fun σ => ⟨.refl σ.ρ⟩, fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ ⟨e'⟩ => ⟨e.trans e'⟩⟩

end GlobalTheory.CuspRep
end
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsOpenKerFinIdele
attribute [-instance] _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open NumberField IsDedekindDomain Topology
open scoped ContDiff

namespace GlobalTheory.CuspRep

theorem eq_one_of_pow_near {z : ℂ} (h : ∀ n : ℕ, ‖z ^ n - 1‖ < 1 / 2) : z = 1 := by
  by_contra hz
  have hp : 0 < ‖z - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 hz)
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / ‖z - 1‖)
  have h1 : ‖(∑ k ∈ Finset.range n, z ^ k) - n‖ ≤ n / 2 := by
    have : (∑ k ∈ Finset.range n, z ^ k) - n = ∑ k ∈ Finset.range n, (z ^ k - 1) := by
      rw [Finset.sum_sub_distrib]; simp
    rw [this]
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun k _ => (h k).le).trans ?_
    simp; linarith
  have h2 : (n : ℝ) / 2 ≤ ‖∑ k ∈ Finset.range n, z ^ k‖ := by
    have := norm_sub_norm_le (n : ℂ) (∑ k ∈ Finset.range n, z ^ k)
    rw [norm_sub_rev, Complex.norm_natCast] at this
    linarith
  have h3 := h n
  rw [← geom_sum_mul, norm_mul] at h3
  rw [div_lt_iff₀ hp] at hn
  nlinarith

end GlobalTheory.CuspRep
end
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
attribute [-instance] _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.Mem.Chr

section Inhabitant

instance negTwoFact : Fact (∀ r : ℚ, r ^ 2 ≠ -2 + 0 * r) := ⟨fun r h => by nlinarith [sq_nonneg r]⟩

end Inhabitant

end GlobalTheory.Mem.Chr
end
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToZModPowKummerEqIff
attribute [-instance] _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.Mem.Chr.negTwoFact
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Polynomial Module

namespace GlobalTheory.WeilDeligne

section Roots

variable {Ω : Type*} [Field Ω] [IsAlgClosed Ω] (l : ℕ) [Fact l.Prime]

def rootSeq (a : Ω) (n : ℕ) : Ω :=
  Nat.rec a (fun _ y => (IsAlgClosed.exists_pow_nat_eq y (Fact.out : l.Prime).pos).choose) n

@[simp] theorem rootSeq_zero (a : Ω) : rootSeq l a 0 = a := rfl

theorem rootSeq_succ_pow (a : Ω) (n : ℕ) : rootSeq l a (n + 1) ^ l = rootSeq l a n :=
  (IsAlgClosed.exists_pow_nat_eq (rootSeq l a n) (Fact.out : l.Prime).pos).choose_spec

theorem rootSeq_pow (a : Ω) (n : ℕ) : rootSeq l a n ^ l ^ n = a := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', pow_mul, rootSeq_succ_pow, ih]

variable (Ω) [CharZero Ω]

theorem exists_unitySeq : ∃ z : ℕ → Ω, (∀ n, IsPrimitiveRoot (z n) (l ^ n)) ∧
    ∀ n, z (n + 1) ^ l = z n := by
  have hl : l.Prime := Fact.out
  have : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr hl.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω l
  refine ⟨fun n => Nat.casesOn n 1 (rootSeq l ζ), fun n => ?_, fun n => ?_⟩
  · cases n with
    | zero => simp
    | succ n =>
      have h := orderOf_eq_prime_pow (x := rootSeq l ζ n) (p := l) (n := n)
        (by rw [rootSeq_pow]; exact hζ.ne_one hl.one_lt)
        (by rw [pow_succ, pow_mul, rootSeq_pow, hζ.pow_eq_one])
      rw [← h]
      exact IsPrimitiveRoot.orderOf _
  · cases n with
    | zero => exact hζ.pow_eq_one
    | succ n => exact rootSeq_succ_pow l ζ n

def unitySeq : ℕ → Ω := (exists_unitySeq Ω l).choose

theorem unitySeq_primitive (n : ℕ) : IsPrimitiveRoot (unitySeq Ω l n) (l ^ n) :=
  (exists_unitySeq Ω l).choose_spec.1 n

theorem unitySeq_succ_pow (n : ℕ) : unitySeq Ω l (n + 1) ^ l = unitySeq Ω l n :=
  (exists_unitySeq Ω l).choose_spec.2 n

theorem unitySeq_pow_eq_iff (n a b : ℕ) :
    unitySeq Ω l n ^ a = unitySeq Ω l n ^ b ↔ (a : ZMod (l ^ n)) = b := by
  have hN0 : l ^ n ≠ 0 := pow_ne_zero _ (Fact.out : l.Prime).ne_zero
  have hζ := unitySeq_primitive Ω l n
  have hu : IsPrimitiveRoot (hζ.isUnit hN0).unit (l ^ n) :=
    IsPrimitiveRoot.coe_units_iff.mp (by simpa using hζ)
  rw [ZMod.natCast_eq_natCast_iff, hu.eq_orderOf, ← pow_eq_pow_iff_modEq, Units.ext_iff]
  simp

def unityPow (n : ℕ) (c : ℤ_[l]) : Ω := unitySeq Ω l n ^ (PadicInt.toZModPow n c).val

theorem unityPow_eq_pow_iff {n k : ℕ} {c : ℤ_[l]} :
    unityPow Ω l n c = unitySeq Ω l n ^ k ↔ PadicInt.toZModPow n c = k := by
  rw [unityPow, unitySeq_pow_eq_iff, ZMod.natCast_zmod_val]

theorem unityPow_add (n : ℕ) (c d : ℤ_[l]) :
    unityPow Ω l n (c + d) = unityPow Ω l n c * unityPow Ω l n d := by
  conv_rhs => rw [unityPow, unityPow, ← pow_add]
  rw [unityPow_eq_pow_iff]; simp

theorem unityPow_mul (n : ℕ) (c d : ℤ_[l]) :
    unityPow Ω l n (c * d) = unityPow Ω l n d ^ (PadicInt.toZModPow n c).val := by
  conv_rhs => rw [unityPow, ← pow_mul]
  rw [unityPow_eq_pow_iff]; simp [mul_comm]

theorem unityPow_pow (n : ℕ) (c : ℤ_[l]) : unityPow Ω l n c ^ l ^ n = 1 := by
  rw [unityPow, ← pow_mul, mul_comm, pow_mul, (unitySeq_primitive Ω l n).pow_eq_one, one_pow]

variable {Ω} in

theorem existsUnique_unityPow {y : ℕ → Ω} (h0 : ∀ n, y n ^ l ^ n = 1)
    (hy : ∀ n, y (n + 1) ^ l = y n) : ∃! c : ℤ_[l], ∀ n, y n = unityPow Ω l n c := by
  have : ∀ n, NeZero (l ^ n) := fun n => ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  choose k _ hk using fun n => (unitySeq_primitive Ω l n).eq_pow_of_pow_eq_one (h0 n)
  have h3 : ∀ n, (l : ℤ) ^ n ∣ (k (n + 1) : ℤ) - k n := fun n => by
    rw [← Nat.cast_pow, ← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, Int.cast_natCast,
      Int.cast_natCast, sub_eq_zero, ← unitySeq_pow_eq_iff Ω, hk, ← hy, ← hk, ← pow_mul, mul_comm,
      pow_mul, unitySeq_succ_pow]
  refine ⟨PadicInt.ofIntSeq _
    (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub (fun n => (k n : ℤ)) l h3), fun n => ?_,
    fun c hc => PadicInt.ext_of_toZModPow.mp fun n => ?_⟩
  · rw [← hk, eq_comm, unityPow_eq_pow_iff,
      PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub (fun n => (k n : ℤ)) l h3 n, Int.cast_natCast]
  · rw [PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub (fun n => (k n : ℤ)) l h3 n, Int.cast_natCast,
      ← unityPow_eq_pow_iff Ω, ← hc, hk]

end Roots

variable {E Ω : Type*} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]

section Kummer

variable (l : ℕ) [Fact l.Prime]

variable (E Ω) in

def zetaPow (n : ℕ) (c : ℤ_[l]) : Ω :=
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  unityPow Ω l n c

variable (Ω) in

def rootOf (a : E) (n : ℕ) : Ω :=
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  rootSeq l (algebraMap E Ω a) n

omit [NumberField E] in

theorem rootOf_pow (a : E) (n : ℕ) : rootOf Ω l a n ^ l ^ n = algebraMap E Ω a :=
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  rootSeq_pow l _ n

omit [NumberField E] in

theorem rootOf_ne_zero {a : E} (ha : a ≠ 0) (n : ℕ) : rootOf Ω l a n ≠ 0 := by
  intro h0
  have := rootOf_pow (Ω := Ω) l a n
  rw [h0, zero_pow (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)] at this
  exact ha ((map_eq_zero _).mp this.symm)

end Kummer

end GlobalTheory.WeilDeligne
end
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
attribute [-instance] _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.Mem.Chr.negTwoFact
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal

noncomputable section
namespace GlobalTheory.SplitWeil

variable (k : Type*) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def nabs (x : kˣ) : ℝ := (distribHaarChar k x : ℝ≥0)

def KO (n : Type*) [Fintype n] [DecidableEq n] : Subgroup (GL n k) :=
  (Matrix.GeneralLinearGroup.map (n := n) (algebraMap 𝒪[k] k)).range

def KOne (n : Type*) [Fintype n] [DecidableEq n] : Subgroup (GL n k) :=
  ((Matrix.GeneralLinearGroup.map (n := n) (IsLocalRing.residue 𝒪[k])).ker).map
    (Matrix.GeneralLinearGroup.map (n := n) (algebraMap 𝒪[k] k))

variable {k}

def IsUnram (μ : kˣ →* ℂˣ) : Prop := ∀ x : kˣ, valuation k (x : k) = 1 → μ x = 1

instance matrixMeasurableSpace {m n α : Type*} [MeasurableSpace α] : MeasurableSpace (Matrix m n α) :=
  (MeasurableSpace.pi : MeasurableSpace (m → n → α))

end GlobalTheory.SplitWeil
end
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
attribute [-instance] _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.Mem.Chr.negTwoFact
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil ValuativeRel
open scoped TensorProduct

namespace GlobalTheory.SmGL

section General

variable {F G H V W U : Type} [Field F] [Group G] [Group H] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W] [AddCommGroup U] [Module F U]

def twist (ρ : Representation F G V) (χ : G →* Fˣ) : Representation F G V where
  toFun g := (χ g : F) • ρ g
  map_one' := by simp
  map_mul' a b := by
    ext v
    simp [smul_smul, mul_comm]

@[simp] theorem twist_apply (ρ : Representation F G V) (χ : G →* Fˣ) (g : G) (v : V) :
    twist ρ χ g v = (χ g : F) • ρ g v := rfl

@[simp] theorem twist_one (ρ : Representation F G V) : twist ρ 1 = ρ := by
  ext g v; simp

def ofChar (χ : G →* Fˣ) : Representation F G F := twist (Representation.trivial F G F) χ

@[simp] theorem ofChar_apply (χ : G →* Fˣ) (g : G) (x : F) : ofChar χ g x = (χ g : F) * x := by
  simp [ofChar]

theorem isIrreducible_ofChar (χ : G →* Fˣ) : (ofChar χ).IsIrreducible := by
  have : Nontrivial (Subrepresentation (ofChar χ)) := ⟨⊥, ⊤, fun h => by
    have := congrArg Subrepresentation.toSubmodule h
    exact bot_ne_top (α := Submodule F F) this⟩
  refine ⟨fun S => ?_⟩
  rcases eq_bot_or_eq_top S.toSubmodule with h | h
  · exact Or.inl (Subrepresentation.toSubmodule_injective h)
  · exact Or.inr (Subrepresentation.toSubmodule_injective h)

def IsSubquotient (σ : Representation F G W) (ρ : Representation F G V) : Prop :=
  ∃ (S : Subrepresentation ρ) (f : S.toRepresentation.IntertwiningMap σ), Function.Surjective f

def piTensor {α : Type} {Γ X : α → Type} [∀ a, Group (Γ a)] [∀ a, AddCommGroup (X a)]
    [∀ a, Module F (X a)] (ρ : ∀ a, Representation F (Γ a) (X a)) :
    Representation F (∀ a, Γ a) (⨂[F] a, X a) :=
  PiTensorProduct.mapMonoidHom.comp
    (MonoidHom.pi fun a => (ρ a).comp (Pi.evalMonoidHom Γ a))

@[simp] theorem piTensor_tprod {α : Type} {Γ X : α → Type} [∀ a, Group (Γ a)]
    [∀ a, AddCommGroup (X a)] [∀ a, Module F (X a)] (ρ : ∀ a, Representation F (Γ a) (X a))
    (g : ∀ a, Γ a) (x : ∀ a, X a) :
    piTensor ρ g (PiTensorProduct.tprod F x) = PiTensorProduct.tprod F fun a => ρ a (g a) (x a) := by
  exact PiTensorProduct.map_tprod _ _

section Top

variable [TopologicalSpace G]

def IsSmoothChar (χ : G →* Fˣ) : Prop := IsOpen (χ.ker : Set G)

theorem IsSmoothChar.comp [TopologicalSpace H] {χ : G →* Fˣ} (hχ : IsSmoothChar χ) (s : H →* G)
    (hs : Continuous s) : IsSmoothChar (χ.comp s) :=
  IsOpen.preimage hs hχ

variable [IsTopologicalGroup G]

theorem mem_smoothPart_of_nhds {ρ : Representation F G V} {v : V}
    (h : {g : G | ρ g v = v} ∈ nhds (1 : G)) : v ∈ smoothPart ρ :=
  Subgroup.isOpen_of_mem_nhds
    { carrier := {g | ρ g v = v}
      mul_mem' := by
        intro x y hx hy
        simp only [Set.mem_ofPred_eq, map_mul, Module.End.mul_apply] at *
        rw [hy, hx]
      one_mem' := by simp
      inv_mem' := by
        intro x hx
        simp only [Set.mem_ofPred_eq] at *
        conv_lhs => rw [← hx]
        rw [← Module.End.mul_apply, ← map_mul]; simp } h

theorem isSmooth_of_nhds {ρ : Representation F G V}
    (h : ∀ v, {g : G | ρ g v = v} ∈ nhds (1 : G)) : IsSmooth ρ := fun v =>
  mem_smoothPart_of_nhds (h v)

theorem isSmooth_twist {ρ : Representation F G V} (hρ : IsSmooth ρ) {χ : G →* Fˣ}
    (hχ : IsSmoothChar χ) : IsSmooth (twist ρ χ) :=
  isSmooth_of_nhds fun v => Filter.mem_of_superset (((hρ v).inter hχ).mem_nhds (by simp)) (by
    rintro g ⟨h1, h2⟩
    have h1' : ρ g v = v := h1
    have h2' : χ g = 1 := h2
    simp [h1', h2'])

theorem isSmooth_ofChar_iff (χ : G →* Fˣ) : IsSmooth (ofChar χ) ↔ IsSmoothChar χ := by
  refine ⟨fun h => ?_, fun h => isSmooth_twist (fun v => by simp) h⟩
  have : (χ.ker : Set G) = {g | ofChar χ g 1 = 1} := by ext g; simp
  unfold IsSmoothChar; rw [this]; exact h 1

end Top

def IsSphericalFor (ρ : Representation F G V) (K : Subgroup G) : Prop := fixed ρ K ≠ ⊥

end General

end GlobalTheory.SmGL
end
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
attribute [-instance] _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.Mem.Chr.negTwoFact _root_.GlobalTheory.SplitWeil.matrixMeasurableSpace
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

namespace GlobalTheory.SmGL

section Blocks

open Matrix

variable (R : Type) [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]

def blk (e : (Σ a, m a) ≃ n) (i : n) : α := (e.symm i).1

open Matrix in
variable (R : Type) [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] in
omit [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n]
  [DecidableEq n] in

@[simp] theorem _root_.GlobalTheory.SmGL.blk_apply (e : (Σ a, m a) ≃ n) (a : α) (i : m a) :
    _root_.GlobalTheory.SmGL.blk e (e ⟨a, i⟩) = a := by
  simp [_root_.GlobalTheory.SmGL.blk]

abbrev Levi (m : α → Type) [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] : Type :=
  ∀ a, GL (m a) R

def parab (e : (Σ a, m a) ≃ n) : Subgroup (GL n R) where
  carrier := {g | (g : Matrix n n R).BlockTriangular (blk e)}
  one_mem' := by
    show ((1 : GL n R) : Matrix n n R).BlockTriangular _
    rw [Units.val_one]; exact blockTriangular_one
  mul_mem' := by
    intro x y hx hy
    show ((x * y : GL n R) : Matrix n n R).BlockTriangular _
    rw [Units.val_mul]; exact BlockTriangular.mul hx hy
  inv_mem' := by
    intro x hx
    show ((x⁻¹ : GL n R) : Matrix n n R).BlockTriangular _
    have : Invertible (x : Matrix n n R) := x.invertible
    rw [Matrix.coe_units_inv]
    exact blockTriangular_inv_of_blockTriangular hx

variable {R}

open Matrix in
variable (R : Type) [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] in
variable {R} in
omit [Fintype α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] in

theorem _root_.GlobalTheory.SmGL.mem_parab {e : (Σ a, m a) ≃ n} {g : GL n R} :
    g ∈ _root_.GlobalTheory.SmGL.parab R e ↔ ∀ i j, _root_.GlobalTheory.SmGL.blk e j <
      _root_.GlobalTheory.SmGL.blk e i → (g : Matrix n n R) i j = 0 :=
  ⟨fun h _ _ hij => h hij, fun h _ _ hij => h _ _ hij⟩

open Matrix in
variable (R : Type) [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] in
variable {R} in
omit [Fintype α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] in

theorem _root_.GlobalTheory.SmGL.mem_parab_iff {e : (Σ a, m a) ≃ n} {g : GL n R} :
    g ∈ _root_.GlobalTheory.SmGL.parab R e ↔ ∀ a b (i : m a) (j : m b), b < a →
      (g : Matrix n n R) (e ⟨a, i⟩) (e ⟨b, j⟩) = 0 := by
  rw [_root_.GlobalTheory.SmGL.mem_parab]
  constructor
  · intro h a b i j hab
    exact h _ _ (by simpa using hab)
  · intro h i j hij
    simpa using h (e.symm i).1 (e.symm j).1 (e.symm i).2 (e.symm j).2 hij

variable (R)

def diagBlock (e : (Σ a, m a) ≃ n) (a : α) : parab R e →* Matrix (m a) (m a) R where
  toFun p := ((p : GL n R) : Matrix n n R).submatrix (fun i => e ⟨a, i⟩) (fun i => e ⟨a, i⟩)
  map_one' := by
    ext i j
    simp [Matrix.one_apply]
  map_mul' x y := by
    ext i j
    show ((x.1 : Matrix n n R) * (y.1 : Matrix n n R)) _ _ = _
    simp only [mul_apply, submatrix_apply]
    rw [← e.sum_comp, Fintype.sum_sigma, Finset.sum_eq_single a]
    · intro b _ hb
      refine Finset.sum_eq_zero fun l _ => ?_
      rcases lt_or_gt_of_ne hb with h | h
      · rw [mem_parab_iff.1 x.2 a b i l h, zero_mul]
      · rw [mem_parab_iff.1 y.2 b a l j h, mul_zero]
    · simp

def leviProj (e : (Σ a, m a) ≃ n) : parab R e →* Levi R m :=
  MonoidHom.pi fun a => (diagBlock R e a).toHomUnits

@[simp] theorem leviProj_apply (e : (Σ a, m a) ≃ n) (p : parab R e) (a : α) (i j : m a) :
    (leviProj R e p a : Matrix (m a) (m a) R) i j =
      ((p : GL n R) : Matrix n n R) (e ⟨a, i⟩) (e ⟨a, j⟩) := rfl

def unipRad (e : (Σ a, m a) ≃ n) : Subgroup (GL n R) := (leviProj R e).ker.map (parab R e).subtype

variable {R}

variable (R)

def opp (e : (Σ a, m a) ≃ n) : (Σ a : αᵒᵈ, m (OrderDual.ofDual a)) ≃ n := e

def parabLower (e : (Σ a, m a) ≃ n) : Subgroup (GL n R) := parab R (opp e)

def leviProjLower (e : (Σ a, m a) ≃ n) : parabLower R e →* Levi R m := leviProj R (opp e)

@[simp] theorem leviProjLower_apply (e : (Σ a, m a) ≃ n) (p : parabLower R e) (a : α) (i j : m a) :
    (leviProjLower R e p a : Matrix (m a) (m a) R) i j =
      ((p : GL n R) : Matrix n n R) (e ⟨a, i⟩) (e ⟨a, j⟩) := rfl

def stdBlocks {s N : ℕ} (d : Fin s → ℕ) (h : ∑ a, d a = N) : (Σ a, Fin (d a)) ≃ Fin N :=
  finSigmaFinEquiv.trans (finCongr h)

@[reducible] def Two (a b : Type) : Bool → Type
  | false => a
  | true => b

variable {a b : Type}

instance instFintypeTwo [Fintype a] [Fintype b] : ∀ x, Fintype (Two a b x)
  | false => inferInstanceAs (Fintype a)
  | true => inferInstanceAs (Fintype b)

instance instDecidableEqTwo [DecidableEq a] [DecidableEq b] : ∀ x, DecidableEq (Two a b x)
  | false => inferInstanceAs (DecidableEq a)
  | true => inferInstanceAs (DecidableEq b)

end Blocks

end GlobalTheory.SmGL
end
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
attribute [-instance] _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.Mem.Chr.negTwoFact
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil ValuativeRel
open scoped TensorProduct

namespace GlobalTheory.SmGL

section Local

open Matrix

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem nabs_pos' (x : kˣ) : 0 < nabs k x := by
  unfold nabs; exact_mod_cast MeasureTheory.distribHaarChar_pos

theorem nabs_mul' (x y : kˣ) : nabs k (x * y) = nabs k x * nabs k y := by simp [nabs]

open scoped Pointwise in

theorem nabs_eq_one {x : kˣ} (hx : valuation k (x : k) = 1) : nabs k x = 1 := by
  borelize k
  have hc : IsCompact (𝒪[k] : Set k) := IsNonarchimedeanLocalField.isCompact_closedBall k 1
  have ho : IsOpen (𝒪[k] : Set k) := Valuation.isOpen_integer
  let K : TopologicalSpace.PositiveCompacts k := ⟨⟨(𝒪[k] : Set k), hc⟩, by
    rw [show interior ((⟨(𝒪[k] : Set k), hc⟩ : TopologicalSpace.Compacts k).carrier) =
      (𝒪[k] : Set k) from ho.interior_eq]
    exact ⟨0, zero_mem _⟩⟩
  have h1 : MeasureTheory.Measure.addHaarMeasure K (𝒪[k] : Set k) = 1 :=
    MeasureTheory.Measure.addHaarMeasure_self
  have hs : x • (𝒪[k] : Set k) = (𝒪[k] : Set k) := by
    ext y
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    show valuation k (((x⁻¹ : kˣ) : k) * y) ≤ 1 ↔ valuation k y ≤ 1
    simp [hx]
  have := MeasureTheory.distribHaarChar_eq_of_measure_smul_eq_mul
    (μ := MeasureTheory.Measure.addHaarMeasure K) (s := (𝒪[k] : Set k)) (g := x) (r := 1)
    (by simp [h1]) (by simp [h1]) (by simp [hs])
  simp [nabs, this]

def absPow (s : ℂ) : kˣ →* ℂˣ :=
  MonoidHom.toHomUnits
    { toFun := fun x => ((nabs k x : ℝ) : ℂ) ^ s
      map_one' := by simp [nabs]
      map_mul' := fun x y => by
        rw [nabs_mul', Complex.ofReal_mul,
          Complex.mul_cpow_ofReal_nonneg (nabs_pos' k x).le (nabs_pos' k y).le] }

theorem val_absPow (s : ℂ) (x : kˣ) : (absPow k s x : ℂ) = ((nabs k x : ℝ) : ℂ) ^ s := rfl

@[simp] theorem absPow_zero : absPow k 0 = 1 := by
  ext x; simp [val_absPow]

theorem isUnram_absPow (s : ℂ) : IsUnram (absPow k s) := fun x hx => by
  ext; simp [val_absPow, nabs_eq_one k hx]

variable {k} in

theorem isSmoothChar_of_isUnram {χ : kˣ →* ℂˣ} (h : IsUnram χ) : IsSmoothChar χ := by
  have ho : IsOpen (𝒪[k] : Set k) := Valuation.isOpen_integer
  have h1 : IsOpen ({x : kˣ | (x : k) ∈ (𝒪[k] : Set k)} ∩
      {x : kˣ | ((x⁻¹ : kˣ) : k) ∈ (𝒪[k] : Set k)}) :=
    (ho.preimage Units.continuous_val).inter (ho.preimage Units.continuous_coe_inv)
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset (h1.mem_nhds ?_) ?_)
  · exact ⟨one_mem 𝒪[k], by simpa using one_mem 𝒪[k]⟩
  · rintro x ⟨hx, hx'⟩
    have a1 : valuation k (x : k) ≤ 1 := hx
    have a2 : valuation k ((x⁻¹ : kˣ) : k) ≤ 1 := hx'
    refine h x (le_antisymm a1 ?_)
    rw [Units.val_inv_eq_inv_val, map_inv₀] at a2
    exact (inv_le_one₀ (zero_lt_iff.2 (by simp))).1 a2

def ord (x : kˣ) : ℤ :=
  -WithZero.log (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt k (valuation k (x : k)))

variable {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

section Det

variable {R : Type} [CommRing R]

def detChar (n : Type) [Fintype n] [DecidableEq n] (χ : Rˣ →* ℂˣ) : GL n R →* ℂˣ :=
  χ.comp GeneralLinearGroup.det

@[simp] theorem detChar_apply (χ : Rˣ →* ℂˣ) (g : GL n R) :
    detChar n χ g = χ (GeneralLinearGroup.det g) := rfl

theorem continuous_glDet [TopologicalSpace R] [IsTopologicalRing R] :
    Continuous (GeneralLinearGroup.det : GL n R → Rˣ) := by
  refine Units.continuous_iff.2 ⟨Units.continuous_val.matrix_det, ?_⟩
  simp only [← map_inv]
  exact Units.continuous_coe_inv.matrix_det

theorem IsSmoothChar.detChar [TopologicalSpace R] [IsTopologicalRing R] {χ : Rˣ →* ℂˣ}
    (h : IsSmoothChar χ) : IsSmoothChar (detChar n χ) :=
  h.comp _ continuous_glDet

def HasCentralChar (π : Representation ℂ (GL n R) V) (ω : Rˣ →* ℂˣ) : Prop :=
  ∀ z v, π (GeneralLinearGroup.scalar n z) v = (ω z : ℂ) • v

end Det

def modExp (m : α → Type) [∀ a, Fintype (m a)] (a : α) : ℤ :=
  (∑ b with a < b, (Fintype.card (m b) : ℤ)) - ∑ b with b < a, (Fintype.card (m b) : ℤ)

def deltaHalf (m : α → Type) [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] : Levi k m →* ℂˣ :=
  ∏ a, (detChar (m a) (absPow k ((modExp m a : ℂ) / 2))).comp (Pi.evalMonoidHom (fun a => GL (m a) k) a)

variable {k}

def IsCuspidal (π : Representation ℂ (GL n k) V) : Prop :=
  IsSmooth π ∧ ∀ (s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ n), unipRad k e ≠ ⊥ →
    Subsingleton (Jacquet π (unipRad k e))

section Borel

variable [LinearOrder n]

variable (k n)

variable {k n}

omit [LinearOrder n] in

def IsSpherical (π : Representation ℂ (GL n k) V) : Prop := IsSphericalFor π (KO k n)

end Borel

end Local

end GlobalTheory.SmGL
end
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
attribute [-instance] _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.Mem.Chr.negTwoFact
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

open MeasureTheory Matrix
open scoped NNReal TensorProduct

noncomputable section
namespace GlobalTheory.LGrp
open GlobalTheory.PRep

section Blocks
variable {k n α : Type} [Field k] [Fintype n] [DecidableEq n] [LinearOrder α]

variable [TopologicalSpace k] [IsTopologicalRing k] [T2Space k]

instance locallyCompact_GL [LocallyCompactSpace k] : LocallyCompactSpace (GL n k) := by
  haveI : LocallyCompactSpace (Matrix n n k) := inferInstanceAs (LocallyCompactSpace (n → n → k))
  haveI : LocallyCompactSpace (Matrix n n k)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace

end Blocks

section LocalGL
open ValuativeRel
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

instance t2Space_of_nonarchimedeanLocalField : T2Space k := by
  let _ := IsTopologicalAddGroup.rightUniformSpace k
  have := isUniformAddGroup_of_addCommGroup (G := k)
  infer_instance

end LocalGL

end GlobalTheory.LGrp
end
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
attribute [-instance] _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.Mem.Chr.negTwoFact _root_.GlobalTheory.SplitWeil.matrixMeasurableSpace
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct

namespace GlobalTheory.Mem.Vol

section Volume

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

def IsCMFam {I : Type} (τ : I → (E →+* ℂ)) : Prop :=
  Function.Bijective fun i => NumberField.InfinitePlace.mk (τ i)

end Volume

end GlobalTheory.Mem.Vol
end
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
attribute [-instance] _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.Mem.Chr.negTwoFact _root_.GlobalTheory.SplitWeil.matrixMeasurableSpace
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Topology Filter
open scoped TensorProduct

namespace GlobalTheory.LocalData

section Completion

variable {F : Type} [Field F] [NumberField F] (p : HeightOneSpectrum (𝓞 F))

@[reducible] def complRel : ValuativeRel (p.adicCompletion F) :=
  ValuativeRel.ofValuation (Valued.v : Valuation (p.adicCompletion F) (WithZero (Multiplicative ℤ)))

end Completion

end GlobalTheory.LocalData

end
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NontrivialOfIrreducible
attribute [-instance] _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.Mem.Chr.negTwoFact
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open GlobalTheory.PRep

namespace GlobalTheory.SmGL

section Groth

variable (G : Type) [Group G] [TopologicalSpace G]

structure IrrRep : Type 1 where

  V : Type
  [acg : AddCommGroup V]
  [mod : Module ℂ V]

  ρ : Representation ℂ G V
  smooth : IsSmooth ρ
  irr : ρ.IsIrreducible

attribute [instance] IrrRep.acg IrrRep.mod

def IrrRep.ofChar {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (χ : G →* ℂˣ)
    (h : IsSmoothChar χ) : IrrRep G :=
  ⟨ℂ, SmGL.ofChar χ, (isSmooth_ofChar_iff χ).2 h, isIrreducible_ofChar χ⟩

instance IrrRep.setoid : Setoid (IrrRep G) where
  r σ τ := Nonempty (σ.ρ.Equiv τ.ρ)
  iseqv := ⟨fun _ => ⟨.refl _⟩, fun ⟨φ⟩ => ⟨φ.symm⟩, fun ⟨φ⟩ ⟨ψ⟩ => ⟨φ.trans ψ⟩⟩

def IrrCl : Type 1 := Quotient (IrrRep.setoid G)

variable {G} {V W U : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup U] [Module ℂ U]

def IrrRep.cl (σ : IrrRep G) : IrrCl G := Quotient.mk _ σ

def IrrCl.rep (c : IrrCl G) : IrrRep G := Quotient.out c

@[simp] theorem IrrCl.cl_rep (c : IrrCl G) : c.rep.cl = c := Quotient.out_eq c

end Groth

end GlobalTheory.SmGL
end
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsReadingLaws
attribute [-instance] _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.Mem.Chr.negTwoFact
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

namespace GlobalTheory.SplitRead

open ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open GlobalTheory.WeilDeligne GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

section Local

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

structure Irr (n : ℕ) : Type 1 where

  V : Type
  [acg : AddCommGroup V]
  [mod : Module ℂ V]

  π : Representation ℂ (GL (Fin n) k) V
  smooth : IsSmooth π
  irr : π.IsIrreducible

attribute [instance] Irr.acg Irr.mod

variable {k} in

@[reducible] def Irr.toIrrRep {n : ℕ} (π : Irr k n) : IrrRep (GL (Fin n) k) := ⟨π.V, π.π, π.smooth, π.irr⟩

variable {k} in

@[reducible] def Irr.ofIrrRep {n : ℕ} (σ : IrrRep (GL (Fin n) k)) : Irr k n := ⟨σ.V, σ.ρ, σ.smooth, σ.irr⟩

end Local

attribute [local instance] GlobalTheory.LocalData.complRel

end GlobalTheory.SplitRead
end
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FormsStable
attribute [-instance] _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.Mem.Chr.negTwoFact _root_.GlobalTheory.SplitWeil.matrixMeasurableSpace
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

namespace GlobalTheory.LvT

open Classical NumberField

structure LocF (q : ℕ) (F : Type) [Field F] where
  K : Type
  [fld : Field K]
  O : Subring K
  frac : ∀ x : K, x ∈ O ∨ x⁻¹ ∈ O
  q_ne : (q : K) ≠ 0
  sep : ∀ x : K, x ≠ 0 → ∃ (n : ℤ) (y : K), y ∈ O ∧ y⁻¹ ∈ O ∧ x = (q : K) ^ n * y
  res : O →+* F
  res_surj : Function.Surjective res
  res_ker : ∀ x : O, res x = 0 ↔ ∃ y : O, (x : K) = (q : K) * y

attribute [instance] LocF.fld

namespace LocF

variable {q : ℕ} {F : Type} [Field F] (Lc : LocF q F) (n : ℕ)

@[ext] structure Raw where
  L : Submodule Lc.O (Fin n → Lc.K)
  f : (Fin n → Lc.K) → F

end LocF

end GlobalTheory.LvT
end
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
attribute [-instance] _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.Mem.Chr.negTwoFact _root_.GlobalTheory.SmGL.instDecidableEqTwo _root_.GlobalTheory.SmGL.instFintypeTwo _root_.GlobalTheory.SplitWeil.matrixMeasurableSpace
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

namespace GlobalTheory.GLq

open Polynomial
open scoped Classical

abbrev Gn (g n : ℕ) : Type := GL (Fin n) (ZMod g)

abbrev Mt (g n : ℕ) : Type := Matrix (Fin n) (Fin n) (ZMod g)

def IsIrr {G : Type} [Group G] (χ : G → ℂ) : Prop :=
  ∃ V : FDRep ℂ G, CategoryTheory.Simple V ∧ ∀ x, V.character x = χ x

variable {g : ℕ} [Fact g.Prime]

def InPar (a : ℕ) {n : ℕ} (M : Mt g n) : Prop := ∀ i j : Fin n, (j : ℕ) < a → a ≤ (i : ℕ) → M i j = 0

end GlobalTheory.GLq
end
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCharLab
attribute [-instance] _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.Mem.Chr.negTwoFact _root_.GlobalTheory.SmGL.instDecidableEqTwo _root_.GlobalTheory.SmGL.instFintypeTwo _root_.GlobalTheory.SplitWeil.matrixMeasurableSpace
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

namespace GlobalTheory.GLp

open Polynomial GlobalTheory.GLq
open scoped Classical

variable (g : ℕ) [Fact g.Prime]

def inc (n : ℕ) : GL (Fin n) ℤ_[g] →* GL (Fin n) ℚ_[g] :=
  Matrix.GeneralLinearGroup.map (algebraMap ℤ_[g] ℚ_[g])

def red (n : ℕ) : GL (Fin n) ℤ_[g] →* Gn g n := Matrix.GeneralLinearGroup.map (PadicInt.toZMod (p := g))

end GlobalTheory.GLp
end
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
attribute [-instance] _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.Mem.Chr.negTwoFact
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL

namespace GlobalTheory

namespace SmGL

section Ring

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

structure Segment : Type 1 where

  d : ℕ
  d_pos : 0 < d

  start : IrrCl (GL (Fin d) k)
  cusp : ∃ σ : IrrRep (GL (Fin d) k), σ.cl = start ∧ IsCuspidal σ.ρ

  len : ℕ
  len_pos : 0 < len

variable {k} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def IrrRep.det (n : Type) [Fintype n] [DecidableEq n] (χ : kˣ →* ℂˣ) (h : IsSmoothChar χ) :
    IrrRep (GL n k) :=
  IrrRep.ofChar (detChar n χ) h.detChar

end Ring

end SmGL

end GlobalTheory
end
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
attribute [-instance] _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.Mem.Chr.negTwoFact
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL

namespace GlobalTheory.LocGL

section General

variable {G H M V W X : Type} [Group G] [Group H] [Group M] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup X] [Module ℂ X]

def IsCosocle (σ : Representation ℂ G W) (π : Representation ℂ G V) : Prop :=
  σ.IsIrreducible ∧ ∃ f : π.IntertwiningMap σ, Function.Surjective f ∧
    ∀ S : Subrepresentation π, IsCoatom S → S = f.ker

end General

end GlobalTheory.LocGL
end
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
attribute [-instance] _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.Mem.Chr.negTwoFact
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix

namespace GlobalTheory.LocGL

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

section Invariance

variable {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
  [Fintype n] [DecidableEq n]

theorem isSmoothChar_absPow (s : ℂ) : IsSmoothChar (absPow k s) := isSmoothChar_of_isUnram (isUnram_absPow k s)

end Invariance

variable (k) in

abbrev IrrGL : Type 1 := Σ n : ℕ, IrrCl (GL (Fin n) k)

namespace IrrGL

abbrev rep (x : IrrGL k) : Representation ℂ (GL (Fin x.1) k) x.2.rep.V := x.2.rep.ρ

def of {N : ℕ} (π : Representation ℂ (GL (Fin N) k) V) (hs : IsSmooth π) (hi : π.IsIrreducible) : IrrGL k :=
  ⟨N, (⟨V, π, hs, hi⟩ : IrrRep _).cl⟩

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in

@[simp] theorem of_rep (x : IrrGL k) : of x.rep x.2.rep.smooth x.2.rep.irr = x := Sigma.ext rfl (heq_of_eq (IrrCl.cl_rep _))

def ofChar (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) : IrrGL k := ⟨1, (IrrRep.det (Fin 1) χ hχ).cl⟩

def IsCusp (x : IrrGL k) : Prop := 0 < x.1 ∧ IsCuspidal x.rep

end IrrGL

end GlobalTheory.LocGL
end
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemIffForallMemLocalizeRingOfIntegers
attribute [-instance] _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.Mem.Chr.negTwoFact _root_.GlobalTheory.SplitWeil.matrixMeasurableSpace
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Matrix
open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.LocalLattice

set_option linter.unusedSectionVars false

section Localize

variable {O : Type*} (K : Type*) [CommRing O] [IsDedekindDomain O] [Field K] [Algebra O K]
  [IsFractionRing O K]
  {V : Type*} [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]

instance instIsScalarTowerLocalRing (v : HeightOneSpectrum O) :
    IsScalarTower O (v.valuationSubringAtPrime K) V :=
  IsScalarTower.to₁₂₄ O (v.valuationSubringAtPrime K) K V

end Localize

end GlobalTheory.LocalLattice
end
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EncardSmulMemLeEncardSmulInterNonempty
attribute [-instance] _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.LocalLattice.instIsScalarTowerLocalRing _root_.GlobalTheory.Mem.Chr.negTwoFact _root_.GlobalTheory.SplitWeil.matrixMeasurableSpace
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

open MeasureTheory Set
open scoped ENNReal Pointwise

namespace GlobalTheory

section Multiplicity

variable {G X : Type*} [Group G] [MulAction G X]

@[to_additive
]
theorem encard_smul_mem_le_encard_smul_inter_nonempty (B : Set X) (x : X) :
    {g : G | g • x ∈ B}.encard ≤ {g : G | (g • B ∩ B).Nonempty}.encard := by
  rcases eq_empty_or_nonempty {g : G | g • x ∈ B} with h | ⟨g₀, hg₀⟩
  · simp [h]
  · refine Set.encard_le_encard_of_injOn (f := fun g => g * g₀⁻¹) ?_ ?_
    · intro g hg
      refine ⟨g • x, ⟨g₀ • x, hg₀, ?_⟩, hg⟩
      simp [smul_smul]
    · intro a _ b _ hab
      exact mul_right_cancel hab

variable [MeasurableSpace X] {μ : Measure X} [MeasurableConstSMul G X]
  [SMulInvariantMeasure G X μ] [Countable G] {B D : Set X}

omit [MeasurableSpace X] [MeasurableConstSMul G X] [Countable G] in

@[to_additive
]
theorem tsum_indicator_smul_eq_encard (B : Set X) (x : X) :
    ∑' g : G, ((fun y => g • y) ⁻¹' B).indicator (fun _ => (1 : ℝ≥0∞)) x
      = ({g : G | g • x ∈ B}.encard : ℝ≥0∞) := by
  rw [← ENNReal.tsum_set_one, tsum_subtype {g : G | g • x ∈ B} (fun _ => (1 : ℝ≥0∞))]
  refine tsum_congr fun g => ?_
  by_cases h : g • x ∈ B <;> simp [Set.indicator, h]

@[to_additive
]
theorem sum_restrict_preimage_smul_le (hB : NullMeasurableSet B μ) {m : ℝ≥0∞}
    (hm : ∀ᵐ x ∂μ.restrict D, ({g : G | g • x ∈ B}.encard : ℝ≥0∞) ≤ m) :
    (Measure.sum fun g : G => (μ.restrict D).restrict ((fun y => g • y) ⁻¹' B))
      ≤ m • μ.restrict D := by
  have hB' : ∀ g : G, NullMeasurableSet ((fun y => g • y) ⁻¹' B) (μ.restrict D) := fun g =>
    (hB.preimage (measurePreserving_smul g μ).quasiMeasurePreserving).mono
      Measure.restrict_le_self
  rw [Measure.le_iff]
  intro A hA
  rw [Measure.sum_apply _ hA, Measure.smul_apply, smul_eq_mul]
  have h1 : ∀ g : G, ((μ.restrict D).restrict ((fun y => g • y) ⁻¹' B)) A
      = ∫⁻ x in A, ((fun y => g • y) ⁻¹' B).indicator (fun _ => (1 : ℝ≥0∞)) x
          ∂(μ.restrict D) := by
    intro g
    rw [lintegral_indicator₀ ((hB' g).mono Measure.restrict_le_self), setLIntegral_one,
      Measure.restrict_apply hA,
      Measure.restrict_apply₀ ((hB' g).mono Measure.restrict_le_self), inter_comm]
  simp_rw [h1]
  rw [← lintegral_tsum fun g => (aemeasurable_const.indicator₀
    ((hB' g).mono Measure.restrict_le_self))]
  simp_rw [tsum_indicator_smul_eq_encard]
  calc ∫⁻ x in A, ({g : G | g • x ∈ B}.encard : ℝ≥0∞) ∂(μ.restrict D)
      ≤ ∫⁻ _ in A, m ∂(μ.restrict D) := lintegral_mono_ae (ae_restrict_of_ae hm)
    _ = m * (μ.restrict D) A := by rw [setLIntegral_const]

@[to_additive setLIntegral_le_mul_of_ae_covers_vadd
]
theorem setLIntegral_le_mul_of_ae_covers (hD : ∀ᵐ x ∂μ, ∃ g : G, g • x ∈ D)
    (hB : NullMeasurableSet B μ) {u : X → ℝ≥0∞} (hu : ∀ (g : G) (x : X), u (g • x) = u x)
    {m : ℝ≥0∞} (hm : ∀ᵐ x ∂μ.restrict D, ({g : G | g • x ∈ B}.encard : ℝ≥0∞) ≤ m) :
    ∫⁻ x in B, u x ∂μ ≤ m * ∫⁻ x in D, u x ∂μ := by
  have hcov : B ≤ᵐ[μ] (⋃ g : G, g • (((fun y => g • y) ⁻¹' B) ∩ D) : Set X) := by
    filter_upwards [hD] with x ⟨g, hg⟩ hx
    refine mem_iUnion.2 ⟨g⁻¹, g • x, ⟨?_, hg⟩, by simp⟩
    change g⁻¹ • g • x ∈ B
    rw [inv_smul_smul]
    exact hx
  have hB' : ∀ g : G, NullMeasurableSet ((fun y => g • y) ⁻¹' B) (μ.restrict D) := fun g =>
    (hB.preimage (measurePreserving_smul g μ).quasiMeasurePreserving).mono
      Measure.restrict_le_self
  calc ∫⁻ x in B, u x ∂μ
      ≤ ∫⁻ x in ⋃ g : G, g • (((fun y => g • y) ⁻¹' B) ∩ D), u x ∂μ :=
        lintegral_mono_set' hcov
    _ ≤ ∑' g : G, ∫⁻ x in g • (((fun y => g • y) ⁻¹' B) ∩ D), u x ∂μ := lintegral_iUnion_le _ _
    _ = ∑' g : G, ∫⁻ x, u x ∂((μ.restrict D).restrict ((fun y => g • y) ⁻¹' B)) := by
        refine tsum_congr fun g => ?_
        rw [Measure.restrict_restrict₀ (hB' g), ← image_smul,
          ← (measurePreserving_smul g μ).setLIntegral_comp_emb (measurableEmbedding_const_smul g)]
        simp only [hu]
    _ = ∫⁻ x, u x ∂(Measure.sum fun g : G =>
          (μ.restrict D).restrict ((fun y => g • y) ⁻¹' B)) := (lintegral_sum_measure _ _).symm
    _ ≤ ∫⁻ x, u x ∂(m • μ.restrict D) :=
        lintegral_mono' (sum_restrict_preimage_smul_le hB hm) le_rfl
    _ = m * ∫⁻ x in D, u x ∂μ := by rw [lintegral_smul_measure, smul_eq_mul]

omit [MeasurableConstSMul G X] [SMulInvariantMeasure G X μ] in

@[to_additive ae_encard_vadd_mem_le_one
]
theorem ae_encard_smul_mem_le_one (hD : IsFundamentalDomain G D μ) :
    ∀ᵐ x ∂μ, {g : G | g • x ∈ D}.encard ≤ 1 := by
  have h : ∀ᵐ x ∂μ, ∀ g₁ g₂ : G, g₁ ≠ g₂ → x ∉ g₁ • D ∩ g₂ • D := by
    refine ae_all_iff.2 fun g₁ => ae_all_iff.2 fun g₂ => ?_
    by_cases h : g₁ = g₂
    · simp [h]
    · filter_upwards [measure_eq_zero_iff_ae_notMem.1 (hD.aedisjoint h)] with x hx _ using hx
  filter_upwards [h] with x hx
  rw [encard_le_one_iff]
  intro a b ha hb
  by_contra hab
  refine hx a⁻¹ b⁻¹ (by simpa using hab) ⟨?_, ?_⟩
  · rw [mem_smul_set_iff_inv_smul_mem, inv_inv]; exact ha
  · rw [mem_smul_set_iff_inv_smul_mem, inv_inv]; exact hb

@[to_additive setLIntegral_le_of_isAddFundamentalDomain_of_ae_covers
]
theorem setLIntegral_le_of_isFundamentalDomain_of_ae_covers {D' : Set X}
    (hD : IsFundamentalDomain G D μ) (hD' : ∀ᵐ x ∂μ, ∃ g : G, g • x ∈ D')
    {u : X → ℝ≥0∞} (hu : ∀ (g : G) (x : X), u (g • x) = u x) :
    ∫⁻ x in D, u x ∂μ ≤ ∫⁻ x in D', u x ∂μ := by
  have := setLIntegral_le_mul_of_ae_covers hD' hD.nullMeasurableSet hu (m := 1) (by
    filter_upwards [ae_restrict_of_ae (ae_encard_smul_mem_le_one hD)] with x hx
    exact_mod_cast ENat.toENNReal_le.2 hx)
  simpa using this

@[to_additive measure_le_of_isAddFundamentalDomain_of_ae_covers
]
theorem measure_le_of_isFundamentalDomain_of_ae_covers {D' : Set X}
    (hD : IsFundamentalDomain G D μ) (hD' : ∀ᵐ x ∂μ, ∃ g : G, g • x ∈ D') : μ D ≤ μ D' := by
  simpa using setLIntegral_le_of_isFundamentalDomain_of_ae_covers hD hD' (u := fun _ => 1)
    (fun _ _ => rfl)

end Multiplicity

section Subgroup

variable {G X : Type*} [Group G] [MulAction G X] [MeasurableSpace X] {μ : Measure X}
  [MeasurableConstSMul G X] [SMulInvariantMeasure G X μ] [Countable G] {D D' : Set X}
  {K : Subgroup G}

omit [Countable G] [MeasurableConstSMul G X] [SMulInvariantMeasure G X μ] in

@[to_additive  ]
theorem pairwise_aedisjoint_out_inv_smul (hD : IsFundamentalDomain G D μ) (K : Subgroup G) :
    Pairwise (Function.onFun (AEDisjoint μ) fun q : G ⧸ K => (q.out)⁻¹ • D) := by
  intro q₁ q₂ h
  refine hD.aedisjoint fun h' => h ?_
  rw [← q₁.out_eq, ← q₂.out_eq, inv_injective h']

@[to_additive isAddFundamentalDomain_iUnion_out_neg_vadd
]
theorem isFundamentalDomain_iUnion_out_inv_smul (hD : IsFundamentalDomain G D μ)
    (K : Subgroup G) : IsFundamentalDomain K (⋃ q : G ⧸ K, (q.out)⁻¹ • D) μ where
  nullMeasurableSet := by
    have : Countable (G ⧸ K) := QuotientGroup.mk_surjective.countable
    exact .iUnion fun q => hD.nullMeasurableSet_smul _
  ae_covers := by
    filter_upwards [hD.ae_covers] with x ⟨g, hg⟩
    have hk : ((g : G ⧸ K).out)⁻¹ * g ∈ K := QuotientGroup.eq.1 (QuotientGroup.out_eq' _)
    refine ⟨⟨_, hk⟩, mem_iUnion.2 ⟨(g : G ⧸ K), g • x, hg, ?_⟩⟩
    simp [Subgroup.smul_def, smul_smul]
  aedisjoint := by
    have : Countable (G ⧸ K) := QuotientGroup.mk_surjective.countable
    intro k₁ k₂ hk
    simp only [Function.onFun, Subgroup.smul_def, smul_set_iUnion, smul_smul]
    refine AEDisjoint.iUnion_left_iff.2 fun q₁ => AEDisjoint.iUnion_right_iff.2 fun q₂ => ?_
    refine hD.aedisjoint fun h => hk ?_
    have hq : q₁ = q₂ := by
      rw [← q₁.out_eq, ← q₂.out_eq]
      refine QuotientGroup.eq.2 ?_
      have : (q₁.out)⁻¹ * q₂.out = (k₁ : G)⁻¹ * k₂ := by
        rw [eq_inv_mul_iff_mul_eq, ← mul_assoc, h, inv_mul_cancel_right]
      rw [this]
      exact K.mul_mem (K.inv_mem k₁.2) k₂.2
    subst hq
    exact Subtype.ext (mul_right_cancel h)

@[to_additive
]
theorem setLIntegral_subgroup_eq_tsum (hD : IsFundamentalDomain G D μ)
    (hD' : IsFundamentalDomain K D' μ) {u : X → ℝ≥0∞}
    (hu : ∀ (g : G) (x : X), u (g • x) = u x) :
    ∫⁻ x in D', u x ∂μ = ∑' _ : G ⧸ K, ∫⁻ x in D, u x ∂μ := by
  have : Countable (G ⧸ K) := QuotientGroup.mk_surjective.countable
  rw [hD'.setLIntegral_eq (isFundamentalDomain_iUnion_out_inv_smul hD K) u fun k x => hu k x,
    lintegral_iUnion₀ (fun q => hD.nullMeasurableSet_smul _)
      (pairwise_aedisjoint_out_inv_smul hD K)]
  exact tsum_congr fun q => (hD.smul _).setLIntegral_eq hD u hu

@[to_additive setLIntegral_addSubgroup_eq_index_mul
]
theorem setLIntegral_subgroup_eq_index_mul [K.FiniteIndex] (hD : IsFundamentalDomain G D μ)
    (hD' : IsFundamentalDomain K D' μ) {u : X → ℝ≥0∞}
    (hu : ∀ (g : G) (x : X), u (g • x) = u x) :
    ∫⁻ x in D', u x ∂μ = (K.index : ℝ≥0∞) * ∫⁻ x in D, u x ∂μ := by
  have := Fintype.ofFinite (G ⧸ K)
  rw [setLIntegral_subgroup_eq_tsum hD hD' hu, tsum_fintype, Finset.sum_const, nsmul_eq_mul,
    Subgroup.index, Nat.card_eq_fintype_card, Finset.card_univ]

@[to_additive measure_addSubgroup_eq_index_mul
]
theorem measure_subgroup_eq_index_mul [K.FiniteIndex] (hD : IsFundamentalDomain G D μ)
    (hD' : IsFundamentalDomain K D' μ) : μ D' = (K.index : ℝ≥0∞) * μ D := by
  simpa using setLIntegral_subgroup_eq_index_mul hD hD' (u := fun _ => 1) (fun _ _ => rfl)

@[to_additive
]
theorem setLAverage_subgroup_eq [K.FiniteIndex] (hD : IsFundamentalDomain G D μ)
    (hD' : IsFundamentalDomain K D' μ) {u : X → ℝ≥0∞}
    (hu : ∀ (g : G) (x : X), u (g • x) = u x) :
    ⨍⁻ x in D', u x ∂μ = ⨍⁻ x in D, u x ∂μ := by
  rw [setLAverage_eq, setLAverage_eq, setLIntegral_subgroup_eq_index_mul hD hD' hu,
    measure_subgroup_eq_index_mul hD hD', ENNReal.mul_div_mul_left]
  · exact_mod_cast Subgroup.FiniteIndex.index_ne_zero
  · exact ENNReal.natCast_ne_top _

@[to_additive
]
theorem measure_le_measure_subgroup (hD : IsFundamentalDomain G D μ)
    (hD' : IsFundamentalDomain K D' μ) : μ D ≤ μ D' :=
  measure_le_of_isFundamentalDomain_of_ae_covers hD
    (hD'.ae_covers.mono fun _ ⟨k, hk⟩ => ⟨k, hk⟩)

variable {E : Type*} [NormedAddCommGroup E]

@[to_additive
]
theorem integrableOn_subgroup_iff [K.FiniteIndex] (hD : IsFundamentalDomain G D μ)
    (hD' : IsFundamentalDomain K D' μ) {f : X → E}
    (hf : ∀ (g : G) (x : X), f (g • x) = f x) : IntegrableOn f D' μ ↔ IntegrableOn f D μ := by
  rw [hD'.integrableOn_iff (isFundamentalDomain_iUnion_out_inv_smul hD K) fun k x => hf k x,
    integrableOn_finite_iUnion]
  simp only [fun g : G => (hD.smul g).integrableOn_iff hD hf, forall_const]

variable [NormedSpace ℝ E]

@[to_additive setIntegral_addSubgroup_eq_index_smul
]
theorem setIntegral_subgroup_eq_index_smul [K.FiniteIndex] (hD : IsFundamentalDomain G D μ)
    (hD' : IsFundamentalDomain K D' μ) {f : X → E}
    (hf : ∀ (g : G) (x : X), f (g • x) = f x) :
    ∫ x in D', f x ∂μ = (K.index : ℝ) • ∫ x in D, f x ∂μ := by
  by_cases hi : IntegrableOn f D μ
  · have := Fintype.ofFinite (G ⧸ K)
    have hE := isFundamentalDomain_iUnion_out_inv_smul hD K
    rw [hD'.setIntegral_eq hE fun k x => hf k x,
      integral_iUnion_ae (fun q => hD.nullMeasurableSet_smul _)
        (pairwise_aedisjoint_out_inv_smul hD K) ((integrableOn_subgroup_iff hD hE hf).2 hi)]
    simp only [fun g : G => (hD.smul g).setIntegral_eq hD hf]
    rw [tsum_fintype, Finset.sum_const, Subgroup.index, Nat.card_eq_fintype_card,
      Finset.card_univ, Nat.cast_smul_eq_nsmul]
  · rw [integral_undef hi, integral_undef (mt (integrableOn_subgroup_iff hD hD' hf).1 hi),
      smul_zero]

@[to_additive
]
theorem setAverage_subgroup_eq [K.FiniteIndex] (hD : IsFundamentalDomain G D μ)
    (hD' : IsFundamentalDomain K D' μ) {f : X → E}
    (hf : ∀ (g : G) (x : X), f (g • x) = f x) :
    ⨍ x in D', f x ∂μ = ⨍ x in D, f x ∂μ := by
  have h0 : (K.index : ℝ) ≠ 0 := by exact_mod_cast Subgroup.FiniteIndex.index_ne_zero
  rw [setAverage_eq, setAverage_eq, setIntegral_subgroup_eq_index_smul hD hD' hf, smul_smul,
    measureReal_def, measureReal_def, measure_subgroup_eq_index_mul hD hD', ENNReal.toReal_mul,
    ENNReal.toReal_natCast, mul_inv, mul_right_comm, inv_mul_cancel₀ h0, one_mul]

end Subgroup

section Kernel

variable {G H X : Type*} [Group G] [Group H] [MulAction G X] [MulAction H X] [MeasurableSpace X]
  {μ : Measure X} {B D D' : Set X} {φ : G →* H}

@[to_additive  ]
theorem measurableConstSMul_of_surjective [MeasurableConstSMul G X]
    (hφ : Function.Surjective φ) (hφs : ∀ (g : G) (x : X), φ g • x = g • x) :
    MeasurableConstSMul H X where
  measurable_const_smul h := by
    obtain ⟨g, rfl⟩ := hφ h
    simpa only [hφs] using measurable_const_smul g

@[to_additive  ]
theorem smulInvariantMeasure_of_surjective [SMulInvariantMeasure G X μ]
    (hφ : Function.Surjective φ) (hφs : ∀ (g : G) (x : X), φ g • x = g • x) :
    SMulInvariantMeasure H X μ where
  measure_preimage_smul h s hs := by
    obtain ⟨g, rfl⟩ := hφ h
    simpa only [hφs] using SMulInvariantMeasure.measure_preimage_smul g hs

@[to_additive  ]
theorem ae_exists_smul_mem_of_surjective (hφ : Function.Surjective φ)
    (hφs : ∀ (g : G) (x : X), φ g • x = g • x) (hD : IsFundamentalDomain H D μ) :
    ∀ᵐ x ∂μ, ∃ g : G, g • x ∈ D := by
  filter_upwards [hD.ae_covers] with x ⟨h, hh⟩
  obtain ⟨g, rfl⟩ := hφ h
  exact ⟨g, hφs g x ▸ hh⟩

variable [MeasurableConstSMul G X] [SMulInvariantMeasure G X μ] [Countable G]

variable {K : Subgroup G} {H' : Type*} [Group H'] [MulAction H' X] {φ' : K →* H'}

@[to_additive isAddFundamentalDomain_map_of_surjective
]
theorem isFundamentalDomain_map_of_surjective (hφ : Function.Surjective φ)
    (hφs : ∀ (g : G) (x : X), φ g • x = g • x) (hD : IsFundamentalDomain H D μ)
    (hφ' : Function.Surjective φ') (hφs' : ∀ (k : K) (x : X), φ' k • x = k • x)
    (hD' : IsFundamentalDomain H' D' μ) : IsFundamentalDomain (K.map φ) D' μ where
  nullMeasurableSet := hD'.nullMeasurableSet
  ae_covers := by
    filter_upwards [ae_exists_smul_mem_of_surjective hφ' hφs' hD'] with x ⟨k, hk⟩
    refine ⟨⟨φ k, k, k.2, rfl⟩, ?_⟩
    rw [Subgroup.smul_def, hφs]
    exact hk
  aedisjoint := by
    have := measurableConstSMul_of_surjective hφ hφs
    have : SMulInvariantMeasure H X μ := smulInvariantMeasure_of_surjective hφ hφs
    have : Countable H := hφ.countable
    rintro ⟨_, k₁, hk₁, rfl⟩ ⟨_, k₂, hk₂, rfl⟩ hne
    have hne' : φ k₁ ≠ φ k₂ := fun h => hne (Subtype.ext h)
    have hset : ∀ (k : K) (S : Set X), φ k • S = φ' k • S := fun k S => by
      simp only [← image_smul, hφs, hφs', Subgroup.smul_def]
    by_cases hμ : μ = 0
    · simp [hμ, Function.onFun, AEDisjoint]
    have hne'' : φ' ⟨k₁, hk₁⟩ ≠ φ' ⟨k₂, hk₂⟩ := by
      intro h
      have h1 := hD.aedisjoint hne'
      have h2 : φ k₁ • D = φ k₂ • D := by
        rw [hset ⟨k₁, hk₁⟩, hset ⟨k₂, hk₂⟩, h]
      simp only [Function.onFun, AEDisjoint, h2, inter_self, measure_smul] at h1
      exact hD.measure_ne_zero hμ h1
    have h3 := hD'.aedisjoint hne''
    simp only [Function.onFun, ← hset] at h3
    exact h3

omit [MeasurableSpace X] [MulAction G X] [MulAction H X] [MeasurableConstSMul G X]
  [SMulInvariantMeasure G X μ] [Countable G] in

@[to_additive finiteIndex_addSubgroup_map_of_surjective
]
theorem finiteIndex_map_of_surjective [K.FiniteIndex] (hφ : Function.Surjective φ) :
    (K.map φ).FiniteIndex :=
  ⟨ne_zero_of_dvd_ne_zero Subgroup.FiniteIndex.index_ne_zero (K.index_map_dvd hφ)⟩

@[to_additive setLIntegral_eq_index_map_mul_vadd
]
theorem setLIntegral_eq_index_map_mul [K.FiniteIndex] (hφ : Function.Surjective φ)
    (hφs : ∀ (g : G) (x : X), φ g • x = g • x) (hD : IsFundamentalDomain H D μ)
    (hφ' : Function.Surjective φ') (hφs' : ∀ (k : K) (x : X), φ' k • x = k • x)
    (hD' : IsFundamentalDomain H' D' μ) {u : X → ℝ≥0∞}
    (hu : ∀ (g : G) (x : X), u (g • x) = u x) :
    ∫⁻ x in D', u x ∂μ = ((K.map φ).index : ℝ≥0∞) * ∫⁻ x in D, u x ∂μ := by
  have := measurableConstSMul_of_surjective hφ hφs
  have : SMulInvariantMeasure H X μ := smulInvariantMeasure_of_surjective hφ hφs
  have : Countable H := hφ.countable
  have := finiteIndex_map_of_surjective (K := K) hφ
  refine setLIntegral_subgroup_eq_index_mul hD
    (isFundamentalDomain_map_of_surjective hφ hφs hD hφ' hφs' hD') fun h x => ?_
  obtain ⟨g, rfl⟩ := hφ h
  rw [hφs, hu]

@[to_additive measure_eq_index_map_mul_vadd
]
theorem measure_eq_index_map_mul [K.FiniteIndex] (hφ : Function.Surjective φ)
    (hφs : ∀ (g : G) (x : X), φ g • x = g • x) (hD : IsFundamentalDomain H D μ)
    (hφ' : Function.Surjective φ') (hφs' : ∀ (k : K) (x : X), φ' k • x = k • x)
    (hD' : IsFundamentalDomain H' D' μ) : μ D' = ((K.map φ).index : ℝ≥0∞) * μ D := by
  simpa using setLIntegral_eq_index_map_mul hφ hφs hD hφ' hφs' hD' (u := fun _ => 1)
    (fun _ _ => rfl)

@[to_additive measure_le_measure_of_surjective_vadd
]
theorem measure_le_measure_of_surjective (hφ : Function.Surjective φ)
    (hφs : ∀ (g : G) (x : X), φ g • x = g • x) (hD : IsFundamentalDomain H D μ)
    (hφ' : Function.Surjective φ') (hφs' : ∀ (k : K) (x : X), φ' k • x = k • x)
    (hD' : IsFundamentalDomain H' D' μ) : μ D ≤ μ D' := by
  have := measurableConstSMul_of_surjective hφ hφs
  have : SMulInvariantMeasure H X μ := smulInvariantMeasure_of_surjective hφ hφs
  have : Countable H := hφ.countable
  exact measure_le_measure_subgroup hD
    (isFundamentalDomain_map_of_surjective hφ hφs hD hφ' hφs' hD')

end Kernel

end GlobalTheory
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsFundamentalDomainAndQuotMeasureEq
attribute [-instance] _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.LocalLattice.instIsScalarTowerLocalRing _root_.GlobalTheory.Mem.Chr.negTwoFact _root_.GlobalTheory.SmGL.instDecidableEqTwo _root_.GlobalTheory.SplitWeil.matrixMeasurableSpace
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

open MeasureTheory Set Topology Filter
open scoped Pointwise ENNReal

namespace GlobalTheory

structure IsAEAddOrbitSection (G : Type*) {X : Type*} [VAdd G X] [MeasurableSpace X]
    (D : Set X) (μ : Measure X) : Prop where
  protected nullMeasurableSet : NullMeasurableSet D μ
  protected ae_covers : ∀ᵐ x ∂μ, ∃ g : G, g +ᵥ x ∈ D
  protected ae_unique : ∀ᵐ x ∂μ, x ∈ D → ∀ g : G, g +ᵥ x ∈ D → g +ᵥ x = x

@[to_additive IsAEAddOrbitSection]
structure IsAEOrbitSection (G : Type*) {X : Type*} [SMul G X] [MeasurableSpace X]
    (D : Set X) (μ : Measure X) : Prop where
  protected nullMeasurableSet : NullMeasurableSet D μ
  protected ae_covers : ∀ᵐ x ∂μ, ∃ g : G, g • x ∈ D
  protected ae_unique : ∀ᵐ x ∂μ, x ∈ D → ∀ g : G, g • x ∈ D → g • x = x

section Existence

variable {G X : Type*} [Group G] [MulAction G X]

@[to_additive exists_measurableSet_addOrbitSection_of_discreteOrbits
]
theorem exists_measurableSet_orbitSection_of_discreteOrbits [Countable G] [TopologicalSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [MeasurableConstSMul G X] (hfix : ∀ g : G, MeasurableSet {x : X | g • x = x})
    (hdisc : ∀ x : X, ∃ U ∈ 𝓝 x, ∀ g : G, g • x ∈ U → g • x = x) :
    ∃ D : Set X, MeasurableSet D ∧ (∀ x, ∃ g : G, g • x ∈ D) ∧
      ∀ x ∈ D, ∀ g : G, g • x ∈ D → g • x = x := by
  classical
  obtain ⟨b, hbc, -, hb⟩ := TopologicalSpace.exists_countable_basis X
  obtain ⟨B, hB⟩ := (hbc.insert ∅).exists_eq_range (insert_nonempty _ _)
  have hBo : ∀ n, IsOpen (B n) := fun n => by
    have : B n ∈ insert ∅ b := hB ▸ mem_range_self n
    rcases this with h | h
    · rw [h]; exact isOpen_empty
    · exact hb.isOpen h
  let S : ℕ → Set X := fun n => B n ∩ ⋂ g : G, (((g • ·) ⁻¹' B n)ᶜ ∪ {x | g • x = x})
  have hSm : ∀ n, MeasurableSet (S n) := fun n =>
    (hBo n).measurableSet.inter <| MeasurableSet.iInter fun g =>
      ((measurable_const_smul g) (hBo n).measurableSet).compl.union (hfix g)
  have hSmem : ∀ n x, x ∈ S n ↔ x ∈ B n ∧ ∀ g : G, g • x ∈ B n → g • x = x := fun n x => by
    simp only [S, mem_inter_iff, mem_iInter, mem_union, mem_compl_iff, mem_preimage,
      mem_setOf_eq, imp_iff_not_or]
  have hS : ∀ x, ∃ n, x ∈ S n := fun x => by
    obtain ⟨U, hU, h⟩ := hdisc x
    obtain ⟨t, ht, hxt, htU⟩ := hb.mem_nhds_iff.1 hU
    have : t ∈ range B := hB ▸ mem_insert_of_mem _ ht
    obtain ⟨n, rfl⟩ := this
    exact ⟨n, (hSmem n x).2 ⟨hxt, fun g hg => h g (htU hg)⟩⟩
  let T : ℕ → Set X := fun n => ⋃ g : G, (g • ·) ⁻¹' S n
  have hTm : ∀ n, MeasurableSet (T n) := fun n =>
    MeasurableSet.iUnion fun g => (measurable_const_smul g) (hSm n)
  have hTmem : ∀ n x, x ∈ T n ↔ ∃ g : G, g • x ∈ S n := fun n x => by simp [T]
  refine ⟨⋃ n, S n \ ⋃ m, ⋃ (_ : m < n), T m, ?_, ?_, ?_⟩
  · exact MeasurableSet.iUnion fun n => (hSm n).diff <|
      MeasurableSet.iUnion fun m => MeasurableSet.iUnion fun _ => hTm m
  · intro x
    have hx : ∃ n, x ∈ T n := by
      obtain ⟨n, hn⟩ := hS x
      exact ⟨n, (hTmem n x).2 ⟨1, by simpa using hn⟩⟩
    obtain ⟨g, hg⟩ := (hTmem _ x).1 (Nat.find_spec hx)
    refine ⟨g, mem_iUnion.2 ⟨Nat.find hx, hg, fun h => ?_⟩⟩
    obtain ⟨m, hm, h⟩ := mem_iUnion₂.1 h
    obtain ⟨k, hk⟩ := (hTmem _ _).1 h
    exact Nat.find_min hx hm ((hTmem _ _).2 ⟨k * g, by rwa [mul_smul]⟩)
  · intro x hx g hg
    obtain ⟨n, hn, hn'⟩ := mem_iUnion.1 hx
    obtain ⟨m, hm, hm'⟩ := mem_iUnion.1 hg
    rcases lt_trichotomy m n with h | rfl | h
    · exact (hn' (mem_iUnion₂.2 ⟨m, h, (hTmem _ _).2 ⟨g, hm⟩⟩)).elim
    · exact ((hSmem _ _).1 hn).2 g ((hSmem _ _).1 hm).1
    · exact (hm' (mem_iUnion₂.2 ⟨n, h, (hTmem _ _).2 ⟨g⁻¹, by rwa [inv_smul_smul]⟩⟩)).elim

end Existence

section Comparison

variable {G X : Type*} [Group G] [MulAction G X] [MeasurableSpace X] {μ : Measure X}

@[to_additive measure_le_of_ae_unique_of_ae_covers_add
]
theorem measure_le_of_ae_unique_of_ae_covers [Countable G] [MeasurableConstSMul G X]
    [SMulInvariantMeasure G X μ] {S B : Set X} (hS : NullMeasurableSet S μ)
    (hB : NullMeasurableSet B μ) (hu : ∀ᵐ x ∂μ, x ∈ S → ∀ g : G, g • x ∈ S → g • x = x)
    (hc : ∀ᵐ x ∂μ, x ∈ S → ∃ g : G, g • x ∈ B) : μ S ≤ μ B := by
  classical
  obtain ⟨e, he⟩ := exists_injective_nat G
  have hq : ∀ g : G, Measure.QuasiMeasurePreserving (g • · : X → X) μ μ := fun g =>
    (measurePreserving_smul g μ).quasiMeasurePreserving
  let P : G → Set X := fun g => (S ∩ (g • ·) ⁻¹' B) \ ⋃ h, ⋃ (_ : e h < e g), (h • ·) ⁻¹' B
  have hPm : ∀ g, NullMeasurableSet (P g) μ := fun g =>
    (hS.inter (hB.preimage (hq g))).diff <|
      NullMeasurableSet.iUnion fun h => NullMeasurableSet.iUnion fun _ => hB.preimage (hq h)
  let Q : G → Set X := fun g => (g⁻¹ • ·) ⁻¹' P g
  have hQm : ∀ g, NullMeasurableSet (Q g) μ := fun g => (hPm g).preimage (hq _)
  have h1 : S ≤ᵐ[μ] ⋃ g, P g := by
    filter_upwards [hc] with x hx hxS
    have hex : ∃ n, ∃ g : G, e g = n ∧ g • x ∈ B := by
      obtain ⟨g, hg⟩ := hx hxS
      exact ⟨_, g, rfl, hg⟩
    obtain ⟨g, hg, hgB⟩ := Nat.find_spec hex
    refine mem_iUnion.2 ⟨g, ⟨hxS, hgB⟩, fun h => ?_⟩
    obtain ⟨k, hk, h⟩ := mem_iUnion₂.1 h
    exact Nat.find_min hex (hg ▸ hk) ⟨k, rfl, h⟩
  have h2 : Pairwise (Function.onFun (AEDisjoint μ) Q) := by
    intro g h hgh
    have := (hq g⁻¹).ae hu
    refine measure_mono_null (fun y hy => ?_) this
    intro hy'
    obtain ⟨⟨⟨hg1, hg2⟩, hg3⟩, ⟨hh1, hh2⟩, hh3⟩ := hy
    have key : h⁻¹ • y = g⁻¹ • y := by
      have := hy' hg1 (h⁻¹ * g) (by simpa [mul_smul] using hh1)
      simpa [mul_smul] using this
    rcases lt_trichotomy (e g) (e h) with hl | hl | hl
    · exact hh3 (mem_iUnion₂.2 ⟨g, hl, by rw [mem_preimage]; beta_reduce; rw [key]; exact hg2⟩)
    · exact hgh (he hl)
    · exact hg3 (mem_iUnion₂.2 ⟨h, hl, by rw [mem_preimage]; beta_reduce; rw [← key]; exact hh2⟩)
  calc μ S ≤ μ (⋃ g, P g) := measure_mono_ae h1
    _ ≤ ∑' g, μ (P g) := measure_iUnion_le _
    _ = ∑' g, μ (Q g) := tsum_congr fun g => (measure_preimage_smul μ g⁻¹ (P g)).symm
    _ = μ (⋃ g, Q g) := (measure_iUnion₀ h2 hQm).symm
    _ ≤ μ B := measure_mono <| iUnion_subset fun g y hy => by simpa using hy.1.2

end Comparison

section Quot

variable {G X : Type*} [Group G] [MulAction G X] [MeasurableSpace X] {μ : Measure X}

@[to_additive addQuotMeasure  ]
noncomputable def quotMeasure (G : Type*) {X : Type*} [Group G] [MulAction G X] [MeasurableSpace X]
    (μ : Measure X) : Measure (Quotient (MulAction.orbitRel G X)) :=
  ⨆ (D : Set X) (_ : NullMeasurableSet D μ)
    (_ : ∀ᵐ x ∂μ, x ∈ D → ∀ g : G, g • x ∈ D → g • x = x),
    (μ.restrict D).map (Quotient.mk (MulAction.orbitRel G X))

@[to_additive map_restrict_le_addQuotMeasure]
theorem map_restrict_le_quotMeasure {D : Set X} (hD : NullMeasurableSet D μ)
    (hu : ∀ᵐ x ∂μ, x ∈ D → ∀ g : G, g • x ∈ D → g • x = x) :
    (μ.restrict D).map (Quotient.mk (MulAction.orbitRel G X)) ≤ quotMeasure G μ :=
  le_iSup_of_le D (le_iSup_of_le hD (le_iSup_of_le hu le_rfl))

@[to_additive isAddFundamentalDomain_of_addOrbitSection
]
theorem isFundamentalDomain_of_orbitSection {D : Set X} (hD : NullMeasurableSet D μ)
    (hc : ∀ᵐ x ∂μ, ∃ g : G, g • x ∈ D) (hu : ∀ x ∈ D, ∀ g : G, g • x ∈ D → g • x = x)
    (hfree : ∀ g : G, g ≠ 1 → μ {x | g • x = x} = 0) : IsFundamentalDomain G D μ where
  nullMeasurableSet := hD
  ae_covers := hc
  aedisjoint g h hgh := by
    refine measure_mono_null (fun y hy => ?_) (hfree (g * h⁻¹) fun e => hgh (mul_inv_eq_one.1 e))
    obtain ⟨hg, hh⟩ := hy
    rw [mem_smul_set_iff_inv_smul_mem] at hg hh
    have := hu _ hg (h⁻¹ * g) (by simpa [mul_smul] using hh)
    rw [mul_smul, smul_inv_smul] at this
    rw [mem_setOf_eq, mul_smul, this, smul_inv_smul]

variable [Countable G] [MeasurableConstSMul G X] [SMulInvariantMeasure G X μ]

@[to_additive measure_fixed_eq_zero_of_isAddFundamentalDomain
]
theorem measure_fixed_eq_zero_of_isFundamentalDomain {D : Set X} (hD : IsFundamentalDomain G D μ)
    {g : G} (hg : g ≠ 1) : μ {x | g • x = x} = 0 := by
  have h1 : ∀ᵐ x ∂μ, ∀ k : G, k • x ∈ D → ¬ g • x = x := by
    refine ae_all_iff.2 fun k => ?_
    have hne : k⁻¹ ≠ (k * g)⁻¹ := fun e => hg (by simpa using inv_injective e)
    refine measure_mono_null (fun x hx => ?_) (hD.aedisjoint hne)
    simp only [mem_compl_iff, mem_setOf_eq, Classical.not_imp, not_not] at hx
    refine ⟨?_, ?_⟩
    · rw [mem_smul_set_iff_inv_smul_mem, inv_inv]; exact hx.1
    · rw [mem_smul_set_iff_inv_smul_mem, inv_inv, mul_smul, hx.2]; exact hx.1
  refine measure_mono_null (fun x hx => ?_) (h1.and hD.ae_covers)
  rintro ⟨h2, k, hk⟩
  exact h2 k hk hx

@[to_additive map_restrict_le_map_restrict_of_ae_unique_of_ae_covers_add]
theorem map_restrict_le_map_restrict_of_ae_unique_of_ae_covers {S B : Set X}
    (hS : NullMeasurableSet S μ) (hB : NullMeasurableSet B μ)
    (hu : ∀ᵐ x ∂μ, x ∈ S → ∀ g : G, g • x ∈ S → g • x = x) (hc : ∀ᵐ x ∂μ, ∃ g : G, g • x ∈ B) :
    (μ.restrict S).map (Quotient.mk (MulAction.orbitRel G X)) ≤
      (μ.restrict B).map (Quotient.mk (MulAction.orbitRel G X)) := by
  refine Measure.le_iff.2 fun U hU => ?_
  rw [measure_map_restrict_apply μ S hU, measure_map_restrict_apply μ B hU]
  have hU' : NullMeasurableSet (Quotient.mk (MulAction.orbitRel G X) ⁻¹' U) μ :=
    (measurableSet_quotient.1 hU).nullMeasurableSet
  refine measure_le_of_ae_unique_of_ae_covers (G := G) (hU'.inter hS) (hU'.inter hB) ?_ ?_
  · filter_upwards [hu] with x hx hxS g hg using hx hxS.2 g hg.2
  · filter_upwards [hc] with x ⟨g, hg⟩ hxS
    refine ⟨g, ?_, hg⟩
    have : Quotient.mk (MulAction.orbitRel G X) (g • x) = Quotient.mk (MulAction.orbitRel G X) x :=
      Quotient.sound ⟨g, rfl⟩
    rw [mem_preimage, this]
    exact hxS.1

@[to_additive addQuotMeasure_le_map_restrict
]
theorem quotMeasure_le_map_restrict {B : Set X} (hB : NullMeasurableSet B μ)
    (hc : ∀ᵐ x ∂μ, ∃ g : G, g • x ∈ B) :
    quotMeasure G μ ≤ (μ.restrict B).map (Quotient.mk (MulAction.orbitRel G X)) :=
  iSup_le fun _ => iSup_le fun hS => iSup_le fun hu =>
    map_restrict_le_map_restrict_of_ae_unique_of_ae_covers hS hB hu hc

@[to_additive addQuotMeasure_univ_le
]
theorem quotMeasure_univ_le {B : Set X} (hB : NullMeasurableSet B μ)
    (hc : ∀ᵐ x ∂μ, ∃ g : G, g • x ∈ B) : quotMeasure G μ univ ≤ μ B := by
  refine (quotMeasure_le_map_restrict hB hc univ).trans_eq ?_
  rw [measure_map_restrict_apply μ B MeasurableSet.univ, preimage_univ, univ_inter]

end Quot

section ProperlyDiscontinuous

variable (G X : Type*) [Group G] [Countable G] [MulAction G X] [TopologicalSpace X] [T2Space X]
  [SecondCountableTopology X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [ContinuousConstSMul G X]

@[to_additive exists_measurableSet_addOrbitSection
]
theorem exists_measurableSet_orbitSection [ProperlyDiscontinuousSMul G X] :
    ∃ D : Set X, MeasurableSet D ∧ (∀ x, ∃ g : G, g • x ∈ D) ∧
      ∀ x ∈ D, ∀ g : G, g • x ∈ D → g • x = x := by
  refine exists_measurableSet_orbitSection_of_discreteOrbits
    (fun g => (isClosed_eq (continuous_const_smul g) continuous_id).measurableSet) fun x => ?_
  obtain ⟨U, hU, h⟩ := ProperlyDiscontinuousSMul.exists_nhds_image_smul_eq_self G x
  exact ⟨U, hU, fun g hg => h g ⟨g • x, ⟨x, mem_of_mem_nhds hU, rfl⟩, hg⟩⟩

@[to_additive exists_isAddFundamentalDomain_of_free
]
theorem exists_isFundamentalDomain_of_free [ProperlyDiscontinuousSMul G X]
    (hfree : ∀ (g : G) (x : X), g • x = x → g = 1) :
    ∃ D : Set X, MeasurableSet D ∧ (∀ x, ∃! g : G, g • x ∈ D) ∧
      ∀ μ : Measure X, IsFundamentalDomain G D μ := by
  obtain ⟨D, hD, hc, hu⟩ := exists_measurableSet_orbitSection G X
  have h : ∀ x, ∃! g : G, g • x ∈ D := fun x => by
    obtain ⟨g, hg⟩ := hc x
    refine ⟨g, hg, fun k hk => ?_⟩
    have := hu _ hg (k * g⁻¹) (by simpa [mul_smul] using hk)
    exact mul_inv_eq_one.1 (hfree _ _ this)
  exact ⟨D, hD, h, fun μ => IsFundamentalDomain.mk' hD.nullMeasurableSet h⟩

variable {X}

@[to_additive exists_isAddFundamentalDomain_of_ae_free
]
theorem exists_isFundamentalDomain_of_ae_free [ProperlyDiscontinuousSMul G X] (μ : Measure X)
    (hfree : μ {x | MulAction.stabilizer G x ≠ ⊥} = 0) :
    ∃ D : Set X, MeasurableSet D ∧ (∀ x, ∃ g : G, g • x ∈ D) ∧
      (∀ x ∈ D, ∀ g : G, g • x ∈ D → g • x = x) ∧ IsFundamentalDomain G D μ := by
  obtain ⟨D, hD, hc, hu⟩ := exists_measurableSet_orbitSection G X
  refine ⟨D, hD, hc, hu, isFundamentalDomain_of_orbitSection hD.nullMeasurableSet
    (Eventually.of_forall hc) hu fun g hg => measure_mono_null (fun x hx => ?_) hfree⟩
  refine fun h : MulAction.stabilizer G x = ⊥ => hg ?_
  have : g ∈ MulAction.stabilizer G x := hx
  simpa [h] using this

@[to_additive exists_isAddFundamentalDomain_of_surjective
]
theorem exists_isFundamentalDomain_of_surjective [ProperlyDiscontinuousSMul G X] {Q : Type*}
    [Group Q] [MulAction Q X] (φ : G →* Q) (hφ : Function.Surjective φ)
    (hact : ∀ g (x : X), φ g • x = g • x) (μ : Measure X)
    (hfree : ∀ g : G, φ g ≠ 1 → μ {x | g • x = x} = 0) :
    ∃ D : Set X, MeasurableSet D ∧ (∀ x, ∃ g : G, g • x ∈ D) ∧
      (∀ x ∈ D, ∀ g : G, g • x ∈ D → g • x = x) ∧ IsFundamentalDomain Q D μ := by
  obtain ⟨D, hD, hc, hu⟩ := exists_measurableSet_orbitSection G X
  refine ⟨D, hD, hc, hu, isFundamentalDomain_of_orbitSection hD.nullMeasurableSet
    (Eventually.of_forall fun x => ?_) (fun x hx q hq => ?_) fun q hq => ?_⟩
  · obtain ⟨g, hg⟩ := hc x
    exact ⟨φ g, by rwa [hact]⟩
  · obtain ⟨g, rfl⟩ := hφ q
    rw [hact] at hq ⊢
    exact hu x hx g hq
  · obtain ⟨g, rfl⟩ := hφ q
    simpa only [hact] using hfree g hq

end ProperlyDiscontinuous

section DiscreteSubgroup

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [SecondCountableTopology G] (Γ : Subgroup G) [DiscreteTopology Γ]

@[to_additive countable_of_discrete_addSubgroup
]
theorem countable_of_discrete_subgroup : Countable Γ :=
  TopologicalSpace.separableSpace_iff_countable.1 inferInstance

omit [IsTopologicalGroup G] [SecondCountableTopology G] in
@[to_additive exists_nhds_zero_inter_addSubgroup]
theorem exists_nhds_one_inter_subgroup : ∃ V ∈ 𝓝 (1 : G), ∀ g ∈ Γ, g ∈ V → g = 1 := by
  have h : ({1} : Set Γ) ∈ 𝓝 (1 : Γ) := (isOpen_discrete _).mem_nhds rfl
  rw [nhds_induced, mem_comap] at h
  obtain ⟨V, hV, h⟩ := h
  exact ⟨V, hV, fun g hg hgV => congrArg Subtype.val (h (a := ⟨g, hg⟩) hgV)⟩

variable [MeasurableSpace G] [BorelSpace G]

@[to_additive exists_isAddFundamentalDomain_addSubgroup
]
theorem exists_isFundamentalDomain_subgroup :
    ∃ D : Set G, MeasurableSet D ∧ (∀ x, ∃! g : Γ, g • x ∈ D) ∧
      ∀ μ : Measure G, IsFundamentalDomain Γ D μ := by
  have := countable_of_discrete_subgroup Γ
  have hfree : ∀ (g : Γ) (x : G), g • x = x → g = 1 := fun g x h =>
    Subtype.ext (mul_eq_right.1 h)
  obtain ⟨V, hV, hV1⟩ := exists_nhds_one_inter_subgroup Γ
  obtain ⟨D, hD, hc, hu⟩ := exists_measurableSet_orbitSection_of_discreteOrbits (G := Γ) (X := G)
    (fun g => by
      by_cases hg : g = 1
      · simp [hg]
      · have : {x : G | g • x = x} = ∅ := eq_empty_of_forall_notMem fun x hx => hg (hfree g x hx)
        simp [this])
    (fun x => by
      refine ⟨(· * x⁻¹) ⁻¹' V, (continuous_mul_const _).continuousAt.preimage_mem_nhds
        (by simpa using hV), fun g hg => ?_⟩
      have h1 : (g : G) ∈ V := by
        have : (g : G) * x * x⁻¹ ∈ V := hg
        simpa using this
      have : g = 1 := Subtype.ext (hV1 g g.2 h1)
      rw [this, one_smul])
  have h : ∀ x, ∃! g : Γ, g • x ∈ D := fun x => by
    obtain ⟨g, hg⟩ := hc x
    refine ⟨g, hg, fun k hk => ?_⟩
    have := hu _ hg (k * g⁻¹) (by rwa [mul_smul, inv_smul_smul])
    exact mul_inv_eq_one.1 (hfree _ _ this)
  exact ⟨D, hD, h, fun μ => IsFundamentalDomain.mk' hD.nullMeasurableSet h⟩

@[to_additive exists_isAddFundamentalDomain_addSubgroup_op
]
theorem exists_isFundamentalDomain_subgroup_op :
    ∃ D : Set G, MeasurableSet D ∧ (∀ x, ∃! g : Γ.op, g • x ∈ D) ∧
      ∀ μ : Measure G, IsFundamentalDomain Γ.op D μ := by
  obtain ⟨D, hD, h, -⟩ := exists_isFundamentalDomain_subgroup Γ
  have h' : ∀ x, ∃! g : Γ.op, g • x ∈ D⁻¹ := fun x => by
    obtain ⟨g, hg, hu⟩ := h x⁻¹
    refine ⟨⟨MulOpposite.op (g : G)⁻¹, inv_mem g.2⟩, ?_, fun k hk => ?_⟩
    · have : (g : G) * x⁻¹ ∈ D := hg
      change (x * (g : G)⁻¹)⁻¹ ∈ D
      rwa [mul_inv_rev, inv_inv]
    · have hk' : (x * MulOpposite.unop (k : Gᵐᵒᵖ))⁻¹ ∈ D := hk
      rw [mul_inv_rev] at hk'
      have := hu ⟨(MulOpposite.unop (k : Gᵐᵒᵖ))⁻¹, inv_mem k.2⟩ hk'
      subst this
      ext
      simp
  exact ⟨D⁻¹, hD.inv, h', fun μ => IsFundamentalDomain.mk' hD.inv.nullMeasurableSet h'⟩

@[to_additive hasAddFundamentalDomain_addSubgroup]
theorem hasFundamentalDomain_subgroup (μ : Measure G) : HasFundamentalDomain Γ G μ := by
  obtain ⟨D, -, -, h⟩ := exists_isFundamentalDomain_subgroup Γ
  exact ⟨D, h μ⟩

@[to_additive hasAddFundamentalDomain_addSubgroup_op]
theorem hasFundamentalDomain_subgroup_op (μ : Measure G) : HasFundamentalDomain Γ.op G μ := by
  obtain ⟨D, -, -, h⟩ := exists_isFundamentalDomain_subgroup_op Γ
  exact ⟨D, h μ⟩

end DiscreteSubgroup

end GlobalTheory
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsAbsoluteValueOfIsDiscreteValuationRing
attribute [-instance] _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.LocalLattice.instIsScalarTowerLocalRing _root_.GlobalTheory.Mem.Chr.negTwoFact _root_.GlobalTheory.SplitWeil.matrixMeasurableSpace
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

open Polynomial

namespace GlobalTheory

universe u

@[reducible] noncomputable def completionNontriviallyNormedField (K : Type*)
    [NontriviallyNormedField K] : NontriviallyNormedField (UniformSpace.Completion K) where
  __ : NormedField (UniformSpace.Completion K) := inferInstance
  non_trivial := by
    obtain ⟨x, hx⟩ := NontriviallyNormedField.non_trivial (α := K)
    exact ⟨x, by simpa using hx⟩

end GlobalTheory
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrincipalCongruenceFixedVectorsLeSmoothVectors
attribute [-instance] _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.LocalLattice.instIsScalarTowerLocalRing _root_.GlobalTheory.Mem.Chr.negTwoFact _root_.GlobalTheory.SmGL.instDecidableEqTwo _root_.GlobalTheory.SmGL.instFintypeTwo _root_.GlobalTheory.SplitWeil.matrixMeasurableSpace
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

namespace GlobalTheory.SerSys.TameGen

open Polynomial GlobalTheory.GLq GlobalTheory.GLp CategoryTheory
open scoped Classical

variable {g : ℕ} [Fact g.Prime]

def Inflates {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) ℚ_[g]) V)
    (τ : FDRep ℂ (Gn g n)) : Prop :=
  ∃ φ : τ →ₗ[ℂ] V, φ ≠ 0 ∧ ∀ (k : GL (Fin n) ℤ_[g]) (w : τ), φ (τ.ρ (red g n k) w) = π (inc g n k) (φ w)

end GlobalTheory.SerSys.TameGen
end
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayLSeriesEulerProduct
attribute [-instance] _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.LocalLattice.instIsScalarTowerLocalRing _root_.GlobalTheory.Mem.Chr.negTwoFact _root_.GlobalTheory.SplitWeil.matrixMeasurableSpace
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

open NumberField IsDedekindDomain GlobalTheory.Mem Complex Filter Topology
open scoped ComplexOrder

namespace GlobalTheory.Mem

instance finite_absNorm_fiber (K : Type) [Field K] [NumberField K] (n : ℕ) :
    Finite {I : Ideal (𝓞 K) // Ideal.absNorm I = n} :=
  (Ideal.finite_setOfPred_absNorm_eq n).to_subtype

end GlobalTheory.Mem
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.Proofs.UnitaryExistence.InfAdeleTensorBijective
attribute [-instance] _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.LocalLattice.instIsScalarTowerLocalRing _root_.GlobalTheory.Mem.Chr.negTwoFact _root_.GlobalTheory.Mem.finite_absNorm_fiber _root_.GlobalTheory.SmGL.instFintypeTwo _root_.GlobalTheory.SplitWeil.matrixMeasurableSpace
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct Topology Matrix

namespace GlobalTheory.InfAdeleCM

variable {F : Type} [Field F] [NumberField F]

def ext (σ : F →+* ℂ) : InfiniteAdeleRing F →+* ℂ :=
  (InfinitePlace.Completion.extensionEmbedding (InfinitePlace.mk σ)).comp
    (Pi.evalRingHom (fun v : InfinitePlace F => v.Completion) (InfinitePlace.mk σ))

theorem ext_apply (σ : F →+* ℂ) (a : InfiniteAdeleRing F) :
    ext σ a = InfinitePlace.Completion.extensionEmbedding (InfinitePlace.mk σ) (a (InfinitePlace.mk σ)) := rfl

theorem continuous_ext (σ : F →+* ℂ) : Continuous (ext σ) :=
  (InfinitePlace.Completion.isometry_extensionEmbedding (InfinitePlace.mk σ)).continuous.comp
    (continuous_apply (InfinitePlace.mk σ))

theorem ext_algebraMap [IsTotallyReal F] (σ : F →+* ℂ) (x : F) :
    ext σ (algebraMap F (InfiniteAdeleRing F) x) = σ x := by
  have h : (InfinitePlace.mk σ).embedding = σ :=
    InfinitePlace.embedding_mk_eq_of_isReal (IsTotallyReal.complexEmbedding_isReal σ)
  rw [ext_apply, InfiniteAdeleRing.algebraMap_apply]
  simp [h]

theorem ext_eq_ofReal [IsTotallyReal F] (σ : F →+* ℂ) (a : InfiniteAdeleRing F) :
    ext σ a = (InfinitePlace.Completion.extensionEmbeddingOfIsReal
      (IsTotallyReal.isReal (InfinitePlace.mk σ)) (a (InfinitePlace.mk σ)) : ℝ) := by
  rw [ext_apply, InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply]

theorem conj_ext [IsTotallyReal F] (σ : F →+* ℂ) (a : InfiniteAdeleRing F) :
    starRingEnd ℂ (ext σ a) = ext σ a := by
  rw [ext_eq_ofReal, Complex.conj_ofReal]

variable {E : Type} [Field E] [NumberField E] [Algebra F E]

theorem exists_hom [IsTotallyReal F] (τ : E →+* ℂ) :
    ∃ θ : InfiniteAdeleRing F ⊗[F] E →+* ℂ, (∀ x, θ (1 ⊗ₜ x) = τ x) ∧
      Continuous fun a : InfiniteAdeleRing F => θ (a ⊗ₜ (1 : E)) := by
  letI : Algebra F ℂ := (τ.comp (algebraMap F E)).toAlgebra
  let f : InfiniteAdeleRing F →ₐ[F] ℂ :=
    { ext (τ.comp (algebraMap F E)) with commutes' := fun x => ext_algebraMap _ x }
  let g : E →ₐ[F] ℂ := { τ with commutes' := fun x => rfl }
  refine ⟨(Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)).toRingHom, ?_, ?_⟩
  · intro x
    simp [g]
  · have : (fun a : InfiniteAdeleRing F =>
        (Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)).toRingHom (a ⊗ₜ (1 : E))) =
        ext (τ.comp (algebraMap F E)) := by
      funext a
      simp [f]
    rw [this]
    exact continuous_ext _

theorem hom_tmul [IsTotallyReal F] (τ : E →+* ℂ) (θ : InfiniteAdeleRing F ⊗[F] E →+* ℂ)
    (h1 : ∀ x, θ (1 ⊗ₜ x) = τ x) (h2 : Continuous fun a : InfiniteAdeleRing F => θ (a ⊗ₜ (1 : E)))
    (a : InfiniteAdeleRing F) (x : E) :
    θ (a ⊗ₜ x) = ext (τ.comp (algebraMap F E)) a * τ x := by
  have : (fun a : InfiniteAdeleRing F => θ (a ⊗ₜ (1 : E))) = ext (τ.comp (algebraMap F E)) := by
    refine (InfiniteAdeleRing.denseRange_algebraMap F).equalizer h2 (continuous_ext _) ?_
    funext y
    simp only [Function.comp_apply, ext_algebraMap, RingHom.comp_apply]
    rw [← h1, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  rw [← this, ← h1, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem exists_delta (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1)
    (hτ : ∀ (τ : E →+* ℂ) x, τ (c x) = starRingEnd ℂ (τ x)) :
    ∃ δ : E, δ ≠ 0 ∧ c δ = -δ ∧ ∀ x : E, ∃ p q : F, x = algebraMap F E p + algebraMap F E q * δ := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  obtain ⟨y, hy⟩ : ∃ y, c y ≠ y := by
    by_contra h
    push_neg at h
    exact hc (AlgEquiv.ext h)
  have hcc : c (c y) = y := τ.injective (by rw [hτ, hτ, Complex.conj_conj])
  have hδ : y - c y ≠ 0 := sub_ne_zero.2 hy.symm
  have hcδ : c (y - c y) = -(y - c y) := by rw [map_sub, hcc]; ring
  refine ⟨y - c y, hδ, hcδ, ?_⟩
  generalize y - c y = δ at hδ hcδ
  have hli : LinearIndependent F ![(1 : E), δ] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h' := congrArg c hst
    have hsm : ∀ (p : F) (x : E), c (p • x) = p • c x := fun p x => by
      rw [Algebra.smul_def, Algebra.smul_def, map_mul, c.commutes]
    rw [map_add, hsm, hsm, map_one, hcδ, map_zero, smul_neg] at h'
    have ht : t • δ = 0 := by
      have : (2 : E) * (t • δ) = 0 := by linear_combination hst - h'
      simpa using this
    have ht' : t = 0 := by simpa [hδ] using ht
    refine ⟨?_, ht'⟩
    simpa [ht'] using hst
  have hsp := hli.span_eq_top_of_card_eq_finrank' (by simp [h2])
  intro x
  have hx : x ∈ Submodule.span F (Set.range ![(1 : E), δ]) := hsp ▸ Submodule.mem_top
  rw [Matrix.range_cons_cons_empty, Submodule.mem_span_pair] at hx
  obtain ⟨p, q, rfl⟩ := hx
  exact ⟨p, q, by simp [Algebra.smul_def]⟩

theorem eq_or_conj (c : E ≃ₐ[F] E) (hτ : ∀ (τ : E →+* ℂ) x, τ (c x) = starRingEnd ℂ (τ x))
    {δ : E} (h0 : δ ≠ 0) (hc : c δ = -δ)
    (hs : ∀ x : E, ∃ p q : F, x = algebraMap F E p + algebraMap F E q * δ) (τ τ' : E →+* ℂ)
    (h : τ.comp (algebraMap F E) = τ'.comp (algebraMap F E)) :
    τ = τ' ∨ τ = ComplexEmbedding.conjugate τ' := by
  have hp : ∀ p, τ (algebraMap F E p) = τ' (algebraMap F E p) := fun p => RingHom.congr_fun h p
  obtain ⟨p, q, hpq⟩ := hs (δ * δ)
  have h' := congrArg c hpq
  rw [map_mul, map_add, map_mul, hc, c.commutes, c.commutes] at h'
  have hsq : δ * δ = algebraMap F E p := by linear_combination (hpq + h') / 2
  have : τ δ * τ δ = τ' δ * τ' δ := by rw [← map_mul, ← map_mul, hsq, hp]
  rcases mul_self_eq_mul_self_iff.1 this with e | e
  · left
    ext x
    obtain ⟨p, q, rfl⟩ := hs x
    simp [hp, e]
  · right
    ext x
    obtain ⟨p, q, rfl⟩ := hs x
    rw [ComplexEmbedding.conjugate_coe_eq, ← hτ]
    simp [hp, e, hc]

theorem exists_decomp {δ : E} (hs : ∀ x : E, ∃ p q : F, x = algebraMap F E p + algebraMap F E q * δ)
    (z : InfiniteAdeleRing F ⊗[F] E) : ∃ a b : InfiniteAdeleRing F, z = a ⊗ₜ 1 + b ⊗ₜ δ := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul a x =>
    obtain ⟨p, q, rfl⟩ := hs x
    refine ⟨p • a, q • a, ?_⟩
    rw [TensorProduct.tmul_add, TensorProduct.smul_tmul, TensorProduct.smul_tmul, Algebra.smul_def,
      Algebra.smul_def, mul_one]
  | add x y hx hy =>
    obtain ⟨a, b, rfl⟩ := hx
    obtain ⟨a', b', rfl⟩ := hy
    exact ⟨a + a', b + b', by rw [TensorProduct.add_tmul, TensorProduct.add_tmul]; abel⟩

theorem mk_eq_iff [IsTotallyReal F] {σ σ' : F →+* ℂ} (h : InfinitePlace.mk σ = InfinitePlace.mk σ') : σ = σ' := by
  rw [← InfinitePlace.embedding_mk_eq_of_isReal (IsTotallyReal.complexEmbedding_isReal σ), h,
    InfinitePlace.embedding_mk_eq_of_isReal (IsTotallyReal.complexEmbedding_isReal σ')]

theorem exists_over [IsTotallyReal F] (Ψ : Set (E →+* ℂ))
    (hΨ : ∀ τ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) (w : InfinitePlace F) :
    ∃ τ ∈ Ψ, InfinitePlace.mk (τ.comp (algebraMap F E)) = w := by
  have h : InfinitePlace.mk ((ComplexEmbedding.lift E w.embedding).comp (algebraMap F E)) = w := by
    rw [ComplexEmbedding.lift_comp_algebraMap, InfinitePlace.mk_embedding]
  by_cases hm : ComplexEmbedding.lift E w.embedding ∈ Ψ
  · exact ⟨_, hm, h⟩
  · refine ⟨ComplexEmbedding.conjugate (ComplexEmbedding.lift E w.embedding), ?_, ?_⟩
    · by_contra hn
      exact hm ((hΨ _).2 hn)
    · rw [← h, ← InfinitePlace.mk_conjugate_eq]
      congr 1
      ext x
      simp

theorem bijective [IsTotallyReal F] (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1)
    (hτ : ∀ (τ : E →+* ℂ) x, τ (c x) = starRingEnd ℂ (τ x))
    (θ : (E →+* ℂ) → (InfiniteAdeleRing F ⊗[F] E →+* ℂ))
    (hθ : ∀ τ a x, θ τ (a ⊗ₜ x) = ext (τ.comp (algebraMap F E)) a * τ x)
    (Ψ : Set (E →+* ℂ)) (hΨ : ∀ τ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) :
    Function.Bijective (fun (z : InfiniteAdeleRing F ⊗[F] E) (τ : Ψ) => θ τ.1 z) := by
  obtain ⟨δ, h0, hcδ, hs⟩ := exists_delta c h2 hc hτ
  have hre : ∀ τ : E →+* ℂ, (τ δ).re = 0 := by
    intro τ
    have := congrArg Complex.re (hτ τ δ)
    rw [hcδ, map_neg, Complex.neg_re, Complex.conj_re] at this
    linarith
  have him : ∀ τ : E →+* ℂ, (τ δ).im ≠ 0 := by
    intro τ h
    exact h0 (τ.injective (by rw [map_zero]; exact Complex.ext (hre τ) h))
  let r : ∀ w : InfinitePlace F, w.Completion →+* ℝ := fun w =>
    InfinitePlace.Completion.extensionEmbeddingOfIsReal (IsTotallyReal.isReal w)
  have hr : ∀ w, Function.Bijective (r w) := fun w =>
    InfinitePlace.Completion.bijective_extensionEmbeddingOfIsReal _
  have hval : ∀ (τ : E →+* ℂ) (a b : InfiniteAdeleRing F), θ τ (a ⊗ₜ 1 + b ⊗ₜ δ) =
      ⟨r _ (a (InfinitePlace.mk (τ.comp (algebraMap F E)))),
        r _ (b (InfinitePlace.mk (τ.comp (algebraMap F E)))) * (τ δ).im⟩ := by
    intro τ a b
    rw [map_add, hθ, hθ, ext_eq_ofReal, ext_eq_ofReal, map_one, mul_one]
    apply Complex.ext
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul, hre, mul_zero, add_zero, r]
    · simp only [Complex.add_im, Complex.ofReal_im, Complex.im_ofReal_mul, zero_add, r]
  choose t ht htw using exists_over (F := F) Ψ hΨ
  constructor
  · intro z z' hz
    obtain ⟨a, b, rfl⟩ := exists_decomp hs z
    obtain ⟨a', b', rfl⟩ := exists_decomp hs z'
    have key : ∀ w, a w = a' w ∧ b w = b' w := by
      intro w
      have := congrFun hz ⟨t w, ht w⟩
      simp only [hval, Complex.mk.injEq] at this
      rw [htw w] at this
      exact ⟨(hr w).1 this.1, (hr w).1 (mul_right_cancel₀ (him _) this.2)⟩
    have ha : a = a' := funext fun w => (key w).1
    have hb : b = b' := funext fun w => (key w).2
    rw [ha, hb]
  · intro y
    choose a ha using fun w => (hr w).2 (y ⟨t w, ht w⟩).re
    choose b hb using fun w => (hr w).2 ((y ⟨t w, ht w⟩).im / (t w δ).im)
    refine ⟨(show InfiniteAdeleRing F from a) ⊗ₜ[F] (1 : E) + (show InfiniteAdeleRing F from b) ⊗ₜ[F] δ, ?_⟩
    funext τ
    obtain ⟨τ, hτΨ⟩ := τ
    have e : t (InfinitePlace.mk (τ.comp (algebraMap F E))) = τ := by
      rcases eq_or_conj c hτ h0 hcδ hs _ _ (mk_eq_iff (htw (InfinitePlace.mk (τ.comp (algebraMap F E))))) with e | e
      · exact e
      · exact absurd (e ▸ ht _) ((hΨ τ).1 hτΨ)
    have := hval τ a b
    simp only [ha, hb, e] at this
    refine this.trans ?_
    apply Complex.ext
    · rfl
    · exact div_mul_cancel₀ _ (him τ)

end GlobalTheory.InfAdeleCM
end
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenRegularCharacters
attribute [-instance] _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.LocalLattice.instIsScalarTowerLocalRing _root_.GlobalTheory.Mem.Chr.negTwoFact _root_.GlobalTheory.Mem.finite_absNorm_fiber _root_.GlobalTheory.SplitWeil.matrixMeasurableSpace
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open Polynomial GlobalTheory.GLq

namespace GlobalTheory.Published

def IsRegularChar (g d : ℕ) {K : Type} [Field K] (θ : Kˣ →* ℂˣ) : Prop :=
  ∀ i j, i < d → j < d → θ ^ g ^ i = θ ^ g ^ j → i = j

end GlobalTheory.Published

end
end

section
-- module Solutions.AlpoGe.Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsInfEmbUnique
attribute [-instance] _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.LocalLattice.instIsScalarTowerLocalRing _root_.GlobalTheory.Mem.Chr.negTwoFact _root_.GlobalTheory.Mem.finite_absNorm_fiber _root_.GlobalTheory.SplitWeil.matrixMeasurableSpace
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qh26.Ainf :
    (F : Type) → [Field F] → Type :=
    fun (F : Type) [Field F] ↦ NumberField.InfiniteAdeleRing F

noncomputable def UpperTheory.Reformulated.B.Qh26.IsInfEmb :
    {F E : Type} →
      [inst : Field F] →
        [inst_1 : Field E] → [inst_2 : Algebra F E] → (E →+* ℂ) → (TensorProduct F (UpperTheory.Reformulated.B.Qh26.Ainf F) E →+* ℂ) → Prop :=
    fun {F E : Type} [Field F] [Field E] [Algebra F E] (τ : E →+* ℂ)
        (θ : TensorProduct F (UpperTheory.Reformulated.B.Qh26.Ainf F) E →+* ℂ) ↦
      (∀ (x : E),
          (θ : TensorProduct F (UpperTheory.Reformulated.B.Qh26.Ainf F) E → ℂ) ((1 : UpperTheory.Reformulated.B.Qh26.Ainf F) ⊗ₜ[F] x) = (τ : E → ℂ) x) ∧
        Continuous fun (a : UpperTheory.Reformulated.B.Qh26.Ainf F) ↦
          (θ : TensorProduct F (UpperTheory.Reformulated.B.Qh26.Ainf F) E → ℂ) (a ⊗ₜ[F] (1 : E))

theorem UpperTheory.Reformulated.B.Qh26.isInfEmb_unique :
    ∀ {F E : Type} [inst : Field F] [NumberField F] [inst_2 : Field E] [NumberField E] [inst_4 : Algebra F E] (τ : E →+* ℂ)
      {θ θ' : TensorProduct F (UpperTheory.Reformulated.B.Qh26.Ainf F) E →+* ℂ},
      UpperTheory.Reformulated.B.Qh26.IsInfEmb τ θ → UpperTheory.Reformulated.B.Qh26.IsInfEmb τ θ' → θ = θ' := by
  intro F E _ _ _ _ _ τ θ θ' h h'
  have hd : DenseRange (algebraMap F (UpperTheory.Reformulated.B.Qh26.Ainf F)) :=
    NumberField.InfiniteAdeleRing.denseRange_algebraMap F
  have key : ∀ x : F, (algebraMap F (UpperTheory.Reformulated.B.Qh26.Ainf F) x) ⊗ₜ[F] (1 : E)
      = (1 : UpperTheory.Reformulated.B.Qh26.Ainf F) ⊗ₜ[F] (algebraMap F E x) := by
    intro x
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  have h1 : (fun a : UpperTheory.Reformulated.B.Qh26.Ainf F ↦ θ (a ⊗ₜ[F] (1 : E)))
      = fun a : UpperTheory.Reformulated.B.Qh26.Ainf F ↦ θ' (a ⊗ₜ[F] (1 : E)) := by
    refine hd.equalizer h.2 h'.2 ?_
    funext x
    simp only [Function.comp_apply]
    rw [key, h.1, h'.1]
  refine RingHom.ext fun z ↦ ?_
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul a e =>
    have hs : a ⊗ₜ[F] e = (a ⊗ₜ[F] (1 : E)) * ((1 : UpperTheory.Reformulated.B.Qh26.Ainf F) ⊗ₜ[F] e) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [hs, map_mul, map_mul, h.1, h'.1, congrFun h1 a]
end

section
-- module Solutions.AlpoGe.Formalism.UnipotentAdelicQuotients.ThmBInHecke
attribute [-instance] _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.LocalLattice.instIsScalarTowerLocalRing _root_.GlobalTheory.Mem.Chr.negTwoFact _root_.GlobalTheory.Mem.finite_absNorm_fiber _root_.GlobalTheory.SplitWeil.matrixMeasurableSpace
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open scoped TensorProduct
open NumberField IsDedekindDomain

namespace HeckeCharacterZeroLocus.ThmBIn

section Adeles

variable (F : Type) [Field F] [NumberField F]

abbrev AF := AdeleRing (𝓞 F) F

abbrev Ainf := InfiniteAdeleRing F

abbrev Af := FiniteAdeleRing (𝓞 F) F

abbrev Fv (v : HeightOneSpectrum (𝓞 F)) := v.adicCompletion F

def sndA : AF F →ₐ[F] Af F := AlgHom.snd F (Ainf F) (Af F)

def evalV (v : HeightOneSpectrum (𝓞 F)) : Af F →ₐ[F] Fv F v :=
  { RestrictedProduct.evalRingHom (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F) v with
    commutes' := fun _ => rfl }

def intAf : Set (Af F) :=
  {a | ∀ v : HeightOneSpectrum (𝓞 F), evalV F v a ∈ v.adicCompletionIntegers F}

end Adeles

section Tens

variable {F E : Type} [Field F] [Field E] [Algebra F E]

scoped instance topTens (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] :
    TopologicalSpace (R ⊗[F] E) := moduleTopology R (R ⊗[F] E)

variable (R : Type) [CommRing R] [Algebra F R]

def inclR : E →+* R ⊗[F] E := (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E).toRingHom

end Tens

def IsCMExt (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) : Prop :=
  NumberField.IsTotallyReal F ∧ NumberField.IsTotallyComplex E ∧ Module.finrank F E = 2 ∧
    ∀ (τ : E →+* ℂ) (x : E), τ (σ x) = star (τ x)

section Hecke

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

abbrev AE : Type := AF F ⊗[F] E

abbrev incA : E →+* AF F ⊗[F] E := inclR (F := F) (AF F)

def finPart : AE F E →+* Af F ⊗[F] E :=
  (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom

def intAE : AddSubgroup (Af F ⊗[F] E) :=
  AddSubgroup.closure {y | ∃ a ∈ intAf F, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)}

end Hecke

end HeckeCharacterZeroLocus.ThmBIn

end
end


