-- Prove2me | solution 1 for AlgebraicGeometry.SmoothOfRelativeDimension.topologicalKrullDim_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/ea48d935-23b0-5080-8931-0869fbeaeb48

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_SmoothOfRelativeDimension_topologicalKrullDim_le

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

namespace P2mSmoothOfRelativeDimensionKrullDim

open TensorProduct IsLocalRing TopologicalSpace Topology

theorem spanFinrank_maximalIdeal_le_finrank_kaehler
    (L P : Type*) [CommRing L] [CommRing P] [Algebra L P] [IsLocalRing P] [IsNoetherianRing P]
    [Algebra.FormallySmooth L P] [Module.Free P Ω[P⁄L]] [Module.Finite P Ω[P⁄L]]
    [Algebra.FormallySmooth L (ResidueField P)] :
    (maximalIdeal P).spanFinrank ≤ Module.finrank P Ω[P⁄L] := by
  have hker : RingHom.ker (algebraMap P (ResidueField P)) = maximalIdeal P := ker_residue
  have hfg : (RingHom.ker (algebraMap P (ResidueField P))).FG :=
    (isNoetherianRing_iff_ideal_fg P).mp ‹_› _
  have hbot : maximalIdeal (ResidueField P) ≤
      RingHom.ker (algebraMap (ResidueField P) (ResidueField P)) := by
    rw [maximalIdeal_eq_bot]
    exact bot_le

  have hinj : Function.Injective (KaehlerDifferential.cotangentComplexBaseChange L
      (ResidueField P) P (ResidueField P)) :=
    (Algebra.FormallySmooth.iff_injective_cotangentComplexBaseChange (R := L)
      (S := ResidueField P) P (ResidueField P) residue_surjective hfg hbot).mp ‹_›
  haveI : Module.Free (ResidueField P)
      (ResidueField P ⊗[P] (RingHom.ker (algebraMap P (ResidueField P)))) :=
    Module.Free.of_divisionRing _ _
  have h1 : Module.finrank (ResidueField P)
        (ResidueField P ⊗[P] (RingHom.ker (algebraMap P (ResidueField P)))) ≤
      Module.finrank (ResidueField P) (ResidueField P ⊗[P] Ω[P⁄L]) :=
    LinearMap.finrank_le_finrank_of_injective hinj
  have h2 : Module.finrank (ResidueField P) (ResidueField P ⊗[P] Ω[P⁄L]) =
      Module.finrank P Ω[P⁄L] := by
    let b := Module.Free.chooseBasis P Ω[P⁄L]
    rw [Module.finrank_eq_card_basis (Algebra.TensorProduct.basis (ResidueField P) b),
      Module.finrank_eq_card_basis b]

  have h3 : (maximalIdeal P).spanFinrank = Module.finrank (ResidueField P)
        (ResidueField P ⊗[P] (RingHom.ker (algebraMap P (ResidueField P)))) := by
    rw [Module.finrank_eq_spanFinrank_of_free,
      TensorProduct.spanFinrank_top_eq_of_residueField _ hfg, hker]
  rw [h3, ← h2]
  exact h1

theorem ringKrullDim_le_finrank_kaehler
    (L P : Type*) [CommRing L] [CommRing P] [Algebra L P] [IsLocalRing P] [IsNoetherianRing P]
    [Algebra.FormallySmooth L P] [Module.Free P Ω[P⁄L]] [Module.Finite P Ω[P⁄L]]
    [Algebra.FormallySmooth L (ResidueField P)] :
    ringKrullDim P ≤ Module.finrank P Ω[P⁄L] :=
  (ringKrullDim_le_spanFinrank_maximalIdeal P).trans
    (by exact_mod_cast spanFinrank_maximalIdeal_le_finrank_kaehler L P)

section PerfectBase

variable {L : Type*} [Field L] {B : Type*} [CommRing B] [Algebra L B]

theorem ringKrullDim_localization_le [PerfectField L] (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n L B] (m : Ideal B) [m.IsPrime] :
    ringKrullDim (Localization.AtPrime m) ≤ n := by
  classical

  haveI : Algebra.IsStandardSmooth L B :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  haveI : Algebra.FiniteType L B := inferInstance
  haveI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing L B
  haveI : Nontrivial B := ⟨⟨0, 1, fun h => Ideal.IsPrime.ne_top' (I := m)
    (Ideal.eq_top_of_isUnit_mem _ m.zero_mem (by rw [h]; exact isUnit_one))⟩⟩
  haveI : IsNoetherianRing (Localization.AtPrime m) :=
    IsLocalization.isNoetherianRing m.primeCompl _ ‹_›

  haveI : Algebra.FormallySmooth B (Localization.AtPrime m) := .of_isLocalization m.primeCompl
  haveI : Algebra.FormallySmooth L (Localization.AtPrime m) := .comp L B _

  let b := Module.Free.chooseBasis B Ω[B⁄L]
  let bm : Module.Basis _ (Localization.AtPrime m) Ω[Localization.AtPrime m⁄L] :=
    b.ofIsLocalizedModule (Localization.AtPrime m) m.primeCompl
      (KaehlerDifferential.map L L B (Localization.AtPrime m))
  haveI : Module.Free (Localization.AtPrime m) Ω[Localization.AtPrime m⁄L] := .of_basis bm
  haveI : Module.Finite (Localization.AtPrime m) Ω[Localization.AtPrime m⁄L] := .of_basis bm
  have hrank : Module.finrank (Localization.AtPrime m) Ω[Localization.AtPrime m⁄L] = n := by
    have h := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (R := L)
      (S := B) n
    rw [Module.Free.rank_eq_card_chooseBasisIndex, Cardinal.mk_fintype] at h
    rw [Module.finrank_eq_card_basis bm]
    exact_mod_cast h

  haveI : Algebra.EssFiniteType L (ResidueField (Localization.AtPrime m)) :=
    .comp L (Localization.AtPrime m) _
  haveI : Algebra.FormallySmooth L (ResidueField (Localization.AtPrime m)) :=
    Algebra.FormallySmooth.of_perfectField
  rw [← hrank]
  exact ringKrullDim_le_finrank_kaehler L _

theorem ringKrullDim_le_of_perfectField [PerfectField L] (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n L B] : ringKrullDim B ≤ n := by
  rw [ringKrullDim_le_iff_isMaximal_height_le]
  intro m hm
  rw [← IsLocalization.AtPrime.ringKrullDim_eq_height m (Localization.AtPrime m)]
  exact ringKrullDim_localization_le (L := L) n m

end PerfectBase

theorem ringKrullDim_le_of_faithfullyFlat (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [Module.FaithfullyFlat R S] : ringKrullDim R ≤ ringKrullDim S := by
  change (⨆ p : LTSeries (PrimeSpectrum R), (p.length : WithBot ℕ∞)) ≤ _
  refine iSup_le fun l => ?_
  obtain ⟨P, hP, hPo⟩ :=
    Ideal.exists_isPrime_liesOver_of_faithfullyFlat (B := S) l.last.asIdeal
  obtain ⟨L', hlen, -, -⟩ := Ideal.exists_ltSeries_of_hasGoingDown (S := S) l P
  calc ((l.length : WithBot ℕ∞)) = L'.length := by rw [hlen]
    _ ≤ Order.krullDim (PrimeSpectrum S) := Order.LTSeries.length_le_krullDim L'

theorem ringKrullDim_le_of_isStandardSmoothOfRelativeDimension
    {K : Type*} [Field K] {B : Type*} [CommRing B] [Algebra K B] (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n K B] : ringKrullDim B ≤ n := by
  let L := AlgebraicClosure K
  have h1 : ringKrullDim (L ⊗[K] B) ≤ n := ringKrullDim_le_of_perfectField (L := L) n
  have h2 : ringKrullDim B ≤ ringKrullDim (B ⊗[K] L) := ringKrullDim_le_of_faithfullyFlat B _
  have h3 : ringKrullDim (B ⊗[K] L) = ringKrullDim (L ⊗[K] B) :=
    ringKrullDim_eq_of_ringEquiv (Algebra.TensorProduct.comm K B L).toRingEquiv
  exact h2.trans (h3 ▸ h1)

theorem ringKrullDim_le_of_ringHom {R S : Type*} [CommRing R] [CommRing S] (hR : IsField R)
    (φ : R →+* S) (n : ℕ) (hφ : φ.IsStandardSmoothOfRelativeDimension n) :
    ringKrullDim S ≤ n := by
  letI := hR.toField
  letI := φ.toAlgebra
  haveI : Algebra.IsStandardSmoothOfRelativeDimension n R S := hφ
  exact ringKrullDim_le_of_isStandardSmoothOfRelativeDimension (K := R) n

section Sober

attribute [local instance] specializationOrder

theorem topologicalKrullDim_le_of_forall_exists_isOpenEmbedding {X : Type u} [TopologicalSpace X]
    [QuasiSober X] [T0Space X] (n : WithBot ℕ∞)
    (h : ∀ x : X, ∃ (U : Type u) (_ : TopologicalSpace U) (g : U → X),
      IsOpenEmbedding g ∧ x ∈ Set.range g ∧ topologicalKrullDim U ≤ n) :
    topologicalKrullDim X ≤ n := by
  rw [topologicalKrullDim, Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X)),
    Order.krullDim_eq_iSup_coheight]
  refine iSup_le fun x => ?_
  obtain ⟨U, _, g, hg, ⟨y, rfl⟩, hU⟩ := h x
  haveI : QuasiSober U := hg.quasiSober
  haveI : T0Space U := hg.isEmbedding.t0Space
  rw [hg.coheight_eq (x := y)]
  calc (↑(Order.coheight y) : WithBot ℕ∞) ≤ Order.krullDim U := Order.coheight_le_krullDim _
    _ = topologicalKrullDim U :=
        (Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := U))).symm
    _ ≤ n := hU

end Sober

theorem topologicalKrullDim_le {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of K)) (n : ℕ) [SmoothOfRelativeDimension n f] :
    topologicalKrullDim X ≤ n := by
  refine topologicalKrullDim_le_of_forall_exists_isOpenEmbedding (X := X) n fun x => ?_
  obtain ⟨U, hU, V, hV, hxV, e, hf⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := n) (f := f) x
  refine ⟨↥V, inferInstance, Subtype.val, V.2.isOpenEmbedding_subtypeVal, ⟨⟨x, hxV⟩, rfl⟩, ?_⟩

  have hU' : U = ⊤ := by
    haveI : Subsingleton (Spec (CommRingCat.of K)) :=
      inferInstanceAs (Subsingleton (PrimeSpectrum K))
    ext y
    simp only [Opens.coe_top, Set.mem_univ, iff_true]
    have hx : f.base x ∈ U := e hxV
    rwa [Subsingleton.elim y (f.base x)]
  subst hU'
  have hK : IsField Γ(Spec (CommRingCat.of K), ⊤) :=
    MulEquiv.isField (Field.toIsField K)
      (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toMulEquiv

  have hring : ringKrullDim Γ(X, V) ≤ n := ringKrullDim_le_of_ringHom hK _ n hf
  have hSpec : topologicalKrullDim (Spec Γ(X, V)) ≤ n := by
    change topologicalKrullDim (PrimeSpectrum Γ(X, V)) ≤ n
    rwa [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  rw [← IsHomeomorph.topologicalKrullDim_eq _ hV.isoSpec.hom.homeomorph.isHomeomorph] at hSpec
  exact hSpec

end P2mSmoothOfRelativeDimensionKrullDim

theorem solution
    {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K)) (n : ℕ)
    [SmoothOfRelativeDimension n f] :
    topologicalKrullDim X ≤ n :=
  P2mSmoothOfRelativeDimensionKrullDim.topologicalKrullDim_le f n

end S_AlgebraicGeometry_SmoothOfRelativeDimension_topologicalKrullDim_le
end P2MW
export P2MW.S_AlgebraicGeometry_SmoothOfRelativeDimension_topologicalKrullDim_le (solution)
