-- Prove2me | Definitions.Def_Yukon_1cd70c1313f8de4ca20c8ffd
-- name    : Yukon_1cd70c1313f8de4ca20c8ffd
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-03T23:06:57.733211+00:00
-- url     : https://prove2.me/theorems/93a61ec0-62c6-4888-808d-4c51b477a4df
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.MovingSourceReducedCycle6814.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.MovingSourceReducedCycle6814.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/MovingSourceReducedCycle6814.lean
--
--   yukon-proof-operation:certificate-r13-b54-ff6b232ebb4267d92c06697e967e61b6769c310b5e07cc217bf23fcec98e1826
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiMmNlNWU2NzZiYmI2YzBhMjNkNzg1ZmI1MGE4MTJmZGQyYTIzMWE3YzM3ZDgyZDk4ZDJkOTkxMjA3NGUzOGM1NyIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLXIxMy1iNTQtZmY2YjIzMmViYjQyNjdkOTJjMDY2OTdlOTY3ZTYxYjY3NjljMzEwYjVlMDdjYzIxN2JmMjNmY2VjOThlMTgyNiIsInRhZyI6ImJldHRlci1jb2RlcyIsInRhcmdldCI6Ill1a29uXzFjZDcwYzEzMTNmOGRlNGNhMjBjOGZmZCIsInYiOjJ9]

import Definitions.Def_Yukon_b9f61aed25b10510aa4d5321


















































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
/-! Shared resultant multiplicities for the reduced flow. The indices are
the original stage's components, not a conjecturally equal new family.
The primary-power input is proved from the old stage and the flow identity.
No separability or characteristic bound is needed for the power theorem. -/
namespace ProximityPrize.SubmissionLower.MovingSourceReducedCycle6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 600000
open scoped BigOperators
open RCN135 RCN136 RCN074 RCN086 RCN095 RCN244 RCN245 RCN246 RCN249 RCN252
open RCN002 RCN011 RCN021 RCN093 RCN106 RCN107 RCN108 RCN109 RCN111 RCN112 RCN113
open RCN120 RCN125 RCN313 RCN333 RCN102
open MovingSourceFlowNumerator6814 MovingSourceReducedPrimary6814

/-- The old component witnesses that localizing the surface in the chosen
coordinate does not turn a different, proper tail into a multiple of it. -/
theorem plane_not_dvd_replacement
    {Ω : Type} [Field Ω] {F T R : MvPolynomial (Fin 3) Ω}
    (C : RCN264.RegularComponent Ω F T R)
    (lam mu nu : Ω) (order : Fin 3 ≃ Fin 3)
    (ht : Transcendental Ω
      (flagEvaluation Ω C.1 lam mu nu (MvPolynomial.X (order 0))))
    (hF : Irreducible F) (N : MvPolynomial (Fin 3) Ω) (hN : ¬F∣N) :
    ¬flagPlaneMap Ω lam mu nu order F∣flagPlaneMap Ω lam mu nu order N := by
  have hroot : flagEvaluation Ω C.1 lam mu nu (flagAlgHom lam mu nu F)=0 := by
    rw [flagEvaluation_flag]
    change F∈RingHom.ker (coordinateEvaluation Ω C.1).toRingHom
    rw [coordinateEvaluation_ker]
    exact RCN264.regularComponent_G_mem Ω F T R C
  intro hd
  have hh := (planeMap_dvd_iff_of_evaluation Ω (CoordinateField Ω C.1) order
    (flagEvaluation Ω C.1 lam mu nu) (flagAlgHom lam mu nu F) (flagAlgHom lam mu nu N)
    ((flag_irreducible_iff lam mu nu F).mpr hF) hroot ht).mp hd
  exact hN ((flag_dvd_iff lam mu nu F N).mp hh)

theorem resultant_ne_replacement
    {Ω : Type} [Field Ω] {F T R : MvPolynomial (Fin 3) Ω}
    (C : RCN264.RegularComponent Ω F T R)
    (lam mu nu : Ω) (order : Fin 3 ≃ Fin 3)
    (ht : Transcendental Ω
      (flagEvaluation Ω C.1 lam mu nu (MvPolynomial.X (order 0))))
    (hF : Irreducible F) (N : MvPolynomial (Fin 3) Ω) (hN : ¬F∣N)
    (hpos : 0<(flagPlaneMap Ω lam mu nu order F).natDegree) :
    flagPlaneResultant lam mu nu order F N≠0 := by
  classical
  have hi := RCN103.transformedSurface_irreducible lam mu nu order hF C ht
  have hn := plane_not_dvd_replacement C lam mu nu order ht hF N hN
  exact RCN362.irreducible_resultant_ne_zero_of_not_dvd _ _ hi hpos hn

variable {K I : Type} [Field K]
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
  [CharP (GenericField K) p] {errorCap : ℕ}
  {stageSupport : RCN275.ResidualSupportParameters}

def reducedTailSurface (H G : MvPolynomial (Fin 4) K) :
    MvPolynomial (Fin 3) (GenericField K) :=
  surfaceMap (polynomialEmbedding K) (numerators H G (RCN326.w+1))

theorem reduced_resultant_ne
    (S : Stage K I Gamma x p flag errorCap stageSupport)
    {A : Type} [Fintype A] (F : StageIndexedFlagFamily S A) (a : A)
    (H G : MvPolynomial (Fin 4) K) (hproper : ¬S.G∣reducedTailSurface H G) :
    flagPlaneResultant F.lam F.mu F.nu F.order S.G (reducedTailSurface H G)≠0 := by
  exact resultant_ne_replacement (F.component a) F.lam F.mu F.nu F.order (F.ht a)
    S.irreducible_G (reducedTailSurface H G) hproper F.positive

/-- A single resultant pays the sum of the OLD multiplicities times the
residue degrees of ALL components over q. No per-component degree charge. -/
theorem reduced_grouped_power_dvd
    (S : Stage K I Gamma x p flag errorCap stageSupport)
    (hfirst : ¬S.G∣globalTailCut (polynomialEmbedding K) S.F (RCN326.w+1))
    (H G : MvPolynomial (Fin 4) K)
    (hcross : S.F∣H^(2*(RCN326.w+1))*numerator K S.F (RCN326.w+1)-
      (polyH K S.F)^(2*(RCN326.w+1))*numerators H G (RCN326.w+1))
    (hproper : ¬S.G∣reducedTailSurface H G)
    {A : Type} [Fintype A] (F : StageIndexedFlagFamily S A) (W : StageIndexedFactor S A F) :
    W.q^stageFamilyGroupedExponent S A hfirst F W.q∣
      flagPlaneResultant F.lam F.mu F.nu F.order S.G (reducedTailSurface H G) := by
  let surface := stageSurfacePlane S F.lam F.mu F.nu F.order
  let oldTail := stageTailPlane S F.lam F.mu F.nu F.order
  let newTail := flagPlaneMap (GenericField K) F.lam F.mu F.nu F.order (reducedTailSurface H G)
  letI : (Ideal.span {indexedFiberSurface W.q W.irreducible surface}).IsPrime :=
    indexedFiberSurface_span_isPrime F.component F.lam F.mu F.nu F.order F.ht
      S.irreducible_G W.q W.irreducible W.witness
  have hsurface := indexedStageSurface_mem_relation S F.component F.lam F.mu F.nu F.order F.ht
  have holdRoot : ∀ a : IndexedFactorFiber F.component F.lam F.mu F.nu F.order F.ht W.q,
      oldTail∈relationKernel (GenericField K) (CoordinateField (GenericField K) (F.component a.1).1)
        F.order (flagEvaluation (GenericField K) (F.component a.1).1 F.lam F.mu F.nu) (F.ht a.1) := by
    intro a
    exact flagPlaneMap_mem_relation (F.component a.1).1 F.lam F.mu F.nu F.order (F.ht a.1)
      (RCN264.regularComponent_T_mem (GenericField K) S.G _ _ (F.component a.1))
  have holdProper : indexedFiberTail W.q W.irreducible oldTail∉
      Ideal.span {indexedFiberSurface W.q W.irreducible surface} :=
    indexedFiberTail_not_mem_surface F.component F.lam F.mu F.nu F.order F.ht
      S.irreducible_G hfirst W.q W.irreducible W.witness
  have hbar := indexedFiberRelationBar_ne_bot F.component F.lam F.mu F.nu F.order F.ht
    W.q W.irreducible surface oldTail holdRoot holdProper
  have htail := indexed_reduced_tail_mem_primary S hfirst H G hcross F.component
    F.lam F.mu F.nu F.order F.ht F.finite F.generates W.q W.irreducible
  have hres : Polynomial.resultant surface newTail surface.natDegree newTail.natDegree≠0 :=
    reduced_resultant_ne S F W.witness.1 H G hproper
  have hmod : (indexedFiberSurface W.q W.irreducible surface).map
      (IsLocalRing.residue (FiberCoefficient W.q W.irreducible))≠0 :=
    stageFamily_surface_mod_ne S F W
  exact indexedFixedFactor_grouped_resultant_power_dvd_of_geometry F.component F.injective
    F.lam F.mu F.nu F.order F.ht F.finite F.generates W.q W.irreducible W.monic
    surface newTail surface.natDegree newTail.natDegree
    (fun a => hsurface a.1) hbar
    (fun a => localMultiplicity S (canonicalLocalDVRFamily S hfirst) (F.component a.1))
    htail Polynomial.natDegree_map_le Polynomial.natDegree_map_le hres hmod

/-- The shared geometric degree estimate for a chosen separating
projection. Separability belongs to the chosen projection, NOT to a
characteristic gate on this resultant's degree. -/
theorem reduced_projection_sum_le
    (S : Stage K I Gamma x p flag errorCap stageSupport)
    (hfirst : ¬S.G∣globalTailCut (polynomialEmbedding K) S.F (RCN326.w+1))
    (H G : MvPolynomial (Fin 4) K)
    (hcross : S.F∣H^(2*(RCN326.w+1))*numerator K S.F (RCN326.w+1)-
      (polyH K S.F)^(2*(RCN326.w+1))*numerators H G (RCN326.w+1))
    (hproper : ¬S.G∣reducedTailSurface H G)
    {A : Type} [Fintype A] (F : StageIndexedFlagFamily S A)
    (hgate : ∀ a, ∀ hx : Transcendental (GenericField K)
        (flagEvaluation (GenericField K) (F.component a).1 F.lam F.mu F.nu
          (MvPolynomial.X (F.order 0))),
      (letI := flagBaseAlgebra (GenericField K) (F.component a).1 F.lam F.mu F.nu F.order hx;
        FiniteDimensional (RatFunc (GenericField K)) (CoordinateField (GenericField K) (F.component a).1)) ∧
      (letI := flagBaseAlgebra (GenericField K) (F.component a).1 F.lam F.mu F.nu F.order hx;
        Algebra.IsSeparable (RatFunc (GenericField K)) (CoordinateField (GenericField K) (F.component a).1)))
    (axis : MovingSourceProjectionFamily6814.Axis) (horder : F.order=axis.order)
    (surfaceFlag tailFlag : FlagDegree)
    (hSflag : RCN095.PolynomialInFlag surfaceFlag S.G)
    (hTflag : RCN095.PolynomialInFlag tailFlag (reducedTailSurface H G)) :
    (∑ a, localMultiplicity S (canonicalLocalDVRFamily S hfirst) (F.component a)*
      RCN344.coordinateDegree (GenericField K) (CoordinateField (GenericField K) (F.component a).1)
        (RCN042.coordinateOfGate
          (flagEvaluation (GenericField K) (F.component a).1 F.lam F.mu F.nu
            (MvPolynomial.X (F.order 0))) (hgate a))) ≤
      RCN095.flagMixed surfaceFlag tailFlag axis.flag := by
  classical
  by_cases hA : Nonempty A
  · let a0 : A := Classical.choice hA
    have hres := reduced_resultant_ne S F a0 H G hproper
    have hTne : reducedTailSurface H G≠0 := fun hz => hproper (hz ▸ dvd_zero _)
    have hdegree : (flagPlaneResultant F.lam F.mu F.nu F.order S.G
        (reducedTailSurface H G)).natDegree ≤ RCN095.flagMixed surfaceFlag tailFlag axis.flag := by
      rw [horder]
      exact MovingSourceProjectionFamily6814.flag_resultant_degree_le axis F.lam F.mu F.nu
        S.G (reducedTailSurface H G) surfaceFlag tailFlag hSflag hTflag hTne
    let channel := RCN104.indexedWeightedFlagPlaneChannel_of_fixedFactors F.component F.lam F.mu F.nu
      F.order F.ht F.finite F.generates hgate
      (fun a => localMultiplicity S (canonicalLocalDVRFamily S hfirst) (F.component a))
      (flagPlaneResultant F.lam F.mu F.nu F.order S.G (reducedTailSurface H G))
      (RCN095.flagMixed surfaceFlag tailFlag axis.flag) hres hdegree
      (fun q hq hmonic a => reduced_grouped_power_dvd S hfirst H G hcross hproper F
        ⟨q,hq,hmonic,a⟩)
    exact channel.sum_mul_cost_le
  · letI : IsEmpty A := ⟨fun a => hA ⟨a⟩⟩
    simp







end
end ProximityPrize.SubmissionLower.MovingSourceReducedCycle6814


