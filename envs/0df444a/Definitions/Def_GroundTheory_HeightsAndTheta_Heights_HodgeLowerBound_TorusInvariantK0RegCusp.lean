-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_TorusInvariantK0RegCusp
-- name    : GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_TorusInvariantK0RegCusp
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T06:06:04.198495+00:00
-- url     : https://prove2.me/theorems/8be095f0-596e-43ce-be21-b6daca6cac60
-- title:
--   Torus Invariant K0 Reg Cusp
-- statement:
--   Definitions and structural lemmas for Torus Invariant K0 Reg Cusp, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/TorusInvariantK0RegCusp.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ArithmeticHilbertSamuelLowerBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MixedFieldContraction_GenericFibreKerTarget
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ProjLineRankTwoPushforwardHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IsConeAnalyticSubset
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree.Nine
open MvPolynomial Filter Topology Matrix ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
section Points
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
abbrev Cone (ι : K → Type) : Type := (Σ k, ι k) → ℂ
def evalC (f : MRing ι) (z : Cone ι) : ℂ := eval z (map (Int.castRingHom ℂ) f)
def cls (P : Ideal (MRing ι)) (f : MRing ι) : FnField P :=
  algebraMap (MRing ι ⧸ P) (FnField P) (Ideal.Quotient.mk P f)
def IsHomogOf (P : Ideal (MRing ι)) (x : FnField P) (d : K → ℤ) : Prop :=
  ∃ (g h : MRing ι) (dg dh : K → ℕ), IsMultiHomog g dg ∧ IsMultiHomog h dh ∧ h ∉ P ∧
    (∀ k, (dg k : ℤ) - dh k = d k) ∧ x * cls P h = cls P g
def IsValAt (P : Ideal (MRing ι)) (x : FnField P) (z : Cone ι) (v : ℂ) : Prop :=
  ∃ (g h : MRing ι) (dg dh : K → ℕ), IsMultiHomog g dg ∧ IsMultiHomog h dh ∧ h ∉ P ∧
    x * cls P h = cls P g ∧ evalC h z ≠ 0 ∧ v = evalC g z / evalC h z
def IsAlgPt (P W : Ideal (MRing ι)) : Prop := IsArithVar W 1 ∧ P ≤ W
def OnBd (Bd : Finset (Ideal (MRing ι))) (W : Ideal (MRing ι)) : Prop := ∃ B ∈ Bd, B ≤ W
def openPts (P : Ideal (MRing ι)) (Bd : Finset (Ideal (MRing ι))) : Set (Cone ι) :=
  {z | z ∈ mcPts P ∧ ∀ B ∈ Bd, z ∉ mcPts B}
def conePts : Set (Cone ι) := {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}
def IsTorusInv (u : Cone ι → ℝ) : Prop :=
  ∀ (c : K → ℂ) (z : Cone ι), (∀ k, c k ≠ 0) → u (fun p => c p.1 * z p) = u z
def IsBlockUnit (z : Cone ι) : Prop := ∀ k, ∑ i, ‖z ⟨k, i⟩‖ ^ 2 = 1
def IsTorusDir (z w : Cone ι) : Prop := ∃ c : K → ℂ, w = fun p => c p.1 * z p
def fsLine (a : K → ℤ) : HermLine ι where
  a := a
  h z := ∏ k, Real.sqrt (∑ i, ‖z ⟨k, i⟩‖ ^ 2) ^ a k
  pos z hz := Finset.prod_pos fun k _ => by
    obtain ⟨i, hi⟩ := hz k
    exact zpow_pos (Real.sqrt_pos.mpr (lt_of_lt_of_le (by positivity)
      (Finset.single_le_sum (f := fun i => ‖z ⟨k, i⟩‖ ^ 2) (fun i _ => by positivity)
        (Finset.mem_univ i)))) _
  smul c z hc := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    have : ∑ i, ‖c k * z ⟨k, i⟩‖ ^ 2 = ‖c k‖ ^ 2 * ∑ i, ‖z ⟨k, i⟩‖ ^ 2 := by
      simp [mul_pow, Finset.mul_sum]
    simp only
    rw [this, Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _), mul_zpow]
def oneLine : HermLine ι := HermLine.ofWeight (fun _ => 0) (fun _ _ _ => rfl)
def hdual (A : HermLine ι) : HermLine ι where
  a := -A.a
  h z := (A.h z)⁻¹
  pos z hz := inv_pos.mpr (A.pos z hz)
  smul c z hc := by
    rw [A.smul c z hc, mul_inv, ← Finset.prod_inv_distrib]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Pi.neg_apply, _root_.zpow_neg]
def tensorList : List (HermLine ι) → HermLine ι
  | [] => oneLine
  | A :: l => A.tensor (tensorList l)
def hzpow (A : HermLine ι) (m : ℤ) : HermLine ι :=
  if 0 ≤ m then tensorList (List.replicate m.toNat A) else tensorList (List.replicate (-m).toNat (hdual A))
def htwist (A : HermLine ι) (u : Cone ι → ℝ) (hu : IsTorusInv u) : HermLine ι :=
  A.tensor (HermLine.ofWeight (fun z => -u z) (fun c z hc => by simp only [hu c z hc]))
end Points
section RLines
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable (ι) in

structure RLine where

  m : ℕ

  c : Fin m → ℝ

  L : Fin m → HermLine ι
namespace RLine
def single (c : ℝ) (A : HermLine ι) : RLine ι := ⟨1, fun _ => c, fun _ => A⟩
def pair (c₁ : ℝ) (A : HermLine ι) (c₂ : ℝ) (B : HermLine ι) : RLine ι := ⟨2, ![c₁, c₂], ![A, B]⟩
def weight (A : RLine ι) (z : Cone ι) : ℝ := ∑ s, A.c s * Real.log ((A.L s).h z)
def deg (A : RLine ι) (k : K) : ℝ := ∑ s, A.c s * ((A.L s).a k : ℝ)
def top (II : IntersectionSystem) (P : Ideal (MRing ι)) (d : ℕ) (A : RLine ι) : ℝ :=
  ∑ g : Fin d → Fin A.m, (∏ i, A.c (g i)) * II K ι P d (fun i => A.L (g i))
def ht (II : IntersectionSystem) (A : RLine ι) (W : Ideal (MRing ι)) : ℝ :=
  (∑ s, A.c s * II K ι W 1 ![A.L s]) / degC W
def geomDeg (P : Ideal (MRing ι)) (A : RLine ι) (D : ℕ) : ℝ :=
  ptsIntegral (e := D) P (fun _ z => A.weight z) (fun _ => 1)
def IsSmooth (A : RLine ι) : Prop := ∀ s, IsSmoothHerm (A.L s)
def IsConjInv (A : RLine ι) : Prop := ∀ s, IsConjInvariantH (A.L s)
def IsSemipos (P : Ideal (MRing ι)) (A : RLine ι) : Prop :=
  A.IsSmooth ∧ ∀ z ∈ mcPts P, ∀ w, IsConeTangent (Int.castRingHom ℂ) P z w → 0 ≤ leviForm A.weight z w
def IsNefFibres (P : Ideal (MRing ι)) (A : RLine ι) : Prop :=
  ∀ W : Ideal (MRing ι), IsMultiProjPrime W → P ≤ W → charOf W ≠ 0 →
    ringKrullDim (MRing ι ⧸ W) = ((1 + Fintype.card K : ℕ) : WithBot ℕ∞) →
    0 ≤ ∑ s, A.c s * (geoNum 1 W (fun _ => (A.L s).a) : ℝ)
def IsAmpleGen (P : Ideal (MRing ι)) (A : RLine ι) : Prop :=
  ∀ (W : Ideal (MRing ι)) (d : ℕ), 1 ≤ d → IsArithVar W (d + 1) → P ≤ W → 0 < A.geomDeg W d
end RLine
end RLines
section Systems
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
def errReg (C t : ℝ) : ℝ := C * Real.log (Real.log t⁻¹) / Real.log t⁻¹
structure IsRegSystem (P : Ideal (MRing ι)) (Xo : Set (Cone ι)) (θ ω r u : Cone ι → ℝ)
    (ut : ℝ → Cone ι → ℝ) : Prop where
  smooth : ∀ t, 0 < t → ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ut t) conePts
  inv : ∀ t, IsTorusInv (ut t)
  bounds : ∃ C ℓ₀ : ℝ, 0 < C ∧ ∀ t, 0 < t → ℓ₀ ≤ Real.log t⁻¹ →
    (∀ z ∈ Xo, u z ≤ ut t z) ∧ (∀ z ∈ mcPts P, ut t z ≤ C) ∧
    (∀ z ∈ mcPts P, -C * Real.log (Real.log t⁻¹) ≤ ut t z) ∧
    (∀ z ∈ mcPts P, ∀ w, IsConeTangent (Int.castRingHom ℂ) P z w →
      -errReg C t * leviForm ω z w ≤ leviForm (fun z => θ z + ut t z) z w) ∧
    (∀ z ∈ Xo, r z ≤ Real.log t⁻¹ → ut t z ≤ u z + t ^ (1 / 3 : ℝ) + errReg C t) ∧
    (∀ z ∈ Xo, ut t z ≤ u z + t ^ (1 / 3 : ℝ) + errReg C t * r z) ∧
    (∀ t₀, t ≤ t₀ → ℓ₀ ≤ Real.log t₀⁻¹ → ∀ z ∈ mcPts P, ut t z ≤ ut t₀ z + C * errReg C t₀)
  conv : ∀ Kc ⊆ Xo, IsCompact Kc → ∀ m ≤ 2,
    TendstoUniformlyOn (fun t z => iteratedFDeriv ℝ m (ut t) z) (fun z => iteratedFDeriv ℝ m u z)
      (𝓝[>] 0) Kc
structure IsRegSystemBdd (P : Ideal (MRing ι)) (Xo : Set (Cone ι)) (θ ω u : Cone ι → ℝ)
    (ut : ℝ → Cone ι → ℝ) : Prop where
  smooth : ∀ t, 0 < t → ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ut t) conePts
  inv : ∀ t, IsTorusInv (ut t)
  bounds : ∃ C ℓ₀ : ℝ, 0 < C ∧ ∀ t, 0 < t → ℓ₀ ≤ Real.log t⁻¹ →
    (∀ z ∈ Xo, u z ≤ ut t z) ∧ (∀ z ∈ mcPts P, ut t z ≤ C) ∧
    (∀ z ∈ mcPts P, ∀ w, IsConeTangent (Int.castRingHom ℂ) P z w →
      -errReg C t * leviForm ω z w ≤ leviForm (fun z => θ z + ut t z) z w)
  conv : ∀ z ∈ Xo, Tendsto (fun t => ut t z) (𝓝[>] 0) (𝓝 (u z))
end Systems
section Data
abbrev FlagBundleBlocksOverX {K : Type} (ι : K → Type) (Ψ : Type) (N1 N : ℕ) : K ⊕ (Ψ × Fin (N - 1)) → Type :=
  Sum.elim ι (fun q => PluckerBlocks N1 N q.2)
variable (Ψ : Type) [Fintype Ψ] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
structure ComponentData where

  N : ℕ

  j : ℕ
  two_le_N : 2 ≤ N
  one_le_j : 1 ≤ j
  j_lt_N : j < N

  P : Ideal (MRing ι)
  arith : IsArithVar P (Fintype.card Ψ * j * (N - j) + 1)

  Bd : Finset (Ideal (MRing ι))
  bd_comp : ∀ B ∈ Bd, IsArithVar B (Fintype.card Ψ * j * (N - j)) ∧ P ≤ B

  bdEq : Ideal (MRing ι) → MRing ι
  bdDeg : Ideal (MRing ι) → K → ℕ
  bdEq_spec : ∀ B ∈ Bd, IsMultiHomog (bdEq B) (bdDeg B) ∧ bdEq B ∉ P ∧ bdEq B ∈ B

  N1 : ℕ
  t : ℕ
  what₂ : Ψ → Fin t → Fin N1 → MRing ι
  rowDeg : Ψ → K → ℕ
  quot : ∀ τ, IsQuotRows P (what₂ τ) (rowDeg τ) N
  twist : Ψ → K → ℤ

  basis : Ψ → Matrix (Fin N) (Fin N1) (FnField P)
  ker_basis : ∀ τ, IsKerBasis P (what₂ τ) (basis τ)
  basis_homog : ∀ τ a l, IsHomogOf P (basis τ a l) (twist τ)

  hodge : Ψ → Matrix (Fin (N - j)) (Fin N1) (FnField P)
  hodge_homog : ∀ τ a l, IsHomogOf P (hodge τ a l) (twist τ)
  hodge_indep : ∀ τ, LinearIndependent (FnField P) (hodge τ)
  hodge_sub : ∀ τ a, hodge τ a ∈ Submodule.span (FnField P) (Set.range (basis τ))

  metric : Ψ → Cone ι → Matrix (Fin N1) (Fin N1) ℂ

  detLine : Ψ → HermLine ι

  detCoord : Ψ → FnField P
  detCoord_homog : ∀ τ, IsHomogOf P (detCoord τ) (detLine τ).a

  kMu : K
  k0 : ℕ
  one_le_k0 : 1 ≤ k0

  muCoord : ι kMu → FnField P
  muCoord_homog : ∀ i, IsHomogOf P (muCoord i) 0
  muCoord_ratio : ∀ i i', genPt P ⟨kMu, i⟩ * muCoord i' = genPt P ⟨kMu, i'⟩ * muCoord i
  muCoord_ne : ∃ i, muCoord i ≠ 0

  muLine : HermLine ι
  muLine_a : muLine.a = Pi.single kMu 1

  muRef : HermLine ι
  muRef_a : muRef.a = Pi.single kMu 1

  ample : HermLine ι

  Kamp : ℝ

  S : Finset ℕ
  S_prime : ∀ p ∈ S, p.Prime

  latNum : ℕ → Ψ → Fin N → MRing ι
  latDen : ℕ → Ψ → Fin N → MRing ι
  latFl : ℕ → Ψ → Fin N → HermLine ι

  cuspNorm : ℕ → Cone ι → ℝ

  rd : ℝ

  Lchi : ℝ
  one_le_rd : 1 ≤ rd

  regMu : ℝ → Cone ι → ℝ
  regMu_inv : ∀ t, IsTorusInv (regMu t)

  regCusp : ℝ → Cone ι → ℝ
  regCusp_inv : ∀ t, IsTorusInv (regCusp t)

  regFl : ℝ → Ψ → Fin N → Cone (FlagBundleBlocksOverX ι Ψ N1 N) → ℝ
  regFl_inv : ∀ t τ r, IsTorusInv (regFl t τ r)
variable {Ψ K ι}
namespace ComponentData
variable (D : ComponentData Ψ K ι)
def f (_D : ComponentData Ψ K ι) : ℕ := Fintype.card Ψ
def jp : ℕ := D.N - D.j
def n : ℕ := D.f * D.j * D.jp
def Xo : Set (Cone ι) := openPts D.P D.Bd
def sncWeight (z : Cone ι) : ℝ :=
  Real.exp 1 + ∑ B ∈ D.Bd, Real.log ((fsLine (fun k => (D.bdDeg B k : ℤ))).h z ^ 2 / ‖evalC (D.bdEq B) z‖ ^ 2)
def rMu : Fin D.N := ⟨D.N - D.j - 1, by have := D.j_lt_N; omega⟩
def SB (B : ℕ) : Finset ℕ := D.S.filter (· ≤ B)
def muLat (B : ℕ) : HermLine ι :=
  tensorList ((D.SB B).toList.flatMap fun p => (Finset.univ : Finset Ψ).toList.map fun τ => hdual (D.latFl p τ D.rMu))
def muBase (B : ℕ) : HermLine ι := D.muRef.tensor (hzpow (D.muLat B) D.k0)
def U (z : Cone ι) : ℝ := max 0 (⨆ I : ℕ, -Real.log (D.cuspNorm I z))
def hodgeW (z : Cone ι) : ℝ := (Real.log (D.muLine.h z) - Real.log (D.muRef.h z)) / D.k0
theorem torusInvariant_k0_regMu (t : ℝ) : IsTorusInv (fun z => (D.k0 : ℝ) * D.regMu t z) := fun c z hc => by
  simp only [D.regMu_inv t c z hc]
theorem torusInvariant_k0_regCusp (t : ℝ) : IsTorusInv (fun z => (D.k0 : ℝ) * D.regCusp t z) := fun c z hc => by
  simp only [D.regCusp_inv t c z hc]
def MU (B : ℕ) (eps t' : ℝ) : RLine ι :=
  RLine.pair (1 / D.k0) (htwist (D.muBase B) _ (D.torusInvariant_k0_regCusp t')) eps D.ample
def muT (B : ℕ) (t : ℝ) : RLine ι :=
  RLine.single (1 / D.k0) (htwist (D.muBase B) _ (D.torusInvariant_k0_regMu t))
def arLim (II : IntersectionSystem) (B : ℕ) : ℝ :=
  limUnder (𝓝[>] (0 : ℝ)) fun t => (D.muT B t).top II D.P (D.n + 1)
def degMu : ℝ := (RLine.single (1 / D.k0) D.muRef).geomDeg D.P D.n
def meanU : ℝ :=
  ptsIntegral (e := D.n) D.P (fun _ z => Real.log (D.muLine.h z) / D.k0) D.U / D.degMu
def abelian₂ (B : ℕ) : ℝ := Real.log (B * D.rd) + |D.Lchi|
end ComponentData
end Data
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree.Nine


