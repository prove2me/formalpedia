-- Prove2me | Definitions.Def_DetDLP_M3D_ECPlanBridge_final
-- name    : DetDLP_M3D_ECPlanBridge_final
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T10:51:44.673367+00:00
-- url     : https://prove2.me/theorems/6394fbbf-ccbc-46b2-8bfc-eb152946cddc
-- title:
--   M3D EC plan bridge
-- statement:
--   Combines Stage I EC plan preparation, enumeration, decoder interface, and a dense-covering surjectivity lemma.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Theorems.Thm_DetDLP_m89_s1_ec_plan_prepare
import Theorems.Thm_DetDLP_m89_s1_ec_plan_enumerate
import Theorems.Thm_DetDLP_m89_s1_ec_plan_decode
import Theorems.Thm_DetDLP_m89_s1_winning_seed_mean
import Theorems.Thm_DetDLP_lemma_3_2_collision_potential
import Theorems.Thm_DetDLP_dense_covering_and_2m_decomp
import Definitions.Def_DetDLP_FactorBase

set_option autoImplicit false
namespace DetDLP
open M89S1 OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

/-- A large-branch Stage-I plan supplies an enumerated native block base; no external `F`
list generator is needed for construction of this base. -/
theorem m3d_ec_plan_base (hord : M89S1.CountOracle) :
    ∃ (U : PrimitiveMachine) (u : Fin U.tapeCount) (V : PrimitiveMachine) (v : Fin V.tapeCount)
      (J K : ℕ),
      ∀ (p : ℕ) [Fact p.Prime], 3 < p → ∀ (E : WeierstrassCurve (ZMod p)) [E.IsElliptic],
        letI := ecPointFintype E
        let m := blockCount (bitLen p)
        let M := Fintype.card E.toAffine.Point
        64 ≤ M → 4096*m ≤ M-1 →
        ∃ (seed : ECSeed p m) (B : Fin m → List E.toAffine.Point),
          seed ∈ winners ecBits (ecCost E) ∧
          (∀ i, (B i).Nodup ∧ (B i).toFinset = ecFactorBlock E (hashThreshold p (M-1) m M) seed i) ∧
          RunsWithin U u (encodeCurveInput p E)
            (Encoding.encodeList id [encodeCurveInput p E,
              m89_ec_plan_word (some (hashThreshold p (M-1) m M,seed))])
            (mainSpaceBound J (bitLen p)) (polyBound J (bitLen p)) ∧
          RunsWithin V v
            (Encoding.encodeList id [encodeCurveInput p E,
              m89_ec_plan_word (some (hashThreshold p (M-1) m M,seed))])
            (encodeECFactorBlocks B) (mainSpaceBound K (bitLen p)) (mainSpaceBound K (bitLen p)) := by
  obtain ⟨U,u,V,v,J,hprep⟩ := m89_s1_ec_plan_prepare hord
  obtain ⟨W,w,K,henum⟩ := m89_s1_ec_plan_enumerate hord
  refine ⟨U,u,W,w,J,K,?_⟩
  intro p hp h3 E hE
  dsimp only
  letI := ecPointFintype E
  let m := blockCount (bitLen p)
  let M := Fintype.card E.toAffine.Point
  intro hM hlarge
  obtain ⟨L,hL,hRunU,hRunV⟩ := hprep p h3 E
  have hlarge' : 64 ≤ M ∧ 4096*m ≤ M-1 := ⟨hM,hlarge⟩
  cases L with
  | none =>
      simp [m89_ec_plan_ok] at hL
      omega
  | some pair =>
      rcases pair with ⟨T,S⟩
      have hL' : 64 ≤ M ∧ 4096*m ≤ M-1 ∧
          T = hashThreshold p (M-1) m M ∧ S ∈ winners ecBits (ecCost E) := by
        simpa [m89_ec_plan_ok] using hL
      rcases hL' with ⟨hM',hlarge'',rfl,hS⟩
      obtain ⟨B,hB,hRunB⟩ := henum p h3 E (some (hashThreshold p (M-1) m M,S)) (by simpa [m89_ec_plan_ok] using ⟨hM',hlarge'',rfl,hS⟩)
      refine ⟨S,B,hS,hB,?_ ,?_⟩
      · simpa using hRunU
      · simpa using hRunB

/-- The plan decoder turns any mathematically available 2m-term decomposition into
its deterministic encoded decomposition; the supplied decomposition may come from density. -/
theorem m3d_ec_plan_decode (hord : M89S1.CountOracle) :
    ∃ (D : PrimitiveMachine) (o : Fin D.tapeCount) (K : ℕ),
      ∀ (p : ℕ) [Fact p.Prime], 3 < p → ∀ (E : WeierstrassCurve (ZMod p)) [E.IsElliptic],
        letI := ecPointFintype E
        let m := blockCount (bitLen p)
        ∀ (L : Option (ℕ × ECSeed p m)), m89_ec_plan_ok E L → ∀ X : E.toAffine.Point,
        (∃ A B : Fin m → E.toAffine.Point,
          (∀ i, A i ∈ m89_ec_plan_block E L i ∧ B i ∈ m89_ec_plan_block E L i) ∧
          (∑ i, (A i+B i)) = X) →
        ∃ A B : Fin m → E.toAffine.Point,
          (∀ i, A i ∈ m89_ec_plan_block E L i ∧ B i ∈ m89_ec_plan_block E L i) ∧
          (∑ i, (A i+B i)) = X ∧
          RunsWithin D o
            (Encoding.encodeList id [Encoding.encodeList id [encodeCurveInput p E,
              encodeNatListBin (pointCoords X)],m89_ec_plan_word L])
            (encodeECDecomp A B) (mainSpaceBound K (bitLen p)) (polyBound K (bitLen p)) :=
  m89_s1_ec_plan_decode hord

/-- A seed whose collision potential is below the density threshold gives a decomposition
using every native block; the list representation follows from equality of `toFinset`. -/
theorem m3d_ec_plan_surjective {p m : ℕ} [Fact p.Prime]
    (E : WeierstrassCurve (ZMod p)) [E.IsElliptic] [Fintype E.toAffine.Point]
    [DecidableEq E.toAffine.Point]
    (seed : ECSeed p m) (B : Fin m → List E.toAffine.Point)
    (hB : ∀ i, (B i).toFinset = ecFactorBlock E
      (hashThreshold p (Fintype.card E.toAffine.Point - 1) m (Fintype.card E.toAffine.Point)) seed i)
    (μ : ℝ) (hμ : 0 < μ)
    (hpotential : collisionPotentialAdd μ
      (ecFactorBlock E (hashThreshold p (Fintype.card E.toAffine.Point - 1) m
        (Fintype.card E.toAffine.Point)) seed) < (64 : ℝ)/57) :
    ∀ X : E.toAffine.Point, ∃ A C : Fin m → E.toAffine.Point,
      (∀ i, A i ∈ B i ∧ C i ∈ B i) ∧ (∑ i, (A i+C i)) = X := by
  classical
  let T := hashThreshold p (Fintype.card E.toAffine.Point - 1) m (Fintype.card E.toAffine.Point)
  have hcover := (dense_covering_and_2m_decomp.1 μ (ecFactorBlock E T seed) hμ (by simpa [T] using hpotential)).2
  intro X
  obtain ⟨A,C,hmem,hsum⟩ := hcover X
  refine ⟨A,C,?_,hsum⟩
  intro i
  constructor
  · apply List.mem_toFinset.mp
    rw [hB i]
    exact (hmem i).1
  · apply List.mem_toFinset.mp
    rw [hB i]
    exact (hmem i).2

end DetDLP


