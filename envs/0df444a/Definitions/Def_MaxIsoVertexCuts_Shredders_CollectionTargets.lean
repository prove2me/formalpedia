-- Prove2me | Definitions.Def_MaxIsoVertexCuts_Shredders_CollectionTargets
-- name    : MaxIsoVertexCuts_Shredders_CollectionTargets
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T23:58:48.733209+00:00
-- url     : https://prove2.me/theorems/38384a54-8de7-46ae-840e-377d73a71b0b
-- title:
--   CollectionTargets
-- statement:
--   The collection contract uses the exact size window ℓ/2≤|L|≤ℓ, small-component threshold 2/3, and (for the linked case) the constants 20 and 4^((log₂ n)^0.7). One program is chosen for each confidence exponent before ε. All executions meet the time, word and validity bounds. For every fixed target-representation choice one event covers every qualifying cut and component simultaneously. ℓ is any integer; the input clamps it to [0, 2n+1], since the target window is empty for ℓ ≤ 0 and beyond 2n. Lemmas 5.9 and 5.18, printed pp.30,35 (PDF 32,37). Collection outputs use explicit shared dictionaries with charged serialization, not repeated copies of every separator.
-- source:
--   Fischer and Yingchareonthawornchai, Maximal Isolating Vertex Cuts and Shredders: Structure and Applications, STOC 2027 submission, Sections 2–5; machine conventions specified in the mission.

import Mathlib
import Definitions.Def_MaxIsoVertexCuts_Shredders_WeightedInputs

open Classical
open scoped BigOperators
noncomputable section

namespace MaxIsoVertexCuts.Shredders

noncomputable def collectionComplete (linkedOnly : Bool) (I : GraphData) (ell : ℤ) (k : ℕ)
    (F : VSet I.n → List (Cut I.n)) (out : List ℤ) : Prop :=
  ∃ zs, EncSharedCollection zs out ∧
    (∀ z ∈ zs, IsKShredder I.G k z.1 ∧ ValidCertificate I.G z.1 z.2) ∧
    (k = kappa I.G → ∀ S, IsKShredder I.G (kappa I.G) S → ∀ c ∈ F S,
      ell ≤ 2*(c.L.card : ℤ) → (c.L.card : ℤ) ≤ ell →
      (linkedOnly = true → Linked I.G ell.toNat c ∧
        (c.S.card : ℝ) ≥ 20 * c.L.card * (4 : ℝ)^subpolyExponent I.n) →
      ∀ D, HypRecov.IsCompOf I.G (Finset.univ \ c.L) D →
        3*D.card ≤ 2*c.L.card → ∃ z ∈ zs,
          z.1 = S ∧ LComplete I.G c z.2 ∧ D ∈ z.2.C)

noncomputable def encCollectionInput (I : GraphData) (k : ℕ) (ell : ℤ) : List ℤ :=
  I.encode ++ [(k : ℤ), max 0 (min ell (2*(I.n : ℤ)+1))]

def CollectionAlgorithm (linkedOnly : Bool) : Prop :=
  ∀ a : ℝ, 1 ≤ a → ∃ (P : CongruencyTU.Program) (c : ℕ), NoQueries P ∧
    ∀ eps : ℝ, 0 < eps → ∃ K : ℝ, 0 < K ∧ ∀ (I : GraphData) (k : ℕ) (ell : ℤ),
      I.Valid → kappa I.G ≤ k → k ≤ minDegree I →
      let B := almostLinearBudget K eps I.m
      (∀ coins : Fin B → Bool,
        HaltWithin P CongruencyTU.noOracle (CongruencyTU.extendCoins coins) (encCollectionInput I k ell) B ∧
        WordBound P CongruencyTU.noOracle (CongruencyTU.extendCoins coins)
          (encCollectionInput I k ell) I.n I.m c ∧
        sharedCollectionValid I.G k (CongruencyTU.outputAfter P CongruencyTU.noOracle
          (CongruencyTU.extendCoins coins) (encCollectionInput I k ell) B)) ∧
      ∀ F, TargetChoice I.G F →
        1 - (I.n : ℝ)^(-a) ≤ successFraction P (encCollectionInput I k ell) B
          (collectionComplete linkedOnly I ell k F)

end MaxIsoVertexCuts.Shredders


