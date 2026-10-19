-- Prove2me | Definitions.Def_QAlgorithms_Defs_NoisyTannerDecoding
-- name    : QAlgorithms_Defs_NoisyTannerDecoding
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:23:46.162219+00:00
-- url     : https://prove2.me/theorems/8eb139ba-6ac3-4380-bdde-2378dcfd0ae4
-- title:
--   NoisyTannerDecoding
-- statement:
--   NoisyTannerDecoding
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\NoisyTannerDecoding.lean

import Definitions.Def_QAlgorithms_Defs_NoisyTannerData
noncomputable section

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.NoisyTanner

/-- Fixed minimum-weight local syndrome selector; 2306.12470 pp.12–13, Algorithm 1.
An inconsistent local syndrome selects zero. Ties are fixed before the input. -/
structure LocalCorrectionSelector {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    {C : CodeData G} (H : CheckPresentation C) where
  select : (v : {v : G × (Bool × Bool) // v.2.1 ≠ v.2.2}) →
    (Fin H.zCount → ZMod 2) → C.A × C.B → ZMod 2
  lawful : ∀ v s,
    let candidates := {y : C.A × C.B → ZMod 2 | ∀ j, H.zLocal j ⬝ᵥ y = s j}
    (candidates.Nonempty →
      select v s ∈ candidates ∧ ∀ y ∈ candidates, hammingNorm (select v s) ≤ hammingNorm y) ∧
    (¬ candidates.Nonempty → select v s = 0)

/-- Initialized and terminally maximal mismatch execution; 2306.12470 p.13, Algorithm 2.
No residual-correctness condition is built into this relation. -/
def CompleteMismatchRun {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    (C : CodeData G) (eps : ℝ) (Z : G × C.A × C.B → ZMod 2)
    (states : ℕ → SeqDecState (G × C.A × C.B)) (T : ℕ) : Prop :=
  0 < eps ∧ eps < 1 ∧ IsSeqDecRun C.CA C.CB eps Z states T ∧
    ((states T).Z = 0 ∨ ¬ ∃ s', SeqDecStep C.CA C.CB eps (states T) s')

/-- Complete execution relation for the source's decoder; 2306.12470 pp.12–13.
Output uses V01 and C1/R0, correcting the mismatch with frozen seqDecOutput.
Permitted move policies are represented by all complete runs. -/
def sequentialDecoder {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    {C : CodeData G} {H : CheckPresentation C} (selector : LocalCorrectionSelector H)
    (eps : ℝ)
    (input : {v : G × (Bool × Bool) // v.2.1 ≠ v.2.2} × Fin H.zCount → ZMod 2)
    (output : G × C.A × C.B → ZMod 2) : Prop := by
  classical
  let localCorrections := fun v : G × (Bool × Bool) =>
    if hv : v.2.1 ≠ v.2.2 then selector.select ⟨v,hv⟩ (fun j => input (⟨v,hv⟩,j)) else 0
  exact ∃ states T, CompleteMismatchRun C eps (qtMismatch localCorrections) states T ∧
    output = (∑ v ∈ Finset.univ.filter (fun v : G × (Bool × Bool) => v.2 = (false,true)),
      qtPush v (localCorrections v)) + (states T).C true + (states T).R false

/-- Positive denominator domain for decoder constants; 2306.12470 pp.21,24–26. -/
structure ConstantDomain where
  degree : ℕ
  degree_pos : 0 < degree
  kappa : ℝ
  relativeDistance : ℝ
  delta : ℝ
  eps : ℝ
  kappa_pos : 0 < kappa
  relativeDistance_range : 0 < relativeDistance ∧ relativeDistance < 1
  delta_pos : 0 < delta
  separation : 2*delta < eps
  eps_lt : eps < 1

/-- (Aε,Bε,Cδ,c1,c2,βV), computed rather than freely supplied;
2306.12470 pp.21,24–26. All arithmetic is real. -/
def decoderConstants (P : ConstantDomain) : Fin 6 → ℝ :=
  let c1 := (P.eps-2*P.delta)/(P.eps*(1-P.delta))
  let c2 := 2/P.eps
  ![24/(P.kappa*P.degree*(1-P.eps)),
    3*P.degree/(P.kappa*(1-P.eps)),
    P.relativeDistance^2*P.delta^3*P.kappa/(2^12*(P.degree : ℝ)^2),
    c1,c2,(1+2*c2/(P.kappa*c1))*(P.degree : ℝ)^2]

example {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    (C : CodeData G) (eps : ℝ) (heps : 0 < eps ∧ eps < 1) :
    CompleteMismatchRun C eps 0 (fun _ => seqDecInit 0) 0 := by
  refine ⟨heps.1,heps.2,⟨rfl,fun i hi => by omega⟩,Or.inl rfl⟩

end QAlgorithms.NoisyTanner


