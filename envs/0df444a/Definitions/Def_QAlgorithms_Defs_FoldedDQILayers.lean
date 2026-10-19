-- Prove2me | Definitions.Def_QAlgorithms_Defs_FoldedDQILayers
-- name    : QAlgorithms_Defs_FoldedDQILayers
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:36:04.206802+00:00
-- url     : https://prove2.me/theorems/fdeaaa24-3cfe-44a5-9834-2240c55beca3
-- title:
--   FoldedDQILayers
-- statement:
--   FoldedDQILayers
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\FoldedDQILayers.lean

import Definitions.Def_QAlgorithms_Defs_FoldedOPIData
noncomputable section

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.FoldedDQI

/-- Absolute-trace Fourier matrix over a characteristic-two field;
2610.02145 pp.33–35 (A.14)–(A.25). No cyclic-field transform or
unverified coordinate dotBits is substituted. -/
def traceFourier {F : Type*} [Field F] [Fintype F] [Algebra (ZMod 2) F]
    [FiniteDimensional (ZMod 2) F] (l : ℕ) :
    Matrix (Fin l → F) (Fin l → F) ℂ :=
  Matrix.of fun x y => ((-1 : ℂ)^(Algebra.trace (ZMod 2) F (x ⬝ᵥ y)).val)/
    (Real.sqrt (Fintype.card (Fin l → F)) : ℂ)

/-- Non-unitary local Fourier coefficients, normalized by alphabet size;
2610.02145 pp.33–35 (A.14)–(A.25). -/
def localFourier {F : Type*} [Field F] [Fintype F] [Algebra (ZMod 2) F]
    [FiniteDimensional (ZMod 2) F] {h : ℕ} (A : Finset (Fin h → F)) (eta : Fin h → F) : ℝ :=
  (Fintype.card (Fin h → F) : ℝ)⁻¹*
    ∑ z : Fin h → F, FoldedOPI.localSign A z*
      (-1 : ℝ)^(Algebra.trace (ZMod 2) F (z ⬝ᵥ eta)).val

/-- Computational layer polynomial divided by sqrt(card V);
2610.02145 pp.34–35. Normalization/orthogonality are distance consequences. -/
def layerState {F : Type*} [Field F] [Fintype F] {M h K : ℕ}
    (gamma : F) (A : FoldedOPI.BalancedInstance M (Fin h → F))
    (j : ℕ) (_hj : j ≤ M) : EuclideanSpace ℂ (Fin K → F) :=
  WithLp.toLp 2 fun x =>
    ((Real.sqrt (Fintype.card (Fin K → F))*Real.sqrt (Nat.choose M j))⁻¹ : ℂ)*
      (∑ T ∈ (Finset.univ : Finset (Fin M)).powersetCard j,
        ∏ i ∈ T, FoldedOPI.localSign (A.sets i) (FoldedOPI.encoder M h K gamma x i) : ℝ)

/-- Largest power-of-two window allowed by ell+1 and floor sqrt M;
2610.02145 p.38, Lemma 6. Positive M excludes a zero width. -/
def windowWidth (M ell : ℕ) (_hM : 0 < M) : ℕ :=
  let limit := min (ell+1) ⌊Real.sqrt M⌋₊
  (Finset.range (ell+2)).sup fun k => if 2^k ≤ limit then 2^k else 0

/-- Public equal top-window amplitudes; 2610.02145 p.38 (A.41). -/
def windowWeights (M ell : ℕ) (hM : 0 < M) (j : ℕ) : ℝ :=
  let width := windowWidth M ell hM
  if ell+1-width ≤ j ∧ j ≤ ell then (Real.sqrt width)⁻¹ else 0

/-- Explicit ideal top-window state, without oracle-dependent optimization;
2610.02145 pp.38–40 (A.41),(A.48). -/
def windowState {F : Type*} [Field F] [Fintype F] {M h K : ℕ}
    (hM : 0 < M) (ell : ℕ) (hell : ell ≤ M)
    (gamma : F) (A : FoldedOPI.BalancedInstance M (Fin h → F)) :
    EuclideanSpace ℂ (Fin K → F) :=
  ∑ j : Fin (ell+1), (windowWeights M ell hM j.val : ℂ) •
    layerState gamma A j.val (by omega)

/-- Exact ideal expected score, with empty adjacent sum zero;
2610.02145 p.38 (A.42). This is not the compiled circuit mean. -/
def windowIdealMean (M ell : ℕ) (hM : 0 < M) (_hell : ell ≤ M) : ℝ :=
  let width := windowWidth M ell hM
  1/2+((M : ℝ)*width)⁻¹*∑ j ∈ Finset.Ico (ell+1-width) ell,
    Real.sqrt (((j : ℝ)+1)*((M : ℝ)-j))

example : windowWidth 1 0 (by omega) = 1 := by norm_num [windowWidth,Finset.range_add_one]

example : windowIdealMean 1 0 (by omega) (by omega) = 1/2 := by simp [windowIdealMean,windowWidth,Finset.range_add_one]

example {F : Type*} [Field F] [Fintype F] [Algebra (ZMod 2) F]
    [FiniteDimensional (ZMod 2) F] (x y : Fin 0 → F) : traceFourier 0 x y = 1 := by
  simp [traceFourier]


end QAlgorithms.FoldedDQI


