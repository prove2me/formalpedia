-- Prove2me | Definitions.Def_Formalism_ThickAverageLoss_Statement
-- name    : Formalism_ThickAverageLoss_Statement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:34:50.218588+00:00
-- url     : https://prove2.me/theorems/80053a7d-41cb-4613-a89b-b7a071d3dcfd
-- title:
--   Statement
-- statement:
--   Definitions and structural lemmas for Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThickAverageLoss/Statement.lean

import Definitions.Def_Formalism_WideWeightTheorem_Statement
import Definitions.Def_Formalism_StatementU
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction
noncomputable section
namespace Formalism.D5
open Formalism Formalism.CMTypeGaloisData Formalism.WT Formalism.WeightedSieveThreeParameter
def AvgNarrow {n : ℕ} (w y : Fin n → ℝ) (x : ℝ) : Prop :=
  (∀ j, 0 ≤ w j) ∧ (∑ j, w j) = 1 ∧ ∀ j, 1 ≤ y j ∧ |y j - x| ≤ x ^ ((1 : ℝ) / 2)
def DLVP : Prop :=
  ∃ c K : ℝ, 0 < c ∧ ∀ y : ℝ, 2 ≤ y → |Gz y| ≤ K * y * Real.exp (-(c * Real.sqrt (Real.log y)))
structure SizeParameters where

  b : ℝ

  b1 : ℝ

  w2 : ℝ

  m : ℕ
  k : ℕ
  H : ℕ

  de1 : ℝ
  de2 : ℝ

  R : ℝ

  p0 : ℝ

  kap : ℝ

  Lrd : ℝ

  hc : ℝ
  logc : ℝ

  mthin : ℝ
structure ExplicitFormulaData (C ε x : ℝ) (P : SizeParameters) {nn : ℕ} (w y : Fin nn → ℝ) (d : ℕ)
    (χ : DirichletCharacter ℂ d) where

  ps : ℕ → ℝ
  chps : ℕ → ℝ
  ellPs : ℝ
  ellChPs : ℝ

  nT : ℕ
  β : Fin nT → ℝ
  u : Fin nT → ℝ
  A : Fin nT → ℝ
  g : Fin nT → ℝ → ℝ
  u_mem : ∀ i, P.w2 ≤ u i ∧ u i ≤ 2 * P.b1

  A_mem : ∀ i, x * P.b ≤ A i ∧ A i ≤ 2 * (x * P.b)
  mass : (∑ i, |β i|) ≤ P.mthin

  box : ∀ i, g i = Gz ∨ ∀ Y : ℝ, x * P.b / (2 * P.b1) ≤ Y →
    |g i Y| ≤ C * Y * (Y ^ (-(1 : ℝ) / 20) * x ^ (P.hc + ε) + x ^ (-P.hc) * P.logc ^ 6
      + Real.exp (-(x ^ (ε / C)) / C))

  copy : ℝ
  frame : ℝ
  lev : ℝ
  phic : ℝ
  serv : ℝ
  iv : ℝ
  ram : ℝ
  thinPl : ℝ
  divMain : ℝ
  nTot : ℝ
  Ld : Finset ℕ
  len : ℕ → ℝ

  ineq : P.de2 / 2 * (gavg w y Gz + gavg w y (Gch ps ellPs) - gavg w y (GJ d χ)
        - gavg w y (Gch chps ellChPs))
      + (∑ i, β i * (u i / P.b) * g i (A i / u i))
      ≤ copy + frame + lev + phic + serv + iv + ram + thinPl
        + P.de2 / P.de1 * (divMain + P.m * nTot + P.m * (∑ l ∈ Ld, Real.log l * len l)) / (P.m * P.b)

  frame_S : frame ≤ C * x ^ ε * (x / P.m)

  copy_G : copy ≤ C * x ^ ε * (x / P.m)

  lev_G : lev ≤ C * x ^ ε * (x * P.m / P.k)

  phic_G : phic ≤ C * x ^ ε * (x / P.H)

  serv_G : serv ≤ C * x ^ ε * (x / P.k + 1 + x / P.p0 ^ 2 + P.m * P.kap * x)

  iv_G : iv ≤ C * x ^ ((1 : ℝ) / 2 + ε)

  ram_G : ram ≤ C * x ^ ε * (1 + P.logc)

  thinPl_DIV : thinPl ≤ C * x ^ ε * (2 * P.k * P.b1 * P.Lrd / (P.de1 * P.b))

  div_DIV : divMain ≤ C * x ^ ε * (P.m : ℝ) ^ 2 * P.b

  N_tot : nTot ≤ C * x ^ ε * P.m * P.b

  N_d : ∀ l ∈ Ld, 0 ≤ len l ∧ len l ≤ C * x ^ ε * P.k * P.b / (l : ℝ) ^ 2

  phi_i : ∀ l ∈ Ld, P.R < l
  phi_ii : (∑ l ∈ Ld, Real.log l / (l : ℝ) ^ 2) ≤ x ^ ε / (P.H * P.R)
def SizeConditions (ε K x : ℝ) (P : SizeParameters) : Prop :=
  0 < P.b ∧ 0 < P.b1 ∧ 0 < P.w2 ∧ 0 < P.m ∧ 0 < P.k ∧ 0 < P.H ∧ 0 < P.de1 ∧ 0 < P.R ∧ 0 < P.p0 ∧
  0 ≤ P.kap ∧ 0 ≤ P.Lrd ∧ 0 ≤ P.logc ∧ 0 ≤ P.mthin ∧
  x ^ (-ε) ≤ P.de2 ∧
  x ≤ K * x ^ ((1 : ℝ) / 2 + ε) * P.m ∧
  x * P.m ≤ K * x ^ ((1 : ℝ) / 2 + ε) * P.k ∧
  P.m * P.de2 ≤ K * x ^ ((1 : ℝ) / 2 + ε) * P.de1 ∧
  x ≤ K * x ^ ((1 : ℝ) / 2 + ε) * P.H ∧
  P.k * P.de2 ≤ K * x ^ ((1 : ℝ) / 2 + ε) * P.de1 * P.H * P.R ∧
  x ≤ K * x ^ ((1 : ℝ) / 2 + ε) * P.k ∧
  x ≤ K * x ^ ((1 : ℝ) / 2 + ε) * P.p0 ^ 2 ∧
  P.m * P.kap * x ≤ K * x ^ ((1 : ℝ) / 2 + ε) ∧
  P.k * P.b1 * P.Lrd ≤ K * x ^ ((1 : ℝ) / 2 + ε) * P.de1 * P.b ∧
  Real.exp (x ^ (ε / K)) ≤ x * P.b / P.b1 ∧
  2 ≤ P.hc ∧ P.hc ≤ K ∧ P.logc ≤ x ^ ε ∧
  P.mthin ≤ K * x ^ K ∧ P.mthin * x * x ^ (-P.hc) * P.logc ^ 6 ≤ K
def EstimateImpliesRHDirichlet : Prop :=
  DLVP →
  (∀ ε : ℝ, 0 < ε → ∃ C K x₀ : ℝ, 0 ≤ C ∧ ∀ x : ℝ, x₀ ≤ x →
    ∃ (P : SizeParameters) (d : ℕ) (χ : DirichletCharacter ℂ d) (nn : ℕ) (w y : Fin nn → ℝ),
      SizeConditions ε K x P ∧ AvgNarrow w y x ∧ d % 4 = 3 ∧
      (∀ n : ℕ, χ (n : ZMod d) = ((jacobiSym (n : ℤ) d : ℤ) : ℂ)) ∧
      ∃ large₂ : ExplicitFormulaData C ε x P w y d χ,
        -(C * x ^ ((1 : ℝ) / 2 + ε)) ≤ gavg w y (Gch large₂.ps large₂.ellPs) ∧
        gavg w y (GJ d χ) ≤ C * x ^ ((1 : ℝ) / 2 + ε) ∧
        gavg w y (Gch large₂.chps large₂.ellChPs) ≤ C * x ^ ((1 : ℝ) / 2 + ε)) →
  RiemannHypothesis
def chiTw (d q1 n : ℕ) : ℝ := ((jacobiSym (n : ℤ) d * jacobiSym (n : ℤ) q1 : ℤ) : ℝ)
def IsJacTwFamily (S : Finset ℕ) (q1 : ℕ) (χψ : (d : ℕ) → DirichletCharacter ℂ (d * q1)) : Prop :=
  ∀ d ∈ S, ∀ n : ℕ, χψ d (n : ZMod (d * q1)) = ((jacobiSym (n : ℤ) d * jacobiSym (n : ℤ) q1 : ℤ) : ℂ)
def WeightCorEx3Psi : Prop :=
  ∃ Cs : ℝ, ∀ C0 : ℝ, Cs ≤ C0 → ∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ (D z : ℝ) (M r q1 : ℕ),
    Par3 C0 x z D → WParams D M r → q1.Prime → q1 ∣ M → q1 % 4 = 3 →
    ∀ χ : (d : ℕ) → DirichletCharacter ℂ d, IsJacFamily (DD D z M r) χ →
    ∀ χψ : (d : ℕ) → DirichletCharacter ℂ (d * q1), IsJacTwFamily (DD D z M r) q1 χψ →
    ∀ (n : ℕ) (w y : Fin n → ℝ), AvgCondition w y z → ∀ (Ex : Finset ℕ) (E κ : ℝ),
      Ex ⊆ DD D z M r → (Ex.card : ℝ) ≤ κ * (DD D z M r).card → 0 ≤ E →
      (∀ d ∈ DD D z M r \ Ex, gavg w y Gz - gavg w y (GJ d (χ d))
          - gavg w y (Gch (chiTw d q1) (ell (χψ d))) ≤ E) →
        gavg w y Gz ≤ E + C * (∑ j, w j * (Real.log (2 * y j) + y j / x ^ 2))
          + C * κ * (∑ j, w j * y j) * Real.log D ^ 2
def EstimateImpliesRHWeighted : Prop :=
  DLVP → ∃ Cs : ℝ, ∀ C0 : ℝ, Cs ≤ C0 →
  (∀ ε : ℝ, 0 < ε → ∃ C K x₀ : ℝ, 0 ≤ C ∧ ∀ x : ℝ, x₀ ≤ x →
    ∃ (P : SizeParameters) (D z : ℝ) (M r q1 : ℕ) (χ : (d : ℕ) → DirichletCharacter ℂ d)
      (χψ : (d : ℕ) → DirichletCharacter ℂ (d * q1)) (ellPs : ℝ) (Ex : Finset ℕ) (κw : ℝ)
      (nn : ℕ) (w y : Fin nn → ℝ),
      SizeConditions ε K x P ∧ Par3 C0 x z D ∧ WParams D M r ∧ q1.Prime ∧ q1 ∣ M ∧ q1 % 4 = 3 ∧
      Real.log D ≤ x ^ ε ∧ IsJacFamily (DD D z M r) χ ∧ IsJacTwFamily (DD D z M r) q1 χψ ∧
      Ex ⊆ DD D z M r ∧ (Ex.card : ℝ) ≤ κw * (DD D z M r).card ∧ (DD D z M r \ Ex).Nonempty ∧
      κw * x * Real.log D ^ 2 ≤ K * x ^ ((1 : ℝ) / 2 + ε) ∧ AvgNarrow w y x ∧
      -(C * x ^ ((1 : ℝ) / 2 + ε)) ≤ gavg w y (Gch (fun n : ℕ => ((jacobiSym (n : ℤ) q1 : ℤ) : ℝ)) ellPs) ∧
      ∀ d ∈ DD D z M r \ Ex, ∃ large₂ : ExplicitFormulaData C ε x P w y d (χ d),
        large₂.ps = (fun n : ℕ => ((jacobiSym (n : ℤ) q1 : ℤ) : ℝ)) ∧ large₂.ellPs = ellPs ∧
        large₂.chps = chiTw d q1 ∧ large₂.ellChPs = ell (χψ d)) →
  RiemannHypothesis
abbrev DirichletExplicitFormulaParameters := @ExplicitFormulaData
end Formalism.D5


