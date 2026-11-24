-- Prove2me | Definitions.Def_Formalism_PieriBlockIdeals_TailInequalityEventually
-- name    : Formalism_PieriBlockIdeals_TailInequalityEventually
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T15:19:53.572836+00:00
-- url     : https://prove2.me/theorems/e1fc6619-dba4-4b26-a431-d31ff20b0033
-- title:
--   Tail Inequality Eventually
-- statement:
--   Definitions and structural lemmas for Tail Inequality Eventually, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/TailInequalityEventually.lean

import Definitions.Def_Formalism_PieriBlockIdeals_MertensReciprocalElementary
import Definitions.Def_Formalism_PieriBlockIdeals_HidaLatticeInclusionAtCoarseWeightBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
namespace Formalism.CohomologicalDescent.LargeParameterEstimates
open Classical
open Formalism.CohomologicalDescent.LogSmallConstantBounds
structure Rows (P : Par) (X' A : ℝ) : Prop where
  b'_eq : P.b' = P.x * P.b / X'
  sum_le : X' * (P.S + P.η) ≤ P.b
  kS_le : (P.k : ℝ) * P.S ≤ P.w''
  S_ge : 1 ≤ P.S
  m_ge : 2 ≤ P.m
  f_eq : P.f = 2 * P.n
  f_le : P.f ≤ P.k
  t_le : (P.t : ℝ) ≤ A
  N_le : P.N ≤ A * P.x
structure Big (L x X' A : ℝ) : Prop where
  x_ge : 5 ≤ x
  L_ge : 4 ≤ L
  X1 : 4 * (L + 2) ≤ X'
  X2 : 5.2 * A ^ 3 * x ≤ X'
  X3 : 40 * A ^ 7 * x ^ 2 * L ≤ X'
  b3 : 40 * A ^ 7 * x ^ 2 * L ^ 3 ≤ Real.exp L
def BigEv : Prop :=
  ∀ ε C : ℝ, 0 < ε → ∃ x0 : ℝ, ∀ x : ℝ, x0 ≤ x →
    Big (x ^ ε) x (Real.exp (x ^ (ε / 3))) (x ^ C)
def KmaxSize : Prop :=
  ∀ (P : Par) (X' A : ℝ), P.Hyp → Rows P X' A → Big P.L P.x X' A →
    (P.kmax : ℝ) ≤ 2 * P.b / P.lstar ∧
    2 * P.b / P.lstar =
      2 * ((P.n : ℝ) * (P.t : ℝ) ^ 2 * (P.N + (P.t : ℝ)) * P.L ^ 2
        + (P.k : ℝ) * (P.n : ℝ) ^ 2 * (P.S + (P.t : ℝ) + P.L)) / (P.m : ℝ) ∧
    2 * P.b / P.lstar ≤ 4 * A ^ 4 * P.x * P.L ^ 2 + 2 * A ^ 3 * (P.S + (P.t : ℝ) + P.L) ∧
    2 * P.b / P.lstar + (P.t : ℝ) ≤ A ^ 4 * P.x ^ 2 * (P.L ^ 2 + P.S) ∧
    (P.kmax : ℝ) + (P.t : ℝ) ≤ A ^ 4 * P.x ^ 2 * (P.L ^ 2 + P.S)
def Small1 : Prop :=
  ∀ (P : Par) (X' A : ℝ) (T : ℕ), P.Hyp → Rows P X' A → Big P.L P.x X' A → T ≤ P.f →
    (P.k : ℝ) * (P.S + 1) ≤ 2 * (P.k : ℝ) * P.S ∧ 2 * (P.k : ℝ) * P.S ≤ 2 * P.w'' ∧
    2 * P.w'' = 2 * P.b / ((P.n : ℝ) * X') ∧
    (T : ℝ) * (2 * (P.k : ℝ) * (P.S + 1) * (P.L + 2)) ≤ 8 * (P.L + 2) * P.b / X' ∧
    8 * (P.L + 2) * P.b / X' ≤ 2 * P.b
def Small2 : Prop :=
  ∀ (P : Par) (X' A : ℝ), P.Hyp → Rows P X' A → Big P.L P.x X' A →
    1.3 * (P.f : ℝ) * (P.Nr : ℝ) ^ 2 * P.b' ≤ 5.2 * (P.f : ℝ) * (P.t : ℝ) ^ 2 * P.b' ∧
    5.2 * (P.f : ℝ) * (P.t : ℝ) ^ 2 * P.b' ≤ 5.2 * A ^ 3 * P.x * P.b / X' ∧
    5.2 * A ^ 3 * P.x * P.b / X' ≤ P.b
def Small3 : Prop :=
  ∀ (P : Par) (X' A : ℝ), P.Hyp → Rows P X' A → Big P.L P.x X' A →
    P.S + P.η ≤ P.b / X' ∧
    P.S + P.η + (P.t : ℝ) + 2 * (P.kmax : ℝ) + 6 ≤ 5 * A ^ 4 * P.x ^ 2 * (P.L ^ 2 + P.b / X') ∧
    (P.f : ℝ) * (P.Nr : ℝ) ^ 2 * P.L ≤ 4 * A ^ 3 * P.L ∧
    (P.S + P.η + (P.t : ℝ) + 2 * (P.kmax : ℝ) + 6) * (P.f : ℝ) * (P.Nr : ℝ) ^ 2 * P.L ≤
      20 * A ^ 7 * P.x ^ 2 * P.L * (P.L ^ 2 + P.b / X') ∧
    20 * A ^ 7 * P.x ^ 2 * P.L * (P.L ^ 2 + P.b / X') ≤ P.b
def SmallSum : Prop :=
  ∀ (P : Par) (X' A : ℝ) (T : ℕ), P.Hyp → Rows P X' A → Big P.L P.x X' A → T ≤ P.f →
    (T : ℝ) * (2 * (P.k : ℝ) * (P.S + 1) * (P.L + 2)) + 1.3 * (P.f : ℝ) * (P.Nr : ℝ) ^ 2 * P.b'
      + (P.S + P.η + (P.t : ℝ) + 2 * (P.kmax : ℝ) + 6) * (P.f : ℝ) * (P.Nr : ℝ) ^ 2 * P.L ≤ 4 * P.b ∧
    4 * P.b ≤ 2 * (P.m : ℝ) * P.b
def TailInequalitySum : Prop :=
  ∀ (P : Par) (X' A : ℝ) (T : ℕ), P.Hyp → Rows P X' A → Big P.L P.x X' A → T ≤ P.f →
    totalBound P T (30 * (P.m : ℝ) * P.b * P.L ^ 2) ≤
      30 * (T : ℝ) * (P.m : ℝ) * P.b * P.L ^ 2 + 2 * (P.m : ℝ) * P.b
def TailInequalityEventually : Prop :=
  ∀ ε C : ℝ, 0 < ε → ∃ x0 : ℝ, ∀ P : Par, P.Hyp → x0 ≤ P.x → P.L = P.x ^ ε →
    Rows P (Real.exp (P.x ^ (ε / 3))) (P.x ^ C) → ∀ T : ℕ, T ≤ P.f →
    totalBound P T (30 * (P.m : ℝ) * P.b * P.x ^ (2 * ε)) ≤
      30 * (T : ℝ) * (P.m : ℝ) * P.b * P.x ^ (2 * ε) + 2 * (P.m : ℝ) * P.b
def Corollary8Tail : Prop :=
  PrimeCountingBound → ∀ (P : Par) (X' A : ℝ), P.Hyp → P.Large → Rows P X' A → Big P.L P.x X' A →
    ∀ (ι : Type) [Fintype ι] (D : SizeData₂ ι), D.Inputs P → Places D P →
    ∀ Q : Finset ℕ, (∀ l ∈ Q, l.Prime) →
      ∑ l ∈ Q, (D.J l : ℝ) * Real.log (l : ℝ) ≤
        30 * (D.T2.card : ℝ) * (P.m : ℝ) * P.b * P.L ^ 2 + 2 * (P.m : ℝ) * P.b
section Real7
open TensorProduct MvPolynomial
open Formalism.UG Formalism.RankGapBounds.FormsTensorLocalization Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LD Formalism.CohomologicalDescent.UnitNormBounds Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.ShortWeightBounds
def CorollaryOfRecord7Tail : Prop :=
  LA.LemmaAZ → PrimeCountingBound → ∀ (P : Par) (X' A : ℝ), P.Hyp → P.Large → Rows P X' A → Big P.L P.x X' A →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (W : Wts ι), W.Ok P → Fintype.card ι = P.f →
    W.Sp.card ≤ 5 →
    ∀ X : ℕ → HidaSetting ι P.Nr W.lam, (∀ l : ℕ, l.Prime → ¬ IsUnit ((l : ℕ) : (X l).O)) →
    (∀ l : ℕ, l.Prime → W.WRange P l → (X l).WInputs l (kc P) W.j W.T2 (W.iW P l)) →
    (∀ l : ℕ, l.Prime → (X l).Incl l (W.Jrec7 P l) ∧ (X l).Incl l ((X l).Jmin l) ∧
      (X l).Jmin l ≤ W.Jrec7 P l) ∧
    ∀ Q : Finset ℕ, (∀ l ∈ Q, l.Prime) →
      ∑ l ∈ Q, (W.Jrec7 P l : ℝ) * Real.log (l : ℝ) ≤
          30 * (W.T2.card : ℝ) * (P.m : ℝ) * P.b * P.L ^ 2 + 2 * (P.m : ℝ) * P.b ∧
      ∑ l ∈ Q, ((X l).Jmin l : ℝ) * Real.log (l : ℝ) ≤
          30 * (W.T2.card : ℝ) * (P.m : ℝ) * P.b * P.L ^ 2 + 2 * (P.m : ℝ) * P.b
end Real7
def LargeOfRows : Prop :=
  ∀ (P : Par) (X' A : ℝ), P.Hyp → Rows P X' A → Big P.L P.x X' A →
    P.b ^ ((4 : ℝ) / 5) ≤ P.w'' / P.S → 4 * A ^ 4 * P.x ^ 2 * P.L ^ 2 < P.b ^ ((4 : ℝ) / 5) → P.Large
def BigEv2 : Prop :=
  ∀ ε C : ℝ, 0 < ε → ∃ x0 : ℝ, ∀ x : ℝ, x0 ≤ x →
    4 * (x ^ C) ^ 4 * x ^ 2 * (x ^ ε) ^ 2 < Real.exp (x ^ ε) ^ ((4 : ℝ) / 5)
def Corollary8Ev : Prop :=
  PrimeCountingBound → ∀ ε C : ℝ, 0 < ε → ∃ x0 : ℝ, ∀ P : Par, P.Hyp → x0 ≤ P.x → P.L = P.x ^ ε →
    Rows P (Real.exp (P.x ^ (ε / 3))) (P.x ^ C) → P.b ^ ((4 : ℝ) / 5) ≤ P.w'' / P.S →
    ∀ (ι : Type) [Fintype ι] (D : SizeData₂ ι), D.Inputs P → Places D P →
    ∀ Q : Finset ℕ, (∀ l ∈ Q, l.Prime) →
      ∑ l ∈ Q, (D.J l : ℝ) * Real.log (l : ℝ) ≤
        30 * (D.T2.card : ℝ) * (P.m : ℝ) * P.b * P.x ^ (2 * ε) + 2 * (P.m : ℝ) * P.b
section Real7Ev
open TensorProduct MvPolynomial
open Formalism.UG Formalism.RankGapBounds.FormsTensorLocalization Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LD Formalism.CohomologicalDescent.UnitNormBounds Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.ShortWeightBounds
def CorollaryOfRecord7Ev : Prop :=
  LA.LemmaAZ → PrimeCountingBound → ∀ ε C : ℝ, 0 < ε → ∃ x0 : ℝ, ∀ P : Par, P.Hyp → x0 ≤ P.x → P.L = P.x ^ ε →
    Rows P (Real.exp (P.x ^ (ε / 3))) (P.x ^ C) → P.b ^ ((4 : ℝ) / 5) ≤ P.w'' / P.S →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (W : Wts ι), W.Ok P → Fintype.card ι = P.f →
    W.Sp.card ≤ 5 →
    ∀ X : ℕ → HidaSetting ι P.Nr W.lam, (∀ l : ℕ, l.Prime → ¬ IsUnit ((l : ℕ) : (X l).O)) →
    (∀ l : ℕ, l.Prime → W.WRange P l → (X l).WInputs l (kc P) W.j W.T2 (W.iW P l)) →
    (∀ l : ℕ, l.Prime → (X l).Incl l (W.Jrec7 P l) ∧ (X l).Incl l ((X l).Jmin l) ∧
      (X l).Jmin l ≤ W.Jrec7 P l) ∧
    ∀ Q : Finset ℕ, (∀ l ∈ Q, l.Prime) →
      ∑ l ∈ Q, (W.Jrec7 P l : ℝ) * Real.log (l : ℝ) ≤
          30 * (W.T2.card : ℝ) * (P.m : ℝ) * P.b * P.x ^ (2 * ε) + 2 * (P.m : ℝ) * P.b ∧
      ∑ l ∈ Q, ((X l).Jmin l : ℝ) * Real.log (l : ℝ) ≤
          30 * (W.T2.card : ℝ) * (P.m : ℝ) * P.b * P.x ^ (2 * ε) + 2 * (P.m : ℝ) * P.b
end Real7Ev
end Formalism.CohomologicalDescent.LargeParameterEstimates


