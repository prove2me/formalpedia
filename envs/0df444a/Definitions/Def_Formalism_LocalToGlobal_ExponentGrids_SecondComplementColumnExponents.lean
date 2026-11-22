-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ExponentGrids_SecondComplementColumnExponents
-- name    : Formalism_LocalToGlobal_ExponentGrids_SecondComplementColumnExponents
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:07:23.436729+00:00
-- url     : https://prove2.me/theorems/e24283dd-dfbf-4a92-8ba8-dc6f6d370d12
-- title:
--   Second Complement Column Exponents
-- statement:
--   Definitions and structural lemmas for Second Complement Column Exponents, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ExponentGrids/SecondComplementColumnExponents.lean

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_Complement2Normaliser
import Definitions.Def_Formalism_TranslateCocycles_Statement
import Definitions.Def_Formalism_TranslateCocycles_StatementHC
import Definitions.Def_Formalism_TranslateCocycles_StatementNet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain Finset
open Formalism.DivisionValues (vw conjPl lw PlOver IsConjAt)
open Formalism.CG (HCdeg HCDplus HCDminus)
noncomputable section
namespace Formalism.AtG
def NormalisedPlaceValuation : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (g : ℕ) (w : HeightOneSpectrum (𝓞 K)),
    PlOver g w →
    ∃ v : AddValuation K (WithTop ℚ),
      (∀ a : K, a ≠ 0 → v a = (((vw w a : ℚ) / (vw w (g : K) : ℚ) : ℚ) : WithTop ℚ)) ∧
      (∀ a : K, a ≠ 0 →
        v (starRingAut a) = (((vw (conjPl w) a : ℚ) / (vw w (g : K) : ℚ) : ℚ) : WithTop ℚ)) ∧
      v (g : K) = 1
def NormaliserValuationFormula : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (g : ℕ) (T : Type) [Fintype T] (a : T → K),
    (∀ τ, a τ * star (a τ) = (g : K)) → ∀ (D : T → ℕ) (w : HeightOneSpectrum (𝓞 K)), PlOver g w →
      vw w (∏ τ, a τ ^ D τ) + vw (conjPl w) (∏ τ, a τ ^ D τ) = ((∑ τ, D τ : ℕ) : ℤ) * vw w (g : K) ∧
      (vw w (∏ τ, a τ ^ D τ) : ℝ) + (vw (conjPl w) (∏ τ, a τ ^ D τ) : ℝ)
        = ((∑ τ, D τ : ℕ) : ℝ) * (vw w (g : K) : ℝ)
def JetFactorNormaliserImage : Prop :=
  ∀ (K : Type) [Field K] (φ : K →+* ℂ) (T : Type) [Fintype T] [DecidableEq T] (a : T → K)
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (H : E → E → ℂ) (L : E →L[ℂ] E) (g : ℂ),
    (∀ z w, H (L z) (L w) = g * H z w) → ∀ (σ : E → ℂ) (b : E) (n : ℕ),
    ContDiff ℂ n σ → ContDiff ℂ n (fun z => H z (L b)) →
    ∀ (v : Fin n → E) (τ : Fin n → T), (∀ k, L (v k) = φ (a (τ k)) • v k) →
      iteratedFDeriv ℂ n (Formalism.CG.canTranslate (fun z w => g * H z w) b (σ ∘ L)) 0 v =
        φ (∏ τ', a τ' ^ (univ.filter fun k => τ k = τ').card)
          * iteratedFDeriv ℂ n (Formalism.CG.canTranslate H (L b) σ) 0 v ∧
      ∑ τ', (univ.filter fun k => τ k = τ').card = n
def PlaceTwoColourDichotomy : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (g : ℕ) (w : HeightOneSpectrum (𝓞 K)),
    PlOver g w → ∀ a x y : K, a * star a = (g : K) → 0 ≤ vw w x → 0 ≤ vw w y →
    x * a + y * star a = 1 → 0 ≤ vw w a → 0 ≤ vw (conjPl w) a →
      (vw w a = 0 ∧ vw (conjPl w) a = vw w (g : K)) ∨ (vw w a = vw w (g : K) ∧ vw (conjPl w) a = 0)
def QuasiPeriodicityScalar : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (v0 : InfinitePlace K), IsConjAt v0 →
    ∀ (X : Type) (H : X → X → ℂ), (∀ z z', H z' z = starRingEnd ℂ (H z z')) →
    ∀ (t l : X) (α : ℂ) (cg : K), ‖α‖ = 1 →
    v0.embedding cg = α * Complex.exp ((Real.pi : ℂ) * (H t l - H l t) / 2) →
    ∀ w : HeightOneSpectrum (𝓞 K), vw w cg + vw (conjPl w) cg = 0
def NormaliserExponentsExist : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (g : Fin 2 → ℕ), Nat.Coprime (g 0) (g 1) →
    ∀ (J : Type) (nn : J → Fin 2 → K) (cg : Fin 2 → K) (m : ℝ) (DD o : J → ℝ),
    ∃ E F : J → HeightOneSpectrum (𝓞 K) → ℝ,
      (∀ j, (Function.support (E j)).Finite) ∧
      (∀ j i w, PlOver (g i) w →
        E j w = F j w + (vw w (nn j i) : ℝ) - (vw w (cg i) : ℝ) / m + o j * (vw w (g i : K) : ℝ)) ∧
      (∀ j i w, PlOver (g i) w → F j w = -(DD j / 2) * (vw w (g i : K) : ℝ)) ∧
      (∀ j w, (∀ i, ¬ PlOver (g i) w) → E j w = 0)
def PairExponentSumFormula : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (g : ℕ)
    (E F : HeightOneSpectrum (𝓞 K) → ℝ) (nn cg : K) (m Dpi Dp Dm er : ℝ),
    (∀ w, PlOver g w →
      |E w - (F w + (vw w nn : ℝ) - (vw w cg : ℝ) / m)| ≤ er * (vw w (g : K) : ℝ)) →
    (∀ w, PlOver g w → F w = -((Dp + Dm) / 2) * (vw w (g : K) : ℝ)) →
    (∀ w, PlOver g w → vw w cg + vw (conjPl w) cg = 0) →
    (∀ w, PlOver g w → (vw w nn : ℝ) + (vw (conjPl w) nn : ℝ) = Dpi * (vw w (g : K) : ℝ)) →
    ∀ (sa sw k ε1 ε2 : ℝ), |Dpi - (sa + k * sw)| ≤ ε1 → |Dp + Dm - (k - 1) * sw| ≤ ε2 →
    ∀ w, PlOver g w →
      |E w + E (conjPl w) - (Dpi - Dp - Dm) * (vw w (g : K) : ℝ)| ≤ 2 * er * (vw w (g : K) : ℝ) ∧
      |E w + E (conjPl w) - (sa + sw) * (vw w (g : K) : ℝ)|
        ≤ (ε1 + ε2 + 2 * er) * (vw w (g : K) : ℝ)
def ColumnBoundBalanceCondition : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (g : ℕ) (J : Finset ℕ)
    (E F : ℕ → HeightOneSpectrum (𝓞 K) → ℝ) (nn : ℕ → K) (cg : K) (m E0 : ℝ) (Dpi er : ℕ → ℝ)
    (col : HeightOneSpectrum (𝓞 K) → ℝ), (J.card : ℝ) = m → 1 ≤ m →
    (∀ j ∈ J, ∀ w, PlOver g w →
      |E j w - (F j w + (vw w (nn j) : ℝ) - (vw w cg : ℝ) / m)| ≤ er j * (vw w (g : K) : ℝ)) →
    (∀ w, PlOver g w → vw w cg + vw (conjPl w) cg = 0) →
    (∀ j ∈ J, ∀ w, PlOver g w →
      (vw w (nn j) : ℝ) + (vw (conjPl w) (nn j) : ℝ) = Dpi j * (vw w (g : K) : ℝ)) →
    (∀ w, PlOver g w →
      -(∑ j ∈ J, (vw w (nn j) : ℝ)) + (vw w cg : ℝ) - E0 * (vw w (g : K) : ℝ) ≤ col w) →
    ∀ w, PlOver g w →
      |∑ j ∈ J, (F j w - E j w) - (-(∑ j ∈ J, (vw w (nn j) : ℝ)) + (vw w cg : ℝ))|
        ≤ (∑ j ∈ J, er j) * (vw w (g : K) : ℝ) ∧
      ∑ j ∈ J, (F j w - E j w) - (E0 + ∑ j ∈ J, er j) * (vw w (g : K) : ℝ) ≤ col w ∧
      -(∑ j ∈ J, Dpi j) - 2 * E0
        ≤ col w / (vw w (g : K) : ℝ) + col (conjPl w) / (vw w (g : K) : ℝ)
def ColumnErrorLink : Prop :=
  (∀ (K : Type) [Field K] [NumberField K] [StarRing K] (g : ℕ) (J : Finset ℕ)
    (E F : ℕ → HeightOneSpectrum (𝓞 K) → ℝ) (nn : ℕ → K) (cg : K) (m E0 : ℝ) (o : ℕ → ℝ)
    (col : HeightOneSpectrum (𝓞 K) → ℝ), (J.card : ℝ) = m → 1 ≤ m → E0 ≤ ∑ j ∈ J, o j →
    ∀ w, PlOver g w →
    (∀ j ∈ J, F j w + (vw w (nn j) : ℝ) - (vw w cg : ℝ) / m + o j * (vw w (g : K) : ℝ) ≤ E j w) →
    -(∑ j ∈ J, (vw w (nn j) : ℝ)) + (vw w cg : ℝ) - E0 * (vw w (g : K) : ℝ) ≤ col w →
      ∑ j ∈ J, (F j w - E j w) ≤ col w) ∧
  (∀ (J : Finset ℕ) (m C0 f N t η : ℝ), (J.card : ℝ) = m →
    ∑ _j ∈ J, C0 * (f * (N * (N + t) + m ^ 2 * η)) = C0 * (f * (m * N * (N + t) + m ^ 3 * η)))
def KernelValuationLink : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (g : ℕ) (w : HeightOneSpectrum (𝓞 K)), PlOver g w →
    ∀ (Ej Fj kj sh m e1 e2 s o : ℝ) (nn cg : K),
    -(vw w nn : ℝ) - e1 * (vw w (g : K) : ℝ) + sh - e2 * (vw w (g : K) : ℝ) ≤ kj →
    |sh - (vw w cg : ℝ) / m| ≤ s * (vw w (g : K) : ℝ) →
    Fj + (vw w nn : ℝ) - (vw w cg : ℝ) / m + o * (vw w (g : K) : ℝ) ≤ Ej → e1 + e2 + s ≤ o →
      Fj - Ej ≤ kj
def NormaliserPairMeanValuation : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (g : ℕ) (T : Type) [Fintype T] (a : T → K),
    (∀ τ, a τ * star (a τ) = (g : K)) → ∀ (D' : T → ℕ) (Dp Dm : ℝ), ((∑ τ, D' τ : ℕ) : ℝ) = Dp + Dm →
    ∀ F : HeightOneSpectrum (𝓞 K) → ℝ,
    (∀ w, PlOver g w →
      F w = -(((vw w (∏ τ, a τ ^ D' τ) : ℝ) + (vw (conjPl w) (∏ τ, a τ ^ D' τ) : ℝ)) / 2)) →
    ∀ w, PlOver g w →
      F w = -((Dp + Dm) / 2) * (vw w (g : K) : ℝ) ∧ F (conjPl w) = F w ∧
      (vw w (∏ τ, a τ ^ D' τ) : ℝ) / (vw w (g : K) : ℝ)
        + (vw (conjPl w) (∏ τ, a τ ^ D' τ) : ℝ) / (vw w (g : K) : ℝ) = Dp + Dm
def HarishChandraParamConditions {Pl : Type} (TT : Finset Pl) (k t m : ℕ) (u v e bb : Pl → ℕ → ℚ) (a bt : Pl → ℚ)
    (b0 x S η C : ℚ) : Prop :=
  2 ≤ k ∧ 1 ≤ t ∧ (k : ℚ) ≤ S ∧ (k : ℚ) * t ≤ η ∧ 0 ≤ C ∧ 0 ≤ b0 ∧ 2 ≤ x ∧
  (∀ ρ i, 2 ≤ i → i ≤ k → 0 ≤ v ρ i ∧ v ρ i ≤ S) ∧
  (∀ ρ i, 1 ≤ i → i ≤ m → bb ρ i + ((t : ℚ) + 3) / 2 ≤ e ρ i) ∧
  (∀ ρ i, 1 ≤ i → i < m → e ρ i + ((t : ℚ) + 3) / 2 ≤ bb ρ (i + 1)) ∧
  (∀ ρ i j, 1 ≤ i → i ≤ m → 1 ≤ j → j ≤ m → |bb ρ i - e ρ j| ≤ η) ∧
  (∀ ρ, ρ ∉ TT → ∀ i, 1 ≤ i → i ≤ k → -1 ≤ u ρ i ∧ u ρ i ≤ (C + 1) * S) ∧
  (∀ ρ ∈ TT, u ρ 1 = a ρ + ((k : ℚ) - 1) / 2 ∧ u ρ k = -bt ρ - ((k : ℚ) - 1) / 2 ∧ b0 ≤ bt ρ ∧
    (∀ i, 1 < i → i < k → 0 ≤ u ρ i ∧ u ρ i ≤ S) ∧
    ∀ j, 1 ≤ j → j ≤ m → bt ρ + b0 / x ≤ e ρ j ∧ e ρ j ≤ bt ρ + b0 / x + η)
def LiftDegreeFormulas : Prop :=
  ∀ (Pl : Type) (TT : Finset Pl) [DecidablePred (· ∈ TT)] (k t m : ℕ) (u v e bb : Pl → ℕ → ℚ)
    (a bt : Pl → ℚ) (b0 x S η C : ℚ), HarishChandraParamConditions TT k t m u v e bb a bt b0 x S η C →
    ∀ (j : ℕ), 1 ≤ j → j ≤ m → ∀ ρ : Pl,
      |HCdeg k t (u ρ) (e ρ) j - (if ρ ∈ TT then a ρ + ((k : ℚ) - 1) * e ρ j else (k : ℚ) * e ρ j)|
        ≤ (C + 3) * (k * S + m * t * η + (if ρ ∈ TT then b0 / x else 0)) ∧
      |HCDplus k t m j (v ρ) (bb ρ) (e ρ) + HCDminus k t m j (v ρ) (bb ρ) (e ρ)
          - ((k : ℚ) - 1) * e ρ j| ≤ k * S + m * η
def ColumnDegreeDifferenceEstimate : Prop :=
  ∀ (Pl : Type) [Fintype Pl] (TT : Finset Pl) [DecidablePred (· ∈ TT)] (k t m : ℕ)
    (u v e bb : Pl → ℕ → ℚ) (a bt : Pl → ℚ) (b0 x S η C : ℚ),
    HarishChandraParamConditions TT k t m u v e bb a bt b0 x S η C → ∀ (j : ℕ), 1 ≤ j → j ≤ m →
      |((∑ ρ, HCdeg k t (u ρ) (e ρ) j : ℚ) : ℝ)
          - ((∑ ρ, HCDplus k t m j (v ρ) (bb ρ) (e ρ) : ℚ) : ℝ)
          - ((∑ ρ, HCDminus k t m j (v ρ) (bb ρ) (e ρ) : ℚ) : ℝ)
          - ((∑ ρ ∈ TT, (a ρ : ℝ)) + ∑ ρ, if ρ ∈ TT then 0 else (e ρ j : ℝ))|
        ≤ ∑ ρ, ((((C + 3) * (k * S + m * t * η + (if ρ ∈ TT then b0 / x else 0)) : ℚ) : ℝ)
            + ((k * S + m * η : ℚ) : ℝ))
def HarishChandraIntegralityClasses {Pl : Type} (k t m : ℕ) (u e bb : Pl → ℕ → ℚ) : Prop :=
  (∀ ρ i, 1 ≤ i → i < k → u ρ (i + 1) + 1 ≤ u ρ i) ∧ (∀ ρ, -bb ρ 1 + 1 / 2 ≤ u ρ k) ∧
  (∀ ρ i, 1 ≤ i → i ≤ k → ∃ z : ℤ, u ρ i = z + ((k : ℚ) + 1) / 2) ∧
  (∀ ρ i, 1 ≤ i → i ≤ m → ∃ z : ℤ, e ρ i = z + ((k : ℚ) + t + 1) / 2)
def ColumnDegreeNatural : Prop :=
  ∀ (Pl : Type) (TT : Finset Pl) (k t m : ℕ) (u v e bb : Pl → ℕ → ℚ) (a bt : Pl → ℚ)
    (b0 x S η C : ℚ), HarishChandraParamConditions TT k t m u v e bb a bt b0 x S η C → HarishChandraIntegralityClasses k t m u e bb →
    ∀ (j : ℕ), 1 ≤ j → j ≤ m → ∀ ρ : Pl, ∃ n : ℕ, (n : ℚ) = HCdeg k t (u ρ) (e ρ) j
def HarishChandraParamsNonempty : Prop :=
  ∃ (TT : Finset Bool) (u v e bb : Bool → ℕ → ℚ) (a bt : Bool → ℚ) (b0 x S η C : ℚ),
    true ∈ TT ∧ false ∉ TT ∧ 0 < b0 ∧ HarishChandraParamConditions TT 2 1 2 u v e bb a bt b0 x S η C ∧ HarishChandraIntegralityClasses 2 1 2 u e bb
def SecondComplementColumnExponents : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (g : Fin 2 → ℕ),
    (∀ i, 0 < g i) → Nat.Coprime (g 0) (g 1) →
    ∀ (Pl : Type) [Fintype Pl] (TT : Finset Pl) [DecidablePred (· ∈ TT)] (k t m : ℕ)
      (E F : Fin m → HeightOneSpectrum (𝓞 K) → ℝ), (∀ j, (Function.support (E j)).Finite) →

    ∀ (u v e bb : Pl → ℕ → ℚ) (a bt : Pl → ℚ) (b0 x S η C : ℚ),
    HarishChandraParamConditions TT k t m u v e bb a bt b0 x S η C →

    ∀ (p : Fin 2 → Pl → K) (Dx : Fin m → Pl → ℕ),
    (∀ i ρ, p i ρ * star (p i ρ) = (g i : K)) →
    (∀ j ρ, (Dx j ρ : ℚ) = HCdeg k t (u ρ) (e ρ) (j.val + 1)) →

    ∀ (v0 : InfinitePlace K), IsConjAt v0 → ∀ (cg : Fin 2 → K), (∀ i, ‖v0.embedding (cg i)‖ = 1) →
    ∀ (er Eels : Fin m → ℝ) (eps L b B0 f N w'' X'' logd C0 : ℝ),

    (∀ j i w, PlOver (g i) w →
      |E j w - (F j w + (vw w (∏ ρ, p i ρ ^ Dx j ρ) : ℝ) - (vw w (cg i) : ℝ) / (m : ℝ))| ≤
        er j * (vw w (g i : K) : ℝ)) →
    (∀ j i w, PlOver (g i) w →
      F j w = -((((∑ ρ, HCDplus k t m (j.val + 1) (v ρ) (bb ρ) (e ρ) : ℚ) : ℝ)
        + ((∑ ρ, HCDminus k t m (j.val + 1) (v ρ) (bb ρ) (e ρ) : ℚ) : ℝ)) / 2)
          * (vw w (g i : K) : ℝ)) →

    (∀ j, (∑ᶠ (w : HeightOneSpectrum (𝓞 K)) (_ : ∀ i, ¬ PlOver (g i) w), lw w * |E j w|) ≤ Eels j) →

    0 < eps → L = (x : ℝ) ^ eps → 0 ≤ b → B0 = f * m * b * (x : ℝ) ^ eps →
    (Fintype.card Pl : ℝ) ≤ f → 1 ≤ m → 1 ≤ f → 1 ≤ N → 0 ≤ logd →
    (∀ (j : Fin m) ρ, 0 ≤ (e ρ (j.val + 1) : ℝ) ∧ (e ρ (j.val + 1) : ℝ) ≤ 2 * b) →
    (k : ℝ) * S ≤ w'' → (m : ℝ) * ((t : ℝ) + 1) * η ≤ w'' → N * w'' ≤ b → N * (N + t) ≤ b →
    (k : ℝ) * b0 ≤ b → f * k * N * X'' ≤ b → logd ≤ L →
    Real.log ((g 0 : ℝ) * (g 1 : ℝ)) ≤ C0 * L →
    (C : ℝ) + 3 ≤ C0 →
    (∀ j, er j ≤ C0 * (f * (N * (N + t) + (m : ℝ) ^ 2 * η))) →
    (∀ j, Eels j ≤ C0 * B0 + ((TT.card : ℝ) * (2 * b + 4 * k * b0) + 4 * f * k * b0) * logd +
      C0 * (f * k * N * X'')) →
      (∀ j, |2 * (∑ᶠ w : HeightOneSpectrum (𝓞 K), lw w * E j w) -
        (∑ ρ ∈ TT, (a ρ : ℝ)) * Real.log ((g 0 : ℝ) * (g 1 : ℝ))| ≤ (9 * C0 ^ 2 + 6 * C0 + 20) * B0) ∧
      |2 * (∑ j, ∑ᶠ w : HeightOneSpectrum (𝓞 K), lw w * E j w) -
        m * ((∑ ρ ∈ TT, (a ρ : ℝ)) * Real.log ((g 0 : ℝ) * (g 1 : ℝ)))| ≤
        (9 * C0 ^ 2 + 6 * C0 + 20) * (m * B0)
def PlacesOverPrimeWeights : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (g : ℕ), 0 < g →
    ∃ (_ : Fintype {w : HeightOneSpectrum (𝓞 K) // PlOver g w})
      (c : {w : HeightOneSpectrum (𝓞 K) // PlOver g w} → {w : HeightOneSpectrum (𝓞 K) // PlOver g w}),
      Function.Involutive c ∧ (∀ u, (c u).1 = conjPl u.1) ∧
      (∀ u, lw (c u).1 * (vw (c u).1 (g : K) : ℝ) = lw u.1 * (vw u.1 (g : K) : ℝ)) ∧
      (∀ u : {w : HeightOneSpectrum (𝓞 K) // PlOver g w}, 0 < lw u.1 * (vw u.1 (g : K) : ℝ)) ∧
      ∑ u : {w : HeightOneSpectrum (𝓞 K) // PlOver g w}, lw u.1 * (vw u.1 (g : K) : ℝ) = Real.log g ∧
      ∀ X : HeightOneSpectrum (𝓞 K) → ℝ,
        ∑ᶠ (w : HeightOneSpectrum (𝓞 K)) (_ : PlOver g w), lw w * (vw w (g : K) : ℝ) * X w
          = ∑ u : {w : HeightOneSpectrum (𝓞 K) // PlOver g w},
              lw u.1 * (vw u.1 (g : K) : ℝ) * ((X u.1 + X (conjPl u.1)) / 2)
def LeadingTermReturnBound : Prop :=
  ∀ (Pl : Type) [Fintype Pl] [DecidableEq Pl] (TT : Finset Pl) (aT n : Pl → ℝ)
    (m k R1 R2 lg X Q : ℝ), 1 ≤ m → 0 < k → m - 1 ≤ 2 * k → 0 ≤ lg →
    (∀ ρ ∈ TT, |n ρ - aT ρ| ≤ R1) → (∀ ρ, ρ ∉ TT → |n ρ| ≤ R2) → 0 ≤ R2 →
    |X - m * ((∑ ρ ∈ TT, aT ρ) * lg)| ≤ Q →
      |(∑ ρ, n ρ) * (m * (1 + (m - 1) / (2 * k)) * lg) - X
          - m * (m - 1) / (2 * k) * (∑ ρ ∈ TT, aT ρ) * lg|
        ≤ Q + 2 * m * ((TT.card : ℝ) * R1 + (Fintype.card Pl : ℝ) * R2) * lg
end Formalism.AtG


