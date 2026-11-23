-- Prove2me | Definitions.Def_Formalism_EllipticTorsion_WChordSeries
-- name    : Formalism_EllipticTorsion_WChordSeries
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:56:57.228252+00:00
-- url     : https://prove2.me/theorems/e6f7ee36-5852-4b75-8dc2-c2ebab99affb
-- title:
--   WChord Series
-- statement:
--   Definitions and structural lemmas for WChord Series, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/WChordSeries.lean

import Definitions.Def_Formalism_EllipticTorsion_WSeriesUnique
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
namespace Formalism.ELL
def WEqAt {R : Type u} [CommRing R] (W : WeierstrassCurve R) {σ : Type}
    (s v : MvPowerSeries σ R) : Prop :=
  v = s ^ 3 + W.a₁ • (s * v) + W.a₂ • (s ^ 2 * v) + W.a₃ • v ^ 2 + W.a₄ • (s * v ^ 2)
      + W.a₆ • v ^ 3
def WSubstUnique : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R) (w : PowerSeries R), WFixed W w →
    ∀ (σ : Type) [Finite σ] (s : MvPowerSeries σ R), MvPowerSeries.constantCoeff s = 0 →
      WEqAt W s (w.subst s) ∧
      ∀ v : MvPowerSeries σ R, MvPowerSeries.constantCoeff v = 0 → WEqAt W s v → v = w.subst s
def ChordAt {K : Type u} [Field K] (W : WeierstrassCurve K) (w : PowerSeries K) {σ : Type}
    (s t r : MvPowerSeries σ K) : Prop :=
  let W' := (W.map (algebraMap K (FractionRing (MvPowerSeries σ K)))).toAffine
  let ℓ := (yOf w s - yOf w t) / (xOf w s - xOf w t)
  xOf w r = W'.addX (xOf w s) (xOf w t) ℓ ∧ yOf w r = W'.addY (xOf w s) (xOf w t) (yOf w s) ℓ
def WChordSeries : Prop :=
  ∀ (K : Type u) [Field K] (W : WeierstrassCurve K) (w : PowerSeries K), WFixed W w →
    ∃ F₂ : MvPowerSeries (Fin 2) K,
      (∀ d, MvPowerSeries.coeff d F₂ ∈ Algebra.adjoin ℤ ({W.a₁, W.a₂, W.a₃, W.a₄, W.a₆} : Set K)) ∧
      MvPowerSeries.constantCoeff F₂ = 0 ∧
      MvPowerSeries.coeff (Finsupp.single 0 1) F₂ = 1 ∧ MvPowerSeries.coeff (Finsupp.single 1 1) F₂ = 1 ∧
      ChordAt W w (MvPowerSeries.X 0) (MvPowerSeries.X 1) F₂
def WChordSubst : Prop :=
  ∀ (K : Type u) [Field K] (W : WeierstrassCurve K) (w : PowerSeries K), WFixed W w →
    ∀ F₂ : MvPowerSeries (Fin 2) K, MvPowerSeries.constantCoeff F₂ = 0 →
      ChordAt W w (MvPowerSeries.X 0) (MvPowerSeries.X 1) F₂ →
      ∀ (σ : Type) [Finite σ] (s t : MvPowerSeries σ K),
        MvPowerSeries.constantCoeff s = 0 → MvPowerSeries.constantCoeff t = 0 → s ≠ 0 → t ≠ 0 →
        xOf w s ≠ xOf w t → ChordAt W w s t (MvPowerSeries.subst ![s, t] F₂)
end Formalism.ELL


