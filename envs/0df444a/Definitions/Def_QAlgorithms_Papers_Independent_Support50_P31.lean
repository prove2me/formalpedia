-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Support50_P31
-- name    : QAlgorithms_Papers_Independent_Support50_P31
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-23T21:21:53.093387+00:00
-- url     : https://prove2.me/theorems/6ca907a2-78e6-4e21-9ec3-c3ed4a9c53d2
-- title:
--   Definitions for On some additivity problems in quantum information theory
-- statement:
--   The objects the formalized statements of *On some additivity problems in quantum information theory* (arXiv:math-ph/0003002) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `positiveRealTracePower`: PDF pp.3–4: trace power on positive operators, with the full spectrum.
--   - `pPurity`: PDF p.3: Schatten purity for p at least one, including operator norm at infinity.
--   - `nuP`: PDF p.3, (5): maximum over ALL density inputs. For channels on a nonempty finite space this range is nonempty, bounded, and its supremum is attained.
--   - `nuH`: PDF p.3, (4): minimum output entropy; the same channel and dimension guards make this a nonempty bounded optimization with attainment.
--   - `nuMinus`: PDF p.3, (6): minimum least output eigenvalue INCLUDING zero. Continuous spectral extension at singular outputs, never a support-only inverse.
--   - `maxPower`: PDF p.4: the maximal trace power in the displayed right-limit identity.
--   - `nuFlat`: PDF p.6, (12): maximal survival probability over norm-one vectors.
--   - `weakNoise`: PDF p.7, (14): the actual weak-noise convex mixture.
--   - `depolarizingProduct`: PDF p.10: tensor product of the frozen depolarizing maps on all matrices.
--   - `subsetExpectation`: PDF p.10: replace factors in L by normalized traces, leave the others alone.
--   - `depolarizingSubsetCoefficient`: PDF p.10: membership form of the coefficient in (20); no Nat subtraction.
--   - `zeroRight`: PDF pp.7–11: limit through strictly positive parameters.
--   - `ComparableScale`: PDF p.10: comparable small parameters, without exact rays or equality. All restrictions need hold only eventually near zero from the right.
-- source:
--   On some additivity problems in quantum information theory, arXiv:math-ph/0003002v2, https://arxiv.org/abs/math-ph/0003002v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Hamiltonian
import Definitions.Def_QAlgorithms_Defs_QuditChannelFidelities
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P03
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P38
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P44

/-!
Amosov, Holevo and Werner, arXiv:math-ph/0003002v2, PDF pp.2–12.
Natural entropy units; all density inputs, including entangled ones.
The false minus-infinity branch of (9) and literal quantitative remainder on p.8
are deferred. The final theorem explicitly corrects the scalar-factor edge.
-/

noncomputable section

open Filter Asymptotics
open scoped ComplexConjugate ENNReal

namespace QAlgorithms.Papers.Independent.Support50.P31

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)
open QAlgorithms.Papers.Independent.Information100.P63 (schatten)
open QAlgorithms.Papers.Independent.Gap48.P03 (holevoQuantity)
open QAlgorithms.Papers.Independent.Claimed50.P38 (tensorSuperop)
open QAlgorithms.Papers.Independent.Dependency50.P44 (tensorChannels)

/-- PDF pp.3–4: trace power on positive operators, with the full spectrum. -/
def positiveRealTracePower {I : Type} [Fintype I] [DecidableEq I] (p : ℝ)
    (X : Matrix I I ℂ) : ℝ :=
  (cfc (fun x : ℝ => x ^ p) X).trace.re

/-- PDF p.3: Schatten purity for p at least one, including operator norm at infinity. -/
def pPurity {I : Type} [Fintype I] [DecidableEq I] (p : ℝ≥0∞)
    (X : Matrix I I ℂ) : ℝ :=
  if p = ⊤ then specNorm X else schatten p.toReal X

/-- PDF p.3, (5): maximum over ALL density inputs. For channels on a nonempty
finite space this range is nonempty, bounded, and its supremum is attained. -/
def nuP {I : Type} [Fintype I] [DecidableEq I] (p : ℝ≥0∞)
    (Phi : Superop I I) : ℝ :=
  if p = ⊤ then sSup (Set.range fun X : {X : Matrix I I ℂ // IsDensityMatrix X} => specNorm (Phi X.val))
  else QAlgorithms.Papers.Independent.Gap48.P03.maximumOutputPNorm Phi p.toReal

/-- PDF p.3, (4): minimum output entropy; the same channel and dimension guards
make this a nonempty bounded optimization with attainment. -/
def nuH {I : Type} [Fintype I] [DecidableEq I] (Phi : Superop I I) : ℝ :=
  sInf (Set.range fun X : {X : Matrix I I ℂ // IsDensityMatrix X} => entropy (Phi X.val))

/-- PDF p.3, (6): minimum least output eigenvalue INCLUDING zero.
Continuous spectral extension at singular outputs, never a support-only inverse. -/
def nuMinus {I : Type} [Fintype I] [DecidableEq I] (Phi : Superop I I) : ℝ :=
  sInf (Set.range fun X : {X : Matrix I I ℂ // IsDensityMatrix X} => minEigenvalue (Phi X.val))

/-- PDF p.4: the maximal trace power in the displayed right-limit identity. -/
def maxPower {I : Type} [Fintype I] [DecidableEq I] (p : ℝ)
    (Phi : Superop I I) : ℝ :=
  sSup (Set.range fun X : {X : Matrix I I ℂ // IsDensityMatrix X} => positiveRealTracePower p (Phi X.val))

/-- PDF p.6, (12): maximal survival probability over norm-one vectors. -/
def nuFlat {I : Type} [Fintype I] [DecidableEq I] (Phi : Superop I I) : ℝ :=
  sSup (Set.range fun v : {v : EuclideanSpace ℂ I // ‖v‖ = 1} =>
    effectProb (pureDensity v.val) (Phi (pureDensity v.val)))

/-- PDF p.7, (14): the actual weak-noise convex mixture. -/
def weakNoise {I : Type} (eps : ℝ) (Phi : Superop I I) : Superop I I :=
  fun X => ((1 - eps : ℝ) : ℂ) • X + (eps : ℂ) • Phi X

/-- PDF p.10: tensor product of the frozen depolarizing maps on all matrices. -/
def depolarizingProduct {n : ℕ} (d : Fin n → ℕ) (hd : ∀ i, 0 < d i)
    (p : Fin n → ℝ) :=
  tensorChannels (fun i => QuditFidelity.depolarizingMap (d i) (hd i) (p i))

/-- PDF p.10: replace factors in L by normalized traces, leave the others alone. -/
def subsetExpectation {n : ℕ} (d : Fin n → ℕ) (hd : ∀ i, 0 < d i)
    (L : Finset (Fin n)) :=
  tensorChannels (fun i =>
    if i ∈ L then QuditFidelity.depolarizingMap (d i) (hd i) 1 else id)

/-- PDF p.10: membership form of the coefficient in (20); no Nat subtraction. -/
def depolarizingSubsetCoefficient {n : ℕ} (p : Fin n → ℝ) (L : Finset (Fin n)) : ℝ :=
  ∏ i, if i ∈ L then p i else 1 - p i

/-- PDF pp.7–11: limit through strictly positive parameters. -/
abbrev zeroRight : Filter ℝ := nhdsWithin 0 (Set.Ioi 0)

/-- PDF p.10: comparable small parameters, without exact rays or equality.
All restrictions need hold only eventually near zero from the right. -/
def ComparableScale {n : ℕ} (q : ℝ → Fin n → ℝ) : Prop :=
  ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧
    ∀ᶠ t in zeroRight, ∀ i, 0 < q t i ∧ q t i < 1 ∧ a * t ≤ q t i ∧ q t i ≤ b * t

/-- Sanity: entropy of the scalar density is zero. -/
example : entropy (1 : Matrix (Fin 1) (Fin 1) ℂ) = 0 := by
  simp [entropy, cfc_one]

/-- Sanity: trace power of the scalar density is one. -/
example (p : ℝ) : positiveRealTracePower p (1 : Matrix (Fin 1) (Fin 1) ℂ) = 1 := by
  simp [positiveRealTracePower, cfc_one]

/-- Sanity: infinity selects exactly the L2 operator norm. -/
example {I : Type} [Fintype I] [DecidableEq I] (X : Matrix I I ℂ) :
    pPurity ⊤ X = specNorm X := by
  simp [pPurity]

/-- Sanity: zero noise is the identity map. -/
example {I : Type} (Phi : Superop I I) : weakNoise 0 Phi = id := by
  funext X
  simp [weakNoise]

/-- Sanity: the tensor extension preserves the zero operator. -/
example {n : ℕ} (d : Fin n → ℕ)
    (Phi : (i : Fin n) → Superop (Fin (d i)) (Fin (d i))) :
    tensorChannels Phi 0 = 0 := by
  ext u v
  simp [tensorChannels]

/-- Sanity: the accepted Holevo score of a singleton scalar ensemble is zero. -/
example : QAlgorithms.Papers.Independent.Information100.P56.holevo
    (fun _ : Fin 1 => (1 : ℝ)) (fun _ : Fin 1 => (1 : Matrix (Fin 1) (Fin 1) ℂ)) = 0 := by
  simp [QAlgorithms.Papers.Independent.Information100.P56.holevo,
    QAlgorithms.Papers.Independent.Information100.P56.average, entropy, cfc_one]

/-- Sanity: the empty tensor coefficient is one. -/
example (p : Fin 0 → ℝ) : depolarizingSubsetCoefficient p ∅ = 1 := by
  simp [depolarizingSubsetCoefficient]

/-- Sanity: a constant density output has exactly the specified entropy. -/
example {I : Type} [Fintype I] [DecidableEq I] (rho : Matrix I I ℂ)
    (hrho : IsDensityMatrix rho) : nuH (fun _ => rho) = entropy rho := by
  letI : Nonempty ({X : Matrix I I ℂ // IsDensityMatrix X}) := ⟨⟨rho, hrho⟩⟩
  simp [nuH]

/-- Sanity: zero eigenvalues are retained by a constant-output objective. -/
example {I : Type} [Fintype I] [DecidableEq I] (rho : Matrix I I ℂ)
    (hrho : IsDensityMatrix rho) : nuMinus (fun _ => rho) = minEigenvalue rho := by
  letI : Nonempty ({X : Matrix I I ℂ // IsDensityMatrix X}) := ⟨⟨rho, hrho⟩⟩
  simp [nuMinus]

/-- Sanity: a constant-output map has its output operator norm as its maximum. -/
example {I : Type} [Fintype I] [DecidableEq I] (rho : Matrix I I ℂ)
    (hrho : IsDensityMatrix rho) : nuP ⊤ (fun _ => rho) = specNorm rho := by
  letI : Nonempty ({X : Matrix I I ℂ // IsDensityMatrix X}) := ⟨⟨rho, hrho⟩⟩
  simp [nuP]

/-- Sanity: the trace-power wrapper also preserves constant-output objectives. -/
example {I : Type} [Fintype I] [DecidableEq I] (rho : Matrix I I ℂ)
    (hrho : IsDensityMatrix rho) (p : ℝ) :
    maxPower p (fun _ => rho) = positiveRealTracePower p rho := by
  letI : Nonempty ({X : Matrix I I ℂ // IsDensityMatrix X}) := ⟨⟨rho, hrho⟩⟩
  simp [maxPower]

/-- Sanity: a zero output has zero survival objective on a nonempty unit sphere. -/
example {I : Type} [Fintype I] [DecidableEq I] (v : EuclideanSpace ℂ I)
    (hv : ‖v‖ = 1) : nuFlat (fun _ : Matrix I I ℂ => 0) = 0 := by
  letI : Nonempty {w : EuclideanSpace ℂ I // ‖w‖ = 1} := ⟨⟨v, hv⟩⟩
  simp [nuFlat, effectProb]

/-- Sanity: at unit noise the weak-noise map is exactly the given map. -/
example {I : Type} (Phi : Superop I I) : weakNoise 1 Phi = Phi := by
  funext X
  simp [weakNoise]

end QAlgorithms.Papers.Independent.Support50.P31


