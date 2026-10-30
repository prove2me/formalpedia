-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P36
-- name    : QAlgorithms_Papers_Independent_Advance50_P36
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T13:51:22.913424+00:00
-- url     : https://prove2.me/theorems/78a249c1-8a05-4075-b065-0ef991737962
-- title:
--   Definitions for Error free Quantum Reading by Quasi Bell State of Entangled Coherent States
-- statement:
--   The objects the formalized statements of *Error free Quantum Reading by Quasi Bell State of Entangled Coherent States* (arXiv:1108.4163) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `antipodalOverlap`: PDF pp.2-3, Eqs.(5),(13): the real antipodal coherent overlap, not a free Gram parameter. Its identification with an actual inner product is a theorem.
--   - `quasiBellNormalization`: PDF p.2, Eq.(5): h1=h3 and h2=h4. Labels 0,1,2,3 denote Psi1,...,Psi4. At alpha=0 the odd normalization is totalized to zero by real division; all assertions concerning odd states explicitly exclude this input.
--   - `quasiBellState`: PDF p.2, Eq.(5): the four finite superpositions on full two-mode Fock space, in printed order. Coherent factors have their canonical number-basis phase convention. Normalization is a conclusion, never an input assumption.
--   - `QuasiBellCoherentRealized`: PDF p.2, Eq.(5): realization of exactly the four product coherent factors used in the construction. This conclusion rules out the accepted coherentWord selection's zero fallback and asserts their canonical coefficients and norms.
--   - `modeBPhaseShift`: PDF pp.2-3, Eqs.(8),(14): I_A tensor exp(-i theta N_B), constructed coefficientwise on the full Hilbert space. The missing i in printed Eq.(8) is corrected as required by Eqs.(12),(15). The modulus-one multiplier preserves square summability; no number-operator domain or choice fallback is needed.
--   - `HasFinitePhotonEnergy`: PDF p.3, §V: finite mean photon number in every mode, in photon-number units. Summability of the actual occupation weights excludes divergent-tsum defaults. This predicate does not assert normalization or energy matching.
--   - `coherentReadingError`: PDF p.3, Eq.(18), coherent row: its numerical value for priors p,1-p. Only p in [0,1] is used in the performance theorem.
-- source:
--   Error free Quantum Reading by Quasi Bell State of Entangled Coherent States, arXiv:1108.4163v2, https://arxiv.org/abs/1108.4163v2

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P21

/-!
Statements from arXiv:1108.4163v2. The oscillator basis is the complete set of
occupation tuples, with mode 0 = A and mode 1 = B. The independently accepted
coherent-word and binary-POVM interfaces are reused. Eq.(8) is corrected by
inserting i; Eq.(17) is restricted to one phase period. The undefined universal
classical-transmitter claim is deferred in HARD.md. Compilation is pending.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P36

open QAlgorithms.Papers.Independent.Frontier30.P21
  (WordFock coherentWord CoherentWordRealized binaryErrorValues)

open scoped Matrix

attribute [local instance] Classical.propDecidable

/-- PDF pp.2-3, Eqs.(5),(13): the real antipodal coherent overlap, not a free
Gram parameter. Its identification with an actual inner product is a theorem. -/
def antipodalOverlap (alpha : ℂ) : ℝ :=
  Real.exp (-2 * Complex.normSq alpha)

/-- PDF p.2, Eq.(5): h1=h3 and h2=h4. Labels 0,1,2,3 denote Psi1,...,Psi4.
At alpha=0 the odd normalization is totalized to zero by real division;
all assertions concerning odd states explicitly exclude this input. -/
def quasiBellNormalization (alpha : ℂ) (i : Fin 4) : ℝ :=
  if i = 0 ∨ i = 2 then
    1 / Real.sqrt (2 * (1 + antipodalOverlap alpha ^ 2))
  else
    1 / Real.sqrt (2 * (1 - antipodalOverlap alpha ^ 2))

/-- PDF p.2, Eq.(5): the four finite superpositions on full two-mode Fock
space, in printed order. Coherent factors have their canonical number-basis
phase convention. Normalization is a conclusion, never an input assumption. -/
def quasiBellState (alpha : ℂ) (i : Fin 4) : WordFock 2 :=
  (quasiBellNormalization alpha i : ℂ) •
    (![coherentWord ![alpha, alpha] + coherentWord ![-alpha, -alpha],
       coherentWord ![alpha, alpha] - coherentWord ![-alpha, -alpha],
       coherentWord ![alpha, -alpha] + coherentWord ![-alpha, alpha],
       coherentWord ![alpha, -alpha] - coherentWord ![-alpha, alpha]] i)

/-- PDF p.2, Eq.(5): realization of exactly the four product coherent factors
used in the construction. This conclusion rules out the accepted coherentWord
selection's zero fallback and asserts their canonical coefficients and norms. -/
def QuasiBellCoherentRealized (alpha : ℂ) : Prop :=
  CoherentWordRealized ![alpha, alpha] ∧
  CoherentWordRealized ![-alpha, -alpha] ∧
  CoherentWordRealized ![alpha, -alpha] ∧
  CoherentWordRealized ![-alpha, alpha]

/-- PDF pp.2-3, Eqs.(8),(14): I_A tensor exp(-i theta N_B), constructed
coefficientwise on the full Hilbert space. The missing i in printed Eq.(8)
is corrected as required by Eqs.(12),(15). The modulus-one multiplier preserves
square summability; no number-operator domain or choice fallback is needed. -/
def modeBPhaseShift (theta : ℝ) (u : WordFock 2) : WordFock 2 :=
  ⟨fun k => Complex.exp (Complex.ofReal (-theta * (k 1 : ℝ)) * Complex.I) * u k, by
    apply (lp.memℓp u).mono'
    intro k
    simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, le_refl]⟩

/-- PDF p.3, §V: finite mean photon number in every mode, in photon-number
units. Summability of the actual occupation weights excludes divergent-tsum
defaults. This predicate does not assert normalization or energy matching. -/
def HasFinitePhotonEnergy {L : ℕ} (u : WordFock L) : Prop :=
  ∀ j : Fin L, Summable (fun k : Fin L → ℕ => (k j : ℝ) * Complex.normSq (u k))

/-- PDF p.3, Eq.(18), coherent row: its numerical value for priors p,1-p.
Only p in [0,1] is used in the performance theorem. -/
def coherentReadingError (alpha : ℂ) (p : ℝ) : ℝ :=
  (1 - Real.sqrt (1 - 4 * p * (1 - p) * Real.exp (-4 * Complex.normSq alpha))) / 2

/-- Sanity check: vacuum has antipodal overlap one. -/
example : antipodalOverlap 0 = 1 := by
  simp [antipodalOverlap]

/-- Sanity check: Psi4 uses the same odd normalization as Psi2. -/
example (alpha : ℂ) :
    quasiBellNormalization alpha 3 = quasiBellNormalization alpha 1 := by
  have h3 : ¬ ((3 : Fin 4) = 0 ∨ (3 : Fin 4) = 2) := by decide
  have h1 : ¬ ((1 : Fin 4) = 0 ∨ (1 : Fin 4) = 2) := by decide
  simp only [quasiBellNormalization, if_neg h3, if_neg h1]

/-- Sanity check: the excluded zero-amplitude odd normalization is zero. -/
example : quasiBellNormalization 0 1 = 0 := by
  have h1 : ¬ ((1 : Fin 4) = 0 ∨ (1 : Fin 4) = 2) := by decide
  simp only [quasiBellNormalization, if_neg h1]
  norm_num [antipodalOverlap]

/-- Sanity check: the fourth vector has the minus sign in the printed order. -/
example (alpha : ℂ) : quasiBellState alpha 3 =
    (quasiBellNormalization alpha 3 : ℂ) •
      (coherentWord ![alpha, -alpha] - coherentWord ![-alpha, alpha]) := by
  simp [quasiBellState]

/-- Sanity check: zero phase is identity on every Hilbert vector. -/
example (u : WordFock 2) : modeBPhaseShift 0 u = u := by
  apply lp.ext
  funext k
  simp [modeBPhaseShift]

/-- Sanity check: the physical phase action preserves every vector norm. -/
example (theta : ℝ) (u : WordFock 2) : ‖modeBPhaseShift theta u‖ = ‖u‖ := by
  apply le_antisymm
  · apply lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0)
    intro k
    change ‖Complex.exp (Complex.ofReal (-theta * (k 1 : ℝ)) * Complex.I) * u k‖ ≤ ‖u k‖
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  · apply lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0)
    intro k
    change ‖u k‖ ≤ ‖Complex.exp (Complex.ofReal (-theta * (k 1 : ℝ)) * Complex.I) * u k‖
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

/-- Sanity check: the zero vector has summable photon weights, but its norm
is zero, so the energy predicate alone never certifies a physical state. -/
example : HasFinitePhotonEnergy (0 : WordFock 2) := by
  intro j
  simp

/-- Sanity check: deterministic priors give zero coherent decision error. -/
example (alpha : ℂ) : coherentReadingError alpha 0 = 0 ∧
    coherentReadingError alpha 1 = 0 := by
  simp [coherentReadingError]

end QAlgorithms.Papers.Independent.Advance50.P36


