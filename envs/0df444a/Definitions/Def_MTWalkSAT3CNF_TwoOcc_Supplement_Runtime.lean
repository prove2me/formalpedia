-- Prove2me | Definitions.Def_MTWalkSAT3CNF_TwoOcc_Supplement_Runtime
-- name    : MTWalkSAT3CNF_TwoOcc_Supplement_Runtime
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:55:42.721881+00:00
-- url     : https://prove2.me/theorems/91c5a3a9-9291-4cd3-b4e0-8648031420ee
-- title:
--   Fixed-initialization MT and structural formula predicates
-- statement:
--   For an indexed 3-CNF formula $F$, a legal history-adaptive rule $R$ and a fixed assignment $\sigma$, the MT trajectory starts at the Dirac law of $(\sigma,\mathrm{none})$ and uses the published MT transition kernel unchanged. Its mean is
--
--   $$E_\sigma[T_{MT}(F)]=\int T_{MT}(\omega)\,dP_{F,R,\sigma}(\omega)\in[0,\infty].$$
--
--   The additional structural predicates mean that $F$ admits a satisfying assignment, that different clause indices have different sets of signed literals, that the largest occurrence count is exactly three, and that a variable has a specified number of positive or negative occurrences. The triple constructor checks only distinctness of its three variables. Finite clause families are reindexed by a bijection with $\operatorname{Fin}m$, preserving all duplicate indices. These interfaces supply the fixed-initialization bounds and structural conclusions of §4 without assuming them.
-- source:
--   Minbo Gao, Kun He, Tao Jiang, STOC 2027 submission #914 (October 2026), §2.2 and §4.1, §4.5–§4.6, pp. 9–10, 17–18, 24–27; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/914.pdf

import Definitions.Def_MTWalkSAT3CNF_TwoOcc_MoserTardos
import Definitions.Def_MTWalkSAT3CNF_TwoOcc_WalkSAT

set_option autoImplicit false

namespace MTWalkSAT3CNF.TwoOcc.Supplement
open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {V : Type} [Fintype V] [DecidableEq V] {m : ℕ}

/-- Fixed-initial-assignment MT law; the published transition kernel is unchanged. -/
noncomputable def mtLawFrom (F : Formula V m) (R : MTRule (cnfSystem F))
    (σ : V → Bool) : Measure (ℕ → MTState (fun _ : V => Bool) (Fin m)) :=
  Kernel.trajMeasure (Measure.dirac (σ, Choice.none)) ((cnfSystem F).mtStep R)

noncomputable def mtMeanFrom (F : Formula V m) (R : MTRule (cnfSystem F))
    (σ : V → Bool) : ℝ≥0∞ :=
  ∫⁻ ω, ((cnfSystem F).mtTimeOf ω : ℝ≥0∞) ∂mtLawFrom F R σ

/-- Satisfaction of all indexed clauses. -/
def Satisfiable (F : Formula V m) : Prop := ∃ σ, bad F σ = ∅

/-- Clause equality ignores permutation of literal positions; indices are retained. -/
def NoRepeated (F : Formula V m) : Prop :=
  Function.Injective (fun i => Finset.univ.image (fun p => ((F i).var p, (F i).sign p)))

def MaxOccThree (F : Formula V m) : Prop :=
  (∀ v, occCount F v ≤ 3) ∧ ∃ v, occCount F v = 3

def signedOcc (F : Formula V m) (v : V) (s : Bool) : ℕ :=
  (Finset.univ.filter (fun ip : Fin m × Fin 3 =>
    (F ip.1).var ip.2 = v ∧ (F ip.1).sign ip.2 = s)).card

/-- A structural constructor only: its proof establishes that the three positions are distinct. -/
def triple (a b c : V) (s t u : Bool) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Clause V where
  var := ![a,b,c]
  sign := ![s,t,u]
  var_inj := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all

/-- Reindex a finite clause family without identifying repeated clauses. -/
noncomputable def indexed {I : Type} [Fintype I] (C : I → Clause V) :
    Formula V (Fintype.card I) := fun i => C ((Fintype.equivFin I).symm i)

end MTWalkSAT3CNF.TwoOcc.Supplement


