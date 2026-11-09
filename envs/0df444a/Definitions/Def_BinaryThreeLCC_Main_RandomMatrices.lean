-- Prove2me | Definitions.Def_BinaryThreeLCC_Main_RandomMatrices
-- name    : BinaryThreeLCC_Main_RandomMatrices
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T13:02:40.774892+00:00
-- url     : https://prove2.me/theorems/7cf44518-9f50-43a5-8772-846482bd1eba
-- title:
--   Column-stochastic random matrices, half laziness and their mean
-- statement:
--   A real matrix is column stochastic when its transpose satisfies the published Markov-chain row-stochastic predicate, equivalently its entries are nonnegative and every column sum is one. It is doubly stochastic when its row sums are also one. Half laziness is the entrywise condition $M\ge I/2$. On a measurable probability space, the mean and its symmetrization are
--
--   $$\overline M(i,j)=\int M(\omega)_{ij}\,d\mu(\omega),\qquad
--   S=\tfrac12(\overline M+\overline M^{\mathsf T}).$$
--
--   Finite matrix coordinates carry their product Borel sigma algebra. No finite support or uniform distribution is imposed. In the mixing theorem the sample matrices are measurable and almost surely bounded by their stochastic hypotheses, so all means and expectations are actual integrable expectations.
-- source:
--   Oliver Janzer, Peter Manohar, STOC 2027 submission #732 (October 2026), Lemma 5.7, complete restatement printed p.18, PDF p.20; original printed pp.15–16, PDF pp.17–18; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/732.pdf

import Definitions.Def_BinaryThreeLCC_Main_Spectral
import Definitions.Def_mm_basic

set_option autoImplicit false

namespace BinaryThreeLCC.Main

open MeasureTheory

/-- The coordinate Borel sigma algebra on finite real matrices. -/
instance matrixMeasurableSpace {V : Type} : MeasurableSpace (Matrix V V ℝ) :=
  inferInstanceAs (MeasurableSpace (V → V → ℝ))

def ColumnStochastic {V : Type} [Fintype V] (M : Matrix V V ℝ) : Prop :=
  MarkovMixing.IsStochastic M.transpose

def DoublyStochastic {V : Type} [Fintype V] (M : Matrix V V ℝ) : Prop :=
  ColumnStochastic M ∧ MarkovMixing.IsStochastic M

def HalfLazy {V : Type} [DecidableEq V] (M : Matrix V V ℝ) : Prop :=
  ∀ i j, (1 / 2 : ℝ) * (1 : Matrix V V ℝ) i j ≤ M i j

noncomputable def meanMatrix {S : Type*} [MeasurableSpace S] {V : Type}
    (μ : Measure S) (M : S → Matrix V V ℝ) : Matrix V V ℝ :=
  fun i j => ∫ s, M s i j ∂μ

noncomputable def symmetrized {V : Type} (M : Matrix V V ℝ) : Matrix V V ℝ :=
  (1 / 2 : ℝ) • (M + M.transpose)

end BinaryThreeLCC.Main


