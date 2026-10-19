-- Prove2me | Definitions.Def_EnsembleSpaceDraft_finiteMixture
-- name    : EnsembleSpaceDraft_finiteMixture
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-18T11:47:46.557999+00:00
-- url     : https://prove2.me/theorems/1cda33e3-c9fd-4962-9ce6-607fdaa344a3
-- title:
--   Finite mixtures of ensembles
-- statement:
--   Definition 1.10 associates to finitely many ensembles $e_1,\ldots,e_n$ and coefficients $p_i\in[0,1]$ with $\sum_i p_i=1$ a single ensemble, the **finite mixture** $\sum_i p_i e_i$.
--
--   Coefficients equal to zero are deleted and the remaining pairs keep their order. If one pair $(p,e)$ remains, the mixture is $e$. If several remain, with first pair $(p,e)$ and with $s$ the sum of the later coefficients, the mixture is
--   $$
--   p\,e+\bar p\,m,
--   $$
--   where $m$ is the finite mixture of the later ensembles with coefficients divided by $s$. This is the bracketing written as (1.11) in the draft.
--
--   The same value is defined for a list of real coefficients and ensembles, and for a finite index set $\{1,\ldots,n\}$ presented as `Fin n`.
--
--   **Formalization Note.** The operation is partial. It returns no ensemble if every coefficient is zero, or if a tail of the list sums to zero. Corollary 1.12 states that a value does exist when the coefficients lie in $[0,1]$ and sum to $1$. While a tail is rescaled, each new coefficient is passed through the projection of $\mathbb R$ onto $[0,1]$. For nonnegative summands that projection is the identity on the ratios that arise from a positive tail sum.
-- source:
--   G. Carcassi, C. A. Aidala, Ensemble spaces, draft of 12 October 2026, Chapter 1. Generated from https://github.com/assumptionsofphysics/book (art_pm_EnsembleSpaces). Definition 1.10, equation (1.11), pp. 15–16.

import Definitions.Def_EnsembleSpaceDraft_axioms
import Mathlib

/-!
# Finite mixtures (Definition 1.10)

The nested expression (1.11) is realized by dropping coefficients equal to `0` and then
folding binary mixes from the left. A coefficient known only as a real number is sent
through `Set.projIcc`, which is the identity on `[0, 1]`. If the filtered list is empty,
or a partial sum of a tail vanishes, the function returns `none`.
-/

open scoped unitInterval

namespace EnsembleSpaceDraft

universe u

variable {E : Type u} [TopologicalSpace E]

/-- Left-nested mixture of a list whose coefficients are intended to be strictly positive.
Returns `none` on the empty list and when a tail sums to zero. -/
noncomputable def nestMixture? (X : EnsembleSpace E) : List (ℝ × E) → Option E
  | [] => none
  | (p, e) :: t =>
      if t = [] then some e
      else
        let s := (t.map Prod.fst).sum
        if s = 0 then none
        else
          (nestMixture? X (t.map fun pe => (pe.1 / s, pe.2))).map fun tail =>
            X.mix (Set.projIcc (0 : ℝ) 1 zero_le_one p) e tail
termination_by l => l.length
decreasing_by
  simp_wf

/-- Definition 1.10. Zero coefficients are dropped, preserving order; the remaining list
is mixed by (1.11). Returns `none` if every coefficient is zero. -/
noncomputable def finiteMixtureList? (X : EnsembleSpace E) (l : List (ℝ × E)) : Option E :=
  nestMixture? X (l.filter fun pe => pe.1 ≠ 0)

/-- Definition 1.10, indexed by `Fin n`. -/
noncomputable def finiteMixture {n : ℕ} (X : EnsembleSpace E) (p : Fin n → ℝ) (e : Fin n → E) :
    Option E :=
  finiteMixtureList? X (List.ofFn fun i => (p i, e i))

end EnsembleSpaceDraft


