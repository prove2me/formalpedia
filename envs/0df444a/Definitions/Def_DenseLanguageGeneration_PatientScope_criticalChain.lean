-- Prove2me | Definitions.Def_DenseLanguageGeneration_PatientScope_criticalChain
-- name    : DenseLanguageGeneration_PatientScope_criticalChain
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T11:46:46.828695+00:00
-- url     : https://prove2.me/theorems/acc361f0-3eee-4cb8-9811-fbebe28a15af
-- title:
--   Consistent languages, critical chain, scope and indexed focus
-- statement:
--   Let $\mathcal L=(L_1,L_2,\ldots)$ be an indexed sequence of infinite subsets of $\mathbb N_+$, and let $h$ be a finite list of received adversary inputs. A language is consistent when it contains every entry of $h$. Scan the family in index order and retain a consistent language precisely when it is contained in every previously retained language:
--
--   $$
--   L_i\text{ critical}\quad\Longleftrightarrow\quad
--   h\subseteq L_i\ \text{ and }\ L_i\subseteq L_j\text{ for every critical }j<i.
--   $$
--
--   The scope of size $s$ contains the first $s$ indices; its focus is the critical language with largest index in that scope. The focus index is retained even when two indexed languages are equal as sets. Absence of a focus has an explicit optional value.
--
--   This interface implements the paper's critical-chain convention, which compares against earlier critical languages rather than all earlier consistent languages. The infinite-language and finite-history primitives are imported from the published language bundle.
--
--   **Formalization Note** Family indices start at zero. The finite scan up to index $i$ defines global criticality at $i$ without truncating the family itself. Completed time $t$ uses exactly $t$ inputs, so time zero has empty history. A missing focus denotes the empty set only when reading its language; legal patient-scope updates repair its absence.
-- source:
--   Cai, Li, Shen, Wang and Zhang, STOC 2027 submission #335 (October 2026), §2, printed p.7 (PDF p.9); Definitions 3.1–3.2 and 3.5–3.6, printed pp.9–10 (PDF pp.11–12); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/335.pdf

import Definitions.Def_ActiveLanguageGeneration_Hierarchy_Language

set_option autoImplicit false
open ActiveLanguageGeneration.Hierarchy

namespace DenseLanguageGeneration.PatientScope

/-- §2 (printed p.7 / PDF p.9). Index i is the paper's index i+1.
Repetitions are allowed, and every language is infinite. -/
abbrev Family := ℕ → ActiveLanguageGeneration.Hierarchy.Language ℕ+

/-- Inputs through the end of paper time t, including none at time zero. -/
def history (a : ℕ → ℕ+) (t : ℕ) : List ℕ+ := (List.range t).map a

/-- Definition 3.1. Only received inputs constrain consistency. -/
def Consistent (L : Family) (h : List ℕ+) (i : ℕ) : Prop :=
  ∀ x ∈ h, x ∈ (L i).val

/-- Definition 3.2. Scan the first s indices in increasing order, comparing a
candidate only with earlier CRITICAL languages. No finiteness assumption on L. -/
noncomputable def criticalIndices (L : Family) (h : List ℕ+) : ℕ → Finset ℕ
  | 0 => ∅
  | s + 1 => by
      classical
      let old := criticalIndices L h s
      exact if Consistent L h s ∧ ∀ j ∈ old, (L s).val ⊆ (L j).val
        then insert s old else old

/-- Criticality at any index is computed from its finite predecessor segment. -/
def Critical (L : Family) (h : List ℕ+) (i : ℕ) : Prop :=
  i ∈ criticalIndices L h (i + 1)

/-- Definitions 3.5--3.6. A scope size s includes exactly indices i < s.
None records absence of a focus, rather than identifying it with index zero. -/
noncomputable def focusIndex (L : Family) (h : List ℕ+) (s : ℕ) : Option ℕ := by
  classical
  exact if hc : (criticalIndices L h s).Nonempty
    then some ((criticalIndices L h s).max' hc) else none

/-- The language of the indexed focus; empty only when no focus exists. -/
noncomputable def focusSet (L : Family) (h : List ℕ+) (s : ℕ) : Set ℕ+ :=
  match focusIndex L h s with
  | some i => (L i).val
  | none => ∅

end DenseLanguageGeneration.PatientScope


