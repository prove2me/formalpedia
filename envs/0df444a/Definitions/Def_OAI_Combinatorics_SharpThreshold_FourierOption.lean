-- Prove2me | Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOption
-- name    : OAI_Combinatorics_SharpThreshold_FourierOption
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T00:07:19.505711+00:00
-- url     : https://prove2.me/theorems/b4c29ce1-b32b-4170-9729-42e5f5d0a058
-- title:
--   Splitting Fourier supports along one extra coordinate
-- statement:
--   Let $\iota^+=\iota\sqcup\{\star\}$ be $\iota$ with one extra coordinate.
--
--   1. Subsets of $\iota^+$ correspond bijectively to tagged subsets of $\iota$: $S\not\ni\star$ corresponds to $S$ itself, and $S\ni\star$ corresponds to $S\setminus\{\star\}$ with the other tag.
--   2. For $x\in\{0,1\}^{\iota^+}$ and $S\subseteq\iota$, writing $x'$ for the restriction to $\iota$,
--   $$
--   \chi_S(x)=\chi_S(x'),\qquad\chi_{S\cup\{\star\}}(x)=\chi_p(x_\star)\,\chi_S(x') .
--   $$
--
--   This supports induction on the number of coordinates in the $p$-biased Fourier expansion.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SharpThreshold/FourierOption.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SharpThreshold/FourierOption.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SharpThreshold mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SharpThreshold
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Model
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockOrbit
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierBasis
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOrthogonality

namespace OAI

universe u

noncomputable section

open scoped BigOperators

namespace Problem313.BiasedFourier

variable {ι : Type u} [Fintype ι]

/-- Separate Fourier supports according to whether the distinguished coordinate occurs. -/
def optionFinsetEquiv : Finset (Option ι) ≃ Finset ι ⊕ Finset ι := by
  classical
  refine
    { toFun := fun S => if none ∈ S then Sum.inr S.eraseNone else Sum.inl S.eraseNone
      invFun := Sum.elim (fun S => S.map Function.Embedding.some) Finset.insertNone
      left_inv := ?_
      right_inv := ?_ }
  · intro S
    by_cases h : none ∈ S
    · simp [h, Finset.insert_eq_of_mem h]
    · simp [h]
  · intro S
    cases S <;> simp

omit [Fintype ι] in
@[simp] theorem char_map_some (p : ℝ) (S : Finset ι) (x : Option ι → Bool) :
    char p (S.map Function.Embedding.some) x = char p S (fun i => x (some i)) := by
  classical
  simp [char]

omit [Fintype ι] in
@[simp] theorem char_insertNone (p : ℝ) (S : Finset ι) (x : Option ι → Bool) :
    char p (Finset.insertNone S) x =
      chi p (x none) * char p S (fun i => x (some i)) := by
  classical
  simp [char, Finset.insertNone]

end Problem313.BiasedFourier

end

end OAI


