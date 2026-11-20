-- Prove2me | Definitions.Def_LatticePrepro_Conversions_Codes_Ext
-- name    : LatticePrepro_Conversions_Codes_Ext
-- status  : Definition
-- author  : @WizardOfMenlo
-- created : 2026-11-20T00:10:44.236088+00:00
-- url     : https://prove2.me/theorems/449303fd-e849-460e-a558-bbac46589008
-- title:
--   The code family of a block-sparse linear system over the prime field (Lemma 3.11)
-- statement:
--   This bundle adds one definition to the code side of Lemma 3.11.
--
--   **The code family of a linear system** (`LinearSystemFamily.toCodeFamily`). Let $L$ be a linear-system family over $\mathbb F_p$: a fixed linear map $A$ on $\mathbb F_p^{\iota}$ for a finite column set $\iota$, right-hand sides $b_x$, and a partition of the columns into $D$ blocks of size $b$. Its code family has coordinate set $\iota\sqcup\iota$, the code
--   $$\mathcal C_L=\ker A\times\{0\}\subseteq\mathbb F_p^{\iota\sqcup\iota},$$
--   and the targets $y_x=(v_x,0)$ for a solution $v_x$ of $Av=b_x$ if the system is solvable, and $y_x=(0,\mathbf 1)$ otherwise.
--
--   The bundle also contains the lemma that each of the $2D$ blocks of the coordinate set $\iota\sqcup\iota$ has exactly $b$ elements (`card_codeBlk_fiber`).
--
--   This packages the code `LinearSystemFamily.code` and the targets `LinearSystemFamily.codeTarget` of the proof of Lemma 3.11 (Appendix B.1) as a `CodeFamily`.
--
--   **Formalization Note.** The solution $v_x$ is picked by classical choice, so the family is noncomputable; the distance from $y_x$ to the code does not depend on the choice.
-- source:
--   G. Fenzi, G. Weissenberg, Nearly Optimal Hardness for CVP and NCP with Preprocessing (STOC 2027 submission #847; IACR ePrint 2026/2634, https://eprint.iacr.org/2026/2634), proof of Lemma 3.11 (\label{lem:block-system-codes}) in Appendix B.1 (\label{subsec:affine-code-proof}); Lean: LatticePrepro/Conversions/Codes.lean, LatticePrepro.LinearSystemFamily.toCodeFamily, LatticePrepro.LinearSystemFamily.card_codeBlk_fiber

import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Reduction_LinearSystem
import Definitions.Def_LatticePrepro_Conversions_Codes

/-! Further definitions from `LatticePrepro/Conversions/Codes.lean`, continuing `Def_LatticePrepro_Conversions_Codes`. -/

namespace LatticePrepro

section OfSystem

variable {p : ℕ} [Fact p.Prime] {X : Type} (L : LinearSystemFamily (ZMod p) X)

/-- The code family of Lemma 3.11 over the prime field. -/
noncomputable def LinearSystemFamily.toCodeFamily : CodeFamily (ZMod p) X where
  M := L.ι ⊕ L.ι
  code := L.code
  target := L.codeTarget

lemma LinearSystemFamily.card_codeBlk_fiber (s : L.β ⊕ L.β) :
    (Finset.univ.filter fun i => L.codeBlk i = s).card = L.blockSize := by
  rcases s with t | t
  · rw [← L.card_fiber t, Finset.card_filter, Finset.card_filter, Fintype.sum_sum_type]
    simp only [LinearSystemFamily.codeBlk, Sum.map_inl, Sum.map_inr, Sum.inl.injEq, reduceCtorEq,
      ite_false, Finset.sum_const_zero, add_zero]
  · rw [← L.card_fiber t, Finset.card_filter, Finset.card_filter, Fintype.sum_sum_type]
    simp only [LinearSystemFamily.codeBlk, Sum.map_inl, Sum.map_inr, Sum.inr.injEq, reduceCtorEq,
      ite_false, Finset.sum_const_zero, zero_add]

end OfSystem

end LatticePrepro


