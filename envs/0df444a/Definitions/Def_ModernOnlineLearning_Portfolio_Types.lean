-- Prove2me | Definitions.Def_ModernOnlineLearning_Portfolio_Types
-- name    : ModernOnlineLearning_Portfolio_Types
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T02:37:20.152983+00:00
-- url     : https://prove2.me/theorems/ba06bae3-ee60-43b2-9515-16fea82fae2a
-- title:
--   Definition 10.2, p. 173 — sequence types and finite type classes
-- statement:
--   For an alphabet with $d$ symbols and a sequence $j=(j_1,\ldots,j_T)$, the **type** $n(j)$ records the fraction of positions occupied by each symbol:
--
--   $$n_i(j)=\frac{N(i;j)}{T},\qquad N(i;j)=|\{t:j_t=i\}|.$$
--
--   The **type class** $\mathcal T_T(n)$ is the finite set of all length-$T$ sequences with type $n$; $Q$ is the set of realized types. These generic counting objects support the method-of-types bound and the portfolio monomial identity.
--
--   **Formalization Note** Sequences are functions on `Fin T`, which indexes their positions from zero but has exactly the book’s $T$ positions. The results using types assume $T\ge1$, so the frequency denominator is nonzero.
-- source:
--   Orabona, arXiv:1912.13213v10, Definition 10.2, p. 173, and Theorem 10.4, p. 174

import Mathlib
set_option autoImplicit false

namespace ModernOnlineLearning.Portfolio

/-- Definition 10.2: the fraction of positions carrying each symbol. -/
noncomputable def sequenceType {d T : ℕ} (j : Fin T → Fin d) : Fin d → ℝ :=
  fun i => ((Finset.univ.filter (fun t : Fin T => j t = i)).card : ℝ) / (T : ℝ)

/-- The type class of a sequence, as a finite set. -/
noncomputable def typeClass {d T : ℕ} (n : Fin d → ℝ) : Finset (Fin T → Fin d) :=
  Finset.univ.filter (fun j => sequenceType j = n)

/-- The set of realized types of length-`T` sequences. -/
def possibleTypes (d T : ℕ) : Set (Fin d → ℝ) :=
  Set.range (fun j : Fin T → Fin d => sequenceType j)

end ModernOnlineLearning.Portfolio


