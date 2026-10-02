-- Prove2me | Definitions.Def_LeblSCV_Varieties_IsDimLE
-- name    : LeblSCV_Varieties_IsDimLE
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T10:11:21.298558+00:00
-- url     : https://prove2.me/theorems/9a2c3b10-946e-4e18-96ee-d4bd5aa82c88
-- title:
--   Definition 6.5.7 — dimension of $X$ at most $d$
-- statement:
--   The **dimension** of a subvariety $X$ is $\dim X = \max_{p \in X_{\mathrm{reg}}} \dim_p X$. For an integer $d$, the statement $\dim X \le d$ means
--   $$\dim_q X \le d \quad \text{for every regular point } q \in X_{\mathrm{reg}}.$$
--
--   **Formalization Note.** The bound $d$ is in `ℤ`, so $d = n - 2$ is negative for $n \le 1$. When $X_{\mathrm{reg}} = \emptyset$ the book's maximum is over the empty set and undefined; here the condition then holds for every $d$ (the convention $\dim \emptyset = -\infty$). By Lemma 6.5.10 a nonempty subvariety has regular points, so for subvarieties this convention only affects $X = \emptyset$.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 186, Definition 6.5.7

import Mathlib
import Definitions.Def_LeblSCV_Varieties_IsRegularPointOfDim

namespace LeblSCV.Varieties

/-- Lebl, Definition 6.5.7: `dim X ≤ d`, where `dim X = max_{p ∈ X_reg} dim_p X`. Stated as
"every regular point `q` of `X` has `dim_q X ≤ d`", with `d ∈ ℤ`; for `X_reg = ∅` (where the book's
maximum is over the empty set) it holds for every `d`. -/
def IsDimLE {n : ℕ} (X : Set (Fin n → ℂ)) (d : ℤ) : Prop :=
  ∀ (q : Fin n → ℂ) (k : ℕ), IsRegularPointOfDim X q k → (k : ℤ) ≤ d

end LeblSCV.Varieties


