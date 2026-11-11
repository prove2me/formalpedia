-- Prove2me | Definitions.Def_SepMeasures_Bisects
-- name    : SepMeasures_Bisects
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:10:36.666839+00:00
-- url     : https://prove2.me/theorems/9b4afc29-d40f-4361-950d-ca8d12566b58
-- title:
--   §2.3, p.12 — a hyperplane bisects a finite signed measure: $\lambda(H^+)=\lambda(H^-)$
-- statement:
--   Let $\lambda$ be a finite signed measure on $\mathbb R^d$ and $H$ an oriented hyperplane with open half-spaces $H^\pm$. Then $H$ **bisects** $\lambda$ if
--   $$\lambda(H^+)=\lambda(H^-).$$
--   For a probability measure that gives no mass to $H$ this says that each side has probability $1/2$; for the signed measure $\sigma_{H'}\lambda$ it expresses a balance of $\lambda$ across $H$ within each side of $H'$. This is the notion used by the signed ham-sandwich theorem (Lemma 2.3).
--
--   **Formalization Note** Finite signed measures are Mathlib's `SignedMeasure` (finite by construction).
-- source:
--   Correa–Griesbach–Harb–Hommelsheim–Jlibene–Livanos–Solan, Separating Measures by Hyperplanes (manuscript, STOC 2027 submission, sha256 96a8692407ff1815980863f3baa9c5d7b90ba27e781ed19063306f67d26fa82f), §2.3, p.12

import Mathlib
import Definitions.Def_SepMeasures_Hyp

open MeasureTheory

namespace SepMeasures

/-- An oriented hyperplane `H` **bisects** a finite signed measure `s` (the paper's `λ`) if
`s(H⁺) = s(H⁻)` (Correa et al., manuscript sha256 96a86924…fa82f, §2.3, p.12).

**Formalization Note.** Finite signed measures are Mathlib's `SignedMeasure` (finite by
construction). `H⁺` and `H⁻` are the open half-spaces. -/
def Bisects {d : ℕ} (s : SignedMeasure (E d)) (H : Hyp d) : Prop := s H.pos = s H.neg

end SepMeasures


