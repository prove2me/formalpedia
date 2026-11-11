-- Prove2me | Definitions.Def_AgnGaussTomo_vacuum
-- name    : AgnGaussTomo_vacuum
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:20:38.127218+00:00
-- url     : https://prove2.me/theorems/4a90c489-26e4-4ed2-9ce5-ac4cc099aabb
-- title:
--   Vacuum projector $|0\rangle\langle 0|$ on $n$-mode Fock space
-- statement:
--   The **vacuum** of $n$ bosonic modes is the Fock state $|0\rangle=|0,\dots,0\rangle$ with no photons. Its density operator $|0\rangle\langle 0|$ has, in the Fock basis $\{|m\rangle : m\in\mathbb N^n\}$, the coefficient $1$ at $(0,0)$ and $0$ everywhere else.
--
--   The vacuum is the reference point of the refinement stage of the high-fidelity algorithm: Lemma 2.7, Proposition 3.9 and Proposition 3.15 are stated for states close to it in trace distance.
--
--   **Formalization Note** The Fock basis is the published `Occupation (Fin n) = Fin n → ℕ`; the vacuum is the all-zero occupation.
-- source:
--   Arulandu, Chen, Chen, Li, Ma, Finding Gaussian Structure in Bosonic States, arXiv:2610.06810 (version of 3 Nov 2026), §2.2, printed p. 8 (PDF p. 11); used in Lemma 2.7 (p. 12), Proposition 3.9 (p. 19), Proposition 3.15 (p. 24)

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P47

open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)

namespace AgnGaussTomo

/-- **The n-mode vacuum projector `|0⟩⟨0|`.** Arulandu, Chen, Chen, Li, Ma, *Finding Gaussian
Structure in Bosonic States*, arXiv:2610.06810 (version of 3 Nov 2026), §2.2, printed p. 8
(PDF p. 11): the vacuum `|0⟩` is the Fock state with no photons; it is the reference state of
Lemma 2.7 (p. 12), Proposition 3.9 (p. 19) and Proposition 3.15 (p. 24).

Its coefficient array in the Fock basis has entry `1` at `(0, 0)` and `0` elsewhere.

**Formalization Note.** The n-mode Fock basis is the published `Occupation (Fin n) = Fin n → ℕ`
(an occupation number for each mode); the all-zero occupation is the vacuum. -/
noncomputable def vacuum (n : ℕ) : Matrix (Occupation (Fin n)) (Occupation (Fin n)) ℂ :=
  fun u v => if u = 0 ∧ v = 0 then 1 else 0

end AgnGaussTomo


