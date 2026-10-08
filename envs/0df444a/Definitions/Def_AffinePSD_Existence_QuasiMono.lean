-- Prove2me | Definitions.Def_AffinePSD_Existence_QuasiMono
-- name    : AffinePSD_Existence_QuasiMono
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T07:49:23.064586+00:00
-- url     : https://prove2.me/theorems/add78c6b-ac03-472d-8133-6e169ca957e5
-- title:
--   Quasi-monotone increasing maps on subsets of S_d (Definition 4.7)
-- statement:
--   Let $U\subseteq S_d$. A map $f:U\to S_d$ is **quasi-monotone increasing** on $U$ if for all $x,y\in U$ and $u\in S_d^+$ with
--   $$x\preceq y\quad\text{and}\quad\langle x,u\rangle=\langle y,u\rangle$$
--   one has $\langle f(x),u\rangle\le\langle f(y),u\rangle$.
--
--   This is the matrix analogue of the Kamke–Müller condition, and it is what makes comparison theorems for matrix ODEs work (Theorem 4.8). The paper applies it to the Riccati vector field $R$ on $S_d^+$ (Lemma 5.1).
--
--   **Formalization Note** The paper states the definition for open $U$. Lemma 5.1 uses it with $U=S_d^+$, so the predicate is defined for any set; $f$ is a map on $M_d$ of which only the values on $U$ matter.
-- source:
--   Cuchiero, Filipović, Mayerhofer, Teichmann, Affine processes on positive semidefinite matrices, arXiv:0910.0137v3 (2011), §4, Definition 4.7, p. 22

import Mathlib
import Definitions.Def_AffinePSD_Existence_Cone

namespace AffinePSD.Existence

/-- Quasi-monotone increasing maps, Definition 4.7 (arXiv:0910.0137v3, p. 22): `f : U → S_d` is
quasi-monotone increasing on `U` if for all `x, y ∈ U` and `u ∈ S_d^+` with `x ⪯ y` and
`⟨x, u⟩ = ⟨y, u⟩` one has `⟨f(x), u⟩ ≤ ⟨f(y), u⟩`.
Formalization Note: the paper states the definition for open `U ⊂ S_d`; the predicate is
meaningful on any set and Lemma 5.1 applies it to `U = S_d^+`. -/
def QuasiMonoOn {d : ℕ} (f : Mat d → Mat d) (U : Set (Mat d)) : Prop :=
  ∀ x ∈ U, ∀ y ∈ U, ∀ u, PSD u → PSD (y - x) → tr x u = tr y u → tr (f x) u ≤ tr (f y) u

end AffinePSD.Existence


