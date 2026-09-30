-- Prove2me | Definitions.Def_TranscendenceTheory_IsolatedComponentMultiplicityData
-- name    : TranscendenceTheory_IsolatedComponentMultiplicityData
-- status  : Definition
-- author  : @tomasz
-- created : 2026-09-20T17:31:40.085229+00:00
-- url     : https://prove2.me/theorems/ef53dcb6-dc3f-4ef7-8fd9-7079e979ddec
-- title:
--   Isolated ideal components with differential contact and a local length bound
-- statement:
--   For nonnegative integers $T,e$, isolated-component multiplicity data consist of a commutative $\mathbb Q$-algebra $R$, a prime ideal $\mathfrak p$, a derivation $D$, and a transverse element
--
--   $$
--   q\in\mathfrak p,\qquad Dq\notin\mathfrak p.
--   $$
--
--   They also contain a finite family of ideals $J_0,\ldots,J_{r-1}$, a distinguished index $i<r$, and the separation condition
--
--   $$
--   J_j\not\subseteq\mathfrak p\qquad(j\ne i).
--   $$
--
--   Writing $I=\bigcap_{j<r}J_j$ and $S=R_{\mathfrak p}$, the remaining conditions are
--
--   $$
--   D^k f\in\mathfrak p\quad(f\in I,\ 0\le k\le T),
--   \qquad \operatorname{length}_{S}(S/IS)\le e.
--   $$
--
--   These conditions are imposed on the whole intersection. Derivative containment for the selected ideal $J_i$ and the equality $IS=J_iS$ are conclusions of the separate component-isolation theorem, rather than fields of these data.
--
--   Primaryness is not required by this definition: the algebraic transfer works for any family satisfying the separation condition. An isolated primary decomposition is the intended geometric application. Constructing such data from the mission hypotheses and proving a uniform sum bound remain open obligations.
-- source:
--   Philippon (1986), Lemmes de zeros dans les groupes algebriques commutatifs, Bull. Soc. Math. France 114, 355-383, Proposition 4.7, especially p. 379, and section 5, Lemma 5.1, pp. 380-382. https://www.numdam.org/item/10.24033/bsmf.2060.pdf. Senthil Kumar K (2026), Appendix A, Theorem A.2. https://doi.org/10.1017/S001309152610145X. Algebraic auxiliary theorem: isolate an ideal component with a separator outside the prime and prove preservation of the local quotient and finite-order derivative containment. Component selection, global transversality, and the total local-length degree budget remain open.

import Definitions.Def_TranscendenceTheory_PrimeMultiplicityData

noncomputable section
namespace TranscendenceTheory

/-- Contact is known for a finite intersection; the local multiplicity is to be assigned
to its isolated component. No contact condition on that component is assumed. -/
structure IsolatedComponentMultiplicityData (T e : ℕ) where
  R : Type
  [commRing : CommRing R]
  [algebra : Algebra ℚ R]
  p : Ideal R
  [prime : p.IsPrime]
  D : Derivation ℚ R R
  q : R
  q_mem : q ∈ p
  deriv_not_mem : D q ∉ p
  n : ℕ
  J : Fin n → Ideal R
  i : Fin n
  isolated : ∀ j, j ≠ i → ¬ J j ≤ p
  jets : ∀ f ∈ ⨅ j, J j, ∀ k ≤ T, (D^[k]) f ∈ p
  length_le : Module.length (Localization.AtPrime p)
    ((Localization.AtPrime p) ⧸ (⨅ j, J j).map
      (algebraMap R (Localization.AtPrime p))) ≤ (e : ℕ∞)

attribute [instance] IsolatedComponentMultiplicityData.commRing
  IsolatedComponentMultiplicityData.algebra IsolatedComponentMultiplicityData.prime

end TranscendenceTheory


