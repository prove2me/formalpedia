-- Prove2me | Definitions.Def_MonoidProdQ_Supplement_strongCertNumber
-- name    : MonoidProdQ_Supplement_strongCertNumber
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T11:10:08.374931+00:00
-- url     : https://prove2.me/theorems/166a5948-1ae5-4dc0-9735-ea8c0fb5bca3
-- title:
--   Strong-certificate number $b_f(U)$
-- statement:
--   Let $f:2^U\to O$. For $S\subseteq U$, a **strong certificate** for $S$ is a subset $C\subseteq S$ with $C\sim_f S$, that is, $f(C\cup K)=f(S\cup K)$ for every $K\subseteq U$. Define
--
--   $$b_f(U)=\max_{S\subseteq U}\ \min\{|C|:\ C\subseteq S,\ C\sim_f S\}.$$
--
--   This is the worst case, over all inputs (yes- and no-instances alike), of the size of a smallest strong certificate; no monotonicity of $f$ is assumed.
--
--   **Formalization Note** The inner minimum is a natural-number infimum over a set containing $|S|$ ($C=S$ is a strong certificate), so it is attained; the outer maximum is a finite supremum.
-- source:
--   Lee–Santha, The quantum query complexity of the semigroup product problem, arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), Definition 4, Eq. (33), p.41

import Mathlib

namespace MonoidProdQ.Supplement

/-- Lee–Santha, *The quantum query complexity of the semigroup product problem*,
arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), Definition 4 (Strong certificate), Eq. (33),
p.41: "For S ⊆ U, a strong certificate for S with respect to f is a subset C ⊆ S with C ∼_f S,
that is, f(C ∪ K) = f(S ∪ K) for every K ⊆ U. Define
b_f(U) = max_{S⊆U} min{|C| : C ⊆ S, C ∼_f S}."

**Formalization Note.** Subsets are `Finset U`. The inner minimum is a natural-number infimum
over a set that contains `|S|` (`C = S` is a strong certificate for `S`), so it is attained; the
outer maximum over the finitely many `S` is `Finset.sup`. -/
noncomputable def strongCertNumber {U O : Type*} [Fintype U] [DecidableEq U]
    (f : Finset U → O) : ℕ :=
  Finset.univ.sup fun S : Finset U =>
    sInf {c : ℕ | ∃ C : Finset U, C ⊆ S ∧ (∀ K : Finset U, f (C ∪ K) = f (S ∪ K)) ∧ C.card = c}

end MonoidProdQ.Supplement


