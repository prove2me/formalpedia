-- Prove2me | Definitions.Def_MonoidProdQ_Supplement_extEquiv
-- name    : MonoidProdQ_Supplement_extEquiv
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T11:08:41.182461+00:00
-- url     : https://prove2.me/theorems/3ab018d6-ae9a-474f-80f8-e0af617bd6dd
-- title:
--   Equivalence under extensions $\sim_f$
-- statement:
--   Let $U$ and $O$ be finite sets and $f:2^U\to O$. For $S,T\subseteq U$,
--
--   $$S\sim_f T\iff f(S\cup K)=f(T\cup K)\quad\text{for every }K\subseteq U.$$
--
--   The extension $K$ may overlap $S$ or $T$. Two sets are equivalent when no extension can tell them apart through $f$; this relation defines the extension monoid of Theorem 29.
--
--   **Formalization Note** Subsets are finite sets of elements of $U$; the relation is packaged as an equivalence relation (reflexive, symmetric and transitive pointwise in $K$) and is decidable when $U$ is finite and $O$ has decidable equality.
-- source:
--   Lee–Santha, The quantum query complexity of the semigroup product problem, arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), Definition 3, Eq. (32), p.41

import Mathlib

namespace MonoidProdQ.Supplement

/-- Lee–Santha, *The quantum query complexity of the semigroup product problem*,
arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), Definition 3 (Extension monoid), Eq. (32),
p.41: for finite sets `U`, `O` and `f : 2^U → O`, "S ∼_f T ⟺ f(S ∪ K) = f(T ∪ K) for every
K ⊆ U" (equivalence under extensions; "the extension K may overlap S or T").

**Formalization Note.** Subsets of `U` are `Finset U`; `K` ranges over all of them. The relation
is an equivalence (reflexive, symmetric and transitive pointwise in `K`), packaged as a
`Setoid`; its decidability (for finite `U` and decidable equality on `O`) is the instance below. -/
def extEquiv {U O : Type*} [DecidableEq U] (f : Finset U → O) : Setoid (Finset U) where
  r S T := ∀ K : Finset U, f (S ∪ K) = f (T ∪ K)
  iseqv := ⟨fun _ _ => rfl, fun h K => (h K).symm, fun h₁ h₂ K => (h₁ K).trans (h₂ K)⟩

instance extEquiv.decRel {U O : Type*} [Fintype U] [DecidableEq U] [DecidableEq O]
    (f : Finset U → O) : DecidableRel (fun S T : Finset U => (extEquiv f).r S T) :=
  fun S T => inferInstanceAs (Decidable (∀ K : Finset U, f (S ∪ K) = f (T ∪ K)))

end MonoidProdQ.Supplement


