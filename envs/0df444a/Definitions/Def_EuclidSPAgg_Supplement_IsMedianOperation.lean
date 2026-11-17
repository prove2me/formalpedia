-- Prove2me | Definitions.Def_EuclidSPAgg_Supplement_IsMedianOperation
-- name    : EuclidSPAgg_Supplement_IsMedianOperation
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:42:44.071449+00:00
-- url     : https://prove2.me/theorems/97e3a682-0d4a-455e-81a1-1c63284bdf5f
-- title:
--   Median operation on a set $C$ (median-algebra axioms)
-- statement:
--   Let $C$ be a set. A ternary operation $m$ is a **median operation on $C$** if it maps $C^3$ into $C$ and, for all $a,b,c,d,e\in C$,
--
--   1. $m(a,b,c)=m(b,a,c)=m(b,c,a)$ (symmetry);
--   2. $m(a,a,b)=a$;
--   3. $m(a,b,m(c,d,e))=m(m(a,b,c),m(a,b,d),e)$.
--
--   These are the axioms of a median algebra in Bowditch's account; by Sholander's characterization they are equivalent to the interval axioms $I(a,a)=\{a\}$, $I(a,b)=I(b,a)$, $c\in I(a,b)\Rightarrow I(a,c)\subseteq I(a,b)$, $I(a,b)\cap I(b,c)\cap I(c,a)=\{m(a,b,c)\}$ that the paper verifies for the restriction of a strategyproof ternary rule to a core. The notion is the hypothesis of Theorem 4.5.
--
--   **Formalization Note** $m$ is a total function $V\to V\to V\to V$; only its values on $C^3$ matter.
-- source:
--   Jia, Strategyproof Aggregation in Euclidean Spaces: Rigidity and Median Optimality, arXiv:2609.19394 (held version, sha256 891e6125…), Theorem 4.5, p.17 (PDF p.19); median-algebra axioms cited from Bowditch [Bow16, Section 2], p.15 (PDF p.17)

import Mathlib

namespace EuclidSPAgg.Supplement

/-- A **median operation** on a set `C` (Jia, *Strategyproof Aggregation in Euclidean Spaces: Rigidity and Median Optimality*, arXiv:2609.19394 (held version, sha256 891e6125…), Theorem 4.5, p.17 (PDF p.19); the paper uses
the median-algebra notion of Bowditch, *Median algebras* [Bow16, Section 2], via Sholander's
characterization, p.15 (PDF p.17)): a ternary operation `m` mapping `C³` into `C` such that, for
all `a, b, c, d, e ∈ C`,

1. `m(a, b, c) = m(b, a, c) = m(b, c, a)` (symmetry);
2. `m(a, a, b) = a`;
3. `m(a, b, m(c, d, e)) = m(m(a, b, c), m(a, b, d), e)` (Bowditch's axiom (M3)).

**Formalization Note** `m` is a total function `V → V → V → V`; only its values on `C³` matter, and
the first clause says that `C³` is mapped into `C`. These are the standard median-algebra axioms;
they are equivalent to the interval axioms (I1)–(I4) the paper quotes on p.15 (Sholander). -/
def IsMedianOperation {V : Type*} (C : Set V) (m : V → V → V → V) : Prop :=
  (∀ a ∈ C, ∀ b ∈ C, ∀ c ∈ C, m a b c ∈ C) ∧
  (∀ a ∈ C, ∀ b ∈ C, ∀ c ∈ C, m a b c = m b a c ∧ m a b c = m b c a) ∧
  (∀ a ∈ C, ∀ b ∈ C, m a a b = a) ∧
  (∀ a ∈ C, ∀ b ∈ C, ∀ c ∈ C, ∀ d ∈ C, ∀ e ∈ C,
    m a b (m c d e) = m (m a b c) (m a b d) e)

end EuclidSPAgg.Supplement


