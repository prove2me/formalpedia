-- Prove2me | Definitions.Def_EvasivePatterns_IsCentralConjGalois
-- name    : EvasivePatterns_IsCentralConjGalois
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:30:33.8256+00:00
-- url     : https://prove2.me/theorems/0baf3491-bdaf-46b2-a926-e0da2f85a06f
-- title:
--   Finite Galois $K/\mathbb Q$ inside $\mathbb C$ with central complex conjugation
-- statement:
--   A subfield $K \subseteq \mathbb C$ belongs to the field class of §4 when $K/\mathbb Q$ is a finite Galois extension in which complex conjugation commutes with every Galois automorphism:
--   $$
--   \sigma(\bar x) = \overline{\sigma(x)} \qquad (\sigma \in \mathrm{Gal}(K/\mathbb Q),\ x \in K).
--   $$
--   Every cyclotomic field $\mathbb Q(\zeta)$ belongs to this class. Lemma 4.1 and Theorem 4.2 are stated for every such $K$.
--
--   **Formalization Note** $K$ is an intermediate field of $\mathbb C/\mathbb Q$. A normal extension inside $\mathbb C$ is mapped onto itself by complex conjugation, so the conjugate $y = \bar x$ of every $x \in K$ lies in $K$; centrality is stated for such pairs.
-- source:
--   Faro, Marino, Pavone, A Complete Characterization of Eventually Evasive Binary Patterns, manuscript (Nov. 2026; sha256 e91deef3…), §4, p.5 (PDF p.6), lines 156–158

import Mathlib

namespace EvasivePatterns

/-- **The field class of §4.** A subfield `K ⊆ ℂ` that is a finite Galois extension of `ℚ` in which
complex conjugation commutes with all Galois automorphisms: `σ(\bar x) = \overline{σ(x)}` for every
`σ ∈ Gal(K/ℚ)` and `x ∈ K`. Cyclotomic fields `ℚ(ζ)` belong to it.

Source: S. Faro, F. P. Marino, A. Pavone, *A Complete Characterization of Eventually Evasive Binary
Patterns*, manuscript (Nov. 2026), §4, printed p. 5 (PDF p. 6), lines 157–158: "More generally,
throughout this section K/ℚ is a finite Galois extension in which complex conjugation commutes with
all Galois automorphisms; cyclotomic fields satisfy this condition."

**Formalization Note** `K` is an `IntermediateField ℚ ℂ` (the paper's fields are embedded in `ℂ`).
Since `K/ℚ` is normal, complex conjugation maps `K` onto itself; centrality is stated for every
`x ∈ K` and its conjugate `y = \bar x ∈ K`. -/
def IsCentralConjGalois (K : IntermediateField ℚ ℂ) : Prop :=
  FiniteDimensional ℚ K ∧ IsGalois ℚ K ∧
    ∀ σ : K ≃ₐ[ℚ] K, ∀ x y : K, (y : ℂ) = star (x : ℂ) → ((σ y : K) : ℂ) = star ((σ x : K) : ℂ)

end EvasivePatterns


