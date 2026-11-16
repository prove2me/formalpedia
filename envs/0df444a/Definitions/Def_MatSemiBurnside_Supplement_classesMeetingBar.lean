-- Prove2me | Definitions.Def_MatSemiBurnside_Supplement_classesMeetingBar
-- name    : MatSemiBurnside_Supplement_classesMeetingBar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:45:29.954564+00:00
-- url     : https://prove2.me/theorems/495723e2-8cbc-4a7a-9374-781de380dc9a
-- title:
--   Class counts, the quotient $\langle X\rangle/\sim$ and its diameter for a congruence on $\overline{\langle X\rangle}$
-- statement:
--   Let $X\subseteq\mathrm{Mat}_d(\mathbb Q)$ be finite and let $\sim$ be a congruence on the Zariski closure $\overline{\langle X\rangle}\subseteq\mathrm{Mat}_d(\overline{\mathbb Q})$.
--
--   1. For a set $G$ of matrices, $|G/\sim|$ is the number of classes of $\overline{\langle X\rangle}/\sim$ that meet $G$.
--   2. $\langle X\rangle/\sim$ is the quotient of $\langle X\rangle$ (embedded in $\mathrm{Mat}_d(\overline{\mathbb Q})$) by the restriction of $\sim$; it is identified with the set of classes of $\overline{\langle X\rangle}/\sim$ that meet $\langle X\rangle$.
--   3. The diameter of $\langle X\rangle/\sim$ is at most $n$ when every $a\in\langle X\rangle$ satisfies $a\sim a_1\cdots a_k$ for some $a_1,\dots,a_k\in X$ with $1\le k\le n$.
--
--   These are the notions in which Theorem 3 is stated: its hypothesis bounds $|G/\sim|$, its conclusion concerns $\langle X\rangle/\sim$.
--
--   **Formalization Note** $|G/\sim|$ is the `Set.encard` of `classesMeetingBar c G`; the quotient is `quotImage X c`; the diameter bound is `DiameterLEBar X c n`, the same convention as the base `DiameterLE` transported to the closure.
-- source:
--   Guttenberg, Lhote, Shirmohammadi, Worrell, Burnside Problems for Matrix Semigroup Quotients with Applications to Border Complexity, STOC 2027 submission (held version, sha256 1bc61d4e…), §2, p.6 (length, diameter, |S/∼|); Theorem 3, p.4; §3.3, p.13

import Mathlib
import Definitions.Def_MatSemiBurnside_Supplement_closureSG
set_option autoImplicit false

namespace MatSemiBurnside.Supplement

/-- **Classes of ⟨X⟩‾/∼ met by a set G.** Guttenberg, Lhote, Shirmohammadi, Worrell, *Burnside Problems for Matrix Semigroup Quotients
with Applications to Border Complexity*, STOC 2027 submission (held version, sha256 1bc61d4e…), §2, p.6 ("its size counts the classes of ⟨X⟩/∼ that
meet S"), applied in Theorem 3 (p.4, restated p.13) to a congruence ∼ on the Zariski closure ⟨X⟩‾: |G/∼| is the
number of classes of ⟨X⟩‾/∼ that meet G (p.4: "the number of classes of this closure met by each subgroup").

**Formalization Note.** `c` is a congruence on the semigroup ⟨X⟩‾ = `closureSG X` ⊆ Mat_d(ℚ̄); |G/∼| is
`(classesMeetingBar c G).encard`, a value in ℕ ∪ {∞}. -/
def classesMeetingBar {d : ℕ} {X : Finset (Matrix (Fin d) (Fin d) ℚ)} (c : Con (closureSG X))
    (G : Set (Matrix (Fin d) (Fin d) Qbar)) : Set c.Quotient :=
  {q | ∃ a : closureSG X, (a : Matrix (Fin d) (Fin d) Qbar) ∈ G ∧ (a : c.Quotient) = q}

/-- **The quotient ⟨X⟩/∼ for a congruence ∼ on ⟨X⟩‾.** Guttenberg, Lhote, Shirmohammadi, Worrell, *Burnside Problems for Matrix Semigroup Quotients
with Applications to Border Complexity*, STOC 2027 submission (held version, sha256 1bc61d4e…), Theorem 3, p.4 and §3.3, p.13: ⟨X⟩/∼ is the
quotient of ⟨X⟩ (embedded entrywise in Mat_d(ℚ̄)) by the restriction of ∼. Its elements correspond to the
classes of ⟨X⟩‾/∼ that meet ⟨X⟩; `quotImage X c` is that set of classes. -/
def quotImage {d : ℕ} (X : Finset (Matrix (Fin d) (Fin d) ℚ)) (c : Con (closureSG X)) : Set c.Quotient :=
  Set.range (fun a : Subsemigroup.closure (X : Set (Matrix (Fin d) (Fin d) ℚ)) => ((incl X a : closureSG X) : c.Quotient))

/-- **Diameter of ⟨X⟩/∼ at most n, for a congruence ∼ on ⟨X⟩‾.** Guttenberg, Lhote, Shirmohammadi, Worrell, *Burnside Problems for Matrix Semigroup Quotients
with Applications to Border Complexity*, STOC 2027 submission (held version, sha256 1bc61d4e…), §2, p.6: "the class of a has length
equal to the least positive integer k such that a ∼ a₁ ⋯ a_k with a_i ∈ X. The diameter of ⟨X⟩/∼ with respect
to X/∼ is the least n ∈ ℕ such that every class has length at most n"; §3, p.7: lengths are measured with
respect to X.

`DiameterLEBar X c n` says: every a ∈ ⟨X⟩ is ∼-congruent (in ⟨X⟩‾, after the entrywise embedding into
Mat_d(ℚ̄)) to a product a₁ ⋯ a_k of elements a_i ∈ X with 1 ≤ k ≤ n.

**Formalization Note.** The same convention as the base `DiameterLE`, transported to the restriction to ⟨X⟩ of
a congruence on the closure. -/
def DiameterLEBar {d : ℕ} (X : Finset (Matrix (Fin d) (Fin d) ℚ)) (c : Con (closureSG X)) (n : ℕ) : Prop :=
  ∀ a : Subsemigroup.closure (X : Set (Matrix (Fin d) (Fin d) ℚ)),
    ∃ l : List (Matrix (Fin d) (Fin d) ℚ), l ≠ [] ∧ l.length ≤ n ∧ (∀ x ∈ l, x ∈ X) ∧
      ∃ h : l.prod ∈ Subsemigroup.closure (X : Set (Matrix (Fin d) (Fin d) ℚ)),
        ((incl X ⟨l.prod, h⟩ : closureSG X) : c.Quotient) = ((incl X a : closureSG X) : c.Quotient)

end MatSemiBurnside.Supplement


