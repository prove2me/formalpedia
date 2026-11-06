-- Prove2me | Definitions.Def_PolymatroidCover_IsPolymatroid
-- name    : PolymatroidCover_IsPolymatroid
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:18:24.611634+00:00
-- url     : https://prove2.me/theorems/13d6ac36-2dde-4d9a-b8b5-14a892993f4d
-- title:
--   Polymatroid $f : 2^E \to \mathbb Z_{\ge 0}$
-- statement:
--   Let $E$ be a finite ground set. A set function $f : 2^E \to \mathbb Z_{\ge 0}$ is a **polymatroid** if it is integer-valued and
--
--   1. normalized: $f(\emptyset) = 0$;
--   2. monotone non-decreasing: $f(B) \le f(A)$ whenever $B \subseteq A \subseteq E$;
--   3. submodular: $f(A) + f(B) \ge f(A \cap B) + f(A \cup B)$ for all $A, B \subseteq E$.
--
--   We write $f(e) := f(\{e\})$. Matroid rank functions are the polymatroids with $f(e) \le 1$; sums of $d$ matroid rank functions are polymatroids with $f(e) \le d$. This is the basic object of the mission: every statement is about a polymatroid given through its values.
--
--   **Formalization Note** The ground set is `Fin n` and the codomain `ℕ` encodes $\mathbb Z_{\ge 0}$ (integrality is essential: several arguments use that a negative integer is at most $-1$).
-- source:
--   Bérczi, Chandrasekaran, Chekuri, Liu, Ravi, Approximate Covering and Packing in Polymatroids, STOC 2027 submission (manuscript sha256 47f38a6f…), §1.1, p.2 (PDF p.4)

import Mathlib

namespace PolymatroidCover

/-- A polymatroid on the ground set `E = Fin n` (Bérczi–Chandrasekaran–Chekuri–Liu–Ravi, *Approximate Covering and Packing in Polymatroids*, STOC 2027 submission (manuscript sha256 47f38a6f…), §1.1, printed p.2 = PDF p.4):
a set function `f : 2^E → ℤ_{≥0}` that is integer-valued, monotone non-decreasing
(`f B ≤ f A` whenever `B ⊆ A`), submodular (`f (A ∩ B) + f (A ∪ B) ≤ f A + f B`) and
satisfies `f ∅ = 0`.

**Formalization Note** The ground set `E` is `Fin n` (the paper's `E` is finite: it sums
over `E` and uses `|E|`). Integer values in `ℤ_{≥0}` are encoded by the codomain `ℕ`;
every subtraction involving `f` elsewhere in the mission is done after casting to `ℤ`. -/
def IsPolymatroid {n : ℕ} (f : Finset (Fin n) → ℕ) : Prop :=
  f ∅ = 0 ∧ (∀ A B : Finset (Fin n), B ⊆ A → f B ≤ f A) ∧
    ∀ A B : Finset (Fin n), f (A ∩ B) + f (A ∪ B) ≤ f A + f B

end PolymatroidCover


