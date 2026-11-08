-- Prove2me | Definitions.Def_AsymSpecConn_IsADecomposable
-- name    : AsymSpecConn_IsADecomposable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:39:40.55145+00:00
-- url     : https://prove2.me/theorems/24bae18d-7c12-4044-b65f-2b803cd84921
-- title:
--   $\mathcal A$-decomposable semiring
-- statement:
--   Let $\mathcal A\subseteq\mathcal S\setminus\{0\}$. The semiring $\mathcal S$ is **$\mathcal A$-decomposable** if:
--
--   1. $\mathcal A$ is multiplicatively closed;
--   2. every positive integer lies in $\mathcal A$;
--   3. for every nonzero $s\in\mathcal S$ there is $a\in\mathcal A$ with $a\le s$;
--   4. for every nonzero $s\in\mathcal S$ we have $\widetilde L_{\mathcal A}(s)=1$.
--
--   This is the structural hypothesis under which spectral points can be built from their values on $\mathcal A$.
--
--   **Formalization Note** The standing requirement $\mathcal A\subseteq\mathcal S\setminus\{0\}$ of the definition is included as the first clause of the predicate.
-- source:
--   Vrana and Zuiddam, The asymptotic spectrum of tensors is connected, preprint (STOC 2027 submission, version of November 2, 2026, sha256 85a0b2ac…), Definition 2.1, p.13

import Mathlib
import Definitions.Def_AsymSpecConn_ALength

set_option autoImplicit false

namespace AsymSpecConn

/-- **A-decomposable** (Definition 2.1, p.13 of Vrana and Zuiddam, *The asymptotic spectrum of tensors is connected*, preprint (STOC 2027 submission, version of November 2, 2026, sha256 85a0b2ac…)).

For `A ⊆ S \ {0}`, `S` is A-decomposable if
(a) `A` is multiplicatively closed; (b) every positive integer lies in `A`;
(c) for every nonzero `s` there is `a ∈ A` with `a ≤ s`;
(d) for every nonzero `s`, `L̃_A(s) = 1`.

**Formalization Note** The standing requirement `A ⊆ S \ {0}` of the definition is the first
clause. -/
def IsADecomposable {S : Type*} [CommSemiring S] (P : Preorder S) (A : Set S) : Prop :=
  (∀ a ∈ A, a ≠ 0) ∧
  (∀ a ∈ A, ∀ b ∈ A, a * b ∈ A) ∧
  (∀ m : ℕ, 1 ≤ m → (m : S) ∈ A) ∧
  (∀ s : S, s ≠ 0 → ∃ a ∈ A, P.le a s) ∧
  (∀ s : S, s ≠ 0 → asymALength P A s = 1)

end AsymSpecConn


