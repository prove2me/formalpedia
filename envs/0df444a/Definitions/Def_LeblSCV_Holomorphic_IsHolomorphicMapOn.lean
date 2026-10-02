-- Prove2me | Definitions.Def_LeblSCV_Holomorphic_IsHolomorphicMapOn
-- name    : LeblSCV_Holomorphic_IsHolomorphicMapOn
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T02:00:30.271855+00:00
-- url     : https://prove2.me/theorems/d9777e2b-2a90-4d8f-9d70-119ef95d5bd0
-- title:
--   Definition 1.3.4 — holomorphic mapping into $\mathbb{C}^m$
-- statement:
--   Let $U \subset \mathbb{C}^n$ be open. A mapping $f = (f_1, \dots, f_m) : U \to \mathbb{C}^m$ is **holomorphic** if each component $f_k : U \to \mathbb{C}$ is a holomorphic function in the sense of Definition 1.1.2 (locally bounded and complex-differentiable in each variable separately).
--
--   **Formalization Note.** $\mathbb{C}^m$ is `Fin m → ℂ`, and the $j$-th component of $f$ is `fun z => f z j`.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 29, Definition 1.3.4

import Mathlib
import Definitions.Def_LeblSCV_Holomorphic_IsHolomorphicOn

namespace LeblSCV.Holomorphic

/-- Definition 1.3.4 (Lebl, p. 29). A mapping `f = (f_1, …, f_m) : U → ℂᵐ` on an open set
`U ⊆ ℂⁿ` is holomorphic if each component `f_j` is holomorphic in the sense of Definition 1.1.2. -/
def IsHolomorphicMapOn {n m : ℕ} (f : (Fin n → ℂ) → (Fin m → ℂ)) (U : Set (Fin n → ℂ)) : Prop :=
  ∀ j : Fin m, IsHolomorphicOn (fun z => f z j) U

end LeblSCV.Holomorphic


