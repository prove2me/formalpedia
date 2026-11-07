-- Prove2me | Definitions.Def_QuadBogolyubov_cubeSet
-- name    : QuadBogolyubov_cubeSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:03:11.802212+00:00
-- url     : https://prove2.me/theorems/9eec879b-311b-4eeb-93ca-972200557248
-- title:
--   The set $\Omega(W)$ of Gowers cubes in $W$
-- statement:
--   The set of **Gowers cubes in $W$** is
--   $$\Omega(W)=\{(u,h_1,h_2,h_3)\in G^4:\ u+\sigma_1h_1+\sigma_2h_2+\sigma_3h_3\in W\text{ for all }\sigma\in\{0,1\}^3\}.$$
--   **Formalization Note** $G^4$ is `G × (Fin 3 → G)` and $\sigma$ is `Fin 3 → ZMod 2`.
-- source:
--   Castro-Silva, Golovnev, Gur, Wolf, A Quadratic Bogolyubov Theorem and Quantum Worst-Case to Average-Case Reductions, STOC 2027 submission (held manuscript, sha256 9d91dee3…), App. D.1, p.55

import Mathlib
import Definitions.Def_QuadBogolyubov_QuadVariety

set_option autoImplicit false

namespace QuadBogolyubov

open Classical in
/-- The set `Ω(W)` of **Gowers cubes in `W`**: tuples `(u, h₁, h₂, h₃) ∈ G⁴` with
`u + σ₁h₁ + σ₂h₂ + σ₃h₃ ∈ W` for all `σ ∈ {0,1}³`.

Castro-Silva, Golovnev, Gur, Wolf, *A Quadratic Bogolyubov Theorem and Quantum Worst-Case to
Average-Case Reductions*, STOC 2027 submission (held manuscript, sha256 9d91dee3…), App. D.1,
p.55: "Ω(W) = {(u, h1, h2, h3) ∈ G⁴ : u + σ1h1 + σ2h2 + σ3h3 ∈ W for all σ ∈ {0, 1}³}."

**Formalization Note.** `G⁴` is `G × (Fin 3 → G)`, the pair `(u, h)`; `σ ∈ {0,1}³` is
`Fin 3 → ZMod 2`. -/
noncomputable def cubeSet {n : ℕ} (W : QuadVariety n) :
    Finset ((Fin n → ZMod 2) × (Fin 3 → Fin n → ZMod 2)) :=
  Finset.univ.filter (fun p => ∀ σ : Fin 3 → ZMod 2, p.1 + ∑ i, σ i • p.2 i ∈ W.carrier)

end QuadBogolyubov


