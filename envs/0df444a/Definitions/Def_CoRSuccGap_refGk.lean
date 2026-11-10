-- Prove2me | Definitions.Def_CoRSuccGap_refGk
-- name    : CoRSuccGap_refGk
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:48:29.515762+00:00
-- url     : https://prove2.me/theorems/27e0c0b8-9103-45a4-8c05-19d6899c66c6
-- title:
--   The reference structure $\mathcal M_0$ for $G_k$: $P_i$ on colours containing $i$, $Q_i$ on colours not containing $i$
-- statement:
--   Let $\chi$ colour the pairs of distinct vertices of $V$ with the palette $\Lambda=2^{[k]}$. The **reference structure** $\mathcal M_0$ for $G_k$ on $V$ interprets, on an edge of colour $\mu$, $P_i$ as true precisely when $i\in\mu$ and $Q_i$ as true precisely when $i\notin\mu$, and sets both to false on every loop:
--
--   $$
--   P_i^{\mathcal M_0}:=\bigcup_{\mu\in\Lambda:\ i\in\mu}e_\mu,\qquad Q_i^{\mathcal M_0}:=\bigcup_{\mu\in\Lambda:\ i\notin\mu}e_\mu ,
--   $$
--
--   where $e_\mu$ is the set of ordered pairs $(u,v)$, $u\neq v$, of colour $\mu$.
--
--   On $\mathcal M_0$ the relation $H_\mu$ of §1.1 is exactly the colour class $e_\mu$; Lemma 3.6 uses $\mathcal M_0$ and its folds as the tests that force $2^k$ folds to be noticed.
--
--   **Formalization Note** `refGk χ (GSym.P i) u v` is $u\neq v\wedge i\in\chi(u,v)$ and `refGk χ (GSym.Q i) u v` is $u\neq v\wedge i\notin\chi(u,v)$, with $P_{i+1},Q_{i+1}$ indexed by $i\in$ `Fin k`. The folded structure $\mathcal M_\lambda$ is `fun r => predict χ h lam (refGk χ r)`.
-- source:
--   Y. Uezato, Y. Nakamura, An Exponential Succinctness Gap between Three-Variable Logic and the Calculus of Relations, arXiv:2609.26778 (held version, sha256 5ad6337daad55bcf6132960d4744d07ff7d67ef2a9aef456f3e3b54ff623c9b6), §3.5, p.22 (PDF 24)

import Mathlib
import Definitions.Def_CoRSuccGap_Gk

set_option autoImplicit false

namespace CoRSuccGap

/-!
# The reference structure M₀ for G_k

Uezato–Nakamura, *An Exponential Succinctness Gap between Three-Variable Logic and the
Calculus of Relations*, arXiv:2609.26778 (held version, sha256 5ad6337d…c9b6), §3.5, p.22 (PDF 24): "On a color μ, interpret P_i as 1 precisely when i ∈ μ, and Q_i as 1
precisely when i ∉ μ. Set both values to zero on every loop. More explicitly,
P_i^{M₀} := ⋃_{μ ∈ Λ : i ∈ μ} e_μ, Q_i^{M₀} := ⋃_{μ ∈ Λ : i ∉ μ} e_μ."

**Formalization Note.** The palette 2^[k] is `Finset (Fin k)` and P_{i+1}, Q_{i+1} are `GSym.P i`,
`GSym.Q i`. On a pair `u ≠ v` of colour μ = χ s(u, v), `P i` holds iff `i ∈ μ` and `Q i` iff
`i ∉ μ`; both are false on loops.
-/

variable {V : Type*} {k : ℕ}

/-- The reference structure M₀ of §3.5 (p.22) on the vertex set `V` coloured by `χ`. -/
def refGk (χ : Sym2 V → Finset (Fin k)) : GSym k → V → V → Prop
  | GSym.P i => fun u v => u ≠ v ∧ i ∈ χ s(u, v)
  | GSym.Q i => fun u v => u ≠ v ∧ i ∉ χ s(u, v)

end CoRSuccGap


