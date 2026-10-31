-- Prove2me | Definitions.Def_TractableComposite_IsPolyhedralOn
-- name    : TractableComposite_IsPolyhedralOn
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:50:38.677385+00:00
-- url     : https://prove2.me/theorems/c63cae7c-9f61-4d2f-8ba1-9321cd7ab520
-- title:
--   A polyhedral function on a set
-- statement:
--   A function $f$ is polyhedral on $D$ if there are finitely many affine functions $s\mapsto\langle\alpha_k,s\rangle+\beta_k$, each at least $f$ on $D$, such that at every point of $D$ one of them equals $f$; that is, $f$ is their minimum on $D$ (for a polytope $D$, its hypograph over $D$ is a polyhedron). Proposition 2 and Lemma 3 assume that $\operatorname{conc}_Q(\bar\phi)$ is polyhedral.
-- source:
--   He & Tawarmalani, Tractable relaxations of composite functions (manuscript, sha256 8c6bca18…), Proposition 2, p.6, and Lemma 3, p.14

import Mathlib
import Definitions.Def_TractableComposite_ip

namespace TractableComposite

/-- **A polyhedral (concave) function on a set D**, the hypothesis of Proposition 2, p.6 and Lemma 3,
p.14 ("conc_Q(φ̄) is a polyhedral function"): there are finitely many affine functions
`s ↦ ⟨αₖ, s⟩ + βₖ`, each `≥ f` on `D`, one of which equals `f` at each point of `D`; i.e. `f` is their
minimum on `D`, equivalently its hypograph over `D` is a polyhedron when `D` is a polytope.
He & Tawarmalani, *Tractable relaxations of composite functions* (manuscript, sha256 8c6bca18…), pp.6, 14.

**Formalization Note.** Stated for functions on `ℝ^{d×(n+1)}` (the only use is `f = conc_Q(φ̄)`,
`D = Q`). -/
def IsPolyhedralOn {d n : ℕ} (D : Set (Fin d → Fin (n + 1) → ℝ)) (f : (Fin d → Fin (n + 1) → ℝ) → ℝ) : Prop :=
  ∃ (m : ℕ) (α : Fin m → Fin d → Fin (n + 1) → ℝ) (β : Fin m → ℝ),
    (∀ k, ∀ s ∈ D, f s ≤ ip (α k) s + β k) ∧ ∀ s ∈ D, ∃ k, f s = ip (α k) s + β k

end TractableComposite


