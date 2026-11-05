-- Prove2me | Definitions.Def_DHRUniq_IsMaxEntRep
-- name    : DHRUniq_IsMaxEntRep
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:34:32.761895+00:00
-- url     : https://prove2.me/theorems/40d41f9e-b9ca-450e-8cc8-283a94a038df
-- title:
--   Representative of $|\Psi_+(\mathbb C^d)\rangle$
-- statement:
--   Let $d\ge1$. A wavefunction $\psi$ on an arbitrary bipartite system $\mathbb C^a\otimes\mathbb C^b$ is a **representative** of $|\Psi_+(\mathbb C^d)\rangle$ if it has the same Schmidt coefficients, that is, if it has a Schmidt decomposition with exactly $d$ coefficients, all equal to $1/d$:
--
--   $$
--   |\psi\rangle=\sum_{i=1}^d\frac1{\sqrt d}\,|e_i\rangle\otimes|f_i\rangle .
--   $$
--
--   Its state $|\psi\rangle\langle\psi|$ is a representative of $P_+(\mathbb C^d)$. Normalization (P1) is imposed on all representatives.
-- source:
--   Donald, Horodecki, Rudolph, The uniqueness theorem for entanglement measures, arXiv:quant-ph/0105017v2, Definition 8, p. 7

import Mathlib
import Definitions.Def_DHRUniq_IsSchmidtDecomp

namespace DHRUniq

/-- **Representative of `|Ψ_+(ℂ^d)⟩`** (Donald, Horodecki, Rudolph, *The uniqueness theorem for entanglement measures*, arXiv:quant-ph/0105017v2, Definition 8, p. 7: "In an arbitrary bipartite
composite system, we shall refer to any wavefunction with the same Schmidt coefficients as
`|Ψ_+(ℂ^d)⟩` as a representative of `|Ψ_+(ℂ^d)⟩`"), for `d = 1, 2, …`: a wavefunction on `a × b`
with a Schmidt decomposition having exactly `d` coefficients, all equal to `1/d`.

**Formalization Note** `0 < d` excludes the zero vector at `d = 0`, so a representative is a
unit vector. The local spaces `a`, `b` are arbitrary (they must have at least `d` elements, by
orthonormality); the representative of `P_+(ℂ^d)` is `pureState ψ`. -/
def IsMaxEntRep {a b : Type} [Fintype a] [Fintype b] (d : ℕ) (ψ : a × b → ℂ) : Prop :=
  0 < d ∧ ∃ (e : Fin d → a → ℂ) (f : Fin d → b → ℂ),
    IsSchmidtDecomp ψ (fun _ => 1 / (d : ℝ)) e f

end DHRUniq


