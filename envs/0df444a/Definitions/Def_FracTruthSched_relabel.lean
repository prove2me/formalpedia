-- Prove2me | Definitions.Def_FracTruthSched_relabel
-- name    : FracTruthSched_relabel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:28:13.854005+00:00
-- url     : https://prove2.me/theorems/98fed906-3b94-4260-8702-66cb99ae09d6
-- title:
--   Relabelling an input by a task permutation, $(\pi s)_{ie}=s_{i,\pi(e)}$
-- statement:
--   For a permutation $\pi$ of the tasks and an input $s$, the relabelled input $\pi s$ is
--   $$(\pi s)_{ie}=s_{i,\pi(e)}.$$
--   It is used to symmetrize mechanisms over task relabellings (Claim 1) and to state the symmetry property (iv) of Lemma 1.
--
--   **Formalization Note.** With composition $(\gamma\pi)(e)=\gamma(\pi(e))$ one has $\pi(\gamma s)=(\gamma\pi)s$.
-- source:
--   Anastasiadis et al., Tight bounds for fractional and randomized truthful scheduling, arXiv:2611.06642v1, App. A, Symmetrization, p.23

import Mathlib

set_option autoImplicit false

namespace FracTruthSched

/-- **Relabelling an input by a task permutation** (Anastasiadis et al., arXiv:2611.06642v1, App. A,
p.23: "For a permutation π of tasks and an input s, let (πs)_ie = s_{i,π(e)}"):
`relabel π s i e = s i (π e)`.

**Formalization Note.** With Lean's composition `(γ * π) e = γ (π e)`, one has
`relabel π (relabel γ s) = relabel (γ * π) s`, which is the identity `π(γs) = π′s` with
`π′ = γ ∘ π` used in the proof of Claim 1. -/
def relabel {n : ℕ} {τ : Type*} (π : Equiv.Perm τ) (s : Fin n → τ → ℝ) : Fin n → τ → ℝ :=
  fun i e => s i (π e)

end FracTruthSched


