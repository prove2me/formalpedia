-- Prove2me | Definitions.Def_GreedNorm_OPT
-- name    : GreedNorm_OPT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:47:11.482278+00:00
-- url     : https://prove2.me/theorems/b00accd0-8cbb-4f7f-aec7-9e9ffb70498d
-- title:
--   Optimal generalized makespan $\mathrm{OPT}$
-- statement:
--   For a GLB instance with $n$ jobs and $m\ge 1$ machines,
--
--   $$
--   \mathrm{OPT}=\min_{\sigma:J\to M} g\bigl(\mathrm{load}(\sigma)\bigr),
--   $$
--
--   the minimum over all $m^n$ assignments. Since $m\ge1$ the set of assignments is finite and nonempty, so the minimum exists and is attained.
--
--   **Formalization Note** `Finset.inf'` over `Fin n → Fin m`, with the nonemptiness witness built from the argument `0 < m`; there is no default value.
-- source:
--   Gan–Huang–Umboh, Greed is All You Need: An Approximation Algorithm Framework for Nested Norm Covering and Packing Problems, manuscript (STOC 2027 submission, held version sha256 2a3d250c…a300b1b6), Definition 1.1, p.1 (PDF 3)

import Mathlib
import Definitions.Def_GreedNorm_glbCost

namespace GreedNorm

/-- **The optimal generalized makespan** `OPT = min_σ g(load(σ))` of a GLB instance.
Gan–Huang–Umboh, *Greed is All You Need: An Approximation Algorithm Framework for Nested Norm
Covering and Packing Problems*, manuscript (STOC 2027 submission, held version sha256 2a3d250c…a300b1b6), Definition 1.1, p.1 (PDF 3): "The goal is to compute an assignment σ that minimizes the
generalized makespan g (load(σ))."

**Formalization Note** The minimum is `Finset.inf'` over all `m^n` assignments
`Fin n → Fin m`, which is a finite set, nonempty because `0 < m` (the argument `hm`); so
`OPT` is the true minimum and is attained, with no junk value. -/
noncomputable def OPT {n m : ℕ} (hm : 0 < m) (p : Fin m → Fin n → ℝ)
    (f : Fin m → (Fin n → ℝ) → ℝ) (g : (Fin m → ℝ) → ℝ) : ℝ :=
  Finset.univ.inf' ⟨fun _ => ⟨0, hm⟩, Finset.mem_univ _⟩ (glbCost p f g)

end GreedNorm


