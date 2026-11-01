-- Prove2me | Definitions.Def_WildeQIT_Schumacher_compressionLimit
-- name    : WildeQIT_Schumacher_compressionLimit
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T18:38:24.157842+00:00
-- url     : https://prove2.me/theorems/1b54e55b-3b41-43ea-87a3-c678c12849d2
-- title:
--   Quantum data compression limit of $\rho$
-- statement:
--   The quantum data compression limit of a density operator $\rho$ is the infimum of all achievable quantum compression rates:
--
--   $$
--   \inf\{R \in \mathbb R : R \text{ is an achievable quantum compression rate for } \rho\}.
--   $$
--
--   **Formalization Note** Lean's real `sInf` is $0$ on an empty set or a set unbounded below. The theorem about the limit also asserts that the set of achievable rates is nonempty and bounded below, so the junk value is never used.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, §18.1, p. 523

import Definitions.Def_WildeQIT_Schumacher_IsAchievableRate

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, §18.1, p. 523.
-/

namespace WildeQIT.Schumacher

/-- **Quantum data compression limit** (Wilde, arXiv:1106.1445v8, §18.1, p. 523): "The quantum
data compression limit of `ρ` is equal to the infimum of all achievable quantum compression
rates."

**Formalization Note.** `sInf` on `ℝ` returns `0` on an empty set or a set unbounded below;
statements about the limit also assert that the set of achievable rates is nonempty and bounded
below, so the junk value is never used. -/
noncomputable def compressionLimit {a : Type} [Fintype a] [DecidableEq a]
    (ρ : Matrix a a ℂ) : ℝ :=
  sInf {R : ℝ | IsAchievableRate ρ R}

end WildeQIT.Schumacher


