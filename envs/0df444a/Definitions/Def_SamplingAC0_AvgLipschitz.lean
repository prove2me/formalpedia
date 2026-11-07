-- Prove2me | Definitions.Def_SamplingAC0_AvgLipschitz
-- name    : SamplingAC0_AvgLipschitz
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:47:49.130406+00:00
-- url     : https://prove2.me/theorems/e102638f-ba73-4ba5-9095-d49951a98398
-- title:
--   Average-$\mu$-Lipschitz forest
-- statement:
--   Let $f=(f_i)_{i\in\iota}$ be a decision forest on $s$ input bits and $\rho$ a restriction. For a free bit $j$ let $\theta_j$ be the number of trees $f_i$ whose path on the input $U\sim(U\mid\rho)$ queries $j$. The restricted forest $f|_\rho$ is **average-$\mu$-Lipschitz** if
--
--   $$\mathbb E[\theta_j]\le\mu\qquad\text{for every bit } j \text{ left free by } \rho .$$
--
--   For the empty restriction this is the paper's definition: $f$ is average-$\mu$-Lipschitz if $\mathbb E[\theta_j]\le\mu$ for every $j\in[s]$, with $U$ uniform on $\{0,1\}^s$. It is the key concept of the lower bound (Lemmas 11, 12, 15).
--
--   **Formalization Note** $\theta_j$ counts trees, not queries: a tree that queries $j$ twice on its path counts once. On inputs extending $\rho$ a tree of $f|_\rho$ queries a free bit exactly when the corresponding tree of $f$ does, and the fixed bits are not inputs of $f|_\rho$, so only free bits are constrained.
-- source:
--   Riazanov–Viola, Sampling Tools and the Power of AC0, STOC 2027 submission (manuscript sha256 99c33d30…), §3, p.8 (average Lipschitzness)

import Mathlib
import Definitions.Def_SamplingAC0_Forest
import Definitions.Def_SamplingAC0_law
import Definitions.Def_SamplingAC0_Restriction
set_option autoImplicit false

namespace SamplingAC0

/-- **Average Lipschitzness of a restricted forest.** Riazanov–Viola, *Sampling Tools and the Power
of AC0*, STOC 2027 submission (manuscript sha256 99c33d30…), §3, p.8: "Let θ_j denote the number of
trees in f that query j on the input U ∼ {0, 1}^s. We then say that f is average-μ-Lipschitz if
E[θ_j] ≤ μ for every j ∈ [s]."

`AvgLipschitz f ρ μ` says that the restricted forest `f|ρ` is average-`μ`-Lipschitz: for every bit
`j` left free by `ρ`, the expected number of trees of `f` whose path queries `j`, on an input
`U` uniform among the inputs extending `ρ`, is at most `μ`.

**Formalization Note.** `θ_j` counts trees, not queries (a tree querying `j` twice counts once).
With `ρ = Restriction.empty s` this is the definition on p.8 for `f` itself. On inputs extending
`ρ` a tree of `f|ρ` queries a free bit exactly when the corresponding tree of `f` does, and the
fixed bits are not inputs of `f|ρ`, so only free `j` are constrained. -/
def AvgLipschitz {s : ℕ} {ι : Type} [Fintype ι] (f : Forest s ι) (ρ : Restriction s) (μ : ℝ) :
    Prop :=
  ∀ j : Fin s, ρ j = none →
    expect (condRestr ρ)
      (fun x => ((Finset.univ.filter (fun i => j ∈ queriedSet (f i) x)).card : ℝ)) ≤ μ

end SamplingAC0


