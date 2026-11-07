-- Prove2me | Definitions.Def_MaxEntOCRS_schemeStep
-- name    : MaxEntOCRS_schemeStep
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:33:50.282648+00:00
-- url     : https://prove2.me/theorems/c6273bde-49ed-427f-b385-6d67319f866f
-- title:
--   One step of the simulate-then-replace scheme (law transform)
-- statement:
--   Let $p$ be the law of the current matching and let edge $e$ arrive. The scheme removes $e$ from the current matching $M$, giving $M_0 = M \setminus\{e\}$; if $e$ is active (probability $x_e$) and addable ($M_0 \cup \{e\}$ is a matching), it adds $e$ with probability $\theta_e/x_e$. Edges with $x_e = 0$ are skipped. The new law sends, from each $M$,
--
--   1. mass $x_e \cdot \theta_e/x_e$ to $M_0\cup\{e\}$ and the rest to $M_0$, if $M_0 \cup \{e\}$ is a matching;
--   2. all mass to $M_0$, otherwise.
--
--   **Formalization Note** Activations are independent across edges and each is revealed only at its edge's arrival, so one independent activation coin and one acceptance coin per step give the exact law of the scheme. The acceptance probability is computed from the initial distribution $\mu$.
-- source:
--   Chen–Wang, Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality, STOC 2027 submission (manuscript sha256 06944af9…), Section 2, p.4

import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_MaxEntOCRS_acceptProb

namespace MaxEntOCRS

open Classical in
/-- One step of the simulate-then-replace scheme (Chen–Wang, *Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality*, STOC 2027 submission manuscript (sha256 06944af9…2d0462c), §2, p.4), as a transform of the law
`p` of the current matching when edge `e` arrives: "it removes e from the current matching,
and if e is active and addable it adds e with probability θe/xe; edges with xe = 0 are
skipped". From a current matching `M`, with `M₀ = M ∖ {e}`: if `M₀ ∪ {e}` is a matching, the
mass `x_e · acceptProb` goes to `M₀ ∪ {e}` and the rest to `M₀`; otherwise all of it goes to
`M₀`. If `x_e = 0` the law is unchanged. `μ` is the initial (maximum-entropy) distribution,
which fixes the acceptance probabilities.

**Formalization Note** Activations are independent across edges and each is revealed only at
its edge's arrival, so one independent Bernoulli(`x_e`) activation coin and one independent
acceptance coin per step give exactly the law of the scheme. -/
noncomputable def schemeStep {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] (G : EdmondsMatching65.Polyhedron.Graph V E) (x : E → ℝ) (μ : Finset E → ℝ) (e : E)
    (p : Finset E → ℝ) : Finset E → ℝ :=
  fun N => if x e = 0 then p N else
    ∑ M, p M *
      (if EdmondsMatching65.Polyhedron.IsMatching G (insert e (M.erase e)) then
        (if N = insert e (M.erase e) then x e * acceptProb G x μ e else 0) +
          (if N = M.erase e then 1 - x e * acceptProb G x μ e else 0)
      else (if N = M.erase e then 1 else 0))

end MaxEntOCRS


