-- Prove2me | Definitions.Def_AggCG_gapClosed
-- name    : AggCG_gapClosed
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:07:20.605069+00:00
-- url     : https://prove2.me/theorems/53208343-8f56-4f17-9166-d5119d299cb8
-- title:
--   The values $\mathrm{LP}(I)$, $\mathrm{IP}(I)$, $\mathrm{LP}(I_u)$ and the gap closed $g_u(I)$
-- statement:
--   For a program $I$ and $u\in[0,1]^m$, let $\mathrm{LP}(I)$ be the supremum of $c^\top z$ over the LP relaxation, $\mathrm{IP}(I)$ the supremum over its integer points, and $\mathrm{LP}(I_u)$ the supremum over the relaxation with the cut (19) appended. The **fraction of the initial root gap closed** is
--   $$g_u(I)=\frac{\mathrm{LP}(I)-\mathrm{LP}(I_u)}{\mathrm{LP}(I)-\mathrm{IP}(I)}.$$
--   An **integer optimum** is an integer point of the relaxation with the largest objective among integer points.
--
--   This is the second performance measure tuned in the mission, next to the tree size.
--
--   **Formalization Note** The values are real suprema and $g_u$ uses real division. The source defines $g_u$ when $\mathrm{LP}(I)>\mathrm{IP}(I)$. Lemma I.1 proves that on every gadget the regions are nonempty and bounded and the denominator is positive, so no junk value is read.
-- source:
--   Sharma, Computational Complexity of Data-Driven Configuration for Integer Programming, Clustering, and Learning Algorithms, STOC 2027 submission (manuscript sha256 f7ea0248…), §I.1, p.49 (PDF p.50)

import Mathlib
import Definitions.Def_AggCG_IP

namespace AggCG

namespace IP

variable {m n : ℕ}

/-- `LP(I)`, the value of the LP relaxation (Sharma, *Computational Complexity of Data-Driven Configuration for Integer Programming, Clustering, and Learning Algorithms*, STOC 2027 submission (manuscript sha256 f7ea0248…), §I.1, p.49, PDF p.50).

**Formalization Note** A real `sSup`: it is the source's value when the region is nonempty and bounded, which holds on every
gadget. No statement about the values is made off the gadgets. -/
noncomputable def LPval (I : IP m n) : ℝ := sSup (I.objective '' I.nodeRegion none [])

/-- `IP(I)`, the integer optimum over the integer points of the relaxation (p.49). -/
noncomputable def IPval (I : IP m n) : ℝ :=
  sSup (I.objective '' {z | z ∈ I.nodeRegion none [] ∧ IsIntegralPt z})

/-- `LP(I_u)`, the value of the LP with the cut (19) appended (p.49). -/
noncomputable def LPcutVal (I : IP m n) (u : Fin m → ℝ) : ℝ :=
  sSup (I.objective '' I.nodeRegion (some (I.cutOf u)) [])

/-- `z` is an optimum of the integer program. -/
def IsIntOpt (I : IP m n) (z : Fin n → ℝ) : Prop :=
  z ∈ I.nodeRegion none [] ∧ IsIntegralPt z ∧
    ∀ z' ∈ I.nodeRegion none [], IsIntegralPt z' → I.objective z' ≤ I.objective z

/-- The fraction of the root gap closed, `g_u(I) = (LP(I) − LP(I_u))/(LP(I) − IP(I))` (p.49).

**Formalization Note** Real division. The source defines `g_u` "when LP(I) > IP(I)", and Lemma I.1 proves the denominator
positive on every gadget (`lemma_I_1`), so the junk value at `0` is never read. -/
noncomputable def gapClosed (I : IP m n) (u : Fin m → ℝ) : ℝ :=
  (I.LPval - I.LPcutVal u) / (I.LPval - I.IPval)

end IP

end AggCG


