-- Prove2me | Definitions.Def_OAI_Combinatorics_ParityLifts_Masses
-- name    : OAI_Combinatorics_ParityLifts_Masses
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T04:05:23.44461+00:00
-- url     : https://prove2.me/theorems/0f9141eb-ac82-4c61-9952-5ecf6db02d78
-- title:
--   Type masses and tested masses of a weighted witness
-- statement:
--   Let $T$ be a graph on a vertex set $A$, $F$ a graph on a finite set $W$, $a\colon F\to T$ a graph homomorphism and $b\colon A\to\mathbb{F}_2$. Let $w$ be a weighted witness for $(a,b)$: vertex weights $s\colon W\to\mathbb{F}_2$ and symmetric edge weights $r$ supported on $E(F)$ with $\sum_{y:\,a(y)=u}r(x,y)=s(x)$ for all $x\in W$ and $u\in N_T(a(x))$, and $\sum_{x}s(x)\,b(a(x))=1$. For a set $Y\subseteq W$ and a type $u\in A$ define:
--
--   1. **Type mass.**
--   $$
--   m_u(Y)=\sum_{\substack{x\in Y\\ a(x)=u}}s(x)\in\mathbb{F}_2,
--   $$
--   the total weight of the vertices of $Y$ of type $u$.
--   2. **Tested mass.** For a predicate $p\colon W\to\mathbb{F}_2$,
--   $$
--   m_u(Y;p)=\sum_{\substack{x\in Y\\ a(x)=u}}s(x)\,p(x)\in\mathbb{F}_2 .
--   $$
--   In particular $m_u(Y;1)=m_u(Y)$.
--
--   Type masses are the bookkeeping of the separator argument. Results built on them show that two adjacent types $u,v$ have equal mass on $Y$ whenever all outside neighbours of $Y$ lie in a set containing no vertex of type $u$ or $v$, and that for the star parity on the template $T_t$ (with $t\ge1$) every main type has total mass $m_i(W)=1$. Tested masses refine this with label predicates: they transport a mismatch test across a separator, which is how an incompatible choice of representatives is turned into a contradiction.
--
--   **Formalization Note** These are `WeightedWitness.mass w Y u` and `WeightedWitness.testMass w Y u p`, with `Y` a `Finset W` and all sums in `Bit := ZMod 2`. A section on template masses contains no declarations.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/ParityLifts/Masses.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ParityLifts/Masses.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ParityLifts mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ParityLifts
import Definitions.Def_OAI_Combinatorics_ParityLifts_LiftCounts
import Definitions.Def_OAI_Combinatorics_ParityLifts_WeightedDual

namespace OAI

namespace ParityWL

open scoped BigOperators

section Masses

open scoped Classical

variable {A W : Type} [Fintype W]
variable {T : SimpleGraph A} {F : SimpleGraph W} {a : F →g T} {b : A → Bit}

noncomputable def WeightedWitness.mass (w : WeightedWitness T F a b)
    (Y : Finset W) (u : A) : Bit :=
  ∑ x ∈ Y, if a x = u then w.vertex x else 0

end Masses

section TemplateMass

open scoped Classical

variable {t : ℕ} {W : Type} [Fintype W] {F : SimpleGraph W}
variable {a : F →g template t}

end TemplateMass

section BoundaryTests

open scoped Classical

variable {A W : Type} [Fintype W]
variable {T : SimpleGraph A} {F : SimpleGraph W} {a : F →g T} {b : A → Bit}

noncomputable def WeightedWitness.testMass (w : WeightedWitness T F a b)
    (Y : Finset W) (u : A) (p : W → Bit) : Bit :=
  ∑ x ∈ Y, if a x = u then w.vertex x * p x else 0

end BoundaryTests

end ParityWL

end OAI


