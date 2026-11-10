-- Prove2me | Definitions.Def_SetDefinedGraphs_Classes
-- name    : SetDefinedGraphs_Classes
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:26:17.734029+00:00
-- url     : https://prove2.me/theorems/49ad693f-368a-470d-97dc-aad8056234c9
-- title:
--   The classes $\vec{\mathcal X}_f$, $\vec{\mathcal X}'_f$, $\vec{\mathcal Y}_f$ and $\vec{\mathcal X}_{f,P}$ of set-defined digraphs
-- statement:
--   A digraph is **$(d,f)$-set-defined** if it is isomorphic to the realisation of $f$ over some finite $V\subseteq\mathbb N^d$. Following Definition 3.1 and §4.2:
--
--   1. $\vec{\mathcal X}_f$ is the full class of $(d,f)$-set-defined digraphs;
--   2. $\vec{\mathcal X}'_f$ consists of the digraphs isomorphic to a realisation of $f$ over a finite **injective** set $V\subseteq\mathbb N^{\underline d}$;
--   3. $\vec{\mathcal Y}_f$ consists of those isomorphic to a realisation of $f$ over a finite **injective order-uniform** set;
--   4. for a partition $P$ of $[d]$, $\vec{\mathcal X}_{f,P}$ consists of those isomorphic to a realisation of $f$ over a finite **$P$-homogeneous** set.
--
--   For a Boolean formula $F$ representing $f$ (for instance a DNF), $\vec{\mathcal X}_F,\vec{\mathcal X}'_F,\vec{\mathcal Y}_F$ denote the same classes. A **set-defined class** (Definition 1.1) is a hereditary class contained in some $\vec{\mathcal X}_f$.
--
--   **Formalization Note** Each class is a predicate on digraphs over an arbitrary vertex type, closed under isomorphism by construction. The vertex sets are finite, as in the paper's definition ("a finite set $V\subseteq\mathbb N^d$", p.2).
-- source:
--   Adenwalla, Braunfeld, Hons, Sylvester, Zamaraev, Set-defined graph classes: χ-boundedness meets tropical algebra, arXiv:2607.23754 (held version, sha256 642c0d70…), §1.1 p.2 (PDF p.4), Definition 1.1; §3.1 pp.14–15, Definition 3.1 (PDF p.17); §4.2 p.25 (X⃗_{f,P})

import Mathlib
import Definitions.Def_FASTournament_Isomorphic
import Definitions.Def_SetDefinedGraphs_DigraphBasics
import Definitions.Def_SetDefinedGraphs_realisation
import Definitions.Def_SetDefinedGraphs_VectorSets

set_option autoImplicit false

namespace SetDefinedGraphs

/-- `G ∈ X⃗_f`: the digraph `G` is **`(d, f)`-set-defined**, i.e. isomorphic to the realisation of `f` over some finite
set `V ⊆ ℕ^d` (Adenwalla–Braunfeld–Hons–Sylvester–Zamaraev, *Set-defined graph classes: χ-boundedness meets tropical
algebra*, arXiv:2607.23754 (held version, sha256 642c0d70…), §1.1 p.2, Definition 1.1; §3.1 p.14, Definition 3.1 p.15).
`X⃗_f` is the full class of `(d, f)`-set-defined digraphs.

**Formalization Note** Classes of digraphs are predicates on digraphs `G : Digraph W` over arbitrary vertex types,
closed under isomorphism by construction. The finiteness of `V` is the paper's ("a finite set V ⊆ ℕ^d", p.2). -/
def InX {d : ℕ} (f : (Fin d → Fin d → Bool) → Bool) {W : Type} (G : Digraph W) : Prop :=
  ∃ V : Set (Fin d → ℕ), V.Finite ∧ FASTournament.Isomorphic G (realisation f V)

/-- `G ∈ X⃗′_f`: `G` admits a realisation of `f` over a finite **injective** set `V ⊆ ℕ^d̲` (Definition 3.1, p.15). -/
def InX' {d : ℕ} (f : (Fin d → Fin d → Bool) → Bool) {W : Type} (G : Digraph W) : Prop :=
  ∃ V : Set (Fin d → ℕ), V.Finite ∧ IsInjectiveSet V ∧ FASTournament.Isomorphic G (realisation f V)

/-- `G ∈ Y⃗_f`: `G` admits a realisation of `f` over a finite **injective order-uniform** set `V ⊆ ℕ^d̲`
(Definition 3.1, p.15). -/
def InY {d : ℕ} (f : (Fin d → Fin d → Bool) → Bool) {W : Type} (G : Digraph W) : Prop :=
  ∃ V : Set (Fin d → ℕ), V.Finite ∧ IsInjectiveSet V ∧ IsOrderUniform V ∧ FASTournament.Isomorphic G (realisation f V)

/-- `G ∈ X⃗_{f,P}`: `G` is isomorphic to the realisation of `f` over a finite **`P`-homogeneous** set `V ⊆ ℕ^d`
(§4.2, p.25). -/
def InXP {d : ℕ} (f : (Fin d → Fin d → Bool) → Bool) (P : Setoid (Fin d)) {W : Type} (G : Digraph W) : Prop :=
  ∃ V : Set (Fin d → ℕ), V.Finite ∧ IsPHomogeneous P V ∧ FASTournament.Isomorphic G (realisation f V)

end SetDefinedGraphs


