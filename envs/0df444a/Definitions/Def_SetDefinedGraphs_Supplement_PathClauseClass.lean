-- Prove2me | Definitions.Def_SetDefinedGraphs_Supplement_PathClauseClass
-- name    : SetDefinedGraphs_Supplement_PathClauseClass
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T17:42:38.725894+00:00
-- url     : https://prove2.me/theorems/3665c1ee-eb9f-4517-b24e-4327f71756a9
-- title:
--   Loopless path clauses, maximal paths $m$, functional constraints $Z$ and the class $\vec{\mathcal Y}_{P,Z}$
-- statement:
--   Fix $d$ and a full clause $P$ over the variables $q_{i,j}$, $i,j\in[d]$, identified with its clause digraph $\Delta_P$ (an arc $i\to j$ iff $q_{i,j}$ occurs positively).
--
--   1. $P$ is a **loopless path clause** if it is a path clause with no loop coordinates.
--   2. $m$ is the number of **maximal paths** of $\Delta_P$, isolated vertices counted as paths.
--   3. A tuple $Z=((L_1,\lambda_1),\dots,(L_k,\lambda_k))$ of **functional constraints** has $L_s\ne[d]$ and $\lambda_s\in[d]\setminus L_s$; $k$ is the number of constraints. A set $V\subseteq\mathbb N^d$ is **$Z$-functional** if for every $s$ the coordinate $v_{\lambda_s}$ is a function of $v|_{L_s}$ on $V$.
--   4. The class
--   $$\vec{\mathcal Y}_{P,Z}=\{H\simeq G=(V,E): V\subseteq\mathbb N^{\underline d}\text{ is order-uniform }Z\text{-functional, and }G\text{ is a realisation of }P\text{ over }V\}.$$
--
--   Theorem 4.15 reduces $\chi$-boundedness of a full set-defined class to bounded chromatic number of finitely many classes $\vec{\mathcal Y}_{P,Z}$, and Theorem 5.1 decides the latter by tropical algebra.
--
--   **Formalization Note** $m$ is the number of connected components of the underlying graph of $\Delta_P$, which for a loopless path clause are exactly its maximal paths. $Z$ is a list (repeats allowed, as in a tuple). The vertex set $V$ is finite and injective, as everywhere in the paper.
-- source:
--   Adenwalla, Braunfeld, Hons, Sylvester, Zamaraev, Set-defined graph classes: χ-boundedness meets tropical algebra, arXiv:2607.23754 (held version, sha256 642c0d70…), §4.5 pp.30–31 (PDF pp.32–33): loopless path clause, Y⃗_{P,Z}; §3.6 p.18 (PDF p.20): functional sets and constraints; §5.1.1 p.36 (PDF p.38): maximal paths m

import Mathlib
import Definitions.Def_FASTournament_Isomorphic
import Definitions.Def_SetDefinedGraphs_realisation
import Definitions.Def_SetDefinedGraphs_VectorSets
import Definitions.Def_SetDefinedGraphs_Clauses
import Definitions.Def_SetDefinedGraphs_Functional

set_option autoImplicit false

namespace SetDefinedGraphs.Supplement

/-- A full clause is a **loopless path clause** (Adenwalla–Braunfeld–Hons–Sylvester–Zamaraev, *Set-defined graph
classes: χ-boundedness meets tropical algebra*, arXiv:2607.23754 (held version, sha256 642c0d70…), §4.5 p.30, PDF p.32)
if it is a path clause with no loop coordinates. -/
def IsLooplessPathClause {d : ℕ} (P : FullClause (Fin d)) : Prop :=
  IsPathClause P ∧ loopCoords P = ∅

/-- The number `m` of **maximal paths** of the clause digraph `Δ_P` of a full clause `P`, isolated vertices counted as
paths (arXiv:2607.23754, §5.1.1 p.36, PDF p.38).

**Formalization Note** For a loopless path clause every connected component of the underlying graph of `Δ_P` is a
directed path or an isolated vertex, so `m` is the number of connected components of the underlying graph
`SimpleGraph.fromRel` of `Δ_P` on `[d]` (`Fin d`). -/
noncomputable def numMaxPaths {d : ℕ} (P : FullClause (Fin d)) : ℕ :=
  Nat.card (SimpleGraph.fromRel (fun i j : Fin d => P i j = true)).ConnectedComponent

/-- A tuple `Z = ((L₁, λ₁), …, (L_k, λ_k))` of **functional constraints** (arXiv:2607.23754, §3.6 p.18 and §4.5
p.30): `L_s ≠ [d]` and `λ_s ∈ [d] ∖ L_s` for every `s`. The number of constraints `k` is the length of the list (repeats
allowed, as in a tuple).

**Formalization Note** `λ_s ∉ L_s` already forces `L_s ≠ [d]`. -/
def IsFunctionalConstraints {d : ℕ} (Z : List (Finset (Fin d) × Fin d)) : Prop :=
  ∀ p ∈ Z, p.2 ∉ p.1

/-- A set `V ⊆ ℕ^d` is **`Z`-functional** (arXiv:2607.23754, §3.6 p.18) if it is `(L_s, λ_s)`-functional for every
constraint `(L_s, λ_s)` of `Z`. -/
def IsZFunctional {d : ℕ} (Z : List (Finset (Fin d) × Fin d)) (V : Set (Fin d → ℕ)) : Prop :=
  ∀ p ∈ Z, IsFunctionalAt p.1 p.2 V

/-- `G ∈ Y⃗_{P,Z}` (arXiv:2607.23754, §4.5 pp.30–31, PDF pp.32–33): `G` is isomorphic to the realisation of the clause
`P` over a finite set `V ⊆ ℕ^d̲` that is injective, order-uniform and `Z`-functional,
`Y⃗_{P,Z} := {H ≃ G = (V, E) : V ⊆ ℕ^d̲ is order-uniform Z-functional, and G is a realisation of P over V}`.

**Formalization Note** The full clause `P` is the Boolean function `dnfFun {P}` (the DNF with the single clause `P`);
the realisation is the paper's loopless one. Finiteness of `V` is the paper's standing convention for realisations
(p.2). -/
def InYPZ {d : ℕ} (P : FullClause (Fin d)) (Z : List (Finset (Fin d) × Fin d)) (W : Type) (G : Digraph W) : Prop :=
  ∃ V : Set (Fin d → ℕ), V.Finite ∧ IsInjectiveSet V ∧ IsOrderUniform V ∧ IsZFunctional Z V ∧
    FASTournament.Isomorphic G (realisation (dnfFun {P}) V)

end SetDefinedGraphs.Supplement


