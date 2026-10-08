-- Prove2me | Definitions.Def_MetricGenerators_IsometryExt_Representation
-- name    : MetricGenerators_IsometryExt_Representation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T03:12:53.399381+00:00
-- url     : https://prove2.me/theorems/905ae46f-f0e3-4737-b7a4-489584fc3059
-- title:
--   Representations of H in G with respect to T, and the candidate procedure C^(i), C* (§2, p. 387)
-- statement:
--   Let $H$ and $G$ be graphs, $T\subseteq V(H)$, and $f:T\to V(G)$.
--
--   **Representation.** Sets $C_u\subseteq V(G)$ ($u\in V(H)$) *represent $H$ in $G$ with respect to $T$* if every $C_u$ is nonempty and
--
--   1. if $t\in T$, $u\in V(H)$ and $x\in C_u$, then $\mu_G(f(t),x)=\mu_H(t,u)$;
--   2. if $uv\in E(H)$ and $x\in C_u$, then there is $y\in C_v$ with $xy\in E(G)$.
--
--   **Candidate procedure.** The initial candidate sets are
--   $$C^{(0)}_u:=\{v\in V(G):\ \mu_G(f(t),v)=\mu_H(t,u)\ \text{for all } t\in T\},\qquad C^{(0)}:=\bigcup_{u\in V(H)}C^{(0)}_u,$$
--   and recursively
--   $$C^{(i+1)}:=\{x\in C^{(i)}:\ \text{if } x\in C^{(i)}_u \text{ and } uv\in E(H), \text{ then some } y\in C^{(i)}_v \text{ has } xy\in E(G)\},\qquad C^{(i+1)}_u:=C^{(i)}_u\cap C^{(i+1)}.$$
--   With $n:=|V(G)|$, set $C^*:=C^{(n)}$ and $C^*_u:=C^{(n)}_u$.
--
--   A representation is a relaxation of an isometry extending $f$ (an extension $\bar f$ gives the singleton representation $C_u=\{\bar f(u)\}$), and the procedure computes the largest candidate family that the two defining conditions allow. Theorem 4 of the paper shows when the relaxation is exact.
--
--   **Formalization Note** The nonemptiness of the sets $C_u$ is part of the definition of a representation; without it the empty family would satisfy (i) and (ii). The paper defines representations for a strong metric generator $T$ and an isometry $f$; those are hypotheses of the theorems, not of the definition. The recursion is carried out on the pair $(C^{(i)},(C^{(i)}_u)_u)$ in the page's union form: the condition on $x$ is tested for every $u$ with $x\in C^{(i)}_u$. Vertex sets of $G$ are Lean `Set`s.
-- source:
--   Sebő and Tannier, On Metric Generators of Graphs, Math. Oper. Res. 29(2):383–393 (2004), DOI 10.1287/moor.1030.0070, p. 387, §2 (C^(0)_u, C^(i), C*; definition of a representation)

import Mathlib
import Definitions.Def_MetricGenerators_IsometryExt_Basic

namespace MetricGenerators.IsometryExt

/-- **Representation** (Sebő and Tannier, *On Metric Generators of Graphs*, Math. Oper. Res.
29(2):383–393 (2004), DOI 10.1287/moor.1030.0070, §2, p. 387). Given graphs `H`, `G`, a set
`T ⊆ V(H)` and a map `f : T → V(G)`, the sets `∅ ≠ C_u ⊆ V(G)` (`u ∈ V(H)`) represent `H` in `G`
with respect to `T` if
* every `C_u` is nonempty;
* (i) if `t ∈ T`, `u ∈ V(H)` and `x ∈ C_u`, then `μ_G(f(t), x) = μ_H(t, u)`;
* (ii) if `uv ∈ E(H)` and `x ∈ C_u`, there exists `y ∈ C_v` with `xy ∈ E(G)`.

Formalization Note: the nonemptiness `∅ ≠ C_u` of the page is part of the definition. The page
defines the notion for a strong metric generator `T` and an isometry `f`; these are hypotheses of
the theorems, not of this definition. -/
def Represents {VH VG : Type*} (H : SimpleGraph VH) (G : SimpleGraph VG) (T : Finset VH)
    (f : ↥T → VG) (C : VH → Set VG) : Prop :=
  (∀ u : VH, (C u).Nonempty) ∧
  (∀ t : ↥T, ∀ u : VH, ∀ x ∈ C u, G.dist (f t) x = H.dist t u) ∧
  (∀ u v : VH, H.Adj u v → ∀ x ∈ C u, ∃ y ∈ C v, G.Adj x y)

/-- **Initial candidate sets** (ibid., §2, p. 387):
`C^(0)_u := {v ∈ V(G) : μ_G(f(t), v) = μ_H(t, u) for all t ∈ T}`. -/
def initialCandidates {VH VG : Type*} (H : SimpleGraph VH) (G : SimpleGraph VG) (T : Finset VH)
    (f : ↥T → VG) (u : VH) : Set VG :=
  {v | ∀ t : ↥T, G.dist (f t) v = H.dist t u}

/-- **The candidate procedure** (ibid., §2, p. 387). Stage `i` is the pair
`(C^(i), (C^(i)_u)_{u ∈ V(H)})`:
* `C^(0) := ⋃_{u ∈ V(H)} C^(0)_u`, with `C^(0)_u` the initial candidates;
* `C^(i+1) := {x ∈ C^(i) : if x ∈ C^(i)_u and uv ∈ E(H), then there is y ∈ C^(i)_v with
  xy ∈ E(G)}`;
* `C^(i+1)_u := C^(i)_u ∩ C^(i+1)`.

Formalization Note: the recursion is the page's union form: the condition on `x` quantifies over
every `u` with `x ∈ C^(i)_u` and every neighbour `v` of `u` in `H`. -/
noncomputable def candidates {VH VG : Type*} (H : SimpleGraph VH) (G : SimpleGraph VG)
    (T : Finset VH) (f : ↥T → VG) : ℕ → Set VG × (VH → Set VG)
  | 0 => (⋃ u, initialCandidates H G T f u, initialCandidates H G T f)
  | i + 1 =>
    let U' : Set VG := {x | x ∈ (candidates H G T f i).1 ∧
      ∀ u v : VH, x ∈ (candidates H G T f i).2 u → H.Adj u v →
        ∃ y ∈ (candidates H G T f i).2 v, G.Adj x y}
    (U', fun u => (candidates H G T f i).2 u ∩ U')

/-- The set `C^(i) ⊆ V(G)` of the procedure (ibid., p. 387). -/
noncomputable def candSet {VH VG : Type*} (H : SimpleGraph VH) (G : SimpleGraph VG)
    (T : Finset VH) (f : ↥T → VG) (i : ℕ) : Set VG :=
  (candidates H G T f i).1

/-- The sets `C^(i)_u ⊆ V(G)` of the procedure (ibid., p. 387). -/
noncomputable def cand {VH VG : Type*} (H : SimpleGraph VH) (G : SimpleGraph VG)
    (T : Finset VH) (f : ↥T → VG) (i : ℕ) (u : VH) : Set VG :=
  (candidates H G T f i).2 u

/-- `C*_u := C^(n)_u` with `n := |V(G)|` (ibid., p. 387). -/
noncomputable def cStar {VH VG : Type*} [Fintype VG] (H : SimpleGraph VH) (G : SimpleGraph VG)
    (T : Finset VH) (f : ↥T → VG) (u : VH) : Set VG :=
  cand H G T f (Fintype.card VG) u

end MetricGenerators.IsometryExt


