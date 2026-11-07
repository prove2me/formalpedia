-- Prove2me | Definitions.Def_LosslessQLTC_Paths
-- name    : LosslessQLTC_Paths
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:19:48.772476+00:00
-- url     : https://prove2.me/theorems/16f37812-4f46-41fc-bb6e-a80ac3a2625a
-- title:
--   Ordered paths, the non-colliding set $G$, and the map $\varphi$
-- statement:
--   Fix $v\in V_\emptyset$. For an ordering $\pi$ of $I\subseteq[k]$ and $x\in\mathrm{Lk}_I(v)$, the **fiber** $\mathrm{End}_\pi^{-1}(x)$ is the set of monotone paths $(x_0,\dots,x_i)$ with $x_0=v$, $x_i=x$, $x_{j-1}\lessdot x_j$ and $\mathrm{type}(x_j)\setminus\mathrm{type}(x_{j-1})=\{\pi(j)\}$. The **non-colliding set** is $G=\mathrm{Lk}(v)\setminus B$, where $x$ is bad when $\mu_I(x)=|\mathrm{End}_\pi^{-1}(x)|-1>0$ for a reference ordering $\pi$ of its type $I$. For $x_I\in G$,
--
--   $$\varphi(x_I)=\{x_{\{j\}}\in\mathrm{Lk}_{\{j\}}(v):x_{\{j\}}\le x_I,\ j\in I\}$$
--
--   is a face of the complete $k$-partite complex whose $j$-th part is $\mathrm{Lk}_{\{j\}}(v)$. These objects compare a link with a complete multipartite complex.
--
--   **Formalization Note.** Paths are functions on $\{0,\dots,i\}$, an ordering is a duplicate-free list, and the reference ordering is the increasing one; Lemma 3.3 shows the choice does not matter. A face of the multipartite complex is recorded by its vertex set.
-- source:
--   Cohen, Leigh, Reiner, Ta-Shma, Tzalik, Good Quantum Locally Testable Codes from Lossless Cubical Complexes, arXiv:2610.00525 (held version, sha256 d61f0ed9…), §3.1–3.2, pp.21–24

import Mathlib
import Definitions.Def_LosslessQLTC_Link

namespace LosslessQLTC

variable {k : ℕ}

/-- `π` is an ordering of `I`: it lists every direction of `I` exactly once
(arXiv:2610.00525, held version, sha256 d61f0ed9…, p.21). -/
def IsOrdering (π : List (Fin k)) (I : Finset (Fin k)) : Prop :=
  π.Nodup ∧ π.toFinset = I

/-- The fiber `End_π⁻¹(x)` of p.21: the monotone paths `(x_0, …, x_i)` with `x_0 = v`, `x_i = x`,
`x_{j−1} ⋖ x_j`, and `type(x_j) ∖ type(x_{j−1}) = {π(j)}`. -/
def fiber (X : SquareComplex k) (v : X.Vtx) (π : List (Fin k)) (x : X.Vtx) :
    Finset (Fin (π.length + 1) → X.Vtx) :=
  Finset.univ.filter fun p =>
    p 0 = v ∧ p (Fin.last _) = x ∧
      ∀ j : Fin π.length, X.up (p j.castSucc) (p j.succ) ∧
        X.type (p j.succ) = insert (π.get j) (X.type (p j.castSucc))

open scoped Classical in
/-- The non-colliding set `G = Lk(v) ∖ B` of p.23, for `v ∈ V_∅`: `x ∈ Lk(v)` is good when
`μ_I(x) = |End_π⁻¹(x)| − 1` is not positive, where `I = type x`.

**Formalization Note.** The source fixes an arbitrary reference ordering of each `I`; here it is the
increasing one. By Lemma 3.3 the fiber size does not depend on the ordering. -/
noncomputable def goodSet (X : SquareComplex k) (v : X.Vtx) : Finset X.Vtx :=
  Finset.univ.filter fun x =>
    Relation.ReflTransGen X.up v x ∧ (fiber X v ((X.type x).sort (· ≤ ·)) x).card ≤ 1

open scoped Classical in
/-- The map `φ` of p.24, for `v ∈ V_∅`: `φ(x_I) = {x_{j} ∈ Lk_{j}(v) : x_{j} ≤ x_I, j ∈ I}`. A face
of the complete `k`-partite complex `M` with `j`-th part `Lk_{j}(v)` is recorded as its set of
vertices. The condition `j ∈ I` follows from `x_{j} ≤ x_I`. -/
noncomputable def phi (X : SquareComplex k) (v x : X.Vtx) : Finset X.Vtx :=
  Finset.univ.filter fun y =>
    (∃ j, y ∈ LkType X v {j}) ∧ Relation.ReflTransGen X.up y x

end LosslessQLTC


