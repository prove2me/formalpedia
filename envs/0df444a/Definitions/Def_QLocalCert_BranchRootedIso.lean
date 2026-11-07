-- Prove2me | Definitions.Def_QLocalCert_BranchRootedIso
-- name    : QLocalCert_BranchRootedIso
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:39:15.746185+00:00
-- url     : https://prove2.me/theorems/64e3c133-2a7c-469e-85d8-7d5ac5d701cc
-- title:
--   Branches of a tree at a vertex and rooted isomorphism $\cong_{\mathrm{rt}}$
-- statement:
--   For rooted trees $T_1,T_2$ with roots $r_1,r_2$, a **rooted isomorphism** is a graph isomorphism $\varphi:V(T_1)\to V(T_2)$ with $\varphi(r_1)=r_2$; one writes $T_1\cong_{\mathrm{rt}}T_2$ when one exists (§2, p.14). For a vertex $v$ of a tree $T$ and a neighbour $u$ of $v$, the **branch of $T$ at $v$ containing $u$** is the connected component of $T-v$ containing $u$, rooted at $u$ (p.36).
--
--   These notions state the rigidity of the tags (Lemma 25).
--
--   **Formalization Note** The branch is the subgraph induced on the vertices reachable from $u$ in $T-v$; `BranchRootedIso G v u H root` says it is rooted-isomorphic to `(H, root)`.
-- source:
--   Jauregui, Miyamoto, Quantum Advantage in Local Certification of Graph Properties, STOC 2027 submission (manuscript sha256 b707143b1ab5511bef4c2b77e1b803f28b32cced25a008516898fd11d28c0451), §2, p.14 (rooted isomorphism); §4, p.36 (branch)

import Mathlib

set_option autoImplicit false

namespace QLocalCert

/-- The vertex set of the branch of `G` at `v` containing `u`: the connected component of `G − v`
containing `u` (empty when `u = v`).

B. Jauregui, M. Miyamoto, *Quantum Advantage in Local Certification of Graph Properties*,
STOC 2027 submission (manuscript sha256 b707143b…0c51), §4, p.36: "For a vertex v of a tree T and a
neighbor u of v, we refer to the branch of T at v containing u as the connected component of T − v
containing u, rooted at u." -/
def branchSet {V : Type} (G : SimpleGraph V) (v u : V) : Set V :=
  {w | ∃ (hu : u ≠ v) (hw : w ≠ v), (G.induce {x | x ≠ v}).Reachable ⟨u, hu⟩ ⟨w, hw⟩}

/-- Rooted isomorphism (§2, p.14): "For rooted trees T₁, T₂ with roots r₁, r₂, a rooted
isomorphism is a graph isomorphism φ : V(T₁) → V(T₂) satisfying φ(r₁) = r₂; we write T₁ ≅_rt T₂
when such an isomorphism exists." -/
def RootedIso {V W : Type} (G : SimpleGraph V) (r : V) (H : SimpleGraph W) (r' : W) : Prop :=
  ∃ φ : G ≃g H, φ r = r'

/-- The branch of `G` at `v` containing `u`, rooted at `u`, is isomorphic as a rooted tree to
`(H, root)` (§4, p.36, with `≅_rt` of §2, p.14).

**Formalization Note.** The branch is the induced subgraph of `G` on `branchSet G v u`; the rooted
isomorphism maps `u` to `root`. -/
def BranchRootedIso {V W : Type} (G : SimpleGraph V) (v u : V) (H : SimpleGraph W) (root : W) :
    Prop :=
  ∃ (hu : u ∈ branchSet G v u) (φ : G.induce (branchSet G v u) ≃g H), φ ⟨u, hu⟩ = root

end QLocalCert


