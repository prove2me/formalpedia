-- Prove2me | Definitions.Def_DirTeleMC_IsJumpArb
-- name    : DirTeleMC_IsJumpArb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T11:30:21.645133+00:00
-- url     : https://prove2.me/theorems/7c8ea1b8-43b2-44b6-9371-5551f4de8524
-- title:
--   Jump arborescences, structures and covered terminals
-- statement:
--   **Jump arborescence (Definition 4.1).** For integers $\theta \ge 1$ and $\eta$, a jump arborescence is a jump tree of depth at most $\eta$ whose root is labelled $s$, in which every terminal labels at least one node, and in which each edge from a node labelled $u$ to a node labelled $w$ carries a directed walk from $u$ to $w$ with at most $\theta$ arcs, the empty walk when $u = w$.
--
--   **Structure (§B.4).** A structure rooted at a node of height $h$ of the unfolding $\mathcal U_{\eta,\theta}$ is a jump tree of depth at most $h$ in which every jump is a path with at most $\theta$ arcs from the parent's label to the child's label (the empty path when the labels agree).
--
--   **Covered terminals.** The nodes at depth exactly $h$ below such a root are leaves of the unfolding; the terminals labelling them are the terminals the structure covers, $\mathrm{cov}(S)$.
--
--   **Formalization Note** A node of the unfolding is the sequence of labels on its root path, so the tree's labels determine it; the unfolding is not built separately.
-- source:
--   S. Kamali, S.-M. Seyed-Javadi, Approximation Algorithms for Directed Telephone Multicast, arXiv:2610.27422 (manuscript sha256 e56edddf…), Definition 4.1, p.10 (PDF p.11); §B.3, p.20 (PDF p.21); §B.4, p.21 (PDF p.22)

import Mathlib
import Definitions.Def_DirTeleMC_JTree

namespace DirTeleMC

namespace JTree

variable {n : ℕ}

/-- **Jump arborescence** (Definition 4.1).
Kamali, Seyed-Javadi, *Approximation Algorithms for Directed Telephone Multicast*, arXiv:2610.27422
(manuscript sha256 e56edddf…), Definition 4.1, p.10 (restated p.20): "A jump arborescence is a rooted tree J
of depth at most η, with edges directed away from the root and nodes labelled by vertices of G. The root is
labelled s, every terminal labels at least one node, and a vertex of G may label several nodes. Each edge
whose parent and child have labels u and w carries a jump: a directed walk from u to w with at most θ arcs.
When u = w, this is the empty walk."

`IsJumpArb adj θ η s Y J`: the root is labelled `s`, the depth is at most `η`, every vertex of the terminal set
`Y` labels a node, and every jump is a walk in `adj` from the parent's label to the child's label with at most
`θ` arcs, the empty walk `[u]` when the two labels agree.

**Formalization Note.** The depth bound `η` and the terminal set are parameters: the paper uses `η = 2ℓ − 1`
and `Y = K` (Lemma 4.2 applies it to the terminals of a given arborescence). -/
def IsJumpArb (adj : Fin n → Fin n → Bool) (θ η : ℕ) (s : Fin n) (Y : Finset (Fin n)) (J : JTree n) :
    Prop :=
  J.label = s ∧ J.depth ≤ η ∧ (∀ t ∈ Y, ∃ d, t ∈ J.labelsAt d) ∧
    J.AllJumps fun u P w => IsJump adj θ u w P ∧ (u = w → P = [u])

/-- **Structure** of height `h` (§B.4, p.21): "A structure rooted at a node σ of U is a finite rooted tree with
root σ whose nodes are nodes of U (a node of U may occur several times); each non-root node is a child in U of
its parent and carries a jump from the label of its parent to its own label: a path with at most θ arcs, or the
empty path if the labels agree."

`IsStructure adj θ h J`: `J` has depth at most `h` (the height of its root in `U_{η,θ}`) and every jump is a
path (a walk without repeated vertex) with at most `θ` arcs from the parent's label to the child's label.

**Formalization Note.** A node of `U_{η,θ}` at height `h` has descendants down to depth `h` below it, and a
child in `U` of a node labelled `u` is any `w` with `dist(u, w) ≤ θ` (§B.3), which the jump witnesses; so
these two conditions say exactly that the nodes are nodes of `U`. The only path from `u` to `u` is `[u]`, the
empty path. The root label is stated separately where a structure is used. -/
def IsStructure (adj : Fin n → Fin n → Bool) (θ h : ℕ) (J : JTree n) : Prop :=
  J.depth ≤ h ∧ J.AllJumps fun u P w => IsJump adj θ u w P ∧ P.Nodup

/-- **The covered vertices** `cov(S)` of a structure rooted at a node of height `h` (§B.3–B.4, pp.20–21:
"we let only leaves cover terminals"; "Its set cov(S) of covered terminals consists of the terminals among the
labels of its nodes that are leaves of U"): the labels of its nodes at depth exactly `h`, which are the leaves
of `U`. The covered terminals are `R ∩ cov h S` for the relevant terminal set `R`. -/
def cov (h : ℕ) (J : JTree n) : Finset (Fin n) := J.labelsAt h

end JTree

end DirTeleMC


