-- Prove2me | Definitions.Def_QLocalCert_Ttr
-- name    : QLocalCert_Ttr
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:39:55.551052+00:00
-- url     : https://prove2.me/theorems/07d92726-64c6-494c-b5a9-10f19224bf6d
-- title:
--   The tree $T^{\mathrm{tr}}_{N,\mu}(z,z')$
-- statement:
--   Let $\rho=2\mu+1$ and let $z,z'\in\{0,1\}^N$ be balanced. The tree $T^{\mathrm{tr}}_{N,\mu}(z,z')$ (Definition 23) is built as follows. Two hubs $h_L,h_R$ are joined by the central path $h_L,w_1,\dots,w_{\rho-1},h_R$ of $\rho$ edges. To $h_L$ attach $N/2+1$ new vertices $a_0,\dots,a_{N/2}$; to each $a_i$ attach $r_i(z)$ pendant leaves, and join $a_i$ by an edge to the root of a disjoint copy of $\mathrm{Tag}(i)$. Attach the same structure to $h_R$, using $r(z')$ in place of $r(z)$.
--
--   The two hubs with their gadgets encode the strings $z$ and $z'$ in the shape of the tree.
--
--   **Formalization Note** Vertices: `path j` is $w_{j+1}$ ($j<2\mu=\rho-1$); `left x` and `right x` are the vertices of the two sides, where on a side `hub` is $h_L$ resp. $h_R$, `a i` is $a_i$, `leaf i k` ($k<r_i$) are its leaves, and `tag i x` are the vertices of its tag. The graph is defined by parent pointers rooted at $h_L$; the leaves of $a_i$ are indexed by $\{0,\dots,r_i-1\}$, so the vertex type depends on $r(z),r(z')$.
-- source:
--   Jauregui, Miyamoto, Quantum Advantage in Local Certification of Graph Properties, STOC 2027 submission (manuscript sha256 b707143b1ab5511bef4c2b77e1b803f28b32cced25a008516898fd11d28c0451), Definition 23, p.34; Remark 24, p.34; Figure 2(b), p.35

import Mathlib
import Definitions.Def_QLocalCert_Tag
import Definitions.Def_QLocalCert_runLengths

set_option autoImplicit false

namespace QLocalCert

/-- The vertices of one side of `T^tr_{N,µ}` (the hub with its gadgets, Remark 24, p.34), for a
run-length vector `r = (r₀, …, r_{N/2})`: the hub `h`, the vertices `aᵢ` (`0 ≤ i ≤ N/2`), the
`rᵢ` pendant leaves `leaf i k` (`k < rᵢ`) of `aᵢ`, and the vertices of the copy of `Tag(i)`
attached to `aᵢ`. -/
inductive SideV (N : ℕ) (r : Fin (N / 2 + 1) → ℕ) where
  | hub
  | a (i : Fin (N / 2 + 1))
  | leaf (i : Fin (N / 2 + 1)) (k : Fin (r i))
  | tag (i : Fin (N / 2 + 1)) (x : TagV (tagL N) i.val)
  deriving DecidableEq, Fintype

namespace SideV

variable {N : ℕ} {r : Fin (N / 2 + 1) → ℕ}

/-- Parent pointers of one side, rooted at its hub: `aᵢ ↦ h`; the leaves of `aᵢ ↦ aᵢ`; the root
`s` of the tag of `aᵢ` `↦ aᵢ`; every other tag vertex `↦` its parent in `Tag(i)`. -/
def parent : SideV N r → Option (SideV N r)
  | hub => none
  | a _ => some hub
  | leaf i _ => some (a i)
  | tag i x => match x.parent with
    | none => some (a i)
    | some y => some (tag i y)

end SideV

/-- The vertices of `T^tr_{N,µ}`: the internal central-path vertices `w_{j+1}` (`path j`,
`j < 2µ = ρ − 1`), the left side (hub `h_L`) built from `r`, and the right side (hub `h_R`) built
from `r'`. -/
inductive TV (N μ : ℕ) (r r' : Fin (N / 2 + 1) → ℕ) where
  | path (j : Fin (2 * μ))
  | left (x : SideV N r)
  | right (x : SideV N r')
  deriving DecidableEq, Fintype

namespace TV

variable {N μ : ℕ} {r r' : Fin (N / 2 + 1) → ℕ}

/-- Parent pointers of `T^tr_{N,µ}`, rooted at `h_L`: the left side as in `SideV.parent`;
`w₁ ↦ h_L`, `w_{j+1} ↦ w_j`; `h_R ↦ w_{ρ−1}` (or `↦ h_L` when `ρ − 1 = 0`); the right side as in
`SideV.parent`. -/
def parent : TV N μ r r' → Option (TV N μ r r')
  | left x => x.parent.map left
  | path j => if j.val = 0 then some (left .hub) else some (path ⟨j.val - 1, by omega⟩)
  | right x => match x.parent with
    | some y => some (right y)
    | none => if h : 0 < 2 * μ then some (path ⟨2 * μ - 1, by omega⟩) else some (left .hub)

end TV

/-- The tree of Definition 23 built from run-length vectors `r` (left) and `r'` (right). -/
def TtrR (N μ : ℕ) (r r' : Fin (N / 2 + 1) → ℕ) : SimpleGraph (TV N μ r r') :=
  parentGraph TV.parent

/-- **Definition 23** (p.34). "For strings z, z′ ∈ {0, 1}^N of Hamming weight N/2, the tree
T^tr_{N,µ}(z, z′) is constructed as follows. Start with two vertices h_L, h_R joined by the central
path P = h_L, w₁, . . . , w_{ρ−1}, h_R of ρ edges. Attach N/2 + 1 new vertices a₀, . . . , a_{N/2} to
h_L. For each i, attach rᵢ(z) leaves to aᵢ, and join aᵢ by an edge to the root of a disjoint copy
of Tag(i). Attach the same structure to h_R, using r(z′) in place of r(z)."

Source: B. Jauregui, M. Miyamoto, *Quantum Advantage in Local Certification of Graph Properties*,
STOC 2027 submission (manuscript sha256 b707143b…0c51), Definition 23 and Figure 2(b),
pp.34–35, with `ρ = 2µ + 1` (p.34).

**Formalization Note.** The vertex type is `TV N μ (runLengths z) (runLengths z')`: `h_L` is
`left hub`, `h_R` is `right hub`, `w_{j+1}` is `path j`; on each side `a i` is `aᵢ`, `leaf i k`
its pendant leaves and `tag i x` the vertices of its tag (root `tag i .s`). The tree is the graph
of the parent pointers `TV.parent`. The definition is total in `z, z'`; it is only used for
balanced strings. -/
noncomputable def Ttr (N μ : ℕ) (z z' : Fin N → Bool) :
    SimpleGraph (TV N μ (runLengths z) (runLengths z')) :=
  TtrR N μ (runLengths z) (runLengths z')

end QLocalCert


