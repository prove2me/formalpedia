-- Prove2me | Definitions.Def_QLocalCert_Tag
-- name    : QLocalCert_Tag
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:39:16.510205+00:00
-- url     : https://prove2.me/theorems/2d1f5077-1280-413f-975c-810d3bb2c66c
-- title:
--   The tag tree $\mathrm{Tag}(i)$ with $L=\lceil\log_2(N/2+1)\rceil$ arms
-- statement:
--   Fix $N$ and set $L=\lceil\log_2(N/2+1)\rceil$. For $i\in\{0,\dots,N/2\}$, the rooted tree $\mathrm{Tag}(i)$ (Definition 22) has a root $s$ with a single child $t$; for each $b\in[L]$ a path of $b$ edges starts at $t$, these paths sharing only $t$; and if the $b$-th least significant bit of $i$ is $1$, two additional leaves are attached to the last vertex of the $b$-th path. For example $\mathrm{Tag}(3)$ with $L=3$ has extra leaves on the paths of lengths $1$ and $2$ (Figure 2(a)).
--
--   The tags record the index $i$ of each gadget in the trees $T^{\mathrm{tr}}_{N,\mu}$ so that it survives isomorphism.
--
--   **Formalization Note** `tagL N = Nat.clog 2 (N/2+1)`, the least $k$ with $N/2+1\le2^k$. Arms and positions are 0-based: `arm b p` is position $p+1$ of the arm with $b+1$ edges, and its extra leaves exist when `Nat.testBit i b`, the $(b+1)$-th least significant bit. The tree is given by parent pointers, rooted at `s`.
-- source:
--   Jauregui, Miyamoto, Quantum Advantage in Local Certification of Graph Properties, STOC 2027 submission (manuscript sha256 b707143b1ab5511bef4c2b77e1b803f28b32cced25a008516898fd11d28c0451), §4, p.34 (L); Definition 22, p.34; Figure 2(a), p.35

import Mathlib

set_option autoImplicit false

namespace QLocalCert

/-- The simple graph of a rooted forest given by parent pointers: `u` and `v` are adjacent iff
one is the parent of the other. -/
def parentGraph {V : Type} (par : V → Option V) : SimpleGraph V :=
  SimpleGraph.fromRel fun u v => par u = some v

/-- `L := ⌈log₂(N/2 + 1)⌉`, the number of arms of every tag.

B. Jauregui, M. Miyamoto, *Quantum Advantage in Local Certification of Graph Properties*,
STOC 2027 submission (manuscript sha256 b707143b…0c51), §4, p.34: "Fix a positive integer µ ≥ 1,
known to the nodes, and an even integer N ≥ 8. Set L := ⌈log₂(N/2 + 1)⌉, ρ := 2µ + 1."

**Formalization Note.** `Nat.clog 2 m` is the least `k` with `m ≤ 2^k`, which is `⌈log₂ m⌉` for
`m ≥ 1`; here `m = N/2 + 1 ≥ 1`. For `N = 8`, `L = 3` (Figure 2(a)). -/
def tagL (N : ℕ) : ℕ := Nat.clog 2 (N / 2 + 1)

/-- The vertices of the tag `Tag(i)` with `L` arms (Definition 22, p.34): the root `s`, its child
`t`, the vertex at position `p + 1` of the arm with `b + 1` edges (`b < L`, `p ≤ b`), and the two
extra leaves (`e = false, true`) at the end of the arm with `b + 1` edges, present exactly when
the `(b + 1)`-th least significant bit of `i` is `1`.

**Formalization Note.** Arms and positions are 0-based: `arm b p` is position `p + 1 ∈ [b + 1]` of
the arm of `b + 1` edges, so the paper's arm `b ∈ [L]` is `b - 1` here, and its "b-th least
significant bit" is `Nat.testBit i (b - 1)`. -/
inductive TagV (L i : ℕ) where
  | s
  | t
  | arm (b : Fin L) (p : Fin (b.val + 1))
  | extra (b : Fin L) (e : Bool) (h : i.testBit b.val = true)
  deriving DecidableEq, Fintype

namespace TagV

variable {L i : ℕ}

/-- Parent pointers of `Tag(i)`, rooted at `s`: `t ↦ s`; the first vertex of each arm `↦ t`;
each later arm vertex `↦` its predecessor on the arm; an extra leaf `↦` the last vertex of its
arm. -/
def parent : TagV L i → Option (TagV L i)
  | s => none
  | t => some s
  | arm b p => if p.val = 0 then some t else some (arm b ⟨p.val - 1, by omega⟩)
  | extra b _ _ => some (arm b ⟨b.val, by omega⟩)

end TagV

/-- **Definition 22** (p.34). "For i ∈ {0, . . . , N/2}, the rooted tree Tag(i) has a root s with a
single child t. For each b ∈ [L], a path of b edges starts at t. These paths share only t. If the
b-th least significant bit of i is 1, we attach two additional leaves to the last vertex of the
corresponding path."

`Tag N i` is this tree for `L = tagL N`, as a simple graph on `TagV (tagL N) i`; its root is
`TagV.s`. Source: B. Jauregui, M. Miyamoto, STOC 2027 submission (manuscript sha256
b707143b…0c51), Definition 22 and Figure 2(a), pp.34–35.

**Formalization Note.** The tree is given by the parent pointers `TagV.parent`; the root is the
vertex `s` with no parent. -/
def Tag (N i : ℕ) : SimpleGraph (TagV (tagL N) i) := parentGraph TagV.parent

end QLocalCert


