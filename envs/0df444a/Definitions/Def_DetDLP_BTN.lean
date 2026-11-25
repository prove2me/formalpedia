-- Prove2me | Definitions.Def_DetDLP_BTN
-- name    : DetDLP_BTN
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-23T09:04:45.11224+00:00
-- url     : https://prove2.me/theorems/8db87421-081b-4465-85e1-18766f5b6ebe
-- title:
--   Bipartite Boolean Tensor Networks over $\mathcal{B}_{P_0,\ell}$ and Parsimonious Encodings
-- statement:
--   This definition module formalizes bipartite Boolean tensor networks (BTNs) over commutative rings, the truncated polynomial ring $\mathcal{B}_{P_0, \ell} = (\mathbb{Z}/2^{P_0}\mathbb{Z})[z]/(z^\ell)$, parsimonious Boolean relation encodings, and uniform Turing-machine local entry evaluation.
--
--   A finite bipartite multigraph $G = (V, E)$ allows parallel edges while forbidding self-loops via its 2-coloring, inducing a canonical ordered incident port list $\delta(v)$ and degree $\deg_G(v) = |\delta(v)|$ at each vertex $v$. For local tensors $T_v : \{0, 1\}^{\delta(v)} \to R$, the contraction is defined as
--
--   $$\mathrm{Contract}(G, T) = \sum_{x \in \{0, 1\}^E} \prod_{v \in V} T_v(x|_{\delta(v)}) \in R.$$
--
--   For $\{0, 1\}$-valued networks, `IsParsimonious` states that every valid interface assignment $x_{\mathrm{ext}} \in R$ extends to a unique satisfying full edge assignment and invalid interface assignments admit none. Canonical coefficient-list encodings in $[0, 2^{P_0})^\ell$ and uniform entry-evaluation predicates (`BTNEntryEvaluable`, `BoolBTNEntryEvaluable`) interface directly with deterministic contraction machines.
--
--   **Formalization Note** `TruncPoly P0 ℓ` is defined as the Mathlib quotient ring `Polynomial (ZMod (2 ^ P0)) ⧸ Ideal.span {X ^ ℓ}`, automatically inheriting `CommRing`.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.2 (Definition 2.1 and Theorem 2.2, pp. 7–8)

import Mathlib
import Definitions.Def_DetDLP_Machine

set_option autoImplicit false

namespace DetDLP

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

/-- A finite bipartite multigraph `G = (V, E)` with vertex set `Fin nV`, edge set `Fin nE`,
endpoint map `endpoints`, and a 2-coloring `side` such that every edge connects opposite sides.
Parallel edges are distinct elements of `Fin nE`; bipartiteness implies there are no self-loops. -/
structure BipartiteMultigraph where
  nV : ℕ
  nE : ℕ
  endpoints : Fin nE → Fin nV × Fin nV
  side : Fin nV → Bool
  bipartite : ∀ e, side (endpoints e).1 ≠ side (endpoints e).2

namespace BipartiteMultigraph

/-- The ordered list `δ(v)` of edge ports incident to vertex `v`, in increasing edge index order. -/
def ports (G : BipartiteMultigraph) (v : Fin G.nV) : List (Fin G.nE) :=
  (List.finRange G.nE).filter (fun e => decide ((G.endpoints e).1 = v ∨ (G.endpoints e).2 = v))

/-- The degree `|δ(v)|` of vertex `v` (counting parallel edges with multiplicity). -/
def deg (G : BipartiteMultigraph) (v : Fin G.nV) : ℕ :=
  (G.ports v).length

/-- The maximum vertex degree `max_{v ∈ V} |δ(v)|` (`0` if `nV = 0`). -/
def maxDeg (G : BipartiteMultigraph) : ℕ :=
  Finset.univ.sup G.deg

/-- Canonical binary encoding of a bipartite multigraph: vertex count, edge count,
bipartition side bits, and flattened endpoint pairs. -/
def encode (G : BipartiteMultigraph) : List Bool :=
  Encoding.encodeList id
    [ countWord G.nV,
      countWord G.nE,
      List.ofFn G.side,
      encodeNatListBin ((List.finRange G.nE).flatMap fun e => [(G.endpoints e).1.val, (G.endpoints e).2.val]) ]

end BipartiteMultigraph

/-- The truncated polynomial ring `B_{P₀, ℓ} = (ℤ / 2^{P₀} ℤ)[z] / (z^ℓ)`. -/
abbrev TruncPoly (P0 ℓ : ℕ) : Type :=
  Polynomial (ZMod (2 ^ P0)) ⧸ Ideal.span {(Polynomial.X : Polynomial (ZMod (2 ^ P0))) ^ ℓ}

/-- Construct an element of `TruncPoly P0 ℓ` from its `ℓ` coefficients `c : Fin ℓ → ℕ`. -/
noncomputable def truncPolyOfCoeffs (P0 ℓ : ℕ) (c : Fin ℓ → ℕ) : TruncPoly P0 ℓ :=
  Ideal.Quotient.mk _ (∑ i : Fin ℓ, Polynomial.monomial i.val ((c i : ZMod (2 ^ P0))))

/-- Canonical binary encoding relation for `x ∈ B_{P₀, ℓ}`: `w` encodes the unique `ℓ`-tuple
of canonical residues `c i ∈ [0, 2^{P₀})` representing `x`. -/
def EncodesTruncPoly (P0 ℓ : ℕ) (w : List Bool) (x : TruncPoly P0 ℓ) : Prop :=
  ∃ c : Fin ℓ → ℕ,
    (∀ i, c i < 2 ^ P0) ∧
    w = encodeNatListBin (List.ofFn c) ∧
    x = truncPolyOfCoeffs P0 ℓ c

/-- Contraction of a bipartite Boolean tensor network `(G, T)` over a commutative ring `R`:
`Contract(G, T) = ∑_{x ∈ {0,1}^E} ∏_{v ∈ V} T_v(x|_{δ(v)})`. -/
def BTNContract (G : BipartiteMultigraph) {R : Type*} [CommRing R]
    (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → R) : R :=
  ∑ x : Fin G.nE → Bool, ∏ v : Fin G.nV, T v (fun i => x ((G.ports v).get i))

/-- A `{0, 1}`-valued bipartite BTN `(G, T)` encodes a relation `R ⊆ {0, 1}^k` on interface edges
`ext : Fin k → Fin G.nE` parsimoniously if every `x_ext ∈ R` extends to a unique satisfying
assignment `x : Fin G.nE → Bool` and every `x_ext ∉ R` has no satisfying extension. -/
def IsParsimonious (G : BipartiteMultigraph)
    (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Bool)
    {k : ℕ} (ext : Fin k → Fin G.nE) (R : (Fin k → Bool) → Prop) : Prop :=
  Function.Injective ext ∧
  ∀ xext : Fin k → Bool,
    (R xext →
      ∃! x : Fin G.nE → Bool,
        (∀ i, x (ext i) = xext i) ∧
        (∀ v : Fin G.nV, T v (fun j => x ((G.ports v).get j)) = true)) ∧
    (¬ R xext →
      ¬ ∃ x : Fin G.nE → Bool,
        (∀ i, x (ext i) = xext i) ∧
        (∀ v : Fin G.nV, T v (fun j => x ((G.ports v).get j)) = true))

/-- Canonical query input `(desc, v, α)` to a local tensor entry evaluator. -/
def encodePortQuery (desc : List Bool) (v : ℕ) (α : List Bool) : List Bool :=
  Encoding.encodeList id [desc, countWord v, α]

/-- Uniform deterministic entry evaluation for a BTN over `B_{P₀, ℓ}` in time `τ` and space `σ`. -/
def BTNEntryEvaluable (desc : List Bool) (G : BipartiteMultigraph) (P0 ℓ : ℕ)
    (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → TruncPoly P0 ℓ)
    (E : PrimitiveMachine) (outE : Fin E.tapeCount) (τ σ : ℝ) : Prop :=
  ∀ (v : Fin G.nV) (α : Fin (G.deg v) → Bool),
    ∃ w : List Bool,
      EncodesTruncPoly P0 ℓ w (T v α) ∧
      RunsWithin E outE (encodePortQuery desc v.val (List.ofFn α)) w τ σ

/-- Uniform deterministic entry evaluation for a `{0, 1}`-valued BTN in time `τ` and space `σ`. -/
def BoolBTNEntryEvaluable (desc : List Bool) (G : BipartiteMultigraph)
    (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Bool)
    (E : PrimitiveMachine) (outE : Fin E.tapeCount) (τ σ : ℝ) : Prop :=
  ∀ (v : Fin G.nV) (α : Fin (G.deg v) → Bool),
    RunsWithin E outE (encodePortQuery desc v.val (List.ofFn α)) [T v α] τ σ

/-- Canonical input encoding of a BTN contraction instance `(desc, G, s, P₀, ℓ)`. -/
def encodeBTNInstance (desc : List Bool) (G : BipartiteMultigraph) (s P0 ℓ : ℕ) : List Bool :=
  Encoding.encodeList id [desc, G.encode, countWord s, countWord P0, countWord ℓ]

/-- Unsigned little-endian value of a `d`-bit vector `v : Fin d → Bool`: `∑_{i<d} v_i 2^i`. -/
def bitsToNat {d : ℕ} (v : Fin d → Bool) : ℕ :=
  ∑ i : Fin d, (if v i then 1 else 0) * 2 ^ i.val

end DetDLP


