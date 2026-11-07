-- Prove2me | Definitions.Def_PctDistortion_alphaMajority
-- name    : PctDistortion_alphaMajority
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:40:54.329317+00:00
-- url     : https://prove2.me/theorems/6c13794c-851b-4c1a-abcc-97dd916b2a52
-- title:
--   The α-majority digraph of an election and the class $M_\alpha$
-- statement:
--   Let $\alpha\in[1/2,1)$ and let $\mathcal E=(V,C,\vec\succ)$ have $n$ voters. Candidate $c$ **α-defeats** $c'$ if strictly more than an $\alpha$ fraction of voters prefer $c$ to $c'$:
--   $$|\{v\in V: c\succ_v c'\}|\ge\lfloor\alpha n+1\rfloor.$$
--   The **α-majority digraph** $G^\alpha_{\mathcal E}=(C,E^\alpha)$ has the arc $(c,c')$ iff $c$ α-defeats $c'$. The class $M_\alpha$ consists of the α-majority digraphs of finite elections.
--
--   For $\alpha=1/2$ this is the majority tournament with pairwise ties left unoriented. The degree condition of Theorem B is a statement about $M_\alpha$.
--
--   **Formalization Note** A digraph on a node type $W$ is in $M_\alpha$ when $W$ is finite and nonempty and the digraph equals $G^\alpha_{\mathcal E}$ for an election with a finite nonempty voter set and candidate set $W$.
-- source:
--   Kizilkaya, Kalayci, Kempe, Micha, The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries, STOC 2027 submission (held version, sha256 fd779dd0…), Definition 3, p.10

import Mathlib
import Definitions.Def_PctDistortion_Election

set_option autoImplicit false

namespace PctDistortion

open Classical in
/-- The **α-majority digraph** `G^α_E = (C, E^α)` of an election `E` with `n` voters: there is
an arc `(c, c')` iff `c` **α-defeats** `c'`, i.e. `|{v ∈ V | c ≻_v c'}| ≥ ⌊αn + 1⌋` (strictly
more than an α fraction of the voters prefer `c` to `c'`).

Kizilkaya, Kalayci, Kempe, Micha, *The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries*, STOC 2027 submission (held version, sha256 fd779dd0…), Definition 3, p.10: "candidate c α-defeats candidate c′ if (strictly) more than an α fraction of
voters prefer c to c′, that is, |{v ∈ V | c ≻v c′}| ≥ ⌊αn + 1⌋. The α-majority digraph of an
election E = (V, C, ≻⃗) is the digraph Gα_E = (C, Eα) where (c, c′) ∈ Eα if and only if c
α-defeats c′." -/
noncomputable def alphaMajority {V C : Type} [Fintype V] (α : ℝ) (E : Election V C) :
    Digraph C where
  Adj c c' := ⌊α * (Fintype.card V : ℝ) + 1⌋₊ ≤ (Finset.univ.filter (fun v => E.prefers v c c')).card

/-- `G` belongs to the class `M_α` of **α-majority digraphs of finite elections**: its node type
`W` is finite and nonempty, and `G` is the α-majority digraph of some election with a finite
nonempty set of voters and candidate set `W`.

Kizilkaya, Kalayci, Kempe, Micha, *The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries*, STOC 2027 submission (held version, sha256 fd779dd0…), Definition 3, p.10: "We denote the class of α-majority digraphs of finite elections by Mα."

**Formalization Note.** The candidate type of the election is the node type of `G` itself, so
membership is invariant under relabelling nodes. Voters and candidates are nonempty, as for every
election of the mission (the paper's `n, m ≥ 1`). -/
def IsAlphaMajority (α : ℝ) {W : Type} (G : Digraph W) : Prop :=
  Finite W ∧ Nonempty W ∧
    ∃ (V : Type) (_ : Fintype V) (_ : Nonempty V) (E : Election V W), alphaMajority α E = G

end PctDistortion


