-- Prove2me | Definitions.Def_OptInapprox_MaxCut_UGC
-- name    : OptInapprox_MaxCut_UGC
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T11:25:36.94573+00:00
-- url     : https://prove2.me/theorems/7a7b5fdf-6adb-4c78-8613-c3c039209edd
-- title:
--   Definition 1 (p. 4), the UGC (p. 5), Definition 9 (p. 15) — Unique Label Cover, gap NP-hardness, weighted MAX-CUT
-- statement:
--   The combinatorial and complexity-theoretic objects of Theorem 1.
--
--   1. **Gap NP-hardness.** For a problem with instances encoded as strings over a finite alphabet, "it is NP-hard to distinguish Yes-instances from No-instances" means: every NP language $L'$ (over any finite nonempty alphabet) has a polynomial-time map $f$ to instances such that $x\in L'$ implies $f(x)$ is a Yes-instance and $x\notin L'$ implies $f(x)$ is a No-instance. NP and polynomial-time computability are those of the published definitions `CookPvsNP_defs` (one-tape Turing machines).
--   2. **Unique Label Cover (Definition 1).** An instance $\mathcal L(V,W,E,[M],\{\sigma_{v,w}\})$ is a bipartite graph with left vertices $V$, right vertices $W$, edges $E\subseteq V\times W$, a label set $[M]$ and a bijection $\sigma_{v,w}:[M]\to[M]$ for each edge. A labeling satisfies the edge $(v,w)$ if $\sigma_{v,w}(\mathrm{label}(w))=\mathrm{label}(v)$, and
--   $$\mathrm{OPT}=\max_{\text{labelings}}\frac{|\{(v,w)\in E\text{ satisfied}\}|}{|E|}.$$
--   3. **The Unique Games Conjecture (p. 5).** For any $\eta,\gamma>0$ there is a constant $M=M(\eta,\gamma)$ such that it is NP-hard to distinguish whether a Unique Label Cover instance with label set of size $M$ has optimum at least $1-\eta$ or at most $\gamma$.
--   4. **Weighted MAX-CUT (Definition 9, §7.1).** An undirected graph with nonnegative integer edge weights; a cut $(V_1,V_2)$ is satisfied to the extent $\sum_{e\in(V_1\times V_2)\cap E}w(e)/\sum_e w(e)$. An instance is *at least $c$-satisfiable* if some cut achieves fraction $\ge c$, and *at most $s$-satisfiable* if every cut achieves fraction $\le s$.
--
--   **Formalization Note.** `GapNPHard` is copied verbatim from the published convention of the Feige set-cover series. Instances are encoded in unary over small finite alphabets (`ULCSym`, `MCSym`); a Unique Label Cover instance is written as its adjacency matrix with the permutation table on each edge. The family `σ` is a bijection for every pair $(v,w)$; its values off $E$ are irrelevant to every predicate. `OPT` is the real supremum over the finitely many labelings; it is $0$ when there is no labeling ($M=0$ with a vertex present), and `satFrac` is $0$ when $E=\emptyset$. Both the UGC's predicates and the MAX-CUT predicates of Theorem 1 require a nonempty edge set. The MAX-CUT graph is loopless, and weights are natural numbers, encoded as edge multiplicities (§7.1: "we freely work with the weighted version").
-- source:
--   Khot, Kindler, Mossel & O'Donnell, Optimal Inapproximability Results for MAX-CUT and Other 2-Variable CSPs?, SIAM J. Comput. 37(1), 2007 (authors' version of February 7, 2007), pp. 4–5, 15–16, Definition 1, the Unique Games Conjecture, Definition 9, §7.1

import Mathlib
import Definitions.Def_CookPvsNP_defs

namespace OptInapprox.MaxCut

/-- Gap NP-hardness (copied verbatim from `SetCoverThreshold.SetCover.GapNPHard`): it is NP-hard to
distinguish `Yes` from `No` instances of a problem with instances `α` encoded by `enc` over the
finite alphabet `Sym` if every NP language `L'` over every finite nonempty alphabet maps in
polynomial time to instances so that members go to `Yes` instances and non-members to `No`
instances. -/
def GapNPHard {α Sym : Type} (enc : α → List Sym) (Yes No : α → Prop) : Prop :=
  ∀ (Sym' : Type) [Fintype Sym'] [Nonempty Sym'] (L' : CookPvsNP.Lang Sym'),
    L' ∈ CookPvsNP.NP Sym' →
      ∃ f : List Sym' → α, CookPvsNP.PolyTimeComputable (fun x => enc (f x)) ∧
        ∀ x, (x ∈ L' → Yes (f x)) ∧ (x ∉ L' → No (f x))

/-- A Unique Label Cover instance `L(V, W, E, [M], {σ_{v,w}})` (Definition 1): a bipartite graph
with left vertices `V = Fin nV`, right vertices `W = Fin nW`, edge set `E ⊆ V × W`, label set
`[M] = Fin M`, and a bijection `σ v w : [M] → [M]` for each edge `(v, w)`; the values of `σ` off
`E` play no role. -/
structure ULC where
  nV : ℕ
  nW : ℕ
  M : ℕ
  E : Finset (Fin nV × Fin nW)
  σ : Fin nV → Fin nW → Equiv.Perm (Fin M)

namespace ULC

/-- The fraction of edges satisfied by a labeling `lab = (labV, labW)`; the edge `(v, w)` is
satisfied iff `σ_{v,w}(label(w)) = label(v)` (Definition 1). It is `0` when `E = ∅`. -/
noncomputable def satFrac (L : ULC) (lab : (Fin L.nV → Fin L.M) × (Fin L.nW → Fin L.M)) : ℝ :=
  ((L.E.filter fun e => L.σ e.1 e.2 (lab.2 e.2) = lab.1 e.1).card : ℝ) / (L.E.card : ℝ)

/-- The optimum `OPT` (Definition 1): the maximum fraction of edges satisfied by any labeling.
There are finitely many labelings; when there are none (`M = 0` with a vertex) the supremum of
the empty family is `0`. -/
noncomputable def OPT (L : ULC) : ℝ :=
  ⨆ lab : (Fin L.nV → Fin L.M) × (Fin L.nW → Fin L.M), L.satFrac lab

end ULC

/-- Alphabet for encoding Unique Label Cover instances. -/
inductive ULCSym where
  | one
  | sep
  | edge
  | noEdge
  deriving DecidableEq

instance : Fintype ULCSym where
  elems := {ULCSym.one, ULCSym.sep, ULCSym.edge, ULCSym.noEdge}
  complete := by intro x; cases x <;> simp

/-- `m` in unary, terminated by a separator. -/
def ULCSym.unary (m : ℕ) : List ULCSym := List.replicate m ULCSym.one ++ [ULCSym.sep]

/-- Encoding of a Unique Label Cover instance: `nV`, `nW`, `M` in unary, then for every pair
`(v, w)` (in lexicographic order) either `noEdge`, or `edge` followed by the table of `σ v w`
(the values `σ v w 0, …, σ v w (M-1)` in unary). -/
def encULC (L : ULC) : List ULCSym :=
  ULCSym.unary L.nV ++ ULCSym.unary L.nW ++ ULCSym.unary L.M ++
    (List.finRange L.nV).flatMap fun v => (List.finRange L.nW).flatMap fun w =>
      if (v, w) ∈ L.E then
        ULCSym.edge :: (List.finRange L.M).flatMap fun j => ULCSym.unary (L.σ v w j : ℕ)
      else [ULCSym.noEdge]

/-- The Unique Games Conjecture (p. 5): for any `η, γ > 0` there is a constant `M = M(η, γ)` such
that it is NP-hard to distinguish Unique Label Cover instances with label set of size `M` and
optimum at least `1 - η` from those with optimum at most `γ` (instances have at least one edge). -/
def UGC : Prop :=
  ∀ η γ : ℝ, 0 < η → 0 < γ → ∃ M : ℕ,
    GapNPHard encULC (fun L : ULC => L.M = M ∧ L.E.Nonempty ∧ 1 - η ≤ L.OPT)
      (fun L : ULC => L.M = M ∧ L.E.Nonempty ∧ L.OPT ≤ γ)

/-- A weighted MAX-CUT instance (Definition 9, with §7.1's weighted version): an undirected
loopless graph on the vertices `Fin n`, given as a list of edges in which an edge listed `m`
times has weight `m` (natural-number weights). -/
structure WMaxCut where
  n : ℕ
  edges : List (Fin n × Fin n)
  loopless : ∀ e ∈ edges, e.1 ≠ e.2

/-- The weighted fraction of edges cut by the partition `c : Fin n → Bool` (`V₁ = c⁻¹(true)`,
`V₂ = c⁻¹(false)`); it is `0` for the empty edge list. -/
noncomputable def WMaxCut.cutFrac (G : WMaxCut) (c : Fin G.n → Bool) : ℝ :=
  ((G.edges.countP fun e => c e.1 != c e.2 : ℕ) : ℝ) / (G.edges.length : ℝ)

/-- Alphabet for encoding MAX-CUT instances. -/
inductive MCSym where
  | one
  | sep
  deriving DecidableEq

instance : Fintype MCSym where
  elems := {MCSym.one, MCSym.sep}
  complete := by intro x; cases x <;> simp

/-- `m` in unary, terminated by a separator. -/
def MCSym.unary (m : ℕ) : List MCSym := List.replicate m MCSym.one ++ [MCSym.sep]

/-- Encoding of a weighted MAX-CUT instance: `n` in unary, then the endpoints of each listed edge
in unary. -/
def encMaxCut (G : WMaxCut) : List MCSym :=
  MCSym.unary G.n ++ G.edges.flatMap fun e => MCSym.unary (e.1 : ℕ) ++ MCSym.unary (e.2 : ℕ)

end OptInapprox.MaxCut


