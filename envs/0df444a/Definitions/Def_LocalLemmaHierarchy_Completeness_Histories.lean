-- Prove2me | Definitions.Def_LocalLemmaHierarchy_Completeness_Histories
-- name    : LocalLemmaHierarchy_Completeness_Histories
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T00:18:18.963974+00:00
-- url     : https://prove2.me/theorems/774319b3-b683-41c8-b231-680640b059eb
-- title:
--   Exact histories, departure sets, the exact update $\Phi$, supersolutions and the canonical branch
-- statement:
--   A **move** $(v,a,u)$ goes along option $a\in\mathcal A(v)$ from $v$ to a site $u$; its **departure set** (2.5) is $\mathcal D(v,a,u)=\{v\}\cup\{w\in D_{v,a}\setminus\{v\}: w\prec_{v,a}u\}$. A **history** is a starting site followed by a list of moves; its endpoint $v(h)$ is the target of the last move (or the start), and its deleted set $B(h)$ is the union of the departure sets of its moves.
--
--   **Exact histories** (Definition 2.2) in a site set $U$ (finite or infinite): the one-site history $(v)$, $v\in U$, is exact; if $h$ is exact with endpoint $v$ and residual $U_h=U\setminus B(h)$, then $h\cdot(v,a,u)$ is exact whenever $A_{v,a}\subseteq U_h$ and $u\in(D_{v,a}\cap U_h)\setminus\{v\}$. Histories exact in $V$ are **ambient**.
--
--   The **exact update** (2.6) at a history $h$ with endpoint $v$, in $U$, at moduli $p$:
--   $$\Phi^U_{p,h}(x)=\sum_{a\in\mathcal A(v),\,A_{v,a}\subseteq U_h}c_{v,a}p_{\tau(v,a)}\prod_{u\in(D_{v,a}\cap U_h)\setminus\{v\}}\bigl(1-x_{h\cdot(v,a,u)}\bigr)^{-1}$$
--   (one factor per option and factor site; different options give different occurrences). A **supersolution on the exact trees of $U$** (2.7) assigns $0\le x_h<1$ to every history $h$ exact in $U$ with $\Phi^U_{p,h}(x)\le x_h$. For a finite region $U$, the exact ratio at $h$ is $X_h=X_{U_h,v(h)}(p)$ (2.8), and `exactIter R U p N` is the depth-$N$ evaluation of the exact trees from zero boundary values ($x^{(0)}=0$, $x^{(N+1)}=\Phi^U_p(x^{(N)})$).
--
--   An option is **available** at an ambient history $h$ when $A_{v,a}\cap B(h)=\emptyset$. The finite-depth ambient evaluations at uniform modulus $\nu$ are $X^{\nu,0}=0$, $X^{\nu,N+1}_h=\Phi_{\nu,h}(X^{\nu,N})$, and the **canonical exact branch** is $X^\nu_h=\lim_N X^{\nu,N}_h$ (B.2), written as the supremum over $N$. A **symmetry preserving the representation** is a bijection of the sites with compatible bijections of the options and labels preserving supports, coefficients, labels and local orders; it acts on histories move by move.
--
--   **Formalization Note.** `Hist R` has a `start : V` and `moves : List (Move R)` (oldest first), with `Move R = Σ v, R.Opt v × V`. Exactness is checked at every prefix (`IsExact`). `σ_j` (`Hist.suffix j`) keeps the last $j$ moves or the whole shorter history, starting where the first kept move starts. `canonicalBranch` is a real `⨆ N`; Under the hypotheses of Proposition 3.4, the finite-region comparison in its proof (B.1)–(B.2) bounds this sequence; outside that range no branch assertion is made.
-- source:
--   Achlioptas, Kritharidis and Zampetakis, A Complete Hierarchy of Local Lemmas, STOC 2027 submission (manuscript sha256 bc1388b0…a434b961), (2.5)–(2.7) and Definition 2.2, printed pp. 6–7 (PDF pp. 8–9); (2.8), printed p. 7; Proposition 3.4 and (B.2), printed pp. 9, 18 (PDF pp. 11, 20)

import Mathlib
import Definitions.Def_LocalLemmaHierarchy_Completeness_Representation

open scoped ENNReal NNReal

namespace LocalLemmaHierarchy.Completeness

variable {V T : Type}

/-- A move `(v, a, u)` along option `a ∈ A(v)` from the site `v` to a site `u` (§2.2). The tag
carries the option, so different options using the same child site are different moves. -/
abbrev Move (R : PosLocalDeletionRep V T) : Type := Σ v : V, R.Opt v × V

/-- A history: a starting site followed by a list of moves, oldest first (§2.2). -/
structure Hist (R : PosLocalDeletionRep V T) where
  start : V
  moves : List (Move R)

namespace Hist

variable {R : PosLocalDeletionRep V T}

/-- The endpoint of the history that starts at `s` and makes the moves `ms`: the target of the last
move, or `s` when there is none. -/
def endpointOf (s : V) (ms : List (Move R)) : V :=
  match ms.getLast? with
  | none => s
  | some m => m.2.2

/-- The endpoint `v(h)` of a history. -/
def endpoint (h : Hist R) : V := endpointOf h.start h.moves

/-- `h · m`: append a move. -/
def append (h : Hist R) (m : Move R) : Hist R := ⟨h.start, h.moves ++ [m]⟩

/-- `σ_j(h)`: the history retaining the last `j` moves of `h`, or the whole history when it is
shorter (§3.3); it starts at the site where its first retained move starts. -/
def suffix (j : ℕ) (h : Hist R) : Hist R :=
  ⟨endpointOf h.start (h.moves.take (h.moves.length - j)), h.moves.drop (h.moves.length - j)⟩

end Hist

open Classical in
/-- The departure set (2.5) of the move `(v, a, u)`:
`D(v,a,u) = {v} ∪ {w ∈ D_{v,a} \ {v} : w ≺_{v,a} u}`. -/
noncomputable def departure (R : PosLocalDeletionRep V T) (m : Move R) : Finset V :=
  insert m.1 (((R.D m.1 m.2.1).erase m.1).filter
    (fun w => R.rank m.1 m.2.1 w < R.rank m.1 m.2.1 m.2.2))

open Classical in
/-- The deleted set `B` of a list of moves: the union of their departure sets. -/
noncomputable def deleted (R : PosLocalDeletionRep V T) (ms : List (Move R)) : Finset V :=
  (ms.map (departure R)).foldr (· ∪ ·) ∅

/-- The move `m` is a legal exact extension, inside the site set `U`, of the history that starts at
`s` and has made the moves `ms` (Definition 2.2): `m = (v, a, u)` with `v` the current endpoint,
`A_{v,a} ⊆ U_h` and `u ∈ (D_{v,a} ∩ U_h) \ {v}`, where `U_h = U \ B(h)` is the residual. -/
def LegalExactStep (R : PosLocalDeletionRep V T) (U : Set V) (s : V) (ms : List (Move R))
    (m : Move R) : Prop :=
  m.1 = Hist.endpointOf s ms ∧
    (↑(R.A m.1 m.2.1) : Set V) ⊆ U \ ↑(deleted R ms) ∧
    m.2.2 ∈ (↑(R.D m.1 m.2.1) : Set V) ∩ (U \ ↑(deleted R ms)) ∧ m.2.2 ≠ m.1

/-- **Exact histories** (Definition 2.2) in a site set `U` (finite or infinite): the one-site
history `(v)`, `v ∈ U`, is exact, and an exact history extended by a legal exact step is exact.
Histories exact in `Set.univ` (i.e. in `V`) are called ambient. -/
def IsExact (R : PosLocalDeletionRep V T) (U : Set V) (h : Hist R) : Prop :=
  h.start ∈ U ∧ ∀ i (hi : i < h.moves.length),
    LegalExactStep R U h.start (h.moves.take i) (h.moves[i]'hi)

open Classical in
/-- The residual `U_h = U \ B(h)` of a history in a finite region `U`. -/
noncomputable def residual (R : PosLocalDeletionRep V T) (U : Finset V) (h : Hist R) : Finset V :=
  U \ deleted R h.moves

open Classical in
/-- The exact update (2.6) at a history `h` with endpoint `v`, in the site set `U`, at moduli `p`:
`Φ^U_{p,h}(x) = ∑_{a ∈ A(v), A_{v,a} ⊆ U_h} c_{v,a} p_{τ(v,a)}
  ∏_{u ∈ (D_{v,a} ∩ U_h) \ {v}} (1 − x_{h·(v,a,u)})⁻¹`, with `U_h = U \ B(h)`.
One factor per (option, factor site) occurrence. For ambient histories take `U = Set.univ`. -/
noncomputable def exactUpdate (R : PosLocalDeletionRep V T) (U : Set V) (p : T → ℝ)
    (x : Hist R → ℝ) (h : Hist R) : ℝ :=
  ∑ a ∈ Finset.univ.filter
      (fun a : R.Opt h.endpoint => (↑(R.A h.endpoint a) : Set V) ⊆ U \ ↑(deleted R h.moves)),
    R.c h.endpoint a * p (R.label h.endpoint a) *
      ∏ u ∈ ((R.D h.endpoint a).erase h.endpoint).filter
          (fun u => u ∈ U \ ↑(deleted R h.moves)),
        (1 - x (h.append ⟨h.endpoint, a, u⟩))⁻¹

/-- A **supersolution on the exact trees of `U`** at moduli `p` (2.7): `0 ≤ x_h < 1` and
`Φ^U_{p,h}(x) ≤ x_h` at every occurrence `h`, i.e. at every history exact in `U` (from every root). -/
def IsExactSupersolution (R : PosLocalDeletionRep V T) (U : Set V) (p : T → ℝ)
    (x : Hist R → ℝ) : Prop :=
  ∀ h : Hist R, IsExact R U h → 0 ≤ x h ∧ x h < 1 ∧ exactUpdate R U p x h ≤ x h

/-- The exact ratio at an occurrence `h` of the exact tree of a finite region `U` (2.8):
`X_h = X_{U_h, v(h)}(p) = 1 − P_{U_h}(p) / P_{U_h − v}(p)`. -/
noncomputable def exactRatio (R : PosLocalDeletionRep V T) (Z : Finset V → MvPolynomial T ℝ)
    [DecidableEq V] (U : Finset V) (p : T → ℝ) (h : Hist R) : ℝ :=
  deletionRatio Z (residual R U h) h.endpoint p

/-- An option is **available** at the ambient history `h` when its activation support avoids the
deleted set `B(h)` (i.e. `A_{v,a} ⊆ V_h`). -/
def HasAvailableOption (R : PosLocalDeletionRep V T) (h : Hist R) : Prop :=
  ∃ a : R.Opt h.endpoint, Disjoint (R.A h.endpoint a) (deleted R h.moves)

/-- Depth-`N` evaluation of the exact trees of `U` at moduli `p` with zero boundary values:
`x^(0) = 0`, `x^(N+1)_h = Φ^U_{p,h}(x^(N))`. On a finite region `U` every branch below an occurrence
has at most `|U| − 1` moves, so `exactIter R U p |U|` is the bottom-up equality evaluation of the
(finite) exact trees of `U` (§2.2–2.3). -/
noncomputable def exactIter (R : PosLocalDeletionRep V T) (U : Set V) (p : T → ℝ) :
    ℕ → Hist R → ℝ
  | 0 => fun _ => 0
  | N + 1 => fun h => exactUpdate R U p (exactIter R U p N) h

/-- Depth-`N` evaluation of the ambient exact trees at uniform modulus `ν` with zero boundary
values (proof of Proposition 3.4, App. B.3): `X^{ν,0} = 0`, `X^{ν,N+1}_h = Φ_{ν,h}(X^{ν,N})`. -/
noncomputable def branchIter (R : PosLocalDeletionRep V T) (ν : ℝ) (N : ℕ) (h : Hist R) : ℝ :=
  exactIter R Set.univ (fun _ => ν) N h

/-- The **canonical exact branch** `X^ν_h = lim_N X^{ν,N}_h` (B.2), written as the supremum of the
nondecreasing depth-`N` evaluations. -/
noncomputable def canonicalBranch (R : PosLocalDeletionRep V T) (ν : ℝ) (h : Hist R) : ℝ :=
  ⨆ N : ℕ, branchIter R ν N h

/-- A **symmetry preserving the representation** (Proposition 3.3(c), 3.4): a bijection of the sites
with compatible bijections of the options and of the labels, preserving activation and deletion
supports, coefficients, labels and the local orders. -/
structure RepSymmetry (R : PosLocalDeletionRep V T) where
  site : V ≃ V
  opt : ∀ v, R.Opt v ≃ R.Opt (site v)
  lab : T ≃ T
  A_map : ∀ v a, R.A (site v) (opt v a) = (R.A v a).map site.toEmbedding
  D_map : ∀ v a, R.D (site v) (opt v a) = (R.D v a).map site.toEmbedding
  c_map : ∀ v a, R.c (site v) (opt v a) = R.c v a
  label_map : ∀ v a, R.label (site v) (opt v a) = lab (R.label v a)
  rank_map : ∀ v a, ∀ w ∈ R.D v a, ∀ u ∈ R.D v a, w ≠ v → u ≠ v →
    (R.rank v a w < R.rank v a u ↔
      R.rank (site v) (opt v a) (site w) < R.rank (site v) (opt v a) (site u))

/-- The image of a history under a symmetry: every move `(v, a, u)` goes to `(γv, γa, γu)`. -/
def RepSymmetry.mapHist {R : PosLocalDeletionRep V T} (g : RepSymmetry R) (h : Hist R) : Hist R :=
  ⟨g.site h.start, h.moves.map (fun m => ⟨g.site m.1, g.opt m.1 m.2.1, g.site m.2.2⟩)⟩

end LocalLemmaHierarchy.Completeness


