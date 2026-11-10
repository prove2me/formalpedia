-- Prove2me | Definitions.Def_MinColorPath_MinorFree_CombineFilter
-- name    : MinColorPath_MinorFree_CombineFilter
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T04:12:47.580795+00:00
-- url     : https://prove2.me/theorems/e1b9111c-d1f3-4233-8b34-a179ee5a8e94
-- title:
--   Algorithm 1 (Combine&Filter) as a relation over all tie-breaks; (w, c)-good decompositions; covering sets
-- statement:
--   **Algorithm 1** (Combine&Filter) on $(\mathcal G,s,t,w,c)$ starts from $F=\mathrm{pow}_w(P)=\{Q\subseteq P:|Q|\le w\}$ and repeats $n+|P|$ times ($n=|V(G)|$):
--   $$F^+=\{Q'\cup Q''\cup B: Q',Q''\in F,\ B\in\mathrm{pow}_w(P)\},$$
--   then **Filter**: for every job $(s_1,t_1,\dots,s_c,t_c)\in V(G)^{2c}$ and $B\in\mathrm{pow}_w(P)$ it collects $F'=\{Q'\in F^+: B\subseteq Q',\ \mathrm{cdist}(\mathcal G-Q',s_i,t_i)=0\ \forall i\}$ and, if $F'\ne\emptyset$, adds one minimum-size member of $F'$ to the new $F$. Finally $Q^*$ is a minimum-size member of $\{Q\in F:\mathrm{cdist}(\mathcal G-Q,s,t)=0\}$ and the algorithm returns an $(s,t)$-path $\pi^*$ with $\mathrm{cl}(V(\pi^*))\subseteq Q^*$.
--
--   A tree decomposition of the $0$-diagram of an $(s,t)$-path $\pi$ is **$(w,c)$-good** if its chromatic width is at most $w$, the crossing number of $\pi$ is at most $c$ and $s,t$ lie in every bag. For a node $x$, $P'(x)=\mathrm{cl}'(\gamma(x))$, and $Q\subseteq P$ **covers** $x$ if $\mathrm{cl}'(\beta(x))\subseteq Q$ and $\mathrm{cdist}(\mathcal G-Q,a,b)=0$ for the left and right endpoints $(a,b)$ of every $x$-segment.
--
--   **Formalization Note.** Every arg min is an arbitrary choice, so the algorithm is modelled as a relation: `FilterRel` holds for each family obtainable with some choice function `ch` (one minimum-size qualifying member per job); `IsRun Fs` says `Fs 0 = pow_w(P)` and `Fs (i+1)` is a Filter result of `Combine (Fs i)` for `i < n + |P|`; `IsOutput Fs π` says `π` is a path the run can return. Jobs are functions `Fin c → V × V`.
-- source:
--   Ajaykrishnan E S, Lokshtanov, Saurabh, Xue, Algorithms for Min-Color Path with Bounded Color-Degree, STOC 2027 submission (manuscript sha256 a088a67b…), p. 4, Algorithm 1; pp. 21–22, (w, c)-good, pairs(x), covers

import Mathlib
import Definitions.Def_MinColorPath_MinorFree_TreeDecomposition

set_option autoImplicit false

/-!
# Algorithm 1 (Combine&Filter) as a mathematical object, and covering sets (pp. 4, 21–22)

Ajaykrishnan E S, Lokshtanov, Saurabh, Xue, *Algorithms for Min-Color Path with Bounded
Color-Degree* (STOC 2027 submission), p. 4 (Algorithm 1), pp. 21–22 (`(w, c)`-good, `pairs(x)`,
covers).

Conventions.
* `pow_w(P) = {Q ⊆ P : |Q| ≤ w}`.
* Every `arg min` of Algorithm 1 is an arbitrary choice. A run is therefore a relation: `FilterRel`
  holds for every family the Filter step can return under some choice of a minimum-size member
  for each job, and `IsRun` / `IsOutput` describe every run and every returned path. The jobs
  `(s_1, t_1, …, s_c, t_c) ∈ V(G)^{2c}` are functions `Fin c → V × V`.
* The loop runs `n + |P|` times with `n = |V|`; `Fs i` is the family after the `i`-th iteration
  and `Fs 0` the initial family.
-/

namespace MinColorPath.MinorFree

noncomputable section

open Classical

variable {V C : Type} [Fintype V] [DecidableEq V] [DecidableEq C]

/-- `pow_w(P) = {Q ⊆ P : |Q| ≤ w}` (p. 17). -/
def powW (P : Finset C) (w : ℕ) : Finset (Finset C) := P.powerset.filter fun Q => Q.card ≤ w

/-- `Combine(F, P, w) = {Q' ∪ Q'' ∪ B : Q', Q'' ∈ F, B ∈ pow_w(P)}` (Algorithm 1, line 10). -/
def combine (F : Finset (Finset C)) (P : Finset C) (w : ℕ) : Finset (Finset C) :=
  (F ×ˢ F ×ˢ powW P w).image fun x => x.1 ∪ x.2.1 ∪ x.2.2

/-- `Q'` qualifies for the job `(σ, B)` of Filter (line 15): `B ⊆ Q'` and
`cdist(G − Q', s_i, t_i) = 0` for all `i ∈ [c]`. -/
def JobOK (G : SimpleGraph V) (cl : V → Finset C) {c : ℕ} (σ : Fin c → V × V) (B Q : Finset C) :
    Prop :=
  B ⊆ Q ∧ ∀ i, cdist G (fun v => cl v \ Q) (σ i).1 (σ i).2 = 0

/-- `F` is a possible result of `Filter(F⁺, G, w, c)` (lines 12–19): for some choice `ch` of a
minimum-size qualifying member for every job whose qualifying family `F'` is nonempty, `F` is
the set of chosen members. -/
def FilterRel (G : SimpleGraph V) (P : Finset C) (cl : V → Finset C) (w c : ℕ)
    (Fplus F : Finset (Finset C)) : Prop :=
  ∃ ch : (Fin c → V × V) → Finset C → Finset C,
    (∀ σ B, B ∈ powW P w → (∃ Q ∈ Fplus, JobOK G cl σ B Q) →
      ch σ B ∈ Fplus ∧ JobOK G cl σ B (ch σ B) ∧
        ∀ Q ∈ Fplus, JobOK G cl σ B Q → (ch σ B).card ≤ Q.card) ∧
    ∀ Q, Q ∈ F ↔ ∃ σ B, B ∈ powW P w ∧ (∃ Q' ∈ Fplus, JobOK G cl σ B Q') ∧ ch σ B = Q

/-- `Fs` is a run of the main loop of Algorithm 1 on `(G, s, t, w, c)` (lines 1–4):
`Fs 0 = pow_w(P)` and `Fs (i+1)` is a Filter result of `Combine(Fs i, P, w)` for each of the
`n + |P|` iterations. -/
def IsRun (G : SimpleGraph V) (P : Finset C) (cl : V → Finset C) (w c : ℕ)
    (Fs : ℕ → Finset (Finset C)) : Prop :=
  Fs 0 = powW P w ∧
    ∀ i < Fintype.card V + P.card, FilterRel G P cl w c (combine (Fs i) P w) (Fs (i + 1))

/-- `π*` is a path the run `Fs` can return (lines 5–8): `Q*` is a minimum-size member of
`F* = {Q ∈ F : cdist(G − Q, s, t) = 0}` and `π*` is an `(s, t)`-path with `cl(V(π*)) ⊆ Q*`. -/
def IsOutput (G : SimpleGraph V) (P : Finset C) (cl : V → Finset C) (s t : V)
    (Fs : ℕ → Finset (Finset C)) (π : G.Walk s t) : Prop :=
  π.IsPath ∧ ∃ Q ∈ Fs (Fintype.card V + P.card),
    cdist G (fun v => cl v \ Q) s t = 0 ∧
    (∀ Q' ∈ Fs (Fintype.card V + P.card), cdist G (fun v => cl v \ Q') s t = 0 →
      Q.card ≤ Q'.card) ∧
    colSet cl π.support.toFinset ⊆ Q

/-- A tree decomposition of the 0-diagram of an `(s, t)`-path `π` is `(w, c)`-good (p. 21):
chromatic width at most `w`, crossing number of `π` at most `c`, and `s, t` in every bag. -/
def IsGood {G : SimpleGraph V} {cl : V → Finset C} {s t : V} {π : G.Walk s t}
    (𝒯 : RTD (pathDiag cl 0 π)) (w c : ℕ) : Prop :=
  diagWidth 𝒯 ≤ w ∧ pathCrossing 𝒯 ≤ c ∧ TerminalsInBags 𝒯 s t

/-- `P'(x) = cl'(γ(x))` (p. 21). -/
def RTD.palBelow {G : SimpleGraph V} {cl : V → Finset C} {s t : V} {d : ℕ} {π : G.Walk s t}
    (𝒯 : RTD (pathDiag cl d π)) (x : 𝒯.T) : Finset C :=
  colSet (diagCl cl π.toSubgraph) (𝒯.gamma x)

/-- `Q` covers the node `x` (p. 22): `cl'(β(x)) ⊆ Q` and `cdist(G − Q, a, b) = 0` for every
`(a, b) ∈ pairs(x)`, the left and right endpoints of the `x`-segments of `π`. -/
def Covers (G : SimpleGraph V) (cl : V → Finset C) {s t : V} {π : G.Walk s t}
    (𝒯 : RTD (pathDiag cl 0 π)) (Q : Finset C) (x : 𝒯.T) : Prop :=
  colSet (diagCl cl π.toSubgraph) (𝒯.bag x) ⊆ Q ∧
    ∀ i j : Fin π.support.length, 𝒯.IsSegment baseIn π.support x i j →
      cdist G (fun v => cl v \ Q) (π.support.get i) (π.support.get j) = 0

end

end MinColorPath.MinorFree


