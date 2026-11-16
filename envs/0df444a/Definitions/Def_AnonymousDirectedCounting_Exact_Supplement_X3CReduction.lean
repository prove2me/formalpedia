-- Prove2me | Definitions.Def_AnonymousDirectedCounting_Exact_Supplement_X3CReduction
-- name    : AnonymousDirectedCounting_Exact_Supplement_X3CReduction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:51:51.201084+00:00
-- url     : https://prove2.me/theorems/7e6d95d0-0cf3-421c-aa06-996b44f672a2
-- title:
--   Exact Cover by 3-Sets, the coefficients of Appendix F and the path and reference networks
-- statement:
--   Fix $q\ge2$ and distinct three-element subsets $S_1,\dots,S_m$ of $U=\{0,\dots,3q-1\}$. A set $J$ of indices is an **exact cover** if every element of $U$ lies in exactly one $S_j$ with $j\in J$.
--
--   The reduction constants are
--   $$B=q+3,\qquad K=B^{3q},\qquad W=\sum_{e=0}^{3q-1}B^e,\qquad A=qK+W,$$
--   $$c_0=A,\qquad c_j=K+\sum_{e\in S_j}B^e\ (1\le j\le m),\qquad C=B\sum_{i=0}^m c_i+A.$$
--   The reference group sizes are $a^0_0=B+1$ and $a^0_j=B$.
--
--   For group sizes $a_0,\dots,a_m$ there is one leader $\lambda$ and group $i$ consists of $x_{i,1},\dots,x_{i,a_i}$. The **path graph** has the arcs $x_{i,1}\to x_{i,2}\to\dots\to x_{i,a_i}\to\lambda$, one copy of each, and $c_i$ parallel arcs $\lambda\to x_{i,k}$ for every member of group $i$. The **ordinary star** keeps the leader's arcs and replaces the path arcs by one arc from every nonleader to $\lambda$. The **group network** uses the path graph in rounds $1,\dots,B-1$ and the ordinary star from round $B$ on; for the reference sizes its first $B$ rounds are the reference prefix $G^0$. The **reference vista** $\mathcal V$ is the round-$B$ vista of $\lambda$ in this network. The suffix of group $i$ after round $r$ is $\{x_{i,r+1},\dots,x_{i,a_i}\}$.
--
--   **Formalization Note** The $K$ here is the reduction coefficient of Appendix F.1, distinct from the bound $K=(1+\nu M)^t$ of Appendix E.2. Rounds after $B$ repeat the star; they do not affect round-$B$ vistas. The network is transported to the published model on $\{0,\dots,n-1\}$ through a fixed enumeration of its agents.
--
--   For an exact cover $J$, the alternative sizes are $a'_0=B$ and $a'_j=B+\mathbf1[j\in J]$. The adjusted final round doubles the special suffix's return to the leader and uses a two-agent chain ending at the leader in every selected suffix; every other nonleader returns once. This construction matches the reference leader's vista. A separate ordinary-star final round on the alternative prefix instead matches every reference nonleader's vista. Both keep the same leader-to-agent multiplicities. The explicit reference-prefix output lists each agent and each positive round-arc entry once, with its multiplicity in binary.
-- source:
--   Giuseppe A. Di Luna, Giovanni Viglietta, STOC 2027 submission #455 (October 2026), printed p. 28 (PDF p. 30), Appendix F.1–F.2; printed p. 29 (PDF p. 31)

import Mathlib
import Definitions.Def_AnonymousDirectedCounting_Exact_Supplement_Vistas

set_option autoImplicit false

namespace AnonymousDirectedCounting.Exact.Supplement

open AnonymousDirectedCounting.Exact
open scoped Classical

noncomputable section

/-- The standing assumptions of Appendix F.1 (printed p. 28, PDF p. 30): universe
`U = {0, …, 3q − 1}` with `q ≥ 2`, and distinct three-element subsets `S_1, …, S_m` of `U`
(indexed by `Fin m`). -/
def IsX3CInstance (q m : ℕ) (S : Fin m → Finset ℕ) : Prop :=
  2 ≤ q ∧ Function.Injective S ∧ ∀ j, S j ⊆ Finset.range (3 * q) ∧ (S j).card = 3

/-- `J` is an exact cover: every element of `U` lies in exactly one selected triple. -/
def IsExactCover (q m : ℕ) (S : Fin m → Finset ℕ) (J : Finset (Fin m)) : Prop :=
  ∀ e, e < 3 * q → (J.filter (fun j => e ∈ S j)).card = 1

/-- `B = q + 3`. -/
def baseB (q : ℕ) : ℕ := q + 3

/-- `K = B^{3q}` (the reduction coefficient of F.1, not the bound of E.2). -/
def coefK (q : ℕ) : ℕ := baseB q ^ (3 * q)

/-- `W = ∑_{e=0}^{3q−1} B^e`. -/
def coefW (q : ℕ) : ℕ := ∑ e ∈ Finset.range (3 * q), baseB q ^ e

/-- `A = qK + W`. -/
def coefA (q : ℕ) : ℕ := q * coefK q + coefW q

/-- `c_0 = A` and `c_j = K + ∑_{e ∈ S_j} B^e` for `1 ≤ j ≤ m` (group `j` is `Fin.succ` of the triple
index). -/
def coef (q m : ℕ) (S : Fin m → Finset ℕ) : Fin (m + 1) → ℕ :=
  Fin.cases (coefA q) (fun j => coefK q + ∑ e ∈ S j, baseB q ^ e)

/-- `C = B ∑_{i=0}^m c_i + A`, the leader's outdegree. -/
def leaderDegree (q m : ℕ) (S : Fin m → Finset ℕ) : ℕ :=
  baseB q * ∑ i, coef q m S i + coefA q

/-- The reference group sizes `a⁰_0 = B + 1`, `a⁰_j = B`. -/
def refSizes (q m : ℕ) : Fin (m + 1) → ℕ :=
  Fin.cases (baseB q + 1) (fun _ => baseB q)

/-- The agents of a network with group sizes `a`: the leader `λ = none` and the members
`x_{i,k+1} = some ⟨i, k⟩` (`k` is 0-based). -/
abbrev GroupAgent (m : ℕ) (a : Fin (m + 1) → ℕ) : Type :=
  Option (Σ i : Fin (m + 1), Fin (a i))

/-- The path graph (printed p. 29, PDF p. 31): `x_{i,1} → ⋯ → x_{i,a_i} → λ`, one copy each, and
`c_i` parallel arcs `λ → x_{i,k}` for every member of group `i`. -/
def pathArcs (q m : ℕ) (S : Fin m → Finset ℕ) (a : Fin (m + 1) → ℕ) :
    GroupAgent m a → GroupAgent m a → ℕ
  | none, none => 0
  | none, some p => coef q m S p.1
  | some p, none => if p.2.val + 1 = a p.1 then 1 else 0
  | some p, some p' => if p.1 = p'.1 ∧ p'.2.val = p.2.val + 1 then 1 else 0

/-- The ordinary star: one arc from every nonleader to `λ`, and the same leader-to-agent arcs. -/
def starArcs (q m : ℕ) (S : Fin m → Finset ℕ) (a : Fin (m + 1) → ℕ) :
    GroupAgent m a → GroupAgent m a → ℕ
  | none, none => 0
  | none, some p => coef q m S p.1
  | some _, none => 1
  | some _, some _ => 0

/-- A network on a finite agent type, transported to the published `NetworkModel` on `Fin`. -/
def ofFintype {α : Type} [Fintype α] (arcs : ℕ → α → α → ℕ) (L : Finset α) :
    NetworkModel (Fintype.card α) where
  arcs r x y := arcs r ((Fintype.equivFin α).symm x) ((Fintype.equivFin α).symm y)
  leaders := L.map (Fintype.equivFin α).toEmbedding

/-- The group network with sizes `a`: the path graph in rounds `1, …, B − 1`, the ordinary star
from round `B` on, one leader `λ`. With the reference sizes, rounds `1, …, B` form the reference
prefix `G⁰` (later rounds repeat the star and do not affect round-`B` histories). -/
def groupNetwork (q m : ℕ) (S : Fin m → Finset ℕ) (a : Fin (m + 1) → ℕ) :
    NetworkModel (Fintype.card (GroupAgent m a)) :=
  ofFintype (fun r => if r < baseB q then pathArcs q m S a else starArcs q m S a) {none}

/-- The agent `x_{i,k+1}` of the group network. -/
def memberAt (m : ℕ) (a : Fin (m + 1) → ℕ) (i : Fin (m + 1)) (k : Fin (a i)) :
    Fin (Fintype.card (GroupAgent m a)) :=
  Fintype.equivFin (GroupAgent m a) (some ⟨i, k⟩)

/-- The leader `λ` of the group network. -/
def leaderAt (m : ℕ) (a : Fin (m + 1) → ℕ) : Fin (Fintype.card (GroupAgent m a)) :=
  Fintype.equivFin (GroupAgent m a) none

/-- The suffix `{x_{i,r+1}, …, x_{i,a_i}}` of group `i`. -/
def suffixSet (m : ℕ) (a : Fin (m + 1) → ℕ) (i : Fin (m + 1)) (r : ℕ) :
    Finset (Fin (Fintype.card (GroupAgent m a))) :=
  (Finset.univ.filter (fun k : Fin (a i) => r ≤ k.val)).image (memberAt m a i)

/-- The reference leader vista `𝒱`: the round-`B` history of `λ` in the reference network. -/
def refVista (q m : ℕ) (S : Fin m → Finset ℕ) : History (baseB q) :=
  history (groupNetwork q m S (refSizes q m)) (baseB q) (leaderAt m (refSizes q m))

/-- The exact-cover alternative sizes of F.4: special group `B`, selected groups `B+1`,
and other groups `B`. No cover assumption is bundled into the data. -/
def alternativeSizes (q m : ℕ) (J : Finset (Fin m)) : Fin (m + 1) → ℕ :=
  Fin.cases (baseB q) (fun j => baseB q + if j ∈ J then 1 else 0)

/-- Whether a group is a selected triple group (group zero is never selected). -/
def selectedGroup {m : ℕ} (J : Finset (Fin m)) : Fin (m + 1) → Bool :=
  Fin.cases false (fun j => decide (j ∈ J))

/-- The adjusted final round matching the reference LEADER vista (F.4, pp.31–32 / PDF33–34).
Double the special last member's return; each selected two-member suffix is a chain into λ;
every other nonleader returns once. Leader-to-member multiplicities remain `c_i`. -/
def adjustedArcs (q m : ℕ) (S : Fin m → Finset ℕ) (J : Finset (Fin m)) :
    GroupAgent m (alternativeSizes q m J) → GroupAgent m (alternativeSizes q m J) → ℕ
  | none, none => 0
  | none, some p => coef q m S p.1
  | some p, none =>
    if p.1 = 0 ∧ p.2.val + 1 = alternativeSizes q m J p.1 then 2
    else if selectedGroup J p.1 = true ∧ p.2.val + 2 = alternativeSizes q m J p.1 then 0
    else 1
  | some p, some w =>
    if p.1 = w.1 ∧ selectedGroup J p.1 = true ∧
      p.2.val + 2 = alternativeSizes q m J p.1 ∧ w.2.val = p.2.val + 1 then 1 else 0

/-- Two alternatives with a common path prefix. `leaderMatch = true` uses the adjusted final
round; `false` uses the ordinary star, matching every reference NONLEADER vista instead.
The final graph is repeated thereafter. Changed outgoing degrees affect only the current
history: the old history has already been sent, as in the published late-awareness semantics. -/
def alternativeNetwork (q m : ℕ) (S : Fin m → Finset ℕ) (J : Finset (Fin m))
    (leaderMatch : Bool) : NetworkModel (Fintype.card (GroupAgent m (alternativeSizes q m J))) :=
  ofFintype (fun r => if r < baseB q then pathArcs q m S (alternativeSizes q m J)
    else if leaderMatch then adjustedArcs q m S J else starArcs q m S (alternativeSizes q m J))
    {none}

/-- An explicit prefix of a given network: one bit per agent, one entry per nonzero
ordered-pair multiplicity per round. Parallel copies are never expanded. -/
def prefixOfNetwork {N : ℕ} (G : NetworkModel N) (t : ℕ) : PrefixInput where
  order := N
  rounds := t
  leaderBits := List.ofFn (fun x : Fin N => decide (x ∈ G.leaders))
  arcs := (Finset.Icc 1 t).toList.flatMap fun r =>
    (Finset.univ : Finset (Fin N)).toList.flatMap fun x =>
      ((Finset.univ : Finset (Fin N)).filter (fun y => 0 < G.arcs r x y)).toList.map
        (fun y => (r, x.val, y.val, G.arcs r x y))

/-- The actual output `G⁰` of the network reduction, with its ordinary-star final round. -/
def referencePrefix (q m : ℕ) (S : Fin m → Finset ℕ) : PrefixInput :=
  prefixOfNetwork (groupNetwork q m S (refSizes q m)) (baseB q)

end

end AnonymousDirectedCounting.Exact.Supplement


