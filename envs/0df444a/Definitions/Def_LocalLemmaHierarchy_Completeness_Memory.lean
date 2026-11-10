-- Prove2me | Definitions.Def_LocalLemmaHierarchy_Completeness_Memory
-- name    : LocalLemmaHierarchy_Completeness_Memory
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T00:19:20.131009+00:00
-- url     : https://prove2.me/theorems/3e960d06-f4c3-4090-8935-27fb31626313
-- title:
--   The memory-$q$ system $S_q$, its update $F_{q,p}$, certificates, $R_q$, and finite grouped presentations
-- statement:
--   Fix $q\ge0$ (Definition 3.1). A **state** $s\in S_q$ is an ambient exact history of at most $q$ moves; shorter ones (including every one-site history) are startup states. $B_q(s)$ is the union of the departure sets of its moves. An option $a$ at $v=v(s)$ is available when $A_{v,a}\cap B_q(s)=\emptyset$; its factors are $D_{v,a}\setminus(\{v\}\cup B_q(s))$. For a factor $u$, $s\star_q(a,u)$ appends $(v,a,u)$ and keeps the last $q$ moves (legality is tested before forgetting). The update (3.1) is
--   $$(F_{q,p}(x))_s=\sum_{a:\,A_{v,a}\cap B_q(s)=\emptyset}c_{v,a}p_{\tau(v,a)}\prod_{u\in D_{v,a}\setminus(\{v\}\cup B_q(s))}\bigl(1-x_{s\star_q(a,u)}\bigr)^{-1},$$
--   a **certificate** at moduli $p$ is $x\in[0,1)^{S_q}$ with $F_{q,p}(x)\le x$, and the **memory-$q$ threshold** (3.2) is $R_q(\mathcal R)=\sup\{t\ge0: F_{q,t}(x)\le x \text{ for some } x\in[0,1)^{S_q}\}$ (uniform moduli $t$). `memIter` is the iteration $x^{(0)}=0$, $x^{(n+1)}=F_{q,p}(x^{(n)})$ of Proposition 3.3.
--
--   A **finite grouped presentation** (§3.1) of $S_q$ at moduli $p$ is a finite set $\Theta$ of types, a typing of states onto $\Theta$, and for each type a row (a multiset over options of pairs: coefficient $c_{v,a}p_{\tau(v,a)}$ and multiset of child types), such that every state's row, read through the typing, is the row of its type. Its update has one variable per type, $G(y)_k=\sum_{(w,C)}w\prod_{k'\in C}(1-y_{k'})^{-1}$; a certificate is $y\in[0,1)^\Theta$ with $G(y)\le y$. For a presentation built at unit moduli, its radius is the supremum of $t\ge0$ for which the update with all coefficients multiplied by $t$ has a certificate (the uniform-moduli condition is the same for every $t>0$).
--
--   Finally, `productRowUpdate` is the abstract row form of Lemmas 3.5 and F.1: $F_s(x)=\sum_{a\in A_s}t_{s,a}\prod_{u\in C(s,a)}(1-x_u)^{-1}$ with a finite option set and a finite multiset of factor occurrences per row.
--
--   **Formalization Note.** A vector on states is a function on all histories, constrained only at states (`IsMemCertificate`); rows at states read only states. Options and factors keep their multiplicities (sums over a `Finset` of options, products over a `Finset` of factor sites, one factor per (option, site)). $R_q$ is in `ℝ≥0∞`.
-- source:
--   Achlioptas, Kritharidis and Zampetakis, A Complete Hierarchy of Local Lemmas, STOC 2027 submission (manuscript sha256 bc1388b0…a434b961), Definition 3.1 and (3.1)–(3.2), printed p. 8 (PDF p. 10); finite grouped presentations, §3.1, printed p. 8; Lemma 3.5 row form, printed p. 9 (PDF p. 11)

import Mathlib
import Definitions.Def_LocalLemmaHierarchy_Completeness_Representation
import Definitions.Def_LocalLemmaHierarchy_Completeness_Histories

open scoped ENNReal NNReal

namespace LocalLemmaHierarchy.Completeness

variable {V T : Type}

/-- A **state of the memory-`q` system** `S_q` (Definition 3.1): an ambient exact history of at most
`q` moves. Shorter histories, in particular every one-site history, are startup states. -/
def IsMemState (R : PosLocalDeletionRep V T) (q : ℕ) (s : Hist R) : Prop :=
  IsExact R Set.univ s ∧ s.moves.length ≤ q

/-- `s ★_q (a, u)`: append the move `(v(s), a, u)` and keep the last `q` moves, or the whole history
when it is shorter (Definition 3.1). -/
def memStar {R : PosLocalDeletionRep V T} (q : ℕ) (s : Hist R) (a : R.Opt s.endpoint) (u : V) :
    Hist R :=
  (s.append ⟨s.endpoint, a, u⟩).suffix q

open Classical in
/-- The memory-`q` update (3.1) at a state `s` with endpoint `v`, at moduli `p`:
`(F_{q,p}(x))_s = ∑_{a ∈ A(v), A_{v,a} ∩ B_q(s) = ∅} c_{v,a} p_{τ(v,a)}
  ∏_{u ∈ D_{v,a} \ ({v} ∪ B_q(s))} (1 − x_{s ★_q (a,u)})⁻¹`,
where `B_q(s)` is the union of the departure sets retained in `s` (all of its at most `q` moves).
Legality is tested against the whole state before the oldest move is forgotten by `★_q`.
One factor per (option, factor site) occurrence. -/
noncomputable def memUpdate (R : PosLocalDeletionRep V T) (q : ℕ) (p : T → ℝ) (x : Hist R → ℝ)
    (s : Hist R) : ℝ :=
  ∑ a ∈ Finset.univ.filter
      (fun a : R.Opt s.endpoint => Disjoint (R.A s.endpoint a) (deleted R s.moves)),
    R.c s.endpoint a * p (R.label s.endpoint a) *
      ∏ u ∈ R.D s.endpoint a \ insert s.endpoint (deleted R s.moves),
        (1 - x (memStar q s a u))⁻¹

/-- A **memory-`q` certificate** at moduli `p` (Definition 3.1): a vector `x ∈ [0, 1)^{S_q}`
(each coordinate in `[0,1)`) with `F_{q,p}(x) ≤ x` at every state. The vector is a function on all
histories; only its values at states are constrained, and the rows at states only read states. -/
def IsMemCertificate (R : PosLocalDeletionRep V T) (q : ℕ) (p : T → ℝ) (x : Hist R → ℝ) : Prop :=
  ∀ s : Hist R, IsMemState R q s → 0 ≤ x s ∧ x s < 1 ∧ memUpdate R q p x s ≤ x s

/-- The memory-`q` threshold (3.2): `R_q(R) = sup{t ≥ 0 : F_{q,t}(x) ≤ x for some x ∈ [0,1)^{S_q}}`,
uniform moduli `t`, in `[0, ∞]`. -/
noncomputable def memRadius (R : PosLocalDeletionRep V T) (q : ℕ) : ℝ≥0∞ :=
  ⨆ (t : ℝ≥0) (_ : ∃ x : Hist R → ℝ, IsMemCertificate R q (fun _ => (t : ℝ)) x), (t : ℝ≥0∞)

/-- The monotone iteration of Proposition 3.3(a): `x^(0) = 0`, `x^(n+1) = F_{q,p}(x^(n))`. -/
noncomputable def memIter (R : PosLocalDeletionRep V T) (q : ℕ) (p : T → ℝ) : ℕ → Hist R → ℝ
  | 0 => fun _ => 0
  | n + 1 => memUpdate R q p (memIter R q p n)

open Classical in
/-- The row of the memory-`q` system at a state `s`, read through a typing `θ` of histories: the
multiset, over the available options `a` (with multiplicity), of the pair (coefficient
`c_{v,a} p_{τ(v,a)}`, multiset of the types of the child occurrences `s ★_q (a,u)`). -/
noncomputable def memRowData (R : PosLocalDeletionRep V T) (q : ℕ) (p : T → ℝ) {Θ : Type}
    (θ : Hist R → Θ) (s : Hist R) : Multiset (ℝ × Multiset Θ) :=
  (Finset.univ.filter
      (fun a : R.Opt s.endpoint => Disjoint (R.A s.endpoint a) (deleted R s.moves))).val.map
    (fun a => (R.c s.endpoint a * p (R.label s.endpoint a),
      (R.D s.endpoint a \ insert s.endpoint (deleted R s.moves)).val.map
        (fun u => θ (memStar q s a u))))

/-- The update of a grouped system with one variable per type: the row of type `k` is a multiset of
(coefficient, multiset of child types) and gives `∑ coefficient · ∏ (1 − y_child)⁻¹`. -/
noncomputable def groupedUpdate {Θ : Type} (rows : Θ → Multiset (ℝ × Multiset Θ)) (y : Θ → ℝ)
    (k : Θ) : ℝ :=
  ((rows k).map (fun r => r.1 * (r.2.map (fun k' => (1 - y k')⁻¹)).prod)).sum

/-- A **finite grouped presentation** of the memory-`q` system at moduli `p` (§3.1): finitely many
types, every type is the type of some state, and states of the same type have identical rows
(every option the same coefficient `c_{v,a} p_{τ(v,a)}` and multiset of child types; options and
repeated factors keep their multiplicities). The update then has one variable per type. -/
structure GroupedPresentation (R : PosLocalDeletionRep V T) (q : ℕ) (p : T → ℝ) where
  Θ : Type
  fintypeΘ : Fintype Θ
  type : Hist R → Θ
  rows : Θ → Multiset (ℝ × Multiset Θ)
  type_surj : ∀ k : Θ, ∃ s, IsMemState R q s ∧ type s = k
  row_eq : ∀ s, IsMemState R q s → memRowData R q p type s = rows (type s)

/-- A certificate of a grouped presentation: `y ∈ [0,1)^Θ` with `G(y) ≤ y`. -/
def GroupedPresentation.IsCertificate {R : PosLocalDeletionRep V T} {q : ℕ} {p : T → ℝ}
    (P : GroupedPresentation R q p) (y : P.Θ → ℝ) : Prop :=
  ∀ k, 0 ≤ y k ∧ y k < 1 ∧ groupedUpdate P.rows y k ≤ y k

/-- The certified radius of a finite grouped presentation built at unit moduli `p = 1` (rows with
coefficients `c_{v,a}`): the supremum of the uniform moduli `t ≥ 0` for which the grouped update
with every coefficient multiplied by `t` has a certificate. -/
noncomputable def GroupedPresentation.radius {R : PosLocalDeletionRep V T} {q : ℕ}
    (P : GroupedPresentation R q (fun _ => 1)) : ℝ≥0∞ :=
  ⨆ (t : ℝ≥0) (_ : ∃ y : P.Θ → ℝ,
      ∀ k, 0 ≤ y k ∧ y k < 1 ∧ (t : ℝ) * groupedUpdate P.rows y k ≤ y k), (t : ℝ≥0∞)

/-- An abstract system of rows of the form used in Lemmas 3.5 and F.1:
`F_s(x) = ∑_{a ∈ A_s} t_{s,a} ∏_{u ∈ C(s,a)} (1 − x_u)⁻¹`, with a finite option set `A_s` and a
finite multiset `C(s,a)` of factor occurrences in each row. -/
noncomputable def productRowUpdate {S ι : Type} (A : S → Finset ι) (t : S → ι → ℝ)
    (C : S → ι → Multiset S) (x : S → ℝ) (s : S) : ℝ :=
  ∑ a ∈ A s, t s a * ((C s a).map (fun u => (1 - x u)⁻¹)).prod

end LocalLemmaHierarchy.Completeness


