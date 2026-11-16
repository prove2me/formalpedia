-- Prove2me | Definitions.Def_MeanCertificates1424_Hardness_Supplement_General
-- name    : MeanCertificates1424_Hardness_Supplement_General
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T08:53:05.351207+00:00
-- url     : https://prove2.me/theorems/f21b77a6-98d3-497d-a033-86354001dfc6
-- title:
--   Real audited weighted model: feasible class, endpoints, components, envelopes, alphabets, counters, depth, radius, cycle gaps
-- statement:
--   This file extends the published uniform rational model of the mission to the full model of §2. An **instance** consists of a connected simple graph $G=(V,E)$ on $V=\{0,\dots,n-1\}$, $n\ge 1$, with shortest-path metric $d_G$, a replacement budget $b\in\{0,\dots,n\}$, a Lipschitz constant $L>0$, a noise level $\epsilon\ge 0$, an arbitrary real report vector $y\in\mathbb R^V$, nonnegative weights $w$ with $\sum_v w_v=1$, and trusted audits on $Q\subseteq V$ given by finite intervals $[\alpha_q,\beta_q]$, $\alpha_q\le\beta_q$. The **feasible class** is
--
--   $$
--   C_I(y)=\{x\in\mathbb R^V:\ |x_u-x_v|\le L\ (uv\in E),\ |\{v:|x_v-y_v|>\epsilon\}|\le b,\ x_q\in[\alpha_q,\beta_q]\ (q\in Q)\},
--   $$
--
--   with one common mismatch budget for the whole field; audits constrain the field, not the reports. The weighted mean is $\mu_w(x)=\sum_v w_vx_v$, and the exact certificate endpoints $\ell_I(y)$, $u_I(y)$ are the infimum and supremum of $\mu_w$ over $C_I(y)$ in the extended reals ($+\infty$ and $-\infty$ on the empty class). The instance is **anchored** if $b<n$ or $Q\neq\emptyset$; the midpoint is $(\ell_I+u_I)/2$.
--
--   For an honest set $H$ the **component** $P_H$ requires $|x_i-y_i|\le\epsilon$ on $H$ and the audit constraints. Its **anchors** are the report anchors $(i,y_i-\epsilon,y_i+\epsilon)$, $i\in H$, and the audit anchors $(q,\alpha_q,\beta_q)$; a vertex both honest and audited carries two anchors with distinct identities. The **envelopes** are $U^H_v=\min_a(\beta_a+Ld_G(a,v))$ and $\Lambda^H_v=\max_a(\alpha_a-Ld_G(a,v))$. The full alphabets $A^\pm_v$ collect all source cones $y_i\pm(\epsilon+Ld_G(i,v))$ and $\beta_q+Ld_G(q,v)$, $\alpha_q-Ld_G(q,v)$. The **truncated alphabet** $A^+_{v,b}$ is the set of numerical values of the first $b+1$ sources at $v$ in increasing order of cone value, ties broken by a fixed injective order on source identities (ranks are taken over identities; duplicates removed only after truncation); $A^-_{v,b}$ applies this to $-y$ and the reflected intervals $[-\beta_q,-\alpha_q]$ and negates.
--
--   The file also defines the mismatch counters of §4.2 (the bounded mismatch counter if $b\le h=n-b$, the honest counter saturated at $h$ if $h<b$, their composition and acceptance), merge trees for Lemma 4.9, the incidence split graph $G_H$ and $\nu_p(H)=\min\{|V(F)|:F\subseteq E(H),|F|=p\}$ of §3.4, distances to sets with $d_G(v,\emptyset)=+\infty$, the depth $\Psi_G(m)=\max_{|S|\le m}\sum_{v\in S}d_G(v,V\setminus S)$ and $\Psi_{G,Q}$, the potentials $g_{S,Q}(v)=\min\{Ld_G(v,Q),\epsilon+Ld_G(v,V\setminus S)\}$, the global minimax radius
--
--   $$
--   R^*_{Q,w}(G,b,L,\epsilon)=\inf_{\hat\mu}\ \sup_{x\in H_L(G)}\ \sup_{y:\,|\{v:|y_v-x_v|>\epsilon\}|\le b}\ |\hat\mu(y,x_Q)-\mu_w(x)|
--   $$
--
--   over all estimators (the uniform $R^*_Q$ is $w_v=1/n$), the midpoint estimator, and the gaps of an audit set on the cycle $C_n$ with $F(a)=\lfloor (a+1)^2/4\rfloor$.
--
--   These objects are shared by every analytic and algorithmic statement of the supplement.
--
--   **Formalization Note** The published rational uniform unaudited instance embeds by `ofUniform`, and two proved lemmas show that it has the same feasible class and the same mean. Endpoints live in `EReal`, radii and $g_{S,Q}$ in $[0,\infty]$; with $L>0$ no product $0\cdot\infty$ occurs. Envelopes are real minima over the anchor set and are used only for components with at least one anchor.
-- source:
--   chaomeng chen, Junhao Dong, STOC 2027 submission #1424 (October 2026), Section 2 (printed pp.5–6, PDF pp.7–8); §3.4 (printed p.11, PDF p.13); §4.1–4.2 (printed pp.12–15, PDF pp.14–17); Lemma 4.9 (printed p.16, PDF p.18); §6 eqs. (2.2), (6.1), (6.4), (6.6), Remark 6.5 (printed pp.6, 19–21, PDF pp.8, 21–23); Appendix A.1 (printed p.23, PDF p.25)

import Mathlib
import Definitions.Def_MeanCertificates1424_Hardness_Model

set_option autoImplicit false

namespace MeanCertificates1424.Hardness.Supplement

open MeanCertificates1424.Hardness

/-! # §2 model with real data, weights and audit intervals (printed pp.5–6, PDF pp.7–8)

The published `UniformInstance` is the rational, unaudited, uniform-mean specialization.
The supplement's analytic statements need arbitrary real reports, noise, Lipschitz
constants, weights and finite audit intervals, so the minimal extension is defined here. -/

/-- An instance of §2: graph on `Fin n`, budget `b`, Lipschitz constant `L`, noise `ε`,
reports `y`, weights `w`, audit set `Q` and audit intervals `[lo q, hi q]` for `q ∈ Q`
(the values of `lo`, `hi` off `Q` are never used). -/
structure Inst where
  n : ℕ
  graph : SimpleGraph (Fin n)
  budget : ℕ
  lip : ℝ
  noise : ℝ
  reports : Fin n → ℝ
  weights : Fin n → ℝ
  audits : Finset (Fin n)
  lo : Fin n → ℝ
  hi : Fin n → ℝ

/-- Standing assumptions of §2: `n ≥ 1`, connected simple graph, `L > 0`, `ε ≥ 0`,
`b ∈ {0,…,n}`, nonnegative weights summing to one, finite audit intervals `α_q ≤ β_q`. -/
def Valid (I : Inst) : Prop :=
  1 ≤ I.n ∧ I.graph.Connected ∧ 0 < I.lip ∧ 0 ≤ I.noise ∧ I.budget ≤ I.n ∧
  (∀ v, 0 ≤ I.weights v) ∧ ∑ v, I.weights v = 1 ∧ ∀ q ∈ I.audits, I.lo q ≤ I.hi q

/-- Anchored: `b < n` or some audit (printed p.6, PDF p.8). -/
def Anchored (I : Inst) : Prop := I.budget < I.n ∨ I.audits.Nonempty

/-- `H_L(G)`: `|x_u − x_v| ≤ L` on every edge. -/
def Lipschitz (I : Inst) (x : Fin I.n → ℝ) : Prop :=
  ∀ u v, I.graph.Adj u v → |x u - x v| ≤ I.lip

/-- The mismatched vertices of a field `x`: `|x_v − y_v| > ε`. -/
noncomputable def mismatches (I : Inst) (x : Fin I.n → ℝ) : Finset (Fin I.n) :=
  Finset.univ.filter fun v => I.noise < |x v - I.reports v|

/-- Audits constrain the field (not the reports). -/
def AuditOK (I : Inst) (x : Fin I.n → ℝ) : Prop :=
  ∀ q ∈ I.audits, I.lo q ≤ x q ∧ x q ≤ I.hi q

/-- The feasible class `C_I(y)`: one common mismatch budget for the entire field. -/
def CI (I : Inst) : Set (Fin I.n → ℝ) :=
  {x | Lipschitz I x ∧ (mismatches I x).card ≤ I.budget ∧ AuditOK I x}

/-- The weighted mean `µ_w(x) = ∑_v w_v x_v`. -/
def wmean (I : Inst) (x : Fin I.n → ℝ) : ℝ := ∑ v, I.weights v * x v

/-- Exact certificate endpoints in the complete lattice `EReal`
(`+∞`/`−∞` on the empty class; infinite on unbounded classes). -/
noncomputable def lower (I : Inst) : EReal := sInf ((fun x => (wmean I x : EReal)) '' CI I)

noncomputable def upper (I : Inst) : EReal := sSup ((fun x => (wmean I x : EReal)) '' CI I)

/-- The midpoint (2.1). Used only on nonempty anchored instances, where both endpoints
are finite; there `toReal` is the identity on the endpoint values. -/
noncomputable def midpoint (I : Inst) : ℝ := ((lower I).toReal + (upper I).toReal) / 2

/-- Uniform weights `w_v = 1/n`. -/
noncomputable def uniformW (n : ℕ) : Fin n → ℝ := fun _ => 1 / (n : ℝ)

/-- Embedding of the published rational uniform unaudited instance. -/
noncomputable def ofUniform (J : UniformInstance) : Inst where
  n := J.n
  graph := J.graph
  budget := J.budget
  lip := J.lipschitz
  noise := J.noise
  reports := fun v => (J.reports v : ℝ)
  weights := uniformW J.n
  audits := ∅
  lo := fun _ => 0
  hi := fun _ => 0

/-- Compatibility with the published Model: same feasible class. -/
theorem mismatches_ofUniform (J : UniformInstance) (x : Fin J.n → ℝ) :
    mismatches (ofUniform J) x = Hardness.mismatches J x := by
  refine Finset.ext fun (v : Fin J.n) => ?_
  unfold mismatches Hardness.mismatches
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, gt_iff_lt]
  rfl

theorem CI_ofUniform (J : UniformInstance) : CI (ofUniform J) = feasible J := by
  ext x
  have hm := mismatches_ofUniform J x
  constructor
  · rintro ⟨h1, h2, -⟩
    refine ⟨h1, ?_⟩
    show (Hardness.mismatches J x).card ≤ J.budget
    rw [← hm]
    exact h2
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_, ?_⟩
    · show (mismatches (ofUniform J) x).card ≤ J.budget
      rw [hm]
      exact h2
    · intro q hq
      exact absurd hq (Finset.notMem_empty q)

/-- Compatibility with the published Model: same mean. -/
theorem wmean_ofUniform (J : UniformInstance) (x : Fin J.n → ℝ) :
    wmean (ofUniform J) x = mean J x := by
  simp only [wmean, ofUniform, uniformW, mean, one_div]
  rw [← Finset.mul_sum, inv_mul_eq_div]
  rfl

/-! ## Honest components, anchors and envelopes (§4.1, printed pp.12–13, PDF pp.14–15) -/

/-- Source identities: `inl i` is the report anchor of vertex `i`, `inr q` the audit anchor
of `q`; a vertex that is reported and audited carries two identities. -/
abbrev Source (n : ℕ) := Fin n ⊕ Fin n

def srcLoc {n : ℕ} : Source n → Fin n
  | Sum.inl i => i
  | Sum.inr q => q

/-- Lower end `α_a` of an anchor: `y_i − ε` for a report, `lo q` for an audit. -/
def srcLo (I : Inst) : Source I.n → ℝ
  | Sum.inl i => I.reports i - I.noise
  | Sum.inr q => I.lo q

/-- Upper end `β_a` of an anchor: `y_i + ε` for a report, `hi q` for an audit. -/
def srcHi (I : Inst) : Source I.n → ℝ
  | Sum.inl i => I.reports i + I.noise
  | Sum.inr q => I.hi q

/-- All `n + |Q|` sources: every report anchor and every audit anchor. -/
def sources (I : Inst) : Finset (Source I.n) :=
  Finset.univ.map Function.Embedding.inl ∪ I.audits.map Function.Embedding.inr

/-- Anchors of the component `P_H`: report anchors of `H` and all audit anchors. -/
def anchorsOf (I : Inst) (H : Finset (Fin I.n)) : Finset (Source I.n) :=
  H.map Function.Embedding.inl ∪ I.audits.map Function.Embedding.inr

/-- The component `P_H = {x ∈ H_L(G) : |x_i − y_i| ≤ ε (i ∈ H), x_q ∈ I_q (q ∈ Q)}`. -/
def PH (I : Inst) (H : Finset (Fin I.n)) : Set (Fin I.n → ℝ) :=
  {x | Lipschitz I x ∧ (∀ i ∈ H, |x i - I.reports i| ≤ I.noise) ∧ AuditOK I x}

/-- Graph distance used in cones (unit edge lengths, `G` connected). -/
noncomputable def gdist (I : Inst) (u v : Fin I.n) : ℝ := (I.graph.dist u v : ℝ)

/-- Upper envelope `U^H_v = min_a (β_a + L d_G(a, v))`. Used only for components with
a nonempty anchor set, where this is a minimum over a finite nonempty set. -/
noncomputable def UH (I : Inst) (H : Finset (Fin I.n)) (v : Fin I.n) : ℝ :=
  sInf (((anchorsOf I H).image fun a => srcHi I a + I.lip * gdist I (srcLoc a) v : Finset ℝ) :
    Set ℝ)

/-- Lower envelope `Λ^H_v = max_a (α_a − L d_G(a, v))` (nonempty anchor set). -/
noncomputable def LH (I : Inst) (H : Finset (Fin I.n)) (v : Fin I.n) : ℝ :=
  sSup (((anchorsOf I H).image fun a => srcLo I a - I.lip * gdist I (srcLoc a) v : Finset ℝ) :
    Set ℝ)

/-- Full upper alphabet `A⁺_v = {y_i + ε + L d(i,v)} ∪ {β_q + L d(q,v) : q ∈ Q}`. -/
noncomputable def fullUp (I : Inst) (v : Fin I.n) : Finset ℝ :=
  (sources I).image fun a => srcHi I a + I.lip * gdist I (srcLoc a) v

/-- Full lower alphabet `A⁻_v = {y_i − ε − L d(i,v)} ∪ {α_q − L d(q,v) : q ∈ Q}`. -/
noncomputable def fullLow (I : Inst) (v : Fin I.n) : Finset ℝ :=
  (sources I).image fun a => srcLo I a - I.lip * gdist I (srcLoc a) v

/-- `a'` precedes `a` in the order by value, ties broken by the identity order `ord`. -/
def Precedes {α : Type} (val : α → ℝ) (ord : α → ℕ) (a' a : α) : Prop :=
  val a' < val a ∨ (val a' = val a ∧ ord a' < ord a)

/-- The first `k` elements of `S` in the order (value, identity): those with fewer than `k`
predecessors in `S`. Ranks are over identities, not distinct values. -/
noncomputable def topSources {α : Type} (S : Finset α) (val : α → ℝ) (ord : α → ℕ)
    (k : ℕ) : Finset α := by
  classical
  exact S.filter fun a => (S.filter fun a' => Precedes val ord a' a).card < k

/-- A fixed global identity order: report source of `i` has identity `i`, audit source of
`q` has identity `n + q`. -/
def stdOrd {n : ℕ} : Source n → ℕ
  | Sum.inl i => i.val
  | Sum.inr q => n + q.val

/-- Truncated upper alphabet for a cone metric `d`: the numerical values of the first
`b + 1` sources at `v` (cone values `β_a + d(a, v)`, with `β_a = y_i + ε` for reports),
ties broken by the injective identity order `ord`; duplicate values are removed only
after truncation. -/
noncomputable def truncUpD (I : Inst) (d : Fin I.n → Fin I.n → ℝ) (ord : Source I.n → ℕ)
    (v : Fin I.n) : Finset ℝ :=
  (topSources (sources I) (fun a => srcHi I a + d (srcLoc a) v) ord (I.budget + 1)).image
    fun a => srcHi I a + d (srcLoc a) v

/-- Reflection: `y ↦ −y`, audit interval `[α, β] ↦ [−β, −α]`. -/
def reflect (I : Inst) : Inst :=
  { I with reports := fun v => -I.reports v, lo := fun v => -I.hi v, hi := fun v => -I.lo v }

/-- Truncated lower alphabet for a cone metric `d`: the construction applied to the
reflected instance, then negated. -/
noncomputable def truncLowD (I : Inst) (d : Fin I.n → Fin I.n → ℝ) (ord : Source I.n → ℕ)
    (v : Fin I.n) : Finset ℝ :=
  (truncUpD (reflect I) d ord v).image fun t => -t

/-- `A⁺_{v,b}` of Lemma 4.3 (unit edge lengths, cone `L d_G`). -/
noncomputable def truncUp (I : Inst) (ord : Source I.n → ℕ) (v : Fin I.n) : Finset ℝ :=
  truncUpD I (fun u v => I.lip * gdist I u v) ord v

/-- `A⁻_{v,b}` of Lemma 4.3. -/
noncomputable def truncLow (I : Inst) (ord : Source I.n → ℕ) (v : Fin I.n) : Finset ℝ :=
  truncLowD I (fun u v => I.lip * gdist I u v) ord v

/-- A compact polytope: a bounded set cut out by finitely many closed half-spaces. -/
def IsCompactPolytope {n : ℕ} (P : Set (Fin n → ℝ)) : Prop :=
  IsCompact P ∧ ∃ (m : ℕ) (A : Fin m → Fin n → ℝ) (c : Fin m → ℝ),
    P = {x | ∀ j, ∑ v, A j v * x v ≤ c j}

/-! ## Incidence split graph (§3.4, printed p.11, PDF p.13) -/

/-- The `j`-th edge of `H` (a fixed enumeration of the ordered endpoint pairs `u < v`). -/
noncomputable def edgeAt {r : ℕ} (H : SimpleGraph (Fin r)) (j : Fin (edgeCount H)) :
    Fin r × Fin r :=
  ((edgePairs H).equivFin.symm j).1

/-- Incidence split graph on `Fin r ⊕ Fin m_H`: original vertices independent, edge vertices
a clique, each edge vertex adjacent to its two endpoints. -/
noncomputable def incidenceSum {r : ℕ} (H : SimpleGraph (Fin r)) : SimpleGraph (Fin r ⊕ Fin (edgeCount H)) :=
  SimpleGraph.fromRel fun a b =>
    match a, b with
    | Sum.inl i, Sum.inr j => i = (edgeAt H j).1 ∨ i = (edgeAt H j).2
    | Sum.inr _, Sum.inr _ => True
    | _, _ => False

/-- `G_H` on `Fin (r + m_H)`: vertices `0,…,r−1` original, `r,…,r+m_H−1` edge vertices. -/
noncomputable def incidenceGraph {r : ℕ} (H : SimpleGraph (Fin r)) : SimpleGraph (Fin (r + edgeCount H)) :=
  (incidenceSum H).comap finSumFinEquiv.symm

/-- `ν_p(H) = min{|V(F)| : F ⊆ E(H), |F| = p}`. -/
noncomputable def nuP {r : ℕ} (H : SimpleGraph (Fin r)) (p : ℕ) : ℕ :=
  sInf {s | ∃ F ⊆ edgePairs H, F.card = p ∧ s = (F.biUnion fun e => {e.1, e.2}).card}

/-- Closed neighbourhood `N[X]`. -/
noncomputable def closedNbhd {n : ℕ} (G : SimpleGraph (Fin n)) (X : Finset (Fin n)) :
    Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun v => v ∈ X ∨ ∃ x ∈ X, G.Adj x v

/-! ## Counters (§4.2, printed p.15, PDF p.17) -/

/-- Number of mismatched vertices of `W`. -/
noncomputable def misCount {n : ℕ} (mis : Fin n → Prop) (W : Finset (Fin n)) : ℕ := by
  classical
  exact (W.filter mis).card

/-- `χ_W`: if `b ≤ h = n − b`, the mismatch count, kept only while `≤ b` (`none` = undefined);
if `h < b`, the saturated honest count `min{h, hon_W}`. -/
noncomputable def counter (n b : ℕ) (mis : Fin n → Prop) (W : Finset (Fin n)) : Option ℕ :=
  if b ≤ n - b then (if misCount mis W ≤ b then some (misCount mis W) else none)
  else some (min (n - b) (W.card - misCount mis W))

/-- The composition `⊕`: sum defined when `≤ b` (case `b ≤ h`); saturated sum `min{h, i+j}`
(case `h < b`). Undefined inputs give an undefined output. -/
def combine (n b : ℕ) : Option ℕ → Option ℕ → Option ℕ
  | some i, some j =>
    if b ≤ n - b then (if i + j ≤ b then some (i + j) else none) else some (min (n - b) (i + j))
  | _, _ => none

/-- Acceptance of a final counter: any defined value if `b ≤ h`; only `h` if `h < b`. -/
def Accepted (n b : ℕ) : Option ℕ → Prop
  | some c => b ≤ n - b ∨ c = n - b
  | none => False

/-! ## Merge sequences (Lemma 4.9, printed p.16, PDF p.18) -/

/-- A history of merging singleton blocks: a leaf is a singleton, a node merges two
disjoint blocks. A tree with `n` leaves performs exactly `n − 1` merges, and every
sequence of `n − 1` merges of disjoint blocks starting from `n` singletons is one. -/
inductive MergeTree
  | leaf : MergeTree
  | node : MergeTree → MergeTree → MergeTree

def MergeTree.size : MergeTree → ℕ
  | .leaf => 1
  | .node l r => l.size + r.size

/-- Inspected pairs: a merge of blocks of sizes `A, C` inspects
`(min{κ, A} + 1)(min{κ, C} + 1)` pairs. -/
def MergeTree.cost (κ : ℕ) : MergeTree → ℕ
  | .leaf => 0
  | .node l r => (min κ l.size + 1) * (min κ r.size + 1) + l.cost κ + r.cost κ

/-! ## Depth, distances to sets and the recovery radius (§6, printed pp.19–21, PDF pp.21–23) -/

/-- `d_G(v, C) = min_{u ∈ C} d_G(v, u)`, with `d_G(v, ∅) = +∞`. -/
noncomputable def distToSet {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n)
    (C : Finset (Fin n)) : ℕ∞ :=
  ⨅ u ∈ C, (G.dist v u : ℕ∞)

/-- Depth sum `∑_{v ∈ S} d_G(v, V ∖ S)`. -/
noncomputable def depthSum {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : ℕ∞ :=
  ∑ v ∈ S, distToSet G v Sᶜ

/-- `Ψ_G(m) = max_{|S| ≤ m} ∑_{v∈S} d_G(v, V∖S)` (6.1); finite whenever `m < n`. -/
noncomputable def Psi {n : ℕ} (G : SimpleGraph (Fin n)) (m : ℕ) : ℕ∞ :=
  (Finset.univ.filter fun S : Finset (Fin n) => S.card ≤ m).sup (depthSum G)

/-- `Ψ_{G,Q}(m) = max_{S ⊆ V∖Q, |S| ≤ m} ∑_{v∈S} d_G(v, V∖S)` (6.6); `m ≥ n` allowed. -/
noncomputable def PsiQ {n : ℕ} (G : SimpleGraph (Fin n)) (Q : Finset (Fin n)) (m : ℕ) : ℕ∞ :=
  (Finset.univ.filter fun S : Finset (Fin n) => Disjoint S Q ∧ S.card ≤ m).sup (depthSum G)

/-- `g_{S,Q}(v) = min{L d_G(v,Q), ε + L d_G(v, V∖S)}` (6.4) in `[0, ∞]`; with `L > 0`
an infinite distance gives `+∞` (no `0·∞` ambiguity). -/
noncomputable def gSQ {n : ℕ} (G : SimpleGraph (Fin n)) (L ε : ℝ) (S Q : Finset (Fin n))
    (v : Fin n) : ENNReal :=
  min (ENNReal.ofReal L * (distToSet G v Q : ENNReal))
    (ENNReal.ofReal ε + ENNReal.ofReal L * (distToSet G v Sᶜ : ENNReal))

/-- The data of the exact-audit problem with weights `w`: zero-length intervals at audits. -/
def exactInst {n : ℕ} (G : SimpleGraph (Fin n)) (b : ℕ) (L ε : ℝ) (Q : Finset (Fin n))
    (w : Fin n → ℝ) (y : Fin n → ℝ) (z : Fin n → ℝ) : Inst where
  n := n
  graph := G
  budget := b
  lip := L
  noise := ε
  reports := y
  weights := w
  audits := Q
  lo := z
  hi := z

/-- Worst-case error of an estimator `a(y, x_Q)` (2.2): the supremum over every real
`L`-Lipschitz field `x` and every report `y` with at most `b` vertices `|y_v − x_v| > ε`. -/
noncomputable def worstCase {n : ℕ} (G : SimpleGraph (Fin n)) (b : ℕ) (L ε : ℝ)
    (Q : Finset (Fin n)) (w : Fin n → ℝ) (a : (Fin n → ℝ) → (Q → ℝ) → ℝ) : ENNReal :=
  ⨆ (x : Fin n → ℝ) (_ : ∀ u v, G.Adj u v → |x u - x v| ≤ L) (y : Fin n → ℝ)
    (_ : (Finset.univ.filter fun v => ε < |y v - x v|).card ≤ b),
    ENNReal.ofReal |a y (fun q => x q) - ∑ v, w v * x v|

/-- The global minimax radius `R*_{Q,w}(G,b,L,ε)`: infimum over all estimators of the
worst-case error. `R*_Q` is the case `w = uniformW n`. This is not the conditional radius. -/
noncomputable def minimaxRadius {n : ℕ} (G : SimpleGraph (Fin n)) (b : ℕ) (L ε : ℝ)
    (Q : Finset (Fin n)) (w : Fin n → ℝ) : ENNReal :=
  ⨅ a : (Fin n → ℝ) → (Q → ℝ) → ℝ, worstCase G b L ε Q w a

/-- The midpoint estimator: midpoint (2.1) of the certificate with exact audit values. -/
noncomputable def midEstimator {n : ℕ} (G : SimpleGraph (Fin n)) (b : ℕ) (L ε : ℝ)
    (Q : Finset (Fin n)) (w : Fin n → ℝ) : (Fin n → ℝ) → (Q → ℝ) → ℝ :=
  fun y zQ => midpoint (exactInst G b L ε Q w y
    (fun v => if h : v ∈ Q then zQ ⟨v, h⟩ else 0))

/-! ## Cycles (Appendix A.1, printed p.23, PDF p.25) -/

/-- `F(a) = ⌊(a + 1)² / 4⌋`. -/
def Fcyc (a : ℕ) : ℕ := (a + 1) ^ 2 / 4

/-- The gap after audit `q` on `C_n` (vertices `0,…,n−1`, `i ~ i ± 1 mod n`): the number of
consecutive unaudited vertices `q+1, q+2, …` (mod `n`) before the next audit. -/
noncomputable def gapAfter (n : ℕ) (Q : Finset (Fin n)) (q : Fin n) : ℕ := by
  classical
  exact ((Finset.range n).filter fun j =>
    1 ≤ j ∧ ∀ i, 1 ≤ i → i ≤ j → ∀ u ∈ Q, u.val ≠ (q.val + i) % n).card

/-- The `k = |Q|` gap lengths sorted nonincreasingly, `g₁ ≥ ⋯ ≥ g_k ≥ 0` (zero gaps kept). -/
noncomputable def gaps (n : ℕ) (Q : Finset (Fin n)) : List ℕ :=
  (Q.val.map (gapAfter n Q)).sort (· ≥ ·)

/-- `g_j` (0-based index `j`). -/
noncomputable def gapAt (n : ℕ) (Q : Finset (Fin n)) (j : ℕ) : ℕ := (gaps n Q).getD j 0

/-- Balanced placement: all gap lengths differ by at most one. -/
def Balanced (n : ℕ) (Q : Finset (Fin n)) : Prop :=
  ∀ q ∈ Q, ∀ q' ∈ Q, gapAfter n Q q ≤ gapAfter n Q q' + 1

end MeanCertificates1424.Hardness.Supplement


