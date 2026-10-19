-- Prove2me | Definitions.Def_OAI_Analysis_RecursivePotentials_Model
-- name    : OAI_Analysis_RecursivePotentials_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T07:31:32.825569+00:00
-- url     : https://prove2.me/theorems/330c7189-4f17-4f27-93dd-f240d4dfeba4
-- title:
--   Recursive least potentials on rooted trees, root-sum norms and their completions, and variable-exponent $\ell^{1+1/h}$ tree spaces
-- statement:
--   This file constructs normed spaces of finitely supported functions on rooted trees whose norm is computed by a recursive pair of potentials, together with their completions, a zero-root variant, a variable-exponent variant with its $\ell^2$-sum, and bundled statements about these completions.
--
--   **Setting.** A rooted tree on an index set $\iota$ (which may be infinite) consists of a root $r\in\iota$, a parent map $\pi:\iota\to\iota$ with $\pi(r)=r$, and a depth function $d:\iota\to\mathbb{N}$ with $d(r)=0$ and $d(\pi(s))<d(s)$ for every $s\neq r$, so every node reaches the root after finitely many parent steps. The children of $s$ are $\operatorname{ch}(s)=\{c\in\iota:\ c\neq r,\ \pi(c)=s\}$. A finite set $H\subseteq\iota$ is *initial* if $r\in H$ and $\pi(s)\in H$ for all $s\in H$; it is then itself a rooted tree with the restricted root, parent and depth. For $x,a,b\in\mathbb{R}$ the *least pair* is
--   $$
--   \lambda(x,a,b)=\big(\max\{a,\ x+b\},\ \max\{b,\ a-x\}\big),
--   $$
--   the coordinatewise smallest pair $(p,q)$ with $p-q=x$, $p\ge a$ and $q\ge b$. For a real number $p\ge1$ (a *child exponent*), a finite set $S$ and $f:\iota\to\mathbb{R}$ put $\|f\|_{p,S}=\big(\sum_{i\in S}|f(i)|^p\big)^{1/p}$. On a tree with finitely many nodes, the recursive potentials of $v:\iota\to\mathbb{R}$ are defined from the leaves upward by
--   $$
--   \big(P^{(p)}_v(s),\,Q^{(p)}_v(s)\big)=\lambda\Big(v(s),\ \big\|P^{(p)}_v\big\|_{p,\operatorname{ch}(s)},\ \big\|Q^{(p)}_v\big\|_{p,\operatorname{ch}(s)}\Big);
--   $$
--   for $p=2$ there is a separate definition written with $\big(\sum_{c\in\operatorname{ch}(s)}P_v(c)^2\big)^{1/2}$ and $\big(\sum_{c\in\operatorname{ch}(s)}Q_v(c)^2\big)^{1/2}$, whose output is denoted $(P_v,Q_v)$. These background notions come from the base definitions of the development; the file introduces the following objects.
--
--   1. **An energy expression.** For real numbers $a,b,\delta$,
--   $$
--   \mathcal{E}(a,b,\delta)=\big(\delta\,(2a+\delta)\,(2b+\delta)\big)^{2/3}.
--   $$
--
--   2. **Square-sum domination on finite trees.** On a finite tree, $f:\iota\to\mathbb{R}$ is *upper* if $\sum_{c\in\operatorname{ch}(s)}f(c)^2\le f(s)^2$ for every node $s$. The file shows that $P_v,Q_v\ge0$, $P_v-Q_v=v$, that $P_v$ and $Q_v$ are upper, and that they form the least such pair: whenever $p,q:\iota\to\mathbb{R}$ are nonnegative and upper with $p-q=v$, then $P_v\le p$ and $Q_v\le q$ pointwise.
--
--   3. **Potentials and the root-sum norm of finitely supported vectors.** Now let the tree be arbitrary. For a node $s$ let $\operatorname{anc}(s)=\{s,\pi(s),\pi^2(s),\dots,r\}$. The *head* of a finitely supported $v:\iota\to\mathbb{R}$ is the initial set $H(v)=\{r\}\cup\bigcup_{s\in\operatorname{supp}v}\operatorname{anc}(s)$, and $P_v,Q_v:\iota\to\mathbb{R}$ are the potentials of $v|_{H(v)}$ on the finite tree $H(v)$, extended by $0$ outside $H(v)$. A function $f$ is *globally upper* if $\sum_{c\in S}f(c)^2\le f(s)^2$ for every node $s$ and every finite set $S\subseteq\operatorname{ch}(s)$. The root-sum norm and the head projection onto a finite set $H$ are
--   $$
--   \|v\|_T=P_v(r)+Q_v(r),\qquad (\Pi_Hv)(s)=\begin{cases}v(s),& s\in H,\\ 0,& s\notin H.\end{cases}
--   $$
--   The file establishes that $(P_v,Q_v)$ is the least pair of nonnegative globally upper functions with difference $v$; that $P_{-v}=Q_v$ and $Q_{-v}=P_v$, that $P_{av}=aP_v$ and $Q_{av}=aQ_v$ for $a\ge0$, and that $P_{v+w}\le P_v+P_w$ and $Q_{v+w}\le Q_v+Q_w$; that a nonnegative globally upper function is largest at the root; and that $\|\cdot\|_T$ is a norm on finitely supported functions with $|v(s)|\le\|v\|_T$ for every node $s$ and $\|\Pi_Hv\|_T\le\|v\|_T$ for every initial $H$.
--
--   4. **Tree spaces.** $V_T$ is the space of finitely supported functions $\iota\to\mathbb{R}$ with the norm $\|\cdot\|_T$; the coordinate functionals $v\mapsto v(s)$ and the head projections $\Pi_H$ ($H$ initial) are continuous linear maps of norm at most $1$. $X_T$ is the completion of $V_T$; it carries the extended coordinate functionals $x\mapsto x(s)$, the extensions $P_s,Q_s:X_T\to\mathbb{R}$ of $v\mapsto P_v(s)$ and $v\mapsto Q_v(s)$, the extended projections $\Pi_H$, and the tails $\ker\Pi_H$. Two trees are singled out. The *sequence tree* $\Sigma$ has as nodes all finite sequences of natural numbers, with root the empty sequence, parent map deleting the last entry and depth equal to length; its tree space is $X_\Sigma$. The *joined tree* $J$ has a root $\ast$ and the nodes $(h,s)$ with $h\ge1$ an integer and $s$ a sequence of natural numbers of length at most $h$; the parent of $(h,\varnothing)$ is $\ast$, the parent of $(h,s)$ with $s$ nonempty is $(h,s')$ where $s'$ deletes the last entry of $s$, and $d(h,s)=|s|+1$. Thus $J$ hangs copies of the trees of height $h=1,2,\dots$ below a common root; its tree space is $X_J$.
--
--   5. **Zero-root spaces.** $V^0_T=\{v\in V_T:\ v(r)=0\}$ carries the norm $\|v\|_0=P_v(r)$; the file shows $\|v\|_0=\|v\|_T/2$, so the inclusion $V^0_T\to V_T$ is bounded (with bound $2$) and each $\Pi_H$ with $H$ initial maps $V^0_T$ into itself with norm at most $1$. $Z_T$ is the completion of $V^0_T$, with the extended inclusion $Z_T\to X_T$, the extended projections and their kernels (tails), and coordinates and potentials $x(s)$, $P_s(x)$, $Q_s(x)$ obtained by composing with the inclusion. $X_0=Z_J$ is the zero-root space of the joined tree.
--
--   6. **Square-sum duality.** For a family $(E_i)$ of real normed spaces, $\ell^2(E)$ is the space of families $(x_i)$ with $x_i\in E_i$ and $\sum_i\|x_i\|^2<\infty$. The pairing $\langle f,x\rangle=\sum_i f_i(x_i)$ of $f\in\ell^2\big((E_i^*)\big)$ with $x\in\ell^2(E)$ is packaged as a continuous linear map $\ell^2\big((E_i^*)\big)\to\ell^2(E)^*$, and $V_T\to\ell^2(\iota)$ is the linear map sending a finitely supported $v$ to itself.
--
--   7. **Variable-exponent potentials and aggregation spaces.** Fix a child exponent $p\ge1$. On a finite tree, $f$ is *$p$-upper* if $\|f\|_{p,\operatorname{ch}(s)}\le f(s)$ for all $s$; the file shows that $\big(P^{(p)}_v,Q^{(p)}_v\big)$ is the least pair of nonnegative $p$-upper functions with difference $v$, and sets $\rho_p(v)=P^{(p)}_v(r)+Q^{(p)}_v(r)$. On an arbitrary tree, $f$ is *globally $p$-upper* if $\|f\|_{p,S}\le f(s)$ for every node $s$ and every finite $S\subseteq\operatorname{ch}(s)$. For finitely supported $v$ the potentials $P^{(p)}_v,Q^{(p)}_v$ are computed on the head $H(v)$ and extended by $0$; they coincide on $H$ with the potentials of $v|_H$ for every initial $H\supseteq\operatorname{supp}v$, they form the least nonnegative globally $p$-upper pair with difference $v$, and
--   $$
--   \|v\|_{T,p}=P^{(p)}_v(r)+Q^{(p)}_v(r)
--   $$
--   is a norm with $|v(s)|\le\|v\|_{T,p}$. The aggregation vector space $V_{T,p}$ consists of the finitely supported functions with this norm, $A_{T,p}$ is its completion with extended coordinates and potentials $P_s,Q_s$, and $e_s$ denotes the indicator vector of the node $s$. The height exponent is $p_h=1+1/h$ for an integer $h\ge1$; it satisfies $p_h>1$.
--
--   8. **Comparison with $\ell^p$.** Let $\ell^p(\iota)$ be the Banach space of real families with $\sum_i|x_i|^p<\infty$, and let $j_p:V_{T,p}\to\ell^p(\iota)$ send a finitely supported $v$ to itself. Suppose $p>1$, $d(c)=d(\pi(c))+1$ for every $c\neq r$, and $d(s)\le h$ for all $s$, for some $h\in\mathbb{N}$. Then for every $v\in V_{T,p}$
--   $$
--   \|v\|_{T,p}\le 2\,(h+1)^{1-1/p}\,\|v\|_{\ell^p},\qquad \|v\|_{\ell^p}\le (h+1)^{1/p}\,\|v\|_{T,p}.
--   $$
--   Under these hypotheses $j_p$ is a bounded linear map with dense range, and it extends to an isomorphism of Banach spaces $A_{T,p}\cong\ell^p(\iota)$ (a continuous linear bijection with continuous inverse). Along the way the file introduces, for finite trees, the depth levels $L_j=\{s:\ d(s)=j\}$, the set $\{c\neq r:\ \pi(c)\in S\}$ of children of a set $S$, and the larger potential $M_v(s)=\max\{P^{(p)}_v(s),Q^{(p)}_v(s)\}$, which satisfies $M_v(s)\le|v(s)|+\|M_v\|_{p,\operatorname{ch}(s)}$; under the level-step hypothesis it shows $\|v\|_{p,L_j}\le\rho_p(v)$ for every level $j$.
--
--   9. **The variable-exponent space.** For an integer $h\ge1$ let $T_h$ be the tree of sequences of natural numbers of length at most $h$ (root the empty sequence, parent deleting the last entry, depth equal to length), let $C_h=A_{T_h,p_h}$, and let
--   $$
--   X_v=\Big(\bigoplus_{h\ge1}C_h\Big)_{\ell^2}=\Big\{x=(x_h)_{h\ge1}:\ x_h\in C_h,\ \sum_{h\ge1}\|x_h\|^2<\infty\Big\}.
--   $$
--   By item 8 with height $h$, $C_h\cong\ell^{p_h}(T_h)$. The nodes of $X_v$ are the pairs $\sigma=(h,s)$ with $s\in T_h$; the coordinate $x(\sigma)$ is the $s$-coordinate of $x_h$, and $e_\sigma$ is the element whose $h$-th component is $e_s$ and whose other components vanish. An element $x\in X_v$ has *finite total support* if $x(\sigma)=0$ for all $\sigma$ outside some finite set, and for a finite set $S$ of nodes $\Pi_Sx=\sum_{\sigma\in S}x(\sigma)\,e_\sigma$. A family $A=(A_h)_{h\ge1}$ of finite sets $A_h\subseteq T_h$ is an *admissible head* for a pair $x,y\in X_v$ if for every $h$ with $x_h\neq0$: $A_h$ is initial in $T_h$, $x_h(s)=0$ for $s\notin A_h$, and $y_h(s)=0$ for $s\in A_h$. Finally, with $c_3=(6e)^{-3}$, the weak-tail constant and the weak-tail bound are
--   $$
--   c_{\mathrm{w}}=\frac{c_3}{2\sqrt2},\qquad \theta(\varepsilon)=\sqrt{1-c_{\mathrm{w}}\,\varepsilon^3}.
--   $$
--
--   10. **Norm data transported to $\ell^{p_h}$.** For $v\in\ell^{p_h}(T_h)$ let $\tilde v\in C_h$ be its preimage under the isomorphism $C_h\cong\ell^{p_h}(T_h)$ of item 9. Then $\nu_h(v)=P_r(\tilde v)+Q_r(\tilde v)$, with $r$ the root of $T_h$, and the transported potentials are $s\mapsto\big(P_s(\tilde v),Q_s(\tilde v)\big)$. The child aggregate of $f:T_h\to\mathbb{R}$ at $s$ is $\big(\sum_{c\in\operatorname{ch}(s)}f(c)^{p_h}\big)^{1/p_h}$, an infinite sum because a node of length less than $h$ has infinitely many children.
--
--   11. **Bundled completion and norm statements.** For a tree $T$, the *root-sum completion statement* asserts: $X_T$ is complete and not finite-dimensional; the coordinate functionals on $X_T$ are continuous and the $s$-coordinate of $v\in V_T\subseteq X_T$ is $v(s)$; the extended potentials $P_s,Q_s$ are continuous and agree with $P_v(s)$, $Q_v(s)$ on $V_T$; $\|x\|=P_r(x)+Q_r(x)$ for all $x\in X_T$; and for every initial $H$: $\|\Pi_Hx\|\le\|x\|$, $\Pi_H^2=\Pi_H$, $(\Pi_Hx)(s)$ equals $x(s)$ for $s\in H$ and $0$ otherwise, $\Pi_H$ has finite-dimensional range, the tail $\ker\Pi_H$ is closed with finite-dimensional quotient $X_T/\ker\Pi_H$, and for every $x\in\ker\Pi_H$ and $\varepsilon>0$ there is $v\in V_T$ with $\Pi_Hv=0$ and $\|v-x\|<\varepsilon$. The *zero-root completion statement* asserts the same for $Z_T$ (with $V^0_T$ in place of $V_T$, and coordinates and potentials taken through the inclusion), except that the root formula is replaced by $x(r)=0$ and $\|x\|=P_r(x)=Q_r(x)$ for all $x\in Z_T$. The *source-norm statement* for $h$ asserts that $\nu_h$ is a norm on $\ell^{p_h}(T_h)$: $\nu_h\ge0$, $\nu_h(v)=0$ if and only if $v=0$, $\nu_h(v+w)\le\nu_h(v)+\nu_h(w)$, and $\nu_h(av)=|a|\,\nu_h(v)$ for all real $a$.
--
--   These are the concrete models behind the main claim of the development, which asserts the existence of a head structure, tree-vector norms, zero-root norms and aggregation norms with the properties proved here (heads are initial; the norm axioms with $|v(s)|\le\|v\|$; contractive head projections; $\|v\|_0=\|v\|_T/2$; the two-sided $\ell^p$ comparison with dense range), and then states completion, modulus, stability and weak-tail results for $X_\Sigma$, $X_J$, $X_0$ and $X_v$ in terms of the objects of items 9 to 11. The minimality characterization of the potentials is the reusable core: any nonnegative upper pair with the right difference bounds the potentials from above.
--
--   **Formalization Note** The tree structure is `FiniteRootedTree ι`; its `depth` is only required to decrease strictly along parents, so the comparison results of item 8 (`lp_comparisons`, `toLp`, `toLp_dense`, `AggregationSpace.lpEquiv`) carry the explicit hypothesis `hstep` that it increases by exactly one. The exponent-2 objects (`Upper`, `GlobalUpper`, `P`, `Q`, `normSum`, `TreeVector`, `TreeSpace`, `XSigma`, `XJoined`, `ZeroTreeVector`, `ZeroTreeSpace`, `XZero`) and the general-exponent objects (`ChildExponent.agg` lemmas, `PUpper`, `pRootSum`, `VariableTree.GlobalUpper`, `VariableTree.P`, `VariableTree.Q`, `VariableTree.normSum`, `AggregationVector`, `AggregationSpace`, `AggregationVector.CoordinateLp`, `pMaximum`, `headLevel`, `childrenOf`) are developed in parallel; the objects of items 9 and 10 are `Variable.exponent`, `Component`, `Xv`, `Node`, `componentEquiv`, `coordinate`, `basis`, `FiniteTotalSupport`, `projection`, `AdmissibleHeads`, `weakTailConstant`, `theta`, `nu`, `aggregateChildren` and `lpPotentials`, and the bundled statements are the structures `RootSumCompletionStatement`, `ZeroRootCompletionStatement` and `Variable.SourceNormStatement`. Potentials on completions are defined with `UniformSpace.Completion.extension`, which is the continuous extension when the map is uniformly continuous; continuity of these extensions is a field of the bundled statements and is not proved in this file. The space $\ell^p(\iota)$ is Mathlib's `lp` with exponent `ENNReal.ofReal p`, and the square-sum pairing is Mathlib's `lp.dualPairing`. In `aggregateChildren` the powers are real powers without absolute values and the infinite sum is a `tsum`, which is $0$ for non-summable families; `energy` uses the real power with exponent $2/3$ and Mathlib's convention for negative bases. Auxiliary lemmas include the Minkowski-type bound $\sum_i(f_i+g_i)^2\le(a+b)^2$ from $\sum_i f_i^2\le a^2$, $\sum_i g_i^2\le b^2$ and $a,b\ge0$ (`sum_add_sq_le`), elementary properties of ancestor closures and of extension by zero, and two private `ite` compatibility lemmas.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/RecursivePotentials/Model.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/RecursivePotentials/Model.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the RecursivePotentials mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_RecursivePotentials

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

noncomputable section

universe uIndex uSpace uOther uDomain uTarget uFiber

open scoped BigOperators

namespace RecursivePotentials

lemma leastPair_difference (x a b : ℝ) :
    (leastPair x a b).1 - (leastPair x a b).2 = x := by
  simp only [leastPair]
  rcases le_total a (x + b) with h | h
  · rw [max_eq_right h, max_eq_left (by linarith)]
    ring
  · rw [max_eq_left h, max_eq_right (by linarith)]
    ring

lemma leastPair_nonneg {x a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ (leastPair x a b).1 ∧ 0 ≤ (leastPair x a b).2 :=
  ⟨ha.trans (le_max_left _ _), hb.trans (le_max_left _ _)⟩

lemma leastPair_minimal {x a b p q : ℝ} (hdiff : p - q = x)
    (hp : a ≤ p) (hq : b ≤ q) :
    (leastPair x a b).1 ≤ p ∧ (leastPair x a b).2 ≤ q := by
  constructor <;> apply max_le
  · exact hp
  · linarith
  · exact hq
  · linarith

lemma sum_add_sq_le {ι : Type uIndex} (s : Finset ι) (f g : ι → ℝ) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hf : ∑ i ∈ s, f i ^ 2 ≤ a ^ 2)
    (hg : ∑ i ∈ s, g i ^ 2 ≤ b ^ 2) :
    ∑ i ∈ s, (f i + g i) ^ 2 ≤ (a + b) ^ 2 := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq s f g
  have hprod : (∑ i ∈ s, f i ^ 2) * (∑ i ∈ s, g i ^ 2) ≤ a ^ 2 * b ^ 2 :=
    mul_le_mul hf hg (Finset.sum_nonneg fun i _ => sq_nonneg _) (sq_nonneg _)
  have hab : 0 ≤ a * b := mul_nonneg ha hb
  have hcross : ∑ i ∈ s, f i * g i ≤ a * b := by
    nlinarith [hc.trans hprod]
  calc
    ∑ i ∈ s, (f i + g i) ^ 2 =
        (∑ i ∈ s, f i ^ 2) + 2 * (∑ i ∈ s, f i * g i) +
          (∑ i ∈ s, g i ^ 2) := by
      simp only [add_sq, Finset.sum_add_distrib]
      congr 1
      congr 1
      simp_rw [mul_assoc, Finset.mul_sum]
    _ ≤ (a + b) ^ 2 := by nlinarith

noncomputable def energy (p q d : ℝ) : ℝ :=
  (d * (2 * p + d) * (2 * q + d)) ^ (2 / 3 : ℝ)

namespace FiniteRootedTree

section

variable {ι : Type uIndex} [indexFinite : Fintype ι] [indexDecidable : DecidableEq ι]
    (T : FiniteRootedTree ι)

def Upper (p : ι → ℝ) : Prop :=
  ∀ s, ∑ c ∈ T.children s, p c ^ 2 ≤ p s ^ 2

lemma depth_le_maxDepth {ι : Type uIndex} [Fintype ι] [DecidableEq ι] (T : FiniteRootedTree ι)
    (s : ι) : T.depth s ≤ T.maxDepth :=
  Finset.le_sup (Finset.mem_univ s)

lemma child_depth {s c : ι} (hc : c ∈ T.children s) : T.depth s < T.depth c := by
  obtain ⟨_, hne, hpar⟩ := Finset.mem_filter.mp hc
  simpa [hpar] using T.parent_depth c hne

lemma child_measure {s c : ι} (hc : c ∈ T.children s) :
    T.maxDepth - T.depth c < T.maxDepth - T.depth s := by
  have := T.child_depth hc
  have := T.depth_le_maxDepth c
  omega

lemma fields_eq (v : ι → ℝ) (s : ι) :
    T.fields v s = leastPair (v s)
      (Real.sqrt (∑ c ∈ T.children s, (T.fields v c).1 ^ 2))
      (Real.sqrt (∑ c ∈ T.children s, (T.fields v c).2 ^ 2)) := by
  rw [fields]
  rw [← Finset.sum_subtype (T.children s) (fun _ => Iff.rfl) (fun c => (T.fields v c).1 ^ 2),
    ← Finset.sum_subtype (T.children s) (fun _ => Iff.rfl) (fun c => (T.fields v c).2 ^ 2)]

lemma fields_nonneg (v : ι → ℝ) (s : ι) :
    0 ≤ (T.fields v s).1 ∧ 0 ≤ (T.fields v s).2 := by
  rw [T.fields_eq]
  exact leastPair_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

lemma fields_difference (v : ι → ℝ) (s : ι) :
    (T.fields v s).1 - (T.fields v s).2 = v s := by
  rw [T.fields_eq]
  exact leastPair_difference _ _ _

lemma fields_upper (v : ι → ℝ) :
    T.Upper (fun s => (T.fields v s).1) ∧ T.Upper (fun s => (T.fields v s).2) := by
  constructor <;> intro s
  · have h : Real.sqrt (∑ c ∈ T.children s, (T.fields v c).1 ^ 2) ≤
        (T.fields v s).1 := by rw [T.fields_eq]; exact le_max_left _ _
    exact (Real.sqrt_le_iff.mp h).2
  · have h : Real.sqrt (∑ c ∈ T.children s, (T.fields v c).2 ^ 2) ≤
        (T.fields v s).2 := by rw [T.fields_eq]; exact le_max_left _ _
    exact (Real.sqrt_le_iff.mp h).2

theorem fields_minimal (v p q : ι → ℝ) (hp : ∀ s, 0 ≤ p s) (hq : ∀ s, 0 ≤ q s)
    (hdiff : ∀ s, p s - q s = v s) (hpU : T.Upper p) (hqU : T.Upper q) (s : ι) :
    (T.fields v s).1 ≤ p s ∧ (T.fields v s).2 ≤ q s := by
  rw [T.fields_eq]
  apply leastPair_minimal (hdiff s)
  · apply Real.sqrt_le_iff.mpr
    refine ⟨hp s, (Finset.sum_le_sum fun c hc => ?_).trans (hpU s)⟩
    exact pow_le_pow_left₀ (T.fields_nonneg v c).1
      (fields_minimal v p q hp hq hdiff hpU hqU c).1 2
  · apply Real.sqrt_le_iff.mpr
    refine ⟨hq s, (Finset.sum_le_sum fun c hc => ?_).trans (hqU s)⟩
    exact pow_le_pow_left₀ (T.fields_nonneg v c).2
      (fields_minimal v p q hp hq hdiff hpU hqU c).2 2
termination_by T.maxDepth - T.depth s
decreasing_by all_goals exact T.child_measure hc

end

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

lemma mem_ancestors_self (s : ι) : s ∈ T.ancestors s := by
  rw [ancestors]
  split_ifs <;> simp

lemma ancestors_parent_closed (s : ι) {c : ι} (hc : c ∈ T.ancestors s) :
    T.parent c ∈ T.ancestors s := by
  rw [ancestors] at hc ⊢
  split_ifs at hc ⊢ with hs
  · have hcs : c = s := Finset.mem_singleton.mp hc
    simp [hcs, hs, T.parent_root]
  · rcases Finset.mem_insert.mp hc with hcs | hc
    · subst c
      exact Finset.mem_insert_of_mem (T.mem_ancestors_self (T.parent s))
    · exact Finset.mem_insert_of_mem (ancestors_parent_closed (T.parent s) hc)
termination_by T.depth s
decreasing_by exact T.parent_depth s hs

lemma subset_ancestorClosure (S : Finset ι) : S ⊆ T.ancestorClosure S := by
  intro s hs
  exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨s, hs, T.mem_ancestors_self s⟩)

lemma ancestorClosure_initial (S : Finset ι) : T.Initial (T.ancestorClosure S) := by
  constructor
  · exact Finset.mem_insert_self _ _
  · intro s hs
    rcases Finset.mem_insert.mp hs with h | h
    · subst s
      change T.parent T.root ∈ insert T.root (S.biUnion T.ancestors)
      rw [T.parent_root]
      exact Finset.mem_insert_self _ _
    · obtain ⟨c, hc, hsc⟩ := Finset.mem_biUnion.mp h
      exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr
        ⟨c, hc, T.ancestors_parent_closed c hsc⟩)

lemma mem_restrict_children (H : Finset ι) (hH : T.Initial H) (s c : H) :
    c ∈ (T.restrict H hH).children s ↔ c.1 ≠ T.root ∧ T.parent c.1 = s.1 := by
  simp [children, restrict, Subtype.ext_iff]

lemma sum_restrict_children (H : Finset ι) (hH : T.Initial H) (s : H) (f : ι → ℝ) :
    ∑ c ∈ (T.restrict H hH).children s, f c.1 =
      ∑ c ∈ H.filter (fun c => c ≠ T.root ∧ T.parent c = s.1), f c := by
  apply Finset.sum_bij (fun c _ => c.1)
  · intro c hc
    exact Finset.mem_filter.mpr ⟨c.2, (T.mem_restrict_children H hH s c).mp hc⟩
  · intro a ha b hb hab
    exact Subtype.ext hab
  · intro c hc
    obtain ⟨hcH, hc⟩ := Finset.mem_filter.mp hc
    exact ⟨⟨c, hcH⟩, (T.mem_restrict_children H hH s _).mpr hc, rfl⟩
  · intro c hc
    rfl

lemma extend_mem (H : Finset ι) (f : H → ℝ) {s : ι} (hs : s ∈ H) :
    extend H f s = f ⟨s, hs⟩ := by simp [extend, hs]

@[simp] lemma extend_coe (H : Finset ι) (f : H → ℝ) (s : H) : extend H f s.1 = f s := by
  exact extend_mem H f s.2

lemma extend_not_mem (H : Finset ι) (f : H → ℝ) {s : ι} (hs : s ∉ H) :
    extend H f s = 0 := by simp [extend, hs]

lemma extend_nonneg (H : Finset ι) (f : H → ℝ) (hf : ∀ s, 0 ≤ f s) (s : ι) :
    0 ≤ extend H f s := by
  by_cases hs : s ∈ H
  · rw [extend_mem H f hs]
    exact hf _
  · rw [extend_not_mem H f hs]

def GlobalUpper (p : ι → ℝ) : Prop :=
  ∀ (s : ι) (S : Finset ι), (∀ c ∈ S, c ≠ T.root ∧ T.parent c = s) →
    ∑ c ∈ S, p c ^ 2 ≤ p s ^ 2

lemma GlobalUpper.restrict {p : ι → ℝ} (hp : T.GlobalUpper p) (H : Finset ι)
    (hH : T.Initial H) : (T.restrict H hH).Upper (fun s => p s.1) := by
  intro s
  rw [T.sum_restrict_children H hH s (fun c => p c ^ 2)]
  exact hp s.1 _ (fun c hc => (Finset.mem_filter.mp hc).2)

lemma extend_upper (H : Finset ι) (hH : T.Initial H) (f : H → ℝ)
    (hf : (T.restrict H hH).Upper f) : T.GlobalUpper (extend H f) := by
  intro s S hS
  by_cases hs : s ∈ H
  · have hsum : ∑ c ∈ S, (extend H f c) ^ 2 =
        ∑ c ∈ S.filter (fun c => c ∈ H), (extend H f c) ^ 2 := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro c hc
      by_cases hh : c ∈ H
      · simp [hh]
      · simp [hh, extend_not_mem H f hh]
    rw [hsum]
    calc
      ∑ c ∈ S.filter (fun c => c ∈ H), (extend H f c) ^ 2 ≤
          ∑ c ∈ H.filter (fun c => c ≠ T.root ∧ T.parent c = s), (extend H f c) ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro c hc
          obtain ⟨hcS, hcH⟩ := Finset.mem_filter.mp hc
          exact Finset.mem_filter.mpr ⟨hcH, hS c hcS⟩
        · intro c hc hc'
          exact sq_nonneg _
      _ = ∑ c ∈ (T.restrict H hH).children ⟨s, hs⟩, f c ^ 2 := by
        rw [← T.sum_restrict_children H hH ⟨s, hs⟩ (fun c => (extend H f c) ^ 2)]
        simp only [extend_coe]
      _ ≤ (extend H f s) ^ 2 := by
        rw [extend_mem H f hs]
        exact hf ⟨s, hs⟩
  · rw [extend_not_mem H f hs]
    have hc0 : ∀ c ∈ S, extend H f c = 0 := by
      intro c hc
      apply extend_not_mem
      intro hh
      have hh' := hH.2 c hh
      rw [(hS c hc).2] at hh'
      exact hs hh'
    simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
    exact le_of_eq (Finset.sum_eq_zero (fun c hc => by rw [hc0 c hc]; norm_num))

lemma GlobalUpper.add {ι : Type uIndex} [DecidableEq ι] (T : FiniteRootedTree ι) {p q : ι → ℝ}
    (hp : T.GlobalUpper p) (hq : T.GlobalUpper q) (hp0 : ∀ s, 0 ≤ p s) (hq0 : ∀ s, 0 ≤ q s) :
    T.GlobalUpper (p + q) := by
  intro s S hS
  exact sum_add_sq_le S p q (hp0 s) (hq0 s) (hp s S hS) (hq s S hS)

lemma GlobalUpper.smul {ι : Type uIndex} [DecidableEq ι] (T : FiniteRootedTree ι) {p : ι → ℝ}
    (hp : T.GlobalUpper p) (a : ℝ) :
    T.GlobalUpper (a • p) := by
  intro s S hS
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (hp s S hS) (sq_nonneg a)

lemma GlobalUpper.le_root {p : ι → ℝ} (hp : T.GlobalUpper p)
    (hp0 : ∀ s, 0 ≤ p s) (s : ι) : p s ≤ p T.root := by
  by_cases hs : s = T.root
  · simp [hs]
  · have hsq := hp (T.parent s) {s} (by simpa using hs)
    simp only [Finset.sum_singleton] at hsq
    have hle : p s ≤ p (T.parent s) := by nlinarith [hp0 (T.parent s)]
    exact hle.trans (GlobalUpper.le_root hp hp0 (T.parent s))
termination_by T.depth s
decreasing_by exact T.parent_depth s hs

lemma head_initial (v : ι →₀ ℝ) : T.Initial (T.head v) :=
  T.ancestorClosure_initial v.support

lemma support_subset_head (v : ι →₀ ℝ) : v.support ⊆ T.head v :=
  T.subset_ancestorClosure v.support

lemma zero_off_head (v : ι →₀ ℝ) {s : ι} (hs : s ∉ T.head v) : v s = 0 := by
  exact Finsupp.notMem_support_iff.mp (fun h => hs (T.support_subset_head v h))

noncomputable def P (v : ι →₀ ℝ) : ι →₀ ℝ :=
  extend (T.head v) (fun s => ((T.restrict (T.head v) (T.head_initial v)).fields
    (fun s => v s.1) s).1)

noncomputable def Q (v : ι →₀ ℝ) : ι →₀ ℝ :=
  extend (T.head v) (fun s => ((T.restrict (T.head v) (T.head_initial v)).fields
    (fun s => v s.1) s).2)

lemma P_nonneg (v : ι →₀ ℝ) (s : ι) : 0 ≤ T.P v s :=
  extend_nonneg _ _ (fun s => ((T.restrict _ _).fields_nonneg _ s).1) s

lemma Q_nonneg (v : ι →₀ ℝ) (s : ι) : 0 ≤ T.Q v s :=
  extend_nonneg _ _ (fun s => ((T.restrict _ _).fields_nonneg _ s).2) s

lemma P_upper (v : ι →₀ ℝ) : T.GlobalUpper (T.P v) :=
  T.extend_upper _ _ _ ((T.restrict _ _).fields_upper _).1

lemma Q_upper (v : ι →₀ ℝ) : T.GlobalUpper (T.Q v) :=
  T.extend_upper _ _ _ ((T.restrict _ _).fields_upper _).2

lemma P_sub_Q (v : ι →₀ ℝ) (s : ι) : T.P v s - T.Q v s = v s := by
  by_cases hs : s ∈ T.head v
  · simp only [P, Q, extend_mem _ _ hs]
    exact (T.restrict _ _).fields_difference _ _
  · simp only [P, Q, extend_not_mem _ _ hs, T.zero_off_head v hs, sub_zero]

lemma potentials_minimal (v : ι →₀ ℝ) (p q : ι → ℝ)
    (hp : ∀ s, 0 ≤ p s) (hq : ∀ s, 0 ≤ q s) (hdiff : ∀ s, p s - q s = v s)
    (hpU : T.GlobalUpper p) (hqU : T.GlobalUpper q) (s : ι) :
    T.P v s ≤ p s ∧ T.Q v s ≤ q s := by
  by_cases hs : s ∈ T.head v
  · simp only [P, Q, extend_mem _ _ hs]
    exact (T.restrict _ _).fields_minimal (fun s => v s.1) (fun s => p s.1)
      (fun s => q s.1) (fun s => hp s.1) (fun s => hq s.1) (fun s => hdiff s.1)
      (hpU.restrict T _ _) (hqU.restrict T _ _) ⟨s, hs⟩
  · simp only [P, Q, extend_not_mem _ _ hs]
    exact ⟨hp s, hq s⟩

noncomputable def normSum (v : ι →₀ ℝ) : ℝ := T.P v T.root + T.Q v T.root

lemma potentials_zero (s : ι) : T.P 0 s = 0 ∧ T.Q 0 s = 0 := by
  have h := T.potentials_minimal 0 (fun _ => 0) (fun _ => 0)
    (fun _ => le_rfl) (fun _ => le_rfl) (fun _ => by simp)
    (by intro s S hS; simp) (by intro s S hS; simp) s
  exact ⟨le_antisymm h.1 (T.P_nonneg 0 s), le_antisymm h.2 (T.Q_nonneg 0 s)⟩

lemma potentials_add_le (v w : ι →₀ ℝ) (s : ι) :
    T.P (v + w) s ≤ T.P v s + T.P w s ∧ T.Q (v + w) s ≤ T.Q v s + T.Q w s := by
  apply T.potentials_minimal (v + w) (fun c => T.P v c + T.P w c)
    (fun c => T.Q v c + T.Q w c)
  · intro c; exact add_nonneg (T.P_nonneg v c) (T.P_nonneg w c)
  · intro c; exact add_nonneg (T.Q_nonneg v c) (T.Q_nonneg w c)
  · intro c
    simp only [Finsupp.add_apply]
    linarith [T.P_sub_Q v c, T.P_sub_Q w c]
  · exact (T.P_upper v).add T (T.P_upper w) (T.P_nonneg v) (T.P_nonneg w)
  · exact (T.Q_upper v).add T (T.Q_upper w) (T.Q_nonneg v) (T.Q_nonneg w)

lemma potentials_neg (v : ι →₀ ℝ) (s : ι) :
    T.P (-v) s = T.Q v s ∧ T.Q (-v) s = T.P v s := by
  have h₁ := T.potentials_minimal (-v) (T.Q v) (T.P v)
    (T.Q_nonneg v) (T.P_nonneg v)
    (fun c => by simp only [Finsupp.neg_apply]; linarith [T.P_sub_Q v c])
    (T.Q_upper v) (T.P_upper v) s
  have h₂ := T.potentials_minimal v (T.Q (-v)) (T.P (-v))
    (T.Q_nonneg (-v)) (T.P_nonneg (-v))
    (fun c => by have h := T.P_sub_Q (-v) c; simp only [Finsupp.neg_apply] at h; linarith)
    (T.Q_upper (-v)) (T.P_upper (-v)) s
  exact ⟨le_antisymm h₁.1 h₂.2, le_antisymm h₁.2 h₂.1⟩

lemma potentials_smul_le (a : ℝ) (ha : 0 ≤ a) (v : ι →₀ ℝ) (s : ι) :
    T.P (a • v) s ≤ a * T.P v s ∧ T.Q (a • v) s ≤ a * T.Q v s := by
  apply T.potentials_minimal (a • v) (fun c => a * T.P v c) (fun c => a * T.Q v c)
  · intro c; exact mul_nonneg ha (T.P_nonneg v c)
  · intro c; exact mul_nonneg ha (T.Q_nonneg v c)
  · intro c
    simp only [Finsupp.smul_apply, smul_eq_mul, ← mul_sub, T.P_sub_Q]
  · exact (T.P_upper v).smul T a
  · exact (T.Q_upper v).smul T a

lemma potentials_smul_nonneg (a : ℝ) (ha : 0 ≤ a) (v : ι →₀ ℝ) (s : ι) :
    T.P (a • v) s = a * T.P v s ∧ T.Q (a • v) s = a * T.Q v s := by
  rcases eq_or_lt_of_le ha with h | h
  · subst a
    simpa using T.potentials_zero s
  · have h₁ := T.potentials_smul_le a ha v s
    have h₂ := T.potentials_smul_le a⁻¹ (inv_nonneg.mpr ha) (a • v) s
    simp only [smul_smul, inv_mul_cancel₀ (ne_of_gt h), one_smul] at h₂
    have hp := mul_le_mul_of_nonneg_left h₂.1 ha
    have hq := mul_le_mul_of_nonneg_left h₂.2 ha
    simp only [← mul_assoc, mul_inv_cancel₀ (ne_of_gt h), one_mul] at hp hq
    exact ⟨le_antisymm h₁.1 hp, le_antisymm h₁.2 hq⟩

lemma normSum_nonneg (v : ι →₀ ℝ) : 0 ≤ T.normSum v :=
  add_nonneg (T.P_nonneg v T.root) (T.Q_nonneg v T.root)

@[simp] lemma normSum_zero : T.normSum 0 = 0 := by
  unfold normSum
  rw [(T.potentials_zero T.root).1, (T.potentials_zero T.root).2, add_zero]

lemma normSum_neg (v : ι →₀ ℝ) : T.normSum (-v) = T.normSum v := by
  unfold normSum
  rw [(T.potentials_neg v T.root).1, (T.potentials_neg v T.root).2, add_comm]

lemma normSum_add_le (v w : ι →₀ ℝ) : T.normSum (v + w) ≤ T.normSum v + T.normSum w := by
  have h := T.potentials_add_le v w T.root
  unfold normSum
  linarith [h.1, h.2]

lemma normSum_smul_nonneg (a : ℝ) (ha : 0 ≤ a) (v : ι →₀ ℝ) :
    T.normSum (a • v) = a * T.normSum v := by
  unfold normSum
  rw [(T.potentials_smul_nonneg a ha v T.root).1,
    (T.potentials_smul_nonneg a ha v T.root).2, mul_add]

lemma normSum_smul (a : ℝ) (v : ι →₀ ℝ) : T.normSum (a • v) = |a| * T.normSum v := by
  rcases le_total 0 a with ha | ha
  · rw [abs_of_nonneg ha, T.normSum_smul_nonneg a ha]
  · rw [abs_of_nonpos ha, ← T.normSum_smul_nonneg (-a) (neg_nonneg.mpr ha) v,
      neg_smul, T.normSum_neg]

lemma abs_coordinate_le_normSum (v : ι →₀ ℝ) (s : ι) : |v s| ≤ T.normSum v := by
  have hp := (T.P_upper v).le_root T (T.P_nonneg v) s
  have hq := (T.Q_upper v).le_root T (T.Q_nonneg v) s
  have hd := T.P_sub_Q v s
  have hp0 := T.P_nonneg v T.root
  have hq0 := T.Q_nonneg v T.root
  have hp1 := T.P_nonneg v s
  have hq1 := T.Q_nonneg v s
  unfold normSum
  exact abs_le.mpr ⟨by linarith, by linarith⟩

lemma normSum_eq_zero_iff (v : ι →₀ ℝ) : T.normSum v = 0 ↔ v = 0 := by
  constructor
  · intro hv
    ext s
    have h := T.abs_coordinate_le_normSum v s
    rw [hv] at h
    exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))
  · rintro rfl
    exact T.normSum_zero

lemma projectHead_apply (H : Finset ι) (v : ι →₀ ℝ) (s : ι) :
    T.projectHead H v s = if s ∈ H then v s else 0 := Finsupp.filter_apply _ _ _

lemma projectHead_bound (H : Finset ι) (hH : T.Initial H) (v : ι →₀ ℝ) :
    T.normSum (T.projectHead H v) ≤ T.normSum v := by
  let p := extend H (fun s => T.P v s.1)
  let q := extend H (fun s => T.Q v s.1)
  have hdiff : ∀ s, p s - q s = T.projectHead H v s := by
    intro s
    rw [T.projectHead_apply]
    by_cases hs : s ∈ H
    · simp only [p, q, extend_mem _ _ hs, ite_eq_left hs, T.P_sub_Q]
    · simp only [p, q, extend_not_mem _ _ hs, ite_eq_right hs, sub_zero]
  have h := T.potentials_minimal _ p q
    (extend_nonneg _ _ (fun s => T.P_nonneg v s.1))
    (extend_nonneg _ _ (fun s => T.Q_nonneg v s.1)) hdiff
    (T.extend_upper H hH _ ((T.P_upper v).restrict T H hH))
    (T.extend_upper H hH _ ((T.Q_upper v).restrict T H hH)) T.root
  simp only [p, q, extend_mem _ _ hH.1] at h
  unfold normSum
  exact add_le_add h.1 h.2

end FiniteRootedTree

def TreeVector {ι : Type uIndex} (_T : FiniteRootedTree ι) := ι →₀ ℝ

namespace TreeVector

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

instance : AddCommGroup (TreeVector T) := inferInstanceAs (AddCommGroup (ι →₀ ℝ))

instance : Module ℝ (TreeVector T) := inferInstanceAs (Module ℝ (ι →₀ ℝ))

instance : CoeFun (TreeVector T) (fun _ => ι → ℝ) := ⟨fun v => (show ι →₀ ℝ from v)⟩

noncomputable instance : Norm (TreeVector T) := ⟨fun v => T.normSum v⟩

theorem normCore : NormedSpace.Core ℝ (TreeVector T) where
  norm_nonneg v := T.normSum_nonneg v
  norm_smul a v := by
    change T.normSum (a • v) = ‖a‖ * T.normSum v
    rw [Real.norm_eq_abs]
    exact T.normSum_smul a v
  norm_triangle v w := T.normSum_add_le v w
  norm_eq_zero_iff v := T.normSum_eq_zero_iff v

noncomputable instance : NormedAddCommGroup (TreeVector T) :=
  NormedAddCommGroup.ofCore (normCore T)

noncomputable instance : NormedSpace ℝ (TreeVector T) := NormedSpace.ofCore (normCore T)

def coordinateLinear (s : ι) : TreeVector T →ₗ[ℝ] ℝ where
  toFun v := v s
  map_add' _v _w := rfl
  map_smul' _a _v := rfl

noncomputable def coordinate (s : ι) : TreeVector T →L[ℝ] ℝ :=
  (coordinateLinear T s).mkContinuous 1 (fun v => by
    change ‖v s‖ ≤ 1 * T.normSum v
    rw [Real.norm_eq_abs, one_mul]
    exact T.abs_coordinate_le_normSum v s)

def projectionLinear (H : Finset ι) : TreeVector T →ₗ[ℝ] TreeVector T where
  toFun := T.projectHead H
  map_add' v w := by
    change ι →₀ ℝ at v w
    apply Finsupp.ext
    intro s
    change T.projectHead H (v + w) s = (T.projectHead H v + T.projectHead H w) s
    by_cases hs : s ∈ H <;> simp [FiniteRootedTree.projectHead, hs]
  map_smul' a v := by
    change ι →₀ ℝ at v
    apply Finsupp.ext
    intro s
    change T.projectHead H (a • v) s = (a • T.projectHead H v) s
    by_cases hs : s ∈ H <;> simp [FiniteRootedTree.projectHead, hs]

noncomputable def projection (H : Finset ι) (hH : T.Initial H) :
    TreeVector T →L[ℝ] TreeVector T :=
  (projectionLinear T H).mkContinuous 1 (fun v => by
    change T.normSum (T.projectHead H v) ≤ 1 * T.normSum v
    rw [one_mul]
    exact T.projectHead_bound H hH v)

lemma projection_contracts (H : Finset ι) (hH : T.Initial H) (v : TreeVector T) :
    ‖projection T H hH v‖ ≤ ‖v‖ := T.projectHead_bound H hH v

end TreeVector

abbrev TreeSpace {ι : Type uIndex} [DecidableEq ι] (T : FiniteRootedTree ι) :=
  UniformSpace.Completion (TreeVector T)

namespace TreeSpace

open UniformSpace

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

def coordinate (s : ι) : TreeSpace T →L[ℝ] ℝ := (TreeVector.coordinate T s).fromCompletion

def P (s : ι) : TreeSpace T → ℝ :=
  Completion.extension (fun v : TreeVector T => T.P v s)

def Q (s : ι) : TreeSpace T → ℝ :=
  Completion.extension (fun v : TreeVector T => T.Q v s)

def projection (H : Finset ι) (hH : T.Initial H) : TreeSpace T →L[ℝ] TreeSpace T :=
  (TreeVector.projection T H hH).completion

def tail (H : Finset ι) (hH : T.Initial H) : Submodule ℝ (TreeSpace T) :=
  (projection T H hH).ker

end TreeSpace

abbrev XSigma := TreeSpace sequenceTree

abbrev XJoined := TreeSpace joinedTree

namespace TreeVector

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

lemma coordinate_projection (H : Finset ι) (hH : T.Initial H) (s : ι) (v : TreeVector T) :
    coordinate T s (projection T H hH v) = if s ∈ H then v s else 0 :=
  T.projectHead_apply H v s

end TreeVector

def ZeroTreeVector {ι : Type uIndex} [DecidableEq ι] (T : FiniteRootedTree ι) : Type _ :=
  ↥((TreeVector.coordinate T T.root).ker)

namespace ZeroTreeVector

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

instance : AddCommGroup (ZeroTreeVector T) :=
  inferInstanceAs (AddCommGroup (TreeVector.coordinate T T.root).ker)

instance : Module ℝ (ZeroTreeVector T) :=
  inferInstanceAs (Module ℝ (TreeVector.coordinate T T.root).ker)

def toTree : ZeroTreeVector T →ₗ[ℝ] TreeVector T :=
  (TreeVector.coordinate T T.root).ker.subtype

lemma toTree_injective : Function.Injective (toTree T) := Subtype.val_injective

lemma root_zero (v : ZeroTreeVector T) : toTree T v T.root = 0 := v.2

instance : Norm (ZeroTreeVector T) := ⟨fun v => T.P (toTree T v) T.root⟩

lemma norm_half (v : ZeroTreeVector T) : ‖v‖ = ‖toTree T v‖ / 2 := by
  change T.P (toTree T v) T.root = T.normSum (toTree T v) / 2
  have h := T.P_sub_Q (toTree T v) T.root
  rw [root_zero] at h
  unfold FiniteRootedTree.normSum
  linarith

lemma normCore : NormedSpace.Core ℝ (ZeroTreeVector T) where
  norm_nonneg v := by rw [norm_half]; positivity
  norm_smul a v := by rw [norm_half, map_smul, norm_smul, norm_half]; ring
  norm_triangle v w := by
    rw [norm_half, map_add, norm_half, norm_half]
    have h := norm_add_le (toTree T v) (toTree T w)
    linarith
  norm_eq_zero_iff v := by
    rw [norm_half, div_eq_zero_iff]
    simp only [show (2 : ℝ) ≠ 0 by norm_num, or_false, norm_eq_zero]
    exact (toTree T).map_eq_zero_iff (toTree_injective T)

instance : NormedAddCommGroup (ZeroTreeVector T) := NormedAddCommGroup.ofCore (normCore T)

instance : NormedSpace ℝ (ZeroTreeVector T) := NormedSpace.ofCore (normCore T)

def inclusion : ZeroTreeVector T →L[ℝ] TreeVector T :=
  (toTree T).mkContinuous 2 (fun v => by rw [norm_half]; exact le_of_eq (by ring))

def projectionLinear (H : Finset ι) (hH : T.Initial H) : ZeroTreeVector T →ₗ[ℝ] ZeroTreeVector T :=
  (((TreeVector.projection T H hH).toLinearMap).comp (toTree T)).codRestrict
    (TreeVector.coordinate T T.root).ker (fun v => by
      change TreeVector.coordinate T T.root (TreeVector.projection T H hH (toTree T v)) = 0
      rw [TreeVector.coordinate_projection, ite_eq_left hH.1, root_zero])

def projection (H : Finset ι) (hH : T.Initial H) : ZeroTreeVector T →L[ℝ] ZeroTreeVector T :=
  (projectionLinear T H hH).mkContinuous 1 (fun v => by
    rw [one_mul, norm_half, norm_half]
    exact (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).mpr
      (TreeVector.projection_contracts T H hH (toTree T v)))

end ZeroTreeVector

abbrev ZeroTreeSpace {ι : Type uIndex} [DecidableEq ι] (T : FiniteRootedTree ι) :=
  UniformSpace.Completion (ZeroTreeVector T)

namespace ZeroTreeSpace

open UniformSpace

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

def inclusion : ZeroTreeSpace T →L[ℝ] TreeSpace T := (ZeroTreeVector.inclusion T).completion

def projection (H : Finset ι) (hH : T.Initial H) : ZeroTreeSpace T →L[ℝ] ZeroTreeSpace T :=
  (ZeroTreeVector.projection T H hH).completion

def tail (H : Finset ι) (hH : T.Initial H) : Submodule ℝ (ZeroTreeSpace T) :=
  (projection T H hH).ker

end ZeroTreeSpace

abbrev XZero := ZeroTreeSpace joinedTree

namespace ZeroTreeSpace

open UniformSpace

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

def coordinate (s : ι) : ZeroTreeSpace T →L[ℝ] ℝ :=
  (TreeSpace.coordinate T s).comp (inclusion T)

def P (s : ι) (x : ZeroTreeSpace T) : ℝ := TreeSpace.P T s (inclusion T x)

def Q (s : ι) (x : ZeroTreeSpace T) : ℝ := TreeSpace.Q T s (inclusion T x)

end ZeroTreeSpace

open Filter Topology

open Filter Topology

open scoped ENNReal

namespace SquareSum

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (E : ι → Type uFiber)
    [∀ i, NormedAddCommGroup (E i)] [fiberNormedSpace : ∀ i, NormedSpace ℝ (E i)]

abbrev DualFamily (i : ι) := E i →L[ℝ] ℝ

def pairing : Space (DualFamily E) →L[ℝ] (Space E →L[ℝ] ℝ) :=
  lp.dualPairing 2 2 (fun i => ContinuousLinearMap.id ℝ (E i →L[ℝ] ℝ))
    (K := 1) (fun _i => ContinuousLinearMap.norm_id_le)

end SquareSum

open UniformSpace

namespace TreeVector

open scoped ENNReal

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

def toSquareLinear : TreeVector T →ₗ[ℝ] SquareSum.Space (fun _ : ι => ℝ) :=
  Finsupp.lsum ℝ (fun s => lp.lsingle (𝕜 := ℝ) (E := fun _ : ι => ℝ) 2 s)

end TreeVector

open Filter

open scoped Topology

namespace ChildExponent

variable (p : ChildExponent)

lemma pos : 0 < p.val := lt_of_lt_of_le zero_lt_one p.one_le

lemma ne_zero : p.val ≠ 0 := p.pos.ne'

lemma inv_pos : 0 < 1 / p.val := one_div_pos.mpr p.pos

lemma agg_nonneg {ι : Type uIndex} (s : Finset ι) (f : ι → ℝ) : 0 ≤ p.agg s f := by
  unfold agg; positivity

lemma agg_rpow {ι : Type uIndex} (s : Finset ι) (f : ι → ℝ) :
    p.agg s f ^ p.val = ∑ i ∈ s, |f i| ^ p.val := by
  rw [agg, ← Real.rpow_mul (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (abs_nonneg _) _)]
  rw [one_div_mul_cancel p.ne_zero, Real.rpow_one]

lemma agg_mono {ι : Type uIndex} (s : Finset ι) (f g : ι → ℝ)
    (hfg : ∀ i ∈ s, |f i| ≤ |g i|) : p.agg s f ≤ p.agg s g := by
  unfold agg
  exact Real.rpow_le_rpow (by positivity)
    (Finset.sum_le_sum fun i hi => Real.rpow_le_rpow (abs_nonneg _) (hfg i hi) p.pos.le) p.inv_pos.le

lemma agg_mono_nonneg {ι : Type uIndex} (s : Finset ι) (f g : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) (hfg : ∀ i ∈ s, f i ≤ g i) : p.agg s f ≤ p.agg s g :=
  p.agg_mono s f g (fun i hi => by rw [abs_of_nonneg (hf i hi), abs_of_nonneg ((hf i hi).trans (hfg i hi))]; exact hfg i hi)

lemma agg_add_le {ι : Type uIndex} (s : Finset ι) (f g : ι → ℝ) :
    p.agg s (f+g) ≤ p.agg s f + p.agg s g := Real.Lp_add_le s f g p.one_le

@[simp] lemma agg_zero {ι : Type uIndex} (s : Finset ι) : p.agg s (fun _ => 0) = 0 := by
  simp [agg, Real.zero_rpow p.ne_zero, Real.zero_rpow (inv_ne_zero p.ne_zero)]

@[simp] lemma agg_empty {ι : Type uIndex} (f : ι → ℝ) : p.agg ∅ f = 0 := by
  simp [agg, Real.zero_rpow (inv_ne_zero p.ne_zero)]

lemma agg_smul {ι : Type uIndex} (s : Finset ι) (a : ℝ) (f : ι → ℝ) :
    p.agg s (fun i => a * f i) = |a| * p.agg s f := by
  unfold agg
  simp_rw [abs_mul, Real.mul_rpow (abs_nonneg a) (abs_nonneg _)]
  rw [← Finset.mul_sum, Real.mul_rpow (Real.rpow_nonneg (abs_nonneg a) _) (by positivity),
    ← Real.rpow_mul (abs_nonneg a), mul_one_div_cancel p.ne_zero, Real.rpow_one]

lemma coordinate_le_agg {ι : Type uIndex} (s : Finset ι) (f : ι → ℝ) {i : ι} (hi : i ∈ s) :
    |f i| ≤ p.agg s f := by
  apply (Real.rpow_le_rpow_iff (abs_nonneg _) (p.agg_nonneg s f) p.pos).mp
  rw [p.agg_rpow]
  exact Finset.single_le_sum (fun j _ => Real.rpow_nonneg (abs_nonneg _) _) hi

lemma agg_subset {ι : Type uIndex} (s t : Finset ι) (f : ι → ℝ) (hst : s ⊆ t) :
    p.agg s f ≤ p.agg t f := by
  apply (Real.rpow_le_rpow_iff (p.agg_nonneg s f) (p.agg_nonneg t f) p.pos).mp
  simp only [p.agg_rpow]
  exact Finset.sum_le_sum_of_subset_of_nonneg hst (fun i _ _ => Real.rpow_nonneg (abs_nonneg _) _)

lemma agg_congr {ι : Type uIndex} (s : Finset ι) (f g : ι → ℝ) (h : ∀ i ∈ s, f i = g i) :
    p.agg s f = p.agg s g := by
  unfold agg
  congr 1
  exact Finset.sum_congr rfl (fun i hi => by rw [h i hi])

end ChildExponent

namespace FiniteRootedTree

variable {ι : Type uIndex} [indexFinite : Fintype ι] [indexDecidable : DecidableEq ι]
    (T : FiniteRootedTree ι) (p : ChildExponent)

def PUpper (f : ι → ℝ) : Prop := ∀ s, p.agg (T.children s) f ≤ f s

lemma pfields_eq (v : ι → ℝ) (s : ι) :
    T.pfields p v s = leastPair (v s)
      (p.agg (T.children s) (fun c => (T.pfields p v c).1))
      (p.agg (T.children s) (fun c => (T.pfields p v c).2)) := by
  rw [pfields]
  simp only [ChildExponent.agg]
  rw [← Finset.sum_subtype (T.children s) (fun _ => Iff.rfl) (fun c => |(T.pfields p v c).1| ^ p.val),
    ← Finset.sum_subtype (T.children s) (fun _ => Iff.rfl) (fun c => |(T.pfields p v c).2| ^ p.val)]

lemma pfields_nonneg (v : ι → ℝ) (s : ι) :
    0 ≤ (T.pfields p v s).1 ∧ 0 ≤ (T.pfields p v s).2 := by
  rw [T.pfields_eq]
  exact leastPair_nonneg (p.agg_nonneg _ _) (p.agg_nonneg _ _)

lemma pfields_difference (v : ι → ℝ) (s : ι) :
    (T.pfields p v s).1 - (T.pfields p v s).2 = v s := by
  rw [T.pfields_eq]; exact leastPair_difference _ _ _

lemma pfields_upper (v : ι → ℝ) :
    T.PUpper p (fun s => (T.pfields p v s).1) ∧ T.PUpper p (fun s => (T.pfields p v s).2) := by
  constructor <;> intro s <;> dsimp only <;> rw [T.pfields_eq] <;> exact le_max_left _ _

theorem pfields_minimal (v a b : ι → ℝ) (ha : ∀ s, 0 ≤ a s) (hb : ∀ s, 0 ≤ b s)
    (hdiff : ∀ s, a s - b s = v s) (haU : T.PUpper p a) (hbU : T.PUpper p b) (s : ι) :
    (T.pfields p v s).1 ≤ a s ∧ (T.pfields p v s).2 ≤ b s := by
  rw [T.pfields_eq]
  apply leastPair_minimal (hdiff s)
  · exact (p.agg_mono_nonneg _ _ a (fun c _ => (T.pfields_nonneg p v c).1)
      (fun c hc => (pfields_minimal v a b ha hb hdiff haU hbU c).1)).trans (haU s)
  · exact (p.agg_mono_nonneg _ _ b (fun c _ => (T.pfields_nonneg p v c).2)
      (fun c hc => (pfields_minimal v a b ha hb hdiff haU hbU c).2)).trans (hbU s)
termination_by T.maxDepth - T.depth s
decreasing_by all_goals exact T.child_measure hc

def pRootSum (v : ι → ℝ) : ℝ := (T.pfields p v T.root).1 + (T.pfields p v T.root).2

lemma pRootSum_nonneg (v : ι → ℝ) : 0 ≤ T.pRootSum p v :=
  add_nonneg (T.pfields_nonneg p v T.root).1 (T.pfields_nonneg p v T.root).2

end FiniteRootedTree

namespace VariableExponent

lemma heightExponent_gt_one (h : ℕ+) : 1 < heightExponent h := by
  have hh : (0 : ℝ) < h.val := by exact_mod_cast h.pos
  dsimp [heightExponent]; exact lt_add_of_pos_right _ (one_div_pos.mpr hh)

end VariableExponent

namespace FiniteRootedTree

variable {ι : Type uIndex} [indexFinite : Fintype ι] [indexDecidable : DecidableEq ι]
    (T : FiniteRootedTree ι)

lemma depth_eq_zero_iff {ι : Type uIndex} [Fintype ι] [DecidableEq ι] (T : FiniteRootedTree ι)
    (s : ι) : T.depth s = 0 ↔ s = T.root := by
  refine ⟨fun hs => ?_, fun hs => hs ▸ T.depth_root⟩
  by_contra hn
  have := T.parent_depth s hn
  omega

def headLevel (H : Finset ι) (j : ℕ) : Finset ι := H.filter fun s => T.depth s = j

def childrenOf (S : Finset ι) : Finset ι := Finset.univ.filter fun c => c ≠ T.root ∧ T.parent c ∈ S

lemma sum_children_on (S : Finset ι) (f : ι → ℝ) :
    ∑ s ∈ S, ∑ c ∈ T.children s, f c = ∑ c ∈ T.childrenOf S, f c := by
  unfold childrenOf children
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c hc
  by_cases hcr : c = T.root
  · simp [hcr]
  · simp only [hcr, ne_eq, not_false_eq_true, true_and]
    rw [Finset.sum_ite_eq]

end FiniteRootedTree

namespace VariableTree

open FiniteRootedTree

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)
    (e : ChildExponent)

def GlobalUpper (f : ι → ℝ) : Prop :=
  ∀ (s : ι) (S : Finset ι), (∀ c ∈ S, c ≠ T.root ∧ T.parent c = s) → e.agg S f ≤ f s

lemma GlobalUpper.restrict {f : ι → ℝ} (hf : GlobalUpper T e f) (H : Finset ι)
    (hH : T.Initial H) : (T.restrict H hH).PUpper e (fun s => f s.1) := by
  intro s
  have he : e.agg (T.restrict H hH |>.children s) (fun c => f c.1) =
      e.agg (H.filter fun c => c ≠ T.root ∧ T.parent c = s.1) f := by
    unfold ChildExponent.agg
    rw [T.sum_restrict_children H hH s (fun c => |f c| ^ e.val)]
  rw [he]
  exact hf s.1 _ (fun c hc => (Finset.mem_filter.mp hc).2)

lemma extend_upper (H : Finset ι) (hH : T.Initial H) (f : H → ℝ)
    (hf : (T.restrict H hH).PUpper e f) : GlobalUpper T e (extend H f) := by
  intro s S hS
  by_cases hs : s ∈ H
  · have hsum : e.agg S (extend H f) = e.agg (S.filter fun c => c ∈ H) (extend H f) := by
      unfold ChildExponent.agg
      rw [Finset.sum_filter]
      congr 1
      apply Finset.sum_congr rfl
      intro c hc
      by_cases hh : c ∈ H
      · simp [hh]
      · simp [hh, extend_not_mem H f hh, Real.zero_rpow e.ne_zero]
    rw [hsum]
    calc
      _ ≤ e.agg (H.filter fun c => c ≠ T.root ∧ T.parent c = s) (extend H f) := by
        apply e.agg_subset
        intro c hc
        obtain ⟨hcS,hcH⟩ := Finset.mem_filter.mp hc
        exact Finset.mem_filter.mpr ⟨hcH,hS c hcS⟩
      _ = e.agg ((T.restrict H hH).children ⟨s,hs⟩) f := by
        unfold ChildExponent.agg
        rw [← T.sum_restrict_children H hH ⟨s,hs⟩ (fun c => |extend H f c| ^ e.val)]
        simp only [extend_coe]
      _ ≤ extend H f s := by rw [extend_mem H f hs]; exact hf ⟨s,hs⟩
  · rw [extend_not_mem H f hs]
    have hc0 : ∀ c ∈ S, extend H f c = 0 := by
      intro c hc
      apply extend_not_mem
      intro hh
      have hcp := hH.2 c hh
      rw [(hS c hc).2] at hcp
      exact hs hcp
    rw [e.agg_congr _ _ (fun _ => 0) hc0, e.agg_zero]

lemma GlobalUpper.add {ι : Type uIndex} [DecidableEq ι] (T : FiniteRootedTree ι) (e : ChildExponent)
    {f g : ι → ℝ} (hf : GlobalUpper T e f) (hg : GlobalUpper T e g) (_hf0 : ∀ s, 0 ≤ f s)
    (_hg0 : ∀ s, 0 ≤ g s) : GlobalUpper T e (f+g) := by
  intro s S hS
  exact (e.agg_add_le S f g).trans (add_le_add (hf s S hS) (hg s S hS))

lemma GlobalUpper.smul {ι : Type uIndex} [DecidableEq ι] (T : FiniteRootedTree ι)
    (e : ChildExponent) {f : ι → ℝ} (hf : GlobalUpper T e f) (a : ℝ) (ha : 0 ≤ a) :
    GlobalUpper T e (a • f) := by
  intro s S hS
  change e.agg S (fun c => a*f c) ≤ a*f s
  rw [e.agg_smul, abs_of_nonneg ha]
  exact mul_le_mul_of_nonneg_left (hf s S hS) ha

lemma GlobalUpper.le_root {f : ι → ℝ} (hf : GlobalUpper T e f)
    (_hf0 : ∀ s, 0 ≤ f s) (s : ι) : f s ≤ f T.root := by
  by_cases hs : s = T.root
  · simp [hs]
  · have hbound := hf (T.parent s) {s} (by simpa using hs)
    have hcoord := e.coordinate_le_agg {s} f (Finset.mem_singleton_self s)
    exact ((le_abs_self _).trans (hcoord.trans hbound)).trans (GlobalUpper.le_root hf _hf0 (T.parent s))
termination_by T.depth s
decreasing_by exact T.parent_depth s hs

noncomputable def P (v : ι →₀ ℝ) : ι →₀ ℝ :=
  extend (T.head v) (fun s => ((T.restrict (T.head v) (T.head_initial v)).pfields e
    (fun s => v s.1) s).1)

noncomputable def Q (v : ι →₀ ℝ) : ι →₀ ℝ :=
  extend (T.head v) (fun s => ((T.restrict (T.head v) (T.head_initial v)).pfields e
    (fun s => v s.1) s).2)

lemma P_nonneg (v : ι →₀ ℝ) (s : ι) : 0 ≤ P T e v s :=
  extend_nonneg _ _ (fun s => ((T.restrict _ _).pfields_nonneg e _ s).1) s

lemma Q_nonneg (v : ι →₀ ℝ) (s : ι) : 0 ≤ Q T e v s :=
  extend_nonneg _ _ (fun s => ((T.restrict _ _).pfields_nonneg e _ s).2) s

lemma P_upper (v : ι →₀ ℝ) : GlobalUpper T e (P T e v) :=
  extend_upper T e _ _ _ ((T.restrict _ _).pfields_upper e _).1

lemma Q_upper (v : ι →₀ ℝ) : GlobalUpper T e (Q T e v) :=
  extend_upper T e _ _ _ ((T.restrict _ _).pfields_upper e _).2

lemma P_sub_Q (v : ι →₀ ℝ) (s : ι) : P T e v s - Q T e v s = v s := by
  by_cases hs : s ∈ T.head v
  · simp only [P, Q, extend_mem _ _ hs]
    exact (T.restrict _ _).pfields_difference e _ _
  · simp only [P, Q, extend_not_mem _ _ hs, T.zero_off_head v hs, sub_zero]

lemma potentials_minimal (v : ι →₀ ℝ) (p q : ι → ℝ)
    (hp : ∀ s, 0 ≤ p s) (hq : ∀ s, 0 ≤ q s) (hdiff : ∀ s, p s - q s = v s)
    (hpU : GlobalUpper T e p) (hqU : GlobalUpper T e q) (s : ι) :
    P T e v s ≤ p s ∧ Q T e v s ≤ q s := by
  by_cases hs : s ∈ T.head v
  · simp only [P, Q, extend_mem _ _ hs]
    exact (T.restrict _ _).pfields_minimal e (fun s => v s.1) (fun s => p s.1)
      (fun s => q s.1) (fun s => hp s.1) (fun s => hq s.1) (fun s => hdiff s.1)
      (hpU.restrict T e _ _) (hqU.restrict T e _ _) ⟨s, hs⟩
  · simp only [P, Q, extend_not_mem _ _ hs]
    exact ⟨hp s, hq s⟩

theorem potentials_on_head (v : ι →₀ ℝ) (H : Finset ι) (hH : T.Initial H)
    (hv : v.support ⊆ H) (s : H) :
    P T e v s.1 = ((T.restrict H hH).pfields e (fun c => v c.1) s).1 ∧
    Q T e v s.1 = ((T.restrict H hH).pfields e (fun c => v c.1) s).2 := by
  let U := T.restrict H hH
  let p : ι →₀ ℝ := extend H (fun c => (U.pfields e (fun c => v c.1) c).1)
  let q : ι →₀ ℝ := extend H (fun c => (U.pfields e (fun c => v c.1) c).2)
  have hdiff : ∀ c, p c - q c = v c := by
    intro c
    by_cases hc : c ∈ H
    · simp only [p, q, extend_mem _ _ hc]
      exact U.pfields_difference e _ _
    · have hv0 : v c = 0 := Finsupp.notMem_support_iff.mp (fun h => hc (hv h))
      simp only [p, q, extend_not_mem _ _ hc, hv0, sub_zero]
  have h₁ := potentials_minimal T e v p q
    (extend_nonneg _ _ (fun c => (U.pfields_nonneg e _ c).1))
    (extend_nonneg _ _ (fun c => (U.pfields_nonneg e _ c).2)) hdiff
    (extend_upper T e _ _ _ (U.pfields_upper e _).1)
    (extend_upper T e _ _ _ (U.pfields_upper e _).2) s.1
  have h₂ := U.pfields_minimal e (fun c => v c.1) (fun c => P T e v c.1)
    (fun c => Q T e v c.1) (fun c => P_nonneg T e v c.1) (fun c => Q_nonneg T e v c.1)
    (fun c => P_sub_Q T e v c.1) ((P_upper T e v).restrict T e H hH)
    ((Q_upper T e v).restrict T e H hH) s
  simp only [p, q, extend_coe] at h₁
  exact ⟨le_antisymm h₁.1 h₂.1, le_antisymm h₁.2 h₂.2⟩

noncomputable def normSum (v : ι →₀ ℝ) : ℝ := P T e v T.root + Q T e v T.root

lemma normSum_on_head (v : ι →₀ ℝ) (H : Finset ι) (hH : T.Initial H)
    (hv : v.support ⊆ H) : normSum T e v = (T.restrict H hH).pRootSum e (fun s => v s.1) := by
  have h := potentials_on_head T e v H hH hv ⟨T.root, hH.1⟩
  exact congrArg₂ (· + ·) h.1 h.2

lemma potentials_zero (s : ι) : P T e 0 s = 0 ∧ Q T e 0 s = 0 := by
  have h := potentials_minimal T e 0 (fun _ => 0) (fun _ => 0)
    (fun _ => le_rfl) (fun _ => le_rfl) (fun _ => by simp)
    (by intro s S hS; simp [ChildExponent.agg_zero]) (by intro s S hS; simp [ChildExponent.agg_zero]) s
  exact ⟨le_antisymm h.1 (P_nonneg T e 0 s), le_antisymm h.2 (Q_nonneg T e 0 s)⟩

lemma potentials_add_le (v w : ι →₀ ℝ) (s : ι) :
    P T e (v + w) s ≤ P T e v s + P T e w s ∧ Q T e (v + w) s ≤ Q T e v s + Q T e w s := by
  apply potentials_minimal T e (v + w) (fun c => P T e v c + P T e w c)
    (fun c => Q T e v c + Q T e w c)
  · intro c; exact add_nonneg (P_nonneg T e v c) (P_nonneg T e w c)
  · intro c; exact add_nonneg (Q_nonneg T e v c) (Q_nonneg T e w c)
  · intro c
    simp only [Finsupp.add_apply]
    linarith [P_sub_Q T e v c, P_sub_Q T e w c]
  · exact (P_upper T e v).add T e (P_upper T e w) (P_nonneg T e v) (P_nonneg T e w)
  · exact (Q_upper T e v).add T e (Q_upper T e w) (Q_nonneg T e v) (Q_nonneg T e w)

lemma potentials_neg (v : ι →₀ ℝ) (s : ι) :
    P T e (-v) s = Q T e v s ∧ Q T e (-v) s = P T e v s := by
  have h₁ := potentials_minimal T e (-v) (Q T e v) (P T e v)
    (Q_nonneg T e v) (P_nonneg T e v)
    (fun c => by simp only [Finsupp.neg_apply]; linarith [P_sub_Q T e v c])
    (Q_upper T e v) (P_upper T e v) s
  have h₂ := potentials_minimal T e v (Q T e (-v)) (P T e (-v))
    (Q_nonneg T e (-v)) (P_nonneg T e (-v))
    (fun c => by have h := P_sub_Q T e (-v) c; simp only [Finsupp.neg_apply] at h; linarith)
    (Q_upper T e (-v)) (P_upper T e (-v)) s
  exact ⟨le_antisymm h₁.1 h₂.2, le_antisymm h₁.2 h₂.1⟩

lemma potentials_smul_le (a : ℝ) (ha : 0 ≤ a) (v : ι →₀ ℝ) (s : ι) :
    P T e (a • v) s ≤ a * P T e v s ∧ Q T e (a • v) s ≤ a * Q T e v s := by
  apply potentials_minimal T e (a • v) (fun c => a * P T e v c) (fun c => a * Q T e v c)
  · intro c; exact mul_nonneg ha (P_nonneg T e v c)
  · intro c; exact mul_nonneg ha (Q_nonneg T e v c)
  · intro c
    simp only [Finsupp.smul_apply, smul_eq_mul, ← mul_sub, P_sub_Q T e]
  · exact (P_upper T e v).smul T e a ha
  · exact (Q_upper T e v).smul T e a ha

lemma potentials_smul_nonneg (a : ℝ) (ha : 0 ≤ a) (v : ι →₀ ℝ) (s : ι) :
    P T e (a • v) s = a * P T e v s ∧ Q T e (a • v) s = a * Q T e v s := by
  rcases eq_or_lt_of_le ha with h | h
  · subst a
    simpa using potentials_zero T e s
  · have h₁ := potentials_smul_le T e a ha v s
    have h₂ := potentials_smul_le T e a⁻¹ (inv_nonneg.mpr ha) (a • v) s
    simp only [smul_smul, inv_mul_cancel₀ (ne_of_gt h), one_smul] at h₂
    have hp := mul_le_mul_of_nonneg_left h₂.1 ha
    have hq := mul_le_mul_of_nonneg_left h₂.2 ha
    simp only [← mul_assoc, mul_inv_cancel₀ (ne_of_gt h), one_mul] at hp hq
    exact ⟨le_antisymm h₁.1 hp, le_antisymm h₁.2 hq⟩

lemma normSum_nonneg (v : ι →₀ ℝ) : 0 ≤ normSum T e v :=
  add_nonneg (P_nonneg T e v T.root) (Q_nonneg T e v T.root)

@[simp] lemma normSum_zero : normSum T e 0 = 0 := by
  unfold normSum
  rw [(potentials_zero T e T.root).1, (potentials_zero T e T.root).2, add_zero]

lemma normSum_neg (v : ι →₀ ℝ) : normSum T e (-v) = normSum T e v := by
  unfold normSum
  rw [(potentials_neg T e v T.root).1, (potentials_neg T e v T.root).2, add_comm]

lemma normSum_add_le (v w : ι →₀ ℝ) : normSum T e (v + w) ≤ normSum T e v + normSum T e w := by
  have h := potentials_add_le T e v w T.root
  unfold normSum
  linarith [h.1, h.2]

lemma normSum_smul_nonneg (a : ℝ) (ha : 0 ≤ a) (v : ι →₀ ℝ) :
    normSum T e (a • v) = a * normSum T e v := by
  unfold normSum
  rw [(potentials_smul_nonneg T e a ha v T.root).1,
    (potentials_smul_nonneg T e a ha v T.root).2, mul_add]

lemma normSum_smul (a : ℝ) (v : ι →₀ ℝ) : normSum T e (a • v) = |a| * normSum T e v := by
  rcases le_total 0 a with ha | ha
  · rw [abs_of_nonneg ha, normSum_smul_nonneg T e a ha]
  · rw [abs_of_nonpos ha, ← normSum_smul_nonneg T e (-a) (neg_nonneg.mpr ha) v,
      neg_smul, normSum_neg T e]

lemma abs_coordinate_le_normSum (v : ι →₀ ℝ) (s : ι) : |v s| ≤ normSum T e v := by
  have hp := (P_upper T e v).le_root T e (P_nonneg T e v) s
  have hq := (Q_upper T e v).le_root T e (Q_nonneg T e v) s
  have hd := P_sub_Q T e v s
  have hp0 := P_nonneg T e v T.root
  have hq0 := Q_nonneg T e v T.root
  have hp1 := P_nonneg T e v s
  have hq1 := Q_nonneg T e v s
  unfold normSum
  exact abs_le.mpr ⟨by linarith, by linarith⟩

lemma normSum_eq_zero_iff (v : ι →₀ ℝ) : normSum T e v = 0 ↔ v = 0 := by
  constructor
  · intro hv
    ext s
    have h := abs_coordinate_le_normSum T e v s
    rw [hv] at h
    exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))
  · rintro rfl
    exact normSum_zero T e

end VariableTree

def AggregationVector {ι : Type uIndex} (_T : FiniteRootedTree ι) (_e : ChildExponent) := ι →₀ ℝ

namespace AggregationVector

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)
    (e : ChildExponent)

instance : AddCommGroup (AggregationVector T e) := inferInstanceAs (AddCommGroup (ι →₀ ℝ))

instance : Module ℝ (AggregationVector T e) := inferInstanceAs (Module ℝ (ι →₀ ℝ))

instance : CoeFun (AggregationVector T e) (fun _ => ι → ℝ) := ⟨fun v => (show ι →₀ ℝ from v)⟩

noncomputable instance : Norm (AggregationVector T e) := ⟨fun v => VariableTree.normSum T e v⟩

theorem normCore : NormedSpace.Core ℝ (AggregationVector T e) where
  norm_nonneg v := VariableTree.normSum_nonneg T e v
  norm_smul a v := by
    change VariableTree.normSum T e (a • v) = ‖a‖ * VariableTree.normSum T e v
    rw [Real.norm_eq_abs]
    exact VariableTree.normSum_smul T e a v
  norm_triangle v w := VariableTree.normSum_add_le T e v w
  norm_eq_zero_iff v := VariableTree.normSum_eq_zero_iff T e v

noncomputable instance : NormedAddCommGroup (AggregationVector T e) :=
  NormedAddCommGroup.ofCore (normCore T e)

noncomputable instance : NormedSpace ℝ (AggregationVector T e) := NormedSpace.ofCore (normCore T e)

def coordinateLinear (s : ι) : AggregationVector T e →ₗ[ℝ] ℝ where
  toFun v := v s
  map_add' _v _w := rfl
  map_smul' _a _v := rfl

noncomputable def coordinate (s : ι) : AggregationVector T e →L[ℝ] ℝ :=
  (coordinateLinear T e s).mkContinuous 1 (fun v => by
    change ‖v s‖ ≤ 1 * VariableTree.normSum T e v
    rw [Real.norm_eq_abs, one_mul]
    exact VariableTree.abs_coordinate_le_normSum T e v s)

end AggregationVector

abbrev AggregationSpace {ι : Type uIndex} [DecidableEq ι] (T : FiniteRootedTree ι)
    (e : ChildExponent) :=
  UniformSpace.Completion (AggregationVector T e)

namespace AggregationSpace

open UniformSpace

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)
    (e : ChildExponent)

def coordinate (s : ι) :
    AggregationSpace T e →L[ℝ] ℝ := (AggregationVector.coordinate T e s).fromCompletion

def P (s : ι) : AggregationSpace T e → ℝ :=
  Completion.extension (fun v : AggregationVector T e => VariableTree.P T e v s)

def Q (s : ι) : AggregationSpace T e → ℝ :=
  Completion.extension (fun v : AggregationVector T e => VariableTree.Q T e v s)

end AggregationSpace

namespace AggregationVector

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)
    (e : ChildExponent)

def basisVector (s : ι) : AggregationVector T e := Finsupp.single s 1

end AggregationVector

namespace FiniteRootedTree

variable {ι : Type uIndex} [indexFinite : Fintype ι] [indexDecidable : DecidableEq ι]
    (T : FiniteRootedTree ι) (e : ChildExponent)

variable (hstep : ∀ c, c ≠ T.root → T.depth c = T.depth (T.parent c) + 1)

lemma level_zero : T.headLevel Finset.univ 0 = {T.root} := by
  ext s
  simp [headLevel,T.depth_eq_zero_iff]

include hstep in

lemma level_succ (j : ℕ) :
    T.childrenOf (T.headLevel Finset.univ j) = T.headLevel Finset.univ (j+1) := by
  ext s
  simp only [childrenOf,headLevel,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨hne,hd⟩; rw [hstep s hne,hd]
  · intro hd
    have hne : s ≠ T.root := by intro he; rw [he,T.depth_root] at hd; omega
    exact ⟨hne, by have hh := hstep s hne; omega⟩

include hstep in

lemma agg_children_level (f : ι → ℝ) (j : ℕ) :
    e.agg (T.headLevel Finset.univ j) (fun s => e.agg (T.children s) f) =
      e.agg (T.headLevel Finset.univ (j+1)) f := by
  apply (Real.rpow_left_inj (e.agg_nonneg _ _) (e.agg_nonneg _ _) e.ne_zero).mp
  rw [e.agg_rpow,e.agg_rpow]
  simp_rw [abs_of_nonneg (e.agg_nonneg _ _),e.agg_rpow]
  rw [T.sum_children_on,T.level_succ hstep]

lemma agg_level_zero (f : ι → ℝ) : e.agg (T.headLevel Finset.univ 0) f = |f T.root| := by
  rw [T.level_zero,ChildExponent.agg,Finset.sum_singleton,← Real.rpow_mul (abs_nonneg _)]
  simp [e.ne_zero]

include hstep in

lemma PUpper.level_le_root {f : ι → ℝ} (hf : ∀ s, 0 ≤ f s) (hu : T.PUpper e f) (j : ℕ) :
    e.agg (T.headLevel Finset.univ j) f ≤ f T.root := by
  induction j with
  | zero => rw [T.agg_level_zero,abs_of_nonneg (hf _) ]
  | succ j ih =>
    rw [← T.agg_children_level e hstep f j]
    exact (e.agg_mono_nonneg _ _ _ (fun s hs => e.agg_nonneg _ _) (fun s hs => hu s)).trans ih

def pMaximum (v : ι → ℝ) (s : ι) : ℝ := max (T.pfields e v s).1 (T.pfields e v s).2

lemma pMaximum_nonneg (v : ι → ℝ) (s : ι) : 0 ≤ T.pMaximum e v s :=
  (T.pfields_nonneg e v s).1.trans (le_max_left _ _)

lemma pMaximum_bound (v : ι → ℝ) (s : ι) :
    T.pMaximum e v s ≤ |v s| + e.agg (T.children s) (T.pMaximum e v) := by
  have hp := e.agg_mono_nonneg (T.children s) (fun c => (T.pfields e v c).1)
    (T.pMaximum e v) (fun c hc => (T.pfields_nonneg e v c).1) (fun c hc => le_max_left _ _)
  have hq := e.agg_mono_nonneg (T.children s) (fun c => (T.pfields e v c).2)
    (T.pMaximum e v) (fun c hc => (T.pfields_nonneg e v c).2) (fun c hc => le_max_right _ _)
  change max (T.pfields e v s).1 (T.pfields e v s).2 ≤ |v s| + e.agg (T.children s) (T.pMaximum e v)
  rw [T.pfields_eq]
  simp only [leastPair, max_le_iff]
  exact ⟨⟨by linarith [abs_nonneg (v s)],by linarith [le_abs_self (v s)]⟩,
    ⟨by linarith [abs_nonneg (v s)],by linarith [neg_le_abs (v s)]⟩⟩

include hstep in

lemma pMaximum_level (v : ι → ℝ) (j : ℕ) :
    e.agg (T.headLevel Finset.univ j) (T.pMaximum e v) ≤
      e.agg (T.headLevel Finset.univ j) v + e.agg (T.headLevel Finset.univ (j+1)) (T.pMaximum e v) := by
  calc
    _ ≤ e.agg (T.headLevel Finset.univ j)
        ((fun s => |v s|) + (fun s => e.agg (T.children s) (T.pMaximum e v))) :=
      e.agg_mono_nonneg _ _ _ (fun s hs => T.pMaximum_nonneg e v s) (fun s hs => T.pMaximum_bound e v s)
    _ ≤ e.agg (T.headLevel Finset.univ j) (fun s => |v s|) +
        e.agg (T.headLevel Finset.univ j) (fun s => e.agg (T.children s) (T.pMaximum e v)) := e.agg_add_le _ _ _
    _ = _ := by rw [T.agg_children_level e hstep]; simp only [ChildExponent.agg,abs_abs]

include hstep in

lemma pMaximum_level_sum (v : ι → ℝ) (n : ℕ) :
    T.pMaximum e v T.root ≤ (∑ j ∈ Finset.range n, e.agg (T.headLevel Finset.univ j) v) +
      e.agg (T.headLevel Finset.univ n) (T.pMaximum e v) := by
  induction n with
  | zero => simp only [Finset.range_zero,Finset.sum_empty,zero_add,T.agg_level_zero,abs_of_nonneg (T.pMaximum_nonneg e v _),le_refl]
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hh := T.pMaximum_level e hstep v n
    linarith

lemma level_empty {ι : Type uIndex} [Fintype ι] [DecidableEq ι] (T : FiniteRootedTree ι) (h : ℕ)
    (hh : ∀ s, T.depth s ≤ h) : T.headLevel Finset.univ (h+1) = ∅ := by
  ext s
  simp only [headLevel,Finset.mem_filter,Finset.mem_univ,true_and,Finset.notMem_empty,iff_false]
  have hs := hh s
  omega

lemma sum_level_rpow {ι : Type uIndex} [Fintype ι] [DecidableEq ι] (T : FiniteRootedTree ι)
    (e : ChildExponent) (h : ℕ) (hh : ∀ s, T.depth s ≤ h) (v : ι → ℝ) :
    (∑ j ∈ Finset.range (h+1), e.agg (T.headLevel Finset.univ j) v ^ e.val) = e.agg Finset.univ v ^ e.val := by
  simp only [e.agg_rpow,headLevel,Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s hs
  rw [Finset.sum_eq_single (T.depth s)]
  · simp
  · intro b hb hbs
    simp [Ne.symm hbs]
  · intro hn
    have hp : T.depth s ∈ Finset.range (h+1) := Finset.mem_range.mpr (Nat.lt_succ_of_le (hh s))
    exact (hn hp).elim

include hstep in

lemma pRootSum_upper_comparison (hp : 1 < e.val) (h : ℕ) (hh : ∀ s, T.depth s ≤ h) (v : ι → ℝ) :
    T.pRootSum e v ≤ 2 * (h+1 : ℝ) ^ (1 - 1/e.val) * e.agg Finset.univ v := by
  have hm := T.pMaximum_level_sum e hstep v (h+1)
  rw [T.level_empty h hh,e.agg_empty,add_zero] at hm
  have hroot : T.pRootSum e v ≤ 2 * T.pMaximum e v T.root := by
    unfold pRootSum pMaximum
    linarith [le_max_left (T.pfields e v T.root).1 (T.pfields e v T.root).2,
      le_max_right (T.pfields e v T.root).1 (T.pfields e v T.root).2]
  have hc := Real.HolderConjugate.conjExponent hp
  have ht := Real.inner_le_Lp_mul_Lq_of_nonneg (Finset.range (h+1)) hc
    (fun j hj => e.agg_nonneg (T.headLevel Finset.univ j) v)
    (fun j hj => (by norm_num : (0:ℝ)≤1))
  simp only [mul_one,Real.one_rpow,Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_one] at ht
  rw [T.sum_level_rpow e h hh v,← Real.rpow_mul (e.agg_nonneg _ _)] at ht
  have he : 1 / Real.conjExponent e.val = 1 - 1/e.val := by simpa only [one_div] using hc.one_sub_inv.symm
  rw [mul_one_div_cancel e.ne_zero,Real.rpow_one,he] at ht
  have hcast : ((h+1:ℕ):ℝ) = (h+1:ℝ) := by simp
  rw [hcast] at ht
  nlinarith

include hstep in

lemma pRootSum_level_lower (v : ι → ℝ) (j : ℕ) :
    e.agg (T.headLevel Finset.univ j) v ≤ T.pRootSum e v := by
  have hp := (T.pfields_upper e v).1.level_le_root T e hstep (fun s => (T.pfields_nonneg e v s).1) j
  have hq := (T.pfields_upper e v).2.level_le_root T e hstep (fun s => (T.pfields_nonneg e v s).2) j
  have heq : v = (fun s => (T.pfields e v s).1) + (fun s => -(T.pfields e v s).2) := by
    funext s
    exact (T.pfields_difference e v s).symm
  have hadd := e.agg_add_le (T.headLevel Finset.univ j) (fun s => (T.pfields e v s).1) (fun s => -(T.pfields e v s).2)
  simp only [ChildExponent.agg,abs_neg] at hadd
  calc
    e.agg (T.headLevel Finset.univ j) v = e.agg (T.headLevel Finset.univ j)
      ((fun s => (T.pfields e v s).1) + (fun s => -(T.pfields e v s).2)) := congrArg (e.agg _) heq
    _ ≤ (T.pfields e v T.root).1 + (T.pfields e v T.root).2 := hadd.trans (add_le_add hp hq)

include hstep in

lemma pRootSum_lower_comparison (h : ℕ) (hh : ∀ s, T.depth s ≤ h) (v : ι → ℝ) :
    e.agg Finset.univ v ≤ (h+1 : ℝ) ^ (1/e.val) * T.pRootSum e v := by
  have hn := T.pRootSum_nonneg e v
  apply (Real.rpow_le_rpow_iff (e.agg_nonneg _ _) (by positivity) e.pos).mp
  rw [Real.mul_rpow (by positivity) (T.pRootSum_nonneg e v),← Real.rpow_mul (by positivity : (0:ℝ)≤h+1),one_div_mul_cancel e.ne_zero,Real.rpow_one]
  rw [← T.sum_level_rpow e h hh v]
  calc
    _ ≤ ∑ j ∈ Finset.range (h+1), T.pRootSum e v ^ e.val := Finset.sum_le_sum fun j hj =>
      Real.rpow_le_rpow (e.agg_nonneg _ _) (T.pRootSum_level_lower e hstep v j) e.pos.le
    _ = _ := by simp

end FiniteRootedTree

open Filter Topology TopologicalSpace

open scoped ENNReal

namespace ChildExponent

instance (e : ChildExponent) : Fact (1 ≤ ENNReal.ofReal e.val) :=
  ⟨by simpa using ENNReal.ofReal_le_ofReal e.one_le⟩

end ChildExponent

namespace AggregationVector

open scoped ENNReal

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)
    (e : ChildExponent)

abbrev CoordinateLp (ι : Type uIndex) (e : ChildExponent) := ↥(lp (fun _ : ι => ℝ) (ENNReal.ofReal e.val))

def toLpLinear : AggregationVector T e →ₗ[ℝ] CoordinateLp ι e :=
  Finsupp.lsum ℝ (fun s => lp.lsingle (𝕜 := ℝ) (E := fun _ : ι => ℝ) (ENNReal.ofReal e.val) s)

lemma toLpLinear_norm_rpow (v : AggregationVector T e) :
    ‖toLpLinear T e v‖ ^ e.val = ∑ s ∈ (show ι →₀ ℝ from v).support, |v s| ^ e.val := by
  change ‖∑ s ∈ (show ι →₀ ℝ from v).support, lp.single _ s (v s)‖ ^ e.val = _
  simpa only [ENNReal.toReal_ofReal e.pos.le,Real.norm_eq_abs] using
    lp.norm_sum_single (E := fun _ : ι => ℝ) (p := ENNReal.ofReal e.val)
      (by simpa only [ENNReal.toReal_ofReal e.pos.le] using e.pos) (fun s => v s)
      (show ι →₀ ℝ from v).support

@[simp] lemma toLpLinear_single (s : ι) (a : ℝ) :
    toLpLinear T e (Finsupp.single s a) = lp.single (ENNReal.ofReal e.val) s a := by
  change ((Finsupp.lsum ℝ) (fun s : ι => lp.lsingle (𝕜 := ℝ) (E := fun _ : ι => ℝ) (ENNReal.ofReal e.val) s))
    (Finsupp.single s a) = _
  simp

lemma lp_comparisons (hp : 1 < e.val)
    (hstep : ∀ c, c ≠ T.root → T.depth c = T.depth (T.parent c) + 1)
    (h : ℕ) (hh : ∀ s, T.depth s ≤ h) (v : AggregationVector T e) :
    ‖v‖ ≤ (2*(h+1:ℝ)^(1-1/e.val))*‖toLpLinear T e v‖ ∧
      ‖toLpLinear T e v‖ ≤ (h+1:ℝ)^(1/e.val)*‖v‖ := by
  let w : ι →₀ ℝ := v
  let H := T.head w
  let U := T.restrict H (T.head_initial w)
  have hstepU : ∀ c, c ≠ U.root → U.depth c = U.depth (U.parent c) + 1 := by
    intro c hc; exact hstep c.1 (fun hh => hc (Subtype.ext hh))
  have hheightU : ∀ c, U.depth c ≤ h := fun c => hh c.1
  have hn : ‖v‖ = U.pRootSum e (fun c => w c.1) :=
    VariableTree.normSum_on_head T e w H (T.head_initial w) (T.support_subset_head w)
  have hl : e.agg (Finset.univ : Finset H) (fun c => w c.1) = ‖toLpLinear T e v‖ := by
    apply (Real.rpow_left_inj (e.agg_nonneg _ _) (norm_nonneg _) e.ne_zero).mp
    rw [e.agg_rpow,toLpLinear_norm_rpow]
    rw [← Finset.sum_subtype H (fun _ => Iff.rfl) (fun s => |w s| ^ e.val)]
    exact (Finset.sum_subset (T.support_subset_head w) (fun s hs hs' => by
      rw [Finsupp.notMem_support_iff.mp hs']; simp [Real.zero_rpow e.ne_zero])).symm
  have hup := U.pRootSum_upper_comparison e hstepU hp h hheightU (fun c => w c.1)
  have hlow := U.pRootSum_lower_comparison e hstepU h hheightU (fun c => w c.1)
  rw [hl,← hn] at hup hlow
  exact ⟨hup,hlow⟩

def toLp (hp : 1 < e.val)
    (hstep : ∀ c, c ≠ T.root → T.depth c = T.depth (T.parent c) + 1)
    (h : ℕ) (hh : ∀ s, T.depth s ≤ h) : AggregationVector T e →L[ℝ] CoordinateLp ι e :=
  (toLpLinear T e).mkContinuous ((h+1:ℝ)^(1/e.val))
    (fun v => (lp_comparisons T e hp hstep h hh v).2)

lemma toLp_dense (hp : 1 < e.val)
    (hstep : ∀ c, c ≠ T.root → T.depth c = T.depth (T.parent c) + 1)
    (h : ℕ) (hh : ∀ s, T.depth s ≤ h) : DenseRange (toLp T e hp hstep h hh) := by
  let V := (toLp T e hp hstep h hh).range.topologicalClosure
  have hv : V = ⊤ := by
    apply top_unique
    intro x hx
    exact (toLp T e hp hstep h hh).range.isClosed_topologicalClosure.mem_of_tendsto
      (lp.hasSum_single ENNReal.ofReal_ne_top x)
      (Filter.Eventually.of_forall fun S => V.sum_mem fun i hi =>
        (toLp T e hp hstep h hh).range.le_topologicalClosure ⟨Finsupp.single i (x i),toLpLinear_single T e i (x i)⟩)
  intro x
  have hm : x ∈ V := by rw [hv]; trivial
  exact hm

end AggregationVector

namespace AggregationSpace

open AggregationVector

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)
    (e : ChildExponent)

def lpEquiv (hp : 1 < e.val)
    (hstep : ∀ c, c ≠ T.root → T.depth c = T.depth (T.parent c) + 1)
    (h : ℕ) (hh : ∀ s, T.depth s ≤ h) : AggregationSpace T e ≃L[ℝ] CoordinateLp ι e :=
  completionEquivOfDense (AggregationVector.toLp T e hp hstep h hh)
    ⟨2*(h+1:ℝ)^(1-1/e.val),by positivity⟩
    (fun v => (AggregationVector.lp_comparisons T e hp hstep h hh v).1)
    (AggregationVector.toLp_dense T e hp hstep h hh)

end AggregationSpace

namespace Variable

open UniformSpace VariableExponent Filter Topology TopologicalSpace

def exponent (h : ℕ+) : ChildExponent := ⟨heightExponent h,(heightExponent_gt_one h).le⟩

abbrev Component (h : ℕ+) := AggregationSpace (componentTree h) (exponent h)

abbrev Xv := SquareSum.Space Component

abbrev Node := Σ h : ℕ+, ComponentNode h

lemma component_step (h : ℕ+) (c : ComponentNode h) (hc : c ≠ (componentTree h).root) :
    (componentTree h).depth c = (componentTree h).depth ((componentTree h).parent c) + 1 := by
  change c.1.length = c.1.dropLast.length+1
  rw [List.length_dropLast]
  have hp := List.length_pos_iff_ne_nil.mpr (show c.1 ≠ [] from fun he => hc (Subtype.ext he))
  omega

lemma component_height (h : ℕ+) (c : ComponentNode h) : (componentTree h).depth c ≤ h.val := c.2

def componentEquiv (h : ℕ+) :
    Component h ≃L[ℝ] AggregationVector.CoordinateLp (ComponentNode h) (exponent h) :=
  AggregationSpace.lpEquiv (componentTree h) (exponent h) (heightExponent_gt_one h)
    (component_step h) h.val (component_height h)

def componentCoordinate (h : ℕ+) (s : ComponentNode h) : Component h →L[ℝ] ℝ :=
  AggregationSpace.coordinate (componentTree h) (exponent h) s

def coordinate (s : Node) : Xv →L[ℝ] ℝ :=
  (componentCoordinate s.1 s.2).comp (lp.evalCLM ℝ Component 2 s.1)

def basis (s : Node) : Xv := lp.single 2 s.1
  ((AggregationVector.basisVector (componentTree s.1) (exponent s.1) s.2 : AggregationVector (componentTree s.1) (exponent s.1)) : Component s.1)

def FiniteTotalSupport (x : Xv) : Prop := ∃ S : Finset Node, ∀ s ∉ S, coordinate s x = 0

def projection (S : Finset Node) : Xv →L[ℝ] Xv := ∑ s ∈ S, (coordinate s).smulRight (basis s)

def AdmissibleHeads (x y : Xv) (A : ∀ h, Finset (ComponentNode h)) : Prop :=
  ∀ h, x h ≠ 0 → (componentTree h).Initial (A h) ∧
    (∀ s ∉ A h, componentCoordinate h s (x h) = 0) ∧
    (∀ s ∈ A h, componentCoordinate h s (y h) = 0)

def weakTailConstant : ℝ := cubicConstant/(2*Real.sqrt 2)

def theta (ε : ℝ) : ℝ := Real.sqrt (1-weakTailConstant*ε^3)

end Variable

structure RootSumCompletionStatement {ι : Type uIndex} [DecidableEq ι]
    (T : FiniteRootedTree ι) : Prop where
  complete : CompleteSpace (TreeSpace T)
  infinite_dimensional : ¬Module.Finite ℝ (TreeSpace T)
  coordinate_continuous : ∀ s, Continuous (TreeSpace.coordinate T s)
  coordinate_extends : ∀ s (v : TreeVector T), TreeSpace.coordinate T s (v : TreeSpace T) = v s
  fields_continuous : ∀ s, Continuous (TreeSpace.P T s) ∧ Continuous (TreeSpace.Q T s)
  fields_extend : ∀ s (v : TreeVector T),
    TreeSpace.P T s (v : TreeSpace T) = T.P v s ∧ TreeSpace.Q T s (v : TreeSpace T) = T.Q v s
  root_formula : ∀ x : TreeSpace T, ‖x‖ = TreeSpace.P T T.root x + TreeSpace.Q T T.root x
  projections : ∀ (H : Finset ι) (hH : T.Initial H),
    (∀ x : TreeSpace T, ‖TreeSpace.projection T H hH x‖ ≤ ‖x‖) ∧
    (∀ x : TreeSpace T, TreeSpace.projection T H hH (TreeSpace.projection T H hH x) = TreeSpace.projection T H hH x) ∧
    (∀ (s : ι) (x : TreeSpace T), TreeSpace.coordinate T s (TreeSpace.projection T H hH x) =
      if s ∈ H then TreeSpace.coordinate T s x else 0) ∧
    FiniteDimensional ℝ (TreeSpace.projection T H hH).range ∧
    IsClosed (TreeSpace.tail T H hH : Set (TreeSpace T)) ∧
    Module.Finite ℝ (TreeSpace T ⧸ TreeSpace.tail T H hH) ∧
    ∀ x ∈ TreeSpace.tail T H hH, ∀ ε : ℝ, 0 < ε →
      ∃ v : TreeVector T, TreeVector.projection T H hH v = 0 ∧ ‖(v : TreeSpace T)-x‖ < ε

structure ZeroRootCompletionStatement {ι : Type uIndex} [DecidableEq ι]
    (T : FiniteRootedTree ι) : Prop where
  complete : CompleteSpace (ZeroTreeSpace T)
  infinite_dimensional : ¬Module.Finite ℝ (ZeroTreeSpace T)
  coordinate_continuous : ∀ s, Continuous (ZeroTreeSpace.coordinate T s)
  coordinate_extends : ∀ s (v : ZeroTreeVector T),
    ZeroTreeSpace.coordinate T s (v : ZeroTreeSpace T) = ZeroTreeVector.toTree T v s
  fields_continuous : ∀ s, Continuous (ZeroTreeSpace.P T s) ∧ Continuous (ZeroTreeSpace.Q T s)
  fields_extend : ∀ s (v : ZeroTreeVector T),
    ZeroTreeSpace.P T s (v : ZeroTreeSpace T) = T.P (ZeroTreeVector.toTree T v) s ∧
    ZeroTreeSpace.Q T s (v : ZeroTreeSpace T) = T.Q (ZeroTreeVector.toTree T v) s
  root_fixed : ∀ x : ZeroTreeSpace T, ZeroTreeSpace.coordinate T T.root x = 0
  root_formula : ∀ x : ZeroTreeSpace T, ‖x‖ = ZeroTreeSpace.P T T.root x ∧ ‖x‖ = ZeroTreeSpace.Q T T.root x
  projections : ∀ (H : Finset ι) (hH : T.Initial H),
    (∀ x : ZeroTreeSpace T, ‖ZeroTreeSpace.projection T H hH x‖ ≤ ‖x‖) ∧
    (∀ x : ZeroTreeSpace T, ZeroTreeSpace.projection T H hH (ZeroTreeSpace.projection T H hH x) = ZeroTreeSpace.projection T H hH x) ∧
    (∀ (s : ι) (x : ZeroTreeSpace T), ZeroTreeSpace.coordinate T s (ZeroTreeSpace.projection T H hH x) =
      if s ∈ H then ZeroTreeSpace.coordinate T s x else 0) ∧
    FiniteDimensional ℝ (ZeroTreeSpace.projection T H hH).range ∧
    IsClosed (ZeroTreeSpace.tail T H hH : Set (ZeroTreeSpace T)) ∧
    Module.Finite ℝ (ZeroTreeSpace T ⧸ ZeroTreeSpace.tail T H hH) ∧
    ∀ x ∈ ZeroTreeSpace.tail T H hH, ∀ ε : ℝ, 0 < ε →
      ∃ v : ZeroTreeVector T, ZeroTreeVector.projection T H hH v = 0 ∧ ‖(v : ZeroTreeSpace T)-x‖ < ε

namespace Variable

open VariableExponent

def nu (h : ℕ+) (v : AggregationVector.CoordinateLp (ComponentNode h) (exponent h)) : ℝ :=
  AggregationSpace.P (componentTree h) (exponent h) (componentTree h).root ((componentEquiv h).symm v) +
  AggregationSpace.Q (componentTree h) (exponent h) (componentTree h).root ((componentEquiv h).symm v)

structure SourceNormStatement (h : ℕ+) : Prop where
  nonneg : ∀ v : AggregationVector.CoordinateLp (ComponentNode h) (exponent h), 0 ≤ nu h v
  definite : ∀ v : AggregationVector.CoordinateLp (ComponentNode h) (exponent h), nu h v = 0 ↔ v = 0
  triangle : ∀ v w : AggregationVector.CoordinateLp (ComponentNode h) (exponent h),
    nu h (v+w) ≤ nu h v + nu h w
  homogeneous : ∀ (a : ℝ) (v : AggregationVector.CoordinateLp (ComponentNode h) (exponent h)),
    nu h (a • v) = |a| * nu h v

def aggregateChildren (h : ℕ+) (s : ComponentNode h) (f : ComponentNode h → ℝ) : ℝ :=
  (∑' c, if c ≠ (componentTree h).root ∧ (componentTree h).parent c = s then
    f c ^ heightExponent h else 0) ^ (1/heightExponent h)

def lpPotentials (h : ℕ+) (v : AggregationVector.CoordinateLp (ComponentNode h) (exponent h))
    (s : ComponentNode h) : ℝ × ℝ :=
  (AggregationSpace.P (componentTree h) (exponent h) s ((componentEquiv h).symm v),
    AggregationSpace.Q (componentTree h) (exponent h) s ((componentEquiv h).symm v))

end Variable

end RecursivePotentials

end

end OAI


