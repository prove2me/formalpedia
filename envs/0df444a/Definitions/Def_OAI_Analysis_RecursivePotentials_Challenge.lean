-- Prove2me | Definitions.Def_OAI_Analysis_RecursivePotentials_Challenge
-- name    : OAI_Analysis_RecursivePotentials_Challenge
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T07:51:38.98984+00:00
-- url     : https://prove2.me/theorems/1839744c-2b74-4b29-9d40-315a11484b0a
-- title:
--   The eleven statements on Banach spaces of recursive tree potentials and their canonical constructions
-- statement:
--   This file states, as propositions, eleven conclusions about Banach spaces of vectors on trees normed by recursive potentials, bundles them into a single proposition, and supplies the canonical constructions that realize the abstract interfaces of the self-contained formulation of the main claim.
--
--   **Tree spaces.** A rooted tree $T$ on an index set $\iota$ has a root $r$, a parent map $\pi$ with $\pi(r)=r$ and a depth $d$ with $d(r)=0$ and $d(\pi(s))<d(s)$ for $s\neq r$; a finite set $H$ is initial if $r\in H$ and $\pi(H)\subseteq H$. For finitely supported $v$ the potentials are computed on the finite set formed by the root, the support and all ancestors, by $P_v(s)=\max(A,\,v(s)+B)$ and $Q_v(s)=\max(B,\,A-v(s))$, where $A$ and $B$ are the Euclidean norms of the values of $P_v$ and $Q_v$ at the children of $s$; they vanish elsewhere. $V_T$ is the space of finitely supported vectors with $\|v\|=P_v(r)+Q_v(r)$ and $X_T$ its completion; the coordinates $x_s$ and potentials $P_s(x)$, $Q_s(x)$ on $X_T$ are the continuous extensions of $v\mapsto v(s)$, $P_v(s)$, $Q_v(s)$; $\Pi_H$ is the continuous extension of restriction to $H$, and $\ker\Pi_H$ is the tail of $H$. The zero-root space $V^0_T=\{v\in V_T:v(r)=0\}$ carries the norm $P_v(r)$; its completion $X^0_T$ embeds into $X_T$, which defines its coordinates and potentials, and restriction to $H$ induces projections $\Pi^0_H$ and tails $\ker\Pi^0_H$.
--
--   The sequence tree $\Sigma$ has as nodes all finite sequences of natural numbers, root the empty sequence $\emptyset$, parent map deleting the last entry and depth equal to length. For $h\ge1$ the component tree $T_h$ is the subtree of sequences of length at most $h$. The joined tree $\mathcal{J}$ has a root $\ast$ and the nodes $(h,s)$ with $h\ge1$ and $s\in T_h$; the parent of $(h,\emptyset)$ is $\ast$, the parent of $(h,s)$ for nonempty $s$ is $(h,s')$ with $s'$ obtained by deleting the last entry, and the depth of $(h,s)$ is the length of $s$ plus one. Put $X_\Sigma=X_{T}$ for $T=\Sigma$, $X_J=X_{\mathcal{J}}$ and $X_0=X^0_{\mathcal{J}}$.
--
--   **Moduli.** For a real normed space $E$ and $t\in\mathbb{R}$, with $F$ ranging over the closed subspaces of finite codimension,
--   $$\bar\delta_E(t)=\inf_{\|x\|=1}\ \sup_F\ \inf\Bigl\{\frac{\|x+ty\|+\|x-ty\|}{2}-1:\ y\in F,\ \|y\|\ge1\Bigr\}.$$
--   An equivalent norm on $E$ is a seminorm $N$ with constants $0<a\le b$ such that $a\|x\|\le N(x)\le b\|x\|$; its modulus is $\delta_N(t)=\inf_{N(x)=1}\sup_F\inf\{N(x+ty)-1:\ y\in F,\ N(y)=1\}$, and $N$ is AUC if $\delta_N(t)>0$ for every $t>0$. A sequence $(y_j)$ is weakly null if $f(y_j)\to0$ for every continuous linear functional $f$, and $E$ is reflexive if the canonical map $E\to E^{**}$ is surjective.
--
--   **The variable-exponent space.** For $h\ge1$ let $p_h=1+\frac1h$, and let $Y_h$ be the completion of the finitely supported vectors on $T_h$ under $P^{(h)}_v(\emptyset)+Q^{(h)}_v(\emptyset)$, where $P^{(h)},Q^{(h)}$ are defined like $P,Q$ but with the children aggregated in $\ell^{p_h}$ instead of $\ell^2$. The potentials $P_s,Q_s$ on $Y_h$ are the continuous extensions of $v\mapsto P^{(h)}_v(s),Q^{(h)}_v(s)$. The identity on coordinates extends to an isomorphism $Y_h\cong\ell^{p_h}(T_h)$; for $v\in\ell^{p_h}(T_h)$ let $\nu_h(v)=P_\emptyset(u)+Q_\emptyset(u)$, where $u\in Y_h$ corresponds to $v$. Let $X_v=\bigl(\bigoplus_{h\ge1}Y_h\bigr)_{\ell^2}$; its nodes are the pairs $(h,s)$, $x_{(h,s)}$ is the $s$-coordinate of the $h$-th component, $b_{(h,s)}$ is the unit vector at $s$ placed in the $h$-th component, and for a finite set $S$ of nodes $\mathcal{P}_Sx=\sum_{\sigma\in S}x_\sigma\,b_\sigma$. A vector has finite total support if its coordinates vanish outside a finite set of nodes. A family $A=(A_h)_{h\ge1}$ of finite sets $A_h\subseteq T_h$ is admissible for $(x,y)$ if for every $h$ with $x_h\neq0$ the set $A_h$ is initial in $T_h$, the coordinates of $x_h$ vanish outside $A_h$, and those of $y_h$ vanish on $A_h$. Finally, with $\mathrm{e}$ Euler's number, $\kappa_3=(6\mathrm{e})^{-3}$, $\kappa_6=2\mathrm{e}^{-(\mathrm{e}-1)}4^{-6}$, $\theta(\varepsilon)=\sqrt{1-\kappa_3\varepsilon^3/(2\sqrt2)}$, and
--   $$\Gamma(M,\beta)=\frac{\beta\lambda}{8}\,\mathrm{e}^{-K},\qquad\lambda=\frac{\beta^2}{2M^2},\quad c=\frac{\beta\sqrt{\lambda}}{8},\quad K=\frac{4(2+\sqrt6)\bigl(1+\log(M/c)\bigr)}{\lambda}.$$
--
--   **The statements.**
--
--   1. *Main statement.* (a) For $0<t<1$, $t^3/128\le\bar\delta_{X_\Sigma}(t)$ and $t^3/128\le\bar\delta_{X_J}(t)$. (b) For every finite initial set $H$ of $\mathcal{J}$, every $x\in X_0$ with $x_s=0$ for $s\notin H$, and every $z\in X_0$ with $z\neq0$ and $z_s=0$ for $s\in H$,
--   $$\frac{\|x+z\|+\|x-z\|}{2}\ge\|x\|+\frac{\|z\|^3}{8(2\|x\|+\|z\|)^2}.$$
--   (c) No equivalent norm on $X_\Sigma$, on $X_0$ or on $X_J$ is AUC.
--   2. *Completions.* $X_\Sigma$ and $X_J$ have the root-sum completion properties, $X_0$ has the zero-root completion properties, and $X_0$ and $X_J$ are reflexive. The root-sum completion properties of $X_T$ are: $X_T$ is complete and infinite-dimensional; each coordinate $x\mapsto x_s$ is continuous and equals $v(s)$ on $V_T$; each $P_s$ and $Q_s$ is continuous and equals $P_v(s)$, $Q_v(s)$ on $V_T$; $\|x\|=P_r(x)+Q_r(x)$; and for every finite initial $H$, $\Pi_H$ is norm-nonincreasing and idempotent, $(\Pi_Hx)_s$ equals $x_s$ for $s\in H$ and $0$ otherwise, $\Pi_H$ has finite-dimensional range, $\ker\Pi_H$ is closed with finite-dimensional quotient, and every $x\in\ker\Pi_H$ lies within any $\varepsilon>0$ of some $v\in V_T$ vanishing on $H$. The zero-root completion properties of $X^0_T$ are the same statements for $V^0_T$, $X^0_T$ and $\Pi^0_H$, except that the norm formula is replaced by $\|x\|=P_r(x)$ and $\|x\|=Q_r(x)$, together with $x_r=0$, for all $x\in X^0_T$.
--   3. *Positivity at all radii.* $\bar\delta_{X_\Sigma}(t)>0$ for every $t>0$.
--   4. *Separated families in $X_J$.* For every $\varepsilon>0$ there is $\eta$ with $0<\eta<1$, equal to $\min\bigl(\tfrac12,\Gamma(2,\varepsilon/16)\bigr)$ when $\varepsilon\le2$, such that: if $x\in X_J$ and $z_n\in X_J$ ($n\in\mathbb{N}$) satisfy $\|x+z_n\|\le1$ and $\|x-z_n\|\le1$ for all $n$ and $\|z_i-z_j\|\ge\varepsilon$ for $i\neq j$, then $\|x\|\le1-\eta$.
--   5. *Structure of $X_v$.* For every $h\ge1$, $Y_h$ is complete and reflexive with separable dual, and $\nu_h$ is a norm on $\ell^{p_h}(T_h)$ (nonnegative, vanishing only at $0$, subadditive and absolutely homogeneous) with
--   $$(h+1)^{-1/p_h}\|v\|_{p_h}\le\nu_h(v)\le2(h+1)^{1-1/p_h}\|v\|_{p_h}.$$
--   Moreover $X_v$ is complete and reflexive with separable dual, the vectors of finite total support are dense, and for every finite set $S$ of nodes, $\mathcal{P}_S$ is continuous, idempotent and of finite rank, with $(\mathcal{P}_Sx)_\sigma=x_\sigma$ for $\sigma\in S$ and $0$ otherwise.
--   6. *Exact $\ell^p$ model.* Let $h\ge1$, $v\in\ell^{p_h}(T_h)$, and let $f=(f_1,f_2)$ assign to each node $s$ of $T_h$ a pair of reals such that, for all $s$,
--   $$f(s)=\Bigl(\max\bigl(\alpha_s(f_1),\,v_s+\alpha_s(f_2)\bigr),\ \max\bigl(\alpha_s(f_2),\,\alpha_s(f_1)-v_s\bigr)\Bigr),\qquad\alpha_s(g)=\Bigl(\sum_cg(c)^{p_h}\Bigr)^{1/p_h},$$
--   the sum running over the children $c$ of $s$. Then $f(s)=\bigl(P_s(u),Q_s(u)\bigr)$ for all $s$, where $u\in Y_h$ corresponds to $v$, and $\nu_h(v)=f_1(\emptyset)+f_2(\emptyset)$.
--   7. *Vanishing one-sided modulus.* For every equivalent norm $N$ on $X_v$ with constants $a\le b$, $\delta_N(a/b)=0$.
--   8. *No AUC renorming.* No equivalent norm on $X_v$ is AUC.
--   9. *Sixth-power stability.* If $x,y\in X_v$, $x$ has finite total support and some family $A$ is admissible for $(x,y)$, then
--   $$\frac{\kappa_6\,\|y\|^6}{(\|x+y\|^2+\|x-y\|^2)^2}\le\|x+y\|^2+\|x-y\|^2-2\|x\|^2.$$
--   10. *Cubic stability.* Under the same hypotheses, if $R>0$, $\|x+y\|\le R$ and $\|x-y\|\le R$, then $\|x\|^2+\frac{\kappa_3}{2\sqrt2\,R}\|y\|^3\le R^2$.
--   11. *Weak tails.* If $x\in X_v$, $0<\varepsilon\le1$, and $(y_j)_{j\in\mathbb{N}}$ is weakly null with $\|y_j\|\ge\varepsilon$, $\|x+y_j\|\le1$ and $\|x-y_j\|\le1$ for all $j$, then $\|x\|\le\theta(\varepsilon)$ and $\theta(\varepsilon)<1$.
--
--   The proposition *OriginalResults* is the conjunction of statements 1 to 11. The file also provides canonical instances of the five construction interfaces of the self-contained formulation (heads of vectors, root-sum tree norms, zero-root norms, aggregation norms, and the comparison of aggregation norms with $\ell^e$ norms), built from the concrete objects above.
--
--   These are the statements proved in the rest of the development. In the module, the self-contained main claim, which asserts that constructions satisfying the five interfaces exist for which all eleven statements hold, is shown to be equivalent to OriginalResults, with the canonical instances as witnesses.
--
--   **Formalization Note** The statements are `rec_mainOriginalStatement`, `rec_completionOriginalStatement` (via the structures `RootSumCompletionStatement` and `ZeroRootCompletionStatement`), `stop_all_radiiOriginalStatement`, `XJoined_separated_familiesOriginalStatement` and, in `Variable`, `spaceOriginalStatement`, `lp_model_exactOriginalStatement`, `one_sided_modulus_zeroOriginalStatement`, `no_equivalent_AUCOriginalStatement`, `sixth_stabilityOriginalStatement`, `cubic_stabilityOriginalStatement`, `weak_tailOriginalStatement`; their conjunction is `OriginalResults`. The local instances `canonicalHeads`, `canonicalTree`, `canonicalZero`, `canonicalAggregation` and `canonicalLp` instantiate, in universe 0, the classes `Heads`, `TreeVector.Construction`, `ZeroTreeVector.Construction`, `AggregationVector.Construction` and `AggregationVector.LpConstruction`, using that the head of a vector is initial, that the root sum is a norm dominating every coordinate and not increased by restriction to initial sets, that the zero-root norm is a norm equal to half the root sum, that the aggregation norm is a norm dominating every coordinate, and that the $\ell^e$ comparison bounds hold and finitely supported vectors are dense in $\ell^e$. The moduli use `sInf`/`sSup` on $\mathbb{R}$ (value $0$ on empty or unbounded sets); in statement 6 the children sum is a `tsum` (value $0$ for non-summable families) of real powers `f c ^ heightExponent h`; $\Gamma$ is `logarithmicGamma`, $\kappa_3$ is `cubicConstant`, $\kappa_6$ is `sixthConstant` and $\theta$ is `theta`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/RecursivePotentials/Challenge.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/RecursivePotentials/Challenge.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the RecursivePotentials mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_RecursivePotentials
import Definitions.Def_OAI_Analysis_RecursivePotentials_Model
import Definitions.Def_OAI_Analysis_RecursivePotentials_TreeGeometry
import Definitions.Def_OAI_Analysis_RecursivePotentials_ZeroRootGeometry
import Definitions.Def_OAI_Analysis_RecursivePotentials_EquivalentNorms
import Definitions.Def_OAI_Analysis_RecursivePotentials_JoinedGeometry
import Definitions.Def_OAI_Analysis_RecursivePotentials_VariableEstimates
import Definitions.Def_OAI_Analysis_RecursivePotentials_VariableCompletion
import Definitions.Def_OAI_Analysis_RecursivePotentials_VariableLp
import Definitions.Def_OAI_Analysis_RecursivePotentials_VariableStability
import Definitions.Def_OAI_Analysis_RecursivePotentials_Main

namespace OAI

noncomputable section

/-! Proved construction certificates and a statement-preservation check for the
self-contained Comparator challenge. All eleven original conclusions are retained. -/

namespace RecursivePotentials

open VariableExponent Filter Topology TopologicalSpace UniformSpace

def rec_mainOriginalStatement : Prop := (∀ t : ℝ, 0 < t → t < 1 → t^3/128 ≤ averagedModulus XSigma t ∧ t^3/128 ≤ averagedModulus XJoined t) ∧
    (∀ (H : Finset JoinedNode), joinedTree.Initial H → ∀ x : XZero,
      (∀ s ∉ H, ZeroTreeSpace.coordinate joinedTree s x = 0) → ∀ z : XZero,
      (∀ s ∈ H, ZeroTreeSpace.coordinate joinedTree s z = 0) → z ≠ 0 →
      (‖x+z‖+‖x-z‖)/2 ≥ ‖x‖+‖z‖^3/(8*(2*‖x‖+‖z‖)^2)) ∧
    (∀ A : EquivalentNorm XSigma, ¬A.AUC) ∧
    (∀ A : EquivalentNorm XZero, ¬A.AUC) ∧
    (∀ A : EquivalentNorm XJoined, ¬A.AUC)

def rec_completionOriginalStatement : Prop := RootSumCompletionStatement sequenceTree ∧
    ZeroRootCompletionStatement joinedTree ∧ RootSumCompletionStatement joinedTree ∧
    IsReflexive XZero ∧ IsReflexive XJoined

def stop_all_radiiOriginalStatement : Prop := ∀ {t : ℝ} (_ht : 0 < t),
  0 < averagedModulus XSigma t

def XJoined_separated_familiesOriginalStatement : Prop := ∀ {ε : ℝ} (_hε : 0 < ε),
  ∃ η : ℝ, 0 < η ∧ η < 1 ∧
      (ε ≤ 2 → η = min (1/2) (logarithmicGamma 2 (ε/16))) ∧
      ∀ (x : XJoined) (z : ℕ → XJoined),
        (∀ n, ‖x+z n‖ ≤ 1) → (∀ n, ‖x-z n‖ ≤ 1) →
        (∀ i j, i ≠ j → ε ≤ ‖z i-z j‖) → ‖x‖ ≤ 1-η

namespace Variable

def spaceOriginalStatement : Prop := (∀ h : ℕ+, CompleteSpace (Component h) ∧ IsReflexive (Component h) ∧
      SeparableSpace (Component h →L[ℝ] ℝ) ∧ SourceNormStatement h ∧
      ∀ v : AggregationVector.CoordinateLp (ComponentNode h) (exponent h),
        (h.val+1:ℝ)^(-1/heightExponent h)*‖v‖ ≤ nu h v ∧
        nu h v ≤ 2*(h.val+1:ℝ)^(1-1/heightExponent h)*‖v‖) ∧
    CompleteSpace Xv ∧ IsReflexive Xv ∧ SeparableSpace (Xv →L[ℝ] ℝ) ∧
    Dense {x : Xv | FiniteTotalSupport x} ∧
    ∀ S : Finset Node, Continuous (projection S) ∧ FiniteDimensional ℝ (projection S).range ∧
      (∀ x : Xv, projection S (projection S x) = projection S x) ∧
      ∀ (s : Node) (x : Xv), coordinate s (projection S x) = if s ∈ S then coordinate s x else 0

def lp_model_exactOriginalStatement : Prop := ∀ (h : ℕ+)
    (v : AggregationVector.CoordinateLp (ComponentNode h) (exponent h))
    (f : ComponentNode h → ℝ × ℝ)
    (_hf : ∀ s, f s = leastPair (v s)
      (aggregateChildren h s (fun c => (f c).1))
      (aggregateChildren h s (fun c => (f c).2))),
  f = lpPotentials h v ∧ nu h v = (f (componentTree h).root).1+(f (componentTree h).root).2

def one_sided_modulus_zeroOriginalStatement : Prop := ∀ (A : EquivalentNorm Xv),
  A.modulus (A.lower/A.upper) = 0

def no_equivalent_AUCOriginalStatement : Prop := ∀ (A : EquivalentNorm Xv),
  ¬A.AUC

def sixth_stabilityOriginalStatement : Prop := ∀ (x y : Xv) (_hx : FiniteTotalSupport x) (A : ∀ h, Finset (ComponentNode h))
    (_hA : AdmissibleHeads x y A),
  sixthConstant*‖y‖^6/(‖x+y‖^2+‖x-y‖^2)^2 ≤ ‖x+y‖^2+‖x-y‖^2-2*‖x‖^2

def cubic_stabilityOriginalStatement : Prop := ∀ (x y : Xv) (_hx : FiniteTotalSupport x) (A : ∀ h, Finset (ComponentNode h))
    (_hA : AdmissibleHeads x y A) {R : ℝ} (_hR : 0 < R) (_hp : ‖x+y‖ ≤ R) (_hm : ‖x-y‖ ≤ R),
  ‖x‖^2+cubicConstant/(2*Real.sqrt 2*R)*‖y‖^3 ≤ R^2

def weak_tailOriginalStatement : Prop := ∀ (x : Xv) {ε : ℝ} (_hε : 0 < ε) (_hε1 : ε ≤ 1)
    (y : ℕ → Xv) (_hy : WeaklyNull y) (_hyε : ∀ j, ε ≤ ‖y j‖)
    (_hp : ∀ j, ‖x+y j‖ ≤ 1) (_hm : ∀ j, ‖x-y j‖ ≤ 1),
  ‖x‖ ≤ theta ε ∧ theta ε < 1

end Variable

def OriginalResults : Prop :=
  rec_mainOriginalStatement ∧
  rec_completionOriginalStatement ∧
  stop_all_radiiOriginalStatement ∧
  XJoined_separated_familiesOriginalStatement ∧
  Variable.spaceOriginalStatement ∧
  Variable.lp_model_exactOriginalStatement ∧
  Variable.one_sided_modulus_zeroOriginalStatement ∧
  Variable.no_equivalent_AUCOriginalStatement ∧
  Variable.sixth_stabilityOriginalStatement ∧
  Variable.cubic_stabilityOriginalStatement ∧
  Variable.weak_tailOriginalStatement

end RecursivePotentials

namespace ComparatorModel.RecursivePotentials

local instance canonicalHeads : FiniteRootedTree.Heads.{0} where
  initial := by intro ι _ T v; exact _root_.OAI.RecursivePotentials.FiniteRootedTree.head_initial T v

local instance canonicalTree : TreeVector.Construction.{0} where
  core := _root_.OAI.RecursivePotentials.TreeVector.normCore
  coordinate_bound := _root_.OAI.RecursivePotentials.FiniteRootedTree.abs_coordinate_le_normSum
  projection_bound := _root_.OAI.RecursivePotentials.FiniteRootedTree.projectHead_bound

local instance canonicalZero : ZeroTreeVector.Construction.{0} where
  core := _root_.OAI.RecursivePotentials.ZeroTreeVector.normCore
  half := _root_.OAI.RecursivePotentials.ZeroTreeVector.norm_half

local instance canonicalAggregation : AggregationVector.Construction.{0} where
  core := _root_.OAI.RecursivePotentials.AggregationVector.normCore
  coordinate_bound := _root_.OAI.RecursivePotentials.VariableTree.abs_coordinate_le_normSum

local instance canonicalLp : AggregationVector.LpConstruction.{0} where
  bounds := _root_.OAI.RecursivePotentials.AggregationVector.lp_comparisons
  dense := by
    intro ι _ T e
    let f := AggregationVector.toLpLinear T e
    let V := f.range.topologicalClosure
    have hv : V = ⊤ := by
      apply top_unique
      intro x _
      exact f.range.isClosed_topologicalClosure.mem_of_tendsto
        (lp.hasSum_single ENNReal.ofReal_ne_top x)
        (Filter.Eventually.of_forall fun S => V.sum_mem fun i hi =>
          f.range.le_topologicalClosure ⟨Finsupp.single i (x i), by
            change ((Finsupp.lsum ℝ) (fun s : ι => lp.lsingle (𝕜 := ℝ)
              (E := fun _ : ι => ℝ) (ENNReal.ofReal e.val) s)) (Finsupp.single i (x i)) = _
            simp⟩)
    intro x
    have hm : x ∈ V := by rw [hv]; trivial
    exact hm

-- Compare the finite-rank projections pointwise, so the statement comparison does not
-- repeatedly unfold the completion and operator-space instances.
end ComparatorModel.RecursivePotentials

end

end OAI


