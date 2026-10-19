-- Prove2me | Definitions.Def_OAI_Analysis_RecursivePotentials_JoinedGeometry
-- name    : OAI_Analysis_RecursivePotentials_JoinedGeometry
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T07:38:37.770862+00:00
-- url     : https://prove2.me/theorems/f7220b2b-8800-4c9e-bced-1482f0b3f748
-- title:
--   Hilbert models of bounded-height tree spaces and $\ell^2$-sum splittings of the joined tree spaces
-- statement:
--   This file constructs explicit isomorphic models of the tree spaces of the construction: a tree space of bounded height is isomorphic to a Hilbert space $\ell^2(I)$, and the two spaces attached to the joined tree split as $\ell^2$-sums of component tree spaces.
--
--   **Setting.** A rooted tree $T$ on an index set $I$ (possibly infinite) consists of a root $r\in I$, a parent map $\pi:I\to I$ with $\pi(r)=r$, and a depth $d:I\to\mathbb N$ with $d(r)=0$ and $d(\pi(s))<d(s)$ for $s\neq r$; the children of $s$ are the nodes $c\neq r$ with $\pi(c)=s$. For a finitely supported $v:I\to\mathbb R$ the potentials $(P_v,Q_v)$ form the least pair of nonnegative functions on $I$ with $P_v-Q_v=v$ such that, for every node $s$ and every finite set $S$ of children of $s$,
--
--   $$
--   \sum_{c\in S}P_v(c)^2\le P_v(s)^2,\qquad \sum_{c\in S}Q_v(c)^2\le Q_v(s)^2 .
--   $$
--
--   On the ancestor closure of the support of $v$ they are computed from the leaves upward by $P_v(s)=\max(a_s,\,v(s)+b_s)$ and $Q_v(s)=\max(b_s,\,-v(s)+a_s)$, where $a_s$ and $b_s$ are the Euclidean norms of the values of $P_v$ and $Q_v$ at the children of $s$; off that closure they vanish. The tree norm is $\|v\|_T=P_v(r)+Q_v(r)$ and the tree space $X_T$ is the completion of the finitely supported vectors in this norm. The root-zero space of $T$ is the completion of the finitely supported $v$ with $v(r)=0$ under $\|v\|_0=P_v(r)$, which equals $\tfrac12\|v\|_T$.
--
--   For $h\in\mathbb N_{+}=\{1,2,\dots\}$ the component tree $T_h$ has as nodes the finite sequences of natural numbers of length at most $h$, the empty sequence $\varnothing$ as root, the parent map that deletes the last entry, and depth equal to length. The joined tree $J$ has a new root $\ast$ and the nodes $(h,s)$ with $h\in\mathbb N_{+}$ and $s$ a node of $T_h$; the parent of $(h,\varnothing)$ is $\ast$, the parent of $(h,s)$ with $s\neq\varnothing$ is $(h,\pi_{T_h}(s))$, and $(h,s)$ has depth $|s|+1$. Write $X_J$ for the tree space of $J$ and $X_0$ for its root-zero space. For real normed spaces $(E_i)_{i\in\Lambda}$, $\big(\bigoplus_i E_i\big)_{\ell^2}$ is the space of families $x=(x_i)$ with $\|x\|=\big(\sum_i\|x_i\|^2\big)^{1/2}<\infty$, and $\iota_i:E_i\to\big(\bigoplus_i E_i\big)_{\ell^2}$ places a vector in coordinate $i$.
--
--   1. **Descendant energy.** For a rooted tree on a finite index set and $v:I\to\mathbb R$, the descendant energy is defined recursively by $\mathcal E_v(s)=v(s)^2+\sum_{c\text{ child of }s}\mathcal E_v(c)$, i.e. the sum of $v^2$ over the subtree below $s$ (including $s$); thus $\mathcal E_v(r)=\sum_{s\in I}v(s)^2$. If $d(s)\le h$ for all $s$, the file shows $\max(P_v(s),Q_v(s))^2\le(h+1-d(s))\,\mathcal E_v(s)$, and also that every function $p:I\to\mathbb R$ with $\sum_{c\text{ child of }s}p(c)^2\le p(s)^2$ for all $s$ satisfies $\sum_s p(s)^2\le(h+1)\,p(r)^2$; together these give
--   $$
--   \max(P_v(r),Q_v(r))^2\le(h+1)\sum_{s}v(s)^2,\qquad \sum_{s}v(s)^2\le4(h+1)\max(P_v(r),Q_v(r))^2 .
--   $$
--
--   2. **Functionals on an $\ell^2$-sum.** For a continuous linear functional $f$ on $E=\big(\bigoplus_i E_i\big)_{\ell^2}$, its restriction to the $i$-th summand is $f_i=f\circ\iota_i\in E_i^{*}$. The family $(f_i)_i$ is an element of $\big(\bigoplus_i E_i^{*}\big)_{\ell^2}$, since $\sum_{i\in S}\|f_i\|^2\le(2\|f\|)^2$ for every finite $S$, and the canonical pairing recovers $f$:
--   $$
--   \sum_i f_i(x_i)=f(x)\qquad\text{for all }x\in E .
--   $$
--   So every functional on an $\ell^2$-sum is represented by an $\ell^2$-family of functionals on the summands. The file also shows that a closed subspace of $E$ containing all vectors $\iota_i(y)$ is all of $E$, so a bounded linear map whose range contains these vectors has dense range.
--
--   3. **Hilbert model of a bounded-height tree space.** Let $T$ be a rooted tree on $I$ and $h\in\mathbb N$ with $d(s)\le h$ for all $s$. The coordinate map $\Theta_T v=\sum_s v(s)\,e_s$ from finitely supported vectors into $\ell^2(I)$ satisfies
--   $$
--   \|v\|_T\le2\sqrt{h+1}\,\|\Theta_Tv\|_{\ell^2},\qquad \|\Theta_Tv\|_{\ell^2}\le2\sqrt{h+1}\,\|v\|_T,
--   $$
--   and has dense range; its continuous extension is an isomorphism (a linear homeomorphism) $X_T\cong\ell^2(I)$.
--
--   4. **Components of the joined tree.** The component spaces are $X_{T_h}$, $h\in\mathbb N_{+}$, and the outer space is $\mathcal O=\big(\bigoplus_{h\in\mathbb N_{+}}X_{T_h}\big)_{\ell^2}$. The embeddings $s\mapsto(h,s)$ of the nodes of $T_h$ into $J$, and $h\mapsto(h,\varnothing)$ onto the children of $\ast$, are injective and respect parents.
--
--   5. **Component parts.** For a finitely supported $v$ on $J$ its $h$-th part is the vector $v^{(h)}(s)=v(h,s)$ on $T_h$. The parts satisfy $P^{T_h}_{v^{(h)}}(s)\le P^J_v(h,s)$ and $Q^{T_h}_{v^{(h)}}(s)\le Q^J_v(h,s)$ and $\sum_h\|v^{(h)}\|_{T_h}^2\le\|v\|_J^2$, so $\Phi(v)=(v^{(h)})_h$ defines a continuous linear map into $\mathcal O$ with $\|\Phi(v)\|\le\|v\|_J$.
--
--   6. **Glued competitor potentials.** For $\rho\in\mathbb R$ and functions $f_h$ on the nodes of $T_h$, the glued function on $J$ takes the value $\rho$ at $\ast$ and $f_h(s)$ at $(h,s)$. Gluing the root values $\|\Phi(v)\|+\max(v(\ast),0)$, resp. $\|\Phi(v)\|+\max(-v(\ast),0)$, with the component potentials $P^{T_h}_{v^{(h)}}$, resp. $Q^{T_h}_{v^{(h)}}$, gives an admissible pair $(\tilde P_v,\tilde Q_v)$ for $v$, hence $P^J_v\le\tilde P_v$, $Q^J_v\le\tilde Q_v$ and
--   $$
--   \|v\|_J\le|v(\ast)|+2\,\|\Phi(v)\| .
--   $$
--
--   7. **Insertions.** A finitely supported $w$ on $T_h$ is inserted into $J$ as the vector with value $w(s)$ at $(h,s)$ and $0$ elsewhere (in particular $0$ at $\ast$, so it is also a root-zero vector); its parts are $w$ in position $h$ and $0$ elsewhere. The root vector $a\,\delta_\ast$ ($a\in\mathbb R$) has all parts $0$.
--
--   8. **Splitting of $X_J$.** The map $\Sigma(v)=(v(\ast),\Phi(v))$ into $\mathbb R\times\mathcal O$, normed by $\|(a,y)\|=\max(|a|,\|y\|)$, is continuous linear with $\|v\|_J\le3\,\|\Sigma(v)\|$ and dense range; its continuous extension is an isomorphism $X_J\cong\mathbb R\times\mathcal O$.
--
--   9. **Splitting of $X_0$.** The restriction $\Phi_0$ of $\Phi$ to root-zero vectors satisfies $\|v\|_0\le\|\Phi_0(v)\|$ and has dense range; its continuous extension is an isomorphism $X_0\cong\mathcal O$.
--
--   By items 3 and 4 every component $X_{T_h}$ is isomorphic to a Hilbert space (with constant $2\sqrt{h+1}$, which is not uniform in $h$), so items 8 and 9 present $X_J$ and $X_0$ as $\ell^2$-sums of Hilbertian spaces, up to one extra real coordinate for $X_J$. Together with the description of the dual of an $\ell^2$-sum in item 2, these models are what the construction uses to prove that $X_0$ and $X_J$ are reflexive.
--
--   **Formalization Note** Rooted trees are the structure `FiniteRootedTree` (finite depth of each node; the index type may be infinite), and $X_T$ is `TreeSpace T`, the `UniformSpace.Completion` of `TreeVector T`; $X_J$ and $X_0$ are `XJoined` and `XZero`. $\ell^2$-sums are `SquareSum.Space E`, i.e. Mathlib's `lp E 2`, and the product $\mathbb R\times\mathcal O$ carries the max norm. All isomorphisms are produced by `completionEquivOfDense`, which turns a bounded linear map $f$ into a complete space with $\|x\|\le K\|f(x)\|$ and dense range into a continuous linear equivalence on the completion. Lean names: `descEnergy`; `SquareSum.restrictAt`, `SquareSum.restrict` (with `pairing_restrict`, `closedSubmodule_eq_top`, `denseRange_of_single`); `TreeVector.toSquare` and `TreeSpace.hilbertEquiv`, both taking $h$ and the depth bound as arguments; `Joined.Component`, `Joined.Outer`, `Joined.embed`, `Joined.rootEmbed`, `Joined.partLinear`, `Joined.components` / `componentsLinear` / `componentsMap`, `Joined.field`, `Joined.liftP`, `Joined.liftQ`, `Joined.put`, `Joined.rootVector`, `Joined.zeroPut`, `Joined.splitting`, `Joined.freeEquiv`, `Joined.zeroComponents`, `Joined.zeroEquiv`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/RecursivePotentials/JoinedGeometry.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/RecursivePotentials/JoinedGeometry.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the RecursivePotentials mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_RecursivePotentials
import Definitions.Def_OAI_Analysis_RecursivePotentials_Model
import Definitions.Def_OAI_Analysis_RecursivePotentials_TreeGeometry
import Definitions.Def_OAI_Analysis_RecursivePotentials_ZeroRootGeometry
import Definitions.Def_OAI_Analysis_RecursivePotentials_EquivalentNorms

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

universe uIndex uSpace uOther uDomain uTarget uFiber

open scoped BigOperators

namespace RecursivePotentials

open Filter Topology

namespace FiniteRootedTree

variable {ι : Type uIndex} [indexFinite : Fintype ι] [indexDecidable : DecidableEq ι]
    (T : FiniteRootedTree ι)

noncomputable def descEnergy (v : ι → ℝ) (s : ι) : ℝ :=
  v s ^ 2 + ∑ c : {c // c ∈ T.children s}, descEnergy v c.1
termination_by T.maxDepth - T.depth s
decreasing_by exact T.child_measure c.2

lemma descEnergy_eq (v : ι → ℝ) (s : ι) :
    T.descEnergy v s = v s ^ 2 + ∑ c ∈ T.children s, T.descEnergy v c := by
  rw [descEnergy, ← Finset.sum_subtype (T.children s) (fun _ => Iff.rfl) (T.descEnergy v)]

lemma descEnergy_nonneg (v : ι → ℝ) (s : ι) : 0 ≤ T.descEnergy v s := by
  rw [T.descEnergy_eq]
  exact add_nonneg (sq_nonneg _) (Finset.sum_nonneg fun c hc => descEnergy_nonneg v c)
termination_by T.maxDepth - T.depth s
decreasing_by exact T.child_measure hc

lemma descEnergy_root (v : ι → ℝ) : T.descEnergy v T.root = ∑ s, v s ^ 2 := by
  have he : (∑ s, T.descEnergy v s) = ∑ s, (v s ^ 2 + ∑ c ∈ T.children s, T.descEnergy v c) :=
    Finset.sum_congr rfl (fun s _ => T.descEnergy_eq v s)
  rw [Finset.sum_add_distrib, T.sum_children, Finset.sum_erase_eq_sub (Finset.mem_univ T.root)] at he
  linarith

lemma max_fields_le (v : ι → ℝ) (s : ι) :
    max (T.fields v s).1 (T.fields v s).2 ≤
      |v s| + Real.sqrt (∑ c ∈ T.children s, (max (T.fields v c).1 (T.fields v c).2) ^ 2) := by
  have hp : Real.sqrt (∑ c ∈ T.children s, (T.fields v c).1 ^ 2) ≤
      Real.sqrt (∑ c ∈ T.children s, (max (T.fields v c).1 (T.fields v c).2) ^ 2) := by
    apply Real.sqrt_le_sqrt
    exact Finset.sum_le_sum fun c hc => pow_le_pow_left₀ (T.fields_nonneg v c).1 (le_max_left _ _) _
  have hq : Real.sqrt (∑ c ∈ T.children s, (T.fields v c).2 ^ 2) ≤
      Real.sqrt (∑ c ∈ T.children s, (max (T.fields v c).1 (T.fields v c).2) ^ 2) := by
    apply Real.sqrt_le_sqrt
    exact Finset.sum_le_sum fun c hc => pow_le_pow_left₀ (T.fields_nonneg v c).2 (le_max_right _ _) _
  rw [T.fields_eq v s]
  simp only [leastPair, max_le_iff]
  constructor <;> constructor
  · linarith [abs_nonneg (v s)]
  · linarith [le_abs_self (v s)]
  · linarith [abs_nonneg (v s)]
  · linarith [neg_le_abs (v s)]

lemma max_fields_square_le (v : ι → ℝ) (h : ℕ) (hh : ∀ s, T.depth s ≤ h) (s : ι) :
    (max (T.fields v s).1 (T.fields v s).2) ^ 2 ≤
      ((h : ℝ) + 1 - T.depth s) * T.descEnergy v s := by
  let k : ℝ := (h : ℝ) - T.depth s
  let B : ℝ := ∑ c ∈ T.children s, T.descEnergy v c
  let r : ℝ := Real.sqrt (∑ c ∈ T.children s, (max (T.fields v c).1 (T.fields v c).2) ^ 2)
  have hk : 0 ≤ k := sub_nonneg.mpr (by exact_mod_cast hh s)
  have hB : 0 ≤ B := Finset.sum_nonneg fun c hc => T.descEnergy_nonneg v c
  have hr : r ^ 2 ≤ k * B := by
    rw [show r ^ 2 = ∑ c ∈ T.children s, (max (T.fields v c).1 (T.fields v c).2) ^ 2 from
      Real.sq_sqrt (Finset.sum_nonneg fun c hc => sq_nonneg _)]
    calc
      _ ≤ ∑ c ∈ T.children s, k * T.descEnergy v c := by
        apply Finset.sum_le_sum
        intro c hc
        apply (max_fields_square_le v h hh c).trans
        apply mul_le_mul_of_nonneg_right _ (T.descEnergy_nonneg v c)
        dsimp [k]
        have hdc : (T.depth s : ℝ) + 1 ≤ T.depth c := by exact_mod_cast T.child_depth hc
        linarith
      _ = k * B := by rw [← Finset.mul_sum]
  have hm0 : 0 ≤ max (T.fields v s).1 (T.fields v s).2 :=
    (T.fields_nonneg v s).1.trans (le_max_left _ _)
  have hsq := pow_le_pow_left₀ hm0 (T.max_fields_le v s) 2
  have hw := weighted_square_bound (a := |v s|) hk hB hr
  rw [sq_abs] at hw
  rw [T.descEnergy_eq]
  calc
    _ ≤ (|v s| + r) ^ 2 := hsq
    _ ≤ (k + 1) * (v s ^ 2 + B) := hw
    _ = ((h : ℝ) + 1 - T.depth s) * (v s ^ 2 + ∑ c ∈ T.children s, T.descEnergy v c) := by
      dsimp [k, B]; ring
termination_by T.maxDepth - T.depth s
decreasing_by exact T.child_measure hc

lemma weighted_sum_children (w e : ι → ℝ) :
    ∑ s, w s * ∑ c ∈ T.children s, e c =
      ∑ c ∈ Finset.univ.erase T.root, w (T.parent c) * e c := by
  simp only [Finset.mul_sum, children, Finset.sum_filter, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  calc
    (∑ c, ∑ s, if c ≠ T.root ∧ T.parent c = s then w s * e c else 0) =
        ∑ c, if c = T.root then 0 else w (T.parent c) * e c := by
      apply Finset.sum_congr rfl
      intro c hc
      by_cases h : c = T.root
      · simp [h]
      · simp [h]
    _ = ∑ c ∈ Finset.univ.erase T.root, w (T.parent c) * e c := by
      have hset : Finset.univ.erase T.root =
          Finset.univ.filter (fun c => c ≠ T.root) := by
        ext c; simp
      rw [hset, Finset.sum_filter]
      simp only [ite_not]

lemma upper_sum_square_le {p : ι → ℝ} (hp : T.Upper p) (h : ℕ)
    (hh : ∀ s, T.depth s ≤ h) : ∑ s, p s ^ 2 ≤ ((h : ℝ) + 1) * p T.root ^ 2 := by
  let w : ι → ℝ := fun s => (h : ℝ) - T.depth s
  have hw : ∀ s, 0 ≤ w s := fun s => sub_nonneg.mpr (by exact_mod_cast hh s)
  have he : ∑ s, w s * ∑ c ∈ T.children s, p c ^ 2 ≤ ∑ s, w s * p s ^ 2 :=
    Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hp s) (hw s)
  rw [T.weighted_sum_children] at he
  have hc : ∑ c ∈ Finset.univ.erase T.root, (w c + 1) * p c ^ 2 ≤
      ∑ c ∈ Finset.univ.erase T.root, w (T.parent c) * p c ^ 2 := by
    apply Finset.sum_le_sum
    intro c hc
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    dsimp [w]
    have hd : (T.depth (T.parent c) : ℝ) + 1 ≤ T.depth c := by
      exact_mod_cast T.parent_depth c (Finset.mem_erase.mp hc).1
    linarith
  have hs : ∑ c ∈ Finset.univ.erase T.root, (w c + 1) * p c ^ 2 =
      (∑ s, w s * p s ^ 2) - h * p T.root ^ 2 + ((∑ s, p s ^ 2) - p T.root ^ 2) := by
    simp only [add_mul, one_mul, Finset.sum_add_distrib,
      Finset.sum_erase_eq_sub (Finset.mem_univ T.root)]
    simp only [w, T.depth_root, Nat.cast_zero, sub_zero]
    ring
  rw [hs] at hc
  nlinarith

lemma block_square_comparison (v : ι → ℝ) (h : ℕ) (hh : ∀ s, T.depth s ≤ h) :
    ((max (T.fields v T.root).1 (T.fields v T.root).2) ^ 2 ≤
      ((h : ℝ) + 1) * ∑ s, v s ^ 2) ∧
    ((∑ s, v s ^ 2) ≤ 4 * ((h : ℝ) + 1) *
      (max (T.fields v T.root).1 (T.fields v T.root).2) ^ 2) := by
  constructor
  · simpa only [T.depth_root, Nat.cast_zero, sub_zero, T.descEnergy_root] using
      T.max_fields_square_le v h hh T.root
  · have hp := T.upper_sum_square_le (T.fields_upper v).1 h hh
    have hq := T.upper_sum_square_le (T.fields_upper v).2 h hh
    have hv : ∑ s, v s ^ 2 ≤ 2 * (∑ s, (T.fields v s).1 ^ 2) +
        2 * (∑ s, (T.fields v s).2 ^ 2) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro s hs
      rw [← T.fields_difference v s]
      nlinarith [sq_nonneg ((T.fields v s).1 + (T.fields v s).2)]
    have hpM := pow_le_pow_left₀ (T.fields_nonneg v T.root).1
      (le_max_left (T.fields v T.root).1 (T.fields v T.root).2) 2
    have hqM := pow_le_pow_left₀ (T.fields_nonneg v T.root).2
      (le_max_right (T.fields v T.root).1 (T.fields v T.root).2) 2
    have hh0 : 0 ≤ (h : ℝ) + 1 := by positivity
    have hp' := mul_le_mul_of_nonneg_left hpM hh0
    have hq' := mul_le_mul_of_nonneg_left hqM hh0
    nlinarith

end FiniteRootedTree

open Filter Topology

open scoped ENNReal

noncomputable section

namespace SquareSum

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (E : ι → Type uFiber)
    [∀ i, NormedAddCommGroup (E i)] [fiberNormedSpace : ∀ i, NormedSpace ℝ (E i)]

lemma pairing_apply {ι : Type uIndex} [DecidableEq ι] (E : ι → Type uFiber)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)] (f : Space (DualFamily E))
    (x : Space E) :
    pairing E f x = ∑' i, f i (x i) := rfl

@[simp] lemma pairing_single_right (f : Space (DualFamily E)) (i : ι) (x : E i) :
    pairing E f (lp.single 2 i x) = f i x := by
  classical
  rw [pairing_apply, tsum_eq_single i]
  · rw [lp.single_apply_self]
  · intro j hj
    rw [lp.single_apply_ne _ _ _ hj, map_zero]

@[simp] lemma pairing_single_left (i : ι) (f : E i →L[ℝ] ℝ) (x : Space E) :
    pairing E (lp.single 2 i f) x = f (x i) := by
  classical
  rw [pairing_apply, tsum_eq_single i]
  · rw [lp.single_apply_self]
  · intro j hj
    rw [lp.single_apply_ne _ _ _ hj]
    rfl

def restrictAt (f : Space E →L[ℝ] ℝ) (i : ι) : E i →L[ℝ] ℝ :=
  f.comp (lp.singleContinuousLinearMap ℝ E 2 i)

@[simp] lemma restrictAt_apply (f : Space E →L[ℝ] ℝ) (i : ι) (x : E i) :
    restrictAt E f i x = f (lp.single 2 i x) := rfl

lemma exists_half_norming {X : Type uTarget} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (f : X →L[ℝ] ℝ) : ∃ x : X, ‖x‖ ≤ 1 ∧ ‖f‖ / 2 ≤ f x := by
  by_cases hf : f = 0
  · subst f; exact ⟨0, by simp, by simp⟩
  have hfpos : 0 < ‖f‖ := norm_pos_iff.mpr hf
  obtain ⟨x, hx, hfx⟩ := f.exists_lt_apply_of_lt_opNorm (half_lt_self hfpos)
  by_cases hsgn : 0 ≤ f x
  · refine ⟨x, hx.le, ?_⟩
    rw [Real.norm_eq_abs, abs_of_nonneg hsgn] at hfx
    exact hfx.le
  · refine ⟨-x, by simpa only [norm_neg] using hx.le, ?_⟩
    rw [map_neg]
    rw [Real.norm_eq_abs, abs_of_neg (lt_of_not_ge hsgn)] at hfx
    exact hfx.le

lemma restriction_square_bound (f : Space E →L[ℝ] ℝ) (S : Finset ι) :
    ∑ i ∈ S, ‖restrictAt E f i‖ ^ 2 ≤ (2 * ‖f‖) ^ 2 := by
  classical
  choose x hx hfx using fun i => exists_half_norming (restrictAt E f i)
  let q : ℝ := ∑ i ∈ S, ‖restrictAt E f i‖ ^ 2
  let v : Space E := ∑ i ∈ S, lp.single 2 i (‖restrictAt E f i‖ • x i)
  have hq : 0 ≤ q := Finset.sum_nonneg (fun i hi => sq_nonneg _)
  have hv2 : ‖v‖ ^ 2 ≤ q := by
    have h := lp.norm_sum_single (E := E) (p := 2) (by norm_num) (fun i => ‖restrictAt E f i‖ • x i) S
    norm_num only [ENNReal.toReal_ofNat, Real.rpow_two] at h
    change ‖v‖ ^ 2 = _ at h
    rw [h]
    apply Finset.sum_le_sum
    intro i hi
    rw [norm_smul, norm_norm, mul_pow]
    have hi0 := norm_nonneg (x i)
    have hi1 := hx i
    have hisq : ‖x i‖ ^ 2 ≤ 1 := by nlinarith
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hisq (sq_nonneg ‖restrictAt E f i‖)
  have hfv : q / 2 ≤ f v := by
    dsimp [v]
    rw [map_sum]
    calc
      q / 2 = ∑ i ∈ S, ‖restrictAt E f i‖ * (‖restrictAt E f i‖ / 2) := by
        dsimp [q]
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i hi
        change _ ≤ restrictAt E f i (‖restrictAt E f i‖ • x i)
        rw [map_smul, smul_eq_mul]
        exact mul_le_mul_of_nonneg_left (hfx i) (norm_nonneg _)
  have hf' : f v ≤ ‖f‖ * ‖v‖ := (le_abs_self _).trans (f.le_opNorm v)
  have hv : ‖v‖ ≤ Real.sqrt q := (Real.le_sqrt (norm_nonneg _) hq).mpr hv2
  have hhalf := hf'.trans (mul_le_mul_of_nonneg_left hv (norm_nonneg f))
  have hr : Real.sqrt q ≤ 2 * ‖f‖ := by
    by_contra hh
    have hlt : 2 * ‖f‖ < Real.sqrt q := lt_of_not_ge hh
    have hp : 0 < Real.sqrt q := (by positivity : (0 : ℝ) ≤ 2 * ‖f‖).trans_lt hlt
    have H := mul_lt_mul_of_pos_right hlt hp
    nlinarith [Real.sq_sqrt hq]
  change q ≤ (2 * ‖f‖) ^ 2
  nlinarith [Real.sq_sqrt hq, Real.sqrt_nonneg q, norm_nonneg f]

lemma restriction_mem (f : Space E →L[ℝ] ℝ) : Memℓp (restrictAt E f) 2 := by
  apply memℓp_gen' (C := (2 * ‖f‖) ^ 2)
  intro S
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using restriction_square_bound E f S

def restrict (f : Space E →L[ℝ] ℝ) : Space (DualFamily E) := ⟨restrictAt E f, restriction_mem E f⟩

@[simp] lemma restrict_apply (f : Space E →L[ℝ] ℝ) (i : ι) :
    restrict E f i = restrictAt E f i := rfl

lemma pairing_restrict (f : Space E →L[ℝ] ℝ) : pairing E (restrict E f) = f := by
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  intro i
  ext x
  exact pairing_single_right E (restrict E f) i x

end SquareSum

end

open UniformSpace

noncomputable section

namespace SquareSum

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (E : ι → Type uFiber)
    [∀ i, NormedAddCommGroup (E i)] [fiberNormedSpace : ∀ i, NormedSpace ℝ (E i)]

lemma closedSubmodule_eq_top (S : Submodule ℝ (Space E)) (hS : IsClosed (S : Set (Space E)))
    (hsingle : ∀ i (x : E i), lp.single 2 i x ∈ S) : S = ⊤ := by
  apply top_unique
  intro x hx
  exact hS.mem_of_tendsto (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) x)
    (Filter.Eventually.of_forall fun J => S.sum_mem fun i hi => hsingle i (x i))

lemma denseRange_of_single {X : Type uTarget} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (f : X →L[ℝ] Space E) (hsingle : ∀ i (x : E i), lp.single 2 i x ∈ f.range) :
    DenseRange f := by
  have htop := closedSubmodule_eq_top E f.range.topologicalClosure
    f.range.isClosed_topologicalClosure (fun i x => f.range.le_topologicalClosure (hsingle i x))
  intro x
  have hm : x ∈ f.range.topologicalClosure := by rw [htop]; trivial
  exact hm

end SquareSum

end

namespace TreeVector

open scoped ENNReal

noncomputable section

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

lemma toSquareLinear_norm_sq (v : TreeVector T) :
    ‖toSquareLinear T v‖ ^ 2 = ∑ s ∈ (show ι →₀ ℝ from v).support, v s ^ 2 := by
  change ‖∑ s ∈ (show ι →₀ ℝ from v).support, lp.single 2 s (v s)‖ ^ 2 = _
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs] using
    lp.norm_sum_single (E := fun _ : ι => ℝ) (p := 2) (by norm_num) (fun s => v s)
      (show ι →₀ ℝ from v).support

@[simp] lemma toSquareLinear_single (s : ι) (a : ℝ) :
    toSquareLinear T (Finsupp.single s a) = lp.single 2 s a := by
  change ((Finsupp.lsum ℝ) (fun s : ι => lp.lsingle (𝕜 := ℝ) (E := fun _ : ι => ℝ) 2 s))
    (Finsupp.single s a) = _
  simp

lemma block_square_comparison (v : TreeVector T) (h : ℕ) (hh : ∀ s, T.depth s ≤ h) :
    (max (T.P v T.root) (T.Q v T.root)) ^ 2 ≤
      ((h : ℝ) + 1) * ‖toSquareLinear T v‖ ^ 2 ∧
    ‖toSquareLinear T v‖ ^ 2 ≤ 4 * ((h : ℝ) + 1) *
      (max (T.P v T.root) (T.Q v T.root)) ^ 2 := by
  let w : ι →₀ ℝ := v
  let H := T.head w
  let U := T.restrict H (T.head_initial w)
  have hfields : T.P w T.root = (U.fields (fun c => w c.1) U.root).1 ∧
      T.Q w T.root = (U.fields (fun c => w c.1) U.root).2 :=
    T.potentials_on_head w H (T.head_initial w) (T.support_subset_head w)
      ⟨T.root, (T.head_initial w).1⟩
  have hn : ‖toSquareLinear T v‖ ^ 2 = ∑ s ∈ w.support, w s ^ 2 :=
    toSquareLinear_norm_sq T v
  have hsum : (∑ s : H, w s.1 ^ 2) = ‖toSquareLinear T v‖ ^ 2 := by
    rw [hn, ← Finset.sum_subtype H (fun _ => Iff.rfl) (fun s => w s ^ 2)]
    exact (Finset.sum_subset (T.support_subset_head w) (fun s hs hs' => by
      rw [Finsupp.notMem_support_iff.mp hs']; norm_num)).symm
  have hc := U.block_square_comparison (fun s => w s.1) h (fun s => hh s.1)
  rw [← hfields.1, ← hfields.2, hsum] at hc
  exact hc

lemma hilbert_comparisons (v : TreeVector T) (h : ℕ) (hh : ∀ s, T.depth s ≤ h) :
    ‖v‖ ≤ (2 * Real.sqrt ((h : ℝ) + 1)) * ‖toSquareLinear T v‖ ∧
    ‖toSquareLinear T v‖ ≤ (2 * Real.sqrt ((h : ℝ) + 1)) * ‖v‖ := by
  have hc := block_square_comparison T v h hh
  have hp := T.P_nonneg v T.root
  have hq := T.Q_nonneg v T.root
  have hM : 0 ≤ max (T.P v T.root) (T.Q v T.root) := hp.trans (le_max_left _ _)
  have hh0 : 0 ≤ (h : ℝ) + 1 := by positivity
  have hr := Real.sq_sqrt hh0
  have hn : ‖v‖ = T.P v T.root + T.Q v T.root := rfl
  have hnM : ‖v‖ ≤ 2 * max (T.P v T.root) (T.Q v T.root) := by
    rw [hn]; linarith [le_max_left (T.P v T.root) (T.Q v T.root), le_max_right (T.P v T.root) (T.Q v T.root)]
  have hMn : max (T.P v T.root) (T.Q v T.root) ≤ ‖v‖ := by rw [hn]; exact max_le (by linarith) (by linarith)
  have hM2n := pow_le_pow_left₀ hM hMn 2
  have hMbound : max (T.P v T.root) (T.Q v T.root) ≤
      Real.sqrt ((h : ℝ) + 1) * ‖toSquareLinear T v‖ := by
    have hsq : (Real.sqrt ((h : ℝ) + 1) * ‖toSquareLinear T v‖) ^ 2 =
        ((h : ℝ) + 1) * ‖toSquareLinear T v‖ ^ 2 := by rw [mul_pow, hr]
    nlinarith [mul_nonneg (Real.sqrt_nonneg ((h : ℝ) + 1)) (norm_nonneg (toSquareLinear T v))]
  constructor
  · nlinarith
  · have he := mul_le_mul_of_nonneg_left hM2n (by positivity : 0 ≤ 4 * ((h : ℝ) + 1))
    have hsq : ((2 * Real.sqrt ((h : ℝ) + 1)) * ‖v‖) ^ 2 =
        4 * ((h : ℝ) + 1) * ‖v‖ ^ 2 := by rw [mul_pow, mul_pow, hr]; ring
    nlinarith [norm_nonneg (toSquareLinear T v),
      mul_nonneg (by positivity : 0 ≤ 2 * Real.sqrt ((h : ℝ) + 1)) (norm_nonneg v)]

def toSquare (h : ℕ) (hh : ∀ s, T.depth s ≤ h) :
    TreeVector T →L[ℝ] SquareSum.Space (fun _ : ι => ℝ) :=
  (toSquareLinear T).mkContinuous (2 * Real.sqrt ((h : ℝ) + 1))
    (fun v => (hilbert_comparisons T v h hh).2)

lemma toSquare_dense (h : ℕ) (hh : ∀ s, T.depth s ≤ h) : DenseRange (toSquare T h hh) := by
  apply SquareSum.denseRange_of_single
  intro s a
  refine ⟨Finsupp.single s a, ?_⟩
  exact toSquareLinear_single T s a

end

end TreeVector

namespace TreeSpace

noncomputable section

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

def hilbertEquiv (h : ℕ) (hh : ∀ s, T.depth s ≤ h) :
    TreeSpace T ≃L[ℝ] SquareSum.Space (fun _ : ι => ℝ) :=
  completionEquivOfDense (TreeVector.toSquare T h hh)
    ⟨2 * Real.sqrt ((h : ℝ) + 1), by positivity⟩
    (fun v => (TreeVector.hilbert_comparisons T v h hh).1) (TreeVector.toSquare_dense T h hh)

end

end TreeSpace

namespace Joined

noncomputable section

open UniformSpace

abbrev Component (h : ℕ+) := TreeSpace (componentTree h)

abbrev Outer : Type := SquareSum.Space Component

def embed (h : ℕ+) : ComponentNode h ↪ JoinedNode where
  toFun s := some ⟨h, s⟩
  inj' := by intro s t he; simpa using he

@[simp] lemma embed_apply (h : ℕ+) (s : ComponentNode h) : embed h s = some ⟨h, s⟩ := rfl

@[simp] lemma embed_ne_root (h : ℕ+) (s : ComponentNode h) : embed h s ≠ joinedTree.root := by
  simp [joinedTree]

lemma embed_parent (h : ℕ+) (s : ComponentNode h) (hs : s ≠ (componentTree h).root) :
    joinedTree.parent (embed h s) = embed h ((componentTree h).parent s) := by
  have hn : s.1 ≠ [] := fun he => hs (Subtype.ext he)
  change (if s.1 = [] then none else _) = _
  rw [ite_eq_right hn]
  rfl

@[simp] lemma embed_root_parent (h : ℕ+) :
    joinedTree.parent (embed h (componentTree h).root) = joinedTree.root := rfl

def rootEmbed : ℕ+ ↪ JoinedNode where
  toFun h := embed h (componentTree h).root
  inj' := by
    intro h k he
    have hh := Option.some.inj he
    exact congrArg Sigma.fst hh

lemma root_child (c : JoinedNode) (hc : c ≠ joinedTree.root)
    (hp : joinedTree.parent c = joinedTree.root) : ∃ h, c = rootEmbed h := by
  cases c with
  | none => exact (hc rfl).elim
  | some c =>
    obtain ⟨h, s⟩ := c
    by_cases hs : s.1 = []
    · refine ⟨h, ?_⟩
      change (some ⟨h, s⟩ : JoinedNode) = some ⟨h, (componentTree h).root⟩
      congr 2
      exact Subtype.ext hs
    · change (if s.1 = [] then none else _) = none at hp
      rw [ite_eq_right hs] at hp
      contradiction

lemma component_child (h : ℕ+) (s : ComponentNode h) (c : JoinedNode)
    (hc : c ≠ joinedTree.root) (hp : joinedTree.parent c = embed h s) :
    ∃ d : ComponentNode h, c = embed h d ∧ d ≠ (componentTree h).root ∧
      (componentTree h).parent d = s := by
  cases c with
  | none => exact (hc rfl).elim
  | some c =>
    obtain ⟨k, d⟩ := c
    by_cases hd : d.1 = []
    · change (if d.1 = [] then none else _) = (some ⟨h, s⟩ : JoinedNode) at hp
      rw [ite_eq_left hd] at hp
      contradiction
    · change (if d.1 = [] then none else _) = (some ⟨h, s⟩ : JoinedNode) at hp
      rw [ite_eq_right hd] at hp
      have hk : k = h := congrArg Sigma.fst (Option.some.inj hp)
      subst k
      refine ⟨d, rfl, fun he => hd (congrArg Subtype.val he), ?_⟩
      exact (embed h).injective (by exact hp)

lemma upper_pull (h : ℕ+) {p : JoinedNode → ℝ} (hp : joinedTree.GlobalUpper p) :
    (componentTree h).GlobalUpper (fun s => p (embed h s)) := by
  intro s S hS
  have hh := hp (embed h s) (S.map (embed h)) (by
    intro c hc
    obtain ⟨d, hd, rfl⟩ := Finset.mem_map.mp hc
    refine ⟨embed_ne_root h d, ?_⟩
    rw [embed_parent h d (hS d hd).1, (hS d hd).2])
  simpa only [Finset.sum_map] using hh

def partLinear (h : ℕ+) : TreeVector joinedTree →ₗ[ℝ] TreeVector (componentTree h) where
  toFun v := Finsupp.comapDomain (embed h) v (embed h).injective.injOn
  map_add' v w := by apply Finsupp.ext; intro s; rfl
  map_smul' a v := by apply Finsupp.ext; intro s; rfl

@[simp] lemma partLinear_apply (h : ℕ+) (v : TreeVector joinedTree) (s : ComponentNode h) :
    partLinear h v s = v (embed h s) := rfl

lemma part_potentials_le (v : TreeVector joinedTree) (h : ℕ+) (s : ComponentNode h) :
    (componentTree h).P (partLinear h v) s ≤ joinedTree.P v (embed h s) ∧
    (componentTree h).Q (partLinear h v) s ≤ joinedTree.Q v (embed h s) := by
  apply (componentTree h).potentials_minimal (partLinear h v)
    (fun s => joinedTree.P v (embed h s)) (fun s => joinedTree.Q v (embed h s))
  · intro s; exact joinedTree.P_nonneg v _
  · intro s; exact joinedTree.Q_nonneg v _
  · intro s; exact joinedTree.P_sub_Q v _
  · exact upper_pull h (joinedTree.P_upper v)
  · exact upper_pull h (joinedTree.Q_upper v)

lemma part_square_bound (v : TreeVector joinedTree) (S : Finset ℕ+) :
    ∑ h ∈ S, ‖partLinear h v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
  let w : JoinedNode →₀ ℝ := v
  have hp : ∑ h ∈ S, (componentTree h).P (partLinear h v) (componentTree h).root ^ 2 ≤
      joinedTree.P w joinedTree.root ^ 2 := by
    calc
      _ ≤ ∑ h ∈ S, joinedTree.P w (rootEmbed h) ^ 2 := by
        apply Finset.sum_le_sum
        intro h hh
        exact pow_le_pow_left₀ ((componentTree h).P_nonneg _ _)
          (part_potentials_le v h (componentTree h).root).1 2
      _ ≤ _ := by
        have hh := joinedTree.P_upper w joinedTree.root (S.map rootEmbed) (by
          intro c hc
          obtain ⟨h, hh, rfl⟩ := Finset.mem_map.mp hc
          exact ⟨embed_ne_root h _, embed_root_parent h⟩)
        simpa only [Finset.sum_map] using hh
  have hq : ∑ h ∈ S, (componentTree h).Q (partLinear h v) (componentTree h).root ^ 2 ≤
      joinedTree.Q w joinedTree.root ^ 2 := by
    calc
      _ ≤ ∑ h ∈ S, joinedTree.Q w (rootEmbed h) ^ 2 := by
        apply Finset.sum_le_sum
        intro h hh
        exact pow_le_pow_left₀ ((componentTree h).Q_nonneg _ _)
          (part_potentials_le v h (componentTree h).root).2 2
      _ ≤ _ := by
        have hh := joinedTree.Q_upper w joinedTree.root (S.map rootEmbed) (by
          intro c hc
          obtain ⟨h, hh, rfl⟩ := Finset.mem_map.mp hc
          exact ⟨embed_ne_root h _, embed_root_parent h⟩)
        simpa only [Finset.sum_map] using hh
  exact sum_add_sq_le S (fun h => (componentTree h).P (partLinear h v) (componentTree h).root)
    (fun h => (componentTree h).Q (partLinear h v) (componentTree h).root)
    (joinedTree.P_nonneg w _) (joinedTree.Q_nonneg w _) hp hq

lemma parts_mem (v : TreeVector joinedTree) :
    Memℓp (fun h => (partLinear h v : Component h)) 2 := by
  apply memℓp_gen' (C := ‖v‖ ^ 2)
  intro S
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Completion.norm_coe] using part_square_bound v S

def components (v : TreeVector joinedTree) :
    Outer := ⟨fun h => (partLinear h v : Component h), parts_mem v⟩

@[simp] lemma components_apply (v : TreeVector joinedTree) (h : ℕ+) :
    components v h = (partLinear h v : Component h) := rfl

lemma components_norm_le (v : TreeVector joinedTree) : ‖components v‖ ≤ ‖v‖ := by
  apply lp.norm_le_of_forall_sum_le (by norm_num) (norm_nonneg v)
  intro S
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, components_apply, Completion.norm_coe] using part_square_bound v S

def componentsLinear : TreeVector joinedTree →ₗ[ℝ] Outer where
  toFun := components
  map_add' v w := by
    apply lp.ext
    funext h
    simp only [lp.coeFn_add, Pi.add_apply, components_apply, map_add, Completion.coe_add]
  map_smul' a v := by
    apply lp.ext
    funext h
    simp only [lp.coeFn_smul, Pi.smul_apply, components_apply, map_smul, Completion.coe_smul, RingHom.id_apply]

def componentsMap : TreeVector joinedTree →L[ℝ] Outer :=
  componentsLinear.mkContinuous 1 (fun v => by
    change ‖components v‖ ≤ 1 * ‖v‖
    simpa only [one_mul] using components_norm_le v)

def field (r : ℝ) (f : ∀ h : ℕ+, ComponentNode h → ℝ) : JoinedNode → ℝ
  | none => r
  | some ⟨h, s⟩ => f h s

@[simp] lemma field_root (r : ℝ) (f : ∀ h : ℕ+, ComponentNode h → ℝ) :
    field r f joinedTree.root = r := rfl

@[simp] lemma field_embed (r : ℝ) (f : ∀ h : ℕ+, ComponentNode h → ℝ) (h : ℕ+) (s : ComponentNode h) :
    field r f (embed h s) = f h s := rfl

lemma field_nonneg (r : ℝ) (f : ∀ h : ℕ+, ComponentNode h → ℝ) (hr : 0 ≤ r)
    (hf : ∀ h s, 0 ≤ f h s) (c : JoinedNode) : 0 ≤ field r f c := by
  cases c with
  | none => exact hr
  | some c => exact hf c.1 c.2

lemma field_upper (r : ℝ) (f : ∀ h : ℕ+, ComponentNode h → ℝ)
    (hf : ∀ h, (componentTree h).GlobalUpper (f h))
    (hr : ∀ S : Finset ℕ+, ∑ h ∈ S, f h (componentTree h).root ^ 2 ≤ r ^ 2) :
    joinedTree.GlobalUpper (field r f) := by
  intro s S hS
  cases s with
  | none =>
    have he := Finset.sum_preimage rootEmbed S rootEmbed.injective.injOn
      (fun c => field r f c ^ 2) (by
        intro c hc hn
        obtain ⟨h, hh⟩ := root_child c (hS c hc).1 (hS c hc).2
        exact (hn ⟨h, hh.symm⟩).elim)
    rw [← he]
    exact hr _
  | some s =>
    obtain ⟨h, s⟩ := s
    have he := Finset.sum_preimage (embed h) S (embed h).injective.injOn
      (fun c => field r f c ^ 2) (by
        intro c hc hn
        obtain ⟨d, hd, hne, hpar⟩ := component_child h s c (hS c hc).1 (hS c hc).2
        exact (hn ⟨d, hd.symm⟩).elim)
    rw [← he]
    apply hf h s
    intro d hd
    have hd' := Finset.mem_preimage.mp hd
    obtain ⟨e, he, hne, hpar⟩ := component_child h s (embed h d) (hS _ hd').1 (hS _ hd').2
    have hde : d = e := (embed h).injective he
    exact hde ▸ ⟨hne, hpar⟩

lemma part_squares_le_outer (v : TreeVector joinedTree) (S : Finset ℕ+) :
    ∑ h ∈ S, ‖partLinear h v‖ ^ 2 ≤ ‖components v‖ ^ 2 := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, components_apply, Completion.norm_coe] using
    lp.sum_rpow_le_norm_rpow (p := 2) (by norm_num) (components v) S

lemma part_field_squares_le_outer (v : TreeVector joinedTree) (S : Finset ℕ+) :
    (∑ h ∈ S, (componentTree h).P (partLinear h v) (componentTree h).root ^ 2 ≤ ‖components v‖ ^ 2) ∧
    (∑ h ∈ S, (componentTree h).Q (partLinear h v) (componentTree h).root ^ 2 ≤ ‖components v‖ ^ 2) := by
  constructor
  · apply le_trans (Finset.sum_le_sum (fun h hh => ?_)) (part_squares_le_outer v S)
    apply pow_le_pow_left₀ ((componentTree h).P_nonneg _ _) _ 2
    exact ((componentTree h).potentials_le_normSum (partLinear h v) (componentTree h).root).1
  · apply le_trans (Finset.sum_le_sum (fun h hh => ?_)) (part_squares_le_outer v S)
    apply pow_le_pow_left₀ ((componentTree h).Q_nonneg _ _) _ 2
    exact ((componentTree h).potentials_le_normSum (partLinear h v) (componentTree h).root).2

def liftP (v : TreeVector joinedTree) : JoinedNode → ℝ :=
  field (‖components v‖ + max (v joinedTree.root) 0)
    (fun h => (componentTree h).P (partLinear h v))

def liftQ (v : TreeVector joinedTree) : JoinedNode → ℝ :=
  field (‖components v‖ + max (-v joinedTree.root) 0)
    (fun h => (componentTree h).Q (partLinear h v))

lemma liftP_nonneg (v : TreeVector joinedTree) (s : JoinedNode) : 0 ≤ liftP v s :=
  field_nonneg _ _ (by positivity) (fun h s => (componentTree h).P_nonneg _ _) s

lemma liftQ_nonneg (v : TreeVector joinedTree) (s : JoinedNode) : 0 ≤ liftQ v s :=
  field_nonneg _ _ (by positivity) (fun h s => (componentTree h).Q_nonneg _ _) s

lemma lift_difference (v : TreeVector joinedTree) (s : JoinedNode) :
    liftP v s - liftQ v s = v s := by
  cases s with
  | none =>
    change (‖components v‖ + max (v joinedTree.root) 0) -
      (‖components v‖ + max (-v joinedTree.root) 0) = v joinedTree.root
    rcases le_total 0 (v joinedTree.root) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  | some s => exact (componentTree s.1).P_sub_Q (partLinear s.1 v) s.2

lemma lifts_upper (v : TreeVector joinedTree) :
    joinedTree.GlobalUpper (liftP v) ∧ joinedTree.GlobalUpper (liftQ v) := by
  constructor
  · apply field_upper
    · intro h; exact (componentTree h).P_upper _
    · intro S
      apply (part_field_squares_le_outer v S).1.trans
      exact pow_le_pow_left₀ (norm_nonneg _) (le_add_of_nonneg_right (le_max_right _ _)) 2
  · apply field_upper
    · intro h; exact (componentTree h).Q_upper _
    · intro S
      apply (part_field_squares_le_outer v S).2.trans
      exact pow_le_pow_left₀ (norm_nonneg _) (le_add_of_nonneg_right (le_max_right _ _)) 2

lemma potentials_le_lifts (v : TreeVector joinedTree) (s : JoinedNode) :
    joinedTree.P v s ≤ liftP v s ∧ joinedTree.Q v s ≤ liftQ v s :=
  joinedTree.potentials_minimal v (liftP v) (liftQ v) (liftP_nonneg v) (liftQ_nonneg v)
    (lift_difference v) (lifts_upper v).1 (lifts_upper v).2 s

lemma norm_le_root_add_outer (v : TreeVector joinedTree) :
    ‖v‖ ≤ |v joinedTree.root| + 2 * ‖components v‖ := by
  have h := potentials_le_lifts v joinedTree.root
  have h1 : joinedTree.P v joinedTree.root ≤ ‖components v‖ + max (v joinedTree.root) 0 := h.1
  have h2 : joinedTree.Q v joinedTree.root ≤ ‖components v‖ + max (-v joinedTree.root) 0 := h.2
  change joinedTree.P v joinedTree.root + joinedTree.Q v joinedTree.root ≤ _
  rcases le_total 0 (v joinedTree.root) with hn | hn
  · rw [abs_of_nonneg hn, max_eq_left hn] at *
    rw [max_eq_right (by linarith : -v joinedTree.root ≤ 0)] at h2
    linarith
  · rw [abs_of_nonpos hn, max_eq_right hn] at *
    rw [max_eq_left (by linarith : 0 ≤ -v joinedTree.root)] at h2
    linarith

def put (h : ℕ+) (v : TreeVector (componentTree h)) :
    TreeVector joinedTree := Finsupp.embDomain (embed h) v

lemma put_root (h : ℕ+) (v : TreeVector (componentTree h)) : put h v joinedTree.root = 0 := by
  apply Finsupp.embDomain_of_notMem_range
  rintro ⟨s, hs⟩
  exact embed_ne_root h s hs

lemma part_put_same (h : ℕ+) (v : TreeVector (componentTree h)) : partLinear h (put h v) = v := by
  apply Finsupp.ext
  intro s
  exact Finsupp.embDomain_apply_self (embed h) v s

lemma part_put_other (h k : ℕ+) (hk : k ≠ h) (v : TreeVector (componentTree h)) :
    partLinear k (put h v) = 0 := by
  apply Finsupp.ext
  intro s
  apply Finsupp.embDomain_of_notMem_range
  rintro ⟨t, ht⟩
  have hk' := congrArg Sigma.fst (Option.some.inj ht)
  exact hk hk'.symm

lemma components_put (h : ℕ+) (v : TreeVector (componentTree h)) :
    components (put h v) = lp.single 2 h (v : Component h) := by
  apply lp.ext
  funext k
  by_cases hk : k = h
  · subst k
    rw [components_apply, part_put_same, lp.single_apply_self]
  · rw [components_apply, part_put_other h k hk, Completion.coe_zero, lp.single_apply_ne _ _ _ hk]

def rootVector (a : ℝ) : TreeVector joinedTree := Finsupp.single joinedTree.root a

lemma components_rootVector (a : ℝ) :
    components (rootVector a) = 0 := by
  have hp : ∀ h, partLinear h (rootVector a) = 0 := by
    intro h
    apply Finsupp.ext
    intro s
    change Finsupp.single joinedTree.root a (embed h s) = 0
    exact Finsupp.single_eq_of_ne (embed_ne_root h s)
  apply lp.ext
  funext h
  rw [components_apply, hp h, Completion.coe_zero]
  rfl

def splitting : TreeVector joinedTree →L[ℝ] ℝ × Outer :=
  (TreeVector.coordinate joinedTree joinedTree.root).prod componentsMap

lemma splitting_apply (v : TreeVector joinedTree) :
    splitting v = (v joinedTree.root, components v) := rfl

lemma norm_le_splitting (v : TreeVector joinedTree) : ‖v‖ ≤ 3 * ‖splitting v‖ := by
  rw [splitting_apply, Prod.norm_def, Real.norm_eq_abs]
  have hn := norm_le_root_add_outer v
  have ha := le_max_left |v joinedTree.root| ‖components v‖
  have hb := le_max_right |v joinedTree.root| ‖components v‖
  linarith

lemma splitting_put (h : ℕ+) (v : TreeVector (componentTree h)) :
    splitting (put h v) = (0, lp.single 2 h (v : Component h)) := by
  rw [splitting_apply, put_root, components_put]

lemma splitting_rootVector (a : ℝ) :
    splitting (rootVector a) = (a, 0) := by
  rw [splitting_apply, components_rootVector]
  exact Prod.ext (Finsupp.single_eq_same) rfl

lemma splitting_dense : DenseRange splitting := by
  let S := splitting.range.topologicalClosure
  have hS : IsClosed (S : Set (ℝ × Outer)) := splitting.range.isClosed_topologicalClosure
  have hroot : ∀ a : ℝ, (a, (0 : Outer)) ∈ S := by
    intro a
    exact splitting.range.le_topologicalClosure ⟨rootVector a, splitting_rootVector a⟩
  have hsingle : ∀ h (x : Component h), (0, lp.single 2 h x) ∈ S := by
    intro h x
    induction x using Completion.induction_on with
    | hp =>
      exact hS.preimage ((ContinuousLinearMap.inr ℝ ℝ Outer).comp
        (lp.singleContinuousLinearMap ℝ Component 2 h)).continuous
    | ih v => exact splitting.range.le_topologicalClosure ⟨put h v, splitting_put h v⟩
  have houter : S.comap (ContinuousLinearMap.inr ℝ ℝ Outer).toLinearMap = ⊤ := by
    apply SquareSum.closedSubmodule_eq_top Component
    · exact hS.preimage (ContinuousLinearMap.inr ℝ ℝ Outer).continuous
    · exact hsingle
  intro z
  have hz : (0, z.2) ∈ S := by
    have h : z.2 ∈ S.comap (ContinuousLinearMap.inr ℝ ℝ Outer).toLinearMap := by rw [houter]; trivial
    exact h
  have hm := S.add_mem (hroot z.1) hz
  have hm' : z ∈ S := by simpa using hm
  exact hm'

def freeEquiv : XJoined ≃L[ℝ] ℝ × Outer :=
  completionEquivOfDense splitting 3 norm_le_splitting splitting_dense

end

end Joined

namespace Joined

noncomputable section

open UniformSpace

def zeroComponents : ZeroTreeVector joinedTree →L[ℝ] Outer :=
  componentsMap.comp (ZeroTreeVector.inclusion joinedTree)

lemma zero_norm_le_components (v : ZeroTreeVector joinedTree) : ‖v‖ ≤ ‖zeroComponents v‖ := by
  have h := norm_le_root_add_outer (ZeroTreeVector.toTree joinedTree v)
  rw [ZeroTreeVector.root_zero, abs_zero, zero_add] at h
  rw [ZeroTreeVector.norm_half]
  change _ ≤ ‖components (ZeroTreeVector.toTree joinedTree v)‖
  linarith

def zeroPut (h : ℕ+) (v : TreeVector (componentTree h)) : ZeroTreeVector joinedTree :=
  ⟨put h v, put_root h v⟩

lemma zeroComponents_zeroPut (h : ℕ+) (v : TreeVector (componentTree h)) :
    zeroComponents (zeroPut h v) = lp.single 2 h (v : Component h) := components_put h v

lemma zeroComponents_dense : DenseRange zeroComponents := by
  let S := zeroComponents.range.topologicalClosure
  have hS : IsClosed (S : Set Outer) := zeroComponents.range.isClosed_topologicalClosure
  have hsingle : ∀ h (x : Component h), lp.single 2 h x ∈ S := by
    intro h x
    induction x using Completion.induction_on with
    | hp => exact hS.preimage (lp.singleContinuousLinearMap ℝ Component 2 h).continuous
    | ih v => exact zeroComponents.range.le_topologicalClosure ⟨zeroPut h v, zeroComponents_zeroPut h v⟩
  have htop := SquareSum.closedSubmodule_eq_top Component S hS hsingle
  intro x
  have hx : x ∈ S := by rw [htop]; trivial
  exact hx

def zeroEquiv : XZero ≃L[ℝ] Outer :=
  completionEquivOfDense zeroComponents 1
    (fun v => by simpa only [NNReal.coe_one, one_mul] using zero_norm_le_components v)
    zeroComponents_dense

end

end Joined

noncomputable section

end

namespace FiniteRootedTree

variable {ι : Type uIndex} [indexFinite : Fintype ι] [indexDecidable : DecidableEq ι]
    (T : FiniteRootedTree ι)

end FiniteRootedTree

namespace TreeSpace

noncomputable section

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

end

end TreeSpace

open Filter

open scoped Topology

namespace TreeSpace

noncomputable section

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

end

end TreeSpace

section Lens

variable {E : Type uSpace} [NormedAddCommGroup E] [NormedSpace ℝ E]

end Lens

namespace TreeSpace

noncomputable section

open UniformSpace

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

end

end TreeSpace

end RecursivePotentials

end OAI


