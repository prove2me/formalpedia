-- Prove2me | Definitions.Def_ConsistentSubmodular_Deterministic_Basic_Simplex
-- name    : ConsistentSubmodular_Deterministic_Basic_Simplex
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:07:17.279002+00:00
-- url     : https://prove2.me/theorems/2695a875-d4f4-44ed-9d48-36cf490aa1ad
-- title:
--   Segments and vertices of the simplex: interpolation identities for $\mathrm{mix}$, $\delta_i$ and $\Delta$
-- statement:
--   This file introduces no new definitions. It develops the elementary calculus of the objects defined in the main statements file: the space $\mathbb R^{m+1}$ of weights on candidates $0,\dots,m$ (`Point m`), the vertex $\delta_i$ (`vertex i`, equal to $1$ at $i$ and $0$ elsewhere), the interpolation $\mathrm{mix}(p,q,x)=(1-x)p+xq$ (`mix`), and the simplex $\Delta=\{p: p_i\ge 0,\ \sum_i p_i=1\}$ (`IsSimplex`).
--
--   The file proves the following facts.
--
--   - Endpoint and degeneracy rules for interpolation: $\mathrm{mix}(p,q,0)=p$, $\mathrm{mix}(p,q,1)=q$, $\mathrm{mix}(p,p,x)=p$.
--   - Reversal: $\mathrm{mix}(p,q,x)=\mathrm{mix}(q,p,1-x)$.
--   - Reparametrization of a sub-segment: $\mathrm{mix}(\mathrm{mix}(p,q,x),q,y)=\mathrm{mix}(p,q,(1-y)x+y)$.
--   - Every vertex $\delta_i$ lies in $\Delta$, and every coordinate of a point of $\Delta$ is at most $1$.
--   - Convexity: if $p,q\in\Delta$ and $x\in[0,1]$ then $\mathrm{mix}(p,q,x)\in\Delta$.
--   - Complement products: for a finite index set $s$, $\prod_{j\in s}(1-\delta_i(j))$ is $0$ if $i\in s$ and $1$ otherwise. For $i\ne j$,
--   $$\prod_{k\in s}\big(1-\mathrm{mix}(\delta_i,\delta_j,x)_k\big)=\big(x\text{ if }i\in s\text{ else }1\big)\cdot\big(1-x\text{ if }j\in s\text{ else }1\big).$$
--
--   These identities are the algebra of the mixtures $H_j(p)$ along edges of the simplex. They are used when certificates (safe polygonal paths in $\Delta$) are built from segments between vertices and half mixtures, in Section 3 and Appendix B.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Basic/Simplex.lean (definitions and supporting lemmas of this module, ported from Lean v4.30.0-rc1 to Lean v4.33.1)

import Mathlib
import Definitions.Def_ConsistentSubmodular_MainStatements

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

variable {m : ℕ}

@[simp] theorem mix_zero (p q : Point m) : mix p q 0 = p := by
  funext i
  simp [mix]

@[simp] theorem mix_one (p q : Point m) : mix p q 1 = q := by
  funext i
  simp [mix]

@[simp] theorem mix_self (p : Point m) (x : ℝ) : mix p p x = p := by
  funext i
  simp only [mix]
  ring

theorem mix_swap (p q : Point m) (x : ℝ) : mix p q x = mix q p (1 - x) := by
  funext i
  simp only [mix]
  ring

theorem mix_mix_right (p q : Point m) (x y : ℝ) :
    mix (mix p q x) q y = mix p q ((1 - y) * x + y) := by
  funext i
  simp only [mix]
  ring

theorem simplex_vertex (i : Fin (m + 1)) : IsSimplex (vertex i) := by
  constructor
  · intro j
    simp only [vertex]
    split_ifs <;> norm_num
  · simp [vertex]

theorem IsSimplex.coordinate_le_one {p : Point m} (hp : IsSimplex p)
    (i : Fin (m + 1)) : p i ≤ 1 := by
  rw [← hp.2]
  exact Finset.single_le_sum (fun j _ => hp.1 j) (Finset.mem_univ i)

theorem IsSimplex.mix {p q : Point m} (hp : IsSimplex p) (hq : IsSimplex q)
    {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1) : IsSimplex (mix p q x) := by
  constructor
  · intro i
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr hx') (hp.1 i))
      (mul_nonneg hx (hq.1 i))
  · change (∑ i, ((1 - x) * p i + x * q i)) = 1
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hp.2, hq.2]
    ring

theorem prod_vertex_complement (s : Finset (Fin (m + 1))) (i : Fin (m + 1)) :
    (∏ j ∈ s, (1 - vertex i j)) = if i ∈ s then 0 else 1 := by
  classical
  by_cases hi : i ∈ s
  · simp only [hi, if_pos]
    exact Finset.prod_eq_zero hi (by simp [vertex])
  · simp only [hi, ite_false]
    apply Finset.prod_eq_one
    intro j hj
    have hji : j ≠ i := fun h => hi (h ▸ hj)
    simp [vertex, hji]

theorem prod_mix_vertices_complement (s : Finset (Fin (m + 1)))
    (i j : Fin (m + 1)) (hij : i ≠ j) (x : ℝ) :
    (∏ k ∈ s, (1 - mix (vertex i) (vertex j) x k)) =
      (if i ∈ s then x else 1) * (if j ∈ s then 1 - x else 1) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert k s hk ih =>
      rw [Finset.prod_insert hk, ih]
      by_cases hki : k = i
      · subst k
        simp [mix, vertex, hk, hij, Ne.symm hij]
      · by_cases hkj : k = j
        · subst k
          simp [mix, vertex, hk, hij, Ne.symm hij, mul_comm]
        · simp [mix, vertex, hki, hkj, Ne.symm hki, Ne.symm hkj]

end ConsistentSubmodular

end


