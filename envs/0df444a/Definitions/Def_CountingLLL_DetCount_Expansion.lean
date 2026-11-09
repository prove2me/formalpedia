-- Prove2me | Definitions.Def_CountingLLL_DetCount_Expansion
-- name    : CountingLLL_DetCount_Expansion
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:47:16.511786+00:00
-- url     : https://prove2.me/theorems/fe0403ea-0735-4e3c-a262-5de805238676
-- title:
--   Dependency graphs, Algorithm 1, free constraints, $f(\boldsymbol x)$ and the truncated estimator $\hat r^{(L)}$
-- statement:
--   Fix a CSP formula $\Phi$ and a family $\mathcal E$ of its constraints.
--
--   1. The **dependency graph** $G(\mathcal E)$ has vertex set $\mathcal E$; distinct $c,c'\in\mathcal E$ are adjacent iff $\mathrm{vbl}(c)\cap\mathrm{vbl}(c')\ne\emptyset$. $\Gamma^+_{\mathcal E}(S)$ and $\Gamma^{\le2}_{\mathcal E}(S)$ are the constraints of $\mathcal E$ at distance at most $1$, respectively $2$, from $S$. $\mathfrak T_{\mathcal E,c}$ is the family of 2-trees of $G(\mathcal E)$ containing $c$.
--   2. **Algorithm 1**, $\mathrm{Tree}_{\mathcal E,c_0}(\mathcal D)$: start from $R=\emptyset$, $T=\{c_0\}$; while some $c\in\mathcal E\setminus R$ has $\mathrm{dist}_{G(\mathcal E)}(c,T)=2$, take the lowest-index such $c$ and add it to $T$ if $c\in\mathcal D$, to $R$ otherwise; return $T$. $R(T)$ is the final rejected set of the run on input $T$, and $\mathrm{free}(T)=\mathcal E\setminus(T\cup R(T))$ (Definition 3.3).
--   3. $\ell^T=|\mathcal E\setminus(\{c_0\}\cup\mathrm{free}(T))|$; for an enumeration $c^T_1,\dots,c^T_{\ell^T}$ of that set, $\mathcal C^T_i=\mathrm{free}(T)\cup\{c^T_1,\dots,c^T_i\}$. $\mathrm{free}^{(1)}(T)=\{c\in\mathrm{free}(T):\mathrm{dist}_{G(\mathcal E)}(c,T)=1\}$.
--   4. For a vector $\boldsymbol x$ indexed by pairs $(T,i)$, equation (12) is
--   $$f(\boldsymbol x)=\sum_{T\in\mathfrak T_{\mathcal E,c_0}}(-1)^{|T|-1}\,\mathbb P\Big[\bigwedge_{c\in T}\neg c\;\Big|\;\mathrm{free}(T)\Big]\prod_{i=1}^{\ell^T}\frac{1}{1-x_{\mathcal C^T_i,c^T_i}}.$$
--   5. The **truncated estimator** (20): $\hat r^{(0)}_{\mathcal E,c_0}=0$ and, for $L>0$,
--   $$\hat r^{(L)}_{\mathcal E,c_0}=\sum_{T\in\mathfrak T_{\mathcal E,c_0},\,|T|\le L}(-1)^{|T|-1}\,\mathbb P\Big[\bigwedge_{c\in T}\neg c\;\Big|\;\mathrm{free}(T)\Big]\prod_{i=1}^{\ell^T}\frac{1}{1-\hat r^{(L-|T|)}_{\mathcal C^T_i,c^T_i}},$$
--   defined for every family and every enumeration choice; $\hat r$ without qualification uses the increasing index order.
--
--   These are the objects of the 2-tree expansion (§3) and of the deterministic estimator (§4).
--
--   **Formalization Note** $G(\mathcal E)$ is realised on all constraint indices with the constraints outside $\mathcal E$ isolated. Algorithm 1 is iterated $|\mathcal E|$ times, which reaches its terminal state because each effective iteration moves a fresh constraint of $\mathcal E$ into $T$ or $R$. Vectors $x$ are functions of $(T,i)$ with $0$-based $i<\ell^T$.
-- source:
--   Hongyang Liu, Chunyang Wang, Yitong Yin, Yiyao Zhang, Can Zhou, A Counting and Sampling Lovász Local Lemma, STOC 2027 submission #442 (October 2026), Definition 2.3, Algorithm 1, Definition 3.3, Lemma 3.5, equation (12), equation (20), Lemma 4.2, PDF p. 9 (printed p. 8); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_DetCount_CSP
import Definitions.Def_CountingLLL_DetCount_TwoTree

set_option autoImplicit false

namespace CountingLLL.DetCount

namespace CSP

variable (Φ : CSP)

/-- The dependency graph `G(E)` of a subfamily `E` (Definition 2.3): its vertices are the
constraints of `E`, and distinct `c, c' ∈ E` are adjacent iff `vbl(c) ∩ vbl(c') ≠ ∅`. It is
realised on `Fin m`; constraints outside `E` are isolated vertices, so every walk between members
of `E` stays inside `E`. -/
def depGraph (E : Finset (Fin Φ.m)) : SimpleGraph (Fin Φ.m) where
  Adj c c' := c ∈ E ∧ c' ∈ E ∧ c ≠ c' ∧ Φ.Overlap c c'
  symm := ⟨fun _ _ h => ⟨h.2.1, h.1, h.2.2.1.symm, fun hd => h.2.2.2 hd.symm⟩⟩
  loopless := ⟨fun _ h => h.2.2.1 rfl⟩

/-- `Γ⁺_E(S) = {c ∈ E : dist_{G(E)}(c, S) ≤ 1}`. -/
noncomputable def GammaPlus (E S : Finset (Fin Φ.m)) : Finset (Fin Φ.m) := by
  classical
  exact E.filter (fun c => distSet (Φ.depGraph E) c S ≤ 1)

/-- `Γ^{≤2}_E(S) = {c ∈ E : dist_{G(E)}(c, S) ≤ 2}`. -/
noncomputable def GammaLe2 (E S : Finset (Fin Φ.m)) : Finset (Fin Φ.m) := by
  classical
  exact E.filter (fun c => distSet (Φ.depGraph E) c S ≤ 2)

/-- `𝔗_{E,c}`: all 2-trees of `G(E)` (subsets of `E`) containing `c` (§3.2). -/
noncomputable def twoTrees (E : Finset (Fin Φ.m)) (c : Fin Φ.m) : Finset (Finset (Fin Φ.m)) := by
  classical
  exact E.powerset.filter (fun T => c ∈ T ∧ IsTwoTree (Φ.depGraph E) T)

/-- One iteration of the while loop of Algorithm 1 on the state `(T, R)` (accepted set,
rejected set), for the constraint set `E` and the input set `D`: if some `c ∈ E ∖ R` has
`dist_{G(E)}(c, T) = 2`, the lowest-index such `c` (order of `Fin m`) is added to `T` if
`c ∈ D` and to `R` otherwise; if there is none, the state is unchanged. -/
noncomputable def treeStep (E D : Finset (Fin Φ.m))
    (st : Finset (Fin Φ.m) × Finset (Fin Φ.m)) : Finset (Fin Φ.m) × Finset (Fin Φ.m) := by
  classical
  exact
    let cand := E.filter (fun c => c ∉ st.2 ∧ distSet (Φ.depGraph E) c st.1 = 2)
    if h : cand.Nonempty then
      (if cand.min' h ∈ D then (insert (cand.min' h) st.1, st.2)
        else (st.1, insert (cand.min' h) st.2))
    else st

/-- The run of Algorithm 1, `Tree_{E,c₀}(D)`, from `(T, R) = ({c₀}, ∅)`. Each effective
iteration moves a fresh constraint of `E` into `T` or `R`, so `|E|` iterations reach the
terminal state (after which `treeStep` is the identity). Returns the final `(T, R)`. -/
noncomputable def treeRun (E : Finset (Fin Φ.m)) (c₀ : Fin Φ.m) (D : Finset (Fin Φ.m)) :
    Finset (Fin Φ.m) × Finset (Fin Φ.m) :=
  (Φ.treeStep E D)^[E.card] ({c₀}, ∅)

/-- `Tree_{E,c₀}(D)`: the accepted set returned by Algorithm 1. -/
noncomputable def Tree (E : Finset (Fin Φ.m)) (c₀ : Fin Φ.m) (D : Finset (Fin Φ.m)) :
    Finset (Fin Φ.m) :=
  (Φ.treeRun E c₀ D).1

/-- `R(T)`: the final rejected set of the run of Algorithm 1 on input `T` (Definition 3.3). -/
noncomputable def rejected (E : Finset (Fin Φ.m)) (c₀ : Fin Φ.m) (T : Finset (Fin Φ.m)) :
    Finset (Fin Φ.m) :=
  (Φ.treeRun E c₀ T).2

/-- `free(T) = free_{E,c₀}(T) = E ∖ (T ∪ R(T))` (Definition 3.3). -/
noncomputable def free (E : Finset (Fin Φ.m)) (c₀ : Fin Φ.m) (T : Finset (Fin Φ.m)) :
    Finset (Fin Φ.m) := by
  classical
  exact E \ (T ∪ Φ.rejected E c₀ T)

/-- `E ∖ ({c₀} ∪ free(T))`, the constraints enumerated in Lemma 3.5. -/
noncomputable def rest (E : Finset (Fin Φ.m)) (c₀ : Fin Φ.m) (T : Finset (Fin Φ.m)) :
    Finset (Fin Φ.m) := by
  classical
  exact E \ ({c₀} ∪ Φ.free E c₀ T)

/-- `ℓ^T = |E ∖ ({c₀} ∪ free(T))|`. -/
noncomputable def ell (E : Finset (Fin Φ.m)) (c₀ : Fin Φ.m) (T : Finset (Fin Φ.m)) : ℕ :=
  (Φ.rest E c₀ T).card

/-- For an enumeration `e` of a finite set (position `j : Fin ℓ` holds `c^T_{j+1}`) and a base
family `B`, `prefixFam B e j = B ∪ {e 0, …, e j}`. With `B = free(T)` this is `C^T_{j+1}`. -/
noncomputable def prefixFam {ℓ : ℕ} (B : Finset (Fin Φ.m)) (e : Fin ℓ → Fin Φ.m) (j : Fin ℓ) :
    Finset (Fin Φ.m) := by
  classical
  exact B ∪ (Finset.univ.filter (fun j' : Fin ℓ => j' ≤ j)).image e

/-- The index-order enumeration `c^T_1 < ⋯ < c^T_{ℓ^T}` of `E ∖ ({c₀} ∪ free(T))`
(0-based: position `j` is `c^T_{j+1}`). -/
noncomputable def enumRest (E : Finset (Fin Φ.m)) (c₀ : Fin Φ.m) (T : Finset (Fin Φ.m)) :
    Fin (Φ.ell E c₀ T) → Fin Φ.m :=
  fun j => (Φ.rest E c₀ T).orderEmbOfFin rfl j

/-- `free^{(1)}(T) = {c ∈ free(T) : dist_{G(E)}(c, T) = 1}` (Lemma 4.2). -/
noncomputable def free1 (E : Finset (Fin Φ.m)) (c₀ : Fin Φ.m) (T : Finset (Fin Φ.m)) :
    Finset (Fin Φ.m) := by
  classical
  exact (Φ.free E c₀ T).filter (fun c => distSet (Φ.depGraph E) c T = 1)

/-- The coefficient `P[⋀_{c ∈ T} ¬c | free(T)]` of the 2-tree expansion. -/
noncomputable def treeCoeff (E : Finset (Fin Φ.m)) (c₀ : Fin Φ.m) (T : Finset (Fin Φ.m)) : ℝ :=
  Φ.condProb (Φ.ViolAll T) (Φ.SatAll (Φ.free E c₀ T))

/-- The function `f(x)` of equation (12), for a vector `x` indexed by pairs `(T, i)`:
`x T i` is the coordinate `x_{C^T_{i+1}, c^T_{i+1}}` (0-based `i < ℓ^T`). Coordinates belonging to
different 2-trees are independent even when the pairs `(C^T_i, c^T_i)` coincide. -/
noncomputable def fvec (E : Finset (Fin Φ.m)) (c₀ : Fin Φ.m)
    (x : Finset (Fin Φ.m) → ℕ → ℝ) : ℝ :=
  ∑ T ∈ Φ.twoTrees E c₀, (-1 : ℝ) ^ (T.card - 1) * Φ.treeCoeff E c₀ T *
    ∏ i ∈ Finset.range (Φ.ell E c₀ T), 1 / (1 - x T i)

/-- An enumeration choice: for every family `E`, root `c₀` and set `T`, a map
`Fin ℓ^T → Fin m` (position `j` holds `c^T_{j+1}`). -/
abbrev EnumChoice : Type :=
  (E : Finset (Fin Φ.m)) → (c₀ : Fin Φ.m) → (T : Finset (Fin Φ.m)) → Fin (Φ.ell E c₀ T) → Fin Φ.m

/-- The enumeration choice enumerates `E ∖ ({c₀} ∪ free(T))` for every 2-tree `T ∈ 𝔗_{E,c₀}`
(injective with values in that set, hence a bijection onto it). -/
def ValidEnum (en : Φ.EnumChoice) : Prop :=
  ∀ (E : Finset (Fin Φ.m)) (c₀ : Fin Φ.m), ∀ T ∈ Φ.twoTrees E c₀,
    Function.Injective (en E c₀ T) ∧ ∀ j, en E c₀ T j ∈ Φ.rest E c₀ T

/-- The truncated estimator `r̂^{(L)}_{E,c₀}` of equation (20) for an enumeration choice `en`,
defined for every subfamily `E` and constraint `c₀` by recursion on the budget `L`:
`r̂^{(0)} = 0`, and for `L > 0`
`r̂^{(L)}_{E,c₀} = Σ_{T ∈ 𝔗_{E,c₀}, |T| ≤ L} (−1)^{|T|−1} P[⋀_{c∈T} ¬c | free(T)]
  · ∏_{i=1}^{ℓ^T} 1 / (1 − r̂^{(L−|T|)}_{C^T_i, c^T_i})`,
where `c^T_{j+1} = en E c₀ T j` and `C^T_{j+1} = free(T) ∪ {c^T_1, …, c^T_{j+1}}`. Every 2-tree
containing `c₀` has `|T| ≥ 1`; the guard `0 < T.card` only makes the decrease of the budget
visible to Lean and never fails on the summation range. -/
noncomputable def rhatWith (en : Φ.EnumChoice) : ℕ → Finset (Fin Φ.m) → Fin Φ.m → ℝ
  | 0, _, _ => 0
  | L + 1, E, c₀ =>
    ∑ T ∈ (Φ.twoTrees E c₀).filter (fun T => T.card ≤ L + 1),
      (-1 : ℝ) ^ (T.card - 1) * Φ.treeCoeff E c₀ T *
      ∏ j : Fin (Φ.ell E c₀ T),
        (if 0 < T.card then
          1 / (1 - rhatWith en (L + 1 - T.card) (Φ.prefixFam (Φ.free E c₀ T) (en E c₀ T) j)
            (en E c₀ T j))
        else 1)
termination_by L _ _ => L
decreasing_by all_goals omega

/-- The estimator `r̂^{(L)}_{E,c₀}` with the index-order enumeration `enumRest`
(`c^T_1 < ⋯ < c^T_{ℓ^T}` in the order of `Fin m`), the one computed in Lemma 4.1. -/
noncomputable def rhat (L : ℕ) (E : Finset (Fin Φ.m)) (c₀ : Fin Φ.m) : ℝ :=
  Φ.rhatWith Φ.enumRest L E c₀

end CSP

end CountingLLL.DetCount


