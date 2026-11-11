-- Prove2me | Definitions.Def_JinMaoSubsetSum_PartitionSpec
-- name    : JinMaoSubsetSum_PartitionSpec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T10:41:18.942032+00:00
-- url     : https://prove2.me/theorems/b10c1512-0822-42e3-8dea-62dd43fd4d7f
-- title:
--   The guarantees of the partitioning theorem (Theorem 4.2)
-- statement:
--   Fix $d\ge1$, a bound $\Delta\ge2$, a constant $C$ and an exponent $c'$. For a multiset $A$ of integers in $[1,\Delta]$, a **partition as in Theorem 4.2** consists of $A=A_{\mathrm{ex}}\sqcup\bigsqcup_{i=1}^kA_i$, integers $1\le d_1\le\dots\le d_k\le d$, nonempty vector multisets $X_i'\subseteq X_i$ in $\mathbb Z^{d_i}$ (identified with the vectors of $\mathbb Z^d$ vanishing after coordinate $d_i$) with coordinates in $[-\Delta^{c'},\Delta^{c'}]$ and $f(X_i)=A_i$ for $f(x)=x_1$, and vectors $\tau_i$, such that, with $\Gamma_i=L(X_i)$ and $H_i=\operatorname{conv}\bigl(\pm\bigcup_{j\ge i}\Pi_{\mathbb R^{d_i}}(\operatorname{supp}X_j)\bigr)$:
--
--   1. $|A_{\mathrm{ex}}|\le C\Delta^{1/d}\log^2\Delta$ and $k\le C\log\Delta$;
--   2. (i) conditions (4.1) hold for $(\Gamma_i,H_i,f,X_i',X_i)$ with some $\lambda\le C\log\Delta$, and $\tau_i\in\Gamma_i$ satisfies $\tau_i+(\Gamma_i\cap(\operatorname{rank}\Gamma_i)H_i)\subseteq\Sigma(X_i')$;
--   3. (ii) $|X_i'|\le C\Delta^{1/d}$;
--   4. (iii) $\bigcup_{j\ge i}\Pi_{\mathbb R^{d_i}}(\operatorname{supp}X_j)\subseteq\Gamma_i$;
--   5. (iv) $\sum_{j\le i}|A_j|\le C|A_i|\log\Delta$.
--
--   **Formalization Note** The input multiset is a pair list `lA`; $A_{\mathrm{ex}}$ and the $A_i$ are multiplicity lists aligned with it and the partition is the multiset identity $A_{\mathrm{ex}}+\sum_iA_i=A$. A group (`GroupOut`) lists the support of $X_i$ as triples (vector, multiplicity in $X_i$, multiplicity in $X_i'$) with distinct vectors and positive $X_i$-multiplicities. $\Pi_{\mathbb R^{d_i}}$ is `projFirst d_i`, $\log=\log_2$, groups are indexed from $0$. `PartOut.words` is the output layout ($k$, $A_{\mathrm{ex}}$, then per group $d_i$, $A_i$, the support with both multiplicities by the first $d_i$ coordinates, and the first $d_i$ coordinates of $\tau_i$).
-- source:
--   Jin, Mao, Subset Sum in Almost-Linear Time, arXiv:2610.20742v1 (sha256 8b604948862d9188e922b8abf95831fde3a3699e26d39177d20a1460e31a926a), Theorem 4.2, pp.18–19 (PDF pp.20–21)

import Mathlib
import Definitions.Def_JinMaoSubsetSum_Cond41

set_option autoImplicit false

namespace JinMaoSubsetSum

open scoped Pointwise

/-!
# The output of the partitioning theorem (Theorem 4.2)

Jin, Mao, *Subset Sum in Almost-Linear Time*, arXiv:2610.20742v1, Theorem 4.2, pp.18–19: "Let
d ≥ 1 be given. Let e_1, . . . , e_d be the standard basis of ℝ^d, and for 1 ≤ d′ ≤ d identify
ℝ^{d′} with the subspace span{e_1, . . . , e_{d′}} of ℝ^d. Given a nonempty multiset A of ∆^{O(1)}
integers in [1, ∆], we can construct in Õ_d(∆^{1+2/d}) time a partition into submultisets,
A = A_ex ⊔ ⨆_{i=1}^k A_i, where |A_ex| = O_d(∆^{1/d} log² ∆), k = O_d(log ∆), integers
1 ≤ d_1 ≤ d_2 ≤ · · · ≤ d_k ≤ d, and nonempty vector multisets X′_i, X_i with X′_i ⊆ X_i, such
that supp(X_i) ⊆ (ℤ ∩ [−∆^{O(1)}, ∆^{O(1)}])^{d_i} and f(X_i) = A_i, where f : ℝ^d → ℝ is given by
f(x) = x_1, and, for i ∈ [k], writing Γ_i := L(X_i) and H_i := conv(± ⋃_{j=i}^k Π_{ℝ^{d_i}}(supp
X_j)), the following properties hold: (i) The conditions in (4.1) hold for
(Γ, H, f, X′, X) = (Γ_i, H_i, f|span(Γ_i), X′_i, X_i) with λ = O_d(log ∆). Moreover, the algorithm
also returns τ_i ∈ Γ_i witnessing (4.1c), i.e., τ_i + (Γ_i ∩ (rank Γ_i)H_i) ⊆ Σ(X′_i). (ii)
|X′_i| = O_d(∆^{1/d}). (iii) For each i ∈ [k], ⋃_{j=i}^k Π_{ℝ^{d_i}}(supp X_j) ⊆ Γ_i. (iv) For
1 ≤ i ≤ k, Σ_{j=1}^i |A_j| = O_d(|A_i| log ∆)."

**Formalization Note.**
* The input multiset `A` is listed by pairs `lA` (element, multiplicity). The parts `A_ex`, `A_i`
  are given by multiplicity lists aligned with `lA`, and the partition is the multiset identity
  `A_ex + Σ_i A_i = A`.
* As in the paper, `ℤ^{d_i}` is identified with the vectors of `ℤ^d` whose coordinates
  `d_i + 1, …, d` vanish (0-based: coordinates `j ≥ d_i` are `0`); `Π_{ℝ^{d_i}}` is `projFirst d_i`.
  The groups are indexed `i = 0, …, k − 1`.
* A group `g` lists the support of `X_i` as triples `(x, µ_{X_i}(x), µ_{X′_i}(x))` with distinct
  `x` and `µ_{X_i}(x) > 0`; `X_i = g.X` and `X′_i = g.X'` are the multisets they list.
* `f(x) = x_1` is `linOf e₀` on `ℝ^d` and `linZ e₀` on `ℤ^d` (`e₀` the indicator of coordinate
  `0`); `f(X_i) = A_i` is equality of multisets (multiplicities preserved).
* Every `O_d(·)` is the single constant `C` (and the exponent `c'` of `∆^{O(1)}`), fixed before the
  instance by the theorem using this definition; `log` is `log₂`. "Conditions (4.1) hold with
  `λ = O_d(log ∆)`" is: they hold for some `λ ≤ C log₂ ∆` (`Cond41` includes `λ ≥ 1`).
* Output words (`PartOut.words`): `k`; the multiplicities of `A_ex`; then for each group `d_i`, the
  multiplicities of `A_i`, the number of support vectors of `X_i`, each support vector by its
  first `d_i` coordinates followed by `µ_{X_i}` and `µ_{X′_i}`, and the first `d_i` coordinates
  of `τ_i`.
-/

/-- One group of the partition: `d_i`, the multiplicities of `A_i` (aligned with the input list),
the support of `X_i` with multiplicities in `X_i` and in `X′_i`, and `τ_i`. -/
structure GroupOut (d : ℕ) where
  dim : ℕ
  amult : List ℕ
  vecs : List ((Fin d → ℤ) × ℕ × ℕ)
  tau : Fin d → ℤ

/-- The partition: the multiplicities of `A_ex` and the groups `1, …, k`. -/
structure PartOut (d : ℕ) where
  aex : List ℕ
  groups : List (GroupOut d)

/-- The multiset `X_i`. -/
def GroupOut.X {d : ℕ} (g : GroupOut d) : Multiset (Fin d → ℤ) :=
  ofPairs (g.vecs.map (fun v => (v.1, v.2.1)))

/-- The multiset `X′_i`. -/
def GroupOut.X' {d : ℕ} (g : GroupOut d) : Multiset (Fin d → ℤ) :=
  ofPairs (g.vecs.map (fun v => (v.1, v.2.2)))

/-- The indicator `e₀` of coordinate `0`, so that `f(x) = x_1` is `x ↦ Σ_j (e₀)_j x_j`. -/
def firstCoord (d : ℕ) : Fin d → ℤ := fun j => if j.val = 0 then 1 else 0

/-- The output words of a partition. -/
def PartOut.words {d : ℕ} (out : PartOut d) : List ℤ :=
  (out.groups.length : ℤ) :: (out.aex.map (fun m => (m : ℤ)) ++
    out.groups.flatMap (fun g =>
      (g.dim : ℤ) :: (g.amult.map (fun m => (m : ℤ)) ++ (g.vecs.length : ℤ) ::
        (g.vecs.flatMap (fun v => (List.ofFn v.1).take g.dim ++ [(v.2.1 : ℤ), (v.2.2 : ℤ)]) ++
          (List.ofFn g.tau).take g.dim))))

/-- **The guarantees of Theorem 4.2** for the input list `lA`, the dimension parameter `d`, the
bound `∆`, the constant `C` of every `O_d(·)` and the exponent `c'` of `∆^{O(1)}`. -/
def PartitionSpec (d Δ : ℕ) (C c' : ℝ) (lA : List (ℤ × ℕ)) (out : PartOut d) : Prop :=
  let G := out.groups
  let k := G.length
  let f : (Fin d → ℝ) →ₗ[ℝ] ℝ := linOf (firstCoord d)
  let Xr : Fin k → Multiset (Fin d → ℝ) := fun i => (G.get i).X.map toR
  let X'r : Fin k → Multiset (Fin d → ℝ) := fun i => (G.get i).X'.map toR
  let suff : Fin k → Set (Fin d → ℝ) := fun i =>
    {y | ∃ j : Fin k, i ≤ j ∧ ∃ x ∈ Xr j, y = projFirst (G.get i).dim x}
  let Γ : Fin k → AddSubgroup (Fin d → ℝ) := fun i => latticeGen {x | x ∈ Xr i}
  let H : Fin k → Set (Fin d → ℝ) := fun i => symmHull (suff i)
  let Ai : Fin k → Multiset ℤ := fun i => subOfPairs lA (G.get i).amult
  -- the partition A = A_ex ⊔ ⨆ A_i
  out.aex.length = lA.length ∧ (∀ g ∈ G, g.amult.length = lA.length) ∧
  subOfPairs lA out.aex + (G.map (fun g => subOfPairs lA g.amult)).sum = ofPairs lA ∧
  -- |A_ex| = O_d(∆^{1/d} log² ∆), k = O_d(log ∆)
  (Multiset.card (subOfPairs lA out.aex) : ℝ) ≤
    C * (Δ : ℝ) ^ ((1 : ℝ) / d) * (Real.logb 2 Δ) ^ 2 ∧
  (k : ℝ) ≤ C * Real.logb 2 Δ ∧
  -- 1 ≤ d_1 ≤ ⋯ ≤ d_k ≤ d
  (G.map GroupOut.dim).Pairwise (· ≤ ·) ∧ (∀ g ∈ G, 1 ≤ g.dim ∧ g.dim ≤ d) ∧
  ∀ i : Fin k,
    -- X_i, X′_i: nonempty, X′_i ⊆ X_i, listed by distinct support vectors
    (G.get i).vecs ≠ [] ∧ ((G.get i).vecs.map Prod.fst).Nodup ∧
    (∀ v ∈ (G.get i).vecs, 0 < v.2.1 ∧ v.2.2 ≤ v.2.1) ∧ (G.get i).X' ≠ 0 ∧
    -- supp(X_i) ⊆ (ℤ ∩ [−∆^{O(1)}, ∆^{O(1)}])^{d_i}
    (∀ v ∈ (G.get i).vecs, ∀ j : Fin d,
      ((G.get i).dim ≤ j.val → v.1 j = 0) ∧ |((v.1 j : ℤ) : ℝ)| ≤ (Δ : ℝ) ^ c') ∧
    -- f(X_i) = A_i
    (G.get i).X.map (linZ (firstCoord d)) = Ai i ∧
    -- (i) conditions (4.1) with λ = O_d(log ∆), and τ_i witnessing (4.1c)
    (∃ lam : ℝ, lam ≤ C * Real.logb 2 Δ ∧ Cond41 (Γ i) (H i) f (X'r i) (Xr i) lam Δ) ∧
    toR (G.get i).tau ∈ Γ i ∧
    (∀ y ∈ Γ i, y ∈ (rankOf (Γ i) : ℝ) • H i → toR (G.get i).tau + y ∈ subsetSums (X'r i)) ∧
    -- (ii) |X′_i| = O_d(∆^{1/d})
    (Multiset.card (G.get i).X' : ℝ) ≤ C * (Δ : ℝ) ^ ((1 : ℝ) / d) ∧
    -- (iii) ⋃_{j ≥ i} Π_{ℝ^{d_i}}(supp X_j) ⊆ Γ_i
    suff i ⊆ (Γ i : Set (Fin d → ℝ)) ∧
    -- (iv) Σ_{j ≤ i} |A_j| = O_d(|A_i| log ∆)
    ((∑ j ∈ Finset.univ.filter (fun j : Fin k => j ≤ i), Multiset.card (Ai j) : ℕ) : ℝ) ≤
      C * (Multiset.card (Ai i) : ℝ) * Real.logb 2 Δ

end JinMaoSubsetSum


