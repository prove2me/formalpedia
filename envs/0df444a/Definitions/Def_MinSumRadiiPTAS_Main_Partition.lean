-- Prove2me | Definitions.Def_MinSumRadiiPTAS_Main_Partition
-- name    : MinSumRadiiPTAS_Main_Partition
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T22:00:56.856039+00:00
-- url     : https://prove2.me/theorems/319c9f43-f033-4db2-b356-38552f52d470
-- title:
--   Nets, the partial low-diameter decomposition, the radii thresholds $a_i$, $\mathrm{lo}_B$, $\mathrm{hi}_B$, FormGroups and the constants $L, U, c_{\max}, r_{\max}$ of §6
-- statement:
--   1. **Net** (p. 9) `IsNet d X N r`: $N \subseteq X$, points of $N$ pairwise more than $r$ apart, every point of $X$ within distance $r$ of $N$.
--   2. **LDD$(X, Y, a, b)$** (p. 9) with the centers $Y$ given as a duplicate-free list $l$ (the "fixed but arbitrary order") and the radius $\ell$: the near part `lddPart d X l ℓ y` $= P_y$ is the set of points of $X$ within distance $\ell$ of $y$ and farther than $\ell$ from every center before $y$ in $l$; the far part `lddFar d X l ℓ` $= P_{\mathrm{far}}$ is the set of points of $X$ farther than $\ell$ from every center.
--   3. **Radii thresholds** (Algorithm 1, pp. 9–10), for a multiplier $L$, an opening cost $\lambda$, a shift $\sigma$ and a target: `thr λ L σ i` $= a_i$ with $a_0 = 0$ and $a_i = \lambda 2^\sigma 2^{L(i-1)}$ for $i \ge 1$; `thrTop λ target L σ` $= t$, the smallest positive integer with $a_t \ge$ target (target $\lceil 10k/\varepsilon \rceil$ in §4, $3R$ in §6.2); `loThr` $= \mathrm{lo}_B = \max\{a_i : i \le t, a_i < r_B\}$ ($0$ when $r_B = 0$) and `hiThr` $= \mathrm{hi}_B = \min\{a_i : i \le t, a_i \ge r_B\}$, as functions of the radius $r = r_B$.
--   4. **FormGroups** (Algorithm 6, p. 17) on a finite simple graph $H$, with $D$ and the random permutation given by the position $\pi(v)$ of every vertex: `fgLeader H D π v` is the first vertex of the permutation within graph distance $D$ of $v$ (distance $\infty$ across components); vertices are in the same group iff they have the same leader. `graphDistToSet H u C` $= d_H(u, C) = \min_{c \in C} d_H(u, c)$. `fgSameGroupProb H U C` is the probability, with $D$ uniform on $\{U+1, \dots, 2U\}$ and the permutation uniform and independent of $D$, that all vertices of $C$ get the same leader.
--   5. **Constants of §6** (p. 24): `L6 ε` $= L = \lceil e^{7100}/\varepsilon\rceil$, `U6 ε` $= U = 2^{3L}$, `cmax ε` $= c_{\max} = 200\, U\, 2^L$, `rmax ε R` $= r_{\max} = c_{\max} R$.
--
--   **Formalization Note** `thrTop` is an infimum of natural numbers; its set is nonempty when $\lambda > 0$ and $L \ge 1$ (otherwise the junk value $0$). `hiThr` is meaningful when $r_B \le a_t$ (otherwise the junk value $0$); Lemma 4.3 assumes it. Algorithm 6 assigns each vertex to the first permutation vertex within distance $D$ (p. 17), which is what the leader encodes.
-- source:
--   Fabrizio Grandoni, Anupam Gupta, Jatin Yadav, A PTAS for the Minimum Sum of Radii Problem, manuscript dated November 3, 2026 (STOC 2027 submission), SHA-256 99b43d49…, pp. 9–10 (Net, LDD, Algorithm 1), p. 17 (Algorithm 6), p. 24 (constants)

import Mathlib
import Definitions.Def_MinSumRadiiPTAS_Main_Basic

open scoped Classical

namespace MinSumRadiiPTAS.Main

/-!
# Nets, the partial low-diameter decomposition, radii thresholds, FormGroups, §6 constants

Grandoni, Gupta, Yadav, *A PTAS for the Minimum Sum of Radii Problem* (STOC 2027 submission,
SHA-256 99b43d49…): p. 9 (Net, LDD), pp. 9–10 (Algorithm 1: thresholds `a_i`, `lo_B`, `hi_B`),
pp. 15–17 (Algorithm 6: FormGroups), p. 24 and p. 26 (the constants `L, U, c_max, r_max` of §6).

**Formalization Note.** The LDD takes the centers `Y` as a duplicate-free list, the "fixed but
arbitrary order" of p. 9, and the radius `ℓ` as an argument; statements put the uniform law on `ℓ`.
The thresholds take the multiplier `L`, the opening cost `λ`, the target (`⌈10k/ε⌉` in §4, `3R` in
§6.2) and `σ ∈ {0, …, L−1}` as arguments. FormGroups takes the random choices `D` and the
permutation (a bijection `V ≃ Fin |V|`, the position of each vertex) as arguments. -/

/-- `N` is an `r`-net of `X` (p. 9): `N ⊆ X`, points of `N` are pairwise more than `r` apart, and
every point of `X` is within distance `r` of some point of `N`. -/
def IsNet {n : ℕ} (d : Fin n → Fin n → ℝ) (X N : Finset (Fin n)) (r : ℝ) : Prop :=
  N ⊆ X ∧ (∀ u ∈ N, ∀ v ∈ N, u ≠ v → r < d u v) ∧ ∀ x ∈ X, ∃ u ∈ N, d u x ≤ r

/-- The near part `P_y` of `LDD(X, Y, a, b)` with radius `ℓ`, the centers listed in the order `l`
(p. 9): the points of `X` within distance `ℓ` of `y` and not within distance `ℓ` of any center that
comes before `y` in `l`. -/
noncomputable def lddPart {n : ℕ} (d : Fin n → Fin n → ℝ) (X : Finset (Fin n)) (l : List (Fin n))
    (ℓ : ℝ) (y : Fin n) : Finset (Fin n) :=
  X.filter (fun p => d y p ≤ ℓ ∧ ∀ y' ∈ l.takeWhile (· ≠ y), ℓ < d y' p)

/-- The far part `P_far = X \ ⋃_{y ∈ Y} P_y` of `LDD(X, Y, a, b)` with radius `ℓ` (p. 9). -/
noncomputable def lddFar {n : ℕ} (d : Fin n → Fin n → ℝ) (X : Finset (Fin n)) (l : List (Fin n))
    (ℓ : ℝ) : Finset (Fin n) :=
  X.filter (fun p => ∀ y ∈ l, ℓ < d y p)

/-- The radii thresholds of Algorithm 1 (p. 10): `a_0 = 0` and `a_i = λ 2^σ 2^{L(i−1)}` for
`i ≥ 1`. -/
noncomputable def thr (lam : ℝ) (L σ : ℕ) (i : ℕ) : ℝ :=
  if i = 0 then 0 else lam * (2 : ℝ) ^ σ * (2 : ℝ) ^ (L * (i - 1))

/-- The top index `t`: the smallest positive integer with `a_t ≥ target` (Algorithm 1, line 5;
target `⌈10k/ε⌉` in §4, `3R` in §6.2). Defined as an infimum of a set of naturals, nonempty when
`λ > 0` and `L ≥ 1`. -/
noncomputable def thrTop (lam target : ℝ) (L σ : ℕ) : ℕ :=
  sInf {j : ℕ | 1 ≤ j ∧ target ≤ thr lam L σ j}

/-- `lo_B = max{a_i : a_i < r_B}` over `i ∈ {0, …, t}`, with `lo_B = 0` when `r_B = 0` (p. 10).
Here `r` is the radius `r_B`. -/
noncomputable def loThr (lam target : ℝ) (L σ : ℕ) (r : ℝ) : ℝ :=
  let S := ((Finset.range (thrTop lam target L σ + 1)).filter (fun i => thr lam L σ i < r)).image
    (thr lam L σ)
  if r ≤ 0 then 0 else if h : S.Nonempty then S.max' h else 0

/-- `hi_B = min{a_i : a_i ≥ r_B}` over `i ∈ {0, …, t}` (p. 10); meaningful when `r_B ≤ a_t`
(otherwise the junk value `0`). -/
noncomputable def hiThr (lam target : ℝ) (L σ : ℕ) (r : ℝ) : ℝ :=
  let S := ((Finset.range (thrTop lam target L σ + 1)).filter (fun i => r ≤ thr lam L σ i)).image
    (thr lam L σ)
  if h : S.Nonempty then S.min' h else 0

/-- FormGroups (Algorithm 6, p. 17) on a finite graph `H` with the radius `D` and the random
permutation given by the position `π v` of each vertex: the leader of `v` is the first vertex of
the permutation within graph distance `D` of `v` (graph distance `∞` across components). Two
vertices are in the same group iff they have the same leader. -/
noncomputable def fgLeader {V : Type*} [Fintype V] (H : SimpleGraph V) (D : ℕ)
    (π : V ≃ Fin (Fintype.card V)) (v : V) : V :=
  let S := (Finset.univ.filter (fun u => H.edist u v ≤ (D : ℕ∞))).image π
  if h : S.Nonempty then π.symm (S.min' h) else v

/-- The graph distance from `u` to a vertex set `C`: `d_H(u, C) = min_{c ∈ C} d_H(u, c)`. -/
noncomputable def graphDistToSet {V : Type*} (H : SimpleGraph V) (u : V) (C : Finset V) : ℕ∞ :=
  ⨅ c ∈ C, H.edist u c

/-- The probability, over `D` uniform on `{U+1, …, 2U}` and an independent uniformly random
permutation of `V(H)`, that all vertices of `C` end up in the same group of FormGroups (p. 17). -/
noncomputable def fgSameGroupProb {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (U : ℕ) (C : Finset V) : ℝ :=
  let Ω := Finset.Icc (U + 1) (2 * U) ×ˢ (Finset.univ : Finset (V ≃ Fin (Fintype.card V)))
  ((Ω.filter (fun Dπ => ∀ u ∈ C, ∀ v ∈ C, fgLeader H Dπ.1 Dπ.2 u = fgLeader H Dπ.1 Dπ.2 v)).card :
      ℝ) / (Ω.card : ℝ)

/-- `L = ⌈e^{7100}/ε⌉` of §6.2, Appendix B and §7 (p. 24, p. 26, p. 28). -/
noncomputable def L6 (ε : ℝ) : ℕ := ⌈Real.exp 7100 / ε⌉₊

/-- `U = 2^{3L}` with the §6 value of `L` (p. 24). -/
noncomputable def U6 (ε : ℝ) : ℕ := 2 ^ (3 * L6 ε)

/-- `c_max = 200 U 2^L` (p. 24). -/
noncomputable def cmax (ε : ℝ) : ℝ := 200 * (U6 ε : ℝ) * (2 : ℝ) ^ (L6 ε)

/-- `r_max = c_max · R` (p. 24). -/
noncomputable def rmax (ε R : ℝ) : ℝ := cmax ε * R

end MinSumRadiiPTAS.Main


