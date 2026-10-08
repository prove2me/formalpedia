-- Prove2me | Definitions.Def_AssocRealizations_SantosFan_Setting
-- name    : AssocRealizations_SantosFan_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T10:17:44.627735+00:00
-- url     : https://prove2.me/theorems/f35c3705-b3ae-49c8-8b2e-ebbd52695c36
-- title:
--   §2 (p. 5), §5 (pp. 19, 22–23) — Santos' vectors and fan, complete simplicial fans, normal fans of polytopes, the weight condition of Lemma 5.4
-- statement:
--   This file fixes the objects of Santos' construction of the associahedron and of the statement that it is polytopal.
--
--   **The polygon.** Let $n \ge 0$ and $N = n+3$. The vertices of a convex $N$-gon are the positions $0, 1, \dots, N-1$ in counterclockwise order. A *chord* is an unordered pair of positions; a *diagonal* joins two distinct, non-adjacent positions; two chords *cross* when their four endpoints are distinct and alternate around the boundary; a *triangulation* is a maximal set of pairwise non-crossing diagonals (it has $n$ elements). These are the published conventions of `ChvatalArtGallery.FanPartition.Triangulation`.
--
--   **Santos' vectors (p. 19).** Fix a seed triangulation $T_0$ and let $V = \mathbb R^{T_0}$, with basis $(\alpha_\delta)_{\delta \in T_0}$. To each chord $pq$ associate
--   $$v_{pq} = \begin{cases} -\alpha_\delta & \text{if } pq = \delta \in T_0,\\ \displaystyle\sum_{\delta \in T_0,\ pq \text{ crosses } \delta} \alpha_\delta & \text{if } pq \notin T_0.\end{cases}$$
--   For a set $D$ of diagonals write $\mathbb R_{\ge 0} D$ for the cone (nonnegative hull) of $\{v_e : e \in D\}$. The fan $\mathcal F_{T_0}$ is the set of cones $\mathbb R_{\ge 0} D$ over all sets $D$ of pairwise non-crossing diagonals, including $D = \emptyset$, whose cone is $\{0\}$.
--
--   **Complete simplicial fans.** For a family $(v_e)$ of vectors indexed by the chords, the cones $\mathbb R_{\ge0}T$ of the triangulations $T$ *form a complete simplicial fan* when: (i) for each triangulation $T$ the vectors $v_e$, $e \in T$, are linearly independent; (ii) every vector of the space lies in some $\mathbb R_{\ge 0}T$; (iii) for any two triangulations, $\mathbb R_{\ge0}T \cap \mathbb R_{\ge0}T' = \mathbb R_{\ge0}(T \cap T')$.
--
--   **Normal fans (p. 5).** For a set $P \subseteq \mathbb R^\iota$ and $x \in P$, the exterior normal cone is
--   $$N_P(x) = \Big\{c : \textstyle\sum_i c_i y_i \le \sum_i c_i x_i \text{ for all } y \in P\Big\}.$$
--   A family $\mathcal F$ of cones is the *normal fan* of $P$ when $P$ is the convex hull of finitely many points and $\mathcal F = \{N_P(x) : x \in P\}$ (the normal cone of a face is that of any of its relative-interior points, so this is the set of normal cones of all nonempty faces).
--
--   **Condition (2) of Lemma 5.4.** A weight $\omega$ on the chords satisfies the condition for $(v_e)$ when $\omega > 0$ on every diagonal, and for every two triangulations $T_1, T_2$ with $T_1\setminus T_2 = \{v_1\}$, $T_2 \setminus T_1 = \{v_2\}$ (adjacent maximal cones) and every $\lambda$ with $\sum_{e \in T_1\cup T_2} \lambda_e v_e = 0$, $\lambda_{v_1} > 0$, $\lambda_{v_2} > 0$, one has $\sum_{e \in T_1 \cup T_2} \lambda_e \omega_e > 0$.
--
--   **The weights of p. 23.** $g_{ij} = (j-i)(n+3+i-j)$ for integers $i, j$; on a chord with positions $a < b$ this is $g = (b-a)(N+a-b)$, the paper's $g_{ij}$ for $i = a+1$, $j = b+1$. For $\varepsilon \in \mathbb R$, $\omega_{ij} = 2$ if $ij \in T_0$ and $\omega_{ij} = 1 + \varepsilon g_{ij}$ otherwise.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** $V$ is `{d // d ∈ T₀} → ℝ`: coordinate $d$ is the coefficient of $\alpha_d$, so the basis is indexed by the seed diagonals themselves. Cones are `PointedCone.hull ℝ` (nonnegative spans). Linear functionals on $\mathbb R^\iota$ are identified with vectors by the coordinate pairing $\sum_i c_i y_i$; since the polytope is only asserted to exist, the choice of this identification does not matter. On a chord, $g$ is computed as `cdist a b * cdist b a`, which is symmetric and equals $(b-a)(N+a-b)$ for $a<b$.
-- source:
--   Ceballos, Santos and Ziegler, Many non-equivalent realizations of the associahedron, arXiv:1109.5544v2, p. 5 (§2, normal fans), p. 19 (vectors v_pq, Theorem 5.1), p. 22 (Lemma 5.4 (2)), p. 23 (weights ω_ij, g_ij)

import Mathlib
import Definitions.Def_ChvatalArtGallery_FanPartition_Triangulation
import Definitions.Def_AssocRealizations_TypesMeet_Setting

namespace AssocRealizations.SantosFan

open ChvatalArtGallery.FanPartition

/-!
Ceballos, Santos and Ziegler, *Many non-equivalent realizations of the associahedron*,
arXiv:1109.5544v2: normal fans (§2, p. 5), Santos' vectors (§5, p. 19), complete simplicial fans
(Theorem 5.1, p. 19), condition (2) of Lemma 5.4 (p. 22) and the weights of p. 23.

The convex `N`-gon (`N = n + 3`) has vertex set `Fin N`, read as positions in counterclockwise
boundary order (the convention of `ChvatalArtGallery.FanPartition`); chords are elements of
`Sym2 (Fin N)`. The ambient space of Santos' construction for a seed triangulation `T₀` is
`{d // d ∈ T₀} → ℝ`: coordinate `d` is the coefficient of the basis vector `α_d`.
-/

/-- The cone `ℝ≥0 T` of a set `T` of diagonals (of a triangulation, for the maximal cones). -/
def maxCone {N : ℕ} (T₀ T : Finset (Sym2 (Fin N))) : Set ({d // d ∈ T₀} → ℝ) :=
  (PointedCone.hull ℝ (AssocRealizations.TypesMeet.santosVec T₀ '' (↑T : Set (Sym2 (Fin N)))) : Set ({d // d ∈ T₀} → ℝ))

/-- The cones `ℝ≥0 T`, `T` a triangulation of the `N`-gon, form a complete simplicial fan:
the vectors of each triangulation are linearly independent (simplicial), every point of `V` lies
in some cone (complete), and two such cones meet in the cone of their common diagonals (fan). -/
def IsCompleteSimplicialFan {N : ℕ} {V : Type*} [AddCommGroup V] [Module ℝ V]
    (v : Sym2 (Fin N) → V) : Prop :=
  (∀ T : Finset (Sym2 (Fin N)), IsTriangulation N T →
      LinearIndependent ℝ (fun e : {e // e ∈ T} => v e.1)) ∧
  (∀ x : V, ∃ T : Finset (Sym2 (Fin N)), IsTriangulation N T ∧
      x ∈ PointedCone.hull ℝ (v '' (↑T : Set (Sym2 (Fin N))))) ∧
  (∀ T T' : Finset (Sym2 (Fin N)), IsTriangulation N T → IsTriangulation N T' →
      ((PointedCone.hull ℝ (v '' (↑T : Set (Sym2 (Fin N)))) : Set V) ∩
          (PointedCone.hull ℝ (v '' (↑T' : Set (Sym2 (Fin N)))) : Set V) =
        (PointedCone.hull ℝ (v '' (↑(T ∩ T') : Set (Sym2 (Fin N)))) : Set V)))

/-- The exterior normal cone of `P` at `x`: the linear functionals `c` (paired with points by
`⟪c, y⟫ = ∑ i, c i * y i`) that attain their maximum over `P` at `x`. -/
def normalCone {ι : Type*} [Fintype ι] (P : Set (ι → ℝ)) (x : ι → ℝ) : Set (ι → ℝ) :=
  {c | ∀ y ∈ P, ∑ i, c i * y i ≤ ∑ i, c i * x i}

/-- `F` is the normal fan of the polytope `P` (p. 5): `P` is the convex hull of finitely many
points, and the cones of `F` are exactly the exterior normal cones of `P` at its points (the
normal cone of a face is that of any of its relative-interior points). -/
def IsNormalFanOf {ι : Type*} [Fintype ι] (F : Set (Set (ι → ℝ))) (P : Set (ι → ℝ)) : Prop :=
  (∃ S : Finset (ι → ℝ), P = convexHull ℝ (↑S : Set (ι → ℝ))) ∧
  F = {C | ∃ x ∈ P, C = normalCone P x}

/-- Condition (2) of Lemma 5.4 for the fan of `v`: `ω` is positive on the diagonals (the
generators), and for every pair of adjacent maximal cones, i.e. triangulations `T₁`, `T₂` with
`T₁ \ T₂ = {v₁}` and `T₂ \ T₁ = {v₂}`, every linear dependence `c` among the vectors of `T₁ ∪ T₂`
that is positive at `v₁` and `v₂` has `∑ c(e) ω(e) > 0`. -/
def WeightCondition {N : ℕ} {V : Type*} [AddCommGroup V] [Module ℝ V]
    (v : Sym2 (Fin N) → V) (ω : Sym2 (Fin N) → ℝ) : Prop :=
  (∀ e : Sym2 (Fin N), IsDiagonal e → 0 < ω e) ∧
  ∀ (T₁ T₂ : Finset (Sym2 (Fin N))) (v₁ v₂ : Sym2 (Fin N)),
    IsTriangulation N T₁ → IsTriangulation N T₂ → T₁ \ T₂ = {v₁} → T₂ \ T₁ = {v₂} →
    ∀ c : Sym2 (Fin N) → ℝ, ∑ e ∈ T₁ ∪ T₂, c e • v e = 0 → 0 < c v₁ → 0 < c v₂ →
      0 < ∑ e ∈ T₁ ∪ T₂, c e * ω e

/-- The paper's `g_ij = (j - i)(n + 3 + i - j)` (p. 23), as integers. -/
def gW (n : ℕ) (i j : ℤ) : ℤ := (j - i) * ((n : ℤ) + 3 + i - j)

/-- `g` on a chord `s(a, b)` of the `N`-gon: `cdist a b * cdist b a`, which for positions
`a < b` equals `(b - a)(N + a - b)`, the paper's `g_ij` with `i = a + 1`, `j = b + 1`. -/
def gDiag {N : ℕ} (e : Sym2 (Fin N)) : ℝ :=
  Sym2.lift ⟨fun a b => ((cdist a b : ℕ) : ℝ) * ((cdist b a : ℕ) : ℝ),
    fun _ _ => mul_comm _ _⟩ e

/-- The weights of p. 23: `ω_ij = 2` on the seed diagonals and `ω_ij = 1 + ε g_ij` otherwise. -/
def santosWeight {N : ℕ} (T₀ : Finset (Sym2 (Fin N))) (ε : ℝ) (e : Sym2 (Fin N)) : ℝ :=
  if e ∈ T₀ then 2 else 1 + ε * gDiag e

end AssocRealizations.SantosFan


