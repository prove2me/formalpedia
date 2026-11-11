-- Prove2me | Definitions.Def_PriceCapacities_LowerBound_HardInstance
-- name    : PriceCapacities_LowerBound_HardInstance
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T00:23:12.273578+00:00
-- url     : https://prove2.me/theorems/2e732d8b-df6e-4c5f-bee6-4c5a1aa2b41b
-- title:
--   The hard instance of §10.1 with the parameter choices of §10.3: groups $P_{aij}$, $Q_{\rm far}$, $Q_{aij}$, $E_{aij}(\theta)$
-- statement:
--   **Construction (§10.1).** Let $D,B,q,d$ be positive integers, $t,\xi,\tau>0$, and $m_x\in\mathbb N$ for $x\in G$ (the pattern set). There are $A=2^D$ **copies**, indexed by the sign vectors $a\in\{-1,1\}^D$ with translation $u_a=a/\sqrt D$; $B$ **columns** (baseline clusters) $j$ and $q$ **rows** $i$. The space is $\mathbb R^\iota$, where the coordinate set $\iota$ is the disjoint union of mutually orthogonal blocks: copy ($D$), cluster ($B$, unit vectors $e_j$), row ($q$, unit vectors $f_i$), pattern ($d$), two circle coordinates, and $n+1$ extra coordinates, where
--   $$n=2AqB\sum_{x\in G}m_x .$$
--   For every copy $a$, row $i$, column $j$, $x\in G$ and sign $\pm$, the location of eq. (22) is
--   $$p^\pm_{aij,x}=u_a+t\,e_j+f_i\pm\xi x .$$
--   It carries $m_x$ input points: the distinct, equally spaced points $p^\pm_{aij,x}+\tau(\cos(\varphi+2\pi r/m_x),\sin(\varphi+2\pi r/m_x))$, $r=0,\dots,m_x-1$, in the two circle coordinates (a circle of radius $\tau$ centred at the location, with an arbitrary phase $\varphi$ per location). The extra coordinates are $0$ on every input point. The group $P_{aij}$ consists of the points of copy $a$, row $i$, column $j$; the input $P$ is the unweighted union of all groups.
--
--   **Neighborhoods and errors (§10.2).** For $\eta>0$ the $\eta$-neighborhood of a finite set $S$ is $\{y:\operatorname{dist}(y,S)\le\eta\}$. For a weighted set $Q$: $Q_{\rm far}$ is the restriction of $Q$ to the points $y$ with $\operatorname{dist}(y,P)>\eta$, and $Q_{aij}$ the restriction of $Q$ to the $\eta$-neighborhood of $P_{aij}$. For a direction $\theta\in\mathbb R^d$ placed in the pattern coordinates, $\varphi_\theta(y)=|\langle\theta,y\rangle|$ and
--   $$E_{aij}(\theta)=\varphi_\theta(Q_{aij})-\varphi_\theta(P_{aij}).$$
--
--   **Parameters (§10.3).** Given $z\ge1$, $k\ge4$, $\varepsilon$, $t\ge2$ and constants $C_z,\kappa_\xi,\kappa_\eta,\kappa_N,\kappa_t$ and $d_0$: $\Lambda=\log(ek/\varepsilon)$, $H=\Lambda^{z+20}$, $q=\lfloor k/4\rfloor$, $B=\min\{q,\lfloor t^2\rfloor\}$; $D$ is the least integer $D\ge1$ with $2^D\ge C_z(tD)^z$; $d$ is the largest even integer $d\ge\max(2,d_0)$ with $N=2^{d-1}<\kappa_N/(\varepsilon tH)^2$; $\xi=\kappa_\xi/d$, $M=\lceil C_z\Lambda\rceil$, $\eta=\kappa_\eta/(DMd^2)$. The multiplicities are $m_x=W_0\omega_x/(2N)$ for an integer $W_0$ and weights $1<\omega_x<2$.
--
--   **Formalization Note.** `InstanceData` holds $D,B,q,d,t,\xi,\tau$, the multiplicities `m` and the phases `φ`; `group g` is $P_{aij}$ for `g = (a, i, j)`, `points` is $P$, `nbhd`, `far`, `near`, `patternEmbed`, `phi`, `projErr` are the objects above. `HardConsts` holds the constants, `hardData c z k ε t m τ φ` the instance with the §10.3 parameters (`copyDim`, `numCols`, `numRows`, `patternDim`, `xiPar`, `interpM`, `etaPar`, `logScale`). $D$ is an `sInf` of a nonempty set of naturals (so the least element); $d$ is an `sSup` and equals $0$ when no admissible $d$ exists, which the lemmas exclude by asserting $d\ge2$. `IsPatternMultiplicity m` says $m_x=W_0\omega_x/(2N)$ with $W_0\in\mathbb N$ and $1<\omega_x<2$. The source requires $A\ge2$, i.e. $D\ge1$ (at $D=0$ the inequality $2^D\ge C_z(tD)^z$ always holds), and $d\ge2$ (§10.1).
-- source:
--   Prabhu, Schwiegelshohn, Shyam, The Price of Capacities for Clustering Coresets, STOC 2027 submission (manuscript sha256 ec35f5ef…), pp. 32–33, §10.1, eq. (22); p. 33, §10.2 (P_aij, Q_far, φ_θ, Q_aij, E_aij(θ)); pp. 34–35, §10.3 (parameters, m_x, τ, extra coordinates)

import Mathlib
import Definitions.Def_PriceCapacities_LowerBound_WeightedSets
import Definitions.Def_PriceCapacities_LowerBound_Fourier
import Definitions.Def_PriceCapacities_LowerBound_Pattern

open scoped BigOperators NNReal

namespace PriceCapacities.LowerBound

/-!
# The hard instance of §10.1 with the parameters of §10.3

Prabhu, Schwiegelshohn, Shyam, *The Price of Capacities for Clustering Coresets*, STOC 2027
submission (manuscript sha256 ec35f5ef…), pp. 32–33, §10.1 (construction, eq. (22)); p. 33, §10.2
(`P_aij`, `Q_far`, `φ_θ`, `Q_aij`, `E_aij(θ)`); pp. 34–35, §10.3 (parameters, `m_x`, `τ`, the
`n + 1` extra coordinates).

**Raw construction (`InstanceData`).** Data: the copy dimension `D` (there are `A = 2^D` copies,
indexed by the sign vectors `a ∈ {−1,1}^D`, with translation `u_a = a/√D`), the number `B` of
baseline clusters (columns `j`), the number `q` of row positions (rows `i`), the pattern dimension
`d` (pattern vectors `x ∈ G`, see `PatternIdx`), the separation `t`, the pattern radius `ξ`, the
circle radius `τ`, the multiplicities `m_x`, and the phases `φ` of the circles. The ambient space
is `ℝ^ι` with mutually orthogonal coordinate blocks
`ι = [copy: D] ⊕ [cluster: B] ⊕ [row: q] ⊕ [pattern: d] ⊕ [circle: 2] ⊕ [extra: n + 1]`,
so `e_j`, `f_i` are coordinate vectors of the cluster and row blocks. The location of eq. (22) is
`p^±_{aij,x} = u_a + t e_j + f_i ± ξ x`; it is realized by the `m_x` points obtained by adding
`τ (cos(φ + 2πr/m_x), sin(φ + 2πr/m_x))` in the two circle coordinates, `r = 0, …, m_x − 1`
(distinct, equally spaced points on a circle of radius `τ` centred at the location; the phase
`φ` may depend on the location). The `n + 1` extra coordinates are zero on every input point, where
`n = 2 A q B Σ_x m_x`.

* `group g` is `P_aij` for `g = (a, i, j)`; `points` is the unweighted input `P`.
* `nbhd η S = {y : dist(y, S) ≤ η}` is the (closed) `η`-neighborhood of a finite set `S`.
* `far Q η = Q_far`: the restriction of `Q` to the points `y` with `dist(y, P) > η`.
* `near Q η g = Q_aij`: the restriction of `Q` to the `η`-neighborhood of `P_aij`.
* `patternEmbed θ` places `θ ∈ ℝ^d` in the pattern coordinates; `phi θ y = φ_θ(y) = |⟨θ, y⟩|`.
* `projErr Q η g θ = E_aij(θ) = φ_θ(Q_aij) − φ_θ(P_aij)`.

**Parameters of §10.3 (`HardConsts`, `hardData`).** The constants `C_z, κ_ξ, κ_η, κ_N, κ_t`
(and the threshold `d_0` of Lemma 10.6) are parameters. With `Λ = log(ek/ε)`, `H = Λ^{z+20}`:
`q = ⌊k/4⌋`, `B = min{q, ⌊t²⌋}`; `D` is the least integer `D ≥ 1` with `2^D ≥ C_z (tD)^z` (the
source requires `A = 2^D ≥ 2`, so `D ≥ 1`; the set is nonempty, so `sInf` is its minimum);
`d` is the largest even `d ≥ max(2, d_0)` with `N = 2^{d−1} < κ_N/(εtH)²` (as `sSup`; it is `0`
when no such `d` exists, which the constants of the lemmas rule out); `ξ = κ_ξ/d`,
`M = ⌈C_z Λ⌉`, `η = κ_η/(D M d²)`. The multiplicities are `m_x = W_0 ω_x/(2N)` with an integer
`W_0` and weights `1 < ω_x < 2` (`IsPatternMultiplicity`).
-/

/-- Data of the raw construction of §10.1. -/
structure InstanceData where
  /-- copy dimension: `A = 2^D` copies -/
  D : ℕ
  /-- number of baseline clusters (columns) -/
  B : ℕ
  /-- number of row positions -/
  q : ℕ
  /-- pattern dimension -/
  d : ℕ
  /-- separation parameter -/
  t : ℝ
  /-- pattern radius -/
  ξ : ℝ
  /-- circle radius -/
  τ : ℝ
  /-- multiplicities `m_x` -/
  m : PatternIdx d → ℕ
  /-- phase of the circle at the location `p^±_{aij,x}` (`true` is `+`) -/
  φ : (Cube D × Fin q × Fin B) → PatternIdx d → Bool → ℝ

namespace InstanceData

variable (I : InstanceData)

/-- `n = 2 A q B Σ_{x ∈ G} m_x`, the number of input points. -/
def n : ℕ := 2 * 2 ^ I.D * I.q * I.B * ∑ x : PatternIdx I.d, I.m x

/-- Coordinates: copy, cluster, row, pattern, circle, and `n + 1` extra coordinates. -/
abbrev Coord : Type := Fin I.D ⊕ Fin I.B ⊕ Fin I.q ⊕ Fin I.d ⊕ Fin 2 ⊕ Fin (I.n + 1)

/-- The ambient Euclidean space. -/
abbrev Space : Type := EuclideanSpace ℝ I.Coord

/-- Group indices `(a, i, j)`: copy `a ∈ {−1,1}^D`, row `i`, column `j`. -/
abbrev GroupIdx : Type := Cube I.D × Fin I.q × Fin I.B

/-- The `r`-th circle point around the location `p^±_{aij,x} = u_a + t e_j + f_i ± ξ x`
(`σ = true` is `+`). -/
noncomputable def point (g : I.GroupIdx) (x : PatternIdx I.d) (σ : Bool) (r : ℕ) : I.Space :=
  WithLp.toLp 2 fun c =>
    match c with
    | Sum.inl l => sgn (g.1 l) / Real.sqrt I.D
    | Sum.inr (Sum.inl j) => if j = g.2.2 then I.t else 0
    | Sum.inr (Sum.inr (Sum.inl i)) => if i = g.2.1 then 1 else 0
    | Sum.inr (Sum.inr (Sum.inr (Sum.inl l))) =>
        (if σ then 1 else -1) * I.ξ * (sgn (x.1 l) / Real.sqrt I.d)
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl l)))) =>
        if (l : ℕ) = 0 then I.τ * Real.cos (I.φ g x σ + 2 * Real.pi * r / I.m x)
        else I.τ * Real.sin (I.φ g x σ + 2 * Real.pi * r / I.m x)
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr _)))) => 0

open Classical in
/-- The group `P_aij`: all circle points around the locations `p^±_{aij,x}`, `x ∈ G`. -/
noncomputable def group (g : I.GroupIdx) : Finset I.Space :=
  (Finset.univ : Finset (PatternIdx I.d)).biUnion fun x =>
    (Finset.univ : Finset (Bool × Fin (I.m x))).image fun p => I.point g x p.1 p.2

open Classical in
/-- The unweighted input set `P`, the union of all groups. -/
noncomputable def points : Finset I.Space :=
  (Finset.univ : Finset I.GroupIdx).biUnion I.group

/-- The closed `η`-neighborhood `{y : dist(y, S) ≤ η}` of a finite set `S`. -/
def nbhd (η : ℝ) (S : Finset I.Space) : Set I.Space :=
  {y | Metric.infDist y (S : Set I.Space) ≤ η}

/-- `Q_far`: the restriction of `Q` to the points farther than `η` from `P`. -/
noncomputable def far (Q : WeightedSet I.Space) (η : ℝ) : WeightedSet I.Space :=
  restrict Q {y | η < Metric.infDist y (I.points : Set I.Space)}

/-- `Q_aij`: the restriction of `Q` to the `η`-neighborhood of `P_aij`. -/
noncomputable def near (Q : WeightedSet I.Space) (η : ℝ) (g : I.GroupIdx) :
    WeightedSet I.Space :=
  restrict Q (I.nbhd η (I.group g))

/-- A vector `θ ∈ ℝ^d` placed in the pattern coordinates. -/
noncomputable def patternEmbed (θ : EuclideanSpace ℝ (Fin I.d)) : I.Space :=
  WithLp.toLp 2 fun c =>
    match c with
    | Sum.inr (Sum.inr (Sum.inr (Sum.inl l))) => θ l
    | _ => 0

/-- `φ_θ(y) = |⟨θ, y⟩|` for a direction `θ` in the pattern coordinates. -/
noncomputable def phi (θ : EuclideanSpace ℝ (Fin I.d)) (y : I.Space) : ℝ :=
  |inner ℝ (I.patternEmbed θ) y|

/-- `E_aij(θ) = φ_θ(Q_aij) − φ_θ(P_aij)`. -/
noncomputable def projErr (Q : WeightedSet I.Space) (η : ℝ) (g : I.GroupIdx)
    (θ : EuclideanSpace ℝ (Fin I.d)) : ℝ :=
  wsum (I.near Q η g) (I.phi θ) - wsum (unweighted (I.group g)) (I.phi θ)

end InstanceData

/-- The constants of §10.3: `C_z` (large), `κ_ξ, κ_η, κ_N, κ_t` (small), and the threshold `d_0`
of Lemma 10.6. -/
structure HardConsts where
  Cz : ℝ
  κξ : ℝ
  κη : ℝ
  κN : ℝ
  κt : ℝ
  d0 : ℕ

/-- `Λ = log(ek/ε)`. -/
noncomputable def logScale (k : ℕ) (ε : ℝ) : ℝ :=
  Real.log (Real.exp 1 * k / ε)

/-- `q = ⌊k/4⌋`. -/
def numRows (k : ℕ) : ℕ := k / 4

/-- `B = min{q, ⌊t²⌋}`. -/
noncomputable def numCols (k : ℕ) (t : ℝ) : ℕ := min (k / 4) ⌊t ^ 2⌋₊

/-- `D`: the least integer `D ≥ 1` with `2^D ≥ C_z (tD)^z`. -/
noncomputable def copyDim (c : HardConsts) (z : ℕ) (t : ℝ) : ℕ :=
  sInf {D : ℕ | 1 ≤ D ∧ c.Cz * (t * D) ^ z ≤ (2 : ℝ) ^ D}

/-- `d`: the largest even `d ≥ max(2, d_0)` with `2^{d−1} < κ_N/(εtH)²`, `H = Λ^{z+20}`. -/
noncomputable def patternDim (c : HardConsts) (z k : ℕ) (ε t : ℝ) : ℕ :=
  sSup {d : ℕ | Even d ∧ 2 ≤ d ∧ c.d0 ≤ d ∧
    (2 : ℝ) ^ (d - 1) < c.κN / (ε * t * logScale k ε ^ (z + 20)) ^ 2}

/-- `ξ = κ_ξ/d`. -/
noncomputable def xiPar (c : HardConsts) (z k : ℕ) (ε t : ℝ) : ℝ :=
  c.κξ / patternDim c z k ε t

/-- `M = ⌈C_z Λ⌉`. -/
noncomputable def interpM (c : HardConsts) (k : ℕ) (ε : ℝ) : ℕ :=
  ⌈c.Cz * logScale k ε⌉₊

/-- `η = κ_η/(D M d²)`. -/
noncomputable def etaPar (c : HardConsts) (z k : ℕ) (ε t : ℝ) : ℝ :=
  c.κη / ((copyDim c z t : ℝ) * interpM c k ε * (patternDim c z k ε t : ℝ) ^ 2)

/-- The multiplicities are `m_x = W_0 ω_x/(2N)` for an integer `W_0` and weights `1 < ω_x < 2`. -/
def IsPatternMultiplicity {d : ℕ} (m : PatternIdx d → ℕ) : Prop :=
  ∃ (W0 : ℕ) (ω : PatternIdx d → ℝ), (∀ x, 1 < ω x ∧ ω x < 2) ∧
    ∀ x, (m x : ℝ) = (W0 : ℝ) * ω x / (2 * (patternCount d : ℝ))

/-- The hard instance with the parameter choices of §10.3, multiplicities `m`, circle radius `τ`
and circle phases `φ`. -/
noncomputable def hardData (c : HardConsts) (z k : ℕ) (ε t : ℝ)
    (m : PatternIdx (patternDim c z k ε t) → ℕ) (τ : ℝ)
    (φ : (Cube (copyDim c z t) × Fin (numRows k) × Fin (numCols k t)) →
      PatternIdx (patternDim c z k ε t) → Bool → ℝ) : InstanceData where
  D := copyDim c z t
  B := numCols k t
  q := numRows k
  d := patternDim c z k ε t
  t := t
  ξ := xiPar c z k ε t
  τ := τ
  m := m
  φ := φ

end PriceCapacities.LowerBound


