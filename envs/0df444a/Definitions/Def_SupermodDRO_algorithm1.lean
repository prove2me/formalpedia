-- Prove2me | Definitions.Def_SupermodDRO_algorithm1
-- name    : SupermodDRO_algorithm1
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:31:52.02299+00:00
-- url     : https://prove2.me/theorems/e762ca2e-5413-496a-a5fe-ccbfcab3c85c
-- title:
--   Algorithm 1: the worst-case chain $z^1,\dots,z^{2n+1}$ and weights $p$
-- statement:
--   Algorithm 1 takes the data of one scenario and returns $2n+1$ points of the box and $2n+1$ weights. Its state is the **level** $L_i\in\{\text{lower},\text{mean},\text{upper}\}$ of each coordinate (the point $z^j$ has coordinates the values of the levels) and a vector $q^j\in\mathbb R^n$.
--
--   1. Initialization: every coordinate at the lower level ($z^1=\underline z$), $q^1_i$ = mass of the lower level of coordinate $i$, $p_1=\min_i q^1_i$.
--   2. For $j=1,\dots,2n$: let $r_j$ be the smallest index with $q^j_{r_j}=p_j$; set $q^{j+1}=q^j-p_j\mathbf 1$; move coordinate $r_j$ up one level (lower → mean → upper; a coordinate at the upper level stays); reset $q^{j+1}_{r_j}$ to the full mass of the new level of coordinate $r_j$; $p_{j+1}=\min_i q^{j+1}_i$.
--   3. Output: $z^1,\dots,z^{2n+1}$ and $p=(p_1,\dots,p_{2n+1})$.
--
--   The masses of the levels are those of (5) (`levelMass`).
--
--   **Formalization Note** Indices are $0$-based. The algorithm tracks levels rather than values; on a coordinate with $\underline z_i<\mu_i<\overline z_i$ this is the printed algorithm, and on a coordinate with $\underline z_i=\overline z_i$ it uses the corrected masses $(1,0,0)$ (see `levelMass`). The minimum is the real infimum over the coordinates, which is the minimum when $n\ge1$; for $n=0$ the algorithm is undefined in the paper.
-- source:
--   Long, Qi & Zhang, Supermodularity in Two-Stage Distributionally Robust Optimization, author manuscript (June 2022; PDF sha256 9e6840ad…5b09160b02b5e47), Algorithm 1, p.10

import Mathlib
import Definitions.Def_SupermodDRO_levelMass

namespace SupermodDRO

/-- Line 6 of Algorithm 1 on levels: lower → mean, mean → upper, upper unchanged. -/
def levelUp : Fin 3 → Fin 3 :=
  ![1, 2, 2]

/-- **One iteration (lines 4–8) of Algorithm 1.** The state is a level vector `L : Fin n → Fin 3`
(the point `zʲ` has coordinates `levelValue (L i)`) and the vector `qʲ`. With
`pⱼ = min{q₁ʲ, …, qₙʲ}` and `rⱼ` the minimal index with `q_{rⱼ}ʲ = pⱼ`: `L^{j+1} = Lʲ` except that
coordinate `rⱼ` moves up one level (line 6), and `q^{j+1} = qʲ − pⱼ𝟏` except that
`q_{rⱼ}^{j+1}` is the full mass of the new level of coordinate `rⱼ` (line 7).

**Formalization Note** `pⱼ` is the real infimum over `Fin n`, the minimum when `n ≥ 1`. The `else`
branch is never reached for `n ≥ 1` (a finite minimum is attained); it exists only to make the
function total. -/
noncomputable def algorithm1Step {n : ℕ} (μ δ zl zu : Fin n → ℝ)
    (S : (Fin n → Fin 3) × (Fin n → ℝ)) : (Fin n → Fin 3) × (Fin n → ℝ) :=
  open Classical in
  let p := ⨅ i, S.2 i
  if h : ∃ i, S.2 i = p then
    let r := Fin.find (fun i => S.2 i = p) h
    (Function.update S.1 r (levelUp (S.1 r)),
      Function.update (fun i => S.2 i - p) r
        (levelMass (μ r) (δ r) (zl r) (zu r) (levelUp (S.1 r))))
  else (S.1, fun i => S.2 i - p)

/-- **The state of Algorithm 1 before iteration `j + 1`** (`j` is 0-based: `algorithm1State … 0`
is the initialization of line 2, `z¹ = z̲ᵏ`, `q¹ᵢ = ℙ^{k*}(z̃ᵢ = z̲ᵢᵏ)`). -/
noncomputable def algorithm1State {n : ℕ} (μ δ zl zu : Fin n → ℝ) :
    ℕ → (Fin n → Fin 3) × (Fin n → ℝ)
  | 0 => (fun _ => 0, fun i => levelMass (μ i) (δ i) (zl i) (zu i) 0)
  | j + 1 => algorithm1Step μ δ zl zu (algorithm1State μ δ zl zu j)

/-- **Algorithm 1, p.10: the support points `z¹, …, z^{2n+1}`.** Long, Qi & Zhang,
*Supermodularity in Two-Stage Distributionally Robust Optimization*, author manuscript (June 2022),
Algorithm 1 ("algorithm for worst-case distribution"), p.10:

```
 1: Input: 𝓕ᵏ in Equation (4) with given µᵏ, δᵏ, z̲ᵏ, z̄ᵏ
 2: Initialization:
    • denote ℙ^{k*} as the worst-case distribution in Proposition 1 and calculate ℙ^{k*}(z̃ᵢᵏ = w)
      for w ∈ {z̲ᵢᵏ, µᵢᵏ, z̄ᵢᵏ}, i ∈ [n] using Equation (5)
    • z¹ = z̲ᵏ, q¹ = (ℙ^{k*}(z̃₁ᵏ = z̲₁ᵏ), …, ℙ^{k*}(z̃ₙᵏ = z̲ₙᵏ)), p₁ = min{q₁¹, …, qₙ¹} and j = 1
 3: while j ≤ 2n do
 4:   choose rⱼ as the minimal index in [n] such that q_{rⱼ}ʲ = pⱼ
 5:   z^{j+1} = zʲ, q^{j+1} = qʲ − pⱼ𝟏
 6:   update z_{rⱼ}^{j+1} = µ_{rⱼ}ᵏ if its existing value is z̲_{rⱼ}ᵏ, and z_{rⱼ}^{j+1} = z̄_{rⱼ}ᵏ if its
      existing value is µ_{rⱼ}ᵏ
 7:   update q_{rⱼ}^{j+1} = ℙ^{k*}(z̃_{rⱼ} = z_{rⱼ}^{j+1})
 8:   p_{j+1} = min{q₁^{j+1}, q₂^{j+1}, …, qₙ^{j+1}}
 9:   update j = j + 1
10: return z¹, z², …, z^{2n+1} and p = (p₁, p₂, …, p_{2n+1})
```

`algorithm1Point μ δ zl zu j` is `z^{j+1}` (0-based `j : Fin (2n+1)`).

**Formalization Note** The algorithm tracks the *level* of each coordinate (lower, mean, upper)
rather than its value, and reads the masses of the levels from `levelMass`, which gives `(1, 0, 0)`
on a coordinate with `z̲ᵢᵏ = z̄ᵢᵏ` (a correction of the paper's masses `(1, 1, 1)` there; see
`levelMass`). On a coordinate with `z̲ᵢᵏ < µᵢᵏ < z̄ᵢᵏ` levels and values are the same thing, and the
algorithm is the printed one: the minimal index in line 4, the full level mass in line 7, and no
move from the upper level in line 6. Indices are 0-based. -/
noncomputable def algorithm1Point {n : ℕ} (μ δ zl zu : Fin n → ℝ) (j : Fin (2 * n + 1)) :
    Fin n → ℝ :=
  fun i => levelValue (μ i) (zl i) (zu i) ((algorithm1State μ δ zl zu j).1 i)

/-- **Algorithm 1, p.10: the weights `p = (p₁, …, p_{2n+1})`**, `pⱼ = min{q₁ʲ, …, qₙʲ}` (lines 2
and 8). `algorithm1Weight μ δ zl zu j` is `p_{j+1}` (0-based). -/
noncomputable def algorithm1Weight {n : ℕ} (μ δ zl zu : Fin n → ℝ) (j : Fin (2 * n + 1)) : ℝ :=
  ⨅ i, (algorithm1State μ δ zl zu j).2 i

/-- **Algorithm 1, p.10: its output** `(z¹, …, z^{2n+1}; p)`, the pair of `algorithm1Point` and
`algorithm1Weight`. -/
noncomputable def algorithm1 {n : ℕ} (μ δ zl zu : Fin n → ℝ) :
    (Fin (2 * n + 1) → Fin n → ℝ) × (Fin (2 * n + 1) → ℝ) :=
  (algorithm1Point μ δ zl zu, algorithm1Weight μ δ zl zu)

end SupermodDRO


