-- Prove2me | Definitions.Def_PathCount2k_Gaussian
-- name    : PathCount2k_Gaussian
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:43:37.463413+00:00
-- url     : https://prove2.me/theorems/c41f56c2-8053-4dec-bebf-077a1efc34cb
-- title:
--   Defs. 2.4–2.11 — Gaussian vertex vectors and matrices, $\chi(P)$, $Z$, $Y$, $K_k$, $\alpha_D$, $C_k$, median of means
-- statement:
--   The vertex vectors $g_v\sim N(0,I_k)$ are independent across vertices. For an integer $D\ge1$, each position $i\in[k]$ and vertex $v$ carries a matrix $M_{i,v}\in\mathbb R^{D\times D}$ whose entries are independent standard Gaussians divided by $\sqrt D$ (mean $0$, variance $1/D$), independent of the vectors. The **matrix-product path weight** is $\chi(P)=\sqrt D\,b_0^\top M_{1,v_1}\cdots M_{k,v_k}b_0$, the **counting estimator** is
--   $$
--   Z=\sum_{P\in\mathcal P_k}\Delta_P\,\chi(P),\qquad Y=\frac{Z^2}{k!}.
--   $$
--   The constants are $K_k=(k+1)(k+2)/2$, $\alpha_D=1+2/D$ and $C_k=3e^2K_k$. The **matrix-product rows** of Definition 2.11 are $R_h=\sum_{w\in V^t}a_{h,w}\,b_0^\top M_{1,w_1}\cdots M_{t,w_t}$. The **median-of-means estimator** draws independent trials $Y_{j,\ell}$ ($j\in[q]$, $\ell\in[R]$, $q$ odd), sets $\bar Y_j=\frac1R\sum_\ell Y_{j,\ell}$ and $\hat N=\mathrm{median}(\bar Y_1,\dots,\bar Y_q)$.
--
--   These are the objects of the unbiasedness and fourth-moment analysis (§§2.3–2.8).
--
--   **Formalization Note** Matrix entries have law `gaussianReal 0 (1/D)`; the trial space is `(Fin n → Fin k → ℝ) × (Fin k → Fin n → Fin D → Fin D → ℝ)`; the median of $q$ reals is the $(\lfloor q/2\rfloor+1)$-th smallest.
-- source:
--   Panolan, Saurabh, Xue, Zehavi, Counting Paths in Time O*(2^k), with Extensions to Counting Bounded Treewidth Graphs and Multilinear Monomials, STOC 2027 submission manuscript (Nov 2026), Definitions 2.4–2.7, pp.5–6; Definition 2.9, p.7; Lemma 2.5, Corollary 2.1, Definition 2.10, p.8; Definition 2.11, p.9

import Mathlib
import Definitions.Def_PathCount2k_Graph
import Definitions.Def_PathCount2k_Exterior

open MeasureTheory ProbabilityTheory

namespace PathCount2k

/-- A choice of real vertex vectors `g = (g_v)_{v ∈ V}`, `g_v ∈ ℝ^k` (Definition 2.2, p.4). -/
abbrev VecSample (n k : ℕ) := Fin n → Fin k → ℝ

/-- A choice of real auxiliary matrices `M = (M_{i,v})`, `M_{i,v} ∈ ℝ^{D×D}` for every position
`i ∈ [k]` and host vertex `v` (Definition 2.6, p.6). Entry `(a, b)` of `M_{i,v}` is `M i v a b`. -/
abbrev MatSample (n k D : ℕ) := Fin k → Fin n → Fin D → Fin D → ℝ

/-- **The law of the vertex vectors**, Definition 2.5 and §2.3, p.5: "We now choose the vertex
vectors `g_v ∼ N(0, I_k)` independently across vertices": all `n·k` coordinates are independent
standard Gaussian variables (Definition 2.4). -/
noncomputable def vecLaw (n k : ℕ) : Measure (VecSample n k) :=
  Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin k => gaussianReal 0 1

/-- **The law of the auxiliary Gaussian matrices**, Definition 2.6, p.6: every entry of every
`M_{i,v}` is "a standard Gaussian variable divided by `√D`", all entries mutually independent;
"each entry has mean zero and variance `1/D`".

**Formalization Note.** Each entry has law `gaussianReal 0 (1/D)`, the law of `X/√D` for
`X ∼ N(0,1)`. The variance argument of `gaussianReal` is in `ℝ≥0`; theorems assume `1 ≤ D`. -/
noncomputable def matLaw (n k D : ℕ) : Measure (MatSample n k D) :=
  Measure.pi fun _ : Fin k => Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin D =>
    Measure.pi fun _ : Fin D => gaussianReal 0 (D : NNReal)⁻¹

/-- **The joint law of one Gaussian trial**: vertex vectors and auxiliary matrices independent
(Definition 2.6, p.6: "independent of the vertex vectors"). -/
noncomputable def jointLaw (n k D : ℕ) : Measure (VecSample n k × MatSample n k D) :=
  (vecLaw n k).prod (matLaw n k D)

/-- **Matrix-product path weights**, Definition 2.7, p.6:
`χ(P) = √D · b₀ᵀ M_{1,v₁} M_{2,v₂} ⋯ M_{k,v_k} b₀`. -/
noncomputable def chi {n k D : ℕ} (M : MatSample n k D) (P : Fin k → Fin n) : ℝ :=
  Real.sqrt D * pathEntry M P

/-- **The counting estimator `Z`**, Definition 2.9, p.7: `Z = ∑_{P ∈ P_k} Δ_P χ(P)`, as a function
of the trial `ω = (g, M)`. -/
noncomputable def Z (n : ℕ) (E : Finset (Fin n × Fin n)) (k D : ℕ)
    (ω : VecSample n k × MatSample n k D) : ℝ :=
  ∑ P ∈ paths n E k, Delta ω.1 P * chi ω.2 P

/-- **One Gaussian trial**, Definition 2.9, p.7: `Y = Z² / k!`. -/
noncomputable def Y (n : ℕ) (E : Finset (Fin n × Fin n)) (k D : ℕ)
    (ω : VecSample n k × MatSample n k D) : ℝ :=
  Z n E k D ω ^ 2 / (Nat.factorial k : ℝ)

/-- `K_k = (k + 1)(k + 2)/2`, Lemma 2.5, p.8. -/
noncomputable def Kk (k : ℕ) : ℝ := ((k : ℝ) + 1) * ((k : ℝ) + 2) / 2

/-- `α_D = 1 + 2/D`, §2.7, p.8: "Throughout this section, write `α_D = 1 + 2/D`". -/
noncomputable def alpha (D : ℕ) : ℝ := 1 + 2 / (D : ℝ)

/-- `C_k = 3e²K_k`, Corollary 2.1, p.8. -/
noncomputable def Ck (k : ℕ) : ℝ := 3 * Real.exp 2 * Kk k

/-- The squared Euclidean norm `‖r‖² = ∑_a r_a²` of a row of length `D`, Definition 2.8, p.7. -/
def sqNorm {D : ℕ} (r : Fin D → ℝ) : ℝ := ∑ a : Fin D, r a ^ 2

/-- **Matrix-product rows**, Definition 2.11, p.9: for `0 ≤ t ≤ k`, a finite index set `I` and real
coefficients `a_{h,w}` (`h ∈ I`, `w ∈ V^t`),
`R_h = ∑_{w ∈ V^t} a_{h,w} b₀ᵀ M_{1,w₁} ⋯ M_{t,w_t}`. For `t = 0` the empty product is the identity,
so `R_h = a_{h,∅} b₀ᵀ`. -/
noncomputable def rowFamily {n k D : ℕ} {I : Type*} (t : ℕ) (ht : t ≤ k)
    (a : I → (Fin t → Fin n) → ℝ) (M : MatSample n k D) (h : I) : Fin D → ℝ :=
  fun b => ∑ w : Fin t → Fin n, a h w * walkRow M ht w b

/-- **The median of an odd number of reals**: the `((q + 1)/2)`-th smallest of `x₀, …, x_{q−1}`
(0-based index `q / 2` of the sorted list). Used in Definition 2.10, p.8. -/
noncomputable def medianR {q : ℕ} (x : Fin q → ℝ) : ℝ :=
  ((List.ofFn x).mergeSort fun a b => decide (a ≤ b)).getD (q / 2) 0

/-- **The law of `q·R` independent Gaussian trials** `Y_{j,ℓ}`, `j ∈ [q]`, `ℓ ∈ [R]`
(Definition 2.10, p.8: "resampling all vertex vectors and auxiliary matrices independently in
every trial"). -/
noncomputable def momLaw (n k D R q : ℕ) : Measure (Fin q → Fin R → VecSample n k × MatSample n k D) :=
  Measure.pi fun _ : Fin q => Measure.pi fun _ : Fin R => jointLaw n k D

/-- **The median-of-means estimator**, Definition 2.10, p.8: `Ȳ_j = (1/R) ∑_{ℓ=1}^R Y_{j,ℓ}` and
`N̂ = median(Ȳ₁, …, Ȳ_q)`, for `R ≥ 1` and odd `q ≥ 1`. -/
noncomputable def momNhat (n : ℕ) (E : Finset (Fin n × Fin n)) (k D R q : ℕ)
    (ω : Fin q → Fin R → VecSample n k × MatSample n k D) : ℝ :=
  medianR fun j : Fin q => (1 / (R : ℝ)) * ∑ l : Fin R, Y n E k D (ω j l)

end PathCount2k


