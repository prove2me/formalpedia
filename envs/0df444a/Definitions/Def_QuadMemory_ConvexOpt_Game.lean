-- Prove2me | Definitions.Def_QuadMemory_ConvexOpt_Game
-- name    : QuadMemory_ConvexOpt_Game
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T23:03:59.17499+00:00
-- url     : https://prove2.me/theorems/3ae84087-5be6-4ee8-b35b-6aea256969fd
-- title:
--   Game 2 (p. 19), §3.1 and Lemma 5 setup (pp. 8–9) — sign matrices, uniform sphere and slab laws, sphere discretizations, the Orthogonal Vector Game with Hints, η, γ₁, γ₂, p_max
-- statement:
--   This module sets up the probabilistic objects of the lower-bound proof.
--
--   1. **Sign matrices (§3.1).** $n=\lceil d/4\rceil$. A matrix $A\in\{\pm1\}^{n\times d}$ has rows $a_1,\dots,a_n$, and $\|Ax\|_\infty=\max_j|a_j^\top x|$.
--   2. **Uniform laws.** $\mathcal U(S^{d-1})$ is the normalized surface measure of the unit sphere. For vectors $x_1,\dots,x_r$ with normalized Gram–Schmidt vectors $b_1,\dots,b_r$, the slab is $S^{d-1}\cap\{z:|b_{r'}^\top z|\le d^{-3},\ r'\le r\}$, and the slab law is $\mathcal U(S^{d-1})$ conditioned on it.
--   3. **Discretizations (pp. 8–9).** A discretization is a partition $\mathcal V=\{V_i\}$ of $S^{d-1}$ into finitely many measurable cells of equal measure, with representatives $b_i\in V_i$ (the set $\mathcal D_\delta$). The map $\varphi_\delta(y)=b_i$ for $y\in V_i$ sends a unit vector to its cell's representative. Lemma 5 provides discretizations whose cells have diameter at most $\delta$.
--   4. **Game 2, the Orthogonal Vector Game with Hints (p. 19)**, with parameters $(d,k,m,M,\alpha,\beta)$. The oracle samples $A$ uniformly. For $l=1,\dots,d$ the Player, knowing $A$ and the earlier hints, submits at most $k$ vectors $x_{l,1},\dots,x_{l,r_l}$; the oracle samples $y_l$ from their slab law and returns the hint $v_l=\varphi_\delta(y_l)$. The Player then stores an $M$-bit $\mathsf{Message}$ and submits a function $g$ mapping each point to a vector of $\{a_j\}\cup\{v_l\}$ and a label in $[d^2]$. For $i=1,\dots,m$ the Player, knowing only $\mathsf{Message}$ and the earlier responses of this phase, queries $x_i$ and receives $g(x_i)$. Finally the Player returns $y_1,\dots,y_k$ from $\mathsf{Message}$ and these responses. It wins if, for all $i\in[k]$,
--   $$\|y_i\|=1,\qquad\|Ay_i\|_\infty\le\alpha,\qquad\|P_{\mathrm{Span}(y_1,\dots,y_{i-1})^\perp}(y_i)\|_2\ge\beta .$$
--   5. **Lemma 12's constant.** $c$ is admissible if, for $h$ uniform on $\{\pm1\}^d$, any orthonormal $z_1,\dots,z_k$ and any $t\in(0,1/2]$, $\mathbb P(\max_i|z_i^\top h|\le t)\le2^{-ck}$.
--   6. **Parameters (§3.1).** $\eta=2/d^3$, $\gamma_1=12\sqrt{\log d/d}$, $\gamma_2=\gamma_1/(4d)$, $c_{d,1}=1/(90^2\log^2d)$, $c_{d,2}=1/(81\log^{2/3}d)$ (natural logarithms), and $p_{max}$ is the largest natural number with
--   $$p_{max}\le\min\Big\{\frac{c_{d,1}d-1}{k},\ c_{d,2}\Big(\frac dk\Big)^{1/3}-1\Big\}.\qquad(3)$$
--
--   These objects are shared by the milestones on the sphere, the game, and the reduction.
--
--   **Formalization Note.** A hint is used only through its cell, so the hints are represented by their cell indices and every probability of Game 2 is a finite sum: $A$ is uniform, and the hint cells have the product of the conditional cell probabilities given the earlier hints (`hintSeqWeight`). A Player is a record of functions; the phase-1 queries of round $l$ may depend on $A$ and the first $l$ hint cells. The box of Game 2 prints $n=\lfloor d/4\rfloor$; here $n=\lceil d/4\rceil$, the value fixed on p. 9 and used by Proposition 14's proof ($n\ge d/4$). The box types $g$ on $B_d(0,1)$ while the phase-2 queries are in $\mathbb R^d$; here $g$ is defined on $\mathbb R^d$. The projection norm $\|P_{W^\perp}y\|$ is the distance from $y$ to $W$ (`perpNorm`). A linearly dependent query gives a zero Gram–Schmidt vector, whose slab constraint is void. If a slab has measure zero, its slab law is the zero measure; this cannot happen with at most $d-2$ queries per round (Lemma 13). $p_{max}=\lfloor\min\{\cdot,\cdot\}\rfloor_+$ is $0$ when the minimum is below $1$. `sphereLaw` has the same body as the published `OAI_Probability_ProjectionMoments_Model` definition, which is not available as a workspace module.
-- source:
--   Blanchard, Zhang & Jaillet, arXiv:2302.04963v2, pp. 8–9 (Lemma 5 notation, D_δ, φ_δ), p. 9 (§3.1: n, η, γ₁, γ₂, Eq. (3)), p. 19 (Game 2), p. 22 (Lemma 12)

import Mathlib
import Definitions.Def_QuadMemory_ConvexOpt_Model

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ENNReal

namespace QuadMemory.ConvexOpt

/-! ### Sign matrices (§3.1, p. 9) -/

/-- `n = ⌈d/4⌉`, the number of rows of the hidden matrix `A` (p. 9). -/
def nRows (d : ℕ) : ℕ := (d + 3) / 4

/-- A sign matrix `A ∈ {±1}^{n×d}`, `n = ⌈d/4⌉`; `true` stands for `+1` and `false` for `-1`. -/
abbrev SignMatrix (d : ℕ) := Fin (nRows d) → Fin d → Bool

/-- The `±1` vector of `ℝ^d` encoded by `h : {0,1}^d` (`true ↦ +1`, `false ↦ -1`). -/
noncomputable def signVec {d : ℕ} (h : Fin d → Bool) : E d :=
  WithLp.toLp 2 (fun i => if h i then (1 : ℝ) else -1)

/-- The row `a_j ∈ {±1}^d` of the sign matrix `A`. -/
noncomputable def rowVec {d : ℕ} (A : SignMatrix d) (j : Fin (nRows d)) : E d := signVec (A j)

/-- `‖A x‖_∞ = max_j |a_jᵀ x|` (the maximum over the empty row set is `0`). -/
noncomputable def supNormA {d : ℕ} (A : SignMatrix d) (x : E d) : ℝ :=
  ⨆ j : Fin (nRows d), |⟪rowVec A j, x⟫|

/-! ### The uniform law on the sphere and its slabs -/

/-- The uniform probability law `U(S^{d-1})` on the unit sphere of `ℝ^d`, as a measure on `ℝ^d`:
the surface measure `Measure.toSphere` of Lebesgue measure, pushed forward to `ℝ^d` and
normalized. It is a probability measure for `d ≥ 1` (for `d = 0` the sphere is empty and this is
the zero measure). -/
noncomputable def sphereLaw (d : ℕ) : Measure (E d) :=
  ((volume : Measure (E d)).toSphere Set.univ)⁻¹ •
    ((volume : Measure (E d)).toSphere).map Subtype.val

/-- The slab `S^{d-1} ∩ {z : |b_{r'}ᵀ z| ≤ d^{-3} for all r' ≤ r}`, where `b_1, …, b_r` is the
normalized Gram–Schmidt orthonormalization of the vectors `x_1, …, x_r` (Procedure 1 and
Game 2). A linearly dependent `x_{r'}` yields `b_{r'} = 0`, whose constraint is void. -/
def slab {d r : ℕ} (xs : Fin r → E d) : Set (E d) :=
  {z | ‖z‖ = 1 ∧ ∀ i, |⟪InnerProductSpace.gramSchmidtNormed ℝ xs i, z⟫| ≤ ((d : ℝ) ^ 3)⁻¹}

/-- The uniform law on the slab `slab xs`: the uniform law on the sphere conditioned on the
slab. With `r = 0` it is the uniform law on the sphere. -/
noncomputable def slabLaw {d r : ℕ} (xs : Fin r → E d) : Measure (E d) :=
  (sphereLaw d)[|slab xs]

/-! ### Discretizations of the sphere (Lemma 5 and `φ_δ`, pp. 8–9) -/

/-- A partition `V = {V_i}` of the unit sphere `S^{d-1}` into finitely many measurable cells of
equal (uniform) measure, together with representatives `b_i ∈ V_i` (the set `D_δ`) and the map
`cellOf` sending a unit vector to the index of its cell. The discretization map is
`φ(y) = rep (cellOf y)` (p. 9). -/
structure SphereDisc (d : ℕ) where
  /-- the index set `[N(δ)]` of the cells -/
  ι : Type
  [instFintype : Fintype ι]
  [instDecEq : DecidableEq ι]
  /-- the cells `V_i` -/
  cell : ι → Set (E d)
  measurableSet_cell : ∀ i, MeasurableSet (cell i)
  pairwise_disjoint : Pairwise fun i j => Disjoint (cell i) (cell j)
  iUnion_cell : (⋃ i, cell i) = Metric.sphere (0 : E d) 1
  /-- all cells have the same uniform measure ("equal volume cells") -/
  measure_cell_eq : ∀ i j, sphereLaw d (cell i) = sphereLaw d (cell j)
  /-- the representative `b_i ∈ V_i` -/
  rep : ι → E d
  rep_mem : ∀ i, rep i ∈ cell i
  /-- the index of the cell containing a unit vector -/
  cellOf : E d → ι
  mem_cellOf : ∀ y ∈ Metric.sphere (0 : E d) 1, y ∈ cell (cellOf y)

attribute [instance] SphereDisc.instFintype SphereDisc.instDecEq

/-- The discretization map `φ_δ(y) = b_i` for `y ∈ V_i` (p. 9). -/
def SphereDisc.phi {d : ℕ} (D : SphereDisc d) (y : E d) : E d := D.rep (D.cellOf y)

/-- Every cell of `D` has Euclidean diameter at most `δ`. -/
def SphereDisc.DiamLe {d : ℕ} (D : SphereDisc d) (δ : ℝ) : Prop :=
  ∀ i, ∀ x ∈ D.cell i, ∀ y ∈ D.cell i, dist x y ≤ δ

/-- The probability that a sample `y ∼ U(S^{d-1} ∩ slab)` of the slab law of the queries `xs`
falls in the cell `V_i`, i.e. that the hint `φ_δ(y)` equals `b_i`. -/
noncomputable def hintWeight {d r : ℕ} (D : SphereDisc d) (xs : Fin r → E d) (i : D.ι) : ℝ≥0∞ :=
  slabLaw xs (D.cell i)

/-! ### Game 2: the Orthogonal Vector Game with Hints (p. 19) -/

/-- A strategy of the Player in Game 2 with parameters `(d, k, m, M)` and discretization `D`.
Hints are seen through their cells (`v_l = rep (w l)`), which is the same information.

* `hintQuery l A w` — the at most `k` vectors `x_{l,1}, …, x_{l,r_l}` submitted in round `l`
  of the first phase, as a function of `A` and the cells `w 0, …, w (l-1)` of the earlier hints;
* `message A w` — the `M`-bit `Message`, stored after the first phase;
* `oracleFn A w x` — the function `g` submitted to the Oracle: for a query `x`, a source
  (`inl j` for the row `a_j` of `A`, `inr l` for the hint `v_l`) and a label in `[d²]`;
* `query i s ρ` — the `i`-th query of the second phase, from `Message = s` and the earlier
  responses `ρ` of this phase;
* `answer s ρ` — the returned vectors `y_1, …, y_k`, from `Message` and all `m` responses. -/
structure Player (d k m M : ℕ) (D : SphereDisc d) where
  hintQuery : (l : Fin d) → SignMatrix d → (Fin l → D.ι) → Σ r : Fin (k + 1), (Fin r → E d)
  message : SignMatrix d → (Fin d → D.ι) → State M
  oracleFn : SignMatrix d → (Fin d → D.ι) → E d → (Fin (nRows d) ⊕ Fin d) × Fin (d ^ 2)
  query : (i : Fin m) → State M → (Fin i → E d × Fin (d ^ 2)) → E d
  answer : State M → (Fin m → E d × Fin (d ^ 2)) → Fin k → E d

namespace Player

variable {d k m M : ℕ} {D : SphereDisc d}

/-- The queries submitted in round `l` of the first phase, given `A` and the hint cells `w`. -/
def roundQuery (P : Player d k m M D) (A : SignMatrix d) (w : Fin d → D.ι) (l : Fin d) :
    Σ r : Fin (k + 1), (Fin r → E d) :=
  P.hintQuery l A (fun j => w (Fin.castLE l.isLt.le j))

/-- The probability of the hint cells `w = (w_0, …, w_{d-1})` given `A`: the product over the
rounds of the conditional probability of `w_l` given the earlier hints, which is the slab law of
the round's queries evaluated on the cell `V_{w_l}`. -/
noncomputable def hintSeqWeight (P : Player d k m M D) (A : SignMatrix d) (w : Fin d → D.ι) :
    ℝ≥0∞ :=
  ∏ l : Fin d, hintWeight D (P.roundQuery A w l).2 (w l)

/-- The probability of an event `S` of Game 2: `A` is uniform on `{±1}^{n×d}` and the hint
cells follow `hintSeqWeight`. -/
noncomputable def gameProb (P : Player d k m M D) (S : SignMatrix d → (Fin d → D.ι) → Prop) :
    ℝ≥0∞ :=
  ∑ A : SignMatrix d, ∑ w : Fin d → D.ι,
    open Classical in
    if S A w then (Fintype.card (SignMatrix d) : ℝ≥0∞)⁻¹ * P.hintSeqWeight A w else 0

/-- The Oracle's response `g(x) = (vector, label)` to a second-phase query `x`. -/
noncomputable def respond (P : Player d k m M D) (A : SignMatrix d) (w : Fin d → D.ι) (x : E d) :
    E d × Fin (d ^ 2) :=
  (Sum.elim (rowVec A) (fun l => D.rep (w l)) (P.oracleFn A w x).1, (P.oracleFn A w x).2)

/-- The first `i` responses of the second phase. -/
noncomputable def phase2 (P : Player d k m M D) (A : SignMatrix d) (w : Fin d → D.ι) :
    (i : ℕ) → i ≤ m → (Fin i → E d × Fin (d ^ 2))
  | 0, _ => Fin.elim0
  | i + 1, h =>
      Fin.snoc (α := fun _ => E d × Fin (d ^ 2)) (P.phase2 A w i (Nat.le_of_succ_le h))
        (P.respond A w (P.query ⟨i, h⟩ (P.message A w) (P.phase2 A w i (Nat.le_of_succ_le h))))

/-- The vectors `y_1, …, y_k` returned by the Player at the end of the game. -/
noncomputable def output (P : Player d k m M D) (A : SignMatrix d) (w : Fin d → D.ι) :
    Fin k → E d :=
  P.answer (P.message A w) (P.phase2 A w m le_rfl)

end Player

/-- `‖P_{Span(y_j, j < i)^⊥}(y_i)‖`, the distance from `y_i` to the span of the earlier
vectors. -/
noncomputable def perpNorm {d r : ℕ} (ys : Fin r → E d) (i : Fin r) : ℝ :=
  Metric.infDist (ys i) (Submodule.span ℝ (ys '' Set.Iio i) : Set (E d))

/-- The winning condition of Game 2 (p. 19): the returned vectors have unit norm and, for all
`i ∈ [k]`, `‖A y_i‖_∞ ≤ α` and `‖P_{Span(y_1,…,y_{i-1})^⊥}(y_i)‖₂ ≥ β`. -/
def Wins {d k : ℕ} (α β : ℝ) (A : SignMatrix d) (ys : Fin k → E d) : Prop :=
  ∀ i : Fin k, ‖ys i‖ = 1 ∧ supNormA A (ys i) ≤ α ∧ β ≤ perpNorm ys i

/-- The probability that the Player `P` wins Game 2 with parameters `α, β`. -/
noncomputable def winProb {d k m M : ℕ} {D : SphereDisc d} (P : Player d k m M D) (α β : ℝ) :
    ℝ≥0∞ :=
  P.gameProb fun A w => Wins α β A (P.output A w)

/-! ### Lemma 12's constant -/

/-- `c` is a valid constant `c_H` for Lemma 12 (p. 22): for `h` uniform on `{±1}^d`, any
orthonormal `z_1, …, z_k ∈ ℝ^d` and any `t ∈ (0, 1/2]`, `P(‖Zᵀh‖_∞ ≤ t) ≤ 2^{-c k}`. -/
def IsHypercubeConst (c : ℝ) : Prop :=
  ∀ (d k : ℕ) (Z : Fin k → E d), Orthonormal ℝ Z → ∀ t : ℝ, 0 < t → t ≤ 1 / 2 →
    ((Finset.univ.filter fun h : Fin d → Bool => ∀ i, |⟪Z i, signVec h⟫| ≤ t).card : ℝ) /
        2 ^ d ≤ (2 : ℝ) ^ (-(c * k))

/-! ### Parameters of the hard family (§3.1, p. 9) -/

/-- `η = 2/d³`. -/
noncomputable def eta (d : ℕ) : ℝ := 2 / (d : ℝ) ^ 3

/-- `γ₁ = 12 √(log d / d)` (natural logarithm). -/
noncomputable def gamma1 (d : ℕ) : ℝ := 12 * Real.sqrt (Real.log d / d)

/-- `γ₂ = γ₁/(4d)`. -/
noncomputable def gamma2 (d : ℕ) : ℝ := gamma1 d / (4 * d)

/-- `c_{d,1} = 1/(90² log² d)`. -/
noncomputable def cd1 (d : ℕ) : ℝ := 1 / (90 ^ 2 * Real.log d ^ 2)

/-- `c_{d,2} = 1/(81 log^{2/3} d)`. -/
noncomputable def cd2 (d : ℕ) : ℝ := 1 / (81 * Real.log d ^ ((2 : ℝ) / 3))

/-- `p_max`, the largest natural number with
`p_max ≤ min{(c_{d,1} d - 1)/k, c_{d,2} (d/k)^{1/3} - 1}` (Eq. (3), p. 9); it is `0` when the
minimum is below `1`. -/
noncomputable def pmax (d k : ℕ) : ℕ :=
  ⌊min ((cd1 d * d - 1) / k) (cd2 d * ((d : ℝ) / k) ^ ((1 : ℝ) / 3) - 1)⌋₊

end QuadMemory.ConvexOpt


