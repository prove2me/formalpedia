-- Prove2me | Definitions.Def_KhachiyanRound_BCD_Setting
-- name    : KhachiyanRound_BCD_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:13:34.624367+00:00
-- url     : https://prove2.me/theorems/cdc41b14-792e-4681-ae86-51270e835952
-- title:
--   §2–§3, pp. 309–315 — A(p), F, S_F, w_j(p), the relaxed conditions (2.10), ε(p), the BCD method, the lift 𝒜′ of (3.3), E′_p of (3.4) and Lemma 5's ellipsoid E
-- statement:
--   This file fixes the objects of Khachiyan's barycentric coordinate descent (BCD) method for rounding a finite point set.
--
--   Let $a_1,\dots,a_m \in \mathbb{R}^n$ be a finite family of points (repetitions allowed), indexed by a finite type $\iota$ with $m = |\iota|$. For a weight vector $p \in \mathbb{R}^\iota$ define:
--
--   1. the **moment matrix** (2.5)
--   $$A(p) = \sum_{i} p_i\, a_i a_i^{\mathsf T};$$
--   2. the **objective** (2.3) $F(p) = \ln\det A(p)$, and the set $S_F = \{p \in S \mid \det A(p) > 0\}$, where $S = \{p \ge 0,\ \sum_i p_i = 1\}$ is the unit simplex (2.4); $F^* = \sup\{F(p) \mid p \in S_F\}$ is the optimal value of (2.3);
--   3. the **leverages** (2.7) $w_j(p) = a_j^{\mathsf T} [A(p)]^{-1} a_j$;
--   4. the **$\varepsilon$-relaxed optimality conditions** (2.10): $w_j(p) \le (1+\varepsilon)n$ for every $j$;
--   5. the **accuracy** $\varepsilon(p) = \max_j w_j(p)/n - 1$, the smallest $\varepsilon$ for which $p$ satisfies (2.10);
--   6. **central symmetry** (2.1): for every $i$ there is $j$ with $a_j = -a_i$;
--   7. a **BCD run** (p. 312): a sequence $p_0, p_1, \dots$ with $p_0 = (1/m,\dots,1/m)$ and
--   $$p_{k+1} = (1-\tau_r)\,p_k + \tau_r e_r, \qquad \tau_r = \frac{\varepsilon(p_k)}{w_r(p_k) - 1},$$
--   where $r$ is any index maximizing $w_j(p_k)$ (equivalently $w_r = (1+\varepsilon(p_k))n$, (2.18)) and $e_r$ is the $r$th coordinate vector. The index $r$ may be chosen afresh at every step, so every tie-breaking rule is allowed.
--
--   For a family $a_1,\dots,a_m\in\mathbb{R}^n$ (not necessarily symmetric), §3 uses:
--
--   8. the **lifted family** (3.3) $\mathcal A' = \{\pm(a_j;1)\} \subset \mathbb{R}^{n+1}$, with $a_j$ in the first $n$ coordinates and $1$ in the last; it is indexed by two copies of $\{1,\dots,m\}$;
--   9. the **aggregated weights** $p_j = p_j^+ + p_j^-$ of a weight vector on $\mathcal A'$;
--   10. for weights $q \in \mathbb{R}^m$, the block matrix and ellipsoid (3.4)
--   $$M(q) = \begin{pmatrix} \sum_j q_j a_j a_j^{\mathsf T} & \sum_j q_j a_j \\ \sum_j q_j a_j^{\mathsf T} & 1 \end{pmatrix}, \qquad E'_q = \{z \in \mathbb{R}^{n+1} \mid z^{\mathsf T} M(q)^{-1} z \le 1\};$$
--   11. the ellipsoid of Lemma 5: $E = \sqrt{1+(1+\varepsilon)n}\,E'_q \cap \Pi$, where $\Pi = \{(x;y) \mid y = 1\}$ is identified with $\mathbb{R}^n$ via $x \mapsto (x;1)$.
--
--   These objects carry every statement of the mission: the D-optimal design problem (2.3), its relaxed optimality conditions, the BCD iteration, and the reduction of the general rounding problem to the centrally symmetric one.
--
--   **Formalization Note** Points are vectors `Fin n → ℝ`; the set $\mathcal A$ is the range of a family, so repeated points are allowed (their weights simply split). $F$ uses `Real.log`, which returns $0$ at $\det A(p) = 0$ instead of $-\infty$; every statement comparing values of $F$ therefore restricts to $S_F$, and $F^*$ is the supremum over $S_F$ only. Matrix inverses are Mathlib's (the zero matrix for a singular matrix), so statements carry $p\in S_F$ or a positive-definiteness hypothesis. $\varepsilon(p)$ uses the real `⨆ j` over the finite index (its value on an empty index is irrelevant: no statement uses one). The BCD run is a predicate, not a function, and has no tolerance parameter: the tolerance enters only through the stopping test (2.10). The ellipsoid $E'_q$ is the published `LinearOptimization.ellipsoid 0 M(q)`, and $\sqrt c\,E$ is the pointwise scalar multiple of a set. For $p$ in the simplex, $M(\text{aggregated } p)$ equals the moment matrix of $\mathcal A'$ at $p$ (its corner entry is $\sum_j p_j = 1$).
-- source:
--   Khachiyan, Rounding of polytopes in the real number model of computation, Math. Oper. Res. 21 (1996), pp. 309–315, (2.1)–(2.7), (2.10), (2.18)–(2.19), (BCD), (3.3)–(3.4), Lemma 5

import Mathlib
import Definitions.Def_LinearOptimization_Ellipsoid

namespace KhachiyanRound.BCD

open Matrix
open scoped Pointwise

/-- (2.5): the moment matrix `A(p) = ∑ᵢ pᵢ aᵢ aᵢᵗ` of the points `a` with weights `p`. -/
noncomputable def momentMatrix {ι : Type*} [Fintype ι] {n : ℕ} (a : ι → Fin n → ℝ)
    (p : ι → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  ∑ i, p i • Matrix.vecMulVec (a i) (a i)

/-- `S_F = {p ∈ S | F(p) > −∞}`, i.e. the points of the unit simplex `S` of (2.4)
with `det A(p) > 0` (2.5). -/
def SF {ι : Type*} [Fintype ι] {n : ℕ} (a : ι → Fin n → ℝ) : Set (ι → ℝ) :=
  {p | p ∈ stdSimplex ℝ ι ∧ 0 < (momentMatrix a p).det}

/-- (2.3): the objective `F(p) = ln det A(p)`. Meaningful only on `S_F`
(off `S_F` the paper's value is `−∞`, while `Real.log 0 = 0`). -/
noncomputable def F {ι : Type*} [Fintype ι] {n : ℕ} (a : ι → Fin n → ℝ) (p : ι → ℝ) : ℝ :=
  Real.log (momentMatrix a p).det

/-- `F* = sup {F(p) | p ∈ S_F}`, the optimal value of (2.3). -/
noncomputable def Fstar {ι : Type*} [Fintype ι] {n : ℕ} (a : ι → Fin n → ℝ) : ℝ :=
  sSup (F a '' SF a)

/-- (2.7): `w_j(p) = a_jᵗ [A(p)]⁻¹ a_j`. -/
noncomputable def w {ι : Type*} [Fintype ι] {n : ℕ} (a : ι → Fin n → ℝ) (p : ι → ℝ)
    (j : ι) : ℝ :=
  a j ⬝ᵥ (momentMatrix a p)⁻¹.mulVec (a j)

/-- (2.10): the `ε`-relaxed optimality conditions `w_j(p) ≤ (1 + ε) n` for every `j`. -/
def IsRelaxedOpt {ι : Type*} [Fintype ι] {n : ℕ} (a : ι → Fin n → ℝ) (p : ι → ℝ)
    (ε : ℝ) : Prop :=
  ∀ j, w a p j ≤ (1 + ε) * (n : ℝ)

/-- `ε(p) = max_j w_j(p) / n − 1`, the smallest `ε` with (2.10) (p. 312). -/
noncomputable def epsOf {ι : Type*} [Fintype ι] {n : ℕ} (a : ι → Fin n → ℝ)
    (p : ι → ℝ) : ℝ :=
  (⨆ j, w a p j) / (n : ℝ) - 1

/-- (2.1): the family is centrally symmetric, `𝒜 = −𝒜`. -/
def IsCentrallySymmetric {ι : Type*} {n : ℕ} (a : ι → Fin n → ℝ) : Prop :=
  ∀ i, ∃ j, a j = -a i

/-- (BCD), p. 312: `p` is a run of the barycentric coordinate descent method:
`p₀ = (1/m, …, 1/m)` and `p_{k+1} = (1 − τ_r) p_k + τ_r e_r` with `r` any index
maximizing `w_j(p_k)` (equivalently `w_r = (1 + ε(p_k)) n`, (2.18)) and
`τ_r = ε(p_k) / (w_r − 1)` (2.19). The index `r` may be chosen afresh at each step. -/
def IsBCDRun {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (a : ι → Fin n → ℝ)
    (p : ℕ → ι → ℝ) : Prop :=
  p 0 = (fun _ => 1 / (Fintype.card ι : ℝ)) ∧
  ∀ k, ∃ r, (∀ j, w a (p k) j ≤ w a (p k) r) ∧
    p (k + 1) = (1 - epsOf a (p k) / (w a (p k) r - 1)) • p k +
      (epsOf a (p k) / (w a (p k) r - 1)) • Pi.single r 1

/-- (3.3): the lifted centrally symmetric family `𝒜′ = {±(a_j; 1)} ⊂ ℝⁿ⁺¹`,
with `a_j` in the first `n` coordinates and `1` in the last. -/
def liftPts {m n : ℕ} (a : Fin m → Fin n → ℝ) : Fin m ⊕ Fin m → Fin (n + 1) → ℝ :=
  Sum.elim (fun j => Fin.snoc (α := fun _ => ℝ) (a j) 1)
    (fun j => -Fin.snoc (α := fun _ => ℝ) (a j) 1)

/-- p. 315: the aggregated weights `p_j = p_j⁺ + p_j⁻`. -/
def aggr {m : ℕ} (p : Fin m ⊕ Fin m → ℝ) : Fin m → ℝ :=
  fun j => p (Sum.inl j) + p (Sum.inr j)

/-- (3.4): the block matrix `[[∑ q_j a_j a_jᵗ, ∑ q_j a_j], [∑ q_j a_jᵗ, 1]]`. -/
noncomputable def blockMatrix {m n : ℕ} (a : Fin m → Fin n → ℝ) (q : Fin m → ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun i j =>
    Fin.lastCases (motive := fun _ => ℝ)
      (Fin.lastCases (motive := fun _ => ℝ) 1 (fun j' => ∑ l, q l * a l j') j)
      (fun i' => Fin.lastCases (motive := fun _ => ℝ) (∑ l, q l * a l i')
        (fun j' => momentMatrix a q i' j') j) i

/-- (3.4): the ellipsoid `E′_q = {z ∈ ℝⁿ⁺¹ | zᵗ M(q)⁻¹ z ≤ 1}` of the block matrix. -/
noncomputable def Eprime {m n : ℕ} (a : Fin m → Fin n → ℝ) (q : Fin m → ℝ) :
    Set (Fin (n + 1) → ℝ) :=
  LinearOptimization.ellipsoid 0 (blockMatrix a q)

/-- Lemma 5, p. 315: `E = √(1 + (1 + ε) n) E′_q ∩ Π`, with `Π = {(x; y) | y = 1}`
identified with `ℝⁿ` through `x ↦ (x; 1)`. -/
def lemma5Ellipsoid {m n : ℕ} (a : Fin m → Fin n → ℝ) (q : Fin m → ℝ) (ε : ℝ) :
    Set (Fin n → ℝ) :=
  {x | Fin.snoc (α := fun _ => ℝ) x 1 ∈ Real.sqrt (1 + (1 + ε) * (n : ℝ)) • Eprime a q}

end KhachiyanRound.BCD


