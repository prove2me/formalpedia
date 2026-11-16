-- Prove2me | Definitions.Def_EntropyLocalCoord_Leader_Supplement_Majority
-- name    : EntropyLocalCoord_Leader_Supplement_Majority
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:26:05.386225+00:00
-- url     : https://prove2.me/theorems/10d7bcb9-3a7e-4f11-be67-a8409f0d3824
-- title:
--   §5, Steps 1, 2, 4.1, 4.2 — weighted majority functions, the graph $H$, $\operatorname{supp}(f)$, crossing probabilities $p_{fg}$ and $P$
-- statement:
--   Fix $k\ge1$ and write $\{\pm1\}^k$ for the Boolean cube. For a weight vector $w\in\mathbb R^k$ and $x\in\{\pm1\}^k$ let $w\cdot x=\sum_i w_ix_i$.
--
--   1. A **weighted majority function** is a function $f:\{\pm1\}^k\to\{\pm1\}$ of the form $f(x)=f_w(x)=\operatorname{sign}(w\cdot x)$ for some weight vector $w$ with all $w_i>0$ and $w\cdot x\ne0$ for every $x\in\{\pm1\}^k$. The set $V(H)$ consists of the distinct such functions; it is finite.
--   2. The **relevant coordinates** of $f$ are $\operatorname{supp}(f)=\{i\in[k]:\exists x,\ f(x_{-i},1)\ne f(x_{-i},-1)\}$.
--   3. The **auxiliary graph** $H$ on $V(H)$ joins $f$ and $g$ when they disagree on exactly one antipodal pair $\{x,-x\}$; equivalently, their regions in the positive orthant share a facet.
--   4. The **region** of $f$ is the open cone $R_f=\{w\in(0,\infty)^k: w\cdot x\ne0\ \forall x,\ f_w=f\}$, and the **common facet** $F_{fg}$ is the set of points of $(0,\infty)^k$ lying in the closures of both $R_f$ and $R_g$.
--   5. Let $W=(W_1,\dots,W_k)$ be uniform on the simplex $\Delta=\{w\in[0,\infty)^k:\sum_iw_i=1\}$ and, for a coordinate $i$, let $w^{(i)}(t)=(W_1,\dots,W_{i-1},t,W_{i+1},\dots,W_k)$, $0<t\le W_i$. The **crossing probability** is
--
--   $$p_{fg}=P\bigl(w^{(i)}(t)\in F_{fg}\text{ for some }0<t\le W_i\bigr).$$
--
--   6. The **total crossing weight** is $P=\sum_{\{f,g\}\in E(H)}p_{fg}$, each edge of $H$ counted once.
--
--   These are the objects of the paper's lower-bound construction for Theorem 3.4; Lemmas 5.1–5.3 are statements about them.
--
--   **Formalization Note** Inputs are functions $\mathrm{Fin}\,k\to\mathbb Z^\times$ (units of $\mathbb Z$, i.e. $\pm1$). The uniform law on $\Delta$ is the published `dirichletOnes k` ($\mathrm{Dirichlet}_k(1,\dots,1)$). The paper defines $p_{fg}$ with an arbitrary coordinate $i$ and proves the value does not depend on $i$; here $p_{fg}$ and $P$ carry $i$ as an explicit argument, and the lemmas are stated for every $i$. $P$ is written as half the sum over ordered adjacent pairs. The graph $H$ is defined by the antipodal-pair criterion, which the paper records as equivalent to the facet definition (p. 14).
-- source:
--   Peretz and Kraizberg, Entropy Bounds for Local Coordination and Graph Amenability, STOC 2027 submission #272 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/272.pdf, SHA-256 ed0fb53954295c5258fc56b2780b62aad05401917ee1fb4064ff953d9d1d0526, §5, Step 1, pp. 13–14 (weighted majority functions, H); Step 2, p. 14 (supp(f)); Step 4.1, p. 16 (Δ, W, w^(i), F_fg, p_fg); Lemma 5.2, p. 17 (P).

import Mathlib
import Definitions.Def_BallPolyApprox_VertexBudget_SimplexLayer

open MeasureTheory

namespace EntropyLocalCoord.Leader.Supplement

/-- The Boolean cube `{±1}^k`, each coordinate a unit of `ℤ` (that is, `1` or `-1`). -/
abbrev Cube (k : ℕ) := Fin k → ℤˣ

/-- The signed sum `w · x = ∑_i w_i x_i` of a weight vector `w` and an input `x ∈ {±1}^k`. -/
def signedSum {k : ℕ} (w : Fin k → ℝ) (x : Cube k) : ℝ :=
  ∑ i, w i * ((x i : ℤ) : ℝ)

/-- Admissible weights (§5, Step 1, p. 13): all weights positive and every signed sum nonzero. -/
def IsAdmissibleWeight {k : ℕ} (w : Fin k → ℝ) : Prop :=
  (∀ i, 0 < w i) ∧ ∀ x : Cube k, signedSum w x ≠ 0

/-- The weighted majority function `f_w(x) = sign(w · x)` of an admissible weight `w`, as the
statement that `f` takes the value `1` exactly where `w · x > 0` (and `-1` elsewhere). -/
def IsMajorityOf {k : ℕ} (w : Fin k → ℝ) (f : Cube k → ℤˣ) : Prop :=
  ∀ x, f x = 1 ↔ 0 < signedSum w x

/-- `f : {±1}^k → {±1}` is a positive-weight, tie-free weighted majority function: `f = f_w` for
some admissible weight `w` (§5, Step 1, p. 13). -/
def IsWeightedMajority {k : ℕ} (f : Cube k → ℤˣ) : Prop :=
  ∃ w, IsAdmissibleWeight w ∧ IsMajorityOf w f

/-- The vertex set `V(H)`: the distinct weighted majority functions on `k` inputs. -/
abbrev MajFun (k : ℕ) := {f : Cube k → ℤˣ // IsWeightedMajority f}

noncomputable instance (k : ℕ) : Fintype (MajFun k) := by
  classical exact Subtype.fintype _

open scoped Classical in
/-- `supp(f) = {i ∈ [k] : ∃ x, f(x_{-i}, 1) ≠ f(x_{-i}, -1)}` (§5, Step 2, p. 14): the
coordinates on which `f` depends. -/
noncomputable def supp {k : ℕ} (f : Cube k → ℤˣ) : Finset (Fin k) :=
  Finset.univ.filter (fun i => ∃ x : Cube k, f (Function.update x i 1) ≠ f (Function.update x i (-1)))

/-- The auxiliary graph `H` on `V(H)` (§5, Step 1, p. 14): `f ∼ g` iff `f` and `g` disagree on
exactly one antipodal pair `{x, -x}`. The source defines `f ∼ g` by "the regions of `f` and `g`
share a facet inside `(0, ∞)^k`" and records this combinatorial description as equivalent. -/
def auxGraph (k : ℕ) : SimpleGraph (MajFun k) where
  Adj f g := ∃ x : Cube k, ∀ y : Cube k, f.1 y ≠ g.1 y ↔ (y = x ∨ y = -x)
  symm := ⟨fun f g ⟨x, hx⟩ => ⟨x, fun y => by rw [ne_comm]; exact hx y⟩⟩
  loopless := ⟨fun f ⟨x, hx⟩ => (hx x).2 (Or.inl rfl) rfl⟩

/-- The open cone (region) of the positive orthant whose weights determine `f`:
`R_f = {w ∈ (0, ∞)^k : w admissible, f_w = f}`. -/
def region {k : ℕ} (f : Cube k → ℤˣ) : Set (Fin k → ℝ) :=
  {w | IsAdmissibleWeight w ∧ IsMajorityOf w f}

/-- The common facet `F_fg` of the regions of `f` and `g` inside the open positive orthant: the
points of `(0, ∞)^k` lying in the closures of both regions (§5, Step 4.1, p. 16). For `f ∼ g`
this is the closed (relative to `(0, ∞)^k`) facet the two regions share. -/
def commonFacet {k : ℕ} (f g : Cube k → ℤˣ) : Set (Fin k → ℝ) :=
  {w | (∀ i, 0 < w i) ∧ w ∈ closure (region f) ∧ w ∈ closure (region g)}

/-- The crossing probability `p_fg = P(w^{(i)} crosses F_fg)` computed along coordinate `i`
(§5, Step 4.1, p. 16): `W` is uniform on the standard simplex
`Δ = {w ∈ [0, ∞)^k : ∑_i w_i = 1}` (the published law `dirichletOnes k`, `Dirichlet_k(1, …, 1)`:
normalized Lebesgue measure on the corner simplex of `ℝ^{k-1}` pushed forward by
`x ↦ (x, 1 - ∑_j x_j)`), and the path
`w^{(i)}(t) = (W_1, …, W_{i-1}, t, W_{i+1}, …, W_k)`, `0 < t ≤ W_i`, crosses `F_fg` when some
point of it lies in `F_fg`. The source defines `p_fg` with an arbitrary `i` and shows that the
value does not depend on `i`. -/
noncomputable def crossProb {k : ℕ} (i : Fin k) (f g : Cube k → ℤˣ) : ℝ :=
  (BallPolyApprox.VertexBudget.dirichletOnes k).real
    {W | ∃ t : ℝ, 0 < t ∧ t ≤ W i ∧ Function.update W i t ∈ commonFacet f g}

open scoped Classical in
/-- `P = ∑_{{f, g} ∈ E(H)} p_fg` (§5, Step 4.2, p. 17), with `p_fg` computed along coordinate
`i`. Each unordered edge is counted once: the double sum over ordered adjacent pairs counts it
twice and is halved (`p_fg` is symmetric in `f, g` by definition). -/
noncomputable def totalCrossing {k : ℕ} (i : Fin k) : ℝ :=
  (1 / 2) * ∑ f : MajFun k, ∑ g : MajFun k,
    if (auxGraph k).Adj f g then crossProb i f.1 g.1 else 0

end EntropyLocalCoord.Leader.Supplement


