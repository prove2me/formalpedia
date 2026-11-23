-- Prove2me | Definitions.Def_GradDOvS_Submod_Supplement_ConvexExt
-- name    : GradDOvS_Submod_Supplement_ConvexExt
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T11:14:54.845844+00:00
-- url     : https://prove2.me/theorems/4fb2d2df-f779-4d56-81e1-006623b6aefd
-- title:
--   §4, pp. 21–22; Definition 3, p. 14; Definition EC.1, p. ec16 — L♮-convexity on [N]^d, the piecewise Lovász extension (7), indifference zone and weak sharp minimum
-- statement:
--   The objects of §4 of Zhang, Zheng and Lavaei for L♮-convex minimization on the box $\mathcal X = [N]^d = \{1,\dots,N\}^d$ (Assumption 3, $N \ge 2$, $d \ge 1$). Lattice points are vectors $x \in \mathbb Z^d$, real points vectors $x \in \mathbb R^d$.
--
--   1. **L♮-convexity** (Definition 3, p. 14). A function $f : \mathcal X \to \mathbb R$ is L♮-convex if it satisfies discrete midpoint convexity
--   $$f(x) + f(y) \ge f\big(\lceil (x+y)/2 \rceil\big) + f\big(\lfloor (x+y)/2 \rfloor\big) \qquad \text{for all } x, y \in \mathcal X,$$
--   with rounding coordinatewise. The box $[N]^d$ is an L♮-convex set, so both midpoints lie in $\mathcal X$.
--   2. **Hypercubes** (p. 21). For a base point $y \in [N-1]^d$, $\mathcal C_y = y + [0,1]^d$. These cubes cover $\operatorname{conv}(\mathcal X) = [1,N]^d$.
--   3. **Consistent permutations** (Definition 4, p. 17). A permutation $\alpha$ of $\{1,\dots,d\}$ is consistent for a vector $v$ if $v_{\alpha(1)} \ge \dots \ge v_{\alpha(d)}$. A canonical one is fixed by sorting the coordinates of $v$ decreasingly, ties broken by index.
--   4. **Neighbouring points and local Lovász extension** (p. 21). For $x \in \mathcal C_y$ and a consistent permutation $\alpha$ of $x - y$, the neighbouring points are $S^{x,0} = y$ and $S^{x,i} = y + \sum_{j=1}^{i} e_{\alpha(j)}$, and
--   $$\tilde f_y(x) = f(S^{x,0}) + \sum_{i=1}^{d} \big[f(S^{x,i}) - f(S^{x,i-1})\big]\,(x-y)_{\alpha(i)} .$$
--   5. **The convex extension** (7), p. 22: $\tilde f(x) = \tilde f_y(x)$ for $x \in [1,N]^d$ and $y \in [N-1]^d$ with $x \in \mathcal C_y$. Here it is computed with the canonical cube $y_j = \max(1, \min(N-1, \lfloor x_j \rfloor))$ and the canonical consistent permutation of $x - y$; Theorem 3 states that every other admissible choice gives the same value.
--   6. **Indifference zone** (p. 10). $f$ has indifference-zone parameter $c$ if it has a minimizer $x^*$ on $\mathcal X$ with $f(x) - f(x^*) \ge c$ for every $x \in \mathcal X \setminus \{x^*\}$. For $c > 0$ the minimizer is then unique, and an L♮-convex $f$ with this property is a member of $\mathcal{MC}_c$.
--   7. **Weak sharp minimum** (Definition EC.1, p. ec16). A function $g$ on a set $D \subseteq \mathbb R^d$ satisfies the WSM condition with constant $\kappa > 0$ if $g$ has a unique minimizer $x^*$ on $D$ and
--   $$\|x - x^*\|_\infty \le \kappa\,\big(g(x) - g(x^*)\big) \qquad \text{for all } x \in D .$$
--
--   These objects are used by Theorem 3 and Theorem EC.3, and the L♮-convexity predicate also defines the model classes of Theorems 5 and 6.
--
--   **Formalization Note** A function on $\mathcal X$ is a function on $\mathbb Z^d$ of which only the values on $[N]^d$ are used. Indices are 0-based: the paper's $i \in \{1,\dots,d\}$ is `k : Fin d` with $i = k+1$, and $S^{x,i}$ is `nbrPt y α i`. The local formula is written in the local coordinates $x - y$, as in (EC.13) on p. ec12; the display on p. 21 prints $x_{\alpha(i)}$, which is a slip (see Theorem 3). The $\ell_\infty$ norm is Lean's norm on `Fin d → ℝ`, which is the sup norm.
-- source:
--   Zhang, Zheng & Lavaei, arXiv:2010.16250v3, p. 10 (indifference zone), p. 14 (Definition 3), p. 15 (Assumption 3), p. 17 (Definition 4), pp. 21–22 (C_y, S^{x,i}, f̃_y, eq. (7)), p. ec12 (PDF 50) (EC.13), p. ec16 (PDF 54) (Definition EC.1)

import Mathlib

namespace GradDOvS.Submod.Supplement

/-! Zhang, Zheng & Lavaei, arXiv:2010.16250v3: the decision space `X = [N]^d` (Assumption 3, p. 15),
L♮-convexity by discrete midpoint convexity (Definition 3, p. 14), the piecewise Lovász extension
`f̃` of (7) (pp. 21–22), the indifference zone (p. 10) and the weak sharp minimum condition
(Definition EC.1, p. ec16 = PDF 54).

Conventions: a lattice point is a vector `Fin d → ℤ` and a real point a vector `Fin d → ℝ`; the
paper's index `i ∈ {1,…,d}` is `k : Fin d` with `i = k + 1`. A function on `X` is a function on
`ℤ^d` of which only the values on `X` are used. -/

/-- The decision space `X = [N]^d = {1, …, N}^d` (Assumption 3, p. 15). -/
def latticeBox (d N : ℕ) : Set (Fin d → ℤ) :=
  {x | ∀ i, 1 ≤ x i ∧ x i ≤ (N : ℤ)}

/-- The rounded-up midpoint `⌈(x + y)/2⌉`, coordinatewise. -/
noncomputable def midCeil {d : ℕ} (x y : Fin d → ℤ) : Fin d → ℤ :=
  fun i => ⌈(((x i + y i : ℤ) : ℝ)) / 2⌉

/-- The rounded-down midpoint `⌊(x + y)/2⌋`, coordinatewise. -/
noncomputable def midFloor {d : ℕ} (x y : Fin d → ℤ) : Fin d → ℤ :=
  fun i => ⌊(((x i + y i : ℤ) : ℝ)) / 2⌋

/-- Definition 3, p. 14: `f` is L♮-convex on `X = [N]^d`, i.e. it satisfies discrete midpoint
convexity `f(x) + f(y) ≥ f(⌈(x+y)/2⌉) + f(⌊(x+y)/2⌋)` for all `x, y ∈ X` (the box `[N]^d` is an
L♮-convex set, so both midpoints lie in `X`). -/
def LNatConvexOn (d N : ℕ) (f : (Fin d → ℤ) → ℝ) : Prop :=
  ∀ x ∈ latticeBox d N, ∀ y ∈ latticeBox d N, f (midCeil x y) + f (midFloor x y) ≤ f x + f y

/-- The real box `conv(X) = [1, N]^d`. -/
def realBox (d N : ℕ) : Set (Fin d → ℝ) :=
  Set.Icc (fun _ => (1 : ℝ)) (fun _ => (N : ℝ))

/-- The base points `y ∈ [N - 1]^d = {1, …, N - 1}^d` of the hypercubes `C_y` (p. 21). -/
def cubeBases (d N : ℕ) : Set (Fin d → ℤ) :=
  {y | ∀ i, 1 ≤ y i ∧ y i ≤ (N : ℤ) - 1}

/-- The hypercube `C_y = y + [0,1]^d` (p. 21). -/
def cube {d : ℕ} (y : Fin d → ℤ) : Set (Fin d → ℝ) :=
  {x | ∀ i, ((y i : ℤ) : ℝ) ≤ x i ∧ x i ≤ ((y i : ℤ) : ℝ) + 1}

/-- Definition 4, p. 17: `α` is a consistent permutation of the vector `v` if
`v_{α(1)} ≥ v_{α(2)} ≥ ⋯ ≥ v_{α(d)}`. -/
def IsConsistentPerm {d : ℕ} (v : Fin d → ℝ) (α : Equiv.Perm (Fin d)) : Prop :=
  Antitone (v ∘ α)

/-- The canonical consistent permutation of `v`: sort `-v` increasingly (`Tuple.sort`, ties broken by
index). It is consistent by `Tuple.monotone_sort`. -/
noncomputable def canonPerm {d : ℕ} (v : Fin d → ℝ) : Equiv.Perm (Fin d) :=
  Tuple.sort (fun i => - v i)

/-- The neighbouring point `S^{x,i} = y + ∑_{j=1}^{i} e_{α(j)}` of p. 21 (`S^{x,0} = y`), for the
permutation `α`, `i = 0, …, d`. In 0-based indexing coordinate `j` is raised by one exactly when
`α⁻¹ j < i`. -/
def nbrPt {d : ℕ} (y : Fin d → ℤ) (α : Equiv.Perm (Fin d)) (i : ℕ) : Fin d → ℤ :=
  fun j => y j + if ((α.symm j : Fin d) : ℕ) < i then 1 else 0

/-- The Lovász extension `f̃_y` of `f` in the hypercube `C_y` (p. 21), evaluated with the
permutation `α`, in the local coordinates `x - y`:
`f̃_y(x) = f(S^{x,0}) + ∑_{i=1}^d [f(S^{x,i}) - f(S^{x,i-1})] (x - y)_{α(i)}`. -/
def localLovasz {d : ℕ} (f : (Fin d → ℤ) → ℝ) (y : Fin d → ℤ) (α : Equiv.Perm (Fin d))
    (x : Fin d → ℝ) : ℝ :=
  f (nbrPt y α 0) +
    ∑ k : Fin d, (f (nbrPt y α ((k : ℕ) + 1)) - f (nbrPt y α k)) * (x (α k) - ((y (α k) : ℤ) : ℝ))

/-- A canonical hypercube containing `x ∈ [1, N]^d`: `y_j = max(1, min(N - 1, ⌊x_j⌋))`. -/
noncomputable def cubeBase (N : ℕ) {d : ℕ} (x : Fin d → ℝ) : Fin d → ℤ :=
  fun i => max 1 (min ((N : ℤ) - 1) ⌊x i⌋)

/-- The piecewise Lovász extension `f̃` of (7), p. 22: `f̃(x) = f̃_y(x)` for a hypercube `C_y`
containing `x`, computed here with the canonical hypercube `cubeBase N x` and the canonical
consistent permutation of `x - y`. Theorem 3 says that every other choice gives the same value. -/
noncomputable def convexExt (N : ℕ) {d : ℕ} (f : (Fin d → ℤ) → ℝ) (x : Fin d → ℝ) : ℝ :=
  localLovasz f (cubeBase N x) (canonPerm (fun i => x i - ((cubeBase N x i : ℤ) : ℝ))) x

/-- The indifference zone of p. 10: `f` has a unique minimizer `x*` on `X = [N]^d` and its value is
at least `c` smaller than every other objective value, `f(x) - f(x*) ≥ c` for `x ∈ X \ {x*}`. For an
L♮-convex `f` this is membership of `f` in `MC_c` (Definition 3, p. 14). -/
def HasIndifferenceZone (d N : ℕ) (f : (Fin d → ℤ) → ℝ) (c : ℝ) : Prop :=
  ∃ xs ∈ latticeBox d N, ∀ x ∈ latticeBox d N, x ≠ xs → f xs + c ≤ f x

/-- Definition EC.1, p. ec16 (PDF 54), with a given constant `κ`: `g` satisfies the weak sharp
minimum condition on `D` with constant `κ > 0` if `g` has a unique minimizer `x*` on `D` and
`‖x - x*‖∞ ≤ κ (g(x) - g(x*))` for all `x ∈ D`. The norm of `Fin d → ℝ` is the sup norm. -/
def IsWSM {d : ℕ} (D : Set (Fin d → ℝ)) (g : (Fin d → ℝ) → ℝ) (κ : ℝ) : Prop :=
  0 < κ ∧ ∃ xs ∈ D, (∀ x ∈ D, x ≠ xs → g xs < g x) ∧ ∀ x ∈ D, ‖x - xs‖ ≤ κ * (g x - g xs)

end GradDOvS.Submod.Supplement


