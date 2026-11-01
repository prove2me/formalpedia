-- Prove2me | Definitions.Def_PWDB_DBPrimeProgram
-- name    : PWDB_DBPrimeProgram
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:37:53.365136+00:00
-- url     : https://prove2.me/theorems/3b1bb958-27cb-484f-9c45-8c12e7692408
-- title:
--   Reformulated dual best problem (D-B′)
-- statement:
--   Problem (D-B′) is
--   $$
--   \begin{aligned}
--   \sup\ & -f_0^{*1}(w_0, z_0) - \sum_{i\in I}\lambda_i f_i^{*1}(w_i/\lambda_i, \upsilon_i/\lambda_i)\\
--   \text{s.t.}\ & \sum_{i\in I_0} w_i = 0,\quad c_\ell(z_0) \le 0\ \ \forall \ell,\quad \lambda_i c_\ell(\upsilon_i/\lambda_i) \le 0\ \ \forall i, \ell,\quad \lambda \ge 0,
--   \end{aligned}
--   $$
--   where $\lambda_i f_i^{*1}(w_i/\lambda_i, \upsilon_i/\lambda_i)$ is the convex perspective of the jointly convex function $(w, z) \mapsto f_i^{*1}(w, z)$, and $\lambda_i c_\ell(\upsilon_i/\lambda_i)$ that of $c_\ell$.
--
--   The module defines `jointConj1`, the objective `dbpObj`, the feasible region `dbpFeas`, the value `dbpVal` and the constraints in the form of Definition 1 (`dbpIneq`, `dbpEq`). In `dbpIneq` the row $\lambda_i c_\ell(\upsilon_i/\lambda_i)$ is `dbpRow`: the perspective for $\lambda_i \ge 0$, extended linearly to $\lambda_i < 0$ when $c_\ell$ is affine, so that the row of an affine $c_\ell$ is an affine constraint of Definition 1, as it is on the paper's domain $\lambda_i \ge 0$.
--
--   **Formalization Note** The product $E \times F$ carries the $L^2$ inner product (`WithLp 2 (E × F)`), that of $\mathbb R^{d_x} \times \mathbb R^{d_z}$.
-- source:
--   Zhen, Kuhn & Wiesemann, A Unified Theory of Robust and Distributionally Robust Optimization via the Primal-Worst-Equals-Dual-Best Principle, arXiv:2105.00760v2 (19 Jul 2023), problem (D-B′), p.12

import Mathlib
import Definitions.Def_PWDB_IsAffineFn
import Definitions.Def_PWDB_persp
import Definitions.Def_PWDB_PartialConj

open scoped InnerProductSpace

namespace PWDB

/-- **Joint partial conjugate** `(w, z) ↦ g∗1(w, z)` of a real-valued `g` on the Euclidean product
`E × F` (Zhen, Kuhn & Wiesemann, arXiv:2105.00760v2, Definition A.3, p.40, viewed as a function of
both arguments, as in (D-B′), p.12).

**Formalization Note** The product carries the `L²` inner product `⟨(w, z), (x, y)⟩ = ⟨w, x⟩ +
⟨z, y⟩` (`WithLp 2 (E × F)`), the inner product of `ℝ^{dx} × ℝ^{dz} = ℝ^{dx+dz}`, so that its
conjugate and perspective are those of the paper. -/
noncomputable def jointConj1 {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : E → F → ℝ) : WithLp 2 (E × F) → EReal :=
  fun q => pconj1 (fun x z => ((g x z : ℝ) : EReal)) (WithLp.ofLp q).1 (WithLp.ofLp q).2

/-- **Objective of the reformulated dual best problem (D-B′)** (arXiv:2105.00760v2, p.12):
`−f0∗1(w0, z0) − Σ_{i∈I} λi fi∗1(wi/λi, υi/λi)` at `p = (w₀, z₀, w, υ, λ)`.

**Formalization Note** `λi fi∗1(wi/λi, υi/λi)` is the convex perspective (Definition A.2, p.39) of
the jointly convex function `(w, z) ↦ fi∗1(w, z)` at `((wi, υi), λi)`, so at `λi = 0` it is the
support function of the domain of its (joint) conjugate, which depends on `υi`. -/
noncomputable def dbpObj {E F ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [Fintype ι]
    (f₀ : E → F → ℝ) (f : ι → E → F → ℝ) (p : E × F × (ι → E) × (ι → F) × (ι → ℝ)) : EReal :=
  -(pconj1 (fun x z => ((f₀ x z : ℝ) : EReal)) p.1 p.2.1 +
    ∑ i, persp (jointConj1 (f i)) (WithLp.toLp 2 (p.2.2.1 i, p.2.2.2.1 i)) (p.2.2.2.2 i))

/-- **Feasible region of (D-B′)** (arXiv:2105.00760v2, p.12): `Σ_{i∈I0} wi = 0`,
`cℓ(z0) ≤ 0 ∀ℓ ∈ L`, `λi cℓ(υi/λi) ≤ 0 ∀i ∈ I, ∀ℓ ∈ L`, `λ ≥ 0`, and (p.40) objective value other
than `−∞`. `λi cℓ(υi/λi)` is the convex perspective `persp (c ℓ) υi λi` (Definition A.2). -/
def dbpFeas {E F ι L : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [Fintype ι]
    (c : L → F → EReal) (f₀ : E → F → ℝ) (f : ι → E → F → ℝ) :
    Set (E × F × (ι → E) × (ι → F) × (ι → ℝ)) :=
  {p | p.1 + ∑ i, p.2.2.1 i = 0 ∧ (∀ ℓ, c ℓ p.2.1 ≤ 0) ∧
    (∀ i ℓ, persp (c ℓ) (p.2.2.2.1 i) (p.2.2.2.2 i) ≤ 0) ∧ (∀ i, 0 ≤ p.2.2.2.2 i) ∧
    dbpObj f₀ f p ≠ ⊥}

/-- **Optimal value (supremum) of (D-B′)** (arXiv:2105.00760v2, p.12), in `EReal`. -/
noncomputable def dbpVal {E F ι L : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [Fintype ι]
    (c : L → F → EReal) (f₀ : E → F → ℝ) (f : ι → E → F → ℝ) : EReal :=
  ⨆ p ∈ dbpFeas c f₀ f, dbpObj f₀ f p

open Classical in
/-- **The row `λi cℓ(υi/λi)` of (D-B′) as a constraint function of Definition 1**
(arXiv:2105.00760v2, p.6 and p.12). `dbpRow g u t` is `persp g u t`, except that for affine `g` and
`t < 0` it is `t · g(u/t)`.

**Formalization Note** The paper's perspective lives on `ℝ^{dz} × ℝ₊`, and for an affine
`cℓ(z) = ⟨a, z⟩ + b` it is the linear function `(υ, λ) ↦ ⟨a, υ⟩ + bλ` on all of that domain, so the
row is one of the linear constraints that condition (iii) of Definition 1 exempts from strictness.
The extension of `persp` by `+∞` to `t < 0` would hide this, since `IsAffineFn` asks for an affine
function on the whole space. `dbpRow` extends the row affinely instead; it equals `persp g u t` at
every `t ≥ 0`, so with the constraint `−λi ≤ 0` it describes the same feasible set. For non-affine
`g` it is `persp g u t` everywhere. -/
noncomputable def dbpRow {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (g : F → EReal) (u : F) (t : ℝ) : EReal :=
  if t < 0 ∧ IsAffineFn g then (t : EReal) * g (t⁻¹ • u) else persp g u t

/-- **Inequality constraints of (D-B′) in the form of Definition 1** (arXiv:2105.00760v2, p.6 and
p.12): `cℓ(z0) ≤ 0` (`ℓ ∈ L`), `λi cℓ(υi/λi) ≤ 0` (`i ∈ I`, `ℓ ∈ L`, as `dbpRow`) and the affine
`−λi ≤ 0` (`i ∈ I`). -/
noncomputable def dbpIneq {E F ι L : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (c : L → F → EReal) :
    L ⊕ (ι × L) ⊕ ι → (E × F × (ι → E) × (ι → F) × (ι → ℝ)) → EReal :=
  fun k p => Sum.elim (fun ℓ => c ℓ p.2.1)
    (Sum.elim (fun q => dbpRow (c q.2) (p.2.2.2.1 q.1) (p.2.2.2.2 q.1))
      (fun i => ((-(p.2.2.2.2 i) : ℝ) : EReal))) k

/-- **Equality constraints of (D-B′) in the form of Definition 1** (arXiv:2105.00760v2, p.6 and
p.12): `Σ_{i∈I0} wi = 0` as the scalar linear equations `⟨v, w₀ + Σ_i wi⟩ = 0`, `v ∈ E`. -/
noncomputable def dbpEq {E F ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fintype ι] : E → (E × F × (ι → E) × (ι → F) × (ι → ℝ)) → EReal :=
  fun v p => ((⟪v, p.1 + ∑ i, p.2.2.1 i⟫_ℝ : ℝ) : EReal)

end PWDB


