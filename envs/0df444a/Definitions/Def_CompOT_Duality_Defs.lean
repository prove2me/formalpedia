-- Prove2me | Definitions.Def_CompOT_Duality_Defs
-- name    : CompOT_Duality_Defs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T01:23:38.125204+00:00
-- url     : https://prove2.me/theorems/1771c52c-8385-4029-ae0e-bb68d337fcea
-- title:
--   (2.10), (2.11), (2.21), §3.2, Definition 3.1 — couplings U(a, b), ⟨C, P⟩, R(C), the dual objective, C- and C̄-transforms, complementarity
-- statement:
--   Fix integers $n, m \ge 0$, a **cost matrix** $C \in \mathbb R^{n\times m}$ and vectors $a \in \mathbb R^n$, $b \in \mathbb R^m$. Indices run over $\llbracket n\rrbracket = \{1,\dots,n\}$ and $\llbracket m\rrbracket$. The coupling and cost objects in items 1–2 below are supplied by the shared Assignment definitions; this file defines items 3–6.
--
--   1. **Couplings** (2.10). The transportation polytope is
--   $$\mathbf U(a,b) = \{P \in \mathbb R_+^{n\times m} : P\mathbb 1_m = a,\ P^{\mathsf T}\mathbb 1_n = b\},$$
--   the nonnegative matrices with row sums $a$ and column sums $b$.
--   2. **Transport cost** (2.11). $\langle C, P\rangle = \sum_{i,j} C_{i,j}P_{i,j}$. A matrix $P$ is an **optimal coupling** when $P \in \mathbf U(a,b)$ and $\langle C, P\rangle \le \langle C, Q\rangle$ for every $Q \in \mathbf U(a,b)$; its cost is then the Kantorovich value $L_C(a,b) = \min_{P\in\mathbf U(a,b)}\langle C,P\rangle$.
--   3. **Admissible dual variables** (2.21). $(f,g) \in \mathbb R^n\times\mathbb R^m$ lies in $\mathbf R(C)$ when $f_i + g_j \le C_{i,j}$ for all $(i,j)$, i.e. $f \oplus g \le C$.
--   4. **Dual objective** (2.20). $\langle f, a\rangle + \langle g, b\rangle = \sum_i f_i a_i + \sum_j g_j b_j$. A pair $(f,g)$ is **dual optimal** when $(f,g) \in \mathbf R(C)$ and $\langle f',a\rangle + \langle g',b\rangle \le \langle f,a\rangle + \langle g,b\rangle$ for every $(f',g') \in \mathbf R(C)$.
--   5. **$C$-transforms** (§3.2). For $f \in \mathbb R^n$ and $g \in \mathbb R^m$,
--   $$(f^{C})_j = \min_{i\in\llbracket n\rrbracket} C_{i,j} - f_i, \qquad (g^{\bar C})_i = \min_{j\in\llbracket m\rrbracket} C_{i,j} - g_j.$$
--   6. **Complementarity** (Definition 3.1). A matrix $P$ and a pair $(f,g)$ are complementary w.r.t. $C$ if $C_{i,j} = f_i + g_j$ whenever $P_{i,j} > 0$.
--
--   These are the objects of discrete Kantorovich duality: the primal problem minimizes $\langle C,P\rangle$ over $\mathbf U(a,b)$, the dual maximizes $\langle f,a\rangle+\langle g,b\rangle$ over $\mathbf R(C)$, and the $C$-transforms and complementarity describe the structure of optimal dual and primal solutions.
--
--   **Formalization Note** Indices are 0-based (`Fin n`). Matrices are `Matrix (Fin n) (Fin m) ℝ`. The minima in the $C$-transforms are Lean's real infimum over the finite index set; this equals the book's minimum when the index set is nonempty, while for $n = 0$ (resp. $m = 0$) Lean returns $0$, so every theorem using a transform assumes $n \ge 1$ (resp. $m \ge 1$) or has hypotheses that imply it. Optimality of primal and dual solutions is encoded as predicates rather than as a real infimum/supremum, so no junk value arises when a set is empty or unbounded.
-- source:
--   Peyré & Cuturi, Computational Optimal Transport (FnT ML 2019), (2.10)–(2.11), pp. 370–371; Proposition 2.4 (2.20)–(2.21), p. 382; §3.2 C-transforms, p. 403; Definition 3.1, p. 405

import Mathlib
import Definitions.Def_CompOT_Assignment_Defs

namespace CompOT.Duality

/-- Membership in the set `R(C)` of admissible dual variables (2.21), p. 382:
`f_i + g_j ≤ C_{i,j}` for all `(i, j)`, i.e. `f ⊕ g ≤ C`. -/
def dualFeasible {n m : ℕ} (C : Matrix (Fin n) (Fin m) ℝ) (f : Fin n → ℝ) (g : Fin m → ℝ) :
    Prop :=
  ∀ i j, f i + g j ≤ C i j

/-- The dual objective `⟨f, a⟩ + ⟨g, b⟩` of (2.20), p. 382. -/
def dualObj {n m : ℕ} (a : Fin n → ℝ) (b : Fin m → ℝ) (f : Fin n → ℝ) (g : Fin m → ℝ) : ℝ :=
  ∑ i, f i * a i + ∑ j, g j * b j

/-- `(f, g)` is a solution of the dual problem (2.20): `(f, g) ∈ R(C)` and
`⟨f', a⟩ + ⟨g', b⟩ ≤ ⟨f, a⟩ + ⟨g, b⟩` for every `(f', g') ∈ R(C)`. -/
def IsDualOptimal {n m : ℕ} (C : Matrix (Fin n) (Fin m) ℝ) (a : Fin n → ℝ) (b : Fin m → ℝ)
    (f : Fin n → ℝ) (g : Fin m → ℝ) : Prop :=
  dualFeasible C f g ∧ ∀ f' g', dualFeasible C f' g' → dualObj a b f' g' ≤ dualObj a b f g

/-- The `C`-transform of §3.2, p. 403: `(f^C)_j = min_{i ∈ ⟦n⟧} C_{i,j} - f_i`.
A finite infimum over `Fin n`; it is the book's minimum only when `n ≥ 1` (for `n = 0` Lean's real
`⨅` over an empty index returns `0`), so every statement using it carries `n ≥ 1`. -/
noncomputable def cTransform {n m : ℕ} (C : Matrix (Fin n) (Fin m) ℝ) (f : Fin n → ℝ) :
    Fin m → ℝ :=
  fun j => ⨅ i, C i j - f i

/-- The `C̄`-transform of §3.2, p. 403: `(g^{C̄})_i = min_{j ∈ ⟦m⟧} C_{i,j} - g_j`
(meaningful for `m ≥ 1`, see `cTransform`). -/
noncomputable def cbarTransform {n m : ℕ} (C : Matrix (Fin n) (Fin m) ℝ) (g : Fin m → ℝ) :
    Fin n → ℝ :=
  fun i => ⨅ j, C i j - g j

/-- Definition 3.1, p. 405: `P` and `(f, g)` are complementary w.r.t. `C` if
`C_{i,j} = f_i + g_j` whenever `P_{i,j} > 0`. -/
def Complementary {n m : ℕ} (C P : Matrix (Fin n) (Fin m) ℝ) (f : Fin n → ℝ) (g : Fin m → ℝ) :
    Prop :=
  ∀ i j, 0 < P i j → C i j = f i + g j

end CompOT.Duality


