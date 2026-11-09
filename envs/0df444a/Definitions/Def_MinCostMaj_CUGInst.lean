-- Prove2me | Definitions.Def_MinCostMaj_CUGInst
-- name    : MinCostMaj_CUGInst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T06:04:49.610192+00:00
-- url     : https://prove2.me/theorems/0a4800b7-bba2-4145-a1c9-fb7c52ab8e0c
-- title:
--   Instances of weighted cyclic Unique Games deletion $\mathrm{cUG}(k)$
-- statement:
--   For $k\ge2$ let $Z_k=\{(a,a+1\bmod k):a\in\{0,\dots,k-1\}\}$, the directed $k$-cycle. An instance of the deletion version $\mathrm{cUG}(k)$ of cyclic Unique Games is a finite set of variables with domain $\{0,\dots,k-1\}$ and a list of directed constraints $Z_k(u,v)$, each with a positive rational weight $w$. An assignment $\beta$ pays $w$ for every constraint with $(\beta(u),\beta(v))\notin Z_k$, that is $\beta(v)\ne\beta(u)+1\bmod k$, and nothing for the others; the cost of $\beta$ is the total payment and $\mathrm{OPT}$ is the minimum cost over all assignments.
--
--   For $k=2$ this is MinUnCut. The hard side of the main theorem is a reduction from this problem.
--
--   **Formalization Note** Instances are raw data: the number $n$ of variables and a list of arcs $(u,v,w)$; `WellFormed` asks for endpoints below $n$ and $w>0$. Loops and parallel arcs are allowed. Positive weights contain unit weights; by the paper's footnote 2 the two versions are equivalent for constant-factor approximation. The minimum is a real infimum over the finite nonempty set of assignments ($k\ge1$).
-- source:
--   Kozik, Živný, Constant-factor approximation of MinCostCSP with a conservative majority polymorphism, arXiv:2607.10667 (held version, sha256 ec17e13c…), §1, pp.3–4 and footnote 2 (PDF pp.4–5)

import Mathlib

namespace MinCostMaj

/-- **An instance of cUG(k)** (weighted deletion version of cyclic Unique Games).

Kozik, Živný, *Constant-factor approximation of MinCostCSP with a conservative majority
polymorphism*, arXiv:2607.10667, §1, pp.3–4: "For k ≥ 2, let Zk = {(a, a + 1 mod k) : a ∈
{0, . . . , k − 1}}. The Cyclic Unique Games problem has alphabet {0, . . . , k − 1} and directed
constraints Zk. The deletion version, denoted by cUG(k), charges cost 0 to tuples in Zk and
positive cost to tuples outside of Zk." Footnote 2, p.4: "For constant-factor approximation,
allowing positive costs and requiring all costs to equal 1 are equivalent."

The vertices are `0, …, n-1`; each arc `(u, v, w)` is a constraint `Z_k(u, v)` of weight `w`.

**Formalization Note.** Arcs carry positive rational weights (the "positive cost" reading, which
contains unit weights); loops and parallel arcs are allowed. -/
structure CUGInst where
  /-- number of variables -/
  n : ℕ
  /-- arcs `(u, v, weight)` -/
  arcs : List (ℕ × ℕ × ℚ)

/-- Well-formed cUG instance: endpoints `< n` and weights `> 0`. -/
def CUGInst.WellFormed (G : CUGInst) : Prop :=
  ∀ e ∈ G.arcs, e.1 < G.n ∧ e.2.1 < G.n ∧ 0 < e.2.2

/-- The value of an assignment `β : V → {0,…,k-1}` at a raw vertex index (`0` off range; never
used on well-formed instances). -/
def CUGInst.val {k : ℕ} (G : CUGInst) (β : Fin G.n → Fin k) (u : ℕ) : ℕ :=
  if h : u < G.n then (β ⟨u, h⟩ : ℕ) else 0

/-- **Cost of an assignment** in cUG(k): the total weight of the arcs `(u, v, w)` whose value pair
is not in `Z_k`, i.e. with `β(v) ≠ β(u) + 1 mod k`. -/
noncomputable def CUGInst.cost (k : ℕ) (G : CUGInst) (β : Fin G.n → Fin k) : ℝ :=
  (G.arcs.map (fun e =>
    if G.val β e.2.1 = (G.val β e.1 + 1) % k then (0 : ℝ) else (e.2.2 : ℝ))).sum

/-- **Optimum of cUG(k)**: the minimum cost over all assignments `V → {0,…,k-1}`.

**Formalization Note.** For `k ≥ 1` the index type is finite and nonempty, so the real infimum is a
minimum; `k ≥ 2` wherever it is used. -/
noncomputable def CUGInst.OPT (k : ℕ) (G : CUGInst) : ℝ :=
  ⨅ β : Fin G.n → Fin k, G.cost k β

end MinCostMaj


