-- Prove2me | Definitions.Def_DataValidation_Instance
-- name    : DataValidation_Instance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:46:26.771715+00:00
-- url     : https://prove2.me/theorems/d6ca3b54-522a-427a-a119-88f08ed5df5d
-- title:
--   Instances of the Data Validation Problem
-- statement:
--   A **DVP instance** consists of a probing budget $T\in\mathbb N$ and a transitive directed acyclic graph $G=(V,E)$, in which each edge $e$ has a weight $w_e\in\mathbb N_0$, a probing cost $\tau_e\in\mathbb N_0$ and a success probability $p_e\in[0,1]$. Transitivity means that $(u,v),(v,x)\in E$ imply $(u,x)\in E$.
--
--   An instance is **unit** if $\tau_e=p_e=1$ and $w_e\in\{0,1\}$ for every edge $e\in E$; this is the special case of Theorem 1.
--
--   **Formalization Note** Vertices are $\mathrm{Fin}\,n$ with $n=|V|$, probabilities are rational so that an instance can be written as a finite string, and validity asks $w$, $\tau$, $p$ to vanish off $E$, which excludes no instance and makes one instance correspond to one set of data.
-- source:
--   Tinguely, van der Heijden, Approximation and Hardness for the Data Validation Problem, arXiv:2611.06773 (sha256 6595f819…), §1, p.1; Theorem 1, p.2

import Definitions.Def_DataValidation_transReduction

set_option autoImplicit false

namespace DataValidation

/-- The raw data of a **DVP instance**: `n` vertices, an edge set `E`, on each edge a weight
`w_e ∈ ℕ₀`, a probing cost `τ_e ∈ ℕ₀` and a success probability `p_e`, and a probing budget
`T ∈ ℕ`. arXiv:2611.06773 (sha256 6595f819…), §1, p.1.

**Formalization Note.** The vertices are `Fin n` (`n := |V|`). The probabilities are rational so that
an instance can be written down as a finite string; `Instance.IsValid` holds the conditions. -/
structure Instance where
  /-- The number of vertices. -/
  n : ℕ
  /-- The edge set. -/
  E : Finset (Fin n × Fin n)
  /-- The weights `w_e`. -/
  w : Fin n × Fin n → ℕ
  /-- The probing costs `τ_e`. -/
  τ : Fin n × Fin n → ℕ
  /-- The success probabilities `p_e`. -/
  p : Fin n × Fin n → ℚ
  /-- The probing budget `T`. -/
  T : ℕ

/-- `I` is a **DVP instance**: the graph is a transitive DAG and `p_e ∈ [0, 1]` on every edge.
arXiv:2611.06773 (sha256 6595f819…), §1, p.1: "a directed acyclic graph (DAG) G = (V, E) which is
also transitive", "a success probability p_e ∈ [0, 1]".

**Formalization Note.** The last clause is a normal form: `w`, `τ` and `p` vanish off `E`, where the
page has no values at all. It excludes no instance of the page, and makes one instance correspond to
one set of data, so that `DataValidation.code` is injective on valid instances. The page's budget is
`T ∈ N = {1, 2, …}` (it writes `N₀` for `w_e` and `τ_e`); `T = 0` is allowed here, and the languages
`dvpLang`, `pDvp` require `0 < T`. -/
def Instance.IsValid (I : Instance) : Prop :=
  IsAcyclic I.E ∧
  (∀ u v x, (u, v) ∈ I.E → (v, x) ∈ I.E → (u, x) ∈ I.E) ∧
  (∀ e ∈ I.E, 0 ≤ I.p e ∧ I.p e ≤ 1) ∧
  (∀ e, e ∉ I.E → I.w e = 0 ∧ I.τ e = 0 ∧ I.p e = 0)

/-- The special case of Theorem 1: `τ_e = p_e = 1` and `w_e ∈ {0, 1}` for every edge `e ∈ E`.
arXiv:2611.06773 (sha256 6595f819…), Theorem 1, p.2. -/
def Instance.IsUnit (I : Instance) : Prop :=
  ∀ e ∈ I.E, I.τ e = 1 ∧ I.p e = 1 ∧ I.w e ≤ 1

end DataValidation


