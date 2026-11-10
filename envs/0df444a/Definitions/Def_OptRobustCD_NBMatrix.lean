-- Prove2me | Definitions.Def_OptRobustCD_NBMatrix
-- name    : OptRobustCD_NBMatrix
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:50:40.130648+00:00
-- url     : https://prove2.me/theorems/1513c0ba-aab7-4213-b6dd-89026260e5ae
-- title:
--   The nonbacktracking matrix $B_G$ and its informative eigenvector (eigenvalue of second-largest modulus)
-- statement:
--   For a graph $G$ the **nonbacktracking matrix** $B_G\in\{0,1\}^{\vec E(G)\times\vec E(G)}$ has entries
--   $$(B_G)_{u\to v,\ x\to w}=\mathbf 1[x=v]\,\mathbf 1[w\ne u],$$
--   so a directed edge $u\to v$ may be followed by any edge leaving $v$ other than its reversal (§3.2).
--
--   The **informative eigenvector** is "a unit eigenvector for the eigenvalue of $B_G$ of second-largest modulus" (Theorem 4.2): a vector $\xi\in\mathbb R^{\vec E(G)}$ with $\|\xi\|=1$ and $B_G\xi=\mu\xi$ for a real $\mu$ whose modulus $|\mu|$ is the second entry of the list of moduli of the eigenvalues of $B_G$ (with multiplicity) in decreasing order.
--
--   **Formalization Note** The paper presumes this eigenvalue real and simple ("which w.h.p. has real entries", p.5); it is so with high probability. Every statement using $\xi$ asserts, inside its high-probability event, that such a $\xi$ exists, and then quantifies over all of them; no $\xi$ is chosen by `Classical.choose`.
-- source:
--   Hopkins, Hua, Mohanty, Rajaraman, Steurer, Optimal Robust Community Detection, STOC 2027 submission (manuscript of November 3, 2026, sha256 3d287d5422db7c4a43e74333bda1dbed204af51a25fd9f2c6e875ae03a4dafa1), §3.2 p.13 (pdf p.15); Theorem 4.2 p.16 (pdf p.18)

import Mathlib
import Definitions.Def_OptRobustCD_DirEdges

namespace OptRobustCD

/-!
# The nonbacktracking matrix and its informative eigenvector

Hopkins, Hua, Mohanty, Rajaraman, Steurer, *Optimal Robust Community Detection*, STOC 2027
submission (manuscript of November 3, 2026, sha256 3d287d54…), §3.2 (p.13, pdf p.15):
"`(B_G)_{u→v, x→w} = 1[x = v] 1[w ≠ u]`"; Theorem 4.2 (p.16, pdf p.18): "let ξ be a unit
eigenvector for the eigenvalue of `B_G` of second-largest modulus".

**Formalization Note.**
* `B_G` is a real matrix indexed by the directed edges `Arc G = {(u, v) // G.Adj u v}`.
* `IsInfEig G ξ`: `ξ` is a real vector on ordered pairs vanishing off `E⃗(G)`, of Euclidean norm `1`,
  with `B_G ξ = μ ξ` on `E⃗(G)` for a real `μ`, and `|μ|` is the second entry of the moduli of the
  complex roots of the characteristic polynomial of `B_G`, with multiplicity, sorted in decreasing
  order. The paper presumes this eigenvalue real and simple ("which w.h.p. has real entries",
  p.5); every statement of the mission that uses `ξ` asserts, inside its high-probability event,
  that such a `ξ` exists and then quantifies over all of them, so the statement is never vacuous
  on graphs whose second eigenvalue is not real.
-/

open Finset
open scoped Classical

/-- The directed edges of `G`. -/
abbrev Arc {n : ℕ} (G : SimpleGraph (Fin n)) := {p : Fin n × Fin n // G.Adj p.1 p.2}

/-- The nonbacktracking matrix: `(B_G)_{u→v, x→w} = 1[x = v] 1[w ≠ u]`. -/
noncomputable def nbMatrix {n : ℕ} (G : SimpleGraph (Fin n)) : Matrix (Arc G) (Arc G) ℝ :=
  fun e f => if f.1.1 = e.1.2 ∧ f.1.2 ≠ e.1.1 then 1 else 0

/-- The moduli of the eigenvalues of `B_G` (complex roots of its characteristic polynomial, with
multiplicity), sorted in decreasing order. -/
noncomputable def nbModuli {n : ℕ} (G : SimpleGraph (Fin n)) : List ℝ :=
  (((nbMatrix G).charpoly.map (algebraMap ℝ ℂ)).roots.map fun z => ‖z‖).sort (· ≥ ·)

/-- `ξ` is a unit eigenvector of `B_G` for a real eigenvalue of second-largest modulus. -/
def IsInfEig {n : ℕ} (G : SimpleGraph (Fin n)) (ξ : EVec n) : Prop :=
  SupportedOn G ξ ∧ l2 ξ = 1 ∧
    ∃ μ : ℝ, (∀ e : Arc G, ∑ f : Arc G, nbMatrix G e f * ξ f.1 = μ * ξ e.1) ∧
      (nbModuli G)[1]? = some |μ|

end OptRobustCD


