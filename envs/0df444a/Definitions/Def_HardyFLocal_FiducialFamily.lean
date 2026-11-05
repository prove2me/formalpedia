-- Prove2me | Definitions.Def_HardyFLocal_FiducialFamily
-- name    : HardyFLocal_FiducialFamily
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:38:30.298986+00:00
-- url     : https://prove2.me/theorems/d38d1d27-b45f-4f0a-9af6-5197466ab591
-- title:
--   The fiducial set $\$_k$, $k\in\Omega^2$, with $\$_1=I$, the tables of (20), (21), and the chain recursion (23)–(26)
-- statement:
--   A **fiducial family** for the qubit is a list of sixteen completely positive, trace non-increasing one-qubit maps $\$_k$, $k\in\Omega^2$, with the first equal to the identity,
--   $$\$_1=I,$$
--   forming a real basis of the Hermiticity-preserving one-qubit maps.
--
--   The **elementary table** $\Lambda^{k_uk_v}_{\Phi}$ is the coordinate vector of a two-qubit map $\Phi$ in the products $\$_{k_u}\otimes\$_{k_v}$, as in (20). The **pair table** $\Lambda^{1k}_{l'l}$ is the coordinate vector of the composite $\$_{l'}\circ\$_l$ in the fiducial family, as in (21): first $\$_l$, then $\$_{l'}$.
--
--   For labels $l_1,\dots,l_r$ in time order, with a table $T$ for each sequential pair, the **chain vector** is given by the indicator of $l_1$ for $r=1$ (26), and otherwise by
--   $$\mathrm{chain}\big((x_1,l_1),(x_2,l_2),\dots\big)_k=\sum_a \mathrm{chain}\big((x_2,l_2),\dots\big)_a\;T_{x_1x_2}{}^{\,k}_{a\,l_1}.$$
--   For $r=2$ this is the table itself, for $r=3$ it is (23), and for $r=4$ it is (24).
--
--   These are the two tables that specify the causaloid (28), and the rule that builds a clump's $\Lambda$ matrix from them.
--
--   **Formalization Note** The first element of $\Omega^2$ is index $0$. The upper index $k'$ of (21) is always $1$, so a table with three indices carries all of it. The empty list has the indicator of the identity label.
-- source:
--   L. Hardy, Formalism Locality in Quantum Theory and Quantum Gravity, arXiv:0804.0054v1, §5, eqs. (20)–(26), pp.12–13

import Mathlib
import Definitions.Def_HardyFLocal_Superoperator

set_option autoImplicit false

namespace HardyFLocal

/-- **The fiducial labels of a qubit**, Hardy, arXiv:0804.0054v1, §5, pp.12–13: `Ω² = Fin 16`, with
`|Ω²| = 2⁴`. The paper's first element `1` is index `0` here. -/
abbrev Ω : Type := Fin 16

/-- **A fiducial spanning set of superoperators for the qubit**, arXiv:0804.0054v1, §5, pp.12–13
("The set $_{k_u} for k_u ∈ Ω² is a fiducial spanning set of superoperators for the qubit"; "we
choose $₁ = I where 1 is the first element of Ω² and I is the identity superoperator"): sixteen
completely positive, trace non-increasing one-qubit maps, the first of which is the identity,
forming a real basis of the Hermiticity-preserving one-qubit maps.

**Formalization Note** The basis is over `ℝ` because the coefficients of the paper are real ("a real
vector space", p.9). No particular family is fixed: the goal holds for each. -/
structure FiducialFamily where
  /-- The superoperators `$_k`, `k ∈ Ω²`. -/
  map : Ω → Op (Fin 2)
  /-- Each is completely positive. -/
  cp : ∀ k, IsCP (map k)
  /-- Each is trace non-increasing. -/
  tni : ∀ k, IsTraceNonIncreasing (map k)
  /-- `$₁ = I`. -/
  map_zero : map 0 = LinearMap.id
  /-- The sixteen maps are linearly independent over `ℝ`. -/
  linearIndependent : LinearIndependent ℝ map
  /-- They span the Hermiticity-preserving one-qubit maps over `ℝ`. -/
  span_eq : Submodule.span ℝ (Set.range map) = hpMaps (Fin 2)

/-- **The elementary table** `Λ^{k_u k_v}_{α_uv}`, arXiv:0804.0054v1, §5, eq. (20), p.12: the real
coefficients of a two-qubit map `Φ` in the products `$_a ⊗ $_b`, for a pair `(a, b)` of a label on
the right mover and one on the left mover. -/
noncomputable def elemCoeff (S : FiducialFamily) (Φ : Op (Fin 2 × Fin 2)) : Ω × Ω → ℝ :=
  coordsOf (fun p : Ω × Ω => prodOp (S.map p.1) (S.map p.2)) Φ

/-- **A table for a pair of sequential vertices**, with `T l' l k` read as `Λ^{1 k}_{l' l}`,
arXiv:0804.0054v1, §5, eq. (21), p.13.

**Formalization Note** The upper index `k'` of (21) is always `1`, so three indices carry all of
the table. -/
abbrev PairTable : Type := Ω → Ω → Ω → ℝ

/-- **The pair table** `Λ^{1 k}_{l' l}`, arXiv:0804.0054v1, §5, eq. (21), p.13: the real coefficients
of the composite `$_{l'} ∘ $_l` (first `$_l`, then `$_{l'}`) in the fiducial set. -/
noncomputable def pairTable (S : FiducialFamily) : PairTable :=
  fun l' l => coordsOf S.map (S.map l' ∘ₗ S.map l)

/-- **The composite along a clump**, arXiv:0804.0054v1, §5, eqs. (21)–(22), p.13: for labels
`[l₁, …, l_r]` in time order, `$_{l_r} ∘ ⋯ ∘ $_{l₁}`; the identity for the empty list. -/
def compose (S : FiducialFamily) : List Ω → Op (Fin 2)
  | [] => LinearMap.id
  | l :: ls => compose S ls ∘ₗ S.map l

/-- **The Λ vector of a clump**, arXiv:0804.0054v1, §5, eqs. (23)–(24) and (26), p.13. For vertices
with labels `[(x₁, l₁), …, (x_r, l_r)]` in time order and a table `T x x'` for each sequential pair:
a single vertex gives the indicator of its label (26), and a longer list satisfies

`chain ((x₁, l₁) :: (x₂, l₂) :: rest) k = Σ_n chain ((x₂, l₂) :: rest) n * T x₁ x₂ n l₁ k`,

which for two vertices is `T x₁ x₂ l₂ l₁ k`, for three is (23), and for four is (24).

**Formalization Note** The empty list gives the indicator of `0`, the coordinates of the identity
`$₁`; no clump is empty, so this is used only by the statement on composites. -/
noncomputable def chain {V : Type} (T : V → V → PairTable) : List (V × Ω) → Ω → ℝ
  | [] => Pi.single 0 1
  | [(_, l)] => Pi.single l 1
  | (x, l) :: (x', l') :: rest =>
      fun k => ∑ a, chain T ((x', l') :: rest) a * T x x' a l k

/-- **`chain` for one table used at every pair**, arXiv:0804.0054v1, §5, eqs. (23)–(24), p.13. -/
noncomputable def chainConst (T : PairTable) (ls : List Ω) : Ω → ℝ :=
  chain (fun _ _ : Unit => T) (ls.map fun l => ((), l))

end HardyFLocal


