-- Prove2me | Definitions.Def_SYKEdge_Hamiltonian
-- name    : SYKEdge_Hamiltonian
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:05:41.15532+00:00
-- url     : https://prove2.me/theorems/de893bea-2445-4c8b-abff-9c6c8b2bd431
-- title:
--   The SYK Hamiltonian $H^{\mathcal H}_{SYK}=|\mathcal H|^{-1/2}\sum_{S\in\mathcal H}g_S\Gamma_S$, its dense case, and the Gaussian disorder
-- statement:
--   Let $n\ge k\ge2$ be even integers and $\mathcal H=(S_1,\dots,S_m)$ a $k$-uniform hypergraph on $[n]$ with $m\ge1$ hyperedges, given as a list (a hyperedge may repeat). With independent standard Gaussian **disorder variables** $g=(g_1,\dots,g_m)\sim N(0,\mathrm{Id}_m)$, one for each position of the list, the **SYK Hamiltonian** is
--   $$H^{\mathcal H}_{SYK}=H(g)=\frac1{\sqrt{m}}\sum_{i=1}^m g_i\,\Gamma_{S_i}.$$
--   The **dense** SYK Hamiltonian takes every $k$-subset once, with one variable $g_S$ per subset:
--   $$H_{SYK}=\binom nk^{-1/2}\sum_{S\in\binom{[n]}k}g_S\Gamma_S .$$
--   The normalization makes $\mathbb E\,H^2=\mathrm{Id}$.
--
--   The file also records the standing assumptions of the paper's §3 ($n\ge k\ge2$ even, $\mathcal H$ $k$-uniform, $m\ge1$) as a single predicate, used by every hypergraph statement.
--
--   **Formalization Note** The disorder law is the product of $N(0,1)$ laws on $\mathbb R^m$ (resp. $\mathbb R^{\binom{[n]}k}$). Repeated hyperedges carry independent disorder (footnote 6). The hyperedge order is the paper's "arbitrary ordering" of $\mathcal H$.
-- source:
--   Basu, Kothari, Midha, Sharp Bounds on Ground State Energy of the SYK Model, arXiv:2607.27185v2, eq. (1), p.1; eq. (8), p.15; footnote 6, p.3; H(g), p.30

import Mathlib
import Definitions.Def_SYKEdge_Majorana

open Matrix MeasureTheory ProbabilityTheory

namespace SYKEdge

/-!
# The SYK Hamiltonian, dense and on a hypergraph, and the Gaussian disorder

A. Basu, P. K. Kothari, S. Midha, *Sharp Bounds on Ground State Energy of the SYK Model*,
arXiv:2607.27185v2, (1), p.1; (8), p.15; footnote 6, p.3; H(g), p.30.

**Formalization Note.**
* `stdGauss α` is the law of i.i.d. `N(0,1)` variables indexed by a finite type `α`,
  `g ∼ N(0, Id_α)`, as a product measure on `α → ℝ`.
* A hypergraph is an indexed family `S : Fin m → Finset (Fin n)` (`H = (S₁, …, S_m)`), with one
  disorder variable `g_i` per index (footnote 6: repeated hyperedges carry independent disorder).
  The order on `Fin m` is the "arbitrary ordering" of p.21.
* `IsKUniform n k m S` collects the standing assumptions of §3 (p.15) and §4: `n ⩾ k ⩾ 2` even,
  `H` a `k`-uniform hypergraph, with `m = |H| ⩾ 1` (needed for the normalization `|H|^{−1/2}`).
* `syk γ S g = H(g) = |H|^{−1/2} Σ_i g_i Γ_{S_i}`, (8) and p.30.
* `sykDense γ g = (n choose k)^{−1/2} Σ_{S ∈ ([n] choose k)} g_S Γ_S`, (1), indexed directly by the
  `k`-subsets (no ordering is needed).
-/

/-- The standard Gaussian law `N(0, Id_α)` on `ℝ^α`: i.i.d. `N(0,1)` coordinates. -/
noncomputable def stdGauss (α : Type*) [Fintype α] : Measure (α → ℝ) :=
  Measure.pi fun _ => gaussianReal 0 1

/-- The standing assumptions of §3 (p.15): `n ⩾ k ⩾ 2` are even integers and
`H = (S₁, …, S_m)` is a `k`-uniform hypergraph with `m ⩾ 1` hyperedges. -/
structure IsKUniform (n k m : ℕ) (S : Fin m → Finset (Fin n)) : Prop where
  even_n : Even n
  even_k : Even k
  two_le_k : 2 ≤ k
  k_le_n : k ≤ n
  pos_m : 0 < m
  card_eq : ∀ i, (S i).card = k

/-- The SYK Hamiltonian on the hypergraph `H = (S₁, …, S_m)`,
`H^H_SYK = H(g) := |H|^{−1/2} Σ_{i} g_i Γ_{S_i}`, (8), p.15 and p.30. -/
noncomputable def syk {n m : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (γ : Fin n → Matrix ι ι ℂ) (S : Fin m → Finset (Fin n)) (g : Fin m → ℝ) : Matrix ι ι ℂ :=
  (((1 / Real.sqrt m : ℝ)) : ℂ) • ∑ i, ((g i : ℝ) : ℂ) • monomial γ (S i)

/-- The dense SYK Hamiltonian `H_SYK := (n choose k)^{−1/2} Σ_{S ∈ ([n] choose k)} g_S Γ_S`,
(1), p.1. -/
noncomputable def sykDense {n k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (γ : Fin n → Matrix ι ι ℂ) (g : KSet n k → ℝ) : Matrix ι ι ℂ :=
  (((1 / Real.sqrt (n.choose k) : ℝ)) : ℂ) • ∑ S : KSet n k, ((g S : ℝ) : ℂ) • monomial γ S.1

end SYKEdge


