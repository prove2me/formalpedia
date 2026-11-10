-- Prove2me | Definitions.Def_OptRobustCD_nbWalks
-- name    : OptRobustCD_nbWalks
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:50:38.636209+00:00
-- url     : https://prove2.me/theorems/fa7c8188-f269-45a6-9283-8d965554c221
-- title:
--   Nonbacktracking walk counts $A^{(\ell)}$, the vectors $\sigma^{(s)}=(d\lambda)^{-s}A^{(s)}\sigma^\star$ and the walk scores $W^{(\ell)}$
-- statement:
--   A walk $(u_0,\dots,u_\ell)$ in $G$ is **nonbacktracking** if $u_{i+1}\ne u_{i-1}$ for every $i$.
--
--   1. (Definition 5.2) $A^{(\ell)}\in\mathbb R^{n\times n}$ counts nonbacktracking walks of length $\ell$: $A^{(\ell)}_{ij}$ is the number of them from $i$ to $j$; $A^{(0)}=I$ and $A^{(1)}=A$.
--   2. (Definition 5.2) $\sigma^{(s)}=(d\lambda)^{-s}A^{(s)}\sigma^\star\in\mathbb R^n$.
--   3. (p.16) The **walk score** $W^{(\ell)}\in\mathbb R^{\vec E(G)}$ is
--   $$W^{(\ell)}_{u\to v}=(d\lambda)^{-\ell}\sum_{(u_0,\dots,u_{\ell+1})}\sigma^\star_{u_{\ell+1}},$$
--   the sum over nonbacktracking walks in $G$ with $u_0=u$, $u_1=v$.
--
--   The normalization $(d\lambda)^{-\ell}$ makes $W^{(\ell)}$ an unbiased estimator of $\sigma^\star_v$ on the broadcast tree, and $\sigma^{(s)}$ converge to a nonzero vector as $s\to\infty$.
--
--   **Formalization Note** $W^{(\ell)}$ is computed by the recursion $S_{\ell+1}(u,v)=\sum_{w\in\partial v\setminus\{u\}}S_\ell(v,w)$, $S_0(u,v)=\sigma^\star_v$, and set to $0$ off $\vec E(G)$.
-- source:
--   Hopkins, Hua, Mohanty, Rajaraman, Steurer, Optimal Robust Community Detection, STOC 2027 submission (manuscript of November 3, 2026, sha256 3d287d5422db7c4a43e74333bda1dbed204af51a25fd9f2c6e875ae03a4dafa1), Definition 5.2 p.24 (pdf p.26); walk score, p.16 (pdf p.18)

import Mathlib
import Definitions.Def_OptRobustCD_DirEdges

namespace OptRobustCD

/-!
# Nonbacktracking walk counts `A^{(ℓ)}`, the vectors `σ^{(s)}`, and the walk scores `W^{(ℓ)}`

Hopkins, Hua, Mohanty, Rajaraman, Steurer, *Optimal Robust Community Detection*, STOC 2027
submission (manuscript of November 3, 2026, sha256 3d287d54…).
* Definition 5.2 (p.24, pdf p.26): "let `A^{(ℓ)} ∈ R^{n×n}` count length-ℓ nonbacktracking walks in
  `G` … by convention let `A^{(0)} = I`. And … let `σ^{(s)} = (dλ)^{−s} A^{(s)} σ∗`."
* p.16 (pdf p.18): "the walk score `W^{(ℓ)} ∈ R^{E⃗(G)}` is
  `W^{(ℓ)}_{u→v} = (dλ)^{−ℓ} Σ_{(u_0,…,u_{ℓ+1})} σ⋆_{u_{ℓ+1}}`, where the sum is over
  nonbacktracking walks in `G` with `u_0 = u`, `u_1 = v`, and `u_{i+1} ≠ u_{i−1}` for `1 ⩽ i ⩽ ℓ`."

**Formalization Note.**
* A walk of length `ℓ` is a map `w : Fin (ℓ+1) → Fin n` with consecutive vertices adjacent; it is
  nonbacktracking when `w (k+2) ≠ w k`. `A^{(0)} = I` follows from the definition.
* `walkSum G σ ℓ u v` is the sum of `σ_{u_{ℓ+1}}` over nonbacktracking walks `(u, v, u_2, …, u_{ℓ+1})`,
  computed by the recursion `walkSum (ℓ+1) u v = Σ_{w ∈ ∂v∖{u}} walkSum ℓ v w`; `W^{(ℓ)}` is
  `(dλ)^{−ℓ}` times it on the directed edges and `0` elsewhere.
* Labels `σ : Fin n → Bool` enter through `SBMThreshold`'s convention `true ↦ +1`, written out here.
-/

open Finset
open scoped Classical

/-- The spin `±1` of a Boolean label (`true ↦ 1`, `false ↦ −1`). -/
def spinR (x : Bool) : ℝ := if x then 1 else -1

/-- The labelling `σ` as a vector in `{±1}^n`. -/
def spinVec {n : ℕ} (σ : Fin n → Bool) : Fin n → ℝ := fun v => spinR (σ v)

/-- `w` is a nonbacktracking walk of length `ℓ` in `G`. -/
def IsNBWalk {n : ℕ} (G : SimpleGraph (Fin n)) (ℓ : ℕ) (w : Fin (ℓ + 1) → Fin n) : Prop :=
  (∀ k : Fin ℓ, G.Adj (w k.castSucc) (w k.succ)) ∧
    ∀ k : ℕ, ∀ h : k + 2 < ℓ + 1, w ⟨k + 2, h⟩ ≠ w ⟨k, by omega⟩

/-- `A^{(ℓ)}_{ij}`: the number of nonbacktracking walks of length `ℓ` from `i` to `j`. -/
noncomputable def nbCount {n : ℕ} (G : SimpleGraph (Fin n)) (ℓ : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => ((univ.filter fun w : Fin (ℓ + 1) → Fin n =>
    w 0 = i ∧ w (Fin.last ℓ) = j ∧ IsNBWalk G ℓ w).card : ℝ)

/-- `σ^{(s)} = (dλ)^{−s} A^{(s)} σ⋆`. -/
noncomputable def sigmaS {n : ℕ} (d lam : ℝ) (s : ℕ) (G : SimpleGraph (Fin n))
    (σ : Fin n → Bool) : Fin n → ℝ :=
  fun i => (d * lam) ^ (-(s : ℤ)) * (nbCount G s).mulVec (spinVec σ) i

/-- The sum of `σ_{u_{ℓ+1}}` over the nonbacktracking walks `(u_0, …, u_{ℓ+1})` with `u_0 = u`,
`u_1 = v` (for an edge `u → v`). -/
noncomputable def walkSum {n : ℕ} (G : SimpleGraph (Fin n)) (σ : Fin n → Bool) :
    ℕ → Fin n → Fin n → ℝ
  | 0, _, v => spinR (σ v)
  | ℓ + 1, u, v => ∑ w ∈ (univ.filter fun w => G.Adj v w ∧ w ≠ u), walkSum G σ ℓ v w

/-- The walk score `W^{(ℓ)}_{u→v} = (dλ)^{−ℓ} Σ σ⋆_{u_{ℓ+1}}` on `E⃗(G)`, `0` off it. -/
noncomputable def walkScore {n : ℕ} (d lam : ℝ) (ℓ : ℕ) (G : SimpleGraph (Fin n))
    (σ : Fin n → Bool) : EVec n :=
  fun p => if G.Adj p.1 p.2 then (d * lam) ^ (-(ℓ : ℤ)) * walkSum G σ ℓ p.1 p.2 else 0

end OptRobustCD


