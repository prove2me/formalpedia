-- Prove2me | Definitions.Def_SYKEdge_SignMatrix
-- name    : SYKEdge_SignMatrix
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:05:56.511019+00:00
-- url     : https://prove2.me/theorems/7b664d15-e377-4c1a-8452-b0f0ff6b0989
-- title:
--   The sign matrix $\mathcal E=|\mathcal H|^{-1}(\varepsilon_{S,T})$ and its leakage parameters $q,\delta,\rho^+,\rho^-$
-- statement:
--   For a hypergraph $\mathcal H$ (indexed by a finite set) the **sign matrix** and the **uniform vector** are
--   $$\mathcal E=\frac1{|\mathcal H|}\big(\varepsilon_{S,T}\big)_{S,T\in\mathcal H},\qquad u=|\mathcal H|^{-1/2}(1,\dots,1)^\top,\qquad \Pi_{u^\perp}=\mathrm{Id}-uu^*.$$
--   Its **spectral leakage parameters** are
--   $$q=\langle u,\mathcal Eu\rangle,\quad \delta=\|\Pi_{u^\perp}\mathcal Eu\|,\quad \rho^+=\lambda_{\max}(\Pi_{u^\perp}\mathcal E\Pi_{u^\perp}),\quad \rho^-=\max\{0,-\lambda_{\min}(\Pi_{u^\perp}\mathcal E\Pi_{u^\perp})\}.$$
--   $q$ measures the weight of $\mathcal E$ on the uniform channel, $\delta$ how far $u$ is from an eigenvector, and $\rho^\pm$ the largest positive and negative eigenvalues transverse to $u$. For even hyperedge sizes $\varepsilon_{S,T}=(-1)^{|S\cap T|}$ (the paper's Table 2).
--
--   These parameters control both the upper bound (Lemma 4.9) and the lower bound (Lemmas 4.10–4.18) on the spectral edge.
--
--   **Formalization Note** $\mathcal E$ is a complex matrix with real entries; $q$ is real and is taken as a real part. $\lambda_{\max},\lambda_{\min}$ are the Rayleigh extrema over unit vectors of $\mathbb C^{\mathcal H}$.
-- source:
--   Basu, Kothari, Midha, Sharp Bounds on Ground State Energy of the SYK Model, arXiv:2607.27185v2, eqs. (13)–(19), p.25; Table 2, p.26

import Mathlib
import Definitions.Def_SYKEdge_MatrixNorms
import Definitions.Def_SYKEdge_Majorana

open Matrix

namespace SYKEdge

/-!
# The sign matrix `ℰ` and its leakage parameters `q, δ, ρ⁺, ρ⁻`

A. Basu, P. K. Kothari, S. Midha, *Sharp Bounds on Ground State Energy of the SYK Model*,
arXiv:2607.27185v2, (13)–(19), p.25; Table 2, p.26.

**Formalization Note.**
* The hyperedges are indexed by a finite type `H` and `S : H → Finset (Fin n)`; for the hypergraphs
  of §4 `H = Fin m`, for the dense case `H = ([n] choose k)` with `S` the inclusion.
* `signMat S = ℰ = |H|^{−1} (ε_{S,T})_{S,T}`, (13), as a complex matrix with real entries. Table 2
  writes `(−1)^{|S∩T|}`, which equals `ε_{S,T}` when `|S|, |T|` are even.
* `uVec H = u = |H|^{−1/2}(1, …, 1)`, (14); `projPerp H = Π_{u⊥} = Id − uu*`, (15).
* `qParam = ⟨u, ℰu⟩` (16) is real because `ℰ` is real symmetric; the real part is taken.
* `deltaParam = ‖Π_{u⊥}ℰu‖`, (17), Euclidean norm.
* `rhoPlus = λ_max(Π_{u⊥}ℰΠ_{u⊥})`, (18), and `rhoMinus = max{0, −λ_min(Π_{u⊥}ℰΠ_{u⊥})}`, (19), with
  `λ_max`, `λ_min` the Rayleigh extrema over unit vectors of `ℂ^H` (`Def_SYKEdge_MatrixNorms`).
-/

/-- The sign matrix `ℰ := |H|^{−1} (ε_{S,T})_{S,T ∈ H}`, (13), p.25. -/
noncomputable def signMat {n : ℕ} {H : Type*} [Fintype H] (S : H → Finset (Fin n)) :
    Matrix H H ℂ :=
  fun i j => ((eps (S i) (S j) : ℤ) : ℂ) / (Fintype.card H : ℂ)

/-- The uniform unit vector `u := |H|^{−1/2} (1, …, 1)ᵀ`, (14), p.25. -/
noncomputable def uVec (H : Type*) [Fintype H] : H → ℂ :=
  fun _ => (((1 / Real.sqrt (Fintype.card H) : ℝ)) : ℂ)

/-- The rank-one projector `uu*`. -/
noncomputable def uuStar (H : Type*) [Fintype H] : Matrix H H ℂ :=
  vecMulVec (uVec H) (star (uVec H))

/-- The projector `Π_{u⊥} := Id − uu*`, (15), p.25. -/
noncomputable def projPerp (H : Type*) [Fintype H] [DecidableEq H] : Matrix H H ℂ :=
  1 - uuStar H

/-- `q := ⟨u, ℰu⟩`, (16), p.25. -/
noncomputable def qParam {n : ℕ} {H : Type*} [Fintype H] (S : H → Finset (Fin n)) : ℝ :=
  (star (uVec H) ⬝ᵥ (signMat S *ᵥ uVec H)).re

/-- `δ := ‖Π_{u⊥}ℰu‖`, (17), p.25. -/
noncomputable def deltaParam {n : ℕ} {H : Type*} [Fintype H] [DecidableEq H]
    (S : H → Finset (Fin n)) : ℝ :=
  vecNorm (projPerp H *ᵥ (signMat S *ᵥ uVec H))

/-- `ρ⁺ := λ_max(Π_{u⊥}ℰΠ_{u⊥})`, (18), p.25. -/
noncomputable def rhoPlus {n : ℕ} {H : Type*} [Fintype H] [DecidableEq H]
    (S : H → Finset (Fin n)) : ℝ :=
  lamMax (projPerp H * signMat S * projPerp H)

/-- `ρ⁻ := max{0, −λ_min(Π_{u⊥}ℰΠ_{u⊥})}`, (19), p.25. -/
noncomputable def rhoMinus {n : ℕ} {H : Type*} [Fintype H] [DecidableEq H]
    (S : H → Finset (Fin n)) : ℝ :=
  max 0 (-lamMin (projPerp H * signMat S * projPerp H))

end SYKEdge


