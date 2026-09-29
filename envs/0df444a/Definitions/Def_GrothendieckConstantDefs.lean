-- Prove2me | Definitions.Def_GrothendieckConstantDefs
-- name    : GrothendieckConstantDefs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-23T18:15:45.457032+00:00
-- url     : https://prove2.me/theorems/f5d1954c-2176-44d4-b3e5-49cfd14a484a
-- title:
--   The Grothendieck constant $K_G$
-- statement:
--   This file sets up the two optimization values whose worst-case ratio is the Grothendieck constant, and the constant itself.
--
--   Let $A=(a_{ij})$ be a real $m\times n$ matrix. The **discrete value** is the maximum of the bilinear form over sign labelings of the rows and columns,
--
--   $$\mathrm{OPT}(A)=\max_{x\in\{\pm1\}^m,\ y\in\{\pm1\}^n}\sum_{i,j}a_{ij}x_iy_j,$$
--
--   and the **relaxed value** replaces each sign by a unit vector and each product by an inner product,
--
--   $$\mathrm{SDP}(A)=\sup_{d\in\mathbb N}\ \sup_{u_i,v_j\in S^{d-1}\subset\mathbb R^d}\sum_{i,j}a_{ij}\langle u_i,v_j\rangle,$$
--
--   the dimension $d$ being unrestricted. A real number $K$ is a **Grothendieck bound** if $\mathrm{SDP}(A)\le K\cdot\mathrm{OPT}(A)$ holds simultaneously for all $m$, $n$ and all $A\in\mathbb R^{m\times n}$, and the **Grothendieck constant** is
--
--   $$K_G=\inf\{K\in\mathbb R: K\text{ is a Grothendieck bound}\}.$$
--
--   $K_G$ is the worst-case integrality gap of the canonical semidefinite relaxation of the bilinear $\pm1$ optimization problem; it also controls cut-norm approximation and the quantum advantage in Bell-type correlation experiments, so this definition layer is reusable for any of those statements.
--
--   **Formalization Note** Both values are supremums of explicitly described sets of reals. The sign vectors are real-valued functions each of whose coordinates is constrained to equal $1$ or $-1$; the relaxation quantifies existentially over the dimension $d$ and over unit vectors of the Euclidean space of that dimension, so no dimension bound is built in. The empty index cases $m=0$ or $n=0$ are permitted and make both values $0$.
-- source:
--   Li, Saha, Xue, Chaudhuri, Klivans, Kothari, Meka, "Long-Horizon AI Research for Grothendieck Constant: A Case Study in Human-AI Mathematical Collaboration", arXiv:2608.11195v3 (2026), https://arxiv.org/abs/2608.11195, Section 2, pp. 3-4 (definitions of OPT, SDP, and of the Grothendieck constant as the least admissible K).

import Mathlib

namespace GrothendieckConstant

/-- Values of the discrete bilinear objective over ±1 labelings of rows and columns. -/
def optSet {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : Set ℝ :=
  {s : ℝ | ∃ x : Fin m → ℝ, ∃ y : Fin n → ℝ,
      (∀ i, x i = 1 ∨ x i = -1) ∧ (∀ j, y j = 1 ∨ y j = -1) ∧
      s = ∑ i, ∑ j, A i j * x i * y j}

/-- `OPT(A)`, the maximum of the bilinear form over ±1 labelings. -/
noncomputable def optValue {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : ℝ := sSup (optSet A)

/-- Values of the relaxed objective over unit vectors in an arbitrary finite dimension. -/
def sdpSet {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : Set ℝ :=
  {s : ℝ | ∃ d : ℕ, ∃ u : Fin m → EuclideanSpace ℝ (Fin d),
      ∃ v : Fin n → EuclideanSpace ℝ (Fin d),
      (∀ i, ‖u i‖ = 1) ∧ (∀ j, ‖v j‖ = 1) ∧
      s = ∑ i, ∑ j, A i j * inner ℝ (u i) (v j)}

/-- `SDP(A)`, the value of the semidefinite relaxation. -/
noncomputable def sdpValue {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : ℝ := sSup (sdpSet A)

/-- `K` is a Grothendieck bound: `SDP(A) ≤ K * OPT(A)` for every real matrix `A`. -/
def IsGrothendieckBound (K : ℝ) : Prop :=
  ∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ), sdpValue A ≤ K * optValue A

/-- The Grothendieck constant `K_G`: the least Grothendieck bound. -/
noncomputable def grothendieckConst : ℝ := sInf {K : ℝ | IsGrothendieckBound K}

end GrothendieckConstant


