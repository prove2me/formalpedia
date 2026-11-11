-- Prove2me | Definitions.Def_PosIndexNash_PPADS_NormalForm
-- name    : PosIndexNash_PPADS_NormalForm
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T01:31:29.063425+00:00
-- url     : https://prove2.me/theorems/4405e1b0-842e-4f0c-9e05-f3b33967464b
-- title:
--   Max-affine circuits in normal form, anchored outputs, A, U, V, b, M = A − UVᵀ, x(λ) and Φ (§5.1, (31)–(36))
-- statement:
--   A **max-affine circuit in normal form** has an input $\lambda \in \mathbb{R}^d$ and max-gate variables $x_1, \dots, x_m$, gate $i$ being
--   $$x_i = \max\{0, \ell_i(x_{<i}, \lambda)\},\qquad \ell_i = b_i + u_i^\top\lambda + \sum_{j<i} c_{ij}\,x_j \tag{31}$$
--   with rational $b_i, c_{ij}$ and $u_i \in \mathbb{Q}^d$. Its **execution** $x(\lambda)$ is the vector of all gate values, computed gate by gate. Output coordinate $\ell$ is the gate $o_\ell$, so the computed map is $\Phi(\lambda) = V^\top x(\lambda)$ (33), where the **selector** $V \in \{0,1\}^{m\times d}$ has column $\ell$ equal to $e_{o_\ell}$.
--
--   The outputs are **anchored** ((32), (35)): for every $\ell$ there is a gate $p_\ell$ placed immediately before $o_\ell$ and $o_\ell = \max\{0, 1 - p_\ell\}$, i.e. row $o_\ell$ has $c_{o_\ell, p_\ell} = -1$, all other $c_{o_\ell, j} = 0$, $u_{o_\ell} = 0$ and $b_{o_\ell} = 1$; the $2d$ gates $p_\ell, o_\ell$ are distinct.
--
--   With $A \in \mathbb{Q}^{m\times m}$ unit lower triangular ($A_{ii} = 1$, $A_{ij} = -c_{ij}$ for $j < i$, $A_{ij} = 0$ for $j > i$), $U$ with rows $u_i^\top$ and $b = (b_i)$, the LCP matrix is
--   $$M := A - UV^\top. \tag{36}$$
--   $\mathrm{Fix}(\Phi)$ is the set of $\lambda \in [0,1]^d$ with $\Phi(\lambda) = \lambda$, and the circuit is **strict at every fixed point** when $\ell_i(x_{<i}(\lambda), \lambda) \ne 0$ for every gate $i$ and every $\lambda \in \mathrm{Fix}(\Phi)$ (a gate $\max\{0, \ell_i\}$ ties exactly when $\ell_i = 0$).
--
--   **Formalization Note** Indices are 0-based. `NormalForm` carries the data $(d, m, b, U, c, o, p)$; `Anchored`, `A`, `V`, `M`, `exec`, `gateInput` ($\ell_i$ at the execution), `Phi`, `Fix` and `StrictAtFixedPoints` are the objects above.
-- source:
--   Kontogiannis, Panageas, Pollatos, Yan, Finding a Positive Index Nash Equilibrium is PPADS-Complete, arXiv:2609.23879 (held PDF, sha256 00d5c5ce…cbb6), pp. 35–37, §5.1 (31)–(35) and (36)

import Mathlib

namespace PosIndexNash.PPADS

open Matrix

/-- **A max-affine circuit in normal form** (Kontogiannis, Panageas, Pollatos, Yan, *Finding a
Positive Index Nash Equilibrium is PPADS-Complete*, arXiv:2609.23879, §5.1, pp. 35–36, (31)–(33)).

`d` inputs `λ ∈ ℝ^d` and `m` max-gate variables `x_1, …, x_m`; gate `i` is
`x_i = max{0, ℓ_i(x_{<i}, λ)}` with `ℓ_i = b_i + u_iᵀ λ + Σ_{j<i} c_{ij} x_j` (31), where `b_i`
is `b i`, `u_i` is row `i` of `U`, and `c_{ij}` is `c i j` (only `j < i` is read). The `ℓ`-th
output coordinate is the gate `o ℓ`, and `p ℓ` is the gate `p_ℓ` of (32).

**Formalization Note** Indices are 0-based (`Fin m`, `Fin d`). The anchoring structure of the
output gates is the separate predicate `NormalForm.Anchored`. -/
structure NormalForm where
  d : ℕ
  m : ℕ
  b : Fin m → ℚ
  U : Matrix (Fin m) (Fin d) ℚ
  c : Matrix (Fin m) (Fin m) ℚ
  o : Fin d → Fin m
  p : Fin d → Fin m

/-- **Anchored output gates** (arXiv:2609.23879, p. 35–36, (32) and (35)). For every output
coordinate `ℓ`, the gate `p_ℓ` comes immediately before `o_ℓ`, and the gate `o_ℓ` is
`o_ℓ = max{0, 1 − p_ℓ}`: `c_{o_ℓ, p_ℓ} = −1`, `c_{o_ℓ, j} = 0` for the other `j < o_ℓ`,
`u_{o_ℓ} = 0` and `b_{o_ℓ} = 1`. The `2d` gates `p_ℓ, o_ℓ` are distinct. -/
def NormalForm.Anchored (F : NormalForm) : Prop :=
  Function.Injective F.o ∧ (∀ l l', F.p l ≠ F.o l') ∧
  ∀ l, (F.p l).val + 1 = (F.o l).val ∧ F.c (F.o l) (F.p l) = -1 ∧
    (∀ j, j < F.o l → j ≠ F.p l → F.c (F.o l) j = 0) ∧
    (∀ k, F.U (F.o l) k = 0) ∧ F.b (F.o l) = 1

/-- **The matrix `A`** (p. 36): `A_ii = 1`, `A_ij = −c_ij` for `j < i`, `A_ij = 0` for `j > i`;
unit lower triangular. -/
def NormalForm.A (F : NormalForm) : Matrix (Fin F.m) (Fin F.m) ℚ :=
  Matrix.of fun i j => if i = j then 1 else if j < i then -F.c i j else 0

/-- **The selector matrix `V ∈ {0,1}^{m×d}`** (p. 36, (33)): column `ℓ` is `e_{o_ℓ}`. -/
def NormalForm.V (F : NormalForm) : Matrix (Fin F.m) (Fin F.d) ℚ :=
  Matrix.of fun i l => if i = F.o l then 1 else 0

/-- **The LCP matrix** `M := A − U Vᵀ ∈ ℚ^{m×m}` (p. 37, (36)). -/
def NormalForm.M (F : NormalForm) : Matrix (Fin F.m) (Fin F.m) ℚ :=
  F.A - F.U * F.Vᵀ

/-- Gate values by recursion on the gate index (auxiliary for `NormalForm.exec`). -/
noncomputable def NormalForm.execNat (F : NormalForm) (lam : Fin F.d → ℝ) (i : ℕ) : ℝ :=
  if h : i < F.m then
    Max.max 0 ((F.b ⟨i, h⟩ : ℝ) + ∑ k, (F.U ⟨i, h⟩ k : ℝ) * lam k +
      ∑ j : Fin i, (F.c ⟨i, h⟩ ⟨j, j.2.trans h⟩ : ℝ) * F.execNat lam j)
  else 0
termination_by i
decreasing_by exact j.2

/-- **The circuit execution `x(λ)`** (p. 36–37): the vector of all max-gate values on input
`λ ∈ ℝ^d`, computed gate by gate, `x_i = max{0, ℓ_i(x_{<i}, λ)}`. -/
noncomputable def NormalForm.exec (F : NormalForm) (lam : Fin F.d → ℝ) : Fin F.m → ℝ :=
  fun i => F.execNat lam i

/-- **The affine input `ℓ_i(x_{<i}(λ), λ)` of gate `i`** at the circuit execution on `λ`
(p. 35, (31)). The max gate `i` ties exactly when this value is `0` (p. 35). -/
noncomputable def NormalForm.gateInput (F : NormalForm) (lam : Fin F.d → ℝ) (i : Fin F.m) : ℝ :=
  (F.b i : ℝ) + ∑ k, (F.U i k : ℝ) * lam k +
    ∑ j, (if j < i then (F.c i j : ℝ) else 0) * F.exec lam j

/-- **The map `Φ(λ) = Vᵀ x(λ)`** computed by the circuit (p. 36, (33)): coordinate `ℓ` is the
value of the output gate `o_ℓ`. -/
noncomputable def NormalForm.Phi (F : NormalForm) (lam : Fin F.d → ℝ) : Fin F.d → ℝ :=
  fun l => F.exec lam (F.o l)

/-- **The fixed point set `Fix(Φ)`** of `Φ` on `[0, 1]^d` (p. 37). -/
def NormalForm.Fix (F : NormalForm) : Set (Fin F.d → ℝ) :=
  {lam | (∀ l, 0 ≤ lam l ∧ lam l ≤ 1) ∧ F.Phi lam = lam}

/-- **Strict at every fixed point** (p. 35: "every fixed point is circuit strict"): at every
fixed point no max gate ties, i.e. `ℓ_i ≠ 0` for every gate `i`. -/
def NormalForm.StrictAtFixedPoints (F : NormalForm) : Prop :=
  ∀ lam ∈ F.Fix, ∀ i, F.gateInput lam i ≠ 0

end PosIndexNash.PPADS


