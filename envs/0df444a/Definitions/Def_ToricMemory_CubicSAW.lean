-- Prove2me | Definitions.Def_ToricMemory_CubicSAW
-- name    : ToricMemory_CubicSAW
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:20:48.834305+00:00
-- url     : https://prove2.me/theorems/777cf0f4-04bf-4195-802c-5232fc1e4b23
-- title:
--   Self-avoiding walks and polygons in $\mathbb Z^3$ and the connective constant $\mu_3$
-- statement:
--   An **$n$-step self-avoiding walk** in $\mathbb Z^3$ is a sequence of $n$ unit steps $\pm e_x,\pm e_y,\pm e_z$ from the origin whose positions $v_0=0,v_1,\dots,v_n$ are pairwise distinct. Let $c_n$ be their number. The **connective constant** of the cubic lattice is
--   $$
--   \mu_3=\inf_{n\ge1}c_n^{1/n},
--   $$
--   which equals $\lim_{n\to\infty}c_n^{1/n}$ because $c_{m+n}\le c_mc_n$; numerically $\mu_3\approx4.684$.
--
--   A **rooted self-avoiding polygon** of $\ell$ steps at the origin is a closed walk $v_0=0,v_1,\dots,v_\ell=0$ with $v_0,\dots,v_{\ell-1}$ pairwise distinct and $\ell\ge3$. Their number, with each orientation counted separately, is $n^{(3)}_{\rm SAP}(\ell)$.
--
--   These counts enter the bound (58) on self-avoiding polygons and, through it, the threshold condition (60).
--
--   **Formalization Note** $\mu_3$ is defined exactly; the decimal $4.684$ is never used. The condition $\ell\ge3$ excludes the walk that steps out and back.
-- source:
--   Dennis, Kitaev, Landahl & Preskill, Topological quantum memory, arXiv:quant-ph/0110143v1, Sec. V C, eq. (58), p. 20 (n_SAP^(3)(ℓ) and μ₃ ≈ 4.684); Sec. V B, p. 19 (walks and SAP's)

import Mathlib

namespace ToricMemory

/-- The six unit steps `±e_x, ±e_y, ±e_z` of the cubic lattice `ℤ³`. -/
def zStep : Fin 6 → ℤ × ℤ × ℤ
  | 0 => (1, 0, 0)
  | 1 => (-1, 0, 0)
  | 2 => (0, 1, 0)
  | 3 => (0, -1, 0)
  | 4 => (0, 0, 1)
  | 5 => (0, 0, -1)

/-- The position after the first `i` steps of the walk `w` started at the origin of `ℤ³`. -/
def walkPos {n : ℕ} (w : Fin n → Fin 6) (i : ℕ) : ℤ × ℤ × ℤ :=
  ((List.ofFn fun j => zStep (w j)).take i).sum

/-- `w` is an `n`-step **self-avoiding walk** in `ℤ³` from the origin: the positions
`v₀ = 0, v₁, …, v_n` are pairwise distinct. -/
def IsSAW3 {n : ℕ} (w : Fin n → Fin 6) : Prop :=
  Function.Injective fun i : Fin (n + 1) => walkPos w i

instance {n : ℕ} (w : Fin n → Fin 6) : Decidable (IsSAW3 w) :=
  inferInstanceAs (Decidable (Function.Injective _))

/-- `c_n`, the number of `n`-step self-avoiding walks in `ℤ³` from the origin. -/
def saw3 (n : ℕ) : ℕ := (Finset.univ.filter fun w : Fin n → Fin 6 => IsSAW3 w).card

/-- The **connective constant** `μ₃` of the cubic lattice, `μ₃ = inf_{n ≥ 1} c_n^{1/n}`, which
equals `lim_n c_n^{1/n}` by submultiplicativity of `c_n` (Fekete's lemma; Hammersley).
arXiv:quant-ph/0110143v1, Sec. V C, eq. (58), p. 20 uses this constant, writing `μ₃ ≈ 4.684`.

**Formalization Note** The constant is defined exactly; the decimal `4.684` of the paper is its
numerical value and is not used. The infimum is over a nonempty set of nonnegative reals. -/
noncomputable def mu3 : ℝ := ⨅ n : {n : ℕ // 1 ≤ n}, (saw3 n.1 : ℝ) ^ (1 / (n.1 : ℝ))

/-- `w` is a rooted **self-avoiding polygon** of `ℓ` steps in `ℤ³` at the origin: a closed walk
`v₀ = 0, v₁, …, v_ℓ = 0` with `v₀, …, v_{ℓ−1}` pairwise distinct and `ℓ ≥ 3` (which excludes
the back-and-forth walk of length 2). -/
def IsSAP3 {ℓ : ℕ} (w : Fin ℓ → Fin 6) : Prop :=
  3 ≤ ℓ ∧ walkPos w ℓ = 0 ∧ Function.Injective fun i : Fin ℓ => walkPos w i

instance {ℓ : ℕ} (w : Fin ℓ → Fin 6) : Decidable (IsSAP3 w) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- `n_SAP^{(3)}(ℓ)` of arXiv:quant-ph/0110143v1, Sec. V C, eq. (58), p. 20: the number of
`ℓ`-step self-avoiding polygons in `ℤ³` with a specified starting site (the origin), each
orientation counted separately, as walks are on p. 19. -/
def sapZ3 (ℓ : ℕ) : ℕ := (Finset.univ.filter fun w : Fin ℓ → Fin 6 => IsSAP3 w).card

end ToricMemory


