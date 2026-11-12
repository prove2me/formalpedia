-- Prove2me | Definitions.Def_SepQPTardos_Main_Circuits
-- name    : SepQPTardos_Main_Circuits
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T07:11:24.620692+00:00
-- url     : https://prove2.me/theorems/09ddfece-fb66-41e6-807b-1a514a9b87d0
-- title:
--   Circuits, conformality, primitive integer vectors, and the constants $U$, $G=(rU)^r$, $\kappa=mG$
-- statement:
--   Let $D$ be a real $p\times n$ matrix and $v\in\mathbb R^n$; write $\operatorname{supp}v=\{e:v_e\ne0\}$.
--
--   1. $v$ is a **circuit** of $D$ if $v\ne0$, $Dv=0$, and no nonzero kernel vector $w$ has $\operatorname{supp}w\subsetneq\operatorname{supp}v$ (inclusion-minimal support).
--   2. $h$ is **conformal** to $v$ if $h_ev_e\ge0$ for every $e$ (sign-compatibility) and $\operatorname{supp}h\subseteq\operatorname{supp}v$.
--   3. An integer vector is **primitive** if the greatest common divisor of its entries is $1$.
--   4. For an integer $r\times m$ matrix $A$,
--   $$U=\max\Bigl(1,\max_{i,e}|A_{ie}|\Bigr),\qquad G=(rU)^r,\qquad \kappa=mG .$$
--   For $r=0$ the convention $0^0=1$ gives $G=1$.
--
--   Circuits of bounded size are the paper's main structural tool: conformal circuit decompositions without cancellation connect continuous optima, integer optima and the auxiliary LPs.
-- source:
--   Bin Cui, Hanqing Li, Xupeng Miao, STOC 2027 submission #829 (October 2026), §2.1, eq. (3) and the definitions of circuit and conformality, p. 4; κ on p. 8

import Mathlib

open Matrix

namespace SepQPTardos.Main

/-!
# Circuits, conformality and the constants `U`, `G` of (3)

Cui–Li–Miao, STOC 2027 submission #829 (October 2026), §2.1, p. 4.

* A **circuit** of a matrix is a nonzero kernel vector with inclusion-minimal support.
* Two vectors are **sign-compatible** if their coordinate products are nonnegative; `h` is
  **conformal** to `v` if it is sign-compatible with `v` and `supp h ⊆ supp v`.
* An integer vector is **primitive** if the gcd of its entries is `1`.
* `U = max(1, maxᵢₑ |Aᵢₑ|)` and `G = (rU)^r`, eq. (3).
-/

variable {p n : ℕ}

/-- The support `{e : vₑ ≠ 0}` of a real vector. -/
def supp (v : Fin n → ℝ) : Set (Fin n) := {e | v e ≠ 0}

/-- `v` is a circuit of `D`: a nonzero kernel vector whose support is inclusion-minimal among
the supports of nonzero kernel vectors. -/
def IsCircuit (D : Matrix (Fin p) (Fin n) ℝ) (v : Fin n → ℝ) : Prop :=
  v ≠ 0 ∧ D *ᵥ v = 0 ∧
    ∀ w : Fin n → ℝ, w ≠ 0 → D *ᵥ w = 0 → supp w ⊆ supp v → supp w = supp v

/-- `h` is conformal to `v`: `hₑ vₑ ≥ 0` for every `e`, and `supp h ⊆ supp v`. -/
def Conformal (h v : Fin n → ℝ) : Prop :=
  (∀ e, 0 ≤ h e * v e) ∧ supp h ⊆ supp v

/-- An integer vector is primitive: the gcd of its entries is `1`. -/
def Primitive (h : Fin n → ℤ) : Prop := Finset.univ.gcd h = 1

/-- An integer vector viewed as a real vector. -/
def castIntVec (h : Fin n → ℤ) : Fin n → ℝ := fun e => (h e : ℝ)

/-- `U = max(1, maxᵢₑ |Aᵢₑ|)`, eq. (3). -/
def Ubound {r m : ℕ} (A : Matrix (Fin r) (Fin m) ℤ) : ℕ :=
  max 1 (Finset.univ.sup fun ie : Fin r × Fin m => (A ie.1 ie.2).natAbs)

/-- `G = (rU)^r`, eq. (3). (For `r = 0` this is `1`.) -/
def Gbound {r m : ℕ} (A : Matrix (Fin r) (Fin m) ℤ) : ℕ := (r * Ubound A) ^ r

/-- `κ = mG`, p. 8. -/
def kappa {r m : ℕ} (A : Matrix (Fin r) (Fin m) ℤ) : ℕ := m * Gbound A

end SepQPTardos.Main


