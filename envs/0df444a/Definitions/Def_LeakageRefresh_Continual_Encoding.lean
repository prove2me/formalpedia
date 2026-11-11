-- Prove2me | Definitions.Def_LeakageRefresh_Continual_Encoding
-- name    : LeakageRefresh_Continual_Encoding
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T23:08:25.55695+00:00
-- url     : https://prove2.me/theorems/849d89c0-9e3b-4e83-81ef-f9e17e5a6384
-- title:
--   Inner-product encodings over $\mathbb F_2$: nonzero shares $U_L,U_R$, the refresh $(\ell,r)\mapsto(\ell M,M^{-1}r)$, the classes $\Omega_s$ and the uniform laws $\mu_s$
-- statement:
--   Fix $n\ge 2$ and put $N=2^n$, $q=N-1$. Let $U_L$ be the set of nonzero row vectors and $U_R$ the set of nonzero column vectors of $\mathbb F_2^n$; each has $q$ elements. A **state** is a pair $x=(\ell,r)\in U_L\times U_R$; it **encodes** the bit
--   $$\ell\cdot r=\sum_{k=1}^n \ell_k r_k\in\mathbb F_2 .$$
--   For $s\in\mathbb F_2$ the **class** of $s$ is $\Omega_s=\{(\ell,r)\in U_L\times U_R:\ \ell\cdot r=s\}$ and $\mu_s$ is the uniform distribution on $\Omega_s$; $\nu$ is the uniform distribution on $U_L\times U_R$. $\mathrm{InvMatr}^n_2$ is the set of invertible $n\times n$ matrices over $\mathbb F_2$. A **refresh** by $M\in\mathrm{InvMatr}^n_2$ maps the state $(\ell,r)$ to $(\ell\cdot M,\ M^{-1}\cdot r)$; it preserves $\ell\cdot r$ and keeps both shares nonzero.
--
--   These are the objects of the matrix refresh protocol whose security under continual leakage is the subject of the mission.
--
--   **Formalization Note.** Rows and columns are both `Fin n → ZMod 2`; `UL n` and `UR n` are the subtype of nonzero vectors. `InvMatr n` is `GL (Fin n) (ZMod 2)`. `refreshL M ℓ` is `Matrix.vecMul ℓ M`, `refreshR M r` is `Matrix.mulVec (M⁻¹) r`, both with a proof that the result is nonzero; `refreshState` applies both. `secret x` is the dot product; `Omega n s` is a `Finset`. A distribution on a finite set is its point-probability function: `mu n s x` is $1/|\Omega_s|$ on $\Omega_s$ and $0$ elsewhere; `muExp n s F` $=\mathbb E_{x\leftarrow\mu_s}[F(x)]$ and `nuExp n F` $=\mathbb E_{x\leftarrow\nu}[F(x)]$. For $n\ge2$ both classes are nonempty, so `mu` is a probability distribution there.
-- source:
--   Dziembowski, Faust, Leakage-Resilient Computation via Matrix Refreshing, arXiv:2611.04876 (sha256 fdbb2454…), p. 16, Definition 2.3; p. 17, Definition 2.4; p. 23, Definition 2.18

import Mathlib

/-!
# Inner-product encodings over `F₂` and the matrix refresh

Dziembowski, Faust, *Leakage-Resilient Computation via Matrix Refreshing*, arXiv:2611.04876
(sha256 fdbb2454…), §2.2, Definitions 2.3 and 2.4, pp. 16–17; Definition 2.18, p. 23.

* `UL n`, `UR n`: the nonzero row and the nonzero column vectors of `F₂ⁿ` (both `Fin n → ZMod 2`);
  each has `q = 2ⁿ − 1` elements.
* `InvMatr n = GL (Fin n) (ZMod 2)`: the invertible `n × n` matrices over `F₂`.
* `refreshL M ℓ = ℓ · M` (`Matrix.vecMul`), `refreshR M r = M⁻¹ · r` (`Matrix.mulVec` with the
  group inverse); both stay nonzero, so they are maps `UL n → UL n` and `UR n → UR n`.
* `State n = UL n × UR n`; `secret x = ℓ · r = ∑ₖ ℓₖ rₖ ∈ F₂`; `Omega n s = Ωₛ`.
* `mu n s x` is the point probability of the uniform distribution `µₛ` on `Ωₛ`; `muExp n s F` is
  `E_{x ←$ µₛ}[F x]`; `nuExp n F` is the expectation under the uniform distribution `ν` on
  `U_L × U_R`.
-/

namespace LeakageRefresh.Continual

/-- `U_L`: the nonzero row vectors of `F₂ⁿ` (Definition 2.3). -/
abbrev UL (n : ℕ) := {v : Fin n → ZMod 2 // v ≠ 0}

/-- `U_R`: the nonzero column vectors of `F₂ⁿ` (Definition 2.3). -/
abbrev UR (n : ℕ) := {v : Fin n → ZMod 2 // v ≠ 0}

/-- `InvMatrⁿ₂`: the invertible `n × n` matrices over `F₂`. -/
abbrev InvMatr (n : ℕ) := Matrix.GeneralLinearGroup (Fin n) (ZMod 2)

/-- A joint state `(ℓ, r) ∈ U_L × U_R`. -/
abbrev State (n : ℕ) := UL n × UR n

/-- The left refresh `ℓ ↦ ℓ · M` (row vector times matrix); it maps nonzero rows to nonzero rows. -/
def refreshL {n : ℕ} (M : InvMatr n) (ℓ : UL n) : UL n :=
  ⟨Matrix.vecMul ℓ.1 (M : Matrix (Fin n) (Fin n) (ZMod 2)), by
    intro h
    apply ℓ.2
    have h2 := congrArg (fun w => Matrix.vecMul w ((M⁻¹ : InvMatr n) : Matrix (Fin n) (Fin n) (ZMod 2))) h
    simp only [Matrix.vecMul_vecMul, Matrix.zero_vecMul] at h2
    rw [← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel, Matrix.GeneralLinearGroup.coe_one,
      Matrix.vecMul_one] at h2
    exact h2⟩

/-- The right refresh `r ↦ M⁻¹ · r` (inverse matrix times column vector); it maps nonzero
columns to nonzero columns. -/
def refreshR {n : ℕ} (M : InvMatr n) (r : UR n) : UR n :=
  ⟨Matrix.mulVec ((M⁻¹ : InvMatr n) : Matrix (Fin n) (Fin n) (ZMod 2)) r.1, by
    intro h
    apply r.2
    have h2 := congrArg (fun w => Matrix.mulVec (M : Matrix (Fin n) (Fin n) (ZMod 2)) w) h
    simp only [Matrix.mulVec_mulVec, Matrix.mulVec_zero] at h2
    rw [← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel, Matrix.GeneralLinearGroup.coe_one,
      Matrix.one_mulVec] at h2
    exact h2⟩

/-- One refresh of a state: `(ℓ, r) ↦ (ℓ · M, M⁻¹ · r)` (Definition 2.4, step 2). -/
def refreshState {n : ℕ} (M : InvMatr n) (x : State n) : State n :=
  (refreshL M x.1, refreshR M x.2)

/-- The bit encoded by a state: `ℓ · r = ∑ₖ ℓₖ rₖ ∈ F₂`. -/
def secret {n : ℕ} (x : State n) : ZMod 2 :=
  dotProduct x.1.1 x.2.1

/-- `Ωₛ = {(ℓ, r) ∈ U_L × U_R : ℓ · r = s}` (Definition 2.3). -/
def Omega (n : ℕ) (s : ZMod 2) : Finset (State n) :=
  Finset.univ.filter (fun x => secret x = s)

/-- The point probability of `µₛ`, the uniform distribution on `Ωₛ` (Definition 2.3). -/
noncomputable def mu (n : ℕ) (s : ZMod 2) (x : State n) : ℝ :=
  if secret x = s then ((Omega n s).card : ℝ)⁻¹ else 0

/-- `E_{x ←$ µₛ}[F x]`. -/
noncomputable def muExp (n : ℕ) (s : ZMod 2) (F : State n → ℝ) : ℝ :=
  ∑ x, mu n s x * F x

/-- `E_{x ←$ ν}[F x]` for the uniform distribution `ν` on `U_L × U_R` (Definition 2.18). -/
noncomputable def nuExp (n : ℕ) (F : State n → ℝ) : ℝ :=
  (Fintype.card (State n) : ℝ)⁻¹ * ∑ x, F x

end LeakageRefresh.Continual


