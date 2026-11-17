-- Prove2me | Definitions.Def_RandomInvolutions
-- name    : RandomInvolutions
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-16T11:45:32.891888+00:00
-- url     : https://prove2.me/theorems/2fec341d-8ff0-44ee-803e-6781a22f2d0a
-- title:
--   Random involutions with prescribed numbers of fixed points, and the counting functions of their trace expansion
-- statement:
--   Definitions for a proof that independent uniform random involutions of $\{0,\dots,N-1\}$, restricted to the orthogonal complement of the constants, converge strongly to the free generators of $\Gamma_r = \mathbb Z_2^{*r}$. The proof conditions on the numbers of fixed points. The group is `BordenaveCollins.G 0 r`, the free product of the trivial free group with $r$ copies of $\mathbb Z_2$, with generators `mI i` (written $m_i$).
--
--   - `InvK N k`: the involutions of $\{0,\dots,N-1\}$ (identity included) with exactly $k$ fixed points. `OmK r N κ`: $r$-tuples $(\tau_i)$ with $\tau_i$ in `InvK N (κ i)`. `homI`, `homK`: the action $m_i \mapsto \tau_i$ of $\Gamma_r$.
--   - `AdmK N κ`: $\kappa_i \le N$ and $\kappa_i \equiv N \pmod 2$ for all $i$. `admF κ`: the filter $N \to \infty$ through admissible $N$, which is $\bot$ when the $\kappa_i$ have mixed parities. `lam κ` $= 1 + \sum_i \kappa_i$.
--   - `expFixOn`, `expFixK r N κ g`: the expected number of fixed points of $g(\tau)$, for uniform $\tau$ in a finite family or in `OmK r N κ`. The value is $0$ on an empty family.
--   - `perpOp π x`: for $x = \sum_g x_g\, g$ with $D \times D$ matrix coefficients, the operator $(I_D \otimes Q)\big(\sum_g x_g \otimes P_{\pi(g)}\big)(I_D \otimes Q)$ on $(\mathbb C^N)^D$, where $Q = I - J/N$ is the projection onto the vectors with coordinate sum $0$.
--   - `Bcount i g`: the number of $a$ with $g = a\, m_i\, a^{-1}$ and $|g| = 2|a| + 1$. This is the coefficient of $\kappa_i$ in the first-order term of the expected fixed-point count.
--   - `C2count i j g`: the number of $(a, b, c, k)$ with $k \ge 1$, $g = a\,(b\, m_j\, b^{-1}\, c\, m_i\, c^{-1})^k\, a^{-1}$ and $|g| = 2|a| + k(2|b| + 2|c| + 2)$. The quadratic-in-$\kappa$ part of the second-order term is $\sum_{i,j} \kappa_i \kappa_j\,$`C2count i j`.
-- source:
--   Barbieri, M. and Jezernik, U., Strong convergence of random representations of free products of finite groups, arXiv:2602.11905 (2026), https://arxiv.org/abs/2602.11905, the objects of a proof of its theorem for Γ = Z_2^{*r} (uniform random involutions); by conditioning on the numbers of fixed points and the polynomial method of Chen, C.-F., Garza-Vargas, J., Tropp, J. A. and van Handel, R., A new approach to strong convergence, Ann. of Math. (2) 203 (2026) 555–602, https://doi.org/10.4007/annals.2026.203.2.4 (arXiv:2405.16026v3, whose page numbers are used)

import Mathlib
import Definitions.Def_BordenaveCollins
import Definitions.Def_DerandSq_mGen
import Definitions.Def_DerandSq_permOp
import Definitions.Def_DerandSq_perpCompress
import Definitions.Def_ZigZagStrong_ZigZag_Models

/-!
# Strong convergence of uniform random involutions: definitions

Definitions for the strong convergence of independent uniform random involutions of `Fin N` to
the generators of `Γ_r = Z₂^{*r}`, by conditioning on the numbers of fixed points. The group is
`BordenaveCollins.G 0 r` (no free generators, `r` involutions).

* `mI i`: the `i`-th generator; `homI τ : G 0 r →* Perm (Fin N)` for a tuple of involutions `τ`.
* The conditional model `OmK r N κ`: the `i`-th involution has exactly `κ i` fixed points; the
  sizes `AdmK N κ` (`κ i ≤ N`, `κ i ≡ N mod 2`), the filter `admF κ` of such sizes, the weight
  `lam κ = 1 + ∑ κ i`.
* Expected fixed points `expFixOn`, `expFixK`; the compressed model operator `perpOp`.
* The coefficient counts `Bcount` (reduced conjugates of `m_i`) and `C2count` (the two-loop
  shapes `a (ρ m_j ρ⁻¹ σ m_i σ⁻¹)^t a⁻¹`).
-/

open Finset BordenaveCollins

noncomputable section

namespace RandomInvolutions

/-! ## The group `Γ_r = G 0 r` -/

/-- The involutive generator `m_i ∈ G 0 r`. -/
def mI {r : ℕ} (i : Fin r) : G 0 r := Monoid.Coprod.inr (DerandSq.mGen i)

/-! ## Involutions and the representation they define -/

/-- The homomorphism `Z₂ → Perm (Fin N)` of an involution `σ`: the generator goes to `σ`. -/
def invHomI {N : ℕ} (σ : ZigZagStrong.ZigZag.Involution N) :
    Multiplicative (ZMod 2) →* Equiv.Perm (Fin N) where
  toFun a := σ.1 ^ (Multiplicative.toAdd a).val
  map_one' := by simp
  map_mul' a b := by
    have hσ : σ.1 * σ.1 = 1 := by
      ext x; simp [σ.2 x]
    have key : ∀ a b : ZMod 2, σ.1 ^ (a + b).val = σ.1 ^ a.val * σ.1 ^ b.val := by
      intro a b
      fin_cases a <;> fin_cases b
      · show σ.1 ^ (0 : ZMod 2).val = σ.1 ^ (0 : ZMod 2).val * σ.1 ^ (0 : ZMod 2).val
        simp
      · show σ.1 ^ (1 : ZMod 2).val = σ.1 ^ (0 : ZMod 2).val * σ.1 ^ (1 : ZMod 2).val
        simp
      · show σ.1 ^ (1 : ZMod 2).val = σ.1 ^ (1 : ZMod 2).val * σ.1 ^ (0 : ZMod 2).val
        simp
      · show σ.1 ^ ((1 : ZMod 2) + 1).val = σ.1 ^ (1 : ZMod 2).val * σ.1 ^ (1 : ZMod 2).val
        have h11 : ((1 : ZMod 2) + 1) = 0 := by decide
        rw [h11]; simp [ZMod.val_one, hσ]
    exact key _ _

/-- The representation of `Γ_r` on `Fin N` given by an `r`-tuple of involutions. -/
def homI {r N : ℕ} (τ : Fin r → ZigZagStrong.ZigZag.Involution N) : G 0 r →* Equiv.Perm (Fin N) :=
  Monoid.Coprod.lift 1 (Monoid.CoprodI.lift fun i => invHomI (τ i))

/-! ## The conditional model `M(N, κ)` -/

/-- Involutions of `Fin N` with exactly `k` fixed points. -/
abbrev InvK (N k : ℕ) := {τ : ZigZagStrong.ZigZag.Involution N // fixCount τ.1 = k}

/-- A sample of the conditional model: the `i`-th involution has exactly `κ i` fixed points. -/
abbrev OmK (r N : ℕ) (κ : Fin r → ℕ) := (i : Fin r) → InvK N (κ i)

/-- The representation of a sample of the conditional model. -/
def homK {r N : ℕ} {κ : Fin r → ℕ} (τ : OmK r N κ) : G 0 r →* Equiv.Perm (Fin N) :=
  homI (fun i => (τ i).1)

/-- Admissible sizes: `κ i ≤ N` and `κ i ≡ N (mod 2)` for all `i`. -/
def AdmK {r : ℕ} (N : ℕ) (κ : Fin r → ℕ) : Prop := ∀ i, κ i ≤ N ∧ κ i % 2 = N % 2

/-- The filter of large admissible sizes. -/
def admF {r : ℕ} (κ : Fin r → ℕ) : Filter ℕ := Filter.atTop ⊓ Filter.principal {N | AdmK N κ}

/-- The weight `1 + ∑ κ i`. -/
def lam {r : ℕ} (κ : Fin r → ℕ) : ℝ := 1 + ∑ i, (κ i : ℝ)

/-! ## Expected fixed points -/

/-- `E[fix(act ω g)]` for `ω` uniform in a finite sample space (`0` if it is empty). -/
def expFixOn {r N : ℕ} {Ω : Type*} [Fintype Ω] (act : Ω → G 0 r →* Equiv.Perm (Fin N))
    (g : G 0 r) : ℝ :=
  (∑ ω : Ω, (fixCount (act ω g) : ℝ)) / (Fintype.card Ω : ℝ)

/-- `E_{N,κ}[fix g]` in the conditional model. -/
def expFixK (r N : ℕ) (κ : Fin r → ℕ) (g : G 0 r) : ℝ :=
  expFixOn (fun τ : OmK r N κ => homK τ) g

/-! ## Operators -/

/-- `x` in the permutation representation `π`, compressed to `1^⊥`, on `D` copies of `ℂ^N`. -/
def perpOp {r D N : ℕ} (π : G 0 r →* Equiv.Perm (Fin N)) (x : MG D 0 r) :=
  DerandSq.perpCompress D N (opOf (fun g : G 0 r => DerandSq.permOp (π g)) x)

/-! ## The coefficient counts -/

/-- `B_i(g)`: the number of ways to write `g` as a reduced product `a m_i a⁻¹` (reduced: the
length of `g` is `2 |a| + 1`). -/
def Bcount {r : ℕ} (i : Fin r) (g : G 0 r) : ℕ :=
  Nat.card {a : G 0 r // g = a * mI i * a⁻¹ ∧ len g = 2 * len a + 1}

/-- `C_{2,ij}(g)`: the number of ways to write `g` as a reduced product
`a (ρ m_j ρ⁻¹ σ m_i σ⁻¹)^t a⁻¹` with `t ≥ 1` (reduced: the length of `g` is
`2 |a| + t (2 |ρ| + 2 |σ| + 2)`). Tuples are `(a, ρ, σ, t)`. -/
def C2count {r : ℕ} (i j : Fin r) (g : G 0 r) : ℕ :=
  Nat.card {p : G 0 r × G 0 r × G 0 r × ℕ // 1 ≤ p.2.2.2 ∧
    g = p.1 * (p.2.1 * mI j * p.2.1⁻¹ * (p.2.2.1 * mI i * p.2.2.1⁻¹)) ^ p.2.2.2 * p.1⁻¹ ∧
    len g = 2 * len p.1 + p.2.2.2 * (2 * len p.2.1 + 2 * len p.2.2.1 + 2)}

end RandomInvolutions

end


