-- Prove2me | Definitions.Def_QDSGibbs_IsChannel
-- name    : QDSGibbs_IsChannel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:34:09.226408+00:00
-- url     : https://prove2.me/theorems/10a971c0-43c4-403e-bfe9-df73bcc0b4c1
-- title:
--   Channels, diamond norm, maps supported on a region, Heisenberg adjoint, KMS inner product, and the semigroup $e^{tK}$
-- statement:
--   A **channel** on $\mathcal B(\mathcal H)$ is a map with a Kraus representation $\Phi(X)=\sum_j E_jXE_j^*$, $\sum_jE_j^*E_j=\mathbb 1$ (equivalently, completely positive and trace preserving). The **diamond norm** of a map $F$ is
--
--   $$
--   \|F\|_\diamond=\sup_{m\ge1}\ \sup_{X\ne0}\frac{\|(F\otimes\mathrm{id}_m)(X)\|_1}{\|X\|_1},
--   $$
--
--   with $X$ ranging over nonzero operators on $\mathcal H\otimes\mathbb C^m$. A map is **supported on** $R$ when it is $\Phi_R\otimes\mathrm{id}_{R^c}$. The **Heisenberg adjoint** $F^*$ is defined by $\mathrm{Tr}[O\,F(X)]=\mathrm{Tr}[F^*(O)X]$, and the **KMS inner product** of a state $\sigma$ is $\langle A,C\rangle_\sigma=\mathrm{Tr}(A^*\sigma^{1/2}C\sigma^{1/2})$. Finally, for a map $K$ on matrices,
--
--   $$
--   e^{tK}(X)=\sum_{k\ge0}\frac{t^k}{k!}K^k(X).
--   $$
--
--   **Formalization Note** The diamond norm takes values in $[0,\infty]$. Support of a map is stated through an explicit kernel on configurations of $R$. The series is summed entrywise; for the linear maps of this mission it converges absolutely in finite dimension. Maps are plain functions; the Kraus form makes a channel linear.
-- source:
--   Rouzé–Stilck França, Rapid mixing of Gibbs samplers via quantum Dobrushin–Shlosman conditions, arXiv:2610.03578 (held file sha256 ede55815…), §2.2, p.12; (3.14), p.19

import Mathlib
import Definitions.Def_QDSGibbs_traceNorm

open scoped Matrix ComplexOrder ENNReal

namespace QDSGibbs

/-- A **channel** (CPTP map) on `B(H)`, `H` finite dimensional (arXiv:2610.03578, held file sha256
ede55815…, §2.2, p.12): a map with a finite Kraus representation `Φ(X) = Σ_j E_j X E_j^*`,
`Σ_j E_j^* E_j = 1`.

**Formalization Note** In finite dimension the Kraus form is equivalent to complete positivity plus
trace preservation (Choi–Kraus); the index type `Fin k` loses no generality. Same shape as the
platform's `QAlgorithms.IsChannel`. The map is a plain function; the Kraus form makes it linear. -/
def IsChannel {n : Type} [Fintype n] [DecidableEq n] (Φ : Matrix n n ℂ → Matrix n n ℂ) : Prop :=
  ∃ (k : ℕ) (E : Fin k → Matrix n n ℂ), ∑ j, (E j)ᴴ * E j = 1 ∧ ∀ X, Φ X = ∑ j, E j * X * (E j)ᴴ

/-- `F ⊗ id_m` on `B(H_Λ ⊗ ℂ^m)`: `((F ⊗ id_m) X)_{(x,a),(y,b)} = F(X_{ab})_{x,y}`, where `X_{ab}` is
the `(a,b)` block of `X` (arXiv:2610.03578, §2.2, p.12). -/
def tensorId {N : ℕ} {d : Fin N → ℕ} (F : Op d → Op d) (m : ℕ)
    (X : Matrix (Cfg d × Fin m) (Cfg d × Fin m) ℂ) : Matrix (Cfg d × Fin m) (Cfg d × Fin m) ℂ :=
  Matrix.of fun p q => F (Matrix.of fun x y => X (x, p.2) (y, q.2)) p.1 q.1

/-- The **diamond norm** `‖F‖⋄ = sup_{m ≥ 1} sup_{X ≠ 0} ‖(F ⊗ id_m)(X)‖₁ / ‖X‖₁`
(arXiv:2610.03578, §2.2, p.12): `m` ranges over the positive integers and `X` over all nonzero
operators on the input tensored with an `m`-dimensional reference system.

**Formalization Note** Valued in `ℝ≥0∞`: an unbounded set of ratios gives `⊤`, never the junk value
`0` of a real supremum. -/
noncomputable def diamondNorm {N : ℕ} {d : Fin N → ℕ} (F : Op d → Op d) : ℝ≥0∞ :=
  ⨆ (m : ℕ) (_ : 1 ≤ m) (X : Matrix (Cfg d × Fin m) (Cfg d × Fin m) ℂ) (_ : X ≠ 0),
    ENNReal.ofReal (traceNorm (tensorId F m X) / traceNorm X)

/-- A map **supported on** `R` (arXiv:2610.03578, §2.2, p.12, "a channel on `B(H_R)` tensored with
the identity on `R^c`"): `Φ = Φ_R ⊗ id_{R^c}`. Entrywise, there is a kernel `κ` on
`R`-configurations with `Φ(X)_{x,y} = Σ_{z,w} κ(x_R, y_R, z, w) X_{(z, x_{R^c}), (w, y_{R^c})}`
(`κ(a, b, z, w) = Φ_R(|z⟩⟨w|)_{a,b}`). "Supported away from `j`" is `MapSupportedOn (univ.erase j)`. -/
def MapSupportedOn {N : ℕ} {d : Fin N → ℕ} (R : Finset (Fin N)) (Φ : Op d → Op d) : Prop :=
  ∃ κ : SubCfg d R → SubCfg d R → SubCfg d R → SubCfg d R → ℂ, ∀ (X : Op d) (x y : Cfg d),
    Φ X x y = ∑ z : SubCfg d R, ∑ w : SubCfg d R, κ (restr R x) (restr R y) z w * X (glue R z x) (glue R w y)

/-- The **Hilbert–Schmidt (Heisenberg) adjoint** `Φ^*` of a map, `Tr[O Φ(X)] = Tr[Φ^*(O) X]`
(arXiv:2610.03578, §2.2, p.12), computed on matrix units:
`Φ^*(Y)_{x,y} = Σ_{a,b} Y_{a,b} Φ(|y⟩⟨x|)_{b,a}`. -/
noncomputable def heisAdj {n : Type} [Fintype n] [DecidableEq n] (Φ : Matrix n n ℂ → Matrix n n ℂ)
    (Y : Matrix n n ℂ) : Matrix n n ℂ :=
  Matrix.of fun x y => ∑ a, ∑ b, Y a b * Φ (Matrix.single y x 1) b a

/-- The **KMS inner product** `⟨A, C⟩_σ = Tr(A^* σ^{1/2} C σ^{1/2})` (arXiv:2610.03578, §2.2, p.12).

**Formalization Note** `σ^{1/2}` is the continuous functional calculus `cfc Real.sqrt σ` (the positive
square root of a positive semidefinite `σ`). -/
noncomputable def kmsInner {n : Type} [Fintype n] [DecidableEq n] (σ A C : Matrix n n ℂ) : ℂ :=
  (Aᴴ * cfc Real.sqrt σ * C * cfc Real.sqrt σ).trace

/-- The **semigroup** `e^{tK}` of a map `K` on matrices (arXiv:2610.03578, §2.2, p.12; (3.14)):
the exponential series `e^{tK}(X) = Σ_{k ≥ 0} (t^k / k!) K^k(X)`, summed entrywise.

**Formalization Note** `K^k` is the `k`-fold iterate. For the linear maps to which it is applied
(all built from matrix products and partial traces) the series converges absolutely in finite
dimension, so the entrywise `tsum` is the usual exponential. -/
noncomputable def sexp {n : Type} (K : Matrix n n ℂ → Matrix n n ℂ) (t : ℝ) (X : Matrix n n ℂ) :
    Matrix n n ℂ :=
  Matrix.of fun x y => ∑' k : ℕ, ((t ^ k / (Nat.factorial k : ℝ) : ℝ) : ℂ) * (K^[k] X) x y

end QDSGibbs


