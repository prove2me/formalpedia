-- Prove2me | Definitions.Def_ChapterH1
-- name    : ChapterH1
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-09T22:39:45.688922+00:00
-- url     : https://prove2.me/theorems/18d70181-58dc-4ce9-9139-5884ddfd89a0
-- title:
--   This file formalizes the algebraic backbone of the Hashimoto–Nodera *Shift-invert Rational Krylov (SIRK)* method (source ...
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.H1`, source chapter `BookProof/ChapterH1.lean`).
--
--   This file formalizes the algebraic backbone of the Hashimoto–Nodera *Shift-invert Rational Krylov (SIRK)* method (source `RiemannProof/Hashimoto.md`; `book.tex` cites at lines 1147 / 2055). It follows §0 S7 of the roadmap (the numerical backbone of the Mehler/Hashimoto Fock formalism), and the `IsSchurFull`/`EXTERNAL` design pattern: the genuinely deep analytic inputs (Crouzeix's inequality, the Göckler–Grimm / Hashimoto RK error theorems) are named hypotheses with citation docstrings in `ChapterH2.lean`, never axioms; everything here is proved outright.
--
--   * **H1.1 — the φ-functions.** `phi : ℕ → ℂ → ℂ`, `phi 0 = exp`, `phi (k+1) z = ∫ s in 0..1, exp (s·z)·(1−s)^k / k!` (eq. 3); `phi_zero`, `phi_at_zero : phi k 0 = 1/k!`. * **H1.2 — the φ-recurrence.** `phi_succ_mul : z · phi (k+1) z = phi k z − 1/k!` (integration by parts); corollary `phi_one : z ≠ 0 → phi 1 z = (exp z − 1)/z`. * **H1.4 — numerical range & eigenvalue inclusion.** `numericalRange A` (the set of Rayleigh quotients) with `eigenvalue_mem_numericalRange` (every eigenvalue lies in `W(A)` — the easy half of Toeplitz–Hausdorff). * **H1.6 — the resolvent shift identity (the clean SIRK algebra core).** The resolvent identity `resolvent_identity` and the SIRK shift form `resolvent_shift_mul : X_j · (1 + h(m−j)·X_m) = X_m` for `γ_j = N − h·j` (§4, between eqs. (10)–(11)) — purely algebraic, no analysis.
--
--   Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`); **no `EXTERNAL` hypothesis**.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterH1.lean

import Mathlib

/-!
# Chapter H1 — Hashimoto SIRK: φ-functions and resolvent algebra (roadmap N13, §0 S7)

This file formalizes the algebraic backbone of the Hashimoto–Nodera *Shift-invert
Rational Krylov (SIRK)* method (source `RiemannProof/Hashimoto.md`; `book.tex`
cites at lines 1147 / 2055).  It follows §0 S7 of the roadmap (the numerical
backbone of the Mehler/Hashimoto Fock formalism), and the `IsSchurFull`/`EXTERNAL`
design pattern: the genuinely deep analytic inputs (Crouzeix's inequality, the
Göckler–Grimm / Hashimoto RK error theorems) are named hypotheses with citation
docstrings in `ChapterH2.lean`, never axioms; everything here is proved outright.

## Deliverables (this file)

* **H1.1 — the φ-functions.** `phi : ℕ → ℂ → ℂ`, `phi 0 = exp`,
  `phi (k+1) z = ∫ s in 0..1, exp (s·z)·(1−s)^k / k!` (eq. 3); `phi_zero`,
  `phi_at_zero : phi k 0 = 1/k!`.
* **H1.2 — the φ-recurrence.** `phi_succ_mul : z · phi (k+1) z = phi k z − 1/k!`
  (integration by parts); corollary `phi_one : z ≠ 0 → phi 1 z = (exp z − 1)/z`.
* **H1.4 — numerical range & eigenvalue inclusion.** `numericalRange A` (the set
  of Rayleigh quotients) with `eigenvalue_mem_numericalRange` (every eigenvalue
  lies in `W(A)` — the easy half of Toeplitz–Hausdorff).
* **H1.6 — the resolvent shift identity (the clean SIRK algebra core).** The
  resolvent identity `resolvent_identity` and the SIRK shift form
  `resolvent_shift_mul : X_j · (1 + h(m−j)·X_m) = X_m` for `γ_j = N − h·j`
  (§4, between eqs. (10)–(11)) — purely algebraic, no analysis.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`); **no `EXTERNAL` hypothesis**.
-/

open scoped BigOperators
open intervalIntegral

namespace BookProof.ChapterH1

noncomputable section

/-! ## H1.1 — the φ-functions and their values -/

/-- The φ-functions (Hashimoto eq. 3): `φ₀ = exp`, and for `k ≥ 0`
`φ_{k+1}(z) = ∫₀¹ e^{s z} (1−s)^k / k! ds`.  Each `φ_k` is entire (a convergent
power series). -/
noncomputable def phi : ℕ → ℂ → ℂ
  | 0, z => Complex.exp z
  | (k + 1), z => ∫ s in (0 : ℝ)..1, Complex.exp (s * z) * (1 - s) ^ k / k.factorial







/-
**H1.1** (values at `0`): `φ_k(0) = 1/k!`.
For `k = 0` this is `exp 0 = 1`.  For `k+1`, the integrand at `z = 0` is
`(1−s)^k / k!`, whose integral over `[0,1]` is `1/((k+1)·k!) = 1/(k+1)!`.
-/


/-! ## H1.2 — the φ-recurrence -/

/-
**H1.2** (recurrence): `z · φ_{k+1}(z) = φ_k(z) − 1/k!`.
Integration by parts on the defining integral: with `u = e^{s z}` and
`dv = (1−s)^k/k! ds`, the boundary terms give `φ_k(z) − 1/k!` and the remaining
integral is `z·φ_{k+1}(z)`.
-/




/-! ## H1.3 — the exponential-integrator Duhamel identity -/

/-- The **operator φ₁-function** as a vector-valued integral (Hashimoto eq. 3 at
`k = 0`, operator form): `phiOp1 M g = ∫₀¹ e^{s·M} g ds`.  This is the operator
analogue of `phi 1` (which is `∫₀¹ e^{s z} ds`). -/
noncomputable def phiOp1 {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (g : Fin n → ℂ) :
    Fin n → ℂ :=
  ∫ s in (0 : ℝ)..1, (NormedSpace.exp (s • M)).mulVec g

/-
**H1.3** (exponential-integrator Duhamel identity, scheme (4)): for a
(bounded) operator `A` the constant-forcing Duhamel term is the operator
φ₁-function, `∫₀^δ e^{(δ−s)·A} g ds = δ · phiOp1 (δ·A) g`.  Proof: substitute
`u = δ − s` (`integral_comp_sub_left`) on the left and `u = δ s`
(`smul_integral_comp_mul_left`) on the right; both equal `∫₀^δ e^{u·A} g du`.
-/


/-! ## H1.4 — numerical range and eigenvalue inclusion -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The **numerical range** `W(A)` of an operator: the set of Rayleigh quotients
`⟪v, A v⟫` over unit vectors `v`. -/
def numericalRange (A : E →ₗ[ℂ] E) : Set ℂ :=
  { c | ∃ v : E, ‖v‖ = 1 ∧ (inner (𝕜 := ℂ) v (A v)) = c }

/-
**H1.4** (eigenvalue inclusion — the easy half of Toeplitz–Hausdorff): every
eigenvalue of `A` lies in its numerical range.  If `A v = λ v` with `‖v‖ = 1`,
then `⟪v, A v⟫ = λ·⟪v, v⟫ = λ·‖v‖² = λ`.
-/


/-! ## H1.5 — the operator φ-function via the resolvent (Definition 2.4) -/

/-- The Taylor(1951)/Güttel(2010) transformed function `ψ_{k,γ}(x) := φ_k(γ − x⁻¹)`
(Hashimoto Definition 2.4).  The operator φ-function is then `φ_k(A) = ψ_{k,γ}(X)`
with `X = (γI − A)⁻¹` (evaluated by the holomorphic functional calculus). -/
noncomputable def psi (k : ℕ) (γ : ℂ) (x : ℂ) : ℂ := phi k (γ - x⁻¹)

/-
**H1.5** (scalar defining identity, Definition 2.4): at an eigenvalue `z` of
`A` the resolvent has eigenvalue `(γ − z)⁻¹`, and the transformed function
recovers `φ_k`: `ψ_{k,γ}((γ − z)⁻¹) = φ_k(z)`.  This is the spectral/
finite-rank-component identity that (via §0 S3, the holomorphic functional
calculus `f_γ((γI−A)⁻¹) = f(A)`) lifts to the operator equality `φ_k(A) =
ψ_{k,γ}(X)`.
-/


/-
**H1.5** (resolvent eigenvector, the spectral bridge): if `A v = z v` and
`γ − z` is invertible, then `v` is an eigenvector of the resolvent
`X = (γI − A)⁻¹` with eigenvalue `(γ − z)⁻¹`, i.e. `X v = (γ − z)⁻¹ • v`.
This is the per-component reduction underlying the CFC identity of H1.5.
-/


/-! ## H1.6 — the resolvent shift identity (the clean SIRK algebra core) -/

variable {A : Type*} [Ring A] [Algebra ℂ A]

/-
**H1.6** (resolvent identity): if `X_j` and `X_m` are two-sided inverses of
the shifted operators `γ_j·1 − a` and `γ_m·1 − a`, then
`X_j − X_m = (γ_m − γ_j)·(X_j · X_m)`.  Purely algebraic: insert the two
inverses and cancel `a`.
-/


/-
**H1.6** (SIRK shift form): with the SIRK shifts `γ_j = N − h·j` the resolvent
identity rearranges to `X_j · (1 + h·(m−j)·X_m) = X_m`.  This is the algebraic
core that turns the rational-Krylov recurrence into a shift-invert recurrence
(§4, between eqs. (10)–(11)); no analysis is needed.
-/


/-
**H1.7** (rational-Krylov representation, eq. 11 generating step): with the SIRK
shifts `γ_j = N − h·j` the resolvent `X_j` is the rational function
`X_j = (1 + h(m−j)·X_m)⁻¹ · X_m` of `X_m` (Hashimoto §4, "Since `X_j` is
represented as …").  This is the load-bearing algebraic identity from which the
rational-Krylov subspace equality `Q_m({X_j}, v) = {r(X_m) v | r ∈ R_SIRK}`
(eq. 11) follows by induction: each `X_j` raises the numerator degree by ≤ 1 and
multiplies the denominator by one more `(1 + h·i·z)` factor.  Purely algebraic,
from the H1.6 shift identity + commutativity of `X_m` with `1 + h(m−j)·X_m`.
-/


end

end BookProof.ChapterH1


