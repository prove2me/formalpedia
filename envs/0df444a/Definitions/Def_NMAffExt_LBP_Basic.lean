-- Prove2me | Definitions.Def_NMAffExt_LBP_Basic
-- name    : NMAffExt_LBP_Basic
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T04:28:25.342006+00:00
-- url     : https://prove2.me/theorems/90efbdef-acfc-4205-8e02-57cbe5085844
-- title:
--   Signs $(-1)^z$, uniform averages, output parities $f_u=\langle u,F\rangle$ and the correlation $\mathrm{Corr}(f,P)$ over $\mathbb F_2$
-- statement:
--   Bits are elements of $\mathbb F_2$, and an $n$-bit string is a vector $x\in\mathbb F_2^n$.
--
--   - For $z\in\mathbb F_2$ the **sign** $(-1)^z$ is $1$ if $z=0$ and $-1$ if $z=1$.
--   - For a real function $g$ on a finite set $\Omega$, $\mathbb E_{\omega\sim U_\Omega}\,g(\omega)=\frac1{|\Omega|}\sum_{\omega\in\Omega}g(\omega)$ is its average under the uniform distribution.
--   - For $u,y\in\mathbb F_2^m$, $\langle u,y\rangle=\sum_i u_iy_i\in\mathbb F_2$.
--   - For $F:\mathbb F_2^n\to\mathbb F_2^m$ and $u\in\mathbb F_2^m$, the **output parity** is $f_u(x)=\langle u,F(x)\rangle$.
--   - For Boolean functions $f,P:\mathbb F_2^n\to\mathbb F_2$, the **correlation** is
--   $$\mathrm{Corr}(f,P)=\Bigl|\mathbb E_{x\sim U_n}(-1)^{f(x)+P(x)}\Bigr|,$$
--   with the sum $f(x)+P(x)$ taken in $\mathbb F_2$ and the absolute value outside the expectation.
--
--   **Formalization Note.** `sgn z`, `avg g` (sum over a `Fintype` divided by its cardinality), `ip u y`, `parity F u` and `corr f P`. Bits are `ZMod 2`, strings `Fin n → ZMod 2`.
-- source:
--   Xin Li, Yan Zhong, Non-Malleable Affine Extractors with Small Error and Complexity Lower Bounds, arXiv:2610.02407 (version of 2026-11-02, sha256 e80dad4d…), p. 18 (PDF 20), §2 notation; p. 55 (PDF 57), §4.1 (Corr); p. 6 (PDF 8) and p. 56 (PDF 58) (f_u)

import Mathlib

/-!
# Signs, uniform averages and correlation over 𝔽₂

Xin Li, Yan Zhong, *Non-Malleable Affine Extractors with Small Error and Complexity Lower Bounds*,
arXiv:2610.02407 (version of 2026-11-02, sha256 e80dad4d…), p. 18 (PDF 20) §2 notation,
p. 55 (PDF 57) §4.1 (`Corr`), p. 6 (PDF 8) and p. 55 (PDF 57) (the output parity `f_u`).

Conventions.
* A bit is an element of `ZMod 2` (= 𝔽₂); an `n`-bit string is `Fin n → ZMod 2`.
* `sgn z = (-1)^z` for `z ∈ 𝔽₂`: `1` at `0` and `-1` at `1`.
* `avg g` is the expectation of `g` under the uniform distribution on a finite type: the sum of `g`
  over the type divided by its cardinality.
* `ip u y = ⟨u, y⟩ = ∑ᵢ uᵢ yᵢ` in 𝔽₂.
* `corr f P = |E_{x∼U_n} (-1)^{f(x)+P(x)}|` for two Boolean functions on `n` bits.
-/

namespace NMAffExt.LBP

/-- The sign `(-1)^z ∈ {1, -1}` of a bit `z ∈ 𝔽₂`. -/
def sgn (z : ZMod 2) : ℝ := if z = 0 then 1 else -1

/-- The expectation `E_{x∼U} g(x)` of a real function under the uniform distribution on a finite
type: `(∑ₓ g x) / |α|`. -/
noncomputable def avg {α : Type*} [Fintype α] (g : α → ℝ) : ℝ :=
  (∑ x, g x) / (Fintype.card α : ℝ)

/-- The inner product `⟨u, y⟩ = ∑ᵢ uᵢ yᵢ ∈ 𝔽₂` of two bit strings. -/
def ip {m : ℕ} (u y : Fin m → ZMod 2) : ZMod 2 := ∑ i, u i * y i

/-- The output parity `f_u(x) = ⟨u, F(x)⟩` of a map `F : 𝔽₂ⁿ → 𝔽₂ᵐ`. -/
def parity {n m : ℕ} (F : (Fin n → ZMod 2) → (Fin m → ZMod 2)) (u : Fin m → ZMod 2)
    (x : Fin n → ZMod 2) : ZMod 2 :=
  ip u (F x)

/-- The correlation `Corr(f, g) = |E_{x∼U_n} (-1)^{f(x)+g(x)}|` of two Boolean functions. -/
noncomputable def corr {n : ℕ} (f g : (Fin n → ZMod 2) → ZMod 2) : ℝ :=
  |avg (fun x => sgn (f x + g x))|

end NMAffExt.LBP


