-- Prove2me | Definitions.Def_PelagicFF_PFF
-- name    : PelagicFF_PFF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:54:43.486269+00:00
-- url     : https://prove2.me/theorems/e821fc7d-585f-4441-aa1d-c758a86967de
-- title:
--   Pelagic Fourier Fishing $\mathrm{PFF}_n$ and the Pelagic condition (9)
-- statement:
--   Let $N=2^n$. A **Boolean function** $f:\{0,1\}^n\to\{-1,1\}$ is given by its truth table of length $N$. For a real function $H$ on $\{0,1\}^n$ write
--   $$\widehat H(y)=\frac1{2^n}\sum_{x\in\{0,1\}^n}H(x)\chi_y(x),\qquad \chi_y(x)=(-1)^{y\cdot x},$$
--   for its Fourier coefficient at $y\in\{0,1\}^n$.
--
--   $H$ satisfies the **Pelagic condition** at $y$ if
--   $$\sum_{z:\,|\widehat H(z)|\le|\widehat H(y)|}|\widehat H(z)|^2\ \ge\ \frac18\qquad\text{and}\qquad\sum_{z:\,|\widehat H(z)|\ge|\widehat H(y)|}|\widehat H(z)|^2\ \ge\ \frac18 .$$
--
--   In **Pelagic Fourier Fishing** $\mathrm{PFF}_n$, Alice receives $f$, Bob receives $g$ (both $\{0,1\}^n\to\{-1,1\}$), $h=fg$ pointwise, and Bob must output some $y\in\{0,1\}^n$ at which $h$ satisfies the Pelagic condition. As a two-party search problem in the sense of §2.1, $\mathrm{PFF}_n(f,g)$ is the set of such $y$.
--
--   The condition asks for an approximate median of the Fourier spectrum weighted by squared Fourier mass; it is the problem behind the paper's optimal $n$ versus $\Theta(2^n)$ quantum–classical separation.
--
--   **Formalization Note** Boolean functions are `Bool`-valued on `Fin n → Bool`, with $\{-1,1\}$ value `sign b` (`false ↦ 1`, `true ↦ −1`); $\widehat H$ is the published `OAI.Cotype.fourier`, whose character is $\prod_{i:\,y_i=1}\mathrm{sign}(x_i)=(-1)^{y\cdot x}$. Both inner comparisons are non-strict, as printed.
-- source:
--   Anselm, Ding, Gilboa, Grewal, Optimal and Verifiable Quantum Advantages in Communication Complexity, arXiv:2610.05585 (held version, sha256 4564aef3…), Problem 4.1, eq. (9), p.27; Fourier conventions §2.2, p.14

import Mathlib
import Definitions.Def_OAI_Analysis_Cotype_Cube

open OAI.Cotype

namespace PelagicFF

/-- A Boolean function `{0,1}ⁿ → {−1,1}`, encoded as a `Bool`-valued function on `Fin n → Bool`
whose `{−1,1}` value is `OAI.Cotype.sign` of the bit (`false ↦ 1`, `true ↦ −1`).

Anselm, Ding, Gilboa, Grewal, *Optimal and Verifiable Quantum Advantages in Communication
Complexity*, arXiv:2610.05585 (held version, sha256 4564aef3…), Problem 4.1, p.27. -/
abbrev BoolFn (n : ℕ) : Type := (Fin n → Bool) → Bool

/-- **The Pelagic condition (9)** for a real function `H` on `{0,1}ⁿ` at the frequency `y`:
both the squared Fourier mass at or below `|Ĥ(y)|` and the squared Fourier mass at or above
`|Ĥ(y)|` are at least `1/8`,
`∑_{z : |Ĥ(z)| ≤ |Ĥ(y)|} |Ĥ(z)|² ≥ 1/8` and `∑_{z : |Ĥ(z)| ≥ |Ĥ(y)|} |Ĥ(z)|² ≥ 1/8`.

arXiv:2610.05585 (held version, sha256 4564aef3…), Problem 4.1, eq. (9), p.27; restated in §4.1,
p.27 and as the Pelagic condition of Lemma 3.7, p.24.

**Formalization Note.** `Ĥ` is the published `OAI.Cotype.fourier`, i.e.
`Ĥ(y) = 2⁻ⁿ ∑ₓ H(x) χ_y(x)` with `χ_y(x) = ∏_{i : yᵢ} sign(xᵢ) = (−1)^{y·x}` (§2.2, p.14). Both
inner comparisons are non-strict and both thresholds are `≥ 1/8`, as printed. -/
noncomputable def IsPelagic {n : ℕ} (H : (Fin n → Bool) → ℝ) (y : Fin n → Bool) : Prop :=
  (1 : ℝ) / 8 ≤ ∑ z ∈ Finset.univ.filter (fun z => |OAI.Cotype.fourier H z| ≤ |OAI.Cotype.fourier H y|), OAI.Cotype.fourier H z ^ 2 ∧
  (1 : ℝ) / 8 ≤ ∑ z ∈ Finset.univ.filter (fun z => |OAI.Cotype.fourier H y| ≤ |OAI.Cotype.fourier H z|), OAI.Cotype.fourier H z ^ 2

/-- **Pelagic Fourier Fishing `PFFₙ`** as a two-party search relation: Alice holds `f`, Bob holds
`g`, both `{0,1}ⁿ → {−1,1}`, and `y ∈ {0,1}ⁿ` is a correct output exactly when `h = f·g` satisfies
the Pelagic condition (9) at `y`.

arXiv:2610.05585 (held version, sha256 4564aef3…), Problem 4.1, p.27: "Let N = 2ⁿ. Alice receives a
function f : {0,1}ⁿ → {−1,1} and Bob receives a function g : {0,1}ⁿ → {−1,1}, each given as a truth
table of length N. Let h(x) = f(x)g(x) for x ∈ {0,1}ⁿ. Bob must output a y ∈ {0,1}ⁿ satisfying (9)."

**Formalization Note.** The `{−1,1}` values are `sign (f x)` and `sign (g x)` with
`sign false = 1`, `sign true = −1`; the relation is `R(f, g) = {y | PFF n f g y}` in the sense of
§2.1, p.14 (`X = Y = BoolFn n`, `Z = Fin n → Bool`). -/
noncomputable def PFF (n : ℕ) (f g : BoolFn n) (y : Fin n → Bool) : Prop :=
  IsPelagic (fun x => sign (f x) * sign (g x)) y

end PelagicFF


