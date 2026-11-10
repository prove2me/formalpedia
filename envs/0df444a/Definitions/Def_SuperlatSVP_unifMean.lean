-- Prove2me | Definitions.Def_SuperlatSVP_unifMean
-- name    : SuperlatSVP_unifMean
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:44:57.428206+00:00
-- url     : https://prove2.me/theorems/f96cec32-2ed8-43f4-9393-41170d71329d
-- title:
--   Expectation over a shift uniform modulo a lattice, and the shifted count $\#((\Lambda+u)\cap S)$
-- statement:
--   Let $\Lambda=B_\Lambda\mathbb Z^n$ be a full-rank lattice. A shift $u$ is **uniform modulo $\Lambda$** when its class in $\mathbb R^n/\Lambda$ follows the normalized Haar measure. Writing $u=B_\Lambda y$ with $y$ uniform on the unit cube $[0,1)^n$ realizes this, since the image of the cube is a fundamental domain of $\Lambda$:
--   $$\mathbb E_u\,g(u)=\int_{[0,1)^n}g(B_\Lambda y)\,dy .$$
--   For a $\Lambda$-periodic $g$ the value does not depend on the basis.
--
--   For a set $S\subseteq\mathbb R^n$ and a shift $u$, $\#((\Lambda+u)\cap S)$ is the number of points of the translate $\Lambda+u$ that lie in $S$. With $S$ the midpoint shell $A$ this is the paper's $K_\Lambda(u)$ (4.8), and with $S=E_z$ it is $K_{\Lambda,z}(u)$ (4.17).
--
--   **Formalization Note** Both the mean and the count take values in $[0,\infty]$. A variance bound $\operatorname{Var}X\le c$ is written $\mathbb E X^2\le(\mathbb E X)^2+c$. This is the same statement whenever $\mathbb E X<\infty$, which holds for every shell count in the mission, and it avoids truncated subtraction.
-- source:
--   Hhan, Kim, Kim, Laarhoven, Superlattice methods for the shortest vector problem and discrete Gaussian sampling, STOC 2027 submission (manuscript sha256 fcf5b14f…ba), §2.2, p.17 (PDF p.17); §4.1.1, (4.8), p.32; (4.17), p.37

import Mathlib
import Definitions.Def_SuperlatSVP_lat

open MeasureTheory
open scoped ENNReal

namespace SuperlatSVP

/-- The expectation `E_u g(u)` over a shift `u` uniform modulo the lattice `Λ = B_Λ ℤⁿ` for the
normalized Haar measure of `ℝⁿ/Λ` (§2.2, p.17: "c is uniform on ℝⁿ/L with respect to normalized
Haar measure"; §4.1, p.32: "Expectations and variances of K_Λ are taken over u uniform modulo Λ").

**Formalization Note.** The uniform class modulo `Λ` is represented by `u = B_Λ y` with `y`
uniform on the unit cube `[0,1)ⁿ`, whose image is a fundamental domain of `Λ`. For an
`Λ`-periodic integrand (every integrand in the mission) the value does not depend on the basis. A
variance bound `Var X ≤ c` is written `E X² ≤ (E X)² + c`, in `ℝ≥0∞`, which is the same statement
whenever `E X < ∞` and avoids truncated subtraction. -/
noncomputable def unifMean {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (g : E n → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ y in Set.univ.pi (fun _ : Fin n => Set.Ico (0 : ℝ) 1), g (vecE (B.mulVec y))

/-- The number of points of the translate `Λ + u` in a set `S`, `#((Λ + u) ∩ S)` ((4.8), p.32;
(4.17), p.37), as an element of `ℝ≥0∞`. -/
noncomputable def shiftCount {n : ℕ} (Λ : Submodule ℤ (E n)) (S : Set (E n)) (u : E n) : ℝ≥0∞ :=
  (({x : E n | x ∈ S ∧ x - u ∈ Λ}.encard : ℕ∞) : ℝ≥0∞)

end SuperlatSVP


