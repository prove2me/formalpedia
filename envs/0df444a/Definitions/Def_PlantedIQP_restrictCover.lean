-- Prove2me | Definitions.Def_PlantedIQP_restrictCover
-- name    : PlantedIQP_restrictCover
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:19:29.789291+00:00
-- url     : https://prove2.me/theorems/2fe8ce70-838b-4755-9bd1-e59a603e506e
-- title:
--   The restricted polynomials $f^C_z$ of the vertex-cover decomposition
-- statement:
--   For $C\subseteq[n]$, write $x_C$ and $x_{C^c}$ for the substrings of $x\in\mathbb F_2^n$ on $C$ and on its complement. For $z\in\mathbb F_2^{C}$ the **restricted polynomial** is the function of the uncovered variables
--
--   $$
--   f^C_z(y)=f(x)\quad\text{where }x_C=z,\ x_{C^c}=y .
--   $$
--
--   When $C$ is a vertex cover of $H(f)$, $f^C_z$ has degree at most $2$ (Lemma 40), so its gap is computable in polynomial time.
--
--   **Formalization Note** Substrings are functions on the subtypes $\{i\in C\}$ and $\{i\notin C\}$; $f^C_z$ may have a constant term.
-- source:
--   Bläser, Gullans, Hangleiter, Liu, Qiao, Verifiable quantum advantage based on polynomials with planted structures, arXiv:2609.39918 (sha256 6e261694…), p.24 and proof of Lemma 40, Eq. (50), p.25

import Mathlib
import Definitions.Def_PlantedIQP_CubicPoly

set_option autoImplicit false

namespace PlantedIQP

/-!
# The restricted polynomials `f^C_z` of the vertex-cover decomposition

Bläser et al., arXiv:2609.39918 (sha256 6e261694…), p.24: "given a set S ⊂ [n] and a bit string
x ∈ 𝔽₂ⁿ write x_S = (x_i)_{i∈S} ∈ 𝔽₂^{|S|} for the substring corresponding to the indices in S, and let
S^c = [n] \ S"; proof of Lemma 40, p.25, Eq. (50): `f^C_{x_C}(x_{C^c})` is `f` with the cover
variables `x_i`, `i ∈ C`, fixed.

**Formalization Note.**
* Substrings are functions on the subtypes `{i // i ∈ C}` and `{i // i ∉ C}`; `merge C z y` is the
  vector of 𝔽₂ⁿ with `x_C = z` and `x_{C^c} = y`.
* `restrictCover f C z = f^C_z`, the function `y ↦ f(merge C z y)` of the uncovered variables. The
  source writes it as a polynomial in `|C^c|` variables; here it is a function on `{i // i ∉ C} → 𝔽₂`,
  whose degree is measured by `DegLE` (its multilinear representative may have a constant term).
-/

/-- The vector `x ∈ 𝔽₂ⁿ` with `x_C = z` and `x_{C^c} = y`. -/
def merge {n : ℕ} (C : Finset (Fin n)) (z : {i // i ∈ C} → ZMod 2) (y : {i // i ∉ C} → ZMod 2) :
    Vec n :=
  fun i => if h : i ∈ C then z ⟨i, h⟩ else y ⟨i, h⟩

/-- `f^C_z(y) = f(merge C z y)`: `f` with the variables in `C` set to `z` (Eq. (50)). -/
def restrictCover {n : ℕ} (f : CubicPoly n) (C : Finset (Fin n)) (z : {i // i ∈ C} → ZMod 2) :
    ({i // i ∉ C} → ZMod 2) → ZMod 2 :=
  fun y => f.eval (merge C z y)

end PlantedIQP


