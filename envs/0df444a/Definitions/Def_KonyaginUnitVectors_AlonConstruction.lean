-- Prove2me | Definitions.Def_KonyaginUnitVectors_AlonConstruction
-- name    : KonyaginUnitVectors_AlonConstruction
-- status  : Definition
-- author  : @moona3k
-- created : 2026-10-06T14:10:14.340841+00:00
-- url     : https://prove2.me/theorems/07123b47-f44b-4a7e-940a-27f834d460be
-- title:
--   Alon's construction over GF(2^k): character, BCH columns and the connection set
-- statement:
--   Throughout, $F$ is a finite field of characteristic $2$ with $q$ elements, regarded as an algebra over $\mathbb F_2$ (for example $\mathrm{GF}(2^k)$), $\mathrm{Tr}:F\to\mathbb F_2$ is the absolute trace, and $\psi(y)=(-1)^{\mathrm{Tr}(y)}\in\{1,-1\}$ is the associated additive character of $F$.
--
--   The module defines the ingredients of Alon's construction of an orthonormal labeling:
--
--   * `psi y`$=\psi(y)=(-1)^{\mathrm{Tr}(y)}$;
--   * `chi w g`$=\psi(w_1g_1+w_2g_2+w_3g_3)$, the character of the additive group $F^3$ indexed by $w\in F^3$;
--   * `gamma x`$=(x,x^3,x^5)\in F^3$, the columns of the parity-check matrix of the binary BCH code of designed distance $7$;
--   * `W0`$=\{x\ne0:\mathrm{Tr}(x^9)=0\}$ and `W1`$=\{x\neq0:\mathrm{Tr}(x^9)=1\}$, a partition of $F\setminus\{0\}$;
--   * `Sset`$=\{\gamma(x)+\gamma(y):x\in W0,\ y\in W1\}\subseteq F^3$, the connection set of a Cayley graph on $F^3$.
--
--   **Formalization Note.** All definitions are for a finite field `F` with `[Algebra (ZMod 2) F]`; the trace is `Algebra.trace (ZMod 2) F`.
-- source:
--   N. Alon, Explicit Ramsey graphs and orthonormal labelings, Electron. J. Combin. 1 (1994), R12, doi:10.37236/1192 (Sections 3 and 4; the construction here partitions by Tr(x^9) instead of the leading bit of x^7)

import Mathlib

/-!
# Alon-type construction over `GF(2^k)` (definitions)

Everything is stated for an arbitrary finite field `F` of characteristic 2 that is an algebra over
`ZMod 2` (e.g. `GaloisField 2 k`). 
-/

set_option autoImplicit false

namespace KonyaginUnitVectors.Alon

variable (F : Type*) [Field F] [Algebra (ZMod 2) F]

/-- The `±1`-valued additive character `ψ y = (-1)^{Tr y}` of `F`, `Tr : F → ZMod 2` the absolute trace. -/
noncomputable def psi (y : F) : ℝ := if Algebra.trace (ZMod 2) F y = 0 then 1 else -1

/-- The character `ψ_w(g) = ψ (w₁ g₁ + w₂ g₂ + w₃ g₃)` of the additive group `F × F × F`. -/
noncomputable def chi (w g : F × F × F) : ℝ := psi F (w.1 * g.1 + w.2.1 * g.2.1 + w.2.2 * g.2.2)

/-- `γ x = (x, x³, x⁵)`: the columns of the parity check matrix of the binary BCH code of designed distance 7. -/
def gamma (x : F) : F × F × F := (x, x ^ 3, x ^ 5)

variable [Fintype F]

open Classical in
/-- Nonzero `x` with `Tr (x⁹) = 0`. -/
noncomputable def W0 : Finset F :=
  Finset.univ.filter fun x => x ≠ 0 ∧ Algebra.trace (ZMod 2) F (x ^ 9) = 0

open Classical in
/-- Nonzero `x` with `Tr (x⁹) = 1`. -/
noncomputable def W1 : Finset F :=
  Finset.univ.filter fun x => x ≠ 0 ∧ Algebra.trace (ZMod 2) F (x ^ 9) ≠ 0

open Classical in
/-- The connection set `S = {γ x + γ y : x ∈ W0, y ∈ W1}` of the Cayley graph on `F × F × F`. -/
noncomputable def Sset : Finset (F × F × F) :=
  (W0 F ×ˢ W1 F).image fun p => gamma F p.1 + gamma F p.2

end KonyaginUnitVectors.Alon


