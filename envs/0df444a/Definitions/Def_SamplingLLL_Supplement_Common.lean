-- Prove2me | Definitions.Def_SamplingLLL_Supplement_Common
-- name    : SamplingLLL_Supplement_Common
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:46:32.153873+00:00
-- url     : https://prove2.me/theorems/e78daedf-3196-4afe-869a-be2d0c8f603e
-- title:
--   Charged rationals, total variation distance and support of a procedure
-- statement:
--   Shared conventions of the supplement, on top of the base mission's procedures (`Proc`: a subdistribution on outputs with a tick counter and a call counter) and charged rational arithmetic.
--
--   1. **Charged rationals.** A rational computed outside a procedure is carried with the accumulated bit charge of computing it: each addition, subtraction, multiplication and division of $a$ and $b$ adds $(\ell(a)+\ell(b)+1)^2$, where $\ell$ is the bit length. Paying the charge inside a procedure returns the value.
--   2. **Total variation.** For a procedure $p$ with outputs in a finite set and a target law $\nu$,
--   $$
--   d_{\mathrm{TV}}(p,\nu)=\tfrac12\sum_y\bigl|\mathrm{law}_p(y)-\nu(y)\bigr| .
--   $$
--   It is used only together with the statement that $p$ terminates with probability one.
--   3. **Support.** The output of $p$ is supported on a property $E$ when every outcome of positive mass satisfies $E$.
--   4. **Uniform draw.** An exact uniform draw from $\{0,\dots,k\}$, by sequential exact coins.
--
--   These are used by every theorem of the supplement: the charged rationals in the budgets and proposals of Appendices B, C, D and H, the total variation distance and the support in Theorems 5.4, 2.18, 2.19 and F.6.
--
--   **Formalization Note** The module has no declaration named `Common`; it groups `CQ`, `cq`, `cadd`, `csub`, `cmul`, `cdiv`, `cprod`, `csum`, `cpow`, `charge`, `tvDist`, `SupportedOn` and `uniformFin`.
-- source:
--   Achlioptas, Counting and Sampling by Local Repair: From the Lovász Local Lemma to Random k-SAT, STOC 2027 submission (manuscript sha256 7a943167…), p.10 (bit operations); Theorem 5.4, pp.16–17 (total variation); Theorem F.6, p.55 (support)

import Mathlib
import Definitions.Def_SamplingLLL_sllData

set_option autoImplicit false

open scoped ENNReal

namespace SamplingLLL.Supplement

open Proc

/-- A rational together with the accumulated bit charge of computing it. Every rational a supplement
procedure computes outside a `Proc` is built from input rationals by `cadd`, `csub`, `cmul`, `cdiv`,
each charging `qcost` of its actual operands, exactly as the base primitives `qadd`, … do inside a `Proc`.

Source: Achlioptas, *Counting and Sampling by Local Repair*, STOC 2027 submission (manuscript sha256
7a943167…), the charge table of the base mission (`Primitives`), p.10 ("bit operations"). -/
abbrev CQ : Type := ℚ × ℕ

/-- An input rational, charged nothing. -/
def cq (a : ℚ) : CQ := (a, 0)

/-- Charged addition. -/
def cadd (x y : CQ) : CQ := (x.1 + y.1, x.2 + y.2 + qcost x.1 y.1)
/-- Charged subtraction. -/
def csub (x y : CQ) : CQ := (x.1 - y.1, x.2 + y.2 + qcost x.1 y.1)
/-- Charged multiplication. -/
def cmul (x y : CQ) : CQ := (x.1 * y.1, x.2 + y.2 + qcost x.1 y.1)
/-- Charged division. -/
def cdiv (x y : CQ) : CQ := (x.1 / y.1, x.2 + y.2 + qcost x.1 y.1)

/-- Charged product of a list, from the left. -/
def cprod (l : List CQ) : CQ := l.foldl cmul (cq 1)
/-- Charged sum of a list, from the left. -/
def csum (l : List CQ) : CQ := l.foldl cadd (cq 0)
/-- Charged power by repeated multiplication. -/
def cpow (x : CQ) : ℕ → CQ
  | 0 => cq 1
  | k + 1 => cmul (cpow x k) x

/-- Pay the charge of a precomputed rational and return its value. -/
noncomputable def charge (x : CQ) : Proc ℚ := do
  tick x.2
  pure x.1

/-- Total variation distance `½ Σ_y |law(y) − ν(y)|` between the output law of a procedure on a finite
type and a target law `ν`. Used only together with `mass p = 1`. -/
noncomputable def tvDist {α : Type} [Fintype α] (p : Proc α) (ν : α → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ y, |(law p y).toReal - ν y|

/-- The output is supported on `E`: every outcome of positive mass satisfies `E`. -/
def SupportedOn {α : Type} (p : Proc α) (E : α → Prop) : Prop := ∀ r, p r ≠ 0 → E r.1

/-- The uniform draw from `Fin k` (`k ≥ 1`), by `drawList` with weights `1/k`; charged as `drawList`. -/
noncomputable def uniformFin (k : ℕ) : Proc (Fin (k + 1)) :=
  drawList ((List.finRange k).map fun j => (j.castSucc, (1 / (k + 1 : ℚ)))) (Fin.last k) 1

end SamplingLLL.Supplement


