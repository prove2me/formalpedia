-- Prove2me | Definitions.Def_PorteusGenSS_IsPolyaDensity
-- name    : PorteusGenSS_IsPolyaDensity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:09:48.685222+00:00
-- url     : https://prove2.me/theorems/ce6aec97-ea8d-4a85-a095-09769950740c
-- title:
--   Pólya density
-- statement:
--   A **Pólya density** is a Pólya frequency function $\varphi$ with $\int_{-\infty}^{\infty}\varphi(x)\,dx=1$, i.e. a probability density that is $PF_n$ for every $n$.
-- source:
--   Porteus, On the Optimality of Generalized (s, S) Policies, Management Science 17(7):411–426 (1971), Definition 7, p. 421

import Mathlib
import Definitions.Def_PorteusGenSS_IsPFF

open MeasureTheory

namespace PorteusGenSS

/-- **Pólya density (Definition 7).**
Porteus, On the Optimality of Generalized (s, S) Policies, Management Science 17(7):411–426 (1971), Definition 7, p. 421: "If φ is PFₙ (PFF) and ∫_{−∞}^∞ φ(x) dx = 1, then φ is a PFₙ
(Pólya) density."

`IsPolyaDensity φ` says `φ` is a Pólya frequency function with `∫ φ = 1`. -/
def IsPolyaDensity (φ : ℝ → ℝ) : Prop :=
  IsPFF φ ∧ ∫ x, φ x = 1

end PorteusGenSS


