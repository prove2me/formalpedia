-- Prove2me | Definitions.Def_ConstrSOSP_Supplement_ValidGen
-- name    : ConstrSOSP_Supplement_ValidGen
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:23:37.106368+00:00
-- url     : https://prove2.me/theorems/19226d44-d2f6-47bf-8500-61d37974831a
-- title:
--   Valid general white-box instances (total version, dimension restriction $D$)
-- statement:
--   Fix a clock exponent $K$ and a predicate $D$ on dimensions. A string is a **valid instance** if it is the code of rational data $\epsilon_G,\epsilon_H,m,d,A,B,L,L_1,L_2$, a clock $T$ and machine codes $c_f,c_g,c_H$ such that
--
--   1. $\epsilon_G,\epsilon_H,L,L_1,L_2>0$;
--   2. $D(d)$ holds;
--   3. $\mathcal X=\{x\in\mathbb R^d: Ax\le B\}$ is non-empty and bounded;
--   4. at every rational point $x\in\mathcal X$ the three machines, run within the clock, return values $f(x)$, $\nabla f(x)$, $\nabla^2 f(x)$.
--
--   No regularity promise is required: in the paper's total version a regularity violation is itself an accepted answer.
--
--   **Formalization Note** Item 4 reads "Turing machine for $f:\mathbb R^d\to\mathbb R$, …" as machines that compute maps on the rational points of the domain within the problem's clock. For Sosp1 $D$ is always true; for Fixed-Dimensions-Sosp2 it is $d=d_0$.
-- source:
--   Kontogiannis, Panageas & Pollatos, The Computational Complexity of Avoiding Strict Saddle Points in Constrained Optimization, arXiv:2604.02285 (2 Nov 2026), Definition 4.6, p.19; Definition 4.8, p.20; §4.1, p.17

import Mathlib
import Definitions.Def_ConstrSOSP_Poly
import Definitions.Def_ConstrSOSP_Supplement_encInstGen
import Definitions.Def_ConstrSOSP_Supplement_EvalsD

namespace ConstrSOSP.Supplement

open ConstrSOSP

/-- **Valid general white-box instances** of Sosp1 and Fixed-Dimensions-Sosp2 (Kontogiannis,
Panageas & Pollatos, arXiv:2604.02285, 2 Nov 2026, Definition 4.6, p.19, and Definition 4.8,
p.20: "precision parameters ϵG, ϵH > 0, A ∈ R^{m×d}, B ∈ R^m defining a bounded non-empty domain
X = {x ∈ R^d : Ax ≤ B}, Turing machine for f : R^d → R, ∇f : R^d → R^d and ∇²f : R^d → R^{d×d},
Lipschitz constants L, L1, L2 > 0").

`ValidGen K D s` holds iff `s = encInstGen ϵG ϵH m d A B L L₁ L₂ T cf cg cH` for rational data
with
1. `ϵG > 0`, `ϵH > 0`, `L > 0`, `L₁ > 0`, `L₂ > 0`;
2. the dimension `d` satisfies `D d` (`D = fun _ => True` for Sosp1, `D = (· = d₀)` for
   Fixed-Dimensions-Sosp2);
3. `X = {x ∈ ℝᵈ : Ax ≤ B}` is non-empty and bounded;
4. at every rational `x ∈ X` the three machines, run with the clock `T · (|w| + 1)^K`, return
   values `f(x)`, `∇f(x)`, `∇²f(x)` (`EvalsD`).

**Formalization Note** No regularity promise is part of validity: this is the paper's *total*
version ("we will rely on the total version for our formal definitions", p.17), in which a
regularity violation is an answer. Item 4 is the reading of "Turing machine for f : R^d → R, …":
the machines compute maps on the rational points of the domain, within the problem's clock; nothing
is required outside `X`. Redundant rows and lower-dimensional polytopes are allowed (p.66). -/
def ValidGen (K : ℕ) (D : ℕ → Prop) (s : List Bool) : Prop :=
  ∃ (ϵG ϵH : ℚ) (m d : ℕ) (A : Fin m → Fin d → ℚ) (B : Fin m → ℚ) (L L1 L2 : ℚ) (T : ℕ)
    (cf cg cH : List Bool),
    s = encInstGen ϵG ϵH m d A B L L1 L2 T cf cg cH ∧
    0 < ϵG ∧ 0 < ϵH ∧ 0 < L ∧ 0 < L1 ∧ 0 < L2 ∧ D d ∧
    (Poly (fun j i => (A j i : ℝ)) (fun j => (B j : ℝ))).Nonempty ∧
    Bornology.IsBounded (Poly (fun j i => (A j i : ℝ)) (fun j => (B j : ℝ))) ∧
    ∀ x : Fin d → ℚ, (fun i => (x i : ℝ)) ∈ Poly (fun j i => (A j i : ℝ)) (fun j => (B j : ℝ)) →
      ∃ (v : ℚ) (g : Fin d → ℚ) (H : Fin d → Fin d → ℚ), EvalsD d K T cf cg cH x v g H

end ConstrSOSP.Supplement


