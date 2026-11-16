-- Prove2me | Definitions.Def_AbelianPromises_Dichotomy_Supplement_CurrentCSP
-- name    : AbelianPromises_Dichotomy_Supplement_CurrentCSP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:53:04.326175+00:00
-- url     : https://prove2.me/theorems/ce39cd6e-0ada-4800-8c5d-52ebb97d4b9c
-- title:
--   Finite current-domain CSP and pinned affine integer programming
-- statement:
--   A finite constraint instance has a finite current domain $D_x$ at each variable and a finite current relation $R_C$ at each constraint. Each constraint has its own arity and ordered scope; variables may repeat within a scope. Current tuples respect every positional domain. Constraint pinning replaces only $R_C$ by the specified singleton; variable pinning restricts $D_x$ and deletes incompatible incident tuples.
--
--   The affine integer programming relaxation asks for signed integer weights $\lambda_x(a)$ and $\lambda_C(t)$ satisfying
--
--   $$
--   \sum_{a\in D_x}\lambda_x(a)=1,\qquad
--   \sum_{t\in R_C}\lambda_C(t)=1,\qquad
--   \lambda_{x_i}(a)=\sum_{t\in R_C:t_i=a}\lambda_C(t).
--   $$
--
--   There is no nonnegativity requirement. Empty domains or relations make the corresponding normalization impossible. This general CSP interface is independent of a fixed paper-specific template and supports binary Label Cover as well as ternary inputs.
-- source:
--   Tamio-Vesa Nakajima, Zephyr Verwimp, Stanislav Živný, STOC 2027 submission #967 (October 2026). Canonical submission artifact; no arXiv pin or acceptance claim. printed p. 16 (PDF p. 17), Section C.2 preamble and Definition C.5.

import Mathlib

set_option autoImplicit false

namespace AbelianPromises.Dichotomy.Supplement

/-- General finite CSP with a current domain at each variable and its own current relation
at each constraint. Labels are natural numbers, not an imposed common template domain. -/
structure CurrentCSP where
  n : ℕ
  m : ℕ
  arity : Fin m → ℕ
  scope : (c : Fin m) → Fin (arity c) → Fin n
  domain : Fin n → Finset ℕ
  tuples : (c : Fin m) → Finset (Fin (arity c) → ℕ)

/-- Current tuples always respect all current positional domains. -/
def CurrentCSP.rel (I : CurrentCSP) (c : Fin I.m) : Finset (Fin (I.arity c) → ℕ) :=
  (I.tuples c).filter fun t => ∀ i, t i ∈ I.domain (I.scope c i)

/-- Pin an entire constraint tuple, replacing only that constraint's relation. -/
def pinConstraint (I : CurrentCSP) (c : Fin I.m) (t : Fin (I.arity c) → ℕ) :
    CurrentCSP :=
  { I with tuples := fun d => if h : d = c then
      {fun i => t (Fin.cast (congrArg I.arity h) i)} else I.tuples d }

/-- Variable pinning also removes incompatible incident tuples through rel. -/
def pinVariable (I : CurrentCSP) (x : Fin I.n) (a : ℕ) : CurrentCSP :=
  { I with domain := fun y => if y = x then (I.domain y).filter (fun b => b = a) else I.domain y }

/-- Definition C.5: integer weights, sum one at every variable and constraint, and all
positional marginal equations. No nonnegativity requirement. -/
def AIPFeasible (I : CurrentCSP) : Prop :=
  ∃ (lv : Fin I.n → ℕ → ℤ) (lc : (c : Fin I.m) → (Fin (I.arity c) → ℕ) → ℤ),
    (∀ x, ∑ a ∈ I.domain x, lv x a = 1) ∧
    (∀ c, ∑ t ∈ I.rel c, lc c t = 1) ∧
    ∀ (c : Fin I.m) (i : Fin (I.arity c)) (a : ℕ), a ∈ I.domain (I.scope c i) →
      lv (I.scope c i) a = ∑ t ∈ (I.rel c).filter (fun t => t i = a), lc c t

end AbelianPromises.Dichotomy.Supplement


