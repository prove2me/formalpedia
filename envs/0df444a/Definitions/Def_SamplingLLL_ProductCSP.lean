-- Prove2me | Definitions.Def_SamplingLLL_ProductCSP
-- name    : SamplingLLL_ProductCSP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:52:32.903133+00:00
-- url     : https://prove2.me/theorems/8d4d3e8a-510a-4210-9e28-7d4b4c9ab4fe
-- title:
--   Product-space CSP: $\lambda$, $Z(S)$, $\mu_S$, $r_{S,c}$
-- statement:
--   A product-space constraint satisfaction problem has variables $X=(X_v)_{v\in V}$ with a product law $\lambda$ on finite sets $\Omega_v$ and a finite family of constraints, each with a scope $\mathrm{vbl}(a)$ and a bad event $\mathrm{Bad}_a$ determined by the variables in the scope. For a subfamily $S$,
--   $$
--   Z(S)=\lambda\Big(\bigcap_{a\in S}\overline{\mathrm{Bad}_a}\Big),\qquad \mu_S=\lambda(\,\cdot\mid\text{every constraint of }S\text{ is satisfied}),\qquad r_{S,c}=\mu_S(c\text{ is violated}).
--   $$
--   These are the objects counted and sampled throughout the mission.
--
--   **Formalization Note** The law has rational entries, and $\Omega_v=\{0,\dots,\mathrm{dom}_v\}$, since a law on a finite set forces the set to be nonempty. Zero entries are allowed. The function $\mu_S$ is $0$ when $Z(S)=0$; every statement that uses it has or proves $Z(S)>0$.
-- source:
--   Achlioptas, Counting and Sampling by Local Repair: From the Lovász Local Lemma to Random k-SAT, STOC 2027 submission (manuscript sha256 7a943167…), §1, p.2; §5.1, p.14; Appendix A.3, p.20

import Mathlib

set_option autoImplicit false

namespace SamplingLLL

/-- A product-space constraint satisfaction problem with `n` variables and `m` constraints:
finite variable domains `Ω_v = Fin (dom v + 1)`, an explicit rational product law `λ`, and
for each constraint `a` a scope `vbl a` and a bad event determined by the variables in the scope.

Source: D. Achlioptas, *Counting and Sampling by Local Repair: From the Lovász Local Lemma to
Random k-SAT*, STOC 2027 submission (manuscript sha256 7a943167…), §1, p.2; §5.1, p.14.

**Formalization Note.** A law on a finite set forces the set to be nonempty, so domains are
written `Fin (dom v + 1)`; zero entries of `λ_v` are allowed. -/
structure ProductCSP (n m : ℕ) where
  /-- `Ω_v = Fin (dom v + 1)`. -/
  dom : Fin n → ℕ
  /-- The coordinate law `λ_v`. -/
  lam : (v : Fin n) → Fin (dom v + 1) → ℚ
  lam_nonneg : ∀ v w, 0 ≤ lam v w
  lam_sum : ∀ v, ∑ w, lam v w = 1
  /-- The scope `vbl(a)`. -/
  vbl : Fin m → Finset (Fin n)
  /-- The bad event `Bad_a`, as a test on configurations. -/
  bad : Fin m → ((v : Fin n) → Fin (dom v + 1)) → Bool
  /-- `Bad_a` is determined by the variables in its scope. -/
  bad_dep : ∀ a x y, (∀ v ∈ vbl a, x v = y v) → bad a x = bad a y

namespace ProductCSP

variable {n m : ℕ} (P : ProductCSP n m)

/-- A configuration `X = (X_v)_v`. -/
abbrev Config : Type := (v : Fin n) → Fin (P.dom v + 1)

/-- The product mass `λ(x) = ∏_v λ_v(x_v)` of a configuration. -/
def mass (x : P.Config) : ℚ := ∏ v, P.lam v (x v)

/-- `λ(E)` for an event `E`, by the finite sum over configurations. -/
def prob (E : P.Config → Bool) : ℚ := ∑ x : P.Config, if E x then P.mass x else 0

/-- The configuration `x` satisfies every constraint of `S`. -/
def sat (S : Finset (Fin m)) (x : P.Config) : Bool := decide (∀ a ∈ S, P.bad a x = false)

/-- The set of constraints of `C` violated by `x`. -/
def badSet (C : Finset (Fin m)) (x : P.Config) : Finset (Fin m) := C.filter fun a => P.bad a x

/-- `Z(S) = λ(⋂_{a∈S} ¬Bad_a)`, p.2 and p.5. -/
def Z (S : Finset (Fin m)) : ℚ := P.prob (P.sat S)

/-- `μ_S = λ(· | every constraint of S is satisfied)`, as a function on configurations (p.2, p.5).
It is `0` everywhere when `Z(S) = 0`; every statement using it has or proves `0 < Z(S)`. -/
def mu (S : Finset (Fin m)) (x : P.Config) : ℚ := if P.sat S x then P.mass x / P.Z S else 0

/-- `r_{S,c} = μ_S(c is violated)`, p.20. -/
def viol (S : Finset (Fin m)) (c : Fin m) : ℚ :=
  ∑ x : P.Config, if P.bad c x then P.mu S x else 0

end ProductCSP

end SamplingLLL


