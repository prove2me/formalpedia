-- Prove2me | Definitions.Def_SamplingLLL_Supplement_RCSP
-- name    : SamplingLLL_Supplement_RCSP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:47:04.479068+00:00
-- url     : https://prove2.me/theorems/de435e03-be64-4454-9669-b3286873e0e8
-- title:
--   Product-space CSP with real coordinate laws, radius-two volume $Q$, exact one-event access
-- statement:
--   A **product-space CSP** has variables $X=(X_v)_{v\in V}$ with a product law $\lambda$ on finite sets $\Omega_v$ and a finite family $A$ of constraints, each with a scope $\mathrm{vbl}(a)$ and a bad event $\mathrm{Bad}_a$ determined by the variables of its scope. Here the coordinate laws $\lambda_v$ are real valued. As in the base mission, $Z=\lambda(\bigcap_a\overline{\mathrm{Bad}_a})$ and $\mu=\lambda(\,\cdot\mid\text{all constraints satisfied})$.
--
--   The **dependency graph** $H$ joins $a\ne b$ when $\mathrm{vbl}(a)\cap\mathrm{vbl}(b)\ne\emptyset$, and the **radius-two volume** is
--   $$
--   Q=\max_{a\in A}\bigl|\{b:\operatorname{dist}_H(a,b)\le 2\}\bigr| ,\qquad Q=0\text{ if }A=\emptyset .
--   $$
--
--   **Exact one-event access** (Definition 2.3) is given by oracles: an exact draw from each coordinate law $\lambda_v$; the exact rational numbers $\lambda(\mathrm{Bad}_a)$, supplied as input; and, whenever $\lambda(\mathrm{Bad}_a)>0$, an exact draw from $\lambda(\,\cdot\mid\mathrm{Bad}_a)$. Constraint evaluation is the test $\mathrm{Bad}_a(x)$. The oracles are *exact* when each draw terminates with exactly the stated law and the supplied rationals equal $\lambda(\mathrm{Bad}_a)$. The input length counts the variables with their domain sizes, the scopes, and the encodings of the rationals $\lambda(\mathrm{Bad}_a)$.
--
--   This is the instance class of Theorem 2.4, which is not restricted to atomic events or to rational coordinate laws.
--
--   **Formalization Note** $\Omega_v=\{0,\dots,\mathrm{dom}(v)\}$, so every domain is nonempty. An oracle's own running time is not part of the counters: its outcomes carry zero ticks and zero calls, and the procedures of Theorem 2.4 count each oracle call separately. $\mu$ is $0$ everywhere when $Z=0$; Theorem 2.4 proves $Z>0$.
-- source:
--   Achlioptas, Counting and Sampling by Local Repair: From the Lovász Local Lemma to Random k-SAT, STOC 2027 submission (manuscript sha256 7a943167…), §1, p.2; Definition 2.2, p.7; Definition 2.3, p.8

import Mathlib
import Definitions.Def_SamplingLLL_Supplement_Common

set_option autoImplicit false

open scoped ENNReal

namespace SamplingLLL.Supplement

open Proc

/-- A product-space CSP with a real product law (§1, p.2; §2.2, p.8): finite variable domains
`Ω_v = Fin (dom v + 1)`, a product law `λ` with real coordinate laws `λ_v`, and for each constraint `a` a scope
`vbl(a)` and a bad event determined by the variables of the scope. Definition 2.3 does not require the
coordinate laws to be rational, so this is the real analogue of the base `ProductCSP`.

Source: Achlioptas, *Counting and Sampling by Local Repair*, STOC 2027 submission (manuscript sha256
7a943167…), p.2 ("a product law λ on finite sets Ω_v") and Definition 2.3, p.8. -/
structure RCSP (n m : ℕ) where
  /-- `Ω_v = Fin (dom v + 1)`. -/
  dom : Fin n → ℕ
  /-- The coordinate law `λ_v`. -/
  lam : (v : Fin n) → Fin (dom v + 1) → ℝ
  lam_nonneg : ∀ v w, 0 ≤ lam v w
  lam_sum : ∀ v, ∑ w, lam v w = 1
  /-- The scope `vbl(a)`. -/
  vbl : Fin m → Finset (Fin n)
  /-- The bad event `Bad_a`, as a test on configurations. -/
  bad : Fin m → ((v : Fin n) → Fin (dom v + 1)) → Bool
  /-- `Bad_a` is determined by the variables of its scope. -/
  bad_dep : ∀ a x y, (∀ v ∈ vbl a, x v = y v) → bad a x = bad a y

namespace RCSP

variable {n m : ℕ} (P : RCSP n m)

/-- A configuration. -/
abbrev Config : Type := (v : Fin n) → Fin (P.dom v + 1)

/-- `λ(x) = ∏_v λ_v(x_v)`. -/
def mass (x : P.Config) : ℝ := ∏ v, P.lam v (x v)

/-- `λ(E)`. -/
noncomputable def prob (E : P.Config → Bool) : ℝ := ∑ x : P.Config, if E x then P.mass x else 0

/-- `x` satisfies every constraint of `S`. -/
def sat (S : Finset (Fin m)) (x : P.Config) : Bool := decide (∀ a ∈ S, P.bad a x = false)

/-- The constraints of `C` violated by `x`. -/
def badSet (C : Finset (Fin m)) (x : P.Config) : Finset (Fin m) := C.filter fun a => P.bad a x

/-- `Z = λ(all constraints satisfied)`. -/
noncomputable def Z : ℝ := P.prob (P.sat Finset.univ)

/-- `μ = λ(· | all constraints satisfied)`; `0` everywhere when `Z = 0`. -/
noncomputable def mu (x : P.Config) : ℝ := if P.sat Finset.univ x then P.mass x / P.Z else 0

/-- Definition 2.2, p.7: the dependency graph, joining `a ≠ b` when `vbl(a) ∩ vbl(b) ≠ ∅`. -/
def H : SimpleGraph (Fin m) where
  Adj a b := a ≠ b ∧ (P.vbl a ∩ P.vbl b).Nonempty
  symm := ⟨fun a b h => ⟨h.1.symm, by rw [Finset.inter_comm]; exact h.2⟩⟩
  loopless := ⟨fun a h => h.1 rfl⟩

instance : DecidableRel P.H.Adj := fun a b => by
  unfold H; exact inferInstanceAs (Decidable (a ≠ b ∧ (P.vbl a ∩ P.vbl b).Nonempty))

/-- `dist_H(a,b) = 2`: distinct, not adjacent, with a common neighbour. -/
def DistTwo (a b : Fin m) : Prop := a ≠ b ∧ ¬ P.H.Adj a b ∧ ∃ e, P.H.Adj a e ∧ P.H.Adj e b

instance (a b : Fin m) : Decidable (P.DistTwo a b) := by unfold DistTwo; infer_instance

/-- `{b : dist_H(a,b) ≤ 2}`. -/
def ball2 (a : Fin m) : Finset (Fin m) :=
  Finset.univ.filter fun b => b = a ∨ P.H.Adj a b ∨ P.DistTwo a b

/-- Definition 2.2, p.7: the radius-two volume, `Q = 0` if `A = ∅` and otherwise
`Q = max_a |{b : dist_H(a,b) ≤ 2}|`. -/
def Q : ℕ := Finset.univ.fold max 0 fun a => (P.ball2 a).card

/-- Exact one-event access (Definition 2.3, p.8), as oracles: an exact draw from each coordinate law
`λ_v`; the exact rationals `λ(Bad_a)`; and an exact draw from `λ(· | Bad_a)`. Constraint evaluation is
the test `bad`. -/
structure Access where
  /-- Draw from `λ_v`. -/
  coord : (v : Fin n) → Proc (Fin (P.dom v + 1))
  /-- The rational `λ(Bad_a)`, part of the input. -/
  pBad : Fin m → ℚ
  /-- Draw from `λ(· | Bad_a)`. -/
  cond : Fin m → Proc P.Config

/-- The oracles are exact (Definition 2.3): each coordinate draw and each conditional draw (when
`λ(Bad_a) > 0`) terminates with the exact law, and `pBad a = λ(Bad_a)`. An oracle's own running time is
not part of the counters: its outcomes carry zero ticks and zero calls, and the procedures count each
oracle call separately (an access call). -/
structure Access.Exact (O : P.Access) : Prop where
  coord_mass : ∀ v, Proc.mass (O.coord v) = 1
  coord_law : ∀ v w, law (O.coord v) w = ENNReal.ofReal (P.lam v w)
  coord_free : ∀ v r, O.coord v r ≠ 0 → r.2 = (0, 0)
  pBad_eq : ∀ a, (O.pBad a : ℝ) = P.prob (P.bad a)
  cond_mass : ∀ a, 0 < P.prob (P.bad a) → Proc.mass (O.cond a) = 1
  cond_law : ∀ a, 0 < P.prob (P.bad a) → ∀ x,
    law (O.cond a) x = ENNReal.ofReal (if P.bad a x then P.mass x / P.prob (P.bad a) else 0)
  cond_free : ∀ a r, O.cond a r ≠ 0 → r.2 = (0, 0)

/-- The input length for Theorem 2.4: the variables with their domain sizes, the scopes, and the encodings
of the rationals `λ(Bad_a)`. -/
def inputSize (O : P.Access) : ℕ :=
  n + m + (∑ v, ((P.dom v + 1).size + 1)) + (∑ a, ∑ v ∈ P.vbl a, ((v : ℕ).size + 1)) +
    ∑ a, bits (O.pBad a)

end RCSP

end SamplingLLL.Supplement


